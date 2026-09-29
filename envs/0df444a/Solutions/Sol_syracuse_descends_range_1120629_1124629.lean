-- Prove2me | solution 1 for syracuse_descends_range_1120629_1124629
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:41.965354+00:00
-- url     : https://prove2.me/submissions/ddbb0bea-d9a8-4050-a97f-d5fbfbdcd2ac

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


theorem B2523149 : Blo 1120629 2523149 := bbase (se 3 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 2523149 = 946181) (by norm_num)
theorem B2523221 : Blo 1120629 2523221 := bbase (se 8 (by rfl) ⟨14784, by rfl⟩ : syracuseStep 2523221 = 29569) (by norm_num)
theorem B1441901 : Blo 1120629 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B2523293 : Blo 1120629 2523293 := bbase (se 3 (by rfl) ⟨473117, by rfl⟩ : syracuseStep 2523293 = 946235) (by norm_num)
theorem B2130077 : Blo 1120629 2130077 := bbase (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) (by norm_num)
theorem B7798997 : Blo 1120629 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B2523365 : Blo 1120629 2523365 := bbase (se 4 (by rfl) ⟨236565, by rfl⟩ : syracuseStep 2523365 = 473131) (by norm_num)
theorem B6062357 : Blo 1120629 6062357 := bbase (se 6 (by rfl) ⟨142086, by rfl⟩ : syracuseStep 6062357 = 284173) (by norm_num)
theorem B2523437 : Blo 1120629 2523437 := bbase (se 3 (by rfl) ⟨473144, by rfl⟩ : syracuseStep 2523437 = 946289) (by norm_num)
theorem B2130229 : Blo 1120629 2130229 := bbase (se 5 (by rfl) ⟨99854, by rfl⟩ : syracuseStep 2130229 = 199709) (by norm_num)
theorem B2523509 : Blo 1120629 2523509 := bbase (se 5 (by rfl) ⟨118289, by rfl⟩ : syracuseStep 2523509 = 236579) (by norm_num)
theorem B2523581 : Blo 1120629 2523581 := bbase (se 3 (by rfl) ⟨473171, by rfl⟩ : syracuseStep 2523581 = 946343) (by norm_num)
theorem B2523653 : Blo 1120629 2523653 := bbase (se 4 (by rfl) ⟨236592, by rfl⟩ : syracuseStep 2523653 = 473185) (by norm_num)
theorem B1278505 : Blo 1120629 1278505 := bbase (se 2 (by rfl) ⟨479439, by rfl⟩ : syracuseStep 1278505 = 958879) (by norm_num)
theorem B2523725 : Blo 1120629 2523725 := bbase (se 3 (by rfl) ⟨473198, by rfl⟩ : syracuseStep 2523725 = 946397) (by norm_num)
theorem B2130533 : Blo 1120629 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B2523797 : Blo 1120629 2523797 := bbase (se 6 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 2523797 = 118303) (by norm_num)
theorem B2523869 : Blo 1120629 2523869 := bbase (se 3 (by rfl) ⟨473225, by rfl⟩ : syracuseStep 2523869 = 946451) (by norm_num)
theorem B2523941 : Blo 1120629 2523941 := bbase (se 4 (by rfl) ⟨236619, by rfl⟩ : syracuseStep 2523941 = 473239) (by norm_num)
theorem B2524013 : Blo 1120629 2524013 := bbase (se 3 (by rfl) ⟨473252, by rfl⟩ : syracuseStep 2524013 = 946505) (by norm_num)
theorem B1278833 : Blo 1120629 1278833 := bbase (se 2 (by rfl) ⟨479562, by rfl⟩ : syracuseStep 1278833 = 959125) (by norm_num)
theorem B2524085 : Blo 1120629 2524085 := bbase (se 5 (by rfl) ⟨118316, by rfl⟩ : syracuseStep 2524085 = 236633) (by norm_num)
theorem B2524157 : Blo 1120629 2524157 := bbase (se 3 (by rfl) ⟨473279, by rfl⟩ : syracuseStep 2524157 = 946559) (by norm_num)
theorem B4260869 : Blo 1120629 4260869 := bbase (se 4 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 4260869 = 798913) (by norm_num)
theorem B2524229 : Blo 1120629 2524229 := bbase (se 4 (by rfl) ⟨236646, by rfl⟩ : syracuseStep 2524229 = 473293) (by norm_num)
theorem B2524301 : Blo 1120629 2524301 := bbase (se 3 (by rfl) ⟨473306, by rfl⟩ : syracuseStep 2524301 = 946613) (by norm_num)
theorem B2524373 : Blo 1120629 2524373 := bbase (se 7 (by rfl) ⟨29582, by rfl⟩ : syracuseStep 2524373 = 59165) (by norm_num)
theorem B2524445 : Blo 1120629 2524445 := bbase (se 3 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 2524445 = 946667) (by norm_num)
theorem B4261157 : Blo 1120629 4261157 := bbase (se 4 (by rfl) ⟨399483, by rfl⟩ : syracuseStep 4261157 = 798967) (by norm_num)
theorem B2131285 : Blo 1120629 2131285 := bbase (se 12 (by rfl) ⟨780, by rfl⟩ : syracuseStep 2131285 = 1561) (by norm_num)
theorem B2524517 : Blo 1120629 2524517 := bbase (se 4 (by rfl) ⟨236673, by rfl⟩ : syracuseStep 2524517 = 473347) (by norm_num)
theorem B2524589 : Blo 1120629 2524589 := bbase (se 3 (by rfl) ⟨473360, by rfl⟩ : syracuseStep 2524589 = 946721) (by norm_num)
theorem B2131429 : Blo 1120629 2131429 := bbase (se 4 (by rfl) ⟨199821, by rfl⟩ : syracuseStep 2131429 = 399643) (by norm_num)
theorem B2524661 : Blo 1120629 2524661 := bbase (se 5 (by rfl) ⟨118343, by rfl⟩ : syracuseStep 2524661 = 236687) (by norm_num)
theorem B2393621 : Blo 1120629 2393621 := bbase (se 6 (by rfl) ⟨56100, by rfl⟩ : syracuseStep 2393621 = 112201) (by norm_num)
theorem B2524733 : Blo 1120629 2524733 := bbase (se 3 (by rfl) ⟨473387, by rfl⟩ : syracuseStep 2524733 = 946775) (by norm_num)
theorem B2524805 : Blo 1120629 2524805 := bbase (se 4 (by rfl) ⟨236700, by rfl⟩ : syracuseStep 2524805 = 473401) (by norm_num)
theorem B2131589 : Blo 1120629 2131589 := bbase (se 4 (by rfl) ⟨199836, by rfl⟩ : syracuseStep 2131589 = 399673) (by norm_num)
theorem B1279633 : Blo 1120629 1279633 := bbase (se 2 (by rfl) ⟨479862, by rfl⟩ : syracuseStep 1279633 = 959725) (by norm_num)
theorem B1279645 : Blo 1120629 1279645 := bbase (se 3 (by rfl) ⟨239933, by rfl⟩ : syracuseStep 1279645 = 479867) (by norm_num)
theorem B2524877 : Blo 1120629 2524877 := bbase (se 3 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 2524877 = 946829) (by norm_num)
theorem B2393869 : Blo 1120629 2393869 := bbase (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) (by norm_num)
theorem B2524949 : Blo 1120629 2524949 := bbase (se 6 (by rfl) ⟨59178, by rfl⟩ : syracuseStep 2524949 = 118357) (by norm_num)
theorem B2131733 : Blo 1120629 2131733 := bbase (se 6 (by rfl) ⟨49962, by rfl⟩ : syracuseStep 2131733 = 99925) (by norm_num)
theorem B2525021 : Blo 1120629 2525021 := bbase (se 3 (by rfl) ⟨473441, by rfl⟩ : syracuseStep 2525021 = 946883) (by norm_num)
theorem B2525093 : Blo 1120629 2525093 := bbase (se 4 (by rfl) ⟨236727, by rfl⟩ : syracuseStep 2525093 = 473455) (by norm_num)
theorem B2557885 : Blo 1120629 2557885 := bbase (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) (by norm_num)
theorem B2525165 : Blo 1120629 2525165 := bbase (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) (by norm_num)
theorem B2525237 : Blo 1120629 2525237 := bbase (se 5 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 2525237 = 236741) (by norm_num)
theorem B2132021 : Blo 1120629 2132021 := bbase (se 5 (by rfl) ⟨99938, by rfl⟩ : syracuseStep 2132021 = 199877) (by norm_num)
theorem B2525309 : Blo 1120629 2525309 := bbase (se 3 (by rfl) ⟨473495, by rfl⟩ : syracuseStep 2525309 = 946991) (by norm_num)
theorem B2525381 : Blo 1120629 2525381 := bbase (se 4 (by rfl) ⟨236754, by rfl⟩ : syracuseStep 2525381 = 473509) (by norm_num)
theorem B2132173 : Blo 1120629 2132173 := bbase (se 3 (by rfl) ⟨399782, by rfl⟩ : syracuseStep 2132173 = 799565) (by norm_num)
theorem B2394373 : Blo 1120629 2394373 := bbase (se 4 (by rfl) ⟨224472, by rfl⟩ : syracuseStep 2394373 = 448945) (by norm_num)
theorem B2525453 : Blo 1120629 2525453 := bbase (se 3 (by rfl) ⟨473522, by rfl⟩ : syracuseStep 2525453 = 947045) (by norm_num)
theorem B1280329 : Blo 1120629 1280329 := bbase (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) (by norm_num)
theorem B2525525 : Blo 1120629 2525525 := bbase (se 10 (by rfl) ⟨3699, by rfl⟩ : syracuseStep 2525525 = 7399) (by norm_num)
theorem B2525597 : Blo 1120629 2525597 := bbase (se 3 (by rfl) ⟨473549, by rfl⟩ : syracuseStep 2525597 = 947099) (by norm_num)
theorem B4262341 : Blo 1120629 4262341 := bbase (se 4 (by rfl) ⟨399594, by rfl⟩ : syracuseStep 4262341 = 799189) (by norm_num)
theorem B2525669 : Blo 1120629 2525669 := bbase (se 4 (by rfl) ⟨236781, by rfl⟩ : syracuseStep 2525669 = 473563) (by norm_num)
theorem B2132477 : Blo 1120629 2132477 := bbase (se 3 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 2132477 = 799679) (by norm_num)
theorem B2525741 : Blo 1120629 2525741 := bbase (se 3 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 2525741 = 947153) (by norm_num)
theorem B2525813 : Blo 1120629 2525813 := bbase (se 5 (by rfl) ⟨118397, by rfl⟩ : syracuseStep 2525813 = 236795) (by norm_num)
theorem B2525885 : Blo 1120629 2525885 := bbase (se 3 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 2525885 = 947207) (by norm_num)
theorem B4786933 : Blo 1120629 4786933 := bbase (se 5 (by rfl) ⟨224387, by rfl⟩ : syracuseStep 4786933 = 448775) (by norm_num)
theorem B4262645 : Blo 1120629 4262645 := bbase (se 5 (by rfl) ⟨199811, by rfl⟩ : syracuseStep 4262645 = 399623) (by norm_num)
theorem B2525957 : Blo 1120629 2525957 := bbase (se 4 (by rfl) ⟨236808, by rfl⟩ : syracuseStep 2525957 = 473617) (by norm_num)
theorem B1280777 : Blo 1120629 1280777 := bbase (se 2 (by rfl) ⟨480291, by rfl⟩ : syracuseStep 1280777 = 960583) (by norm_num)
theorem B1346321 : Blo 1120629 1346321 := bbase (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) (by norm_num)
theorem B2526029 : Blo 1120629 2526029 := bbase (se 3 (by rfl) ⟨473630, by rfl⟩ : syracuseStep 2526029 = 947261) (by norm_num)
theorem B2526101 : Blo 1120629 2526101 := bbase (se 6 (by rfl) ⟨59205, by rfl⟩ : syracuseStep 2526101 = 118411) (by norm_num)
theorem B2526173 : Blo 1120629 2526173 := bbase (se 3 (by rfl) ⟨473657, by rfl⟩ : syracuseStep 2526173 = 947315) (by norm_num)
theorem B2526245 : Blo 1120629 2526245 := bbase (se 4 (by rfl) ⟨236835, by rfl⟩ : syracuseStep 2526245 = 473671) (by norm_num)
theorem B2526317 : Blo 1120629 2526317 := bbase (se 3 (by rfl) ⟨473684, by rfl⟩ : syracuseStep 2526317 = 947369) (by norm_num)
theorem B2395261 : Blo 1120629 2395261 := bbase (se 3 (by rfl) ⟨449111, by rfl⟩ : syracuseStep 2395261 = 898223) (by norm_num)
theorem B2526389 : Blo 1120629 2526389 := bbase (se 5 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 2526389 = 236849) (by norm_num)
theorem B1313977 : Blo 1120629 1313977 := bbase (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) (by norm_num)
theorem B2133229 : Blo 1120629 2133229 := bbase (se 3 (by rfl) ⟨399980, by rfl⟩ : syracuseStep 2133229 = 799961) (by norm_num)
theorem B2526461 : Blo 1120629 2526461 := bbase (se 3 (by rfl) ⟨473711, by rfl⟩ : syracuseStep 2526461 = 947423) (by norm_num)
theorem B1346825 : Blo 1120629 1346825 := bbase (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) (by norm_num)
theorem B2002205 : Blo 1120629 2002205 := bbase (se 3 (by rfl) ⟨375413, by rfl⟩ : syracuseStep 2002205 = 750827) (by norm_num)
theorem B1346873 : Blo 1120629 1346873 := bbase (se 2 (by rfl) ⟨505077, by rfl⟩ : syracuseStep 1346873 = 1010155) (by norm_num)
theorem B2526533 : Blo 1120629 2526533 := bbase (se 4 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 2526533 = 473725) (by norm_num)
theorem B2133373 : Blo 1120629 2133373 := bbase (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) (by norm_num)
theorem B2526605 : Blo 1120629 2526605 := bbase (se 3 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 2526605 = 947477) (by norm_num)
theorem B2526677 : Blo 1120629 2526677 := bbase (se 7 (by rfl) ⟨29609, by rfl⟩ : syracuseStep 2526677 = 59219) (by norm_num)
theorem B2526749 : Blo 1120629 2526749 := bbase (se 3 (by rfl) ⟨473765, by rfl⟩ : syracuseStep 2526749 = 947531) (by norm_num)
theorem B2133533 : Blo 1120629 2133533 := bbase (se 3 (by rfl) ⟨400037, by rfl⟩ : syracuseStep 2133533 = 800075) (by norm_num)
theorem B1347133 : Blo 1120629 1347133 := bbase (se 3 (by rfl) ⟨252587, by rfl⟩ : syracuseStep 1347133 = 505175) (by norm_num)
theorem B2526821 : Blo 1120629 2526821 := bbase (se 4 (by rfl) ⟨236889, by rfl⟩ : syracuseStep 2526821 = 473779) (by norm_num)
theorem B2395757 : Blo 1120629 2395757 := bbase (se 3 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 2395757 = 898409) (by norm_num)
theorem B9604757 : Blo 1120629 9604757 := bbase (se 6 (by rfl) ⟨225111, by rfl⟩ : syracuseStep 9604757 = 450223) (by norm_num)
theorem B2526893 : Blo 1120629 2526893 := bbase (se 3 (by rfl) ⟨473792, by rfl⟩ : syracuseStep 2526893 = 947585) (by norm_num)
theorem B2133677 : Blo 1120629 2133677 := bbase (se 3 (by rfl) ⟨400064, by rfl⟩ : syracuseStep 2133677 = 800129) (by norm_num)
theorem B1281749 : Blo 1120629 1281749 := bbase (se 7 (by rfl) ⟨15020, by rfl⟩ : syracuseStep 1281749 = 30041) (by norm_num)
theorem B2526965 : Blo 1120629 2526965 := bbase (se 5 (by rfl) ⟨118451, by rfl⟩ : syracuseStep 2526965 = 236903) (by norm_num)
theorem B2527037 : Blo 1120629 2527037 := bbase (se 3 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 2527037 = 947639) (by norm_num)
theorem B1347397 : Blo 1120629 1347397 := bbase (se 4 (by rfl) ⟨126318, by rfl⟩ : syracuseStep 1347397 = 252637) (by norm_num)
theorem B2527109 : Blo 1120629 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B1347517 : Blo 1120629 1347517 := bbase (se 3 (by rfl) ⟨252659, by rfl⟩ : syracuseStep 1347517 = 505319) (by norm_num)
theorem B2527181 : Blo 1120629 2527181 := bbase (se 3 (by rfl) ⟨473846, by rfl⟩ : syracuseStep 2527181 = 947693) (by norm_num)
theorem B2133965 : Blo 1120629 2133965 := bbase (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) (by norm_num)
theorem B3411925 : Blo 1120629 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B2592749 : Blo 1120629 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B2527253 : Blo 1120629 2527253 := bbase (se 6 (by rfl) ⟨59232, by rfl⟩ : syracuseStep 2527253 = 118465) (by norm_num)
theorem B2527325 : Blo 1120629 2527325 := bbase (se 3 (by rfl) ⟨473873, by rfl⟩ : syracuseStep 2527325 = 947747) (by norm_num)
theorem B2134117 : Blo 1120629 2134117 := bbase (se 4 (by rfl) ⟨200073, by rfl⟩ : syracuseStep 2134117 = 400147) (by norm_num)
theorem B2527397 : Blo 1120629 2527397 := bbase (se 4 (by rfl) ⟨236943, by rfl⟩ : syracuseStep 2527397 = 473887) (by norm_num)
theorem B2527469 : Blo 1120629 2527469 := bbase (se 3 (by rfl) ⟨473900, by rfl⟩ : syracuseStep 2527469 = 947801) (by norm_num)
theorem B2527541 : Blo 1120629 2527541 := bbase (se 5 (by rfl) ⟨118478, by rfl⟩ : syracuseStep 2527541 = 236957) (by norm_num)
theorem B2527613 : Blo 1120629 2527613 := bbase (se 3 (by rfl) ⟨473927, by rfl⟩ : syracuseStep 2527613 = 947855) (by norm_num)
theorem B2134421 : Blo 1120629 2134421 := bbase (se 6 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 2134421 = 100051) (by norm_num)
theorem B4919717 : Blo 1120629 4919717 := bbase (se 4 (by rfl) ⟨461223, by rfl⟩ : syracuseStep 4919717 = 922447) (by norm_num)
theorem B1708469 : Blo 1120629 1708469 := bbase (se 5 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 1708469 = 160169) (by norm_num)
theorem B2527685 : Blo 1120629 2527685 := bbase (se 4 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 2527685 = 473941) (by norm_num)
theorem B2396645 : Blo 1120629 2396645 := bbase (se 4 (by rfl) ⟨224685, by rfl⟩ : syracuseStep 2396645 = 449371) (by norm_num)
theorem B2527757 : Blo 1120629 2527757 := bbase (se 3 (by rfl) ⟨473954, by rfl⟩ : syracuseStep 2527757 = 947909) (by norm_num)
theorem B2527829 : Blo 1120629 2527829 := bbase (se 8 (by rfl) ⟨14811, by rfl⟩ : syracuseStep 2527829 = 29623) (by norm_num)
theorem B2396765 : Blo 1120629 2396765 := bbase (se 3 (by rfl) ⟨449393, by rfl⟩ : syracuseStep 2396765 = 898787) (by norm_num)
theorem B2527901 : Blo 1120629 2527901 := bbase (se 3 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 2527901 = 947963) (by norm_num)
theorem B5116645 : Blo 1120629 5116645 := bbase (se 4 (by rfl) ⟨479685, by rfl⟩ : syracuseStep 5116645 = 959371) (by norm_num)
theorem B2527973 : Blo 1120629 2527973 := bbase (se 4 (by rfl) ⟨236997, by rfl⟩ : syracuseStep 2527973 = 473995) (by norm_num)
theorem B1348373 : Blo 1120629 1348373 := bbase (se 6 (by rfl) ⟨31602, by rfl⟩ : syracuseStep 1348373 = 63205) (by norm_num)
theorem B2528045 : Blo 1120629 2528045 := bbase (se 3 (by rfl) ⟨474008, by rfl⟩ : syracuseStep 2528045 = 948017) (by norm_num)
theorem B4264757 : Blo 1120629 4264757 := bbase (se 5 (by rfl) ⟨199910, by rfl⟩ : syracuseStep 4264757 = 399821) (by norm_num)
theorem B2528117 : Blo 1120629 2528117 := bbase (se 5 (by rfl) ⟨118505, by rfl⟩ : syracuseStep 2528117 = 237011) (by norm_num)
theorem B11539381 : Blo 1120629 11539381 := bbase (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) (by norm_num)
theorem B2528189 : Blo 1120629 2528189 := bbase (se 3 (by rfl) ⟨474035, by rfl⟩ : syracuseStep 2528189 = 948071) (by norm_num)
theorem B2528261 : Blo 1120629 2528261 := bbase (se 4 (by rfl) ⟨237024, by rfl⟩ : syracuseStep 2528261 = 474049) (by norm_num)
theorem B2528333 : Blo 1120629 2528333 := bbase (se 3 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 2528333 = 948125) (by norm_num)
theorem B4265045 : Blo 1120629 4265045 := bbase (se 8 (by rfl) ⟨24990, by rfl⟩ : syracuseStep 4265045 = 49981) (by norm_num)
theorem B1709149 : Blo 1120629 1709149 := bbase (se 3 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 1709149 = 640931) (by norm_num)
theorem B2528405 : Blo 1120629 2528405 := bbase (se 6 (by rfl) ⟨59259, by rfl⟩ : syracuseStep 2528405 = 118519) (by norm_num)
theorem B2397397 : Blo 1120629 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B2528477 : Blo 1120629 2528477 := bbase (se 3 (by rfl) ⟨474089, by rfl⟩ : syracuseStep 2528477 = 948179) (by norm_num)
theorem B2528549 : Blo 1120629 2528549 := bbase (se 4 (by rfl) ⟨237051, by rfl⟩ : syracuseStep 2528549 = 474103) (by norm_num)
theorem B2528621 : Blo 1120629 2528621 := bbase (se 3 (by rfl) ⟨474116, by rfl⟩ : syracuseStep 2528621 = 948233) (by norm_num)
theorem B5674373 : Blo 1120629 5674373 := bbase (se 4 (by rfl) ⟨531972, by rfl⟩ : syracuseStep 5674373 = 1063945) (by norm_num)
theorem B2528693 : Blo 1120629 2528693 := bbase (se 5 (by rfl) ⟨118532, by rfl⟩ : syracuseStep 2528693 = 237065) (by norm_num)
theorem B1349093 : Blo 1120629 1349093 := bbase (se 4 (by rfl) ⟨126477, by rfl⟩ : syracuseStep 1349093 = 252955) (by norm_num)
theorem B6395381 : Blo 1120629 6395381 := bbase (se 5 (by rfl) ⟨299783, by rfl⟩ : syracuseStep 6395381 = 599567) (by norm_num)
theorem B2528765 : Blo 1120629 2528765 := bbase (se 3 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 2528765 = 948287) (by norm_num)
theorem B2528837 : Blo 1120629 2528837 := bbase (se 4 (by rfl) ⟨237078, by rfl⟩ : syracuseStep 2528837 = 474157) (by norm_num)
theorem B2528909 : Blo 1120629 2528909 := bbase (se 3 (by rfl) ⟨474170, by rfl⟩ : syracuseStep 2528909 = 948341) (by norm_num)
theorem B4789925 : Blo 1120629 4789925 := bbase (se 4 (by rfl) ⟨449055, by rfl⟩ : syracuseStep 4789925 = 898111) (by norm_num)
theorem B2528981 : Blo 1120629 2528981 := bbase (se 7 (by rfl) ⟨29636, by rfl⟩ : syracuseStep 2528981 = 59273) (by norm_num)
theorem B1349401 : Blo 1120629 1349401 := bbase (se 2 (by rfl) ⟨506025, by rfl⟩ : syracuseStep 1349401 = 1012051) (by norm_num)
theorem B2529053 : Blo 1120629 2529053 := bbase (se 3 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 2529053 = 948395) (by norm_num)
theorem B2529125 : Blo 1120629 2529125 := bbase (se 4 (by rfl) ⟨237105, by rfl⟩ : syracuseStep 2529125 = 474211) (by norm_num)
theorem B1349497 : Blo 1120629 1349497 := bbase (se 2 (by rfl) ⟨506061, by rfl⟩ : syracuseStep 1349497 = 1012123) (by norm_num)
theorem B2692997 : Blo 1120629 2692997 := bbase (se 4 (by rfl) ⟨252468, by rfl⟩ : syracuseStep 2692997 = 504937) (by norm_num)
theorem B2529197 : Blo 1120629 2529197 := bbase (se 3 (by rfl) ⟨474224, by rfl⟩ : syracuseStep 2529197 = 948449) (by norm_num)
theorem B2529269 : Blo 1120629 2529269 := bbase (se 5 (by rfl) ⟨118559, by rfl⟩ : syracuseStep 2529269 = 237119) (by norm_num)
theorem B1349641 : Blo 1120629 1349641 := bbase (se 2 (by rfl) ⟨506115, by rfl⟩ : syracuseStep 1349641 = 1012231) (by norm_num)
theorem B1153073 : Blo 1120629 1153073 := bbase (se 2 (by rfl) ⟨432402, by rfl⟩ : syracuseStep 1153073 = 864805) (by norm_num)
theorem B2529341 : Blo 1120629 2529341 := bbase (se 3 (by rfl) ⟨474251, by rfl⟩ : syracuseStep 2529341 = 948503) (by norm_num)
theorem B2398285 : Blo 1120629 2398285 := bbase (se 3 (by rfl) ⟨449678, by rfl⟩ : syracuseStep 2398285 = 899357) (by norm_num)
theorem B2529413 : Blo 1120629 2529413 := bbase (se 4 (by rfl) ⟨237132, by rfl⟩ : syracuseStep 2529413 = 474265) (by norm_num)
theorem B2398405 : Blo 1120629 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B2529485 : Blo 1120629 2529485 := bbase (se 3 (by rfl) ⟨474278, by rfl⟩ : syracuseStep 2529485 = 948557) (by norm_num)
theorem B4266229 : Blo 1120629 4266229 := bbase (se 5 (by rfl) ⟨199979, by rfl⟩ : syracuseStep 4266229 = 399959) (by norm_num)
theorem B2529557 : Blo 1120629 2529557 := bbase (se 6 (by rfl) ⟨59286, by rfl⟩ : syracuseStep 2529557 = 118573) (by norm_num)
theorem B2529629 : Blo 1120629 2529629 := bbase (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) (by norm_num)
theorem B2529701 : Blo 1120629 2529701 := bbase (se 4 (by rfl) ⟨237159, by rfl⟩ : syracuseStep 2529701 = 474319) (by norm_num)
theorem B2398661 : Blo 1120629 2398661 := bbase (se 4 (by rfl) ⟨224874, by rfl⟩ : syracuseStep 2398661 = 449749) (by norm_num)
theorem B2529773 : Blo 1120629 2529773 := bbase (se 3 (by rfl) ⟨474332, by rfl⟩ : syracuseStep 2529773 = 948665) (by norm_num)
theorem B1972765 : Blo 1120629 1972765 := bbase (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) (by norm_num)
theorem B4266533 : Blo 1120629 4266533 := bbase (se 4 (by rfl) ⟨399987, by rfl⟩ : syracuseStep 4266533 = 799975) (by norm_num)
theorem B2529845 : Blo 1120629 2529845 := bbase (se 5 (by rfl) ⟨118586, by rfl⟩ : syracuseStep 2529845 = 237173) (by norm_num)
theorem B2529917 : Blo 1120629 2529917 := bbase (se 3 (by rfl) ⟨474359, by rfl⟩ : syracuseStep 2529917 = 948719) (by norm_num)
theorem B5675669 : Blo 1120629 5675669 := bbase (se 6 (by rfl) ⟨133023, by rfl⟩ : syracuseStep 5675669 = 266047) (by norm_num)
theorem B4790933 : Blo 1120629 4790933 := bbase (se 6 (by rfl) ⟨112287, by rfl⟩ : syracuseStep 4790933 = 224575) (by norm_num)
theorem B2529989 : Blo 1120629 2529989 := bbase (se 4 (by rfl) ⟨237186, by rfl⟩ : syracuseStep 2529989 = 474373) (by norm_num)
theorem B2530061 : Blo 1120629 2530061 := bbase (se 3 (by rfl) ⟨474386, by rfl⟩ : syracuseStep 2530061 = 948773) (by norm_num)
theorem B2693957 : Blo 1120629 2693957 := bbase (se 4 (by rfl) ⟨252558, by rfl⟩ : syracuseStep 2693957 = 505117) (by norm_num)
theorem B2530133 : Blo 1120629 2530133 := bbase (se 9 (by rfl) ⟨7412, by rfl⟩ : syracuseStep 2530133 = 14825) (by norm_num)
theorem B2530205 : Blo 1120629 2530205 := bbase (se 3 (by rfl) ⟨474413, by rfl⟩ : syracuseStep 2530205 = 948827) (by norm_num)
theorem B2530277 : Blo 1120629 2530277 := bbase (se 4 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 2530277 = 474427) (by norm_num)
theorem B1350641 : Blo 1120629 1350641 := bbase (se 2 (by rfl) ⟨506490, by rfl⟩ : syracuseStep 1350641 = 1012981) (by norm_num)
theorem B8526869 : Blo 1120629 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B2530349 : Blo 1120629 2530349 := bbase (se 3 (by rfl) ⟨474440, by rfl⟩ : syracuseStep 2530349 = 948881) (by norm_num)
theorem B3513413 : Blo 1120629 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B2104421 : Blo 1120629 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B2399549 : Blo 1120629 2399549 := bbase (se 3 (by rfl) ⟨449915, by rfl⟩ : syracuseStep 2399549 = 899831) (by norm_num)
theorem B1514957 : Blo 1120629 1514957 := bbase (se 3 (by rfl) ⟨284054, by rfl⟩ : syracuseStep 1514957 = 568109) (by norm_num)
theorem B2399789 : Blo 1120629 2399789 := bbase (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) (by norm_num)
theorem B9576053 : Blo 1120629 9576053 := bbase (se 5 (by rfl) ⟨448877, by rfl⟩ : syracuseStep 9576053 = 897755) (by norm_num)
theorem B2334413 : Blo 1120629 2334413 := bbase (se 3 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 2334413 = 875405) (by norm_num)
theorem B8625973 : Blo 1120629 8625973 := bbase (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) (by norm_num)
theorem B5676965 : Blo 1120629 5676965 := bbase (se 4 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 5676965 = 1064431) (by norm_num)
theorem B2400293 : Blo 1120629 2400293 := bbase (se 4 (by rfl) ⟨225027, by rfl⟩ : syracuseStep 2400293 = 450055) (by norm_num)
theorem B2400301 : Blo 1120629 2400301 := bbase (se 3 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 2400301 = 900113) (by norm_num)
theorem B7184501 : Blo 1120629 7184501 := bbase (se 5 (by rfl) ⟨336773, by rfl⟩ : syracuseStep 7184501 = 673547) (by norm_num)
theorem B4792709 : Blo 1120629 4792709 := bbase (se 4 (by rfl) ⟨449316, by rfl⟩ : syracuseStep 4792709 = 898633) (by norm_num)
theorem B12788117 : Blo 1120629 12788117 := bbase (se 6 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 12788117 = 599443) (by norm_num)
theorem B2695717 : Blo 1120629 2695717 := bbase (se 4 (by rfl) ⟨252723, by rfl⟩ : syracuseStep 2695717 = 505447) (by norm_num)
theorem B6824533 : Blo 1120629 6824533 := bbase (se 8 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 6824533 = 79975) (by norm_num)
theorem B2564693 : Blo 1120629 2564693 := bbase (se 8 (by rfl) ⟨15027, by rfl⟩ : syracuseStep 2564693 = 30055) (by norm_num)
theorem B4268645 : Blo 1120629 4268645 := bbase (se 4 (by rfl) ⟨400185, by rfl⟩ : syracuseStep 4268645 = 800371) (by norm_num)
theorem B2695949 : Blo 1120629 2695949 := bbase (se 3 (by rfl) ⟨505490, by rfl⟩ : syracuseStep 2695949 = 1010981) (by norm_num)
theorem B2564885 : Blo 1120629 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B4268933 : Blo 1120629 4268933 := bbase (se 4 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 4268933 = 800425) (by norm_num)
theorem B1418305 : Blo 1120629 1418305 := bbase (se 2 (by rfl) ⟨531864, by rfl⟩ : syracuseStep 1418305 = 1063729) (by norm_num)
theorem B5121157 : Blo 1120629 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B2696341 : Blo 1120629 2696341 := bbase (se 6 (by rfl) ⟨63195, by rfl⟩ : syracuseStep 2696341 = 126391) (by norm_num)
theorem B2401429 : Blo 1120629 2401429 := bbase (se 6 (by rfl) ⟨56283, by rfl⟩ : syracuseStep 2401429 = 112567) (by norm_num)
theorem B1418401 : Blo 1120629 1418401 := bbase (se 2 (by rfl) ⟨531900, by rfl⟩ : syracuseStep 1418401 = 1063801) (by norm_num)
theorem B5678261 : Blo 1120629 5678261 := bbase (se 5 (by rfl) ⟨266168, by rfl⟩ : syracuseStep 5678261 = 532337) (by norm_num)
theorem B1418573 : Blo 1120629 1418573 := bbase (se 3 (by rfl) ⟨265982, by rfl⟩ : syracuseStep 1418573 = 531965) (by norm_num)
theorem B1516909 : Blo 1120629 1516909 := bbase (se 3 (by rfl) ⟨284420, by rfl⟩ : syracuseStep 1516909 = 568841) (by norm_num)
theorem B1418629 : Blo 1120629 1418629 := bbase (se 4 (by rfl) ⟨132996, by rfl⟩ : syracuseStep 1418629 = 265993) (by norm_num)
theorem B1516973 : Blo 1120629 1516973 := bbase (se 3 (by rfl) ⟨284432, by rfl⟩ : syracuseStep 1516973 = 568865) (by norm_num)
theorem B1418725 : Blo 1120629 1418725 := bbase (se 4 (by rfl) ⟨133005, by rfl⟩ : syracuseStep 1418725 = 266011) (by norm_num)
theorem B2401805 : Blo 1120629 2401805 := bbase (se 3 (by rfl) ⟨450338, by rfl⟩ : syracuseStep 2401805 = 900677) (by norm_num)
theorem B1680965 : Blo 1120629 1680965 := bbase (se 4 (by rfl) ⟨157590, by rfl⟩ : syracuseStep 1680965 = 315181) (by norm_num)
theorem B1517125 : Blo 1120629 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B1680989 : Blo 1120629 1680989 := bbase (se 3 (by rfl) ⟨315185, by rfl⟩ : syracuseStep 1680989 = 630371) (by norm_num)
theorem B1681013 : Blo 1120629 1681013 := bbase (se 5 (by rfl) ⟨78797, by rfl⟩ : syracuseStep 1681013 = 157595) (by norm_num)
theorem B1681037 : Blo 1120629 1681037 := bbase (se 3 (by rfl) ⟨315194, by rfl⟩ : syracuseStep 1681037 = 630389) (by norm_num)
theorem B1418897 : Blo 1120629 1418897 := bbase (se 2 (by rfl) ⟨532086, by rfl⟩ : syracuseStep 1418897 = 1064173) (by norm_num)
theorem B1681061 : Blo 1120629 1681061 := bbase (se 4 (by rfl) ⟨157599, by rfl⟩ : syracuseStep 1681061 = 315199) (by norm_num)
theorem B1681085 : Blo 1120629 1681085 := bbase (se 3 (by rfl) ⟨315203, by rfl⟩ : syracuseStep 1681085 = 630407) (by norm_num)
theorem B1418953 : Blo 1120629 1418953 := bbase (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) (by norm_num)
theorem B1681109 : Blo 1120629 1681109 := bbase (se 7 (by rfl) ⟨19700, by rfl⟩ : syracuseStep 1681109 = 39401) (by norm_num)
theorem B1681133 : Blo 1120629 1681133 := bbase (se 3 (by rfl) ⟨315212, by rfl⟩ : syracuseStep 1681133 = 630425) (by norm_num)
theorem B1681157 : Blo 1120629 1681157 := bbase (se 4 (by rfl) ⟨157608, by rfl⟩ : syracuseStep 1681157 = 315217) (by norm_num)
theorem B1681181 : Blo 1120629 1681181 := bbase (se 3 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 1681181 = 630443) (by norm_num)
theorem B5121829 : Blo 1120629 5121829 := bbase (se 4 (by rfl) ⟨480171, by rfl⟩ : syracuseStep 5121829 = 960343) (by norm_num)
theorem B1419049 : Blo 1120629 1419049 := bbase (se 2 (by rfl) ⟨532143, by rfl⟩ : syracuseStep 1419049 = 1064287) (by norm_num)
theorem B1681205 : Blo 1120629 1681205 := bbase (se 5 (by rfl) ⟨78806, by rfl⟩ : syracuseStep 1681205 = 157613) (by norm_num)
theorem B1681229 : Blo 1120629 1681229 := bbase (se 3 (by rfl) ⟨315230, by rfl⟩ : syracuseStep 1681229 = 630461) (by norm_num)
theorem B1681253 : Blo 1120629 1681253 := bbase (se 4 (by rfl) ⟨157617, by rfl⟩ : syracuseStep 1681253 = 315235) (by norm_num)
theorem B1681277 : Blo 1120629 1681277 := bbase (se 3 (by rfl) ⟨315239, by rfl⟩ : syracuseStep 1681277 = 630479) (by norm_num)
theorem B1681301 : Blo 1120629 1681301 := bbase (se 6 (by rfl) ⟨39405, by rfl⟩ : syracuseStep 1681301 = 78811) (by norm_num)
theorem B15345557 : Blo 1120629 15345557 := bbase (se 6 (by rfl) ⟨359661, by rfl⟩ : syracuseStep 15345557 = 719323) (by norm_num)
theorem B1681325 : Blo 1120629 1681325 := bbase (se 3 (by rfl) ⟨315248, by rfl⟩ : syracuseStep 1681325 = 630497) (by norm_num)
theorem B2467757 : Blo 1120629 2467757 := bbase (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) (by norm_num)
theorem B1681349 : Blo 1120629 1681349 := bbase (se 4 (by rfl) ⟨157626, by rfl⟩ : syracuseStep 1681349 = 315253) (by norm_num)
theorem B1419221 : Blo 1120629 1419221 := bbase (se 7 (by rfl) ⟨16631, by rfl⟩ : syracuseStep 1419221 = 33263) (by norm_num)
theorem B1681373 : Blo 1120629 1681373 := bbase (se 3 (by rfl) ⟨315257, by rfl⟩ : syracuseStep 1681373 = 630515) (by norm_num)
theorem B1681397 : Blo 1120629 1681397 := bbase (se 5 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 1681397 = 157631) (by norm_num)
theorem B1681421 : Blo 1120629 1681421 := bbase (se 3 (by rfl) ⟨315266, by rfl⟩ : syracuseStep 1681421 = 630533) (by norm_num)
theorem B1419277 : Blo 1120629 1419277 := bbase (se 3 (by rfl) ⟨266114, by rfl⟩ : syracuseStep 1419277 = 532229) (by norm_num)
theorem B1681445 : Blo 1120629 1681445 := bbase (se 4 (by rfl) ⟨157635, by rfl⟩ : syracuseStep 1681445 = 315271) (by norm_num)
theorem B1681469 : Blo 1120629 1681469 := bbase (se 3 (by rfl) ⟨315275, by rfl⟩ : syracuseStep 1681469 = 630551) (by norm_num)
theorem B1681493 : Blo 1120629 1681493 := bbase (se 8 (by rfl) ⟨9852, by rfl⟩ : syracuseStep 1681493 = 19705) (by norm_num)
theorem B1681517 : Blo 1120629 1681517 := bbase (se 3 (by rfl) ⟨315284, by rfl⟩ : syracuseStep 1681517 = 630569) (by norm_num)
theorem B1419373 : Blo 1120629 1419373 := bbase (se 3 (by rfl) ⟨266132, by rfl⟩ : syracuseStep 1419373 = 532265) (by norm_num)
theorem B1681541 : Blo 1120629 1681541 := bbase (se 4 (by rfl) ⟨157644, by rfl⟩ : syracuseStep 1681541 = 315289) (by norm_num)
theorem B1681565 : Blo 1120629 1681565 := bbase (se 3 (by rfl) ⟨315293, by rfl⟩ : syracuseStep 1681565 = 630587) (by norm_num)
theorem B1517725 : Blo 1120629 1517725 := bbase (se 3 (by rfl) ⟨284573, by rfl⟩ : syracuseStep 1517725 = 569147) (by norm_num)
theorem B1681589 : Blo 1120629 1681589 := bbase (se 5 (by rfl) ⟨78824, by rfl⟩ : syracuseStep 1681589 = 157649) (by norm_num)
theorem B1681613 : Blo 1120629 1681613 := bbase (se 3 (by rfl) ⟨315302, by rfl⟩ : syracuseStep 1681613 = 630605) (by norm_num)
theorem B2697437 : Blo 1120629 2697437 := bbase (se 3 (by rfl) ⟨505769, by rfl⟩ : syracuseStep 2697437 = 1011539) (by norm_num)
theorem B1681637 : Blo 1120629 1681637 := bbase (se 4 (by rfl) ⟨157653, by rfl⟩ : syracuseStep 1681637 = 315307) (by norm_num)
theorem B1681661 : Blo 1120629 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B1681685 : Blo 1120629 1681685 := bbase (se 6 (by rfl) ⟨39414, by rfl⟩ : syracuseStep 1681685 = 78829) (by norm_num)
theorem B1419545 : Blo 1120629 1419545 := bbase (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) (by norm_num)
theorem B1681709 : Blo 1120629 1681709 := bbase (se 3 (by rfl) ⟨315320, by rfl⟩ : syracuseStep 1681709 = 630641) (by norm_num)
theorem B1681733 : Blo 1120629 1681733 := bbase (se 4 (by rfl) ⟨157662, by rfl⟩ : syracuseStep 1681733 = 315325) (by norm_num)
theorem B1419601 : Blo 1120629 1419601 := bbase (se 2 (by rfl) ⟨532350, by rfl⟩ : syracuseStep 1419601 = 1064701) (by norm_num)
theorem B1681757 : Blo 1120629 1681757 := bbase (se 3 (by rfl) ⟨315329, by rfl⟩ : syracuseStep 1681757 = 630659) (by norm_num)
theorem B1681781 : Blo 1120629 1681781 := bbase (se 5 (by rfl) ⟨78833, by rfl⟩ : syracuseStep 1681781 = 157667) (by norm_num)
theorem B1681805 : Blo 1120629 1681805 := bbase (se 3 (by rfl) ⟨315338, by rfl⟩ : syracuseStep 1681805 = 630677) (by norm_num)
theorem B1681829 : Blo 1120629 1681829 := bbase (se 4 (by rfl) ⟨157671, by rfl⟩ : syracuseStep 1681829 = 315343) (by norm_num)
theorem B1419697 : Blo 1120629 1419697 := bbase (se 2 (by rfl) ⟨532386, by rfl⟩ : syracuseStep 1419697 = 1064773) (by norm_num)
theorem B1681853 : Blo 1120629 1681853 := bbase (se 3 (by rfl) ⟨315347, by rfl⟩ : syracuseStep 1681853 = 630695) (by norm_num)
theorem B5679557 : Blo 1120629 5679557 := bbase (se 4 (by rfl) ⟨532458, by rfl⟩ : syracuseStep 5679557 = 1064917) (by norm_num)
theorem B4106693 : Blo 1120629 4106693 := bbase (se 4 (by rfl) ⟨385002, by rfl⟩ : syracuseStep 4106693 = 770005) (by norm_num)
theorem B1681877 : Blo 1120629 1681877 := bbase (se 7 (by rfl) ⟨19709, by rfl⟩ : syracuseStep 1681877 = 39419) (by norm_num)
theorem B19179989 : Blo 1120629 19179989 := bbase (se 7 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 19179989 = 449531) (by norm_num)
theorem B1681901 : Blo 1120629 1681901 := bbase (se 3 (by rfl) ⟨315356, by rfl⟩ : syracuseStep 1681901 = 630713) (by norm_num)
theorem B6072821 : Blo 1120629 6072821 := bbase (se 5 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 6072821 = 569327) (by norm_num)
theorem B2697725 : Blo 1120629 2697725 := bbase (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) (by norm_num)
theorem B1681925 : Blo 1120629 1681925 := bbase (se 4 (by rfl) ⟨157680, by rfl⟩ : syracuseStep 1681925 = 315361) (by norm_num)
theorem B2599445 : Blo 1120629 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B1681949 : Blo 1120629 1681949 := bbase (se 3 (by rfl) ⟨315365, by rfl⟩ : syracuseStep 1681949 = 630731) (by norm_num)
theorem B4041269 : Blo 1120629 4041269 := bbase (se 5 (by rfl) ⟨189434, by rfl⟩ : syracuseStep 4041269 = 378869) (by norm_num)
theorem B1681973 : Blo 1120629 1681973 := bbase (se 5 (by rfl) ⟨78842, by rfl⟩ : syracuseStep 1681973 = 157685) (by norm_num)
theorem B1681997 : Blo 1120629 1681997 := bbase (se 3 (by rfl) ⟨315374, by rfl⟩ : syracuseStep 1681997 = 630749) (by norm_num)
theorem B1419869 : Blo 1120629 1419869 := bbase (se 3 (by rfl) ⟨266225, by rfl⟩ : syracuseStep 1419869 = 532451) (by norm_num)
theorem B1682021 : Blo 1120629 1682021 := bbase (se 4 (by rfl) ⟨157689, by rfl⟩ : syracuseStep 1682021 = 315379) (by norm_num)
theorem B1682045 : Blo 1120629 1682045 := bbase (se 3 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 1682045 = 630767) (by norm_num)
theorem B1682069 : Blo 1120629 1682069 := bbase (se 6 (by rfl) ⟨39423, by rfl⟩ : syracuseStep 1682069 = 78847) (by norm_num)
theorem B1419925 : Blo 1120629 1419925 := bbase (se 6 (by rfl) ⟨33279, by rfl⟩ : syracuseStep 1419925 = 66559) (by norm_num)
theorem B1682093 : Blo 1120629 1682093 := bbase (se 3 (by rfl) ⟨315392, by rfl⟩ : syracuseStep 1682093 = 630785) (by norm_num)
theorem B1682117 : Blo 1120629 1682117 := bbase (se 4 (by rfl) ⟨157698, by rfl⟩ : syracuseStep 1682117 = 315397) (by norm_num)
theorem B1682141 : Blo 1120629 1682141 := bbase (se 3 (by rfl) ⟨315401, by rfl⟩ : syracuseStep 1682141 = 630803) (by norm_num)
theorem B1682165 : Blo 1120629 1682165 := bbase (se 5 (by rfl) ⟨78851, by rfl⟩ : syracuseStep 1682165 = 157703) (by norm_num)
theorem B1420021 : Blo 1120629 1420021 := bbase (se 5 (by rfl) ⟨66563, by rfl⟩ : syracuseStep 1420021 = 133127) (by norm_num)
theorem B1682189 : Blo 1120629 1682189 := bbase (se 3 (by rfl) ⟨315410, by rfl⟩ : syracuseStep 1682189 = 630821) (by norm_num)
theorem B1682213 : Blo 1120629 1682213 := bbase (se 4 (by rfl) ⟨157707, by rfl⟩ : syracuseStep 1682213 = 315415) (by norm_num)
theorem B1682237 : Blo 1120629 1682237 := bbase (se 3 (by rfl) ⟨315419, by rfl⟩ : syracuseStep 1682237 = 630839) (by norm_num)
theorem B1682261 : Blo 1120629 1682261 := bbase (se 9 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 1682261 = 9857) (by norm_num)
theorem B1682285 : Blo 1120629 1682285 := bbase (se 3 (by rfl) ⟨315428, by rfl⟩ : syracuseStep 1682285 = 630857) (by norm_num)
theorem B1682309 : Blo 1120629 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B1682333 : Blo 1120629 1682333 := bbase (se 3 (by rfl) ⟨315437, by rfl⟩ : syracuseStep 1682333 = 630875) (by norm_num)
theorem B1420193 : Blo 1120629 1420193 := bbase (se 2 (by rfl) ⟨532572, by rfl⟩ : syracuseStep 1420193 = 1065145) (by norm_num)
theorem B1682357 : Blo 1120629 1682357 := bbase (se 5 (by rfl) ⟨78860, by rfl⟩ : syracuseStep 1682357 = 157721) (by norm_num)
theorem B1682381 : Blo 1120629 1682381 := bbase (se 3 (by rfl) ⟨315446, by rfl⟩ : syracuseStep 1682381 = 630893) (by norm_num)
theorem B1420249 : Blo 1120629 1420249 := bbase (se 2 (by rfl) ⟨532593, by rfl⟩ : syracuseStep 1420249 = 1065187) (by norm_num)
theorem B1682405 : Blo 1120629 1682405 := bbase (se 4 (by rfl) ⟨157725, by rfl⟩ : syracuseStep 1682405 = 315451) (by norm_num)
theorem B1682429 : Blo 1120629 1682429 := bbase (se 3 (by rfl) ⟨315455, by rfl⟩ : syracuseStep 1682429 = 630911) (by norm_num)
theorem B14363669 : Blo 1120629 14363669 := bbase (se 6 (by rfl) ⟨336648, by rfl⟩ : syracuseStep 14363669 = 673297) (by norm_num)
theorem B1682453 : Blo 1120629 1682453 := bbase (se 6 (by rfl) ⟨39432, by rfl⟩ : syracuseStep 1682453 = 78865) (by norm_num)
theorem B1682477 : Blo 1120629 1682477 := bbase (se 3 (by rfl) ⟨315464, by rfl⟩ : syracuseStep 1682477 = 630929) (by norm_num)
theorem B1420345 : Blo 1120629 1420345 := bbase (se 2 (by rfl) ⟨532629, by rfl⟩ : syracuseStep 1420345 = 1065259) (by norm_num)
theorem B1682501 : Blo 1120629 1682501 := bbase (se 4 (by rfl) ⟨157734, by rfl⟩ : syracuseStep 1682501 = 315469) (by norm_num)
theorem B1682525 : Blo 1120629 1682525 := bbase (se 3 (by rfl) ⟨315473, by rfl⟩ : syracuseStep 1682525 = 630947) (by norm_num)
theorem B1682549 : Blo 1120629 1682549 := bbase (se 5 (by rfl) ⟨78869, by rfl⟩ : syracuseStep 1682549 = 157739) (by norm_num)
theorem B1682573 : Blo 1120629 1682573 := bbase (se 3 (by rfl) ⟨315482, by rfl⟩ : syracuseStep 1682573 = 630965) (by norm_num)
theorem B1682597 : Blo 1120629 1682597 := bbase (se 4 (by rfl) ⟨157743, by rfl⟩ : syracuseStep 1682597 = 315487) (by norm_num)
theorem B1682621 : Blo 1120629 1682621 := bbase (se 3 (by rfl) ⟨315491, by rfl⟩ : syracuseStep 1682621 = 630983) (by norm_num)
theorem B1682645 : Blo 1120629 1682645 := bbase (se 7 (by rfl) ⟨19718, by rfl⟩ : syracuseStep 1682645 = 39437) (by norm_num)
theorem B1420517 : Blo 1120629 1420517 := bbase (se 4 (by rfl) ⟨133173, by rfl⟩ : syracuseStep 1420517 = 266347) (by norm_num)
theorem B1682669 : Blo 1120629 1682669 := bbase (se 3 (by rfl) ⟨315500, by rfl⟩ : syracuseStep 1682669 = 631001) (by norm_num)
theorem B1682693 : Blo 1120629 1682693 := bbase (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) (by norm_num)
theorem B2272541 : Blo 1120629 2272541 := bbase (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) (by norm_num)
theorem B1682717 : Blo 1120629 1682717 := bbase (se 3 (by rfl) ⟨315509, by rfl⟩ : syracuseStep 1682717 = 631019) (by norm_num)
theorem B1420573 : Blo 1120629 1420573 := bbase (se 3 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 1420573 = 532715) (by norm_num)
theorem B1682741 : Blo 1120629 1682741 := bbase (se 5 (by rfl) ⟨78878, by rfl⟩ : syracuseStep 1682741 = 157757) (by norm_num)
theorem B1682765 : Blo 1120629 1682765 := bbase (se 3 (by rfl) ⟨315518, by rfl⟩ : syracuseStep 1682765 = 631037) (by norm_num)
theorem B1682789 : Blo 1120629 1682789 := bbase (se 4 (by rfl) ⟨157761, by rfl⟩ : syracuseStep 1682789 = 315523) (by norm_num)
theorem B1682813 : Blo 1120629 1682813 := bbase (se 3 (by rfl) ⟨315527, by rfl⟩ : syracuseStep 1682813 = 631055) (by norm_num)
theorem B1420669 : Blo 1120629 1420669 := bbase (se 3 (by rfl) ⟨266375, by rfl⟩ : syracuseStep 1420669 = 532751) (by norm_num)
theorem B1682837 : Blo 1120629 1682837 := bbase (se 6 (by rfl) ⟨39441, by rfl⟩ : syracuseStep 1682837 = 78883) (by norm_num)
theorem B1682861 : Blo 1120629 1682861 := bbase (se 3 (by rfl) ⟨315536, by rfl⟩ : syracuseStep 1682861 = 631073) (by norm_num)
theorem B1682885 : Blo 1120629 1682885 := bbase (se 4 (by rfl) ⟨157770, by rfl⟩ : syracuseStep 1682885 = 315541) (by norm_num)
theorem B5385685 : Blo 1120629 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B14396885 : Blo 1120629 14396885 := bbase (se 7 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 14396885 = 337427) (by norm_num)
theorem B1682909 : Blo 1120629 1682909 := bbase (se 3 (by rfl) ⟨315545, by rfl⟩ : syracuseStep 1682909 = 631091) (by norm_num)
theorem B1682933 : Blo 1120629 1682933 := bbase (se 5 (by rfl) ⟨78887, by rfl⟩ : syracuseStep 1682933 = 157775) (by norm_num)
theorem B1682957 : Blo 1120629 1682957 := bbase (se 3 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 1682957 = 631109) (by norm_num)
theorem B1682981 : Blo 1120629 1682981 := bbase (se 4 (by rfl) ⟨157779, by rfl⟩ : syracuseStep 1682981 = 315559) (by norm_num)
theorem B1420841 : Blo 1120629 1420841 := bbase (se 2 (by rfl) ⟨532815, by rfl⟩ : syracuseStep 1420841 = 1065631) (by norm_num)
theorem B1683005 : Blo 1120629 1683005 := bbase (se 3 (by rfl) ⟨315563, by rfl⟩ : syracuseStep 1683005 = 631127) (by norm_num)
theorem B1683029 : Blo 1120629 1683029 := bbase (se 8 (by rfl) ⟨9861, by rfl⟩ : syracuseStep 1683029 = 19723) (by norm_num)
theorem B43789909 : Blo 1120629 43789909 := bbase (se 8 (by rfl) ⟨256581, by rfl⟩ : syracuseStep 43789909 = 513163) (by norm_num)
theorem B1420897 : Blo 1120629 1420897 := bbase (se 2 (by rfl) ⟨532836, by rfl⟩ : syracuseStep 1420897 = 1065673) (by norm_num)
theorem B1617509 : Blo 1120629 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B1683053 : Blo 1120629 1683053 := bbase (se 3 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 1683053 = 631145) (by norm_num)
theorem B1683077 : Blo 1120629 1683077 := bbase (se 4 (by rfl) ⟨157788, by rfl⟩ : syracuseStep 1683077 = 315577) (by norm_num)
theorem B1683101 : Blo 1120629 1683101 := bbase (se 3 (by rfl) ⟨315581, by rfl⟩ : syracuseStep 1683101 = 631163) (by norm_num)
theorem B1683125 : Blo 1120629 1683125 := bbase (se 5 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 1683125 = 157793) (by norm_num)
theorem B1420993 : Blo 1120629 1420993 := bbase (se 2 (by rfl) ⟨532872, by rfl⟩ : syracuseStep 1420993 = 1065745) (by norm_num)
theorem B1683149 : Blo 1120629 1683149 := bbase (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) (by norm_num)
theorem B5680853 : Blo 1120629 5680853 := bbase (se 7 (by rfl) ⟨66572, by rfl⟩ : syracuseStep 5680853 = 133145) (by norm_num)
theorem B1683173 : Blo 1120629 1683173 := bbase (se 4 (by rfl) ⟨157797, by rfl⟩ : syracuseStep 1683173 = 315595) (by norm_num)
theorem B1683197 : Blo 1120629 1683197 := bbase (se 3 (by rfl) ⟨315599, by rfl⟩ : syracuseStep 1683197 = 631199) (by norm_num)
theorem B1683221 : Blo 1120629 1683221 := bbase (se 6 (by rfl) ⟨39450, by rfl⟩ : syracuseStep 1683221 = 78901) (by norm_num)
theorem B1683245 : Blo 1120629 1683245 := bbase (se 3 (by rfl) ⟨315608, by rfl⟩ : syracuseStep 1683245 = 631217) (by norm_num)
theorem B2273093 : Blo 1120629 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B1683269 : Blo 1120629 1683269 := bbase (se 4 (by rfl) ⟨157806, by rfl⟩ : syracuseStep 1683269 = 315613) (by norm_num)
theorem B1683293 : Blo 1120629 1683293 := bbase (se 3 (by rfl) ⟨315617, by rfl⟩ : syracuseStep 1683293 = 631235) (by norm_num)
theorem B2273125 : Blo 1120629 2273125 := bbase (se 4 (by rfl) ⟨213105, by rfl⟩ : syracuseStep 2273125 = 426211) (by norm_num)
theorem B1421165 : Blo 1120629 1421165 := bbase (se 3 (by rfl) ⟨266468, by rfl⟩ : syracuseStep 1421165 = 532937) (by norm_num)
theorem B1683317 : Blo 1120629 1683317 := bbase (se 5 (by rfl) ⟨78905, by rfl⟩ : syracuseStep 1683317 = 157811) (by norm_num)
theorem B1683341 : Blo 1120629 1683341 := bbase (se 3 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 1683341 = 631253) (by norm_num)
theorem B1683365 : Blo 1120629 1683365 := bbase (se 4 (by rfl) ⟨157815, by rfl⟩ : syracuseStep 1683365 = 315631) (by norm_num)
theorem B1421221 : Blo 1120629 1421221 := bbase (se 4 (by rfl) ⟨133239, by rfl⟩ : syracuseStep 1421221 = 266479) (by norm_num)
theorem B1683389 : Blo 1120629 1683389 := bbase (se 3 (by rfl) ⟨315635, by rfl⟩ : syracuseStep 1683389 = 631271) (by norm_num)
theorem B1683413 : Blo 1120629 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B1683437 : Blo 1120629 1683437 := bbase (se 3 (by rfl) ⟨315644, by rfl⟩ : syracuseStep 1683437 = 631289) (by norm_num)
theorem B1683461 : Blo 1120629 1683461 := bbase (se 4 (by rfl) ⟨157824, by rfl⟩ : syracuseStep 1683461 = 315649) (by norm_num)
theorem B1421317 : Blo 1120629 1421317 := bbase (se 4 (by rfl) ⟨133248, by rfl⟩ : syracuseStep 1421317 = 266497) (by norm_num)
theorem B1683485 : Blo 1120629 1683485 := bbase (se 3 (by rfl) ⟨315653, by rfl⟩ : syracuseStep 1683485 = 631307) (by norm_num)
theorem B1683509 : Blo 1120629 1683509 := bbase (se 5 (by rfl) ⟨78914, by rfl⟩ : syracuseStep 1683509 = 157829) (by norm_num)
theorem B1683533 : Blo 1120629 1683533 := bbase (se 3 (by rfl) ⟨315662, by rfl⟩ : syracuseStep 1683533 = 631325) (by norm_num)
theorem B1683557 : Blo 1120629 1683557 := bbase (se 4 (by rfl) ⟨157833, by rfl⟩ : syracuseStep 1683557 = 315667) (by norm_num)
theorem B1683581 : Blo 1120629 1683581 := bbase (se 3 (by rfl) ⟨315671, by rfl⟩ : syracuseStep 1683581 = 631343) (by norm_num)
theorem B1519741 : Blo 1120629 1519741 := bbase (se 3 (by rfl) ⟨284951, by rfl⟩ : syracuseStep 1519741 = 569903) (by norm_num)
theorem B1683605 : Blo 1120629 1683605 := bbase (se 6 (by rfl) ⟨39459, by rfl⟩ : syracuseStep 1683605 = 78919) (by norm_num)
theorem B1683629 : Blo 1120629 1683629 := bbase (se 3 (by rfl) ⟨315680, by rfl⟩ : syracuseStep 1683629 = 631361) (by norm_num)
theorem B1421489 : Blo 1120629 1421489 := bbase (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) (by norm_num)
theorem B1683653 : Blo 1120629 1683653 := bbase (se 4 (by rfl) ⟨157842, by rfl⟩ : syracuseStep 1683653 = 315685) (by norm_num)
theorem B1683677 : Blo 1120629 1683677 := bbase (se 3 (by rfl) ⟨315689, by rfl⟩ : syracuseStep 1683677 = 631379) (by norm_num)
theorem B1421545 : Blo 1120629 1421545 := bbase (se 2 (by rfl) ⟨533079, by rfl⟩ : syracuseStep 1421545 = 1066159) (by norm_num)
theorem B1683701 : Blo 1120629 1683701 := bbase (se 5 (by rfl) ⟨78923, by rfl⟩ : syracuseStep 1683701 = 157847) (by norm_num)
theorem B1683725 : Blo 1120629 1683725 := bbase (se 3 (by rfl) ⟨315698, by rfl⟩ : syracuseStep 1683725 = 631397) (by norm_num)
theorem B1683749 : Blo 1120629 1683749 := bbase (se 4 (by rfl) ⟨157851, by rfl⟩ : syracuseStep 1683749 = 315703) (by norm_num)
theorem B1683773 : Blo 1120629 1683773 := bbase (se 3 (by rfl) ⟨315707, by rfl⟩ : syracuseStep 1683773 = 631415) (by norm_num)
theorem B1421641 : Blo 1120629 1421641 := bbase (se 2 (by rfl) ⟨533115, by rfl⟩ : syracuseStep 1421641 = 1066231) (by norm_num)
theorem B1683797 : Blo 1120629 1683797 := bbase (se 10 (by rfl) ⟨2466, by rfl⟩ : syracuseStep 1683797 = 4933) (by norm_num)
theorem B1683821 : Blo 1120629 1683821 := bbase (se 3 (by rfl) ⟨315716, by rfl⟩ : syracuseStep 1683821 = 631433) (by norm_num)
theorem B1683845 : Blo 1120629 1683845 := bbase (se 4 (by rfl) ⟨157860, by rfl⟩ : syracuseStep 1683845 = 315721) (by norm_num)
theorem B2732429 : Blo 1120629 2732429 := bbase (se 3 (by rfl) ⟨512330, by rfl⟩ : syracuseStep 2732429 = 1024661) (by norm_num)
theorem B1683869 : Blo 1120629 1683869 := bbase (se 3 (by rfl) ⟨315725, by rfl⟩ : syracuseStep 1683869 = 631451) (by norm_num)
theorem B1683893 : Blo 1120629 1683893 := bbase (se 5 (by rfl) ⟨78932, by rfl⟩ : syracuseStep 1683893 = 157865) (by norm_num)
theorem B1683917 : Blo 1120629 1683917 := bbase (se 3 (by rfl) ⟨315734, by rfl⟩ : syracuseStep 1683917 = 631469) (by norm_num)
theorem B1683941 : Blo 1120629 1683941 := bbase (se 4 (by rfl) ⟨157869, by rfl⟩ : syracuseStep 1683941 = 315739) (by norm_num)
theorem B1421813 : Blo 1120629 1421813 := bbase (se 5 (by rfl) ⟨66647, by rfl⟩ : syracuseStep 1421813 = 133295) (by norm_num)
theorem B1683965 : Blo 1120629 1683965 := bbase (se 3 (by rfl) ⟨315743, by rfl⟩ : syracuseStep 1683965 = 631487) (by norm_num)
theorem B1683989 : Blo 1120629 1683989 := bbase (se 6 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 1683989 = 78937) (by norm_num)
theorem B1684013 : Blo 1120629 1684013 := bbase (se 3 (by rfl) ⟨315752, by rfl⟩ : syracuseStep 1684013 = 631505) (by norm_num)
theorem B1421869 : Blo 1120629 1421869 := bbase (se 3 (by rfl) ⟨266600, by rfl⟩ : syracuseStep 1421869 = 533201) (by norm_num)
theorem B2699821 : Blo 1120629 2699821 := bbase (se 3 (by rfl) ⟨506216, by rfl⟩ : syracuseStep 2699821 = 1012433) (by norm_num)
theorem B4796981 : Blo 1120629 4796981 := bbase (se 5 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 4796981 = 449717) (by norm_num)
theorem B1684037 : Blo 1120629 1684037 := bbase (se 4 (by rfl) ⟨157878, by rfl⟩ : syracuseStep 1684037 = 315757) (by norm_num)
theorem B1684061 : Blo 1120629 1684061 := bbase (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) (by norm_num)
theorem B1684085 : Blo 1120629 1684085 := bbase (se 5 (by rfl) ⟨78941, by rfl⟩ : syracuseStep 1684085 = 157883) (by norm_num)
theorem B1684109 : Blo 1120629 1684109 := bbase (se 3 (by rfl) ⟨315770, by rfl⟩ : syracuseStep 1684109 = 631541) (by norm_num)
theorem B1421965 : Blo 1120629 1421965 := bbase (se 3 (by rfl) ⟨266618, by rfl⟩ : syracuseStep 1421965 = 533237) (by norm_num)
theorem B1684133 : Blo 1120629 1684133 := bbase (se 4 (by rfl) ⟨157887, by rfl⟩ : syracuseStep 1684133 = 315775) (by norm_num)
theorem B1684157 : Blo 1120629 1684157 := bbase (se 3 (by rfl) ⟨315779, by rfl⟩ : syracuseStep 1684157 = 631559) (by norm_num)
theorem B1684181 : Blo 1120629 1684181 := bbase (se 7 (by rfl) ⟨19736, by rfl⟩ : syracuseStep 1684181 = 39473) (by norm_num)
theorem B1684205 : Blo 1120629 1684205 := bbase (se 3 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 1684205 = 631577) (by norm_num)
theorem B1684229 : Blo 1120629 1684229 := bbase (se 4 (by rfl) ⟨157896, by rfl⟩ : syracuseStep 1684229 = 315793) (by norm_num)
theorem B1684253 : Blo 1120629 1684253 := bbase (se 3 (by rfl) ⟨315797, by rfl⟩ : syracuseStep 1684253 = 631595) (by norm_num)
theorem B1684277 : Blo 1120629 1684277 := bbase (se 5 (by rfl) ⟨78950, by rfl⟩ : syracuseStep 1684277 = 157901) (by norm_num)
theorem B1422137 : Blo 1120629 1422137 := bbase (se 2 (by rfl) ⟨533301, by rfl⟩ : syracuseStep 1422137 = 1066603) (by norm_num)
theorem B1684301 : Blo 1120629 1684301 := bbase (se 3 (by rfl) ⟨315806, by rfl⟩ : syracuseStep 1684301 = 631613) (by norm_num)
theorem B3191653 : Blo 1120629 3191653 := bbase (se 4 (by rfl) ⟨299217, by rfl⟩ : syracuseStep 3191653 = 598435) (by norm_num)
theorem B1684325 : Blo 1120629 1684325 := bbase (se 4 (by rfl) ⟨157905, by rfl⟩ : syracuseStep 1684325 = 315811) (by norm_num)
theorem B1422193 : Blo 1120629 1422193 := bbase (se 2 (by rfl) ⟨533322, by rfl⟩ : syracuseStep 1422193 = 1066645) (by norm_num)
theorem B1618813 : Blo 1120629 1618813 := bbase (se 3 (by rfl) ⟨303527, by rfl⟩ : syracuseStep 1618813 = 607055) (by norm_num)
theorem B1684349 : Blo 1120629 1684349 := bbase (se 3 (by rfl) ⟨315815, by rfl⟩ : syracuseStep 1684349 = 631631) (by norm_num)
theorem B1684373 : Blo 1120629 1684373 := bbase (se 6 (by rfl) ⟨39477, by rfl⟩ : syracuseStep 1684373 = 78955) (by norm_num)
theorem B1684397 : Blo 1120629 1684397 := bbase (se 3 (by rfl) ⟨315824, by rfl⟩ : syracuseStep 1684397 = 631649) (by norm_num)
theorem B1684421 : Blo 1120629 1684421 := bbase (se 4 (by rfl) ⟨157914, by rfl⟩ : syracuseStep 1684421 = 315829) (by norm_num)
theorem B1422289 : Blo 1120629 1422289 := bbase (se 2 (by rfl) ⟨533358, by rfl⟩ : syracuseStep 1422289 = 1066717) (by norm_num)
theorem B1684445 : Blo 1120629 1684445 := bbase (se 3 (by rfl) ⟨315833, by rfl⟩ : syracuseStep 1684445 = 631667) (by norm_num)
theorem B5682149 : Blo 1120629 5682149 := bbase (se 4 (by rfl) ⟨532701, by rfl⟩ : syracuseStep 5682149 = 1065403) (by norm_num)
theorem B2274293 : Blo 1120629 2274293 := bbase (se 5 (by rfl) ⟨106607, by rfl⟩ : syracuseStep 2274293 = 213215) (by norm_num)
theorem B1684469 : Blo 1120629 1684469 := bbase (se 5 (by rfl) ⟨78959, by rfl⟩ : syracuseStep 1684469 = 157919) (by norm_num)
theorem B1684493 : Blo 1120629 1684493 := bbase (se 3 (by rfl) ⟨315842, by rfl⟩ : syracuseStep 1684493 = 631685) (by norm_num)
theorem B1684517 : Blo 1120629 1684517 := bbase (se 4 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 1684517 = 315847) (by norm_num)
theorem B1684541 : Blo 1120629 1684541 := bbase (se 3 (by rfl) ⟨315851, by rfl⟩ : syracuseStep 1684541 = 631703) (by norm_num)
theorem B1684565 : Blo 1120629 1684565 := bbase (se 8 (by rfl) ⟨9870, by rfl⟩ : syracuseStep 1684565 = 19741) (by norm_num)
theorem B1684589 : Blo 1120629 1684589 := bbase (se 3 (by rfl) ⟨315860, by rfl⟩ : syracuseStep 1684589 = 631721) (by norm_num)
theorem B1422461 : Blo 1120629 1422461 := bbase (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) (by norm_num)
theorem B1684613 : Blo 1120629 1684613 := bbase (se 4 (by rfl) ⟨157932, by rfl⟩ : syracuseStep 1684613 = 315865) (by norm_num)
theorem B1684637 : Blo 1120629 1684637 := bbase (se 3 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 1684637 = 631739) (by norm_num)
theorem B1684661 : Blo 1120629 1684661 := bbase (se 5 (by rfl) ⟨78968, by rfl⟩ : syracuseStep 1684661 = 157937) (by norm_num)
theorem B1422517 : Blo 1120629 1422517 := bbase (se 5 (by rfl) ⟨66680, by rfl⟩ : syracuseStep 1422517 = 133361) (by norm_num)
theorem B2700485 : Blo 1120629 2700485 := bbase (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) (by norm_num)
theorem B1684685 : Blo 1120629 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B1684709 : Blo 1120629 1684709 := bbase (se 4 (by rfl) ⟨157941, by rfl⟩ : syracuseStep 1684709 = 315883) (by norm_num)
theorem B1684733 : Blo 1120629 1684733 := bbase (se 3 (by rfl) ⟨315887, by rfl⟩ : syracuseStep 1684733 = 631775) (by norm_num)
theorem B1684757 : Blo 1120629 1684757 := bbase (se 6 (by rfl) ⟨39486, by rfl⟩ : syracuseStep 1684757 = 78973) (by norm_num)
theorem B1422613 : Blo 1120629 1422613 := bbase (se 6 (by rfl) ⟨33342, by rfl⟩ : syracuseStep 1422613 = 66685) (by norm_num)
theorem B1684781 : Blo 1120629 1684781 := bbase (se 3 (by rfl) ⟨315896, by rfl⟩ : syracuseStep 1684781 = 631793) (by norm_num)
theorem B1684805 : Blo 1120629 1684805 := bbase (se 4 (by rfl) ⟨157950, by rfl⟩ : syracuseStep 1684805 = 315901) (by norm_num)
theorem B1684829 : Blo 1120629 1684829 := bbase (se 3 (by rfl) ⟨315905, by rfl⟩ : syracuseStep 1684829 = 631811) (by norm_num)
theorem B1684853 : Blo 1120629 1684853 := bbase (se 5 (by rfl) ⟨78977, by rfl⟩ : syracuseStep 1684853 = 157955) (by norm_num)
theorem B6403445 : Blo 1120629 6403445 := bbase (se 5 (by rfl) ⟨300161, by rfl⟩ : syracuseStep 6403445 = 600323) (by norm_num)
theorem B1684877 : Blo 1120629 1684877 := bbase (se 3 (by rfl) ⟨315914, by rfl⟩ : syracuseStep 1684877 = 631829) (by norm_num)
theorem B1684901 : Blo 1120629 1684901 := bbase (se 4 (by rfl) ⟨157959, by rfl⟩ : syracuseStep 1684901 = 315919) (by norm_num)
theorem B1684925 : Blo 1120629 1684925 := bbase (se 3 (by rfl) ⟨315923, by rfl⟩ : syracuseStep 1684925 = 631847) (by norm_num)
theorem B1422785 : Blo 1120629 1422785 := bbase (se 2 (by rfl) ⟨533544, by rfl⟩ : syracuseStep 1422785 = 1067089) (by norm_num)
theorem B1684949 : Blo 1120629 1684949 := bbase (se 7 (by rfl) ⟨19745, by rfl⟩ : syracuseStep 1684949 = 39491) (by norm_num)
theorem B5125589 : Blo 1120629 5125589 := bbase (se 7 (by rfl) ⟨60065, by rfl⟩ : syracuseStep 5125589 = 120131) (by norm_num)
theorem B1684973 : Blo 1120629 1684973 := bbase (se 3 (by rfl) ⟨315932, by rfl⟩ : syracuseStep 1684973 = 631865) (by norm_num)
theorem B1422841 : Blo 1120629 1422841 := bbase (se 2 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 1422841 = 1067131) (by norm_num)
theorem B1684997 : Blo 1120629 1684997 := bbase (se 4 (by rfl) ⟨157968, by rfl⟩ : syracuseStep 1684997 = 315937) (by norm_num)
theorem B6829589 : Blo 1120629 6829589 := bbase (se 6 (by rfl) ⟨160068, by rfl⟩ : syracuseStep 6829589 = 320137) (by norm_num)
theorem B1685021 : Blo 1120629 1685021 := bbase (se 3 (by rfl) ⟨315941, by rfl⟩ : syracuseStep 1685021 = 631883) (by norm_num)
theorem B1685045 : Blo 1120629 1685045 := bbase (se 5 (by rfl) ⟨78986, by rfl⟩ : syracuseStep 1685045 = 157973) (by norm_num)
theorem B3782213 : Blo 1120629 3782213 := bbase (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) (by norm_num)
theorem B1685069 : Blo 1120629 1685069 := bbase (se 3 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 1685069 = 631901) (by norm_num)
theorem B1422937 : Blo 1120629 1422937 := bbase (se 2 (by rfl) ⟨533601, by rfl⟩ : syracuseStep 1422937 = 1067203) (by norm_num)
theorem B1685093 : Blo 1120629 1685093 := bbase (se 4 (by rfl) ⟨157977, by rfl⟩ : syracuseStep 1685093 = 315955) (by norm_num)
theorem B1685117 : Blo 1120629 1685117 := bbase (se 3 (by rfl) ⟨315959, by rfl⟩ : syracuseStep 1685117 = 631919) (by norm_num)
theorem B1685141 : Blo 1120629 1685141 := bbase (se 6 (by rfl) ⟨39495, by rfl⟩ : syracuseStep 1685141 = 78991) (by norm_num)
theorem B1685165 : Blo 1120629 1685165 := bbase (se 3 (by rfl) ⟨315968, by rfl⟩ : syracuseStep 1685165 = 631937) (by norm_num)
theorem B1685189 : Blo 1120629 1685189 := bbase (se 4 (by rfl) ⟨157986, by rfl⟩ : syracuseStep 1685189 = 315973) (by norm_num)
theorem B1685213 : Blo 1120629 1685213 := bbase (se 3 (by rfl) ⟨315977, by rfl⟩ : syracuseStep 1685213 = 631955) (by norm_num)
theorem B1685237 : Blo 1120629 1685237 := bbase (se 5 (by rfl) ⟨78995, by rfl⟩ : syracuseStep 1685237 = 157991) (by norm_num)
theorem B1423109 : Blo 1120629 1423109 := bbase (se 4 (by rfl) ⟨133416, by rfl⟩ : syracuseStep 1423109 = 266833) (by norm_num)
theorem B1685261 : Blo 1120629 1685261 := bbase (se 3 (by rfl) ⟨315986, by rfl⟩ : syracuseStep 1685261 = 631973) (by norm_num)
theorem B1685285 : Blo 1120629 1685285 := bbase (se 4 (by rfl) ⟨157995, by rfl⟩ : syracuseStep 1685285 = 315991) (by norm_num)
theorem B1685309 : Blo 1120629 1685309 := bbase (se 3 (by rfl) ⟨315995, by rfl⟩ : syracuseStep 1685309 = 631991) (by norm_num)
theorem B1423165 : Blo 1120629 1423165 := bbase (se 3 (by rfl) ⟨266843, by rfl⟩ : syracuseStep 1423165 = 533687) (by norm_num)
theorem B1685333 : Blo 1120629 1685333 := bbase (se 9 (by rfl) ⟨4937, by rfl⟩ : syracuseStep 1685333 = 9875) (by norm_num)
theorem B1685357 : Blo 1120629 1685357 := bbase (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) (by norm_num)
theorem B1685381 : Blo 1120629 1685381 := bbase (se 4 (by rfl) ⟨158004, by rfl⟩ : syracuseStep 1685381 = 316009) (by norm_num)
theorem B1685405 : Blo 1120629 1685405 := bbase (se 3 (by rfl) ⟨316013, by rfl⟩ : syracuseStep 1685405 = 632027) (by norm_num)
theorem B1423261 : Blo 1120629 1423261 := bbase (se 3 (by rfl) ⟨266861, by rfl⟩ : syracuseStep 1423261 = 533723) (by norm_num)
theorem B1685429 : Blo 1120629 1685429 := bbase (se 5 (by rfl) ⟨79004, by rfl⟩ : syracuseStep 1685429 = 158009) (by norm_num)
theorem B1685453 : Blo 1120629 1685453 := bbase (se 3 (by rfl) ⟨316022, by rfl⟩ : syracuseStep 1685453 = 632045) (by norm_num)
theorem B1685477 : Blo 1120629 1685477 := bbase (se 4 (by rfl) ⟨158013, by rfl⟩ : syracuseStep 1685477 = 316027) (by norm_num)
theorem B3782645 : Blo 1120629 3782645 := bbase (se 5 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 3782645 = 354623) (by norm_num)
theorem B1685501 : Blo 1120629 1685501 := bbase (se 3 (by rfl) ⟨316031, by rfl⟩ : syracuseStep 1685501 = 632063) (by norm_num)
theorem B1685525 : Blo 1120629 1685525 := bbase (se 6 (by rfl) ⟨39504, by rfl⟩ : syracuseStep 1685525 = 79009) (by norm_num)
theorem B1685549 : Blo 1120629 1685549 := bbase (se 3 (by rfl) ⟨316040, by rfl⟩ : syracuseStep 1685549 = 632081) (by norm_num)
theorem B1685573 : Blo 1120629 1685573 := bbase (se 4 (by rfl) ⟨158022, by rfl⟩ : syracuseStep 1685573 = 316045) (by norm_num)
theorem B1685597 : Blo 1120629 1685597 := bbase (se 3 (by rfl) ⟨316049, by rfl⟩ : syracuseStep 1685597 = 632099) (by norm_num)
theorem B2275445 : Blo 1120629 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B1685621 : Blo 1120629 1685621 := bbase (se 5 (by rfl) ⟨79013, by rfl⟩ : syracuseStep 1685621 = 158027) (by norm_num)
theorem B1685645 : Blo 1120629 1685645 := bbase (se 3 (by rfl) ⟨316058, by rfl⟩ : syracuseStep 1685645 = 632117) (by norm_num)
theorem B1685669 : Blo 1120629 1685669 := bbase (se 4 (by rfl) ⟨158031, by rfl⟩ : syracuseStep 1685669 = 316063) (by norm_num)
theorem B1685693 : Blo 1120629 1685693 := bbase (se 3 (by rfl) ⟨316067, by rfl⟩ : syracuseStep 1685693 = 632135) (by norm_num)
theorem B1685717 : Blo 1120629 1685717 := bbase (se 7 (by rfl) ⟨19754, by rfl⟩ : syracuseStep 1685717 = 39509) (by norm_num)
theorem B1685741 : Blo 1120629 1685741 := bbase (se 3 (by rfl) ⟨316076, by rfl⟩ : syracuseStep 1685741 = 632153) (by norm_num)
theorem B5683445 : Blo 1120629 5683445 := bbase (se 5 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 5683445 = 532823) (by norm_num)
theorem B1685765 : Blo 1120629 1685765 := bbase (se 4 (by rfl) ⟨158040, by rfl⟩ : syracuseStep 1685765 = 316081) (by norm_num)
theorem B1685789 : Blo 1120629 1685789 := bbase (se 3 (by rfl) ⟨316085, by rfl⟩ : syracuseStep 1685789 = 632171) (by norm_num)
theorem B4798757 : Blo 1120629 4798757 := bbase (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) (by norm_num)
theorem B1685813 : Blo 1120629 1685813 := bbase (se 5 (by rfl) ⟨79022, by rfl⟩ : syracuseStep 1685813 = 158045) (by norm_num)
theorem B3193157 : Blo 1120629 3193157 := bbase (se 4 (by rfl) ⟨299358, by rfl⟩ : syracuseStep 3193157 = 598717) (by norm_num)
theorem B1685837 : Blo 1120629 1685837 := bbase (se 3 (by rfl) ⟨316094, by rfl⟩ : syracuseStep 1685837 = 632189) (by norm_num)
theorem B1685861 : Blo 1120629 1685861 := bbase (se 4 (by rfl) ⟨158049, by rfl⟩ : syracuseStep 1685861 = 316099) (by norm_num)
theorem B1685885 : Blo 1120629 1685885 := bbase (se 3 (by rfl) ⟨316103, by rfl⟩ : syracuseStep 1685885 = 632207) (by norm_num)
theorem B1685909 : Blo 1120629 1685909 := bbase (se 6 (by rfl) ⟨39513, by rfl⟩ : syracuseStep 1685909 = 79027) (by norm_num)
theorem B3783077 : Blo 1120629 3783077 := bbase (se 4 (by rfl) ⟨354663, by rfl⟩ : syracuseStep 3783077 = 709327) (by norm_num)
theorem B1685933 : Blo 1120629 1685933 := bbase (se 3 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 1685933 = 632225) (by norm_num)
theorem B1685957 : Blo 1120629 1685957 := bbase (se 4 (by rfl) ⟨158058, by rfl⟩ : syracuseStep 1685957 = 316117) (by norm_num)
theorem B1685981 : Blo 1120629 1685981 := bbase (se 3 (by rfl) ⟨316121, by rfl⟩ : syracuseStep 1685981 = 632243) (by norm_num)
theorem B1686005 : Blo 1120629 1686005 := bbase (se 5 (by rfl) ⟨79031, by rfl⟩ : syracuseStep 1686005 = 158063) (by norm_num)
theorem B1686029 : Blo 1120629 1686029 := bbase (se 3 (by rfl) ⟨316130, by rfl⟩ : syracuseStep 1686029 = 632261) (by norm_num)
theorem B4798997 : Blo 1120629 4798997 := bbase (se 6 (by rfl) ⟨112476, by rfl⟩ : syracuseStep 4798997 = 224953) (by norm_num)
theorem B6404629 : Blo 1120629 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B1686053 : Blo 1120629 1686053 := bbase (se 4 (by rfl) ⟨158067, by rfl⟩ : syracuseStep 1686053 = 316135) (by norm_num)
theorem B1686077 : Blo 1120629 1686077 := bbase (se 3 (by rfl) ⟨316139, by rfl⟩ : syracuseStep 1686077 = 632279) (by norm_num)
theorem B1686101 : Blo 1120629 1686101 := bbase (se 8 (by rfl) ⟨9879, by rfl⟩ : syracuseStep 1686101 = 19759) (by norm_num)
theorem B1686125 : Blo 1120629 1686125 := bbase (se 3 (by rfl) ⟨316148, by rfl⟩ : syracuseStep 1686125 = 632297) (by norm_num)
theorem B8534645 : Blo 1120629 8534645 := bbase (se 5 (by rfl) ⟨400061, by rfl⟩ : syracuseStep 8534645 = 800123) (by norm_num)
theorem B1686149 : Blo 1120629 1686149 := bbase (se 4 (by rfl) ⟨158076, by rfl⟩ : syracuseStep 1686149 = 316153) (by norm_num)
theorem B1686173 : Blo 1120629 1686173 := bbase (se 3 (by rfl) ⟨316157, by rfl⟩ : syracuseStep 1686173 = 632315) (by norm_num)
theorem B1686197 : Blo 1120629 1686197 := bbase (se 5 (by rfl) ⟨79040, by rfl⟩ : syracuseStep 1686197 = 158081) (by norm_num)
theorem B1686221 : Blo 1120629 1686221 := bbase (se 3 (by rfl) ⟨316166, by rfl⟩ : syracuseStep 1686221 = 632333) (by norm_num)
theorem B1686245 : Blo 1120629 1686245 := bbase (se 4 (by rfl) ⟨158085, by rfl⟩ : syracuseStep 1686245 = 316171) (by norm_num)
theorem B1686269 : Blo 1120629 1686269 := bbase (se 3 (by rfl) ⟨316175, by rfl⟩ : syracuseStep 1686269 = 632351) (by norm_num)
theorem B1686293 : Blo 1120629 1686293 := bbase (se 6 (by rfl) ⟨39522, by rfl⟩ : syracuseStep 1686293 = 79045) (by norm_num)
theorem B1686317 : Blo 1120629 1686317 := bbase (se 3 (by rfl) ⟨316184, by rfl⟩ : syracuseStep 1686317 = 632369) (by norm_num)
theorem B1686341 : Blo 1120629 1686341 := bbase (se 4 (by rfl) ⟨158094, by rfl⟩ : syracuseStep 1686341 = 316189) (by norm_num)
theorem B3783509 : Blo 1120629 3783509 := bbase (se 9 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 3783509 = 22169) (by norm_num)
theorem B1686365 : Blo 1120629 1686365 := bbase (se 3 (by rfl) ⟨316193, by rfl⟩ : syracuseStep 1686365 = 632387) (by norm_num)
theorem B1686389 : Blo 1120629 1686389 := bbase (se 5 (by rfl) ⟨79049, by rfl⟩ : syracuseStep 1686389 = 158099) (by norm_num)
theorem B1686413 : Blo 1120629 1686413 := bbase (se 3 (by rfl) ⟨316202, by rfl⟩ : syracuseStep 1686413 = 632405) (by norm_num)
theorem B1686437 : Blo 1120629 1686437 := bbase (se 4 (by rfl) ⟨158103, by rfl⟩ : syracuseStep 1686437 = 316207) (by norm_num)
theorem B1686461 : Blo 1120629 1686461 := bbase (se 3 (by rfl) ⟨316211, by rfl⟩ : syracuseStep 1686461 = 632423) (by norm_num)
theorem B1686485 : Blo 1120629 1686485 := bbase (se 7 (by rfl) ⟨19763, by rfl⟩ : syracuseStep 1686485 = 39527) (by norm_num)
theorem B1686509 : Blo 1120629 1686509 := bbase (se 3 (by rfl) ⟨316220, by rfl⟩ : syracuseStep 1686509 = 632441) (by norm_num)
theorem B1686533 : Blo 1120629 1686533 := bbase (se 4 (by rfl) ⟨158112, by rfl⟩ : syracuseStep 1686533 = 316225) (by norm_num)
theorem B1686557 : Blo 1120629 1686557 := bbase (se 3 (by rfl) ⟨316229, by rfl⟩ : syracuseStep 1686557 = 632459) (by norm_num)
theorem B1686581 : Blo 1120629 1686581 := bbase (se 5 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 1686581 = 158117) (by norm_num)
theorem B1686605 : Blo 1120629 1686605 := bbase (se 3 (by rfl) ⟨316238, by rfl⟩ : syracuseStep 1686605 = 632477) (by norm_num)
theorem B1686629 : Blo 1120629 1686629 := bbase (se 4 (by rfl) ⟨158121, by rfl⟩ : syracuseStep 1686629 = 316243) (by norm_num)
theorem B1686653 : Blo 1120629 1686653 := bbase (se 3 (by rfl) ⟨316247, by rfl⟩ : syracuseStep 1686653 = 632495) (by norm_num)
theorem B1686677 : Blo 1120629 1686677 := bbase (se 6 (by rfl) ⟨39531, by rfl⟩ : syracuseStep 1686677 = 79063) (by norm_num)
theorem B1686701 : Blo 1120629 1686701 := bbase (se 3 (by rfl) ⟨316256, by rfl⟩ : syracuseStep 1686701 = 632513) (by norm_num)
theorem B1260733 : Blo 1120629 1260733 := bbase (se 3 (by rfl) ⟨236387, by rfl⟩ : syracuseStep 1260733 = 472775) (by norm_num)
theorem B1686725 : Blo 1120629 1686725 := bbase (se 4 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 1686725 = 316261) (by norm_num)
theorem B15383765 : Blo 1120629 15383765 := bbase (se 7 (by rfl) ⟨180278, by rfl⟩ : syracuseStep 15383765 = 360557) (by norm_num)
theorem B1686749 : Blo 1120629 1686749 := bbase (se 3 (by rfl) ⟨316265, by rfl⟩ : syracuseStep 1686749 = 632531) (by norm_num)
theorem B1260769 : Blo 1120629 1260769 := bbase (se 2 (by rfl) ⟨472788, by rfl⟩ : syracuseStep 1260769 = 945577) (by norm_num)
theorem B1686773 : Blo 1120629 1686773 := bbase (se 5 (by rfl) ⟨79067, by rfl⟩ : syracuseStep 1686773 = 158135) (by norm_num)
theorem B1260805 : Blo 1120629 1260805 := bbase (se 4 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 1260805 = 236401) (by norm_num)
theorem B3783941 : Blo 1120629 3783941 := bbase (se 4 (by rfl) ⟨354744, by rfl⟩ : syracuseStep 3783941 = 709489) (by norm_num)
theorem B1686797 : Blo 1120629 1686797 := bbase (se 3 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 1686797 = 632549) (by norm_num)
theorem B1686821 : Blo 1120629 1686821 := bbase (se 4 (by rfl) ⟨158139, by rfl⟩ : syracuseStep 1686821 = 316279) (by norm_num)
theorem B1260841 : Blo 1120629 1260841 := bbase (se 2 (by rfl) ⟨472815, by rfl⟩ : syracuseStep 1260841 = 945631) (by norm_num)
theorem B1686845 : Blo 1120629 1686845 := bbase (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) (by norm_num)
theorem B1260877 : Blo 1120629 1260877 := bbase (se 3 (by rfl) ⟨236414, by rfl⟩ : syracuseStep 1260877 = 472829) (by norm_num)
theorem B1686869 : Blo 1120629 1686869 := bbase (se 11 (by rfl) ⟨1235, by rfl⟩ : syracuseStep 1686869 = 2471) (by norm_num)
theorem B1686893 : Blo 1120629 1686893 := bbase (se 3 (by rfl) ⟨316292, by rfl⟩ : syracuseStep 1686893 = 632585) (by norm_num)
theorem B1260913 : Blo 1120629 1260913 := bbase (se 2 (by rfl) ⟨472842, by rfl⟩ : syracuseStep 1260913 = 945685) (by norm_num)
theorem B5389685 : Blo 1120629 5389685 := bbase (se 5 (by rfl) ⟨252641, by rfl⟩ : syracuseStep 5389685 = 505283) (by norm_num)
theorem B1686917 : Blo 1120629 1686917 := bbase (se 4 (by rfl) ⟨158148, by rfl⟩ : syracuseStep 1686917 = 316297) (by norm_num)
theorem B1260949 : Blo 1120629 1260949 := bbase (se 6 (by rfl) ⟨29553, by rfl⟩ : syracuseStep 1260949 = 59107) (by norm_num)
theorem B1686941 : Blo 1120629 1686941 := bbase (se 3 (by rfl) ⟨316301, by rfl⟩ : syracuseStep 1686941 = 632603) (by norm_num)
theorem B2276789 : Blo 1120629 2276789 := bbase (se 5 (by rfl) ⟨106724, by rfl⟩ : syracuseStep 2276789 = 213449) (by norm_num)
theorem B1260985 : Blo 1120629 1260985 := bbase (se 2 (by rfl) ⟨472869, by rfl⟩ : syracuseStep 1260985 = 945739) (by norm_num)
theorem B1261021 : Blo 1120629 1261021 := bbase (se 3 (by rfl) ⟨236441, by rfl⟩ : syracuseStep 1261021 = 472883) (by norm_num)
theorem B1261057 : Blo 1120629 1261057 := bbase (se 2 (by rfl) ⟨472896, by rfl⟩ : syracuseStep 1261057 = 945793) (by norm_num)
theorem B5684741 : Blo 1120629 5684741 := bbase (se 4 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 5684741 = 1065889) (by norm_num)
theorem B4046357 : Blo 1120629 4046357 := bbase (se 6 (by rfl) ⟨94836, by rfl⟩ : syracuseStep 4046357 = 189673) (by norm_num)
theorem B1261093 : Blo 1120629 1261093 := bbase (se 4 (by rfl) ⟨118227, by rfl⟩ : syracuseStep 1261093 = 236455) (by norm_num)
theorem B1261129 : Blo 1120629 1261129 := bbase (se 2 (by rfl) ⟨472923, by rfl⟩ : syracuseStep 1261129 = 945847) (by norm_num)
theorem B1261165 : Blo 1120629 1261165 := bbase (se 3 (by rfl) ⟨236468, by rfl⟩ : syracuseStep 1261165 = 472937) (by norm_num)
theorem B1261201 : Blo 1120629 1261201 := bbase (se 2 (by rfl) ⟨472950, by rfl⟩ : syracuseStep 1261201 = 945901) (by norm_num)
theorem B1261237 : Blo 1120629 1261237 := bbase (se 5 (by rfl) ⟨59120, by rfl⟩ : syracuseStep 1261237 = 118241) (by norm_num)
theorem B3784373 : Blo 1120629 3784373 := bbase (se 5 (by rfl) ⟨177392, by rfl⟩ : syracuseStep 3784373 = 354785) (by norm_num)
theorem B1261273 : Blo 1120629 1261273 := bbase (se 2 (by rfl) ⟨472977, by rfl⟩ : syracuseStep 1261273 = 945955) (by norm_num)
theorem B1261309 : Blo 1120629 1261309 := bbase (se 3 (by rfl) ⟨236495, by rfl⟩ : syracuseStep 1261309 = 472991) (by norm_num)
theorem B1261345 : Blo 1120629 1261345 := bbase (se 2 (by rfl) ⟨473004, by rfl⟩ : syracuseStep 1261345 = 946009) (by norm_num)
theorem B4046645 : Blo 1120629 4046645 := bbase (se 5 (by rfl) ⟨189686, by rfl⟩ : syracuseStep 4046645 = 379373) (by norm_num)
theorem B1261381 : Blo 1120629 1261381 := bbase (se 4 (by rfl) ⟨118254, by rfl⟩ : syracuseStep 1261381 = 236509) (by norm_num)
theorem B1261417 : Blo 1120629 1261417 := bbase (se 2 (by rfl) ⟨473031, by rfl⟩ : syracuseStep 1261417 = 946063) (by norm_num)
theorem B3194741 : Blo 1120629 3194741 := bbase (se 5 (by rfl) ⟨149753, by rfl⟩ : syracuseStep 3194741 = 299507) (by norm_num)
theorem B9715573 : Blo 1120629 9715573 := bbase (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) (by norm_num)
theorem B1261453 : Blo 1120629 1261453 := bbase (se 3 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 1261453 = 473045) (by norm_num)
theorem B1261489 : Blo 1120629 1261489 := bbase (se 2 (by rfl) ⟨473058, by rfl⟩ : syracuseStep 1261489 = 946117) (by norm_num)
theorem B1261525 : Blo 1120629 1261525 := bbase (se 7 (by rfl) ⟨14783, by rfl⟩ : syracuseStep 1261525 = 29567) (by norm_num)
theorem B5128181 : Blo 1120629 5128181 := bbase (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) (by norm_num)
theorem B1261561 : Blo 1120629 1261561 := bbase (se 2 (by rfl) ⟨473085, by rfl⟩ : syracuseStep 1261561 = 946171) (by norm_num)
theorem B1261597 : Blo 1120629 1261597 := bbase (se 3 (by rfl) ⟨236549, by rfl⟩ : syracuseStep 1261597 = 473099) (by norm_num)
theorem B1261633 : Blo 1120629 1261633 := bbase (se 2 (by rfl) ⟨473112, by rfl⟩ : syracuseStep 1261633 = 946225) (by norm_num)
theorem B3784805 : Blo 1120629 3784805 := bbase (se 4 (by rfl) ⟨354825, by rfl⟩ : syracuseStep 3784805 = 709651) (by norm_num)
theorem B1261669 : Blo 1120629 1261669 := bbase (se 4 (by rfl) ⟨118281, by rfl⟩ : syracuseStep 1261669 = 236563) (by norm_num)
theorem B3031157 : Blo 1120629 3031157 := bbase (se 5 (by rfl) ⟨142085, by rfl⟩ : syracuseStep 3031157 = 284171) (by norm_num)
theorem B1261705 : Blo 1120629 1261705 := bbase (se 2 (by rfl) ⟨473139, by rfl⟩ : syracuseStep 1261705 = 946279) (by norm_num)
theorem B23052437 : Blo 1120629 23052437 := bbase (se 6 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 23052437 = 1080583) (by norm_num)
theorem B1917101 : Blo 1120629 1917101 := bbase (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) (by norm_num)
theorem B1261741 : Blo 1120629 1261741 := bbase (se 3 (by rfl) ⟨236576, by rfl⟩ : syracuseStep 1261741 = 473153) (by norm_num)
theorem B1261777 : Blo 1120629 1261777 := bbase (se 2 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 1261777 = 946333) (by norm_num)
theorem B1261813 : Blo 1120629 1261813 := bbase (se 5 (by rfl) ⟨59147, by rfl⟩ : syracuseStep 1261813 = 118295) (by norm_num)
theorem B1753349 : Blo 1120629 1753349 := bbase (se 4 (by rfl) ⟨164376, by rfl⟩ : syracuseStep 1753349 = 328753) (by norm_num)
theorem B5193989 : Blo 1120629 5193989 := bbase (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) (by norm_num)
theorem B1261849 : Blo 1120629 1261849 := bbase (se 2 (by rfl) ⟨473193, by rfl⟩ : syracuseStep 1261849 = 946387) (by norm_num)
theorem B1261885 : Blo 1120629 1261885 := bbase (se 3 (by rfl) ⟨236603, by rfl⟩ : syracuseStep 1261885 = 473207) (by norm_num)
theorem B1261921 : Blo 1120629 1261921 := bbase (se 2 (by rfl) ⟨473220, by rfl⟩ : syracuseStep 1261921 = 946441) (by norm_num)
theorem B1261957 : Blo 1120629 1261957 := bbase (se 4 (by rfl) ⟨118308, by rfl⟩ : syracuseStep 1261957 = 236617) (by norm_num)
theorem B1261993 : Blo 1120629 1261993 := bbase (se 2 (by rfl) ⟨473247, by rfl⟩ : syracuseStep 1261993 = 946495) (by norm_num)
theorem B2277821 : Blo 1120629 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B1262029 : Blo 1120629 1262029 := bbase (se 3 (by rfl) ⟨236630, by rfl⟩ : syracuseStep 1262029 = 473261) (by norm_num)
theorem B1262065 : Blo 1120629 1262065 := bbase (se 2 (by rfl) ⟨473274, by rfl⟩ : syracuseStep 1262065 = 946549) (by norm_num)
theorem B5390837 : Blo 1120629 5390837 := bbase (se 5 (by rfl) ⟨252695, by rfl⟩ : syracuseStep 5390837 = 505391) (by norm_num)
theorem B3785237 : Blo 1120629 3785237 := bbase (se 6 (by rfl) ⟨88716, by rfl⟩ : syracuseStep 3785237 = 177433) (by norm_num)
theorem B1262101 : Blo 1120629 1262101 := bbase (se 6 (by rfl) ⟨29580, by rfl⟩ : syracuseStep 1262101 = 59161) (by norm_num)
theorem B3195413 : Blo 1120629 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B1262137 : Blo 1120629 1262137 := bbase (se 2 (by rfl) ⟨473301, by rfl⟩ : syracuseStep 1262137 = 946603) (by norm_num)
theorem B1262173 : Blo 1120629 1262173 := bbase (se 3 (by rfl) ⟨236657, by rfl⟩ : syracuseStep 1262173 = 473315) (by norm_num)
theorem B1262209 : Blo 1120629 1262209 := bbase (se 2 (by rfl) ⟨473328, by rfl⟩ : syracuseStep 1262209 = 946657) (by norm_num)
theorem B1262245 : Blo 1120629 1262245 := bbase (se 4 (by rfl) ⟨118335, by rfl⟩ : syracuseStep 1262245 = 236671) (by norm_num)
theorem B4670149 : Blo 1120629 4670149 := bbase (se 4 (by rfl) ⟨437826, by rfl⟩ : syracuseStep 4670149 = 875653) (by norm_num)
theorem B1262281 : Blo 1120629 1262281 := bbase (se 2 (by rfl) ⟨473355, by rfl⟩ : syracuseStep 1262281 = 946711) (by norm_num)
theorem B1262317 : Blo 1120629 1262317 := bbase (se 3 (by rfl) ⟨236684, by rfl⟩ : syracuseStep 1262317 = 473369) (by norm_num)
theorem B1196785 : Blo 1120629 1196785 := bbase (se 2 (by rfl) ⟨448794, by rfl⟩ : syracuseStep 1196785 = 897589) (by norm_num)
theorem B4801285 : Blo 1120629 4801285 := bbase (se 4 (by rfl) ⟨450120, by rfl⟩ : syracuseStep 4801285 = 900241) (by norm_num)
theorem B1262353 : Blo 1120629 1262353 := bbase (se 2 (by rfl) ⟨473382, by rfl⟩ : syracuseStep 1262353 = 946765) (by norm_num)
theorem B5686037 : Blo 1120629 5686037 := bbase (se 6 (by rfl) ⟨133266, by rfl⟩ : syracuseStep 5686037 = 266533) (by norm_num)
theorem B1262389 : Blo 1120629 1262389 := bbase (se 5 (by rfl) ⟨59174, by rfl⟩ : syracuseStep 1262389 = 118349) (by norm_num)
theorem B1262425 : Blo 1120629 1262425 := bbase (se 2 (by rfl) ⟨473409, by rfl⟩ : syracuseStep 1262425 = 946819) (by norm_num)
theorem B1262461 : Blo 1120629 1262461 := bbase (se 3 (by rfl) ⟨236711, by rfl⟩ : syracuseStep 1262461 = 473423) (by norm_num)
theorem B1262497 : Blo 1120629 1262497 := bbase (se 2 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 1262497 = 946873) (by norm_num)
theorem B3785669 : Blo 1120629 3785669 := bbase (se 4 (by rfl) ⟨354906, by rfl⟩ : syracuseStep 3785669 = 709813) (by norm_num)
theorem B1262533 : Blo 1120629 1262533 := bbase (se 4 (by rfl) ⟨118362, by rfl⟩ : syracuseStep 1262533 = 236725) (by norm_num)
theorem B3195845 : Blo 1120629 3195845 := bbase (se 4 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 3195845 = 599221) (by norm_num)
theorem B1262569 : Blo 1120629 1262569 := bbase (se 2 (by rfl) ⟨473463, by rfl⟩ : syracuseStep 1262569 = 946927) (by norm_num)
theorem B1262605 : Blo 1120629 1262605 := bbase (se 3 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 1262605 = 473477) (by norm_num)
theorem B1262641 : Blo 1120629 1262641 := bbase (se 2 (by rfl) ⟨473490, by rfl⟩ : syracuseStep 1262641 = 946981) (by norm_num)
theorem B1262677 : Blo 1120629 1262677 := bbase (se 8 (by rfl) ⟨7398, by rfl⟩ : syracuseStep 1262677 = 14797) (by norm_num)
theorem B1262713 : Blo 1120629 1262713 := bbase (se 2 (by rfl) ⟨473517, by rfl⟩ : syracuseStep 1262713 = 947035) (by norm_num)
theorem B1262749 : Blo 1120629 1262749 := bbase (se 3 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 1262749 = 473531) (by norm_num)
theorem B1197229 : Blo 1120629 1197229 := bbase (se 3 (by rfl) ⟨224480, by rfl⟩ : syracuseStep 1197229 = 448961) (by norm_num)
theorem B1262785 : Blo 1120629 1262785 := bbase (se 2 (by rfl) ⟨473544, by rfl⟩ : syracuseStep 1262785 = 947089) (by norm_num)
theorem B1262821 : Blo 1120629 1262821 := bbase (se 4 (by rfl) ⟨118389, by rfl⟩ : syracuseStep 1262821 = 236779) (by norm_num)
theorem B1197289 : Blo 1120629 1197289 := bbase (se 2 (by rfl) ⟨448983, by rfl⟩ : syracuseStep 1197289 = 897967) (by norm_num)
theorem B5391605 : Blo 1120629 5391605 := bbase (se 5 (by rfl) ⟨252731, by rfl⟩ : syracuseStep 5391605 = 505463) (by norm_num)
theorem B1262857 : Blo 1120629 1262857 := bbase (se 2 (by rfl) ⟨473571, by rfl⟩ : syracuseStep 1262857 = 947143) (by norm_num)
theorem B1262893 : Blo 1120629 1262893 := bbase (se 3 (by rfl) ⟨236792, by rfl⟩ : syracuseStep 1262893 = 473585) (by norm_num)
theorem B1262929 : Blo 1120629 1262929 := bbase (se 2 (by rfl) ⟨473598, by rfl⟩ : syracuseStep 1262929 = 947197) (by norm_num)
theorem B3786101 : Blo 1120629 3786101 := bbase (se 5 (by rfl) ⟨177473, by rfl⟩ : syracuseStep 3786101 = 354947) (by norm_num)
theorem B1262965 : Blo 1120629 1262965 := bbase (se 5 (by rfl) ⟨59201, by rfl⟩ : syracuseStep 1262965 = 118403) (by norm_num)
theorem B1263001 : Blo 1120629 1263001 := bbase (se 2 (by rfl) ⟨473625, by rfl⟩ : syracuseStep 1263001 = 947251) (by norm_num)
theorem B1263037 : Blo 1120629 1263037 := bbase (se 3 (by rfl) ⟨236819, by rfl⟩ : syracuseStep 1263037 = 473639) (by norm_num)
theorem B1263073 : Blo 1120629 1263073 := bbase (se 2 (by rfl) ⟨473652, by rfl⟩ : syracuseStep 1263073 = 947305) (by norm_num)
theorem B1263109 : Blo 1120629 1263109 := bbase (se 4 (by rfl) ⟨118416, by rfl⟩ : syracuseStep 1263109 = 236833) (by norm_num)
theorem B1197605 : Blo 1120629 1197605 := bbase (se 4 (by rfl) ⟨112275, by rfl⟩ : syracuseStep 1197605 = 224551) (by norm_num)
theorem B1263145 : Blo 1120629 1263145 := bbase (se 2 (by rfl) ⟨473679, by rfl⟩ : syracuseStep 1263145 = 947359) (by norm_num)
theorem B1263181 : Blo 1120629 1263181 := bbase (se 3 (by rfl) ⟨236846, by rfl⟩ : syracuseStep 1263181 = 473693) (by norm_num)
theorem B1263217 : Blo 1120629 1263217 := bbase (se 2 (by rfl) ⟨473706, by rfl⟩ : syracuseStep 1263217 = 947413) (by norm_num)
theorem B1263253 : Blo 1120629 1263253 := bbase (se 6 (by rfl) ⟨29607, by rfl⟩ : syracuseStep 1263253 = 59215) (by norm_num)
theorem B3196597 : Blo 1120629 3196597 := bbase (se 5 (by rfl) ⟨149840, by rfl⟩ : syracuseStep 3196597 = 299681) (by norm_num)
theorem B1263289 : Blo 1120629 1263289 := bbase (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) (by norm_num)
theorem B2279125 : Blo 1120629 2279125 := bbase (se 7 (by rfl) ⟨26708, by rfl⟩ : syracuseStep 2279125 = 53417) (by norm_num)
theorem B1263325 : Blo 1120629 1263325 := bbase (se 3 (by rfl) ⟨236873, by rfl⟩ : syracuseStep 1263325 = 473747) (by norm_num)
theorem B1263361 : Blo 1120629 1263361 := bbase (se 2 (by rfl) ⟨473760, by rfl⟩ : syracuseStep 1263361 = 947521) (by norm_num)
theorem B3786533 : Blo 1120629 3786533 := bbase (se 4 (by rfl) ⟨354987, by rfl⟩ : syracuseStep 3786533 = 709975) (by norm_num)
theorem B1263397 : Blo 1120629 1263397 := bbase (se 4 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 1263397 = 236887) (by norm_num)
theorem B1263433 : Blo 1120629 1263433 := bbase (se 2 (by rfl) ⟨473787, by rfl⟩ : syracuseStep 1263433 = 947575) (by norm_num)
theorem B1263469 : Blo 1120629 1263469 := bbase (se 3 (by rfl) ⟨236900, by rfl⟩ : syracuseStep 1263469 = 473801) (by norm_num)
theorem B1263505 : Blo 1120629 1263505 := bbase (se 2 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 1263505 = 947629) (by norm_num)
theorem B1263541 : Blo 1120629 1263541 := bbase (se 5 (by rfl) ⟨59228, by rfl⟩ : syracuseStep 1263541 = 118457) (by norm_num)
theorem B1263577 : Blo 1120629 1263577 := bbase (se 2 (by rfl) ⟨473841, by rfl⟩ : syracuseStep 1263577 = 947683) (by norm_num)
theorem B1198049 : Blo 1120629 1198049 := bbase (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) (by norm_num)
theorem B1263613 : Blo 1120629 1263613 := bbase (se 3 (by rfl) ⟨236927, by rfl⟩ : syracuseStep 1263613 = 473855) (by norm_num)
theorem B1198109 : Blo 1120629 1198109 := bbase (se 3 (by rfl) ⟨224645, by rfl⟩ : syracuseStep 1198109 = 449291) (by norm_num)
theorem B1263649 : Blo 1120629 1263649 := bbase (se 2 (by rfl) ⟨473868, by rfl⟩ : syracuseStep 1263649 = 947737) (by norm_num)
theorem B5687333 : Blo 1120629 5687333 := bbase (se 4 (by rfl) ⟨533187, by rfl⟩ : syracuseStep 5687333 = 1066375) (by norm_num)
theorem B1263685 : Blo 1120629 1263685 := bbase (se 4 (by rfl) ⟨118470, by rfl⟩ : syracuseStep 1263685 = 236941) (by norm_num)
theorem B1263721 : Blo 1120629 1263721 := bbase (se 2 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 1263721 = 947791) (by norm_num)
theorem B1263757 : Blo 1120629 1263757 := bbase (se 3 (by rfl) ⟨236954, by rfl⟩ : syracuseStep 1263757 = 473909) (by norm_num)
theorem B1198237 : Blo 1120629 1198237 := bbase (se 3 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 1198237 = 449339) (by norm_num)
theorem B1263793 : Blo 1120629 1263793 := bbase (se 2 (by rfl) ⟨473922, by rfl⟩ : syracuseStep 1263793 = 947845) (by norm_num)
theorem B3786965 : Blo 1120629 3786965 := bbase (se 7 (by rfl) ⟨44378, by rfl⟩ : syracuseStep 3786965 = 88757) (by norm_num)
theorem B1263829 : Blo 1120629 1263829 := bbase (se 7 (by rfl) ⟨14810, by rfl⟩ : syracuseStep 1263829 = 29621) (by norm_num)
theorem B4802773 : Blo 1120629 4802773 := bbase (se 7 (by rfl) ⟨56282, by rfl⟩ : syracuseStep 4802773 = 112565) (by norm_num)
theorem B4802789 : Blo 1120629 4802789 := bbase (se 4 (by rfl) ⟨450261, by rfl⟩ : syracuseStep 4802789 = 900523) (by norm_num)
theorem B1263865 : Blo 1120629 1263865 := bbase (se 2 (by rfl) ⟨473949, by rfl⟩ : syracuseStep 1263865 = 947899) (by norm_num)
theorem B2836741 : Blo 1120629 2836741 := bbase (se 4 (by rfl) ⟨265944, by rfl⟩ : syracuseStep 2836741 = 531889) (by norm_num)
theorem B1263901 : Blo 1120629 1263901 := bbase (se 3 (by rfl) ⟨236981, by rfl⟩ : syracuseStep 1263901 = 473963) (by norm_num)
theorem B1263937 : Blo 1120629 1263937 := bbase (se 2 (by rfl) ⟨473976, by rfl⟩ : syracuseStep 1263937 = 947953) (by norm_num)
theorem B1263973 : Blo 1120629 1263973 := bbase (se 4 (by rfl) ⟨118497, by rfl⟩ : syracuseStep 1263973 = 236995) (by norm_num)
theorem B2836853 : Blo 1120629 2836853 := bbase (se 5 (by rfl) ⟨132977, by rfl⟩ : syracuseStep 2836853 = 265955) (by norm_num)
theorem B1264009 : Blo 1120629 1264009 := bbase (se 2 (by rfl) ⟨474003, by rfl⟩ : syracuseStep 1264009 = 948007) (by norm_num)
theorem B1264045 : Blo 1120629 1264045 := bbase (se 3 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 1264045 = 474017) (by norm_num)
theorem B1264081 : Blo 1120629 1264081 := bbase (se 2 (by rfl) ⟨474030, by rfl⟩ : syracuseStep 1264081 = 948061) (by norm_num)
theorem B1264117 : Blo 1120629 1264117 := bbase (se 5 (by rfl) ⟨59255, by rfl⟩ : syracuseStep 1264117 = 118511) (by norm_num)
theorem B1264153 : Blo 1120629 1264153 := bbase (se 2 (by rfl) ⟨474057, by rfl⟩ : syracuseStep 1264153 = 948115) (by norm_num)
theorem B2837045 : Blo 1120629 2837045 := bbase (se 5 (by rfl) ⟨132986, by rfl⟩ : syracuseStep 2837045 = 265973) (by norm_num)
theorem B1264189 : Blo 1120629 1264189 := bbase (se 3 (by rfl) ⟨237035, by rfl⟩ : syracuseStep 1264189 = 474071) (by norm_num)
theorem B1198681 : Blo 1120629 1198681 := bbase (se 2 (by rfl) ⟨449505, by rfl⟩ : syracuseStep 1198681 = 899011) (by norm_num)
theorem B1264225 : Blo 1120629 1264225 := bbase (se 2 (by rfl) ⟨474084, by rfl⟩ : syracuseStep 1264225 = 948169) (by norm_num)
theorem B3787397 : Blo 1120629 3787397 := bbase (se 4 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 3787397 = 710137) (by norm_num)
theorem B1264261 : Blo 1120629 1264261 := bbase (se 4 (by rfl) ⟨118524, by rfl⟩ : syracuseStep 1264261 = 237049) (by norm_num)
theorem B1264297 : Blo 1120629 1264297 := bbase (se 2 (by rfl) ⟨474111, by rfl⟩ : syracuseStep 1264297 = 948223) (by norm_num)
theorem B1264333 : Blo 1120629 1264333 := bbase (se 3 (by rfl) ⟨237062, by rfl⟩ : syracuseStep 1264333 = 474125) (by norm_num)
theorem B1198801 : Blo 1120629 1198801 := bbase (se 2 (by rfl) ⟨449550, by rfl⟩ : syracuseStep 1198801 = 899101) (by norm_num)
theorem B1264369 : Blo 1120629 1264369 := bbase (se 2 (by rfl) ⟨474138, by rfl⟩ : syracuseStep 1264369 = 948277) (by norm_num)
theorem B1264405 : Blo 1120629 1264405 := bbase (se 6 (by rfl) ⟨29634, by rfl⟩ : syracuseStep 1264405 = 59269) (by norm_num)
theorem B3033893 : Blo 1120629 3033893 := bbase (se 4 (by rfl) ⟨284427, by rfl⟩ : syracuseStep 3033893 = 568855) (by norm_num)
theorem B1264441 : Blo 1120629 1264441 := bbase (se 2 (by rfl) ⟨474165, by rfl⟩ : syracuseStep 1264441 = 948331) (by norm_num)
theorem B1264477 : Blo 1120629 1264477 := bbase (se 3 (by rfl) ⟨237089, by rfl⟩ : syracuseStep 1264477 = 474179) (by norm_num)
theorem B1264513 : Blo 1120629 1264513 := bbase (se 2 (by rfl) ⟨474192, by rfl⟩ : syracuseStep 1264513 = 948385) (by norm_num)
theorem B2837389 : Blo 1120629 2837389 := bbase (se 3 (by rfl) ⟨532010, by rfl⟩ : syracuseStep 2837389 = 1064021) (by norm_num)
theorem B2050957 : Blo 1120629 2050957 := bbase (se 3 (by rfl) ⟨384554, by rfl⟩ : syracuseStep 2050957 = 769109) (by norm_num)
theorem B1264549 : Blo 1120629 1264549 := bbase (se 4 (by rfl) ⟨118551, by rfl⟩ : syracuseStep 1264549 = 237103) (by norm_num)
theorem B1264585 : Blo 1120629 1264585 := bbase (se 2 (by rfl) ⟨474219, by rfl⟩ : syracuseStep 1264585 = 948439) (by norm_num)
theorem B1199053 : Blo 1120629 1199053 := bbase (se 3 (by rfl) ⟨224822, by rfl⟩ : syracuseStep 1199053 = 449645) (by norm_num)
theorem B1199057 : Blo 1120629 1199057 := bbase (se 2 (by rfl) ⟨449646, by rfl⟩ : syracuseStep 1199057 = 899293) (by norm_num)
theorem B1264621 : Blo 1120629 1264621 := bbase (se 3 (by rfl) ⟨237116, by rfl⟩ : syracuseStep 1264621 = 474233) (by norm_num)
theorem B8080373 : Blo 1120629 8080373 := bbase (se 5 (by rfl) ⟨378767, by rfl⟩ : syracuseStep 8080373 = 757535) (by norm_num)
theorem B2837501 : Blo 1120629 2837501 := bbase (se 3 (by rfl) ⟨532031, by rfl⟩ : syracuseStep 2837501 = 1064063) (by norm_num)
theorem B1264657 : Blo 1120629 1264657 := bbase (se 2 (by rfl) ⟨474246, by rfl⟩ : syracuseStep 1264657 = 948493) (by norm_num)
theorem B3787829 : Blo 1120629 3787829 := bbase (se 5 (by rfl) ⟨177554, by rfl⟩ : syracuseStep 3787829 = 355109) (by norm_num)
theorem B1264693 : Blo 1120629 1264693 := bbase (se 5 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 1264693 = 118565) (by norm_num)
theorem B1264729 : Blo 1120629 1264729 := bbase (se 2 (by rfl) ⟨474273, by rfl⟩ : syracuseStep 1264729 = 948547) (by norm_num)
theorem B1264765 : Blo 1120629 1264765 := bbase (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) (by norm_num)
theorem B3591317 : Blo 1120629 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B1264801 : Blo 1120629 1264801 := bbase (se 2 (by rfl) ⟨474300, by rfl⟩ : syracuseStep 1264801 = 948601) (by norm_num)
theorem B2837693 : Blo 1120629 2837693 := bbase (se 3 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 2837693 = 1064135) (by norm_num)
theorem B1264837 : Blo 1120629 1264837 := bbase (se 4 (by rfl) ⟨118578, by rfl⟩ : syracuseStep 1264837 = 237157) (by norm_num)
theorem B36457685 : Blo 1120629 36457685 := bbase (se 7 (by rfl) ⟨427238, by rfl⟩ : syracuseStep 36457685 = 854477) (by norm_num)
theorem B1264873 : Blo 1120629 1264873 := bbase (se 2 (by rfl) ⟨474327, by rfl⟩ : syracuseStep 1264873 = 948655) (by norm_num)
theorem B1264909 : Blo 1120629 1264909 := bbase (se 3 (by rfl) ⟨237170, by rfl⟩ : syracuseStep 1264909 = 474341) (by norm_num)
theorem B1264945 : Blo 1120629 1264945 := bbase (se 2 (by rfl) ⟨474354, by rfl⟩ : syracuseStep 1264945 = 948709) (by norm_num)
theorem B5688629 : Blo 1120629 5688629 := bbase (se 5 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 5688629 = 533309) (by norm_num)
theorem B1264981 : Blo 1120629 1264981 := bbase (se 11 (by rfl) ⟨926, by rfl⟩ : syracuseStep 1264981 = 1853) (by norm_num)
theorem B1265017 : Blo 1120629 1265017 := bbase (se 2 (by rfl) ⟨474381, by rfl⟩ : syracuseStep 1265017 = 948763) (by norm_num)
theorem B1265053 : Blo 1120629 1265053 := bbase (se 3 (by rfl) ⟨237197, by rfl⟩ : syracuseStep 1265053 = 474395) (by norm_num)
theorem B1265089 : Blo 1120629 1265089 := bbase (se 2 (by rfl) ⟨474408, by rfl⟩ : syracuseStep 1265089 = 948817) (by norm_num)
theorem B3788261 : Blo 1120629 3788261 := bbase (se 4 (by rfl) ⟨355149, by rfl⟩ : syracuseStep 3788261 = 710299) (by norm_num)
theorem B1265125 : Blo 1120629 1265125 := bbase (se 4 (by rfl) ⟨118605, by rfl⟩ : syracuseStep 1265125 = 237211) (by norm_num)
theorem B7687669 : Blo 1120629 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B1199621 : Blo 1120629 1199621 := bbase (se 4 (by rfl) ⟨112464, by rfl⟩ : syracuseStep 1199621 = 224929) (by norm_num)
theorem B1265161 : Blo 1120629 1265161 := bbase (se 2 (by rfl) ⟨474435, by rfl⟩ : syracuseStep 1265161 = 948871) (by norm_num)
theorem B2838037 : Blo 1120629 2838037 := bbase (se 6 (by rfl) ⟨66516, by rfl⟩ : syracuseStep 2838037 = 133033) (by norm_num)
theorem B1265197 : Blo 1120629 1265197 := bbase (se 3 (by rfl) ⟨237224, by rfl⟩ : syracuseStep 1265197 = 474449) (by norm_num)
theorem B2838149 : Blo 1120629 2838149 := bbase (se 4 (by rfl) ⟨266076, by rfl⟩ : syracuseStep 2838149 = 532153) (by norm_num)
theorem B1199809 : Blo 1120629 1199809 := bbase (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) (by norm_num)
theorem B2838341 : Blo 1120629 2838341 := bbase (se 4 (by rfl) ⟨266094, by rfl⟩ : syracuseStep 2838341 = 532189) (by norm_num)
theorem B3788693 : Blo 1120629 3788693 := bbase (se 6 (by rfl) ⟨88797, by rfl⟩ : syracuseStep 3788693 = 177595) (by norm_num)
theorem B7196597 : Blo 1120629 7196597 := bbase (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) (by norm_num)
theorem B2838685 : Blo 1120629 2838685 := bbase (se 3 (by rfl) ⟨532253, by rfl⟩ : syracuseStep 2838685 = 1064507) (by norm_num)
theorem B2838797 : Blo 1120629 2838797 := bbase (se 3 (by rfl) ⟨532274, by rfl⟩ : syracuseStep 2838797 = 1064549) (by norm_num)
theorem B6836501 : Blo 1120629 6836501 := bbase (se 6 (by rfl) ⟨160230, by rfl⟩ : syracuseStep 6836501 = 320461) (by norm_num)
theorem B3789125 : Blo 1120629 3789125 := bbase (se 4 (by rfl) ⟨355230, by rfl⟩ : syracuseStep 3789125 = 710461) (by norm_num)
theorem B2838989 : Blo 1120629 2838989 := bbase (se 3 (by rfl) ⟨532310, by rfl⟩ : syracuseStep 2838989 = 1064621) (by norm_num)
theorem B3199445 : Blo 1120629 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B1200629 : Blo 1120629 1200629 := bbase (se 5 (by rfl) ⟨56279, by rfl⟩ : syracuseStep 1200629 = 112559) (by norm_num)
theorem B3330629 : Blo 1120629 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B5689925 : Blo 1120629 5689925 := bbase (se 4 (by rfl) ⟨533430, by rfl⟩ : syracuseStep 5689925 = 1066861) (by norm_num)
theorem B12145301 : Blo 1120629 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B3789557 : Blo 1120629 3789557 := bbase (se 5 (by rfl) ⟨177635, by rfl⟩ : syracuseStep 3789557 = 355271) (by norm_num)
theorem B3035893 : Blo 1120629 3035893 := bbase (se 5 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 3035893 = 284615) (by norm_num)
theorem B2839333 : Blo 1120629 2839333 := bbase (se 4 (by rfl) ⟨266187, by rfl⟩ : syracuseStep 2839333 = 532375) (by norm_num)
theorem B2839445 : Blo 1120629 2839445 := bbase (se 6 (by rfl) ⟨66549, by rfl⟩ : syracuseStep 2839445 = 133099) (by norm_num)
theorem B3593173 : Blo 1120629 3593173 := bbase (se 7 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 3593173 = 84215) (by norm_num)
theorem B2839637 : Blo 1120629 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B1365157 : Blo 1120629 1365157 := bbase (se 4 (by rfl) ⟨127983, by rfl⟩ : syracuseStep 1365157 = 255967) (by norm_num)
theorem B3789989 : Blo 1120629 3789989 := bbase (se 4 (by rfl) ⟨355311, by rfl⟩ : syracuseStep 3789989 = 710623) (by norm_num)
theorem B2839981 : Blo 1120629 2839981 := bbase (se 3 (by rfl) ⟨532496, by rfl⟩ : syracuseStep 2839981 = 1064993) (by norm_num)
theorem B1299925 : Blo 1120629 1299925 := bbase (se 7 (by rfl) ⟨15233, by rfl⟩ : syracuseStep 1299925 = 30467) (by norm_num)
theorem B4052501 : Blo 1120629 4052501 := bbase (se 6 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 4052501 = 189961) (by norm_num)
theorem B2840093 : Blo 1120629 2840093 := bbase (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) (by norm_num)
theorem B1922629 : Blo 1120629 1922629 := bbase (se 4 (by rfl) ⟨180246, by rfl⟩ : syracuseStep 1922629 = 360493) (by norm_num)
theorem B3790421 : Blo 1120629 3790421 := bbase (se 8 (by rfl) ⟨22209, by rfl⟩ : syracuseStep 3790421 = 44419) (by norm_num)
theorem B3036757 : Blo 1120629 3036757 := bbase (se 8 (by rfl) ⟨17793, by rfl⟩ : syracuseStep 3036757 = 35587) (by norm_num)
theorem B3200629 : Blo 1120629 3200629 := bbase (se 5 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 3200629 = 300059) (by norm_num)
theorem B2840285 : Blo 1120629 2840285 := bbase (se 3 (by rfl) ⟨532553, by rfl⟩ : syracuseStep 2840285 = 1065107) (by norm_num)
theorem B3200789 : Blo 1120629 3200789 := bbase (se 6 (by rfl) ⟨75018, by rfl⟩ : syracuseStep 3200789 = 150037) (by norm_num)
theorem B5691221 : Blo 1120629 5691221 := bbase (se 9 (by rfl) ⟨16673, by rfl⟩ : syracuseStep 5691221 = 33347) (by norm_num)
theorem B2021333 : Blo 1120629 2021333 := bbase (se 7 (by rfl) ⟨23687, by rfl⟩ : syracuseStep 2021333 = 47375) (by norm_num)
theorem B1366021 : Blo 1120629 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B3790853 : Blo 1120629 3790853 := bbase (se 4 (by rfl) ⟨355392, by rfl⟩ : syracuseStep 3790853 = 710785) (by norm_num)
theorem B3201029 : Blo 1120629 3201029 := bbase (se 4 (by rfl) ⟨300096, by rfl⟩ : syracuseStep 3201029 = 600193) (by norm_num)
theorem B2840629 : Blo 1120629 2840629 := bbase (se 5 (by rfl) ⟨133154, by rfl⟩ : syracuseStep 2840629 = 266309) (by norm_num)
theorem B4053077 : Blo 1120629 4053077 := bbase (se 8 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 4053077 = 47497) (by norm_num)
theorem B1136737 : Blo 1120629 1136737 := bbase (se 2 (by rfl) ⟨426276, by rfl⟩ : syracuseStep 1136737 = 852553) (by norm_num)
theorem B1136773 : Blo 1120629 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B2840741 : Blo 1120629 2840741 := bbase (se 4 (by rfl) ⟨266319, by rfl⟩ : syracuseStep 2840741 = 532639) (by norm_num)
theorem B4544693 : Blo 1120629 4544693 := bbase (se 5 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 4544693 = 426065) (by norm_num)
theorem B3201221 : Blo 1120629 3201221 := bbase (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) (by norm_num)
theorem B2840933 : Blo 1120629 2840933 := bbase (se 4 (by rfl) ⟨266337, by rfl⟩ : syracuseStep 2840933 = 532675) (by norm_num)
theorem B3791285 : Blo 1120629 3791285 := bbase (se 5 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 3791285 = 355433) (by norm_num)
theorem B1137097 : Blo 1120629 1137097 := bbase (se 2 (by rfl) ⟨426411, by rfl⟩ : syracuseStep 1137097 = 852823) (by norm_num)
theorem B3037733 : Blo 1120629 3037733 := bbase (se 4 (by rfl) ⟨284787, by rfl⟩ : syracuseStep 3037733 = 569575) (by norm_num)
theorem B4381253 : Blo 1120629 4381253 := bbase (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) (by norm_num)
theorem B1366681 : Blo 1120629 1366681 := bbase (se 2 (by rfl) ⟨512505, by rfl⟩ : syracuseStep 1366681 = 1025011) (by norm_num)
theorem B1137341 : Blo 1120629 1137341 := bbase (se 3 (by rfl) ⟨213251, by rfl⟩ : syracuseStep 1137341 = 426503) (by norm_num)
theorem B2841277 : Blo 1120629 2841277 := bbase (se 3 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 2841277 = 1065479) (by norm_num)
theorem B1891093 : Blo 1120629 1891093 := bbase (se 6 (by rfl) ⟨44322, by rfl⟩ : syracuseStep 1891093 = 88645) (by norm_num)
theorem B2841389 : Blo 1120629 2841389 := bbase (se 3 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 2841389 = 1065521) (by norm_num)
theorem B3791717 : Blo 1120629 3791717 := bbase (se 4 (by rfl) ⟨355473, by rfl⟩ : syracuseStep 3791717 = 710947) (by norm_num)
theorem B1891181 : Blo 1120629 1891181 := bbase (se 3 (by rfl) ⟨354596, by rfl⟩ : syracuseStep 1891181 = 709193) (by norm_num)
theorem B1596277 : Blo 1120629 1596277 := bbase (se 5 (by rfl) ⟨74825, by rfl⟩ : syracuseStep 1596277 = 149651) (by norm_num)
theorem B1137601 : Blo 1120629 1137601 := bbase (se 2 (by rfl) ⟨426600, by rfl⟩ : syracuseStep 1137601 = 853201) (by norm_num)
theorem B1891309 : Blo 1120629 1891309 := bbase (se 3 (by rfl) ⟨354620, by rfl⟩ : syracuseStep 1891309 = 709241) (by norm_num)
theorem B2841581 : Blo 1120629 2841581 := bbase (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) (by norm_num)
theorem B1137649 : Blo 1120629 1137649 := bbase (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) (by norm_num)
theorem B1891397 : Blo 1120629 1891397 := bbase (se 4 (by rfl) ⟨177318, by rfl⟩ : syracuseStep 1891397 = 354637) (by norm_num)
theorem B5692517 : Blo 1120629 5692517 := bbase (se 4 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 5692517 = 1067347) (by norm_num)
theorem B3202213 : Blo 1120629 3202213 := bbase (se 4 (by rfl) ⟨300207, by rfl⟩ : syracuseStep 3202213 = 600415) (by norm_num)
theorem B1891525 : Blo 1120629 1891525 := bbase (se 4 (by rfl) ⟨177330, by rfl⟩ : syracuseStep 1891525 = 354661) (by norm_num)
theorem B1596613 : Blo 1120629 1596613 := bbase (se 4 (by rfl) ⟨149682, by rfl⟩ : syracuseStep 1596613 = 299365) (by norm_num)
theorem B3792149 : Blo 1120629 3792149 := bbase (se 6 (by rfl) ⟨88878, by rfl⟩ : syracuseStep 3792149 = 177757) (by norm_num)
theorem B1891613 : Blo 1120629 1891613 := bbase (se 3 (by rfl) ⟨354677, by rfl⟩ : syracuseStep 1891613 = 709355) (by norm_num)
theorem B2841925 : Blo 1120629 2841925 := bbase (se 4 (by rfl) ⟨266430, by rfl⟩ : syracuseStep 2841925 = 532861) (by norm_num)
theorem B1891741 : Blo 1120629 1891741 := bbase (se 3 (by rfl) ⟨354701, by rfl⟩ : syracuseStep 1891741 = 709403) (by norm_num)
theorem B1596829 : Blo 1120629 1596829 := bbase (se 3 (by rfl) ⟨299405, by rfl⟩ : syracuseStep 1596829 = 598811) (by norm_num)
theorem B2842037 : Blo 1120629 2842037 := bbase (se 5 (by rfl) ⟨133220, by rfl⟩ : syracuseStep 2842037 = 266441) (by norm_num)
theorem B3071461 : Blo 1120629 3071461 := bbase (se 4 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 3071461 = 575899) (by norm_num)
theorem B1891829 : Blo 1120629 1891829 := bbase (se 5 (by rfl) ⟨88679, by rfl⟩ : syracuseStep 1891829 = 177359) (by norm_num)
theorem B2022941 : Blo 1120629 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B1891957 : Blo 1120629 1891957 := bbase (se 5 (by rfl) ⟨88685, by rfl⟩ : syracuseStep 1891957 = 177371) (by norm_num)
theorem B2842229 : Blo 1120629 2842229 := bbase (se 5 (by rfl) ⟨133229, by rfl⟩ : syracuseStep 2842229 = 266459) (by norm_num)
theorem B5463749 : Blo 1120629 5463749 := bbase (se 4 (by rfl) ⟨512226, by rfl⟩ : syracuseStep 5463749 = 1024453) (by norm_num)
theorem B3792581 : Blo 1120629 3792581 := bbase (se 4 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 3792581 = 711109) (by norm_num)
theorem B1892045 : Blo 1120629 1892045 := bbase (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) (by norm_num)
theorem B1597205 : Blo 1120629 1597205 := bbase (se 6 (by rfl) ⟨37434, by rfl⟩ : syracuseStep 1597205 = 74869) (by norm_num)
theorem B1892173 : Blo 1120629 1892173 := bbase (se 3 (by rfl) ⟨354782, by rfl⟩ : syracuseStep 1892173 = 709565) (by norm_num)
theorem B8511317 : Blo 1120629 8511317 := bbase (se 9 (by rfl) ⟨24935, by rfl⟩ : syracuseStep 8511317 = 49871) (by norm_num)
theorem B2023309 : Blo 1120629 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B1892261 : Blo 1120629 1892261 := bbase (se 4 (by rfl) ⟨177399, by rfl⟩ : syracuseStep 1892261 = 354799) (by norm_num)
theorem B2842573 : Blo 1120629 2842573 := bbase (se 3 (by rfl) ⟨532982, by rfl⟩ : syracuseStep 2842573 = 1065965) (by norm_num)
theorem B1892389 : Blo 1120629 1892389 := bbase (se 4 (by rfl) ⟨177411, by rfl⟩ : syracuseStep 1892389 = 354823) (by norm_num)
theorem B2842685 : Blo 1120629 2842685 := bbase (se 3 (by rfl) ⟨533003, by rfl⟩ : syracuseStep 2842685 = 1066007) (by norm_num)
theorem B3793013 : Blo 1120629 3793013 := bbase (se 5 (by rfl) ⟨177797, by rfl⟩ : syracuseStep 3793013 = 355595) (by norm_num)
theorem B1892477 : Blo 1120629 1892477 := bbase (se 3 (by rfl) ⟨354839, by rfl⟩ : syracuseStep 1892477 = 709679) (by norm_num)
theorem B3039461 : Blo 1120629 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B1892605 : Blo 1120629 1892605 := bbase (se 3 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 1892605 = 709727) (by norm_num)
theorem B2842877 : Blo 1120629 2842877 := bbase (se 3 (by rfl) ⟨533039, by rfl⟩ : syracuseStep 2842877 = 1066079) (by norm_num)
theorem B1892693 : Blo 1120629 1892693 := bbase (se 10 (by rfl) ⟨2772, by rfl⟩ : syracuseStep 1892693 = 5545) (by norm_num)
theorem B1139141 : Blo 1120629 1139141 := bbase (se 4 (by rfl) ⟨106794, by rfl⟩ : syracuseStep 1139141 = 213589) (by norm_num)
theorem B1892821 : Blo 1120629 1892821 := bbase (se 7 (by rfl) ⟨22181, by rfl⟩ : syracuseStep 1892821 = 44363) (by norm_num)
theorem B1139173 : Blo 1120629 1139173 := bbase (se 4 (by rfl) ⟨106797, by rfl⟩ : syracuseStep 1139173 = 213595) (by norm_num)
theorem B3793445 : Blo 1120629 3793445 := bbase (se 4 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 3793445 = 711271) (by norm_num)
theorem B1892909 : Blo 1120629 1892909 := bbase (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) (by norm_num)
theorem B2843221 : Blo 1120629 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B1893037 : Blo 1120629 1893037 := bbase (se 3 (by rfl) ⟨354944, by rfl⟩ : syracuseStep 1893037 = 709889) (by norm_num)
theorem B2843333 : Blo 1120629 2843333 := bbase (se 4 (by rfl) ⟨266562, by rfl⟩ : syracuseStep 2843333 = 533125) (by norm_num)
theorem B8086229 : Blo 1120629 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B1893125 : Blo 1120629 1893125 := bbase (se 4 (by rfl) ⟨177480, by rfl⟩ : syracuseStep 1893125 = 354961) (by norm_num)
theorem B1893253 : Blo 1120629 1893253 := bbase (se 4 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 1893253 = 354985) (by norm_num)
theorem B2843525 : Blo 1120629 2843525 := bbase (se 4 (by rfl) ⟨266580, by rfl⟩ : syracuseStep 2843525 = 533161) (by norm_num)
theorem B3793877 : Blo 1120629 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B1893341 : Blo 1120629 1893341 := bbase (se 3 (by rfl) ⟨355001, by rfl⟩ : syracuseStep 1893341 = 710003) (by norm_num)
theorem B1139689 : Blo 1120629 1139689 := bbase (se 2 (by rfl) ⟨427383, by rfl⟩ : syracuseStep 1139689 = 854767) (by norm_num)
theorem B3597365 : Blo 1120629 3597365 := bbase (se 5 (by rfl) ⟨168626, by rfl⟩ : syracuseStep 3597365 = 337253) (by norm_num)
theorem B1893469 : Blo 1120629 1893469 := bbase (se 3 (by rfl) ⟨355025, by rfl⟩ : syracuseStep 1893469 = 710051) (by norm_num)
theorem B1598629 : Blo 1120629 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B1893557 : Blo 1120629 1893557 := bbase (se 5 (by rfl) ⟨88760, by rfl⟩ : syracuseStep 1893557 = 177521) (by norm_num)
theorem B2843869 : Blo 1120629 2843869 := bbase (se 3 (by rfl) ⟨533225, by rfl⟩ : syracuseStep 2843869 = 1066451) (by norm_num)
theorem B2024693 : Blo 1120629 2024693 := bbase (se 5 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 2024693 = 189815) (by norm_num)
theorem B1893685 : Blo 1120629 1893685 := bbase (se 5 (by rfl) ⟨88766, by rfl⟩ : syracuseStep 1893685 = 177533) (by norm_num)
theorem B2843981 : Blo 1120629 2843981 := bbase (se 3 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 2843981 = 1066493) (by norm_num)
theorem B1795421 : Blo 1120629 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B5399909 : Blo 1120629 5399909 := bbase (se 4 (by rfl) ⟨506241, by rfl⟩ : syracuseStep 5399909 = 1012483) (by norm_num)
theorem B3794309 : Blo 1120629 3794309 := bbase (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) (by norm_num)
theorem B1893773 : Blo 1120629 1893773 := bbase (se 3 (by rfl) ⟨355082, by rfl⟩ : syracuseStep 1893773 = 710165) (by norm_num)
theorem B3237317 : Blo 1120629 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B1893901 : Blo 1120629 1893901 := bbase (se 3 (by rfl) ⟨355106, by rfl⟩ : syracuseStep 1893901 = 710213) (by norm_num)
theorem B2844173 : Blo 1120629 2844173 := bbase (se 3 (by rfl) ⟨533282, by rfl⟩ : syracuseStep 2844173 = 1066565) (by norm_num)
theorem B1893989 : Blo 1120629 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B6383285 : Blo 1120629 6383285 := bbase (se 5 (by rfl) ⟨299216, by rfl⟩ : syracuseStep 6383285 = 598433) (by norm_num)
theorem B4548325 : Blo 1120629 4548325 := bbase (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) (by norm_num)
theorem B1894117 : Blo 1120629 1894117 := bbase (se 4 (by rfl) ⟨177573, by rfl⟩ : syracuseStep 1894117 = 355147) (by norm_num)
theorem B1599221 : Blo 1120629 1599221 := bbase (se 5 (by rfl) ⟨74963, by rfl⟩ : syracuseStep 1599221 = 149927) (by norm_num)
theorem B3794741 : Blo 1120629 3794741 := bbase (se 5 (by rfl) ⟨177878, by rfl⟩ : syracuseStep 3794741 = 355757) (by norm_num)
theorem B1894205 : Blo 1120629 1894205 := bbase (se 3 (by rfl) ⟨355163, by rfl⟩ : syracuseStep 1894205 = 710327) (by norm_num)
theorem B1599301 : Blo 1120629 1599301 := bbase (se 4 (by rfl) ⟨149934, by rfl⟩ : syracuseStep 1599301 = 299869) (by norm_num)
theorem B2844517 : Blo 1120629 2844517 := bbase (se 4 (by rfl) ⟨266673, by rfl⟩ : syracuseStep 2844517 = 533347) (by norm_num)
theorem B1894333 : Blo 1120629 1894333 := bbase (se 3 (by rfl) ⟨355187, by rfl⟩ : syracuseStep 1894333 = 710375) (by norm_num)
theorem B1599421 : Blo 1120629 1599421 := bbase (se 3 (by rfl) ⟨299891, by rfl⟩ : syracuseStep 1599421 = 599783) (by norm_num)
theorem B2844629 : Blo 1120629 2844629 := bbase (se 7 (by rfl) ⟨33335, by rfl⟩ : syracuseStep 2844629 = 66671) (by norm_num)
theorem B1796069 : Blo 1120629 1796069 := bbase (se 4 (by rfl) ⟨168381, by rfl⟩ : syracuseStep 1796069 = 336763) (by norm_num)
theorem B1894421 : Blo 1120629 1894421 := bbase (se 6 (by rfl) ⟨44400, by rfl⟩ : syracuseStep 1894421 = 88801) (by norm_num)
theorem B1599517 : Blo 1120629 1599517 := bbase (se 3 (by rfl) ⟨299909, by rfl⟩ : syracuseStep 1599517 = 599819) (by norm_num)
theorem B1894549 : Blo 1120629 1894549 := bbase (se 6 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 1894549 = 88807) (by norm_num)
theorem B2844821 : Blo 1120629 2844821 := bbase (se 6 (by rfl) ⟨66675, by rfl⟩ : syracuseStep 2844821 = 133351) (by norm_num)
theorem B3795173 : Blo 1120629 3795173 := bbase (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) (by norm_num)
theorem B1894637 : Blo 1120629 1894637 := bbase (se 3 (by rfl) ⟨355244, by rfl⟩ : syracuseStep 1894637 = 710489) (by norm_num)
theorem B4319573 : Blo 1120629 4319573 := bbase (se 10 (by rfl) ⟨6327, by rfl⟩ : syracuseStep 4319573 = 12655) (by norm_num)
theorem B1894765 : Blo 1120629 1894765 := bbase (se 3 (by rfl) ⟨355268, by rfl⟩ : syracuseStep 1894765 = 710537) (by norm_num)
theorem B1894853 : Blo 1120629 1894853 := bbase (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) (by norm_num)
theorem B2845165 : Blo 1120629 2845165 := bbase (se 3 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 2845165 = 1066937) (by norm_num)
theorem B1600013 : Blo 1120629 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B1894981 : Blo 1120629 1894981 := bbase (se 4 (by rfl) ⟨177654, by rfl⟩ : syracuseStep 1894981 = 355309) (by norm_num)
theorem B2845277 : Blo 1120629 2845277 := bbase (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) (by norm_num)
theorem B3795605 : Blo 1120629 3795605 := bbase (se 6 (by rfl) ⟨88959, by rfl⟩ : syracuseStep 3795605 = 177919) (by norm_num)
theorem B1895069 : Blo 1120629 1895069 := bbase (se 3 (by rfl) ⟨355325, by rfl⟩ : syracuseStep 1895069 = 710651) (by norm_num)
theorem B9857749 : Blo 1120629 9857749 := bbase (se 7 (by rfl) ⟨115520, by rfl⟩ : syracuseStep 9857749 = 231041) (by norm_num)
theorem B1895197 : Blo 1120629 1895197 := bbase (se 3 (by rfl) ⟨355349, by rfl⟩ : syracuseStep 1895197 = 710699) (by norm_num)
theorem B2845469 : Blo 1120629 2845469 := bbase (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) (by norm_num)
theorem B1895285 : Blo 1120629 1895285 := bbase (se 5 (by rfl) ⟨88841, by rfl⟩ : syracuseStep 1895285 = 177683) (by norm_num)
theorem B4549541 : Blo 1120629 4549541 := bbase (se 4 (by rfl) ⟨426519, by rfl⟩ : syracuseStep 4549541 = 853039) (by norm_num)
theorem B5401525 : Blo 1120629 5401525 := bbase (se 5 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 5401525 = 506393) (by norm_num)
theorem B1797061 : Blo 1120629 1797061 := bbase (se 4 (by rfl) ⟨168474, by rfl⟩ : syracuseStep 1797061 = 336949) (by norm_num)
theorem B1895413 : Blo 1120629 1895413 := bbase (se 5 (by rfl) ⟨88847, by rfl⟩ : syracuseStep 1895413 = 177695) (by norm_num)
theorem B1600565 : Blo 1120629 1600565 := bbase (se 5 (by rfl) ⟨75026, by rfl⟩ : syracuseStep 1600565 = 150053) (by norm_num)
theorem B1895501 : Blo 1120629 1895501 := bbase (se 3 (by rfl) ⟨355406, by rfl⟩ : syracuseStep 1895501 = 710813) (by norm_num)
theorem B2845813 : Blo 1120629 2845813 := bbase (se 5 (by rfl) ⟨133397, by rfl⟩ : syracuseStep 2845813 = 266795) (by norm_num)
theorem B1141933 : Blo 1120629 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B1895629 : Blo 1120629 1895629 := bbase (se 3 (by rfl) ⟨355430, by rfl⟩ : syracuseStep 1895629 = 710861) (by norm_num)
theorem B2845925 : Blo 1120629 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B1895717 : Blo 1120629 1895717 := bbase (se 4 (by rfl) ⟨177723, by rfl⟩ : syracuseStep 1895717 = 355447) (by norm_num)
theorem B1895741 : Blo 1120629 1895741 := bbase (se 3 (by rfl) ⟨355451, by rfl⟩ : syracuseStep 1895741 = 710903) (by norm_num)
theorem B1797509 : Blo 1120629 1797509 := bbase (se 4 (by rfl) ⟨168516, by rfl⟩ : syracuseStep 1797509 = 337033) (by norm_num)
theorem B9498005 : Blo 1120629 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B1895845 : Blo 1120629 1895845 := bbase (se 4 (by rfl) ⟨177735, by rfl⟩ : syracuseStep 1895845 = 355471) (by norm_num)
theorem B2846117 : Blo 1120629 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B1895933 : Blo 1120629 1895933 := bbase (se 3 (by rfl) ⟨355487, by rfl⟩ : syracuseStep 1895933 = 710975) (by norm_num)
theorem B1797709 : Blo 1120629 1797709 := bbase (se 3 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 1797709 = 674141) (by norm_num)
theorem B1896061 : Blo 1120629 1896061 := bbase (se 3 (by rfl) ⟨355511, by rfl⟩ : syracuseStep 1896061 = 711023) (by norm_num)
theorem B18706133 : Blo 1120629 18706133 := bbase (se 7 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 18706133 = 438425) (by norm_num)
theorem B1896149 : Blo 1120629 1896149 := bbase (se 7 (by rfl) ⟨22220, by rfl⟩ : syracuseStep 1896149 = 44441) (by norm_num)
theorem B7302869 : Blo 1120629 7302869 := bbase (se 7 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 7302869 = 171161) (by norm_num)
theorem B2846461 : Blo 1120629 2846461 := bbase (se 3 (by rfl) ⟨533711, by rfl⟩ : syracuseStep 2846461 = 1067423) (by norm_num)
theorem B3600197 : Blo 1120629 3600197 := bbase (se 4 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 3600197 = 675037) (by norm_num)
theorem B1797965 : Blo 1120629 1797965 := bbase (se 3 (by rfl) ⟨337118, by rfl⟩ : syracuseStep 1797965 = 674237) (by norm_num)
theorem B6385493 : Blo 1120629 6385493 := bbase (se 9 (by rfl) ⟨18707, by rfl⟩ : syracuseStep 6385493 = 37415) (by norm_num)
theorem B1896277 : Blo 1120629 1896277 := bbase (se 9 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 1896277 = 11111) (by norm_num)
theorem B2846573 : Blo 1120629 2846573 := bbase (se 3 (by rfl) ⟨533732, by rfl⟩ : syracuseStep 2846573 = 1067465) (by norm_num)
theorem B1896365 : Blo 1120629 1896365 := bbase (se 3 (by rfl) ⟨355568, by rfl⟩ : syracuseStep 1896365 = 711137) (by norm_num)
theorem B2191301 : Blo 1120629 2191301 := bbase (se 4 (by rfl) ⟨205434, by rfl⟩ : syracuseStep 2191301 = 410869) (by norm_num)
theorem B1896493 : Blo 1120629 1896493 := bbase (se 3 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 1896493 = 711185) (by norm_num)
theorem B1896581 : Blo 1120629 1896581 := bbase (se 4 (by rfl) ⟨177804, by rfl⟩ : syracuseStep 1896581 = 355609) (by norm_num)
theorem B5763269 : Blo 1120629 5763269 := bbase (se 4 (by rfl) ⟨540306, by rfl⟩ : syracuseStep 5763269 = 1080613) (by norm_num)
theorem B1896709 : Blo 1120629 1896709 := bbase (se 4 (by rfl) ⟨177816, by rfl⟩ : syracuseStep 1896709 = 355633) (by norm_num)
theorem B1896797 : Blo 1120629 1896797 := bbase (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) (by norm_num)
theorem B1896925 : Blo 1120629 1896925 := bbase (se 3 (by rfl) ⟨355673, by rfl⟩ : syracuseStep 1896925 = 711347) (by norm_num)
theorem B1897013 : Blo 1120629 1897013 := bbase (se 5 (by rfl) ⟨88922, by rfl⟩ : syracuseStep 1897013 = 177845) (by norm_num)
theorem B1897141 : Blo 1120629 1897141 := bbase (se 5 (by rfl) ⟨88928, by rfl⟩ : syracuseStep 1897141 = 177857) (by norm_num)
theorem B3601093 : Blo 1120629 3601093 := bbase (se 4 (by rfl) ⟨337602, by rfl⟩ : syracuseStep 3601093 = 675205) (by norm_num)
theorem B1897229 : Blo 1120629 1897229 := bbase (se 3 (by rfl) ⟨355730, by rfl⟩ : syracuseStep 1897229 = 711461) (by norm_num)
theorem B1897357 : Blo 1120629 1897357 := bbase (se 3 (by rfl) ⟨355754, by rfl⟩ : syracuseStep 1897357 = 711509) (by norm_num)
theorem B1799093 : Blo 1120629 1799093 := bbase (se 5 (by rfl) ⟨84332, by rfl⟩ : syracuseStep 1799093 = 168665) (by norm_num)
theorem B6157237 : Blo 1120629 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B1897445 : Blo 1120629 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B1897573 : Blo 1120629 1897573 := bbase (se 4 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 1897573 = 355795) (by norm_num)
theorem B4551797 : Blo 1120629 4551797 := bbase (se 5 (by rfl) ⟨213365, by rfl⟩ : syracuseStep 4551797 = 426731) (by norm_num)
theorem B1537165 : Blo 1120629 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B1897661 : Blo 1120629 1897661 := bbase (se 3 (by rfl) ⟨355811, by rfl⟩ : syracuseStep 1897661 = 711623) (by norm_num)
theorem B4256981 : Blo 1120629 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B1897789 : Blo 1120629 1897789 := bbase (se 3 (by rfl) ⟨355835, by rfl⟩ : syracuseStep 1897789 = 711671) (by norm_num)
theorem B2159941 : Blo 1120629 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B1799605 : Blo 1120629 1799605 := bbase (se 5 (by rfl) ⟨84356, by rfl⟩ : syracuseStep 1799605 = 168713) (by norm_num)
theorem B4257269 : Blo 1120629 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B2127541 : Blo 1120629 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B2127701 : Blo 1120629 2127701 := bbase (se 9 (by rfl) ⟨6233, by rfl⟩ : syracuseStep 2127701 = 12467) (by norm_num)
theorem B6059893 : Blo 1120629 6059893 := bbase (se 5 (by rfl) ⟨284057, by rfl⟩ : syracuseStep 6059893 = 568115) (by norm_num)
theorem B1800149 : Blo 1120629 1800149 := bbase (se 7 (by rfl) ⟨21095, by rfl⟩ : syracuseStep 1800149 = 42191) (by norm_num)
theorem B2127845 : Blo 1120629 2127845 := bbase (se 4 (by rfl) ⟨199485, by rfl⟩ : syracuseStep 2127845 = 398971) (by norm_num)
theorem B1440001 : Blo 1120629 1440001 := bbase (se 2 (by rfl) ⟨540000, by rfl⟩ : syracuseStep 1440001 = 1080001) (by norm_num)
theorem B2128133 : Blo 1120629 2128133 := bbase (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) (by norm_num)
theorem B2881829 : Blo 1120629 2881829 := bbase (se 4 (by rfl) ⟨270171, by rfl⟩ : syracuseStep 2881829 = 540343) (by norm_num)
theorem B2521421 : Blo 1120629 2521421 := bbase (se 3 (by rfl) ⟨472766, by rfl⟩ : syracuseStep 2521421 = 945533) (by norm_num)
theorem B8092021 : Blo 1120629 8092021 := bbase (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) (by norm_num)
theorem B2521493 : Blo 1120629 2521493 := bbase (se 6 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 2521493 = 118195) (by norm_num)
theorem B2128285 : Blo 1120629 2128285 := bbase (se 3 (by rfl) ⟨399053, by rfl⟩ : syracuseStep 2128285 = 798107) (by norm_num)
theorem B2849213 : Blo 1120629 2849213 := bbase (se 3 (by rfl) ⟨534227, by rfl⟩ : syracuseStep 2849213 = 1068455) (by norm_num)
theorem B2521565 : Blo 1120629 2521565 := bbase (se 3 (by rfl) ⟨472793, by rfl⟩ : syracuseStep 2521565 = 945587) (by norm_num)
theorem B1800701 : Blo 1120629 1800701 := bbase (se 3 (by rfl) ⟨337631, by rfl⟩ : syracuseStep 1800701 = 675263) (by norm_num)
theorem B1800733 : Blo 1120629 1800733 := bbase (se 3 (by rfl) ⟨337637, by rfl⟩ : syracuseStep 1800733 = 675275) (by norm_num)
theorem B2521637 : Blo 1120629 2521637 := bbase (se 4 (by rfl) ⟨236403, by rfl⟩ : syracuseStep 2521637 = 472807) (by norm_num)
theorem B5765669 : Blo 1120629 5765669 := bbase (se 4 (by rfl) ⟨540531, by rfl⟩ : syracuseStep 5765669 = 1081063) (by norm_num)
theorem B2521709 : Blo 1120629 2521709 := bbase (se 3 (by rfl) ⟨472820, by rfl⟩ : syracuseStep 2521709 = 945641) (by norm_num)
theorem B4258453 : Blo 1120629 4258453 := bbase (se 6 (by rfl) ⟨99807, by rfl⟩ : syracuseStep 4258453 = 199615) (by norm_num)
theorem B2521781 : Blo 1120629 2521781 := bbase (se 5 (by rfl) ⟨118208, by rfl⟩ : syracuseStep 2521781 = 236417) (by norm_num)
theorem B2128589 : Blo 1120629 2128589 := bbase (se 3 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 2128589 = 798221) (by norm_num)
theorem B2521853 : Blo 1120629 2521853 := bbase (se 3 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 2521853 = 945695) (by norm_num)
theorem B2521925 : Blo 1120629 2521925 := bbase (se 4 (by rfl) ⟨236430, by rfl⟩ : syracuseStep 2521925 = 472861) (by norm_num)
theorem B2521997 : Blo 1120629 2521997 := bbase (se 3 (by rfl) ⟨472874, by rfl⟩ : syracuseStep 2521997 = 945749) (by norm_num)
theorem B4258757 : Blo 1120629 4258757 := bbase (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) (by norm_num)
theorem B2522069 : Blo 1120629 2522069 := bbase (se 7 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 2522069 = 59111) (by norm_num)
theorem B2522141 : Blo 1120629 2522141 := bbase (se 3 (by rfl) ⟨472901, by rfl⟩ : syracuseStep 2522141 = 945803) (by norm_num)
theorem B2522213 : Blo 1120629 2522213 := bbase (se 4 (by rfl) ⟨236457, by rfl⟩ : syracuseStep 2522213 = 472915) (by norm_num)
theorem B2522285 : Blo 1120629 2522285 := bbase (se 3 (by rfl) ⟨472928, by rfl⟩ : syracuseStep 2522285 = 945857) (by norm_num)
theorem B2522357 : Blo 1120629 2522357 := bbase (se 5 (by rfl) ⟨118235, by rfl⟩ : syracuseStep 2522357 = 236471) (by norm_num)
theorem B2522429 : Blo 1120629 2522429 := bbase (se 3 (by rfl) ⟨472955, by rfl⟩ : syracuseStep 2522429 = 945911) (by norm_num)
theorem B2522501 : Blo 1120629 2522501 := bbase (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) (by norm_num)
theorem B8519093 : Blo 1120629 8519093 := bbase (se 5 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 8519093 = 798665) (by norm_num)
theorem B2129341 : Blo 1120629 2129341 := bbase (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) (by norm_num)
theorem B2522573 : Blo 1120629 2522573 := bbase (se 3 (by rfl) ⟨472982, by rfl⟩ : syracuseStep 2522573 = 945965) (by norm_num)
theorem B1539533 : Blo 1120629 1539533 := bbase (se 3 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 1539533 = 577325) (by norm_num)
theorem B2522645 : Blo 1120629 2522645 := bbase (se 6 (by rfl) ⟨59124, by rfl⟩ : syracuseStep 2522645 = 118249) (by norm_num)
theorem B2129485 : Blo 1120629 2129485 := bbase (se 3 (by rfl) ⟨399278, by rfl⟩ : syracuseStep 2129485 = 798557) (by norm_num)
theorem B2522717 : Blo 1120629 2522717 := bbase (se 3 (by rfl) ⟨473009, by rfl⟩ : syracuseStep 2522717 = 946019) (by norm_num)
theorem B14384789 : Blo 1120629 14384789 := bbase (se 6 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 14384789 = 674287) (by norm_num)
theorem B2522789 : Blo 1120629 2522789 := bbase (se 4 (by rfl) ⟨236511, by rfl⟩ : syracuseStep 2522789 = 473023) (by norm_num)
theorem B2522861 : Blo 1120629 2522861 := bbase (se 3 (by rfl) ⟨473036, by rfl⟩ : syracuseStep 2522861 = 946073) (by norm_num)
theorem B2129645 : Blo 1120629 2129645 := bbase (se 3 (by rfl) ⟨399308, by rfl⟩ : syracuseStep 2129645 = 798617) (by norm_num)
theorem B2522933 : Blo 1120629 2522933 := bbase (se 5 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 2522933 = 236525) (by norm_num)
theorem B10944341 : Blo 1120629 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B2523005 : Blo 1120629 2523005 := bbase (se 3 (by rfl) ⟨473063, by rfl⟩ : syracuseStep 2523005 = 946127) (by norm_num)
theorem B2129789 : Blo 1120629 2129789 := bbase (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) (by norm_num)
theorem B2523077 : Blo 1120629 2523077 := bbase (se 4 (by rfl) ⟨236538, by rfl⟩ : syracuseStep 2523077 = 473077) (by norm_num)
theorem B9109493 : Blo 1120629 9109493 := bbase (se 5 (by rfl) ⟨427007, by rfl⟩ : syracuseStep 9109493 = 854015) (by norm_num)
theorem B2523185 : Blo 1120629 2523185 := bstep (se 2 (by rfl) ⟨946194, by rfl⟩ : syracuseStep 2523185 = 1892389) B1892389
theorem B2523203 : Blo 1120629 2523203 := bstep (se 1 (by rfl) ⟨1892402, by rfl⟩ : syracuseStep 2523203 = 3784805) B3784805
theorem B15368291 : Blo 1120629 15368291 := bstep (se 1 (by rfl) ⟨11526218, by rfl⟩ : syracuseStep 15368291 = 23052437) B23052437
theorem B1278067 : Blo 1120629 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B2523473 : Blo 1120629 2523473 := bstep (se 2 (by rfl) ⟨946302, by rfl⟩ : syracuseStep 2523473 = 1892605) B1892605
theorem B2523491 : Blo 1120629 2523491 := bstep (se 1 (by rfl) ⟨1892618, by rfl⟩ : syracuseStep 2523491 = 3785237) B3785237
theorem B2130275 : Blo 1120629 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B6062597 : Blo 1120629 6062597 := bstep (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) B1136737
theorem B15368717 : Blo 1120629 15368717 := bstep (se 3 (by rfl) ⟨2881634, by rfl⟩ : syracuseStep 15368717 = 5763269) B5763269
theorem B2523761 : Blo 1120629 2523761 := bstep (se 2 (by rfl) ⟨946410, by rfl⟩ : syracuseStep 2523761 = 1892821) B1892821
theorem B2523779 : Blo 1120629 2523779 := bstep (se 1 (by rfl) ⟨1892834, by rfl⟩ : syracuseStep 2523779 = 3785669) B3785669
theorem B2130563 : Blo 1120629 2130563 := bstep (se 1 (by rfl) ⟨1597922, by rfl⟩ : syracuseStep 2130563 = 3195845) B3195845
theorem B6062789 : Blo 1120629 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B1704673 : Blo 1120629 1704673 := bstep (se 2 (by rfl) ⟨639252, by rfl⟩ : syracuseStep 1704673 = 1278505) B1278505
theorem B2524049 : Blo 1120629 2524049 := bstep (se 2 (by rfl) ⟨946518, by rfl⟩ : syracuseStep 2524049 = 1893037) B1893037
theorem B2524067 : Blo 1120629 2524067 := bstep (se 1 (by rfl) ⟨1893050, by rfl⟩ : syracuseStep 2524067 = 3786101) B3786101
theorem B6226865 : Blo 1120629 6226865 := bstep (se 2 (by rfl) ⟨2335074, by rfl⟩ : syracuseStep 6226865 = 4670149) B4670149
theorem B2524337 : Blo 1120629 2524337 := bstep (se 2 (by rfl) ⟨946626, by rfl⟩ : syracuseStep 2524337 = 1893253) B1893253
theorem B2524355 : Blo 1120629 2524355 := bstep (se 1 (by rfl) ⟨1893266, by rfl⟩ : syracuseStep 2524355 = 3786533) B3786533
theorem B2524625 : Blo 1120629 2524625 := bstep (se 2 (by rfl) ⟨946734, by rfl⟩ : syracuseStep 2524625 = 1893469) B1893469
theorem B2524643 : Blo 1120629 2524643 := bstep (se 1 (by rfl) ⟨1893482, by rfl⟩ : syracuseStep 2524643 = 3786965) B3786965
theorem B2131505 : Blo 1120629 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B2524913 : Blo 1120629 2524913 := bstep (se 2 (by rfl) ⟨946842, by rfl⟩ : syracuseStep 2524913 = 1893685) B1893685
theorem B2524931 : Blo 1120629 2524931 := bstep (se 1 (by rfl) ⟨1893698, by rfl⟩ : syracuseStep 2524931 = 3787397) B3787397
theorem B2525201 : Blo 1120629 2525201 := bstep (se 2 (by rfl) ⟨946950, by rfl⟩ : syracuseStep 2525201 = 1893901) B1893901
theorem B2525219 : Blo 1120629 2525219 := bstep (se 1 (by rfl) ⟨1893914, by rfl⟩ : syracuseStep 2525219 = 3787829) B3787829
theorem B2394211 : Blo 1120629 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B1706177 : Blo 1120629 1706177 := bstep (se 2 (by rfl) ⟨639816, by rfl⟩ : syracuseStep 1706177 = 1279633) B1279633
theorem B4262129 : Blo 1120629 4262129 := bstep (se 2 (by rfl) ⟨1598298, by rfl⟩ : syracuseStep 4262129 = 3196597) B3196597
theorem B6064433 : Blo 1120629 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B2525489 : Blo 1120629 2525489 := bstep (se 2 (by rfl) ⟨947058, by rfl⟩ : syracuseStep 2525489 = 1894117) B1894117
theorem B2525507 : Blo 1120629 2525507 := bstep (se 1 (by rfl) ⟨1894130, by rfl⟩ : syracuseStep 2525507 = 3788261) B3788261
theorem B6064517 : Blo 1120629 6064517 := bstep (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) B1137097
theorem B2132401 : Blo 1120629 2132401 := bstep (se 2 (by rfl) ⟨799650, by rfl⟩ : syracuseStep 2132401 = 1599301) B1599301
theorem B3410513 : Blo 1120629 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B2525777 : Blo 1120629 2525777 := bstep (se 2 (by rfl) ⟨947166, by rfl⟩ : syracuseStep 2525777 = 1894333) B1894333
theorem B2132561 : Blo 1120629 2132561 := bstep (se 2 (by rfl) ⟨799710, by rfl⟩ : syracuseStep 2132561 = 1599421) B1599421
theorem B2525795 : Blo 1120629 2525795 := bstep (se 1 (by rfl) ⟨1894346, by rfl⟩ : syracuseStep 2525795 = 3788693) B3788693
theorem B10521413 : Blo 1120629 10521413 := bstep (se 4 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 10521413 = 1972765) B1972765
theorem B4557667 : Blo 1120629 4557667 := bstep (se 1 (by rfl) ⟨3418250, by rfl⟩ : syracuseStep 4557667 = 6836501) B6836501
theorem B2526065 : Blo 1120629 2526065 := bstep (se 2 (by rfl) ⟨947274, by rfl⟩ : syracuseStep 2526065 = 1894549) B1894549
theorem B2526083 : Blo 1120629 2526083 := bstep (se 1 (by rfl) ⟨1894562, by rfl⟩ : syracuseStep 2526083 = 3789125) B3789125
theorem B2132963 : Blo 1120629 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B8096867 : Blo 1120629 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B6392965 : Blo 1120629 6392965 := bstep (se 4 (by rfl) ⟨599340, by rfl⟩ : syracuseStep 6392965 = 1198681) B1198681
theorem B2526353 : Blo 1120629 2526353 := bstep (se 2 (by rfl) ⟨947382, by rfl⟩ : syracuseStep 2526353 = 1894765) B1894765
theorem B2526371 : Blo 1120629 2526371 := bstep (se 1 (by rfl) ⟨1894778, by rfl⟩ : syracuseStep 2526371 = 3789557) B3789557
theorem B2526641 : Blo 1120629 2526641 := bstep (se 2 (by rfl) ⟨947490, by rfl⟩ : syracuseStep 2526641 = 1894981) B1894981
theorem B2526659 : Blo 1120629 2526659 := bstep (se 1 (by rfl) ⟨1894994, by rfl⟩ : syracuseStep 2526659 = 3789989) B3789989
theorem B13143665 : Blo 1120629 13143665 := bstep (se 2 (by rfl) ⟨4928874, by rfl⟩ : syracuseStep 13143665 = 9857749) B9857749
theorem B4263587 : Blo 1120629 4263587 := bstep (se 1 (by rfl) ⟨3197690, by rfl⟩ : syracuseStep 4263587 = 6395381) B6395381
theorem B2526929 : Blo 1120629 2526929 := bstep (se 2 (by rfl) ⟨947598, by rfl⟩ : syracuseStep 2526929 = 1895197) B1895197
theorem B2526947 : Blo 1120629 2526947 := bstep (se 1 (by rfl) ⟨1895210, by rfl⟩ : syracuseStep 2526947 = 3790421) B3790421
theorem B2133859 : Blo 1120629 2133859 := bstep (se 1 (by rfl) ⟨1600394, by rfl⟩ : syracuseStep 2133859 = 3200789) B3200789
theorem B2396081 : Blo 1120629 2396081 := bstep (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) B1797061
theorem B2527217 : Blo 1120629 2527217 := bstep (se 2 (by rfl) ⟨947706, by rfl⟩ : syracuseStep 2527217 = 1895413) B1895413
theorem B2527235 : Blo 1120629 2527235 := bstep (se 1 (by rfl) ⟨1895426, by rfl⟩ : syracuseStep 2527235 = 3790853) B3790853
theorem B2134019 : Blo 1120629 2134019 := bstep (se 1 (by rfl) ⟨1600514, by rfl⟩ : syracuseStep 2134019 = 3201029) B3201029
theorem B2527505 : Blo 1120629 2527505 := bstep (se 2 (by rfl) ⟨947814, by rfl⟩ : syracuseStep 2527505 = 1895629) B1895629
theorem B2527523 : Blo 1120629 2527523 := bstep (se 1 (by rfl) ⟨1895642, by rfl⟩ : syracuseStep 2527523 = 3791285) B3791285
theorem B2920835 : Blo 1120629 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B2527793 : Blo 1120629 2527793 := bstep (se 2 (by rfl) ⟨947922, by rfl⟩ : syracuseStep 2527793 = 1895845) B1895845
theorem B2527811 : Blo 1120629 2527811 := bstep (se 1 (by rfl) ⟨1895858, by rfl⟩ : syracuseStep 2527811 = 3791717) B3791717
theorem B7180913 : Blo 1120629 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B4264589 : Blo 1120629 4264589 := bstep (se 3 (by rfl) ⟨799610, by rfl⟩ : syracuseStep 4264589 = 1599221) B1599221
theorem B2396945 : Blo 1120629 2396945 := bstep (se 2 (by rfl) ⟨898854, by rfl⟩ : syracuseStep 2396945 = 1797709) B1797709
theorem B2528081 : Blo 1120629 2528081 := bstep (se 2 (by rfl) ⟨948030, by rfl⟩ : syracuseStep 2528081 = 1896061) B1896061
theorem B2528099 : Blo 1120629 2528099 := bstep (se 1 (by rfl) ⟨1896074, by rfl⟩ : syracuseStep 2528099 = 3792149) B3792149
theorem B6394949 : Blo 1120629 6394949 := bstep (se 4 (by rfl) ⟨599526, by rfl⟩ : syracuseStep 6394949 = 1199053) B1199053
theorem B2528369 : Blo 1120629 2528369 := bstep (se 2 (by rfl) ⟨948138, by rfl⟩ : syracuseStep 2528369 = 1896277) B1896277
theorem B3642499 : Blo 1120629 3642499 := bstep (se 1 (by rfl) ⟨2731874, by rfl⟩ : syracuseStep 3642499 = 5463749) B5463749
theorem B2528387 : Blo 1120629 2528387 := bstep (se 1 (by rfl) ⟨1896290, by rfl⟩ : syracuseStep 2528387 = 3792581) B3792581
theorem B5674211 : Blo 1120629 5674211 := bstep (se 1 (by rfl) ⟨4255658, by rfl⟩ : syracuseStep 5674211 = 8511317) B8511317
theorem B2528657 : Blo 1120629 2528657 := bstep (se 2 (by rfl) ⟨948246, by rfl⟩ : syracuseStep 2528657 = 1896493) B1896493
theorem B4789667 : Blo 1120629 4789667 := bstep (se 1 (by rfl) ⟨3592250, by rfl⟩ : syracuseStep 4789667 = 7184501) B7184501
theorem B2528675 : Blo 1120629 2528675 := bstep (se 1 (by rfl) ⟨1896506, by rfl⟩ : syracuseStep 2528675 = 3793013) B3793013
theorem B8525411 : Blo 1120629 8525411 := bstep (se 1 (by rfl) ⟨6394058, by rfl⟩ : syracuseStep 8525411 = 12788117) B12788117
theorem B2528945 : Blo 1120629 2528945 := bstep (se 2 (by rfl) ⟨948354, by rfl⟩ : syracuseStep 2528945 = 1896709) B1896709
theorem B2528963 : Blo 1120629 2528963 := bstep (se 1 (by rfl) ⟨1896722, by rfl⟩ : syracuseStep 2528963 = 3793445) B3793445
theorem B1709795 : Blo 1120629 1709795 := bstep (se 1 (by rfl) ⟨1282346, by rfl⟩ : syracuseStep 1709795 = 2564693) B2564693
theorem B1709923 : Blo 1120629 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B2529233 : Blo 1120629 2529233 := bstep (se 2 (by rfl) ⟨948462, by rfl⟩ : syracuseStep 2529233 = 1896925) B1896925
theorem B2529251 : Blo 1120629 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B5675021 : Blo 1120629 5675021 := bstep (se 3 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 5675021 = 2128133) B2128133
theorem B2398243 : Blo 1120629 2398243 := bstep (se 1 (by rfl) ⟨1798682, by rfl⟩ : syracuseStep 2398243 = 3597365) B3597365
theorem B8198213 : Blo 1120629 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B1349795 : Blo 1120629 1349795 := bstep (se 1 (by rfl) ⟨1012346, by rfl⟩ : syracuseStep 1349795 = 2024693) B2024693
theorem B2529521 : Blo 1120629 2529521 := bstep (se 2 (by rfl) ⟨948570, by rfl⟩ : syracuseStep 2529521 = 1897141) B1897141
theorem B2529539 : Blo 1120629 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B6822193 : Blo 1120629 6822193 := bstep (se 2 (by rfl) ⟨2558322, by rfl⟩ : syracuseStep 6822193 = 5116645) B5116645
theorem B1120643 : Blo 1120629 1120643 := bstep (se 1 (by rfl) ⟨840482, by rfl⟩ : syracuseStep 1120643 = 1680965) B1680965
theorem B1120659 : Blo 1120629 1120659 := bstep (se 1 (by rfl) ⟨840494, by rfl⟩ : syracuseStep 1120659 = 1680989) B1680989
theorem B1120675 : Blo 1120629 1120675 := bstep (se 1 (by rfl) ⟨840506, by rfl⟩ : syracuseStep 1120675 = 1681013) B1681013
theorem B1120691 : Blo 1120629 1120691 := bstep (se 1 (by rfl) ⟨840518, by rfl⟩ : syracuseStep 1120691 = 1681037) B1681037
theorem B1120707 : Blo 1120629 1120707 := bstep (se 1 (by rfl) ⟨840530, by rfl⟩ : syracuseStep 1120707 = 1681061) B1681061
theorem B1120723 : Blo 1120629 1120723 := bstep (se 1 (by rfl) ⟨840542, by rfl⟩ : syracuseStep 1120723 = 1681085) B1681085
theorem B1120739 : Blo 1120629 1120739 := bstep (se 1 (by rfl) ⟨840554, by rfl⟩ : syracuseStep 1120739 = 1681109) B1681109
theorem B1120755 : Blo 1120629 1120755 := bstep (se 1 (by rfl) ⟨840566, by rfl⟩ : syracuseStep 1120755 = 1681133) B1681133
theorem B1120771 : Blo 1120629 1120771 := bstep (se 1 (by rfl) ⟨840578, by rfl⟩ : syracuseStep 1120771 = 1681157) B1681157
theorem B10951181 : Blo 1120629 10951181 := bstep (se 3 (by rfl) ⟨2053346, by rfl⟩ : syracuseStep 10951181 = 4106693) B4106693
theorem B2529809 : Blo 1120629 2529809 := bstep (se 2 (by rfl) ⟨948678, by rfl⟩ : syracuseStep 2529809 = 1897357) B1897357
theorem B1120787 : Blo 1120629 1120787 := bstep (se 1 (by rfl) ⟨840590, by rfl⟩ : syracuseStep 1120787 = 1681181) B1681181
theorem B1120803 : Blo 1120629 1120803 := bstep (se 1 (by rfl) ⟨840602, by rfl⟩ : syracuseStep 1120803 = 1681205) B1681205
theorem B2529827 : Blo 1120629 2529827 := bstep (se 1 (by rfl) ⟨1897370, by rfl⟩ : syracuseStep 2529827 = 3794741) B3794741
theorem B1120819 : Blo 1120629 1120819 := bstep (se 1 (by rfl) ⟨840614, by rfl⟩ : syracuseStep 1120819 = 1681229) B1681229
theorem B1120835 : Blo 1120629 1120835 := bstep (se 1 (by rfl) ⟨840626, by rfl⟩ : syracuseStep 1120835 = 1681253) B1681253
theorem B1120851 : Blo 1120629 1120851 := bstep (se 1 (by rfl) ⟨840638, by rfl⟩ : syracuseStep 1120851 = 1681277) B1681277
theorem B1120867 : Blo 1120629 1120867 := bstep (se 1 (by rfl) ⟨840650, by rfl⟩ : syracuseStep 1120867 = 1681301) B1681301
theorem B10230371 : Blo 1120629 10230371 := bstep (se 1 (by rfl) ⟨7672778, by rfl⟩ : syracuseStep 10230371 = 15345557) B15345557
theorem B4790897 : Blo 1120629 4790897 := bstep (se 2 (by rfl) ⟨1796586, by rfl⟩ : syracuseStep 4790897 = 3593173) B3593173
theorem B1120883 : Blo 1120629 1120883 := bstep (se 1 (by rfl) ⟨840662, by rfl⟩ : syracuseStep 1120883 = 1681325) B1681325
theorem B1645171 : Blo 1120629 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B1120899 : Blo 1120629 1120899 := bstep (se 1 (by rfl) ⟨840674, by rfl⟩ : syracuseStep 1120899 = 1681349) B1681349
theorem B1120915 : Blo 1120629 1120915 := bstep (se 1 (by rfl) ⟨840686, by rfl⟩ : syracuseStep 1120915 = 1681373) B1681373
theorem B1120931 : Blo 1120629 1120931 := bstep (se 1 (by rfl) ⟨840698, by rfl⟩ : syracuseStep 1120931 = 1681397) B1681397
theorem B1120947 : Blo 1120629 1120947 := bstep (se 1 (by rfl) ⟨840710, by rfl⟩ : syracuseStep 1120947 = 1681421) B1681421
theorem B1120963 : Blo 1120629 1120963 := bstep (se 1 (by rfl) ⟨840722, by rfl⟩ : syracuseStep 1120963 = 1681445) B1681445
theorem B4266701 : Blo 1120629 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B1120979 : Blo 1120629 1120979 := bstep (se 1 (by rfl) ⟨840734, by rfl⟩ : syracuseStep 1120979 = 1681469) B1681469
theorem B1120995 : Blo 1120629 1120995 := bstep (se 1 (by rfl) ⟨840746, by rfl⟩ : syracuseStep 1120995 = 1681493) B1681493
theorem B1121011 : Blo 1120629 1121011 := bstep (se 1 (by rfl) ⟨840758, by rfl⟩ : syracuseStep 1121011 = 1681517) B1681517
theorem B1121027 : Blo 1120629 1121027 := bstep (se 1 (by rfl) ⟨840770, by rfl⟩ : syracuseStep 1121027 = 1681541) B1681541
theorem B1121043 : Blo 1120629 1121043 := bstep (se 1 (by rfl) ⟨840782, by rfl⟩ : syracuseStep 1121043 = 1681565) B1681565
theorem B1121059 : Blo 1120629 1121059 := bstep (se 1 (by rfl) ⟨840794, by rfl⟩ : syracuseStep 1121059 = 1681589) B1681589
theorem B2530097 : Blo 1120629 2530097 := bstep (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) B1897573
theorem B1121075 : Blo 1120629 1121075 := bstep (se 1 (by rfl) ⟨840806, by rfl⟩ : syracuseStep 1121075 = 1681613) B1681613
theorem B1121091 : Blo 1120629 1121091 := bstep (se 1 (by rfl) ⟨840818, by rfl⟩ : syracuseStep 1121091 = 1681637) B1681637
theorem B2530115 : Blo 1120629 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B1121107 : Blo 1120629 1121107 := bstep (se 1 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 1121107 = 1681661) B1681661
theorem B1121123 : Blo 1120629 1121123 := bstep (se 1 (by rfl) ⟨840842, by rfl⟩ : syracuseStep 1121123 = 1681685) B1681685
theorem B1121139 : Blo 1120629 1121139 := bstep (se 1 (by rfl) ⟨840854, by rfl⟩ : syracuseStep 1121139 = 1681709) B1681709
theorem B1121155 : Blo 1120629 1121155 := bstep (se 1 (by rfl) ⟨840866, by rfl⟩ : syracuseStep 1121155 = 1681733) B1681733
theorem B1121171 : Blo 1120629 1121171 := bstep (se 1 (by rfl) ⟨840878, by rfl⟩ : syracuseStep 1121171 = 1681757) B1681757
theorem B1121187 : Blo 1120629 1121187 := bstep (se 1 (by rfl) ⟨840890, by rfl⟩ : syracuseStep 1121187 = 1681781) B1681781
theorem B1121203 : Blo 1120629 1121203 := bstep (se 1 (by rfl) ⟨840902, by rfl⟩ : syracuseStep 1121203 = 1681805) B1681805
theorem B1121219 : Blo 1120629 1121219 := bstep (se 1 (by rfl) ⟨840914, by rfl⟩ : syracuseStep 1121219 = 1681829) B1681829
theorem B1121235 : Blo 1120629 1121235 := bstep (se 1 (by rfl) ⟨840926, by rfl⟩ : syracuseStep 1121235 = 1681853) B1681853
theorem B1121251 : Blo 1120629 1121251 := bstep (se 1 (by rfl) ⟨840938, by rfl⟩ : syracuseStep 1121251 = 1681877) B1681877
theorem B12786659 : Blo 1120629 12786659 := bstep (se 1 (by rfl) ⟨9589994, by rfl⟩ : syracuseStep 12786659 = 19179989) B19179989
theorem B1121267 : Blo 1120629 1121267 := bstep (se 1 (by rfl) ⟨840950, by rfl⟩ : syracuseStep 1121267 = 1681901) B1681901
theorem B1121283 : Blo 1120629 1121283 := bstep (se 1 (by rfl) ⟨840962, by rfl⟩ : syracuseStep 1121283 = 1681925) B1681925
theorem B1121299 : Blo 1120629 1121299 := bstep (se 1 (by rfl) ⟨840974, by rfl⟩ : syracuseStep 1121299 = 1681949) B1681949
theorem B2694179 : Blo 1120629 2694179 := bstep (se 1 (by rfl) ⟨2020634, by rfl⟩ : syracuseStep 2694179 = 4041269) B4041269
theorem B1121315 : Blo 1120629 1121315 := bstep (se 1 (by rfl) ⟨840986, by rfl⟩ : syracuseStep 1121315 = 1681973) B1681973
theorem B1121331 : Blo 1120629 1121331 := bstep (se 1 (by rfl) ⟨840998, by rfl⟩ : syracuseStep 1121331 = 1681997) B1681997
theorem B1121347 : Blo 1120629 1121347 := bstep (se 1 (by rfl) ⟨841010, by rfl⟩ : syracuseStep 1121347 = 1682021) B1682021
theorem B2530385 : Blo 1120629 2530385 := bstep (se 2 (by rfl) ⟨948894, by rfl⟩ : syracuseStep 2530385 = 1897789) B1897789
theorem B1121363 : Blo 1120629 1121363 := bstep (se 1 (by rfl) ⟨841022, by rfl⟩ : syracuseStep 1121363 = 1682045) B1682045
theorem B1121379 : Blo 1120629 1121379 := bstep (se 1 (by rfl) ⟨841034, by rfl⟩ : syracuseStep 1121379 = 1682069) B1682069
theorem B2530403 : Blo 1120629 2530403 := bstep (se 1 (by rfl) ⟨1897802, by rfl⟩ : syracuseStep 2530403 = 3795605) B3795605
theorem B1121395 : Blo 1120629 1121395 := bstep (se 1 (by rfl) ⟨841046, by rfl⟩ : syracuseStep 1121395 = 1682093) B1682093
theorem B1121411 : Blo 1120629 1121411 := bstep (se 1 (by rfl) ⟨841058, by rfl⟩ : syracuseStep 1121411 = 1682117) B1682117
theorem B1121427 : Blo 1120629 1121427 := bstep (se 1 (by rfl) ⟨841070, by rfl⟩ : syracuseStep 1121427 = 1682141) B1682141
theorem B1121443 : Blo 1120629 1121443 := bstep (se 1 (by rfl) ⟨841082, by rfl⟩ : syracuseStep 1121443 = 1682165) B1682165
theorem B1121459 : Blo 1120629 1121459 := bstep (se 1 (by rfl) ⟨841094, by rfl⟩ : syracuseStep 1121459 = 1682189) B1682189
theorem B1121475 : Blo 1120629 1121475 := bstep (se 1 (by rfl) ⟨841106, by rfl⟩ : syracuseStep 1121475 = 1682213) B1682213
theorem B1121491 : Blo 1120629 1121491 := bstep (se 1 (by rfl) ⟨841118, by rfl⟩ : syracuseStep 1121491 = 1682237) B1682237
theorem B1121507 : Blo 1120629 1121507 := bstep (se 1 (by rfl) ⟨841130, by rfl⟩ : syracuseStep 1121507 = 1682261) B1682261
theorem B2399473 : Blo 1120629 2399473 := bstep (se 2 (by rfl) ⟨899802, by rfl⟩ : syracuseStep 2399473 = 1799605) B1799605
theorem B1121523 : Blo 1120629 1121523 := bstep (se 1 (by rfl) ⟨841142, by rfl⟩ : syracuseStep 1121523 = 1682285) B1682285
theorem B1121539 : Blo 1120629 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B1121555 : Blo 1120629 1121555 := bstep (se 1 (by rfl) ⟨841166, by rfl⟩ : syracuseStep 1121555 = 1682333) B1682333
theorem B1121571 : Blo 1120629 1121571 := bstep (se 1 (by rfl) ⟨841178, by rfl⟩ : syracuseStep 1121571 = 1682357) B1682357
theorem B1121587 : Blo 1120629 1121587 := bstep (se 1 (by rfl) ⟨841190, by rfl⟩ : syracuseStep 1121587 = 1682381) B1682381
theorem B1121603 : Blo 1120629 1121603 := bstep (se 1 (by rfl) ⟨841202, by rfl⟩ : syracuseStep 1121603 = 1682405) B1682405
theorem B1121619 : Blo 1120629 1121619 := bstep (se 1 (by rfl) ⟨841214, by rfl⟩ : syracuseStep 1121619 = 1682429) B1682429
theorem B9575779 : Blo 1120629 9575779 := bstep (se 1 (by rfl) ⟨7181834, by rfl⟩ : syracuseStep 9575779 = 14363669) B14363669
theorem B1121635 : Blo 1120629 1121635 := bstep (se 1 (by rfl) ⟨841226, by rfl⟩ : syracuseStep 1121635 = 1682453) B1682453
theorem B1121651 : Blo 1120629 1121651 := bstep (se 1 (by rfl) ⟨841238, by rfl⟩ : syracuseStep 1121651 = 1682477) B1682477
theorem B1121667 : Blo 1120629 1121667 := bstep (se 1 (by rfl) ⟨841250, by rfl⟩ : syracuseStep 1121667 = 1682501) B1682501
theorem B1121683 : Blo 1120629 1121683 := bstep (se 1 (by rfl) ⟨841262, by rfl⟩ : syracuseStep 1121683 = 1682525) B1682525
theorem B1121699 : Blo 1120629 1121699 := bstep (se 1 (by rfl) ⟨841274, by rfl⟩ : syracuseStep 1121699 = 1682549) B1682549
theorem B2563505 : Blo 1120629 2563505 := bstep (se 2 (by rfl) ⟨961314, by rfl⟩ : syracuseStep 2563505 = 1922629) B1922629
theorem B1121715 : Blo 1120629 1121715 := bstep (se 1 (by rfl) ⟨841286, by rfl⟩ : syracuseStep 1121715 = 1682573) B1682573
theorem B1121731 : Blo 1120629 1121731 := bstep (se 1 (by rfl) ⟨841298, by rfl⟩ : syracuseStep 1121731 = 1682597) B1682597
theorem B1121747 : Blo 1120629 1121747 := bstep (se 1 (by rfl) ⟨841310, by rfl⟩ : syracuseStep 1121747 = 1682621) B1682621
theorem B1121763 : Blo 1120629 1121763 := bstep (se 1 (by rfl) ⟨841322, by rfl⟩ : syracuseStep 1121763 = 1682645) B1682645
theorem B4267505 : Blo 1120629 4267505 := bstep (se 2 (by rfl) ⟨1600314, by rfl⟩ : syracuseStep 4267505 = 3200629) B3200629
theorem B1121779 : Blo 1120629 1121779 := bstep (se 1 (by rfl) ⟨841334, by rfl⟩ : syracuseStep 1121779 = 1682669) B1682669
theorem B1121795 : Blo 1120629 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B7183885 : Blo 1120629 7183885 := bstep (se 3 (by rfl) ⟨1346978, by rfl⟩ : syracuseStep 7183885 = 2693957) B2693957
theorem B1121811 : Blo 1120629 1121811 := bstep (se 1 (by rfl) ⟨841358, by rfl⟩ : syracuseStep 1121811 = 1682717) B1682717
theorem B1121827 : Blo 1120629 1121827 := bstep (se 1 (by rfl) ⟨841370, by rfl⟩ : syracuseStep 1121827 = 1682741) B1682741
theorem B1121843 : Blo 1120629 1121843 := bstep (se 1 (by rfl) ⟨841382, by rfl⟩ : syracuseStep 1121843 = 1682765) B1682765
theorem B1121859 : Blo 1120629 1121859 := bstep (se 1 (by rfl) ⟨841394, by rfl⟩ : syracuseStep 1121859 = 1682789) B1682789
theorem B1121875 : Blo 1120629 1121875 := bstep (se 1 (by rfl) ⟨841406, by rfl⟩ : syracuseStep 1121875 = 1682813) B1682813
theorem B1121891 : Blo 1120629 1121891 := bstep (se 1 (by rfl) ⟨841418, by rfl⟩ : syracuseStep 1121891 = 1682837) B1682837
theorem B6332003 : Blo 1120629 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B1121907 : Blo 1120629 1121907 := bstep (se 1 (by rfl) ⟨841430, by rfl⟩ : syracuseStep 1121907 = 1682861) B1682861
theorem B1121923 : Blo 1120629 1121923 := bstep (se 1 (by rfl) ⟨841442, by rfl⟩ : syracuseStep 1121923 = 1682885) B1682885
theorem B1121939 : Blo 1120629 1121939 := bstep (se 1 (by rfl) ⟨841454, by rfl⟩ : syracuseStep 1121939 = 1682909) B1682909
theorem B1121955 : Blo 1120629 1121955 := bstep (se 1 (by rfl) ⟨841466, by rfl⟩ : syracuseStep 1121955 = 1682933) B1682933
theorem B1121971 : Blo 1120629 1121971 := bstep (se 1 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 1121971 = 1682957) B1682957
theorem B1121987 : Blo 1120629 1121987 := bstep (se 1 (by rfl) ⟨841490, by rfl⟩ : syracuseStep 1121987 = 1682981) B1682981
theorem B1122003 : Blo 1120629 1122003 := bstep (se 1 (by rfl) ⟨841502, by rfl⟩ : syracuseStep 1122003 = 1683005) B1683005
theorem B1122019 : Blo 1120629 1122019 := bstep (se 1 (by rfl) ⟨841514, by rfl⟩ : syracuseStep 1122019 = 1683029) B1683029
theorem B1122035 : Blo 1120629 1122035 := bstep (se 1 (by rfl) ⟨841526, by rfl⟩ : syracuseStep 1122035 = 1683053) B1683053
theorem B1122051 : Blo 1120629 1122051 := bstep (se 1 (by rfl) ⟨841538, by rfl⟩ : syracuseStep 1122051 = 1683077) B1683077
theorem B12132109 : Blo 1120629 12132109 := bstep (se 3 (by rfl) ⟨2274770, by rfl⟩ : syracuseStep 12132109 = 4549541) B4549541
theorem B1122067 : Blo 1120629 1122067 := bstep (se 1 (by rfl) ⟨841550, by rfl⟩ : syracuseStep 1122067 = 1683101) B1683101
theorem B1122083 : Blo 1120629 1122083 := bstep (se 1 (by rfl) ⟨841562, by rfl⟩ : syracuseStep 1122083 = 1683125) B1683125
theorem B1122099 : Blo 1120629 1122099 := bstep (se 1 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 1122099 = 1683149) B1683149
theorem B1122115 : Blo 1120629 1122115 := bstep (se 1 (by rfl) ⟨841586, by rfl⟩ : syracuseStep 1122115 = 1683173) B1683173
theorem B1122131 : Blo 1120629 1122131 := bstep (se 1 (by rfl) ⟨841598, by rfl⟩ : syracuseStep 1122131 = 1683197) B1683197
theorem B1122147 : Blo 1120629 1122147 := bstep (se 1 (by rfl) ⟨841610, by rfl⟩ : syracuseStep 1122147 = 1683221) B1683221
theorem B1122163 : Blo 1120629 1122163 := bstep (se 1 (by rfl) ⟨841622, by rfl⟩ : syracuseStep 1122163 = 1683245) B1683245
theorem B1515395 : Blo 1120629 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B1122179 : Blo 1120629 1122179 := bstep (se 1 (by rfl) ⟨841634, by rfl⟩ : syracuseStep 1122179 = 1683269) B1683269
theorem B2400131 : Blo 1120629 2400131 := bstep (se 1 (by rfl) ⟨1800098, by rfl⟩ : syracuseStep 2400131 = 3600197) B3600197
theorem B1122195 : Blo 1120629 1122195 := bstep (se 1 (by rfl) ⟨841646, by rfl⟩ : syracuseStep 1122195 = 1683293) B1683293
theorem B1122211 : Blo 1120629 1122211 := bstep (se 1 (by rfl) ⟨841658, by rfl⟩ : syracuseStep 1122211 = 1683317) B1683317
theorem B1122227 : Blo 1120629 1122227 := bstep (se 1 (by rfl) ⟨841670, by rfl⟩ : syracuseStep 1122227 = 1683341) B1683341
theorem B1122243 : Blo 1120629 1122243 := bstep (se 1 (by rfl) ⟨841682, by rfl⟩ : syracuseStep 1122243 = 1683365) B1683365
theorem B1122259 : Blo 1120629 1122259 := bstep (se 1 (by rfl) ⟨841694, by rfl⟩ : syracuseStep 1122259 = 1683389) B1683389
theorem B1122275 : Blo 1120629 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B1122291 : Blo 1120629 1122291 := bstep (se 1 (by rfl) ⟨841718, by rfl⟩ : syracuseStep 1122291 = 1683437) B1683437
theorem B1122307 : Blo 1120629 1122307 := bstep (se 1 (by rfl) ⟨841730, by rfl⟩ : syracuseStep 1122307 = 1683461) B1683461
theorem B1122323 : Blo 1120629 1122323 := bstep (se 1 (by rfl) ⟨841742, by rfl⟩ : syracuseStep 1122323 = 1683485) B1683485
theorem B1122339 : Blo 1120629 1122339 := bstep (se 1 (by rfl) ⟨841754, by rfl⟩ : syracuseStep 1122339 = 1683509) B1683509
theorem B1122355 : Blo 1120629 1122355 := bstep (se 1 (by rfl) ⟨841766, by rfl⟩ : syracuseStep 1122355 = 1683533) B1683533
theorem B1122371 : Blo 1120629 1122371 := bstep (se 1 (by rfl) ⟨841778, by rfl⟩ : syracuseStep 1122371 = 1683557) B1683557
theorem B1122387 : Blo 1120629 1122387 := bstep (se 1 (by rfl) ⟨841790, by rfl⟩ : syracuseStep 1122387 = 1683581) B1683581
theorem B1122403 : Blo 1120629 1122403 := bstep (se 1 (by rfl) ⟨841802, by rfl⟩ : syracuseStep 1122403 = 1683605) B1683605
theorem B1122419 : Blo 1120629 1122419 := bstep (se 1 (by rfl) ⟨841814, by rfl⟩ : syracuseStep 1122419 = 1683629) B1683629
theorem B1122435 : Blo 1120629 1122435 := bstep (se 1 (by rfl) ⟨841826, by rfl⟩ : syracuseStep 1122435 = 1683653) B1683653
theorem B4268173 : Blo 1120629 4268173 := bstep (se 3 (by rfl) ⟨800282, by rfl⟩ : syracuseStep 4268173 = 1600565) B1600565
theorem B1122451 : Blo 1120629 1122451 := bstep (se 1 (by rfl) ⟨841838, by rfl⟩ : syracuseStep 1122451 = 1683677) B1683677
theorem B1122467 : Blo 1120629 1122467 := bstep (se 1 (by rfl) ⟨841850, by rfl⟩ : syracuseStep 1122467 = 1683701) B1683701
theorem B1122483 : Blo 1120629 1122483 := bstep (se 1 (by rfl) ⟨841862, by rfl⟩ : syracuseStep 1122483 = 1683725) B1683725
theorem B1122499 : Blo 1120629 1122499 := bstep (se 1 (by rfl) ⟨841874, by rfl⟩ : syracuseStep 1122499 = 1683749) B1683749
theorem B1122515 : Blo 1120629 1122515 := bstep (se 1 (by rfl) ⟨841886, by rfl⟩ : syracuseStep 1122515 = 1683773) B1683773
theorem B1122531 : Blo 1120629 1122531 := bstep (se 1 (by rfl) ⟨841898, by rfl⟩ : syracuseStep 1122531 = 1683797) B1683797
theorem B1122547 : Blo 1120629 1122547 := bstep (se 1 (by rfl) ⟨841910, by rfl⟩ : syracuseStep 1122547 = 1683821) B1683821
theorem B1122563 : Blo 1120629 1122563 := bstep (se 1 (by rfl) ⟨841922, by rfl⟩ : syracuseStep 1122563 = 1683845) B1683845
theorem B5611789 : Blo 1120629 5611789 := bstep (se 3 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 5611789 = 2104421) B2104421
theorem B1122579 : Blo 1120629 1122579 := bstep (se 1 (by rfl) ⟨841934, by rfl⟩ : syracuseStep 1122579 = 1683869) B1683869
theorem B1122595 : Blo 1120629 1122595 := bstep (se 1 (by rfl) ⟨841946, by rfl⟩ : syracuseStep 1122595 = 1683893) B1683893
theorem B1122611 : Blo 1120629 1122611 := bstep (se 1 (by rfl) ⟨841958, by rfl⟩ : syracuseStep 1122611 = 1683917) B1683917
theorem B1122627 : Blo 1120629 1122627 := bstep (se 1 (by rfl) ⟨841970, by rfl⟩ : syracuseStep 1122627 = 1683941) B1683941
theorem B1122643 : Blo 1120629 1122643 := bstep (se 1 (by rfl) ⟨841982, by rfl⟩ : syracuseStep 1122643 = 1683965) B1683965
theorem B1122659 : Blo 1120629 1122659 := bstep (se 1 (by rfl) ⟨841994, by rfl⟩ : syracuseStep 1122659 = 1683989) B1683989
theorem B1122675 : Blo 1120629 1122675 := bstep (se 1 (by rfl) ⟨842006, by rfl⟩ : syracuseStep 1122675 = 1684013) B1684013
theorem B1122691 : Blo 1120629 1122691 := bstep (se 1 (by rfl) ⟨842018, by rfl⟩ : syracuseStep 1122691 = 1684037) B1684037
theorem B1122707 : Blo 1120629 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B1122723 : Blo 1120629 1122723 := bstep (se 1 (by rfl) ⟨842042, by rfl⟩ : syracuseStep 1122723 = 1684085) B1684085
theorem B1122739 : Blo 1120629 1122739 := bstep (se 1 (by rfl) ⟨842054, by rfl⟩ : syracuseStep 1122739 = 1684109) B1684109
theorem B1122755 : Blo 1120629 1122755 := bstep (se 1 (by rfl) ⟨842066, by rfl⟩ : syracuseStep 1122755 = 1684133) B1684133
theorem B1122771 : Blo 1120629 1122771 := bstep (se 1 (by rfl) ⟨842078, by rfl⟩ : syracuseStep 1122771 = 1684157) B1684157
theorem B1122787 : Blo 1120629 1122787 := bstep (se 1 (by rfl) ⟨842090, by rfl⟩ : syracuseStep 1122787 = 1684181) B1684181
theorem B10789361 : Blo 1120629 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B1122803 : Blo 1120629 1122803 := bstep (se 1 (by rfl) ⟨842102, by rfl⟩ : syracuseStep 1122803 = 1684205) B1684205
theorem B1122819 : Blo 1120629 1122819 := bstep (se 1 (by rfl) ⟨842114, by rfl⟩ : syracuseStep 1122819 = 1684229) B1684229
theorem B1122835 : Blo 1120629 1122835 := bstep (se 1 (by rfl) ⟨842126, by rfl⟩ : syracuseStep 1122835 = 1684253) B1684253
theorem B1122851 : Blo 1120629 1122851 := bstep (se 1 (by rfl) ⟨842138, by rfl⟩ : syracuseStep 1122851 = 1684277) B1684277
theorem B1122867 : Blo 1120629 1122867 := bstep (se 1 (by rfl) ⟨842150, by rfl⟩ : syracuseStep 1122867 = 1684301) B1684301
theorem B1122883 : Blo 1120629 1122883 := bstep (se 1 (by rfl) ⟨842162, by rfl⟩ : syracuseStep 1122883 = 1684325) B1684325
theorem B1122899 : Blo 1120629 1122899 := bstep (se 1 (by rfl) ⟨842174, by rfl⟩ : syracuseStep 1122899 = 1684349) B1684349
theorem B1122915 : Blo 1120629 1122915 := bstep (se 1 (by rfl) ⟨842186, by rfl⟩ : syracuseStep 1122915 = 1684373) B1684373
theorem B1122931 : Blo 1120629 1122931 := bstep (se 1 (by rfl) ⟨842198, by rfl⟩ : syracuseStep 1122931 = 1684397) B1684397
theorem B1122947 : Blo 1120629 1122947 := bstep (se 1 (by rfl) ⟨842210, by rfl⟩ : syracuseStep 1122947 = 1684421) B1684421
theorem B1122963 : Blo 1120629 1122963 := bstep (se 1 (by rfl) ⟨842222, by rfl⟩ : syracuseStep 1122963 = 1684445) B1684445
theorem B1516195 : Blo 1120629 1516195 := bstep (se 1 (by rfl) ⟨1137146, by rfl⟩ : syracuseStep 1516195 = 2274293) B2274293
theorem B1122979 : Blo 1120629 1122979 := bstep (se 1 (by rfl) ⟨842234, by rfl⟩ : syracuseStep 1122979 = 1684469) B1684469
theorem B1122995 : Blo 1120629 1122995 := bstep (se 1 (by rfl) ⟨842246, by rfl⟩ : syracuseStep 1122995 = 1684493) B1684493
theorem B1123011 : Blo 1120629 1123011 := bstep (se 1 (by rfl) ⟨842258, by rfl⟩ : syracuseStep 1123011 = 1684517) B1684517
theorem B2400977 : Blo 1120629 2400977 := bstep (se 2 (by rfl) ⟨900366, by rfl⟩ : syracuseStep 2400977 = 1800733) B1800733
theorem B1123027 : Blo 1120629 1123027 := bstep (se 1 (by rfl) ⟨842270, by rfl⟩ : syracuseStep 1123027 = 1684541) B1684541
theorem B1123043 : Blo 1120629 1123043 := bstep (se 1 (by rfl) ⟨842282, by rfl⟩ : syracuseStep 1123043 = 1684565) B1684565
theorem B1123059 : Blo 1120629 1123059 := bstep (se 1 (by rfl) ⟨842294, by rfl⟩ : syracuseStep 1123059 = 1684589) B1684589
theorem B1123075 : Blo 1120629 1123075 := bstep (se 1 (by rfl) ⟨842306, by rfl⟩ : syracuseStep 1123075 = 1684613) B1684613
theorem B1123091 : Blo 1120629 1123091 := bstep (se 1 (by rfl) ⟨842318, by rfl⟩ : syracuseStep 1123091 = 1684637) B1684637
theorem B1123107 : Blo 1120629 1123107 := bstep (se 1 (by rfl) ⟨842330, by rfl⟩ : syracuseStep 1123107 = 1684661) B1684661
theorem B1123123 : Blo 1120629 1123123 := bstep (se 1 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 1123123 = 1684685) B1684685
theorem B1123139 : Blo 1120629 1123139 := bstep (se 1 (by rfl) ⟨842354, by rfl⟩ : syracuseStep 1123139 = 1684709) B1684709
theorem B6824773 : Blo 1120629 6824773 := bstep (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) B1279645
theorem B6398797 : Blo 1120629 6398797 := bstep (se 3 (by rfl) ⟨1199774, by rfl⟩ : syracuseStep 6398797 = 2399549) B2399549
theorem B1123155 : Blo 1120629 1123155 := bstep (se 1 (by rfl) ⟨842366, by rfl⟩ : syracuseStep 1123155 = 1684733) B1684733
theorem B1123171 : Blo 1120629 1123171 := bstep (se 1 (by rfl) ⟨842378, by rfl⟩ : syracuseStep 1123171 = 1684757) B1684757
theorem B5677937 : Blo 1120629 5677937 := bstep (se 2 (by rfl) ⟨2129226, by rfl⟩ : syracuseStep 5677937 = 4258453) B4258453
theorem B1123187 : Blo 1120629 1123187 := bstep (se 1 (by rfl) ⟨842390, by rfl⟩ : syracuseStep 1123187 = 1684781) B1684781
theorem B1123203 : Blo 1120629 1123203 := bstep (se 1 (by rfl) ⟨842402, by rfl⟩ : syracuseStep 1123203 = 1684805) B1684805
theorem B1123219 : Blo 1120629 1123219 := bstep (se 1 (by rfl) ⟨842414, by rfl⟩ : syracuseStep 1123219 = 1684829) B1684829
theorem B1123235 : Blo 1120629 1123235 := bstep (se 1 (by rfl) ⟨842426, by rfl⟩ : syracuseStep 1123235 = 1684853) B1684853
theorem B4268963 : Blo 1120629 4268963 := bstep (se 1 (by rfl) ⟨3201722, by rfl⟩ : syracuseStep 4268963 = 6403445) B6403445
theorem B1123251 : Blo 1120629 1123251 := bstep (se 1 (by rfl) ⟨842438, by rfl⟩ : syracuseStep 1123251 = 1684877) B1684877
theorem B1123267 : Blo 1120629 1123267 := bstep (se 1 (by rfl) ⟨842450, by rfl⟩ : syracuseStep 1123267 = 1684901) B1684901
theorem B1123283 : Blo 1120629 1123283 := bstep (se 1 (by rfl) ⟨842462, by rfl⟩ : syracuseStep 1123283 = 1684925) B1684925
theorem B1123299 : Blo 1120629 1123299 := bstep (se 1 (by rfl) ⟨842474, by rfl⟩ : syracuseStep 1123299 = 1684949) B1684949
theorem B3417059 : Blo 1120629 3417059 := bstep (se 1 (by rfl) ⟨2562794, by rfl⟩ : syracuseStep 3417059 = 5125589) B5125589
theorem B1123315 : Blo 1120629 1123315 := bstep (se 1 (by rfl) ⟨842486, by rfl⟩ : syracuseStep 1123315 = 1684973) B1684973
theorem B1123331 : Blo 1120629 1123331 := bstep (se 1 (by rfl) ⟨842498, by rfl⟩ : syracuseStep 1123331 = 1684997) B1684997
theorem B4793357 : Blo 1120629 4793357 := bstep (se 3 (by rfl) ⟨898754, by rfl⟩ : syracuseStep 4793357 = 1797509) B1797509
theorem B1123347 : Blo 1120629 1123347 := bstep (se 1 (by rfl) ⟨842510, by rfl⟩ : syracuseStep 1123347 = 1685021) B1685021
theorem B1123363 : Blo 1120629 1123363 := bstep (se 1 (by rfl) ⟨842522, by rfl⟩ : syracuseStep 1123363 = 1685045) B1685045
theorem B1123379 : Blo 1120629 1123379 := bstep (se 1 (by rfl) ⟨842534, by rfl⟩ : syracuseStep 1123379 = 1685069) B1685069
theorem B1123395 : Blo 1120629 1123395 := bstep (se 1 (by rfl) ⟨842546, by rfl⟩ : syracuseStep 1123395 = 1685093) B1685093
theorem B1123411 : Blo 1120629 1123411 := bstep (se 1 (by rfl) ⟨842558, by rfl⟩ : syracuseStep 1123411 = 1685117) B1685117
theorem B1123427 : Blo 1120629 1123427 := bstep (se 1 (by rfl) ⟨842570, by rfl⟩ : syracuseStep 1123427 = 1685141) B1685141
theorem B1123443 : Blo 1120629 1123443 := bstep (se 1 (by rfl) ⟨842582, by rfl⟩ : syracuseStep 1123443 = 1685165) B1685165
theorem B1123459 : Blo 1120629 1123459 := bstep (se 1 (by rfl) ⟨842594, by rfl⟩ : syracuseStep 1123459 = 1685189) B1685189
theorem B6071437 : Blo 1120629 6071437 := bstep (se 3 (by rfl) ⟨1138394, by rfl⟩ : syracuseStep 6071437 = 2276789) B2276789
theorem B1123475 : Blo 1120629 1123475 := bstep (se 1 (by rfl) ⟨842606, by rfl⟩ : syracuseStep 1123475 = 1685213) B1685213
theorem B1123491 : Blo 1120629 1123491 := bstep (se 1 (by rfl) ⟨842618, by rfl⟩ : syracuseStep 1123491 = 1685237) B1685237
theorem B1123507 : Blo 1120629 1123507 := bstep (se 1 (by rfl) ⟨842630, by rfl⟩ : syracuseStep 1123507 = 1685261) B1685261
theorem B13640885 : Blo 1120629 13640885 := bstep (se 5 (by rfl) ⟨639416, by rfl⟩ : syracuseStep 13640885 = 1278833) B1278833
theorem B1123523 : Blo 1120629 1123523 := bstep (se 1 (by rfl) ⟨842642, by rfl⟩ : syracuseStep 1123523 = 1685285) B1685285
theorem B4039885 : Blo 1120629 4039885 := bstep (se 3 (by rfl) ⟨757478, by rfl⟩ : syracuseStep 4039885 = 1514957) B1514957
theorem B4105421 : Blo 1120629 4105421 := bstep (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) B1539533
theorem B1123539 : Blo 1120629 1123539 := bstep (se 1 (by rfl) ⟨842654, by rfl⟩ : syracuseStep 1123539 = 1685309) B1685309
theorem B1418467 : Blo 1120629 1418467 := bstep (se 1 (by rfl) ⟨1063850, by rfl⟩ : syracuseStep 1418467 = 2127701) B2127701
theorem B1123555 : Blo 1120629 1123555 := bstep (se 1 (by rfl) ⟨842666, by rfl⟩ : syracuseStep 1123555 = 1685333) B1685333
theorem B1123571 : Blo 1120629 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B1516801 : Blo 1120629 1516801 := bstep (se 2 (by rfl) ⟨568800, by rfl⟩ : syracuseStep 1516801 = 1137601) B1137601
theorem B1123587 : Blo 1120629 1123587 := bstep (se 1 (by rfl) ⟨842690, by rfl⟩ : syracuseStep 1123587 = 1685381) B1685381
theorem B1123603 : Blo 1120629 1123603 := bstep (se 1 (by rfl) ⟨842702, by rfl⟩ : syracuseStep 1123603 = 1685405) B1685405
theorem B1123619 : Blo 1120629 1123619 := bstep (se 1 (by rfl) ⟨842714, by rfl⟩ : syracuseStep 1123619 = 1685429) B1685429
theorem B1123635 : Blo 1120629 1123635 := bstep (se 1 (by rfl) ⟨842726, by rfl⟩ : syracuseStep 1123635 = 1685453) B1685453
theorem B1516865 : Blo 1120629 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B1418563 : Blo 1120629 1418563 := bstep (se 1 (by rfl) ⟨1063922, by rfl⟩ : syracuseStep 1418563 = 2127845) B2127845
theorem B1123651 : Blo 1120629 1123651 := bstep (se 1 (by rfl) ⟨842738, by rfl⟩ : syracuseStep 1123651 = 1685477) B1685477
theorem B1123667 : Blo 1120629 1123667 := bstep (se 1 (by rfl) ⟨842750, by rfl⟩ : syracuseStep 1123667 = 1685501) B1685501
theorem B1123683 : Blo 1120629 1123683 := bstep (se 1 (by rfl) ⟨842762, by rfl⟩ : syracuseStep 1123683 = 1685525) B1685525
theorem B1123699 : Blo 1120629 1123699 := bstep (se 1 (by rfl) ⟨842774, by rfl⟩ : syracuseStep 1123699 = 1685549) B1685549
theorem B1123715 : Blo 1120629 1123715 := bstep (se 1 (by rfl) ⟨842786, by rfl⟩ : syracuseStep 1123715 = 1685573) B1685573
theorem B1123731 : Blo 1120629 1123731 := bstep (se 1 (by rfl) ⟨842798, by rfl⟩ : syracuseStep 1123731 = 1685597) B1685597
theorem B1516963 : Blo 1120629 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B1123747 : Blo 1120629 1123747 := bstep (se 1 (by rfl) ⟨842810, by rfl⟩ : syracuseStep 1123747 = 1685621) B1685621
theorem B1123763 : Blo 1120629 1123763 := bstep (se 1 (by rfl) ⟨842822, by rfl⟩ : syracuseStep 1123763 = 1685645) B1685645
theorem B1123779 : Blo 1120629 1123779 := bstep (se 1 (by rfl) ⟨842834, by rfl⟩ : syracuseStep 1123779 = 1685669) B1685669
theorem B1123795 : Blo 1120629 1123795 := bstep (se 1 (by rfl) ⟨842846, by rfl⟩ : syracuseStep 1123795 = 1685693) B1685693
theorem B1123811 : Blo 1120629 1123811 := bstep (se 1 (by rfl) ⟨842858, by rfl⟩ : syracuseStep 1123811 = 1685717) B1685717
theorem B1123827 : Blo 1120629 1123827 := bstep (se 1 (by rfl) ⟨842870, by rfl⟩ : syracuseStep 1123827 = 1685741) B1685741
theorem B1123843 : Blo 1120629 1123843 := bstep (se 1 (by rfl) ⟨842882, by rfl⟩ : syracuseStep 1123843 = 1685765) B1685765
theorem B1123859 : Blo 1120629 1123859 := bstep (se 1 (by rfl) ⟨842894, by rfl⟩ : syracuseStep 1123859 = 1685789) B1685789
theorem B1123875 : Blo 1120629 1123875 := bstep (se 1 (by rfl) ⟨842906, by rfl⟩ : syracuseStep 1123875 = 1685813) B1685813
theorem B4269617 : Blo 1120629 4269617 := bstep (se 2 (by rfl) ⟨1601106, by rfl⟩ : syracuseStep 4269617 = 3202213) B3202213
theorem B1680947 : Blo 1120629 1680947 := bstep (se 1 (by rfl) ⟨1260710, by rfl⟩ : syracuseStep 1680947 = 2521421) B2521421
theorem B1123891 : Blo 1120629 1123891 := bstep (se 1 (by rfl) ⟨842918, by rfl⟩ : syracuseStep 1123891 = 1685837) B1685837
theorem B1123907 : Blo 1120629 1123907 := bstep (se 1 (by rfl) ⟨842930, by rfl⟩ : syracuseStep 1123907 = 1685861) B1685861
theorem B1680977 : Blo 1120629 1680977 := bstep (se 2 (by rfl) ⟨630366, by rfl⟩ : syracuseStep 1680977 = 1260733) B1260733
theorem B1123923 : Blo 1120629 1123923 := bstep (se 1 (by rfl) ⟨842942, by rfl⟩ : syracuseStep 1123923 = 1685885) B1685885
theorem B1680995 : Blo 1120629 1680995 := bstep (se 1 (by rfl) ⟨1260746, by rfl⟩ : syracuseStep 1680995 = 2521493) B2521493
theorem B1123939 : Blo 1120629 1123939 := bstep (se 1 (by rfl) ⟨842954, by rfl⟩ : syracuseStep 1123939 = 1685909) B1685909
theorem B1123955 : Blo 1120629 1123955 := bstep (se 1 (by rfl) ⟨842966, by rfl⟩ : syracuseStep 1123955 = 1685933) B1685933
theorem B1681025 : Blo 1120629 1681025 := bstep (se 2 (by rfl) ⟨630384, by rfl⟩ : syracuseStep 1681025 = 1260769) B1260769
theorem B1123971 : Blo 1120629 1123971 := bstep (se 1 (by rfl) ⟨842978, by rfl⟩ : syracuseStep 1123971 = 1685957) B1685957
theorem B1681043 : Blo 1120629 1681043 := bstep (se 1 (by rfl) ⟨1260782, by rfl⟩ : syracuseStep 1681043 = 2521565) B2521565
theorem B1123987 : Blo 1120629 1123987 := bstep (se 1 (by rfl) ⟨842990, by rfl⟩ : syracuseStep 1123987 = 1685981) B1685981
theorem B1124003 : Blo 1120629 1124003 := bstep (se 1 (by rfl) ⟨843002, by rfl⟩ : syracuseStep 1124003 = 1686005) B1686005
theorem B1681073 : Blo 1120629 1681073 := bstep (se 2 (by rfl) ⟨630402, by rfl⟩ : syracuseStep 1681073 = 1260805) B1260805
theorem B1124019 : Blo 1120629 1124019 := bstep (se 1 (by rfl) ⟨843014, by rfl⟩ : syracuseStep 1124019 = 1686029) B1686029
theorem B1681091 : Blo 1120629 1681091 := bstep (se 1 (by rfl) ⟨1260818, by rfl⟩ : syracuseStep 1681091 = 2521637) B2521637
theorem B3843779 : Blo 1120629 3843779 := bstep (se 1 (by rfl) ⟨2882834, by rfl⟩ : syracuseStep 3843779 = 5765669) B5765669
theorem B7186117 : Blo 1120629 7186117 := bstep (se 4 (by rfl) ⟨673698, by rfl⟩ : syracuseStep 7186117 = 1347397) B1347397
theorem B1124035 : Blo 1120629 1124035 := bstep (se 1 (by rfl) ⟨843026, by rfl⟩ : syracuseStep 1124035 = 1686053) B1686053
theorem B1124051 : Blo 1120629 1124051 := bstep (se 1 (by rfl) ⟨843038, by rfl⟩ : syracuseStep 1124051 = 1686077) B1686077
theorem B1681121 : Blo 1120629 1681121 := bstep (se 2 (by rfl) ⟨630420, by rfl⟩ : syracuseStep 1681121 = 1260841) B1260841
theorem B1124067 : Blo 1120629 1124067 := bstep (se 1 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 1124067 = 1686101) B1686101
theorem B1681139 : Blo 1120629 1681139 := bstep (se 1 (by rfl) ⟨1260854, by rfl⟩ : syracuseStep 1681139 = 2521709) B2521709
theorem B1124083 : Blo 1120629 1124083 := bstep (se 1 (by rfl) ⟨843062, by rfl⟩ : syracuseStep 1124083 = 1686125) B1686125
theorem B1124099 : Blo 1120629 1124099 := bstep (se 1 (by rfl) ⟨843074, by rfl⟩ : syracuseStep 1124099 = 1686149) B1686149
theorem B1681169 : Blo 1120629 1681169 := bstep (se 2 (by rfl) ⟨630438, by rfl⟩ : syracuseStep 1681169 = 1260877) B1260877
theorem B1124115 : Blo 1120629 1124115 := bstep (se 1 (by rfl) ⟨843086, by rfl⟩ : syracuseStep 1124115 = 1686173) B1686173
theorem B1681187 : Blo 1120629 1681187 := bstep (se 1 (by rfl) ⟨1260890, by rfl⟩ : syracuseStep 1681187 = 2521781) B2521781
theorem B1124131 : Blo 1120629 1124131 := bstep (se 1 (by rfl) ⟨843098, by rfl⟩ : syracuseStep 1124131 = 1686197) B1686197
theorem B1419059 : Blo 1120629 1419059 := bstep (se 1 (by rfl) ⟨1064294, by rfl⟩ : syracuseStep 1419059 = 2128589) B2128589
theorem B1124147 : Blo 1120629 1124147 := bstep (se 1 (by rfl) ⟨843110, by rfl⟩ : syracuseStep 1124147 = 1686221) B1686221
theorem B1681217 : Blo 1120629 1681217 := bstep (se 2 (by rfl) ⟨630456, by rfl⟩ : syracuseStep 1681217 = 1260913) B1260913
theorem B1124163 : Blo 1120629 1124163 := bstep (se 1 (by rfl) ⟨843122, by rfl⟩ : syracuseStep 1124163 = 1686245) B1686245
theorem B1681235 : Blo 1120629 1681235 := bstep (se 1 (by rfl) ⟨1260926, by rfl⟩ : syracuseStep 1681235 = 2521853) B2521853
theorem B1124179 : Blo 1120629 1124179 := bstep (se 1 (by rfl) ⟨843134, by rfl⟩ : syracuseStep 1124179 = 1686269) B1686269
theorem B1124195 : Blo 1120629 1124195 := bstep (se 1 (by rfl) ⟨843146, by rfl⟩ : syracuseStep 1124195 = 1686293) B1686293
theorem B1681265 : Blo 1120629 1681265 := bstep (se 2 (by rfl) ⟨630474, by rfl⟩ : syracuseStep 1681265 = 1260949) B1260949
theorem B1124211 : Blo 1120629 1124211 := bstep (se 1 (by rfl) ⟨843158, by rfl⟩ : syracuseStep 1124211 = 1686317) B1686317
theorem B1681283 : Blo 1120629 1681283 := bstep (se 1 (by rfl) ⟨1260962, by rfl⟩ : syracuseStep 1681283 = 2521925) B2521925
theorem B1124227 : Blo 1120629 1124227 := bstep (se 1 (by rfl) ⟨843170, by rfl⟩ : syracuseStep 1124227 = 1686341) B1686341
theorem B3417997 : Blo 1120629 3417997 := bstep (se 3 (by rfl) ⟨640874, by rfl⟩ : syracuseStep 3417997 = 1281749) B1281749
theorem B1124243 : Blo 1120629 1124243 := bstep (se 1 (by rfl) ⟨843182, by rfl⟩ : syracuseStep 1124243 = 1686365) B1686365
theorem B1681313 : Blo 1120629 1681313 := bstep (se 2 (by rfl) ⟨630492, by rfl⟩ : syracuseStep 1681313 = 1260985) B1260985
theorem B1124259 : Blo 1120629 1124259 := bstep (se 1 (by rfl) ⟨843194, by rfl⟩ : syracuseStep 1124259 = 1686389) B1686389
theorem B1681331 : Blo 1120629 1681331 := bstep (se 1 (by rfl) ⟨1260998, by rfl⟩ : syracuseStep 1681331 = 2521997) B2521997
theorem B1124275 : Blo 1120629 1124275 := bstep (se 1 (by rfl) ⟨843206, by rfl⟩ : syracuseStep 1124275 = 1686413) B1686413
theorem B1124291 : Blo 1120629 1124291 := bstep (se 1 (by rfl) ⟨843218, by rfl⟩ : syracuseStep 1124291 = 1686437) B1686437
theorem B1681361 : Blo 1120629 1681361 := bstep (se 2 (by rfl) ⟨630510, by rfl⟩ : syracuseStep 1681361 = 1261021) B1261021
theorem B1124307 : Blo 1120629 1124307 := bstep (se 1 (by rfl) ⟨843230, by rfl⟩ : syracuseStep 1124307 = 1686461) B1686461
theorem B1681379 : Blo 1120629 1681379 := bstep (se 1 (by rfl) ⟨1261034, by rfl⟩ : syracuseStep 1681379 = 2522069) B2522069
theorem B1124323 : Blo 1120629 1124323 := bstep (se 1 (by rfl) ⟨843242, by rfl⟩ : syracuseStep 1124323 = 1686485) B1686485
theorem B1124339 : Blo 1120629 1124339 := bstep (se 1 (by rfl) ⟨843254, by rfl⟩ : syracuseStep 1124339 = 1686509) B1686509
theorem B1681409 : Blo 1120629 1681409 := bstep (se 2 (by rfl) ⟨630528, by rfl⟩ : syracuseStep 1681409 = 1261057) B1261057
theorem B1124355 : Blo 1120629 1124355 := bstep (se 1 (by rfl) ⟨843266, by rfl⟩ : syracuseStep 1124355 = 1686533) B1686533
theorem B1681427 : Blo 1120629 1681427 := bstep (se 1 (by rfl) ⟨1261070, by rfl⟩ : syracuseStep 1681427 = 2522141) B2522141
theorem B1124371 : Blo 1120629 1124371 := bstep (se 1 (by rfl) ⟨843278, by rfl⟩ : syracuseStep 1124371 = 1686557) B1686557
theorem B1124387 : Blo 1120629 1124387 := bstep (se 1 (by rfl) ⟨843290, by rfl⟩ : syracuseStep 1124387 = 1686581) B1686581
theorem B1681457 : Blo 1120629 1681457 := bstep (se 2 (by rfl) ⟨630546, by rfl⟩ : syracuseStep 1681457 = 1261093) B1261093
theorem B1124403 : Blo 1120629 1124403 := bstep (se 1 (by rfl) ⟨843302, by rfl⟩ : syracuseStep 1124403 = 1686605) B1686605
theorem B1681475 : Blo 1120629 1681475 := bstep (se 1 (by rfl) ⟨1261106, by rfl⟩ : syracuseStep 1681475 = 2522213) B2522213
theorem B1124419 : Blo 1120629 1124419 := bstep (se 1 (by rfl) ⟨843314, by rfl⟩ : syracuseStep 1124419 = 1686629) B1686629
theorem B1124435 : Blo 1120629 1124435 := bstep (se 1 (by rfl) ⟨843326, by rfl⟩ : syracuseStep 1124435 = 1686653) B1686653
theorem B1681505 : Blo 1120629 1681505 := bstep (se 2 (by rfl) ⟨630564, by rfl⟩ : syracuseStep 1681505 = 1261129) B1261129
theorem B1124451 : Blo 1120629 1124451 := bstep (se 1 (by rfl) ⟨843338, by rfl⟩ : syracuseStep 1124451 = 1686677) B1686677
theorem B1681523 : Blo 1120629 1681523 := bstep (se 1 (by rfl) ⟨1261142, by rfl⟩ : syracuseStep 1681523 = 2522285) B2522285
theorem B1124467 : Blo 1120629 1124467 := bstep (se 1 (by rfl) ⟨843350, by rfl⟩ : syracuseStep 1124467 = 1686701) B1686701
theorem B1124483 : Blo 1120629 1124483 := bstep (se 1 (by rfl) ⟨843362, by rfl⟩ : syracuseStep 1124483 = 1686725) B1686725
theorem B10791053 : Blo 1120629 10791053 := bstep (se 3 (by rfl) ⟨2023322, by rfl⟩ : syracuseStep 10791053 = 4046645) B4046645
theorem B1681553 : Blo 1120629 1681553 := bstep (se 2 (by rfl) ⟨630582, by rfl⟩ : syracuseStep 1681553 = 1261165) B1261165
theorem B1124499 : Blo 1120629 1124499 := bstep (se 1 (by rfl) ⟨843374, by rfl⟩ : syracuseStep 1124499 = 1686749) B1686749
theorem B1681571 : Blo 1120629 1681571 := bstep (se 1 (by rfl) ⟨1261178, by rfl⟩ : syracuseStep 1681571 = 2522357) B2522357
theorem B1124515 : Blo 1120629 1124515 := bstep (se 1 (by rfl) ⟨843386, by rfl⟩ : syracuseStep 1124515 = 1686773) B1686773
theorem B1124531 : Blo 1120629 1124531 := bstep (se 1 (by rfl) ⟨843398, by rfl⟩ : syracuseStep 1124531 = 1686797) B1686797
theorem B1681601 : Blo 1120629 1681601 := bstep (se 2 (by rfl) ⟨630600, by rfl⟩ : syracuseStep 1681601 = 1261201) B1261201
theorem B1124547 : Blo 1120629 1124547 := bstep (se 1 (by rfl) ⟨843410, by rfl⟩ : syracuseStep 1124547 = 1686821) B1686821
theorem B1681619 : Blo 1120629 1681619 := bstep (se 1 (by rfl) ⟨1261214, by rfl⟩ : syracuseStep 1681619 = 2522429) B2522429
theorem B1124563 : Blo 1120629 1124563 := bstep (se 1 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 1124563 = 1686845) B1686845
theorem B1124579 : Blo 1120629 1124579 := bstep (se 1 (by rfl) ⟨843434, by rfl⟩ : syracuseStep 1124579 = 1686869) B1686869
theorem B1681649 : Blo 1120629 1681649 := bstep (se 2 (by rfl) ⟨630618, by rfl⟩ : syracuseStep 1681649 = 1261237) B1261237
theorem B1124595 : Blo 1120629 1124595 := bstep (se 1 (by rfl) ⟨843446, by rfl⟩ : syracuseStep 1124595 = 1686893) B1686893
theorem B1681667 : Blo 1120629 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1124611 : Blo 1120629 1124611 := bstep (se 1 (by rfl) ⟨843458, by rfl⟩ : syracuseStep 1124611 = 1686917) B1686917
theorem B1124627 : Blo 1120629 1124627 := bstep (se 1 (by rfl) ⟨843470, by rfl⟩ : syracuseStep 1124627 = 1686941) B1686941
theorem B1681697 : Blo 1120629 1681697 := bstep (se 2 (by rfl) ⟨630636, by rfl⟩ : syracuseStep 1681697 = 1261273) B1261273
theorem B5679395 : Blo 1120629 5679395 := bstep (se 1 (by rfl) ⟨4259546, by rfl⟩ : syracuseStep 5679395 = 8519093) B8519093
theorem B1681715 : Blo 1120629 1681715 := bstep (se 1 (by rfl) ⟨1261286, by rfl⟩ : syracuseStep 1681715 = 2522573) B2522573
theorem B1681745 : Blo 1120629 1681745 := bstep (se 2 (by rfl) ⟨630654, by rfl⟩ : syracuseStep 1681745 = 1261309) B1261309
theorem B1681763 : Blo 1120629 1681763 := bstep (se 1 (by rfl) ⟨1261322, by rfl⟩ : syracuseStep 1681763 = 2522645) B2522645
theorem B2697571 : Blo 1120629 2697571 := bstep (se 1 (by rfl) ⟨2023178, by rfl⟩ : syracuseStep 2697571 = 4046357) B4046357
theorem B1681793 : Blo 1120629 1681793 := bstep (se 2 (by rfl) ⟨630672, by rfl⟩ : syracuseStep 1681793 = 1261345) B1261345
theorem B1681811 : Blo 1120629 1681811 := bstep (se 1 (by rfl) ⟨1261358, by rfl⟩ : syracuseStep 1681811 = 2522717) B2522717
theorem B1681841 : Blo 1120629 1681841 := bstep (se 2 (by rfl) ⟨630690, by rfl⟩ : syracuseStep 1681841 = 1261381) B1261381
theorem B1681859 : Blo 1120629 1681859 := bstep (se 1 (by rfl) ⟨1261394, by rfl⟩ : syracuseStep 1681859 = 2522789) B2522789
theorem B18196933 : Blo 1120629 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B1681889 : Blo 1120629 1681889 := bstep (se 2 (by rfl) ⟨630708, by rfl⟩ : syracuseStep 1681889 = 1261417) B1261417
theorem B12954097 : Blo 1120629 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B1681907 : Blo 1120629 1681907 := bstep (se 1 (by rfl) ⟨1261430, by rfl⟩ : syracuseStep 1681907 = 2522861) B2522861
theorem B1419763 : Blo 1120629 1419763 := bstep (se 1 (by rfl) ⟨1064822, by rfl⟩ : syracuseStep 1419763 = 2129645) B2129645
theorem B1681937 : Blo 1120629 1681937 := bstep (se 2 (by rfl) ⟨630726, by rfl⟩ : syracuseStep 1681937 = 1261453) B1261453
theorem B2697745 : Blo 1120629 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B1681955 : Blo 1120629 1681955 := bstep (se 1 (by rfl) ⟨1261466, by rfl⟩ : syracuseStep 1681955 = 2522933) B2522933
theorem B1681985 : Blo 1120629 1681985 := bstep (se 2 (by rfl) ⟨630744, by rfl⟩ : syracuseStep 1681985 = 1261489) B1261489
theorem B1682003 : Blo 1120629 1682003 := bstep (se 1 (by rfl) ⟨1261502, by rfl⟩ : syracuseStep 1682003 = 2523005) B2523005
theorem B1419859 : Blo 1120629 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B1682033 : Blo 1120629 1682033 := bstep (se 2 (by rfl) ⟨630762, by rfl⟩ : syracuseStep 1682033 = 1261525) B1261525
theorem B1682051 : Blo 1120629 1682051 := bstep (se 1 (by rfl) ⟨1261538, by rfl⟩ : syracuseStep 1682051 = 2523077) B2523077
theorem B1682081 : Blo 1120629 1682081 := bstep (se 2 (by rfl) ⟨630780, by rfl⟩ : syracuseStep 1682081 = 1261561) B1261561
theorem B6072995 : Blo 1120629 6072995 := bstep (se 1 (by rfl) ⟨4554746, by rfl⟩ : syracuseStep 6072995 = 9109493) B9109493
theorem B3418787 : Blo 1120629 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B1682099 : Blo 1120629 1682099 := bstep (se 1 (by rfl) ⟨1261574, by rfl⟩ : syracuseStep 1682099 = 2523149) B2523149
theorem B1682129 : Blo 1120629 1682129 := bstep (se 2 (by rfl) ⟨630798, by rfl⟩ : syracuseStep 1682129 = 1261597) B1261597
theorem B1682147 : Blo 1120629 1682147 := bstep (se 1 (by rfl) ⟨1261610, by rfl⟩ : syracuseStep 1682147 = 2523221) B2523221
theorem B1682177 : Blo 1120629 1682177 := bstep (se 2 (by rfl) ⟨630816, by rfl⟩ : syracuseStep 1682177 = 1261633) B1261633
theorem B6400781 : Blo 1120629 6400781 := bstep (se 3 (by rfl) ⟨1200146, by rfl⟩ : syracuseStep 6400781 = 2400293) B2400293
theorem B1682195 : Blo 1120629 1682195 := bstep (se 1 (by rfl) ⟨1261646, by rfl⟩ : syracuseStep 1682195 = 2523293) B2523293
theorem B1682225 : Blo 1120629 1682225 := bstep (se 2 (by rfl) ⟨630834, by rfl⟩ : syracuseStep 1682225 = 1261669) B1261669
theorem B1682243 : Blo 1120629 1682243 := bstep (se 1 (by rfl) ⟨1261682, by rfl⟩ : syracuseStep 1682243 = 2523365) B2523365
theorem B8530757 : Blo 1120629 8530757 := bstep (se 4 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 8530757 = 1599517) B1599517
theorem B1682273 : Blo 1120629 1682273 := bstep (se 2 (by rfl) ⟨630852, by rfl⟩ : syracuseStep 1682273 = 1261705) B1261705
theorem B4041571 : Blo 1120629 4041571 := bstep (se 1 (by rfl) ⟨3031178, by rfl⟩ : syracuseStep 4041571 = 6062357) B6062357
theorem B1682291 : Blo 1120629 1682291 := bstep (se 1 (by rfl) ⟨1261718, by rfl⟩ : syracuseStep 1682291 = 2523437) B2523437
theorem B1682321 : Blo 1120629 1682321 := bstep (se 2 (by rfl) ⟨630870, by rfl⟩ : syracuseStep 1682321 = 1261741) B1261741
theorem B1682339 : Blo 1120629 1682339 := bstep (se 1 (by rfl) ⟨1261754, by rfl⟩ : syracuseStep 1682339 = 2523509) B2523509
theorem B1682369 : Blo 1120629 1682369 := bstep (se 2 (by rfl) ⟨630888, by rfl⟩ : syracuseStep 1682369 = 1261777) B1261777
theorem B3845069 : Blo 1120629 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B1682387 : Blo 1120629 1682387 := bstep (se 1 (by rfl) ⟨1261790, by rfl⟩ : syracuseStep 1682387 = 2523581) B2523581
theorem B1682417 : Blo 1120629 1682417 := bstep (se 2 (by rfl) ⟨630906, by rfl⟩ : syracuseStep 1682417 = 1261813) B1261813
theorem B1682435 : Blo 1120629 1682435 := bstep (se 1 (by rfl) ⟨1261826, by rfl⟩ : syracuseStep 1682435 = 2523653) B2523653
theorem B1682465 : Blo 1120629 1682465 := bstep (se 2 (by rfl) ⟨630924, by rfl⟩ : syracuseStep 1682465 = 1261849) B1261849
theorem B1682483 : Blo 1120629 1682483 := bstep (se 1 (by rfl) ⟨1261862, by rfl⟩ : syracuseStep 1682483 = 2523725) B2523725
theorem B1420355 : Blo 1120629 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B5680205 : Blo 1120629 5680205 := bstep (se 3 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 5680205 = 2130077) B2130077
theorem B1682513 : Blo 1120629 1682513 := bstep (se 2 (by rfl) ⟨630942, by rfl⟩ : syracuseStep 1682513 = 1261885) B1261885
theorem B1682531 : Blo 1120629 1682531 := bstep (se 1 (by rfl) ⟨1261898, by rfl⟩ : syracuseStep 1682531 = 2523797) B2523797
theorem B1682561 : Blo 1120629 1682561 := bstep (se 2 (by rfl) ⟨630960, by rfl⟩ : syracuseStep 1682561 = 1261921) B1261921
theorem B1682579 : Blo 1120629 1682579 := bstep (se 1 (by rfl) ⟨1261934, by rfl⟩ : syracuseStep 1682579 = 2523869) B2523869
theorem B1682609 : Blo 1120629 1682609 := bstep (se 2 (by rfl) ⟨630978, by rfl⟩ : syracuseStep 1682609 = 1261957) B1261957
theorem B1682627 : Blo 1120629 1682627 := bstep (se 1 (by rfl) ⟨1261970, by rfl⟩ : syracuseStep 1682627 = 2523941) B2523941
theorem B1682657 : Blo 1120629 1682657 := bstep (se 2 (by rfl) ⟨630996, by rfl⟩ : syracuseStep 1682657 = 1261993) B1261993
theorem B1682675 : Blo 1120629 1682675 := bstep (se 1 (by rfl) ⟨1262006, by rfl⟩ : syracuseStep 1682675 = 2524013) B2524013
theorem B1682705 : Blo 1120629 1682705 := bstep (se 2 (by rfl) ⟨631014, by rfl⟩ : syracuseStep 1682705 = 1262029) B1262029
theorem B1682723 : Blo 1120629 1682723 := bstep (se 1 (by rfl) ⟨1262042, by rfl⟩ : syracuseStep 1682723 = 2524085) B2524085
theorem B1682753 : Blo 1120629 1682753 := bstep (se 2 (by rfl) ⟨631032, by rfl⟩ : syracuseStep 1682753 = 1262065) B1262065
theorem B8105285 : Blo 1120629 8105285 := bstep (se 4 (by rfl) ⟨759870, by rfl⟩ : syracuseStep 8105285 = 1519741) B1519741
theorem B1682771 : Blo 1120629 1682771 := bstep (se 1 (by rfl) ⟨1262078, by rfl⟩ : syracuseStep 1682771 = 2524157) B2524157
theorem B1682801 : Blo 1120629 1682801 := bstep (se 2 (by rfl) ⟨631050, by rfl⟩ : syracuseStep 1682801 = 1262101) B1262101
theorem B1682819 : Blo 1120629 1682819 := bstep (se 1 (by rfl) ⟨1262114, by rfl⟩ : syracuseStep 1682819 = 2524229) B2524229
theorem B1682849 : Blo 1120629 1682849 := bstep (se 2 (by rfl) ⟨631068, by rfl⟩ : syracuseStep 1682849 = 1262137) B1262137
theorem B1682867 : Blo 1120629 1682867 := bstep (se 1 (by rfl) ⟨1262150, by rfl⟩ : syracuseStep 1682867 = 2524301) B2524301
theorem B1682897 : Blo 1120629 1682897 := bstep (se 2 (by rfl) ⟨631086, by rfl⟩ : syracuseStep 1682897 = 1262173) B1262173
theorem B1682915 : Blo 1120629 1682915 := bstep (se 1 (by rfl) ⟨1262186, by rfl⟩ : syracuseStep 1682915 = 2524373) B2524373
theorem B1682945 : Blo 1120629 1682945 := bstep (se 2 (by rfl) ⟨631104, by rfl⟩ : syracuseStep 1682945 = 1262209) B1262209
theorem B1682963 : Blo 1120629 1682963 := bstep (se 1 (by rfl) ⟨1262222, by rfl⟩ : syracuseStep 1682963 = 2524445) B2524445
theorem B1682993 : Blo 1120629 1682993 := bstep (se 2 (by rfl) ⟨631122, by rfl⟩ : syracuseStep 1682993 = 1262245) B1262245
theorem B1683011 : Blo 1120629 1683011 := bstep (se 1 (by rfl) ⟨1262258, by rfl⟩ : syracuseStep 1683011 = 2524517) B2524517
theorem B1683041 : Blo 1120629 1683041 := bstep (se 2 (by rfl) ⟨631140, by rfl⟩ : syracuseStep 1683041 = 1262281) B1262281
theorem B1683059 : Blo 1120629 1683059 := bstep (se 1 (by rfl) ⟨1262294, by rfl⟩ : syracuseStep 1683059 = 2524589) B2524589
theorem B1683089 : Blo 1120629 1683089 := bstep (se 2 (by rfl) ⟨631158, by rfl⟩ : syracuseStep 1683089 = 1262317) B1262317
theorem B1683107 : Blo 1120629 1683107 := bstep (se 1 (by rfl) ⟨1262330, by rfl⟩ : syracuseStep 1683107 = 2524661) B2524661
theorem B6401713 : Blo 1120629 6401713 := bstep (se 2 (by rfl) ⟨2400642, by rfl⟩ : syracuseStep 6401713 = 4801285) B4801285
theorem B1683137 : Blo 1120629 1683137 := bstep (se 2 (by rfl) ⟨631176, by rfl⟩ : syracuseStep 1683137 = 1262353) B1262353
theorem B1683155 : Blo 1120629 1683155 := bstep (se 1 (by rfl) ⟨1262366, by rfl⟩ : syracuseStep 1683155 = 2524733) B2524733
theorem B1683185 : Blo 1120629 1683185 := bstep (se 2 (by rfl) ⟨631194, by rfl⟩ : syracuseStep 1683185 = 1262389) B1262389
theorem B1683203 : Blo 1120629 1683203 := bstep (se 1 (by rfl) ⟨1262402, by rfl⟩ : syracuseStep 1683203 = 2524805) B2524805
theorem B1421059 : Blo 1120629 1421059 := bstep (se 1 (by rfl) ⟨1065794, by rfl⟩ : syracuseStep 1421059 = 2131589) B2131589
theorem B13119245 : Blo 1120629 13119245 := bstep (se 3 (by rfl) ⟨2459858, by rfl⟩ : syracuseStep 13119245 = 4919717) B4919717
theorem B1683233 : Blo 1120629 1683233 := bstep (se 2 (by rfl) ⟨631212, by rfl⟩ : syracuseStep 1683233 = 1262425) B1262425
theorem B1683251 : Blo 1120629 1683251 := bstep (se 1 (by rfl) ⟨1262438, by rfl⟩ : syracuseStep 1683251 = 2524877) B2524877
theorem B6074189 : Blo 1120629 6074189 := bstep (se 3 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 6074189 = 2277821) B2277821
theorem B1683281 : Blo 1120629 1683281 := bstep (se 2 (by rfl) ⟨631230, by rfl⟩ : syracuseStep 1683281 = 1262461) B1262461
theorem B1683299 : Blo 1120629 1683299 := bstep (se 1 (by rfl) ⟨1262474, by rfl⟩ : syracuseStep 1683299 = 2524949) B2524949
theorem B1421155 : Blo 1120629 1421155 := bstep (se 1 (by rfl) ⟨1065866, by rfl⟩ : syracuseStep 1421155 = 2131733) B2131733
theorem B1683329 : Blo 1120629 1683329 := bstep (se 2 (by rfl) ⟨631248, by rfl⟩ : syracuseStep 1683329 = 1262497) B1262497
theorem B1683347 : Blo 1120629 1683347 := bstep (se 1 (by rfl) ⟨1262510, by rfl⟩ : syracuseStep 1683347 = 2525021) B2525021
theorem B1683377 : Blo 1120629 1683377 := bstep (se 2 (by rfl) ⟨631266, by rfl⟩ : syracuseStep 1683377 = 1262533) B1262533
theorem B1683395 : Blo 1120629 1683395 := bstep (se 1 (by rfl) ⟨1262546, by rfl⟩ : syracuseStep 1683395 = 2525093) B2525093
theorem B1683425 : Blo 1120629 1683425 := bstep (se 2 (by rfl) ⟨631284, by rfl⟩ : syracuseStep 1683425 = 1262569) B1262569
theorem B1683443 : Blo 1120629 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B7680005 : Blo 1120629 7680005 := bstep (se 4 (by rfl) ⟨720000, by rfl⟩ : syracuseStep 7680005 = 1440001) B1440001
theorem B1683473 : Blo 1120629 1683473 := bstep (se 2 (by rfl) ⟨631302, by rfl⟩ : syracuseStep 1683473 = 1262605) B1262605
theorem B1683491 : Blo 1120629 1683491 := bstep (se 1 (by rfl) ⟨1262618, by rfl⟩ : syracuseStep 1683491 = 2525237) B2525237
theorem B1683521 : Blo 1120629 1683521 := bstep (se 2 (by rfl) ⟨631320, by rfl⟩ : syracuseStep 1683521 = 1262641) B1262641
theorem B1683539 : Blo 1120629 1683539 := bstep (se 1 (by rfl) ⟨1262654, by rfl⟩ : syracuseStep 1683539 = 2525309) B2525309
theorem B1683569 : Blo 1120629 1683569 := bstep (se 2 (by rfl) ⟨631338, by rfl⟩ : syracuseStep 1683569 = 1262677) B1262677
theorem B1683587 : Blo 1120629 1683587 := bstep (se 1 (by rfl) ⟨1262690, by rfl⟩ : syracuseStep 1683587 = 2525381) B2525381
theorem B1683617 : Blo 1120629 1683617 := bstep (se 2 (by rfl) ⟨631356, by rfl⟩ : syracuseStep 1683617 = 1262713) B1262713
theorem B6828209 : Blo 1120629 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B1683635 : Blo 1120629 1683635 := bstep (se 1 (by rfl) ⟨1262726, by rfl⟩ : syracuseStep 1683635 = 2525453) B2525453
theorem B1683665 : Blo 1120629 1683665 := bstep (se 2 (by rfl) ⟨631374, by rfl⟩ : syracuseStep 1683665 = 1262749) B1262749
theorem B1683683 : Blo 1120629 1683683 := bstep (se 1 (by rfl) ⟨1262762, by rfl⟩ : syracuseStep 1683683 = 2525525) B2525525
theorem B1683713 : Blo 1120629 1683713 := bstep (se 2 (by rfl) ⟨631392, by rfl⟩ : syracuseStep 1683713 = 1262785) B1262785
theorem B1683731 : Blo 1120629 1683731 := bstep (se 1 (by rfl) ⟨1262798, by rfl⟩ : syracuseStep 1683731 = 2525597) B2525597
theorem B1683761 : Blo 1120629 1683761 := bstep (se 2 (by rfl) ⟨631410, by rfl⟩ : syracuseStep 1683761 = 1262821) B1262821
theorem B1683779 : Blo 1120629 1683779 := bstep (se 1 (by rfl) ⟨1262834, by rfl⟩ : syracuseStep 1683779 = 2525669) B2525669
theorem B1421651 : Blo 1120629 1421651 := bstep (se 1 (by rfl) ⟨1066238, by rfl⟩ : syracuseStep 1421651 = 2132477) B2132477
theorem B1683809 : Blo 1120629 1683809 := bstep (se 2 (by rfl) ⟨631428, by rfl⟩ : syracuseStep 1683809 = 1262857) B1262857
theorem B1683827 : Blo 1120629 1683827 := bstep (se 1 (by rfl) ⟨1262870, by rfl⟩ : syracuseStep 1683827 = 2525741) B2525741
theorem B1683857 : Blo 1120629 1683857 := bstep (se 2 (by rfl) ⟨631446, by rfl⟩ : syracuseStep 1683857 = 1262893) B1262893
theorem B1683875 : Blo 1120629 1683875 := bstep (se 1 (by rfl) ⟨1262906, by rfl⟩ : syracuseStep 1683875 = 2525813) B2525813
theorem B1683905 : Blo 1120629 1683905 := bstep (se 2 (by rfl) ⟨631464, by rfl⟩ : syracuseStep 1683905 = 1262929) B1262929
theorem B1683923 : Blo 1120629 1683923 := bstep (se 1 (by rfl) ⟨1262942, by rfl⟩ : syracuseStep 1683923 = 2525885) B2525885
theorem B1683953 : Blo 1120629 1683953 := bstep (se 2 (by rfl) ⟨631482, by rfl⟩ : syracuseStep 1683953 = 1262965) B1262965
theorem B1683971 : Blo 1120629 1683971 := bstep (se 1 (by rfl) ⟨1262978, by rfl⟩ : syracuseStep 1683971 = 2525957) B2525957
theorem B1684001 : Blo 1120629 1684001 := bstep (se 2 (by rfl) ⟨631500, by rfl⟩ : syracuseStep 1684001 = 1263001) B1263001
theorem B1684019 : Blo 1120629 1684019 := bstep (se 1 (by rfl) ⟨1263014, by rfl⟩ : syracuseStep 1684019 = 2526029) B2526029
theorem B1684049 : Blo 1120629 1684049 := bstep (se 2 (by rfl) ⟨631518, by rfl⟩ : syracuseStep 1684049 = 1263037) B1263037
theorem B1684067 : Blo 1120629 1684067 := bstep (se 1 (by rfl) ⟨1263050, by rfl⟩ : syracuseStep 1684067 = 2526101) B2526101
theorem B1684097 : Blo 1120629 1684097 := bstep (se 2 (by rfl) ⟨631536, by rfl⟩ : syracuseStep 1684097 = 1263073) B1263073
theorem B1684115 : Blo 1120629 1684115 := bstep (se 1 (by rfl) ⟨1263086, by rfl⟩ : syracuseStep 1684115 = 2526173) B2526173
theorem B5386915 : Blo 1120629 5386915 := bstep (se 1 (by rfl) ⟨4040186, by rfl⟩ : syracuseStep 5386915 = 8080373) B8080373
theorem B1684145 : Blo 1120629 1684145 := bstep (se 2 (by rfl) ⟨631554, by rfl⟩ : syracuseStep 1684145 = 1263109) B1263109
theorem B1684163 : Blo 1120629 1684163 := bstep (se 1 (by rfl) ⟨1263122, by rfl⟩ : syracuseStep 1684163 = 2526245) B2526245
theorem B1684193 : Blo 1120629 1684193 := bstep (se 2 (by rfl) ⟨631572, by rfl⟩ : syracuseStep 1684193 = 1263145) B1263145
theorem B1684211 : Blo 1120629 1684211 := bstep (se 1 (by rfl) ⟨1263158, by rfl⟩ : syracuseStep 1684211 = 2526317) B2526317
theorem B1684241 : Blo 1120629 1684241 := bstep (se 2 (by rfl) ⟨631590, by rfl⟩ : syracuseStep 1684241 = 1263181) B1263181
theorem B1684259 : Blo 1120629 1684259 := bstep (se 1 (by rfl) ⟨1263194, by rfl⟩ : syracuseStep 1684259 = 2526389) B2526389
theorem B1684289 : Blo 1120629 1684289 := bstep (se 2 (by rfl) ⟨631608, by rfl⟩ : syracuseStep 1684289 = 1263217) B1263217
theorem B1684307 : Blo 1120629 1684307 := bstep (se 1 (by rfl) ⟨1263230, by rfl⟩ : syracuseStep 1684307 = 2526461) B2526461
theorem B1684337 : Blo 1120629 1684337 := bstep (se 2 (by rfl) ⟨631626, by rfl⟩ : syracuseStep 1684337 = 1263253) B1263253
theorem B1684355 : Blo 1120629 1684355 := bstep (se 1 (by rfl) ⟨1263266, by rfl⟩ : syracuseStep 1684355 = 2526533) B2526533
theorem B1684385 : Blo 1120629 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B1684403 : Blo 1120629 1684403 := bstep (se 1 (by rfl) ⟨1263302, by rfl⟩ : syracuseStep 1684403 = 2526605) B2526605
theorem B1684433 : Blo 1120629 1684433 := bstep (se 2 (by rfl) ⟨631662, by rfl⟩ : syracuseStep 1684433 = 1263325) B1263325
theorem B1684451 : Blo 1120629 1684451 := bstep (se 1 (by rfl) ⟨1263338, by rfl⟩ : syracuseStep 1684451 = 2526677) B2526677
theorem B1684481 : Blo 1120629 1684481 := bstep (se 2 (by rfl) ⟨631680, by rfl⟩ : syracuseStep 1684481 = 1263361) B1263361
theorem B3191825 : Blo 1120629 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B1684499 : Blo 1120629 1684499 := bstep (se 1 (by rfl) ⟨1263374, by rfl⟩ : syracuseStep 1684499 = 2526749) B2526749
theorem B1422355 : Blo 1120629 1422355 := bstep (se 1 (by rfl) ⟨1066766, by rfl⟩ : syracuseStep 1422355 = 2133533) B2133533
theorem B6829105 : Blo 1120629 6829105 := bstep (se 2 (by rfl) ⟨2560914, by rfl⟩ : syracuseStep 6829105 = 5121829) B5121829
theorem B1684529 : Blo 1120629 1684529 := bstep (se 2 (by rfl) ⟨631698, by rfl⟩ : syracuseStep 1684529 = 1263397) B1263397
theorem B1684547 : Blo 1120629 1684547 := bstep (se 1 (by rfl) ⟨1263410, by rfl⟩ : syracuseStep 1684547 = 2526821) B2526821
theorem B1684577 : Blo 1120629 1684577 := bstep (se 2 (by rfl) ⟨631716, by rfl⟩ : syracuseStep 1684577 = 1263433) B1263433
theorem B6403171 : Blo 1120629 6403171 := bstep (se 1 (by rfl) ⟨4802378, by rfl⟩ : syracuseStep 6403171 = 9604757) B9604757
theorem B1684595 : Blo 1120629 1684595 := bstep (se 1 (by rfl) ⟨1263446, by rfl⟩ : syracuseStep 1684595 = 2526893) B2526893
theorem B1422451 : Blo 1120629 1422451 := bstep (se 1 (by rfl) ⟨1066838, by rfl⟩ : syracuseStep 1422451 = 2133677) B2133677
theorem B1684625 : Blo 1120629 1684625 := bstep (se 2 (by rfl) ⟨631734, by rfl⟩ : syracuseStep 1684625 = 1263469) B1263469
theorem B1684643 : Blo 1120629 1684643 := bstep (se 1 (by rfl) ⟨1263482, by rfl⟩ : syracuseStep 1684643 = 2526965) B2526965
theorem B1684673 : Blo 1120629 1684673 := bstep (se 2 (by rfl) ⟨631752, by rfl⟩ : syracuseStep 1684673 = 1263505) B1263505
theorem B6075589 : Blo 1120629 6075589 := bstep (se 4 (by rfl) ⟨569586, by rfl⟩ : syracuseStep 6075589 = 1139173) B1139173
theorem B1684691 : Blo 1120629 1684691 := bstep (se 1 (by rfl) ⟨1263518, by rfl⟩ : syracuseStep 1684691 = 2527037) B2527037
theorem B1684721 : Blo 1120629 1684721 := bstep (se 2 (by rfl) ⟨631770, by rfl⟩ : syracuseStep 1684721 = 1263541) B1263541
theorem B1684739 : Blo 1120629 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B1684769 : Blo 1120629 1684769 := bstep (se 2 (by rfl) ⟨631788, by rfl⟩ : syracuseStep 1684769 = 1263577) B1263577
theorem B4797731 : Blo 1120629 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B1684787 : Blo 1120629 1684787 := bstep (se 1 (by rfl) ⟨1263590, by rfl⟩ : syracuseStep 1684787 = 2527181) B2527181
theorem B1684817 : Blo 1120629 1684817 := bstep (se 2 (by rfl) ⟨631806, by rfl⟩ : syracuseStep 1684817 = 1263613) B1263613
theorem B1684835 : Blo 1120629 1684835 := bstep (se 1 (by rfl) ⟨1263626, by rfl⟩ : syracuseStep 1684835 = 2527253) B2527253
theorem B1684865 : Blo 1120629 1684865 := bstep (se 2 (by rfl) ⟨631824, by rfl⟩ : syracuseStep 1684865 = 1263649) B1263649
theorem B1684883 : Blo 1120629 1684883 := bstep (se 1 (by rfl) ⟨1263662, by rfl⟩ : syracuseStep 1684883 = 2527325) B2527325
theorem B1684913 : Blo 1120629 1684913 := bstep (se 2 (by rfl) ⟨631842, by rfl⟩ : syracuseStep 1684913 = 1263685) B1263685
theorem B1684931 : Blo 1120629 1684931 := bstep (se 1 (by rfl) ⟨1263698, by rfl⟩ : syracuseStep 1684931 = 2527397) B2527397
theorem B1684961 : Blo 1120629 1684961 := bstep (se 2 (by rfl) ⟨631860, by rfl⟩ : syracuseStep 1684961 = 1263721) B1263721
theorem B1684979 : Blo 1120629 1684979 := bstep (se 1 (by rfl) ⟨1263734, by rfl⟩ : syracuseStep 1684979 = 2527469) B2527469
theorem B1685009 : Blo 1120629 1685009 := bstep (se 2 (by rfl) ⟨631878, by rfl⟩ : syracuseStep 1685009 = 1263757) B1263757
theorem B1685027 : Blo 1120629 1685027 := bstep (se 1 (by rfl) ⟨1263770, by rfl⟩ : syracuseStep 1685027 = 2527541) B2527541
theorem B1685057 : Blo 1120629 1685057 := bstep (se 2 (by rfl) ⟨631896, by rfl⟩ : syracuseStep 1685057 = 1263793) B1263793
theorem B1685075 : Blo 1120629 1685075 := bstep (se 1 (by rfl) ⟨1263806, by rfl⟩ : syracuseStep 1685075 = 2527613) B2527613
theorem B1422947 : Blo 1120629 1422947 := bstep (se 1 (by rfl) ⟨1067210, by rfl⟩ : syracuseStep 1422947 = 2134421) B2134421
theorem B1685105 : Blo 1120629 1685105 := bstep (se 2 (by rfl) ⟨631914, by rfl⟩ : syracuseStep 1685105 = 1263829) B1263829
theorem B6403697 : Blo 1120629 6403697 := bstep (se 2 (by rfl) ⟨2401386, by rfl⟩ : syracuseStep 6403697 = 4802773) B4802773
theorem B1685123 : Blo 1120629 1685123 := bstep (se 1 (by rfl) ⟨1263842, by rfl⟩ : syracuseStep 1685123 = 2527685) B2527685
theorem B1685153 : Blo 1120629 1685153 := bstep (se 2 (by rfl) ⟨631932, by rfl⟩ : syracuseStep 1685153 = 1263865) B1263865
theorem B3782321 : Blo 1120629 3782321 := bstep (se 2 (by rfl) ⟨1418370, by rfl⟩ : syracuseStep 3782321 = 2836741) B2836741
theorem B3192497 : Blo 1120629 3192497 := bstep (se 2 (by rfl) ⟨1197186, by rfl⟩ : syracuseStep 3192497 = 2394373) B2394373
theorem B1685171 : Blo 1120629 1685171 := bstep (se 1 (by rfl) ⟨1263878, by rfl⟩ : syracuseStep 1685171 = 2527757) B2527757
theorem B1685201 : Blo 1120629 1685201 := bstep (se 2 (by rfl) ⟨631950, by rfl⟩ : syracuseStep 1685201 = 1263901) B1263901
theorem B1685219 : Blo 1120629 1685219 := bstep (se 1 (by rfl) ⟨1263914, by rfl⟩ : syracuseStep 1685219 = 2527829) B2527829
theorem B1685249 : Blo 1120629 1685249 := bstep (se 2 (by rfl) ⟨631968, by rfl⟩ : syracuseStep 1685249 = 1263937) B1263937
theorem B1685267 : Blo 1120629 1685267 := bstep (se 1 (by rfl) ⟨1263950, by rfl⟩ : syracuseStep 1685267 = 2527901) B2527901
theorem B1685297 : Blo 1120629 1685297 := bstep (se 2 (by rfl) ⟨631986, by rfl⟩ : syracuseStep 1685297 = 1263973) B1263973
theorem B1685315 : Blo 1120629 1685315 := bstep (se 1 (by rfl) ⟨1263986, by rfl⟩ : syracuseStep 1685315 = 2527973) B2527973
theorem B1685345 : Blo 1120629 1685345 := bstep (se 2 (by rfl) ⟨632004, by rfl⟩ : syracuseStep 1685345 = 1264009) B1264009
theorem B1685363 : Blo 1120629 1685363 := bstep (se 1 (by rfl) ⟨1264022, by rfl⟩ : syracuseStep 1685363 = 2528045) B2528045
theorem B1685393 : Blo 1120629 1685393 := bstep (se 2 (by rfl) ⟨632022, by rfl⟩ : syracuseStep 1685393 = 1264045) B1264045
theorem B1685411 : Blo 1120629 1685411 := bstep (se 1 (by rfl) ⟨1264058, by rfl⟩ : syracuseStep 1685411 = 2528117) B2528117
theorem B5683121 : Blo 1120629 5683121 := bstep (se 2 (by rfl) ⟨2131170, by rfl⟩ : syracuseStep 5683121 = 4262341) B4262341
theorem B14366645 : Blo 1120629 14366645 := bstep (se 5 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 14366645 = 1346873) B1346873
theorem B1685441 : Blo 1120629 1685441 := bstep (se 2 (by rfl) ⟨632040, by rfl⟩ : syracuseStep 1685441 = 1264081) B1264081
theorem B1685459 : Blo 1120629 1685459 := bstep (se 1 (by rfl) ⟨1264094, by rfl⟩ : syracuseStep 1685459 = 2528189) B2528189
theorem B1685489 : Blo 1120629 1685489 := bstep (se 2 (by rfl) ⟨632058, by rfl⟩ : syracuseStep 1685489 = 1264117) B1264117
theorem B1685507 : Blo 1120629 1685507 := bstep (se 1 (by rfl) ⟨1264130, by rfl⟩ : syracuseStep 1685507 = 2528261) B2528261
theorem B1685537 : Blo 1120629 1685537 := bstep (se 2 (by rfl) ⟨632076, by rfl⟩ : syracuseStep 1685537 = 1264153) B1264153
theorem B1685555 : Blo 1120629 1685555 := bstep (se 1 (by rfl) ⟨1264166, by rfl⟩ : syracuseStep 1685555 = 2528333) B2528333
theorem B1685585 : Blo 1120629 1685585 := bstep (se 2 (by rfl) ⟨632094, by rfl⟩ : syracuseStep 1685585 = 1264189) B1264189
theorem B1685603 : Blo 1120629 1685603 := bstep (se 1 (by rfl) ⟨1264202, by rfl⟩ : syracuseStep 1685603 = 2528405) B2528405
theorem B1685633 : Blo 1120629 1685633 := bstep (se 2 (by rfl) ⟨632112, by rfl⟩ : syracuseStep 1685633 = 1264225) B1264225
theorem B1685651 : Blo 1120629 1685651 := bstep (se 1 (by rfl) ⟨1264238, by rfl⟩ : syracuseStep 1685651 = 2528477) B2528477
theorem B1685681 : Blo 1120629 1685681 := bstep (se 2 (by rfl) ⟨632130, by rfl⟩ : syracuseStep 1685681 = 1264261) B1264261
theorem B1685699 : Blo 1120629 1685699 := bstep (se 1 (by rfl) ⟨1264274, by rfl⟩ : syracuseStep 1685699 = 2528549) B2528549
theorem B3782861 : Blo 1120629 3782861 := bstep (se 3 (by rfl) ⟨709286, by rfl⟩ : syracuseStep 3782861 = 1418573) B1418573
theorem B1685729 : Blo 1120629 1685729 := bstep (se 2 (by rfl) ⟨632148, by rfl⟩ : syracuseStep 1685729 = 1264297) B1264297
theorem B1685747 : Blo 1120629 1685747 := bstep (se 1 (by rfl) ⟨1264310, by rfl⟩ : syracuseStep 1685747 = 2528621) B2528621
theorem B3782915 : Blo 1120629 3782915 := bstep (se 1 (by rfl) ⟨2837186, by rfl⟩ : syracuseStep 3782915 = 5674373) B5674373
theorem B1685777 : Blo 1120629 1685777 := bstep (se 2 (by rfl) ⟨632166, by rfl⟩ : syracuseStep 1685777 = 1264333) B1264333
theorem B1685795 : Blo 1120629 1685795 := bstep (se 1 (by rfl) ⟨1264346, by rfl⟩ : syracuseStep 1685795 = 2528693) B2528693
theorem B1685825 : Blo 1120629 1685825 := bstep (se 2 (by rfl) ⟨632184, by rfl⟩ : syracuseStep 1685825 = 1264369) B1264369
theorem B1685843 : Blo 1120629 1685843 := bstep (se 1 (by rfl) ⟨1264382, by rfl⟩ : syracuseStep 1685843 = 2528765) B2528765
theorem B2701667 : Blo 1120629 2701667 := bstep (se 1 (by rfl) ⟨2026250, by rfl⟩ : syracuseStep 2701667 = 4052501) B4052501
theorem B1685873 : Blo 1120629 1685873 := bstep (se 2 (by rfl) ⟨632202, by rfl⟩ : syracuseStep 1685873 = 1264405) B1264405
theorem B1685891 : Blo 1120629 1685891 := bstep (se 1 (by rfl) ⟨1264418, by rfl⟩ : syracuseStep 1685891 = 2528837) B2528837
theorem B1685921 : Blo 1120629 1685921 := bstep (se 2 (by rfl) ⟨632220, by rfl⟩ : syracuseStep 1685921 = 1264441) B1264441
theorem B1685939 : Blo 1120629 1685939 := bstep (se 1 (by rfl) ⟨1264454, by rfl⟩ : syracuseStep 1685939 = 2528909) B2528909
theorem B3193283 : Blo 1120629 3193283 := bstep (se 1 (by rfl) ⟨2394962, by rfl⟩ : syracuseStep 3193283 = 4789925) B4789925
theorem B1685969 : Blo 1120629 1685969 := bstep (se 2 (by rfl) ⟨632238, by rfl⟩ : syracuseStep 1685969 = 1264477) B1264477
theorem B1685987 : Blo 1120629 1685987 := bstep (se 1 (by rfl) ⟨1264490, by rfl⟩ : syracuseStep 1685987 = 2528981) B2528981
theorem B1686017 : Blo 1120629 1686017 := bstep (se 2 (by rfl) ⟨632256, by rfl⟩ : syracuseStep 1686017 = 1264513) B1264513
theorem B3783185 : Blo 1120629 3783185 := bstep (se 2 (by rfl) ⟨1418694, by rfl⟩ : syracuseStep 3783185 = 2837389) B2837389
theorem B2734609 : Blo 1120629 2734609 := bstep (se 2 (by rfl) ⟨1025478, by rfl⟩ : syracuseStep 2734609 = 2050957) B2050957
theorem B1686035 : Blo 1120629 1686035 := bstep (se 1 (by rfl) ⟨1264526, by rfl⟩ : syracuseStep 1686035 = 2529053) B2529053
theorem B1686065 : Blo 1120629 1686065 := bstep (se 2 (by rfl) ⟨632274, by rfl⟩ : syracuseStep 1686065 = 1264549) B1264549
theorem B1686083 : Blo 1120629 1686083 := bstep (se 1 (by rfl) ⟨1264562, by rfl⟩ : syracuseStep 1686083 = 2529125) B2529125
theorem B1686113 : Blo 1120629 1686113 := bstep (se 2 (by rfl) ⟨632292, by rfl⟩ : syracuseStep 1686113 = 1264585) B1264585
theorem B1686131 : Blo 1120629 1686131 := bstep (se 1 (by rfl) ⟨1264598, by rfl⟩ : syracuseStep 1686131 = 2529197) B2529197
theorem B1686161 : Blo 1120629 1686161 := bstep (se 2 (by rfl) ⟨632310, by rfl⟩ : syracuseStep 1686161 = 1264621) B1264621
theorem B1686179 : Blo 1120629 1686179 := bstep (se 1 (by rfl) ⟨1264634, by rfl⟩ : syracuseStep 1686179 = 2529269) B2529269
theorem B1686209 : Blo 1120629 1686209 := bstep (se 2 (by rfl) ⟨632328, by rfl⟩ : syracuseStep 1686209 = 1264657) B1264657
theorem B1686227 : Blo 1120629 1686227 := bstep (se 1 (by rfl) ⟨1264670, by rfl⟩ : syracuseStep 1686227 = 2529341) B2529341
theorem B2702051 : Blo 1120629 2702051 := bstep (se 1 (by rfl) ⟨2026538, by rfl⟩ : syracuseStep 2702051 = 4053077) B4053077
theorem B1686257 : Blo 1120629 1686257 := bstep (se 2 (by rfl) ⟨632346, by rfl⟩ : syracuseStep 1686257 = 1264693) B1264693
theorem B1686275 : Blo 1120629 1686275 := bstep (se 1 (by rfl) ⟨1264706, by rfl⟩ : syracuseStep 1686275 = 2529413) B2529413
theorem B3193613 : Blo 1120629 3193613 := bstep (se 3 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 3193613 = 1197605) B1197605
theorem B1686305 : Blo 1120629 1686305 := bstep (se 2 (by rfl) ⟨632364, by rfl⟩ : syracuseStep 1686305 = 1264729) B1264729
theorem B3029795 : Blo 1120629 3029795 := bstep (se 1 (by rfl) ⟨2272346, by rfl⟩ : syracuseStep 3029795 = 4544693) B4544693
theorem B1686323 : Blo 1120629 1686323 := bstep (se 1 (by rfl) ⟨1264742, by rfl⟩ : syracuseStep 1686323 = 2529485) B2529485
theorem B3193681 : Blo 1120629 3193681 := bstep (se 2 (by rfl) ⟨1197630, by rfl⟩ : syracuseStep 3193681 = 2395261) B2395261
theorem B1686353 : Blo 1120629 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B1686371 : Blo 1120629 1686371 := bstep (se 1 (by rfl) ⟨1264778, by rfl⟩ : syracuseStep 1686371 = 2529557) B2529557
theorem B1686401 : Blo 1120629 1686401 := bstep (se 2 (by rfl) ⟨632400, by rfl⟩ : syracuseStep 1686401 = 1264801) B1264801
theorem B1522577 : Blo 1120629 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B1686419 : Blo 1120629 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B1751969 : Blo 1120629 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1686449 : Blo 1120629 1686449 := bstep (se 2 (by rfl) ⟨632418, by rfl⟩ : syracuseStep 1686449 = 1264837) B1264837
theorem B1686467 : Blo 1120629 1686467 := bstep (se 1 (by rfl) ⟨1264850, by rfl⟩ : syracuseStep 1686467 = 2529701) B2529701
theorem B1686497 : Blo 1120629 1686497 := bstep (se 2 (by rfl) ⟨632436, by rfl⟩ : syracuseStep 1686497 = 1264873) B1264873
theorem B1686515 : Blo 1120629 1686515 := bstep (se 1 (by rfl) ⟨1264886, by rfl⟩ : syracuseStep 1686515 = 2529773) B2529773
theorem B1686545 : Blo 1120629 1686545 := bstep (se 2 (by rfl) ⟨632454, by rfl⟩ : syracuseStep 1686545 = 1264909) B1264909
theorem B1686563 : Blo 1120629 1686563 := bstep (se 1 (by rfl) ⟨1264922, by rfl⟩ : syracuseStep 1686563 = 2529845) B2529845
theorem B3783725 : Blo 1120629 3783725 := bstep (se 3 (by rfl) ⟨709448, by rfl⟩ : syracuseStep 3783725 = 1418897) B1418897
theorem B1686593 : Blo 1120629 1686593 := bstep (se 2 (by rfl) ⟨632472, by rfl⟩ : syracuseStep 1686593 = 1264945) B1264945
theorem B1686611 : Blo 1120629 1686611 := bstep (se 1 (by rfl) ⟨1264958, by rfl⟩ : syracuseStep 1686611 = 2529917) B2529917
theorem B3783779 : Blo 1120629 3783779 := bstep (se 1 (by rfl) ⟨2837834, by rfl⟩ : syracuseStep 3783779 = 5675669) B5675669
theorem B3193955 : Blo 1120629 3193955 := bstep (se 1 (by rfl) ⟨2395466, by rfl⟩ : syracuseStep 3193955 = 4790933) B4790933
theorem B1686641 : Blo 1120629 1686641 := bstep (se 2 (by rfl) ⟨632490, by rfl⟩ : syracuseStep 1686641 = 1264981) B1264981
theorem B1686659 : Blo 1120629 1686659 := bstep (se 1 (by rfl) ⟨1264994, by rfl⟩ : syracuseStep 1686659 = 2529989) B2529989
theorem B1686689 : Blo 1120629 1686689 := bstep (se 2 (by rfl) ⟨632508, by rfl⟩ : syracuseStep 1686689 = 1265017) B1265017
theorem B1686707 : Blo 1120629 1686707 := bstep (se 1 (by rfl) ⟨1265030, by rfl⟩ : syracuseStep 1686707 = 2530061) B2530061
theorem B1686737 : Blo 1120629 1686737 := bstep (se 2 (by rfl) ⟨632526, by rfl⟩ : syracuseStep 1686737 = 1265053) B1265053
theorem B1686755 : Blo 1120629 1686755 := bstep (se 1 (by rfl) ⟨1265066, by rfl⟩ : syracuseStep 1686755 = 2530133) B2530133
theorem B1260787 : Blo 1120629 1260787 := bstep (se 1 (by rfl) ⟨945590, by rfl⟩ : syracuseStep 1260787 = 1891181) B1891181
theorem B1686785 : Blo 1120629 1686785 := bstep (se 2 (by rfl) ⟨632544, by rfl⟩ : syracuseStep 1686785 = 1265089) B1265089
theorem B1686803 : Blo 1120629 1686803 := bstep (se 1 (by rfl) ⟨1265102, by rfl⟩ : syracuseStep 1686803 = 2530205) B2530205
theorem B1686833 : Blo 1120629 1686833 := bstep (se 2 (by rfl) ⟨632562, by rfl⟩ : syracuseStep 1686833 = 1265125) B1265125
theorem B1686851 : Blo 1120629 1686851 := bstep (se 1 (by rfl) ⟨1265138, by rfl⟩ : syracuseStep 1686851 = 2530277) B2530277
theorem B1686881 : Blo 1120629 1686881 := bstep (se 2 (by rfl) ⟨632580, by rfl⟩ : syracuseStep 1686881 = 1265161) B1265161
theorem B5684579 : Blo 1120629 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B3784049 : Blo 1120629 3784049 := bstep (se 2 (by rfl) ⟨1419018, by rfl⟩ : syracuseStep 3784049 = 2838037) B2838037
theorem B1686899 : Blo 1120629 1686899 := bstep (se 1 (by rfl) ⟨1265174, by rfl⟩ : syracuseStep 1686899 = 2530349) B2530349
theorem B1260931 : Blo 1120629 1260931 := bstep (se 1 (by rfl) ⟨945698, by rfl⟩ : syracuseStep 1260931 = 1891397) B1891397
theorem B1686929 : Blo 1120629 1686929 := bstep (se 2 (by rfl) ⟨632598, by rfl⟩ : syracuseStep 1686929 = 1265197) B1265197
theorem B1261075 : Blo 1120629 1261075 := bstep (se 1 (by rfl) ⟨945806, by rfl⟩ : syracuseStep 1261075 = 1891613) B1891613
theorem B1261219 : Blo 1120629 1261219 := bstep (se 1 (by rfl) ⟨945914, by rfl⟩ : syracuseStep 1261219 = 1891829) B1891829
theorem B3030833 : Blo 1120629 3030833 := bstep (se 2 (by rfl) ⟨1136562, by rfl⟩ : syracuseStep 3030833 = 2273125) B2273125
theorem B1556275 : Blo 1120629 1556275 := bstep (se 1 (by rfl) ⟨1167206, by rfl⟩ : syracuseStep 1556275 = 2334413) B2334413
theorem B1261363 : Blo 1120629 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B6078341 : Blo 1120629 6078341 := bstep (se 4 (by rfl) ⟨569844, by rfl⟩ : syracuseStep 6078341 = 1139689) B1139689
theorem B4800397 : Blo 1120629 4800397 := bstep (se 3 (by rfl) ⟨900074, by rfl⟩ : syracuseStep 4800397 = 1800149) B1800149
theorem B3784589 : Blo 1120629 3784589 := bstep (se 3 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 3784589 = 1419221) B1419221
theorem B5390221 : Blo 1120629 5390221 := bstep (se 3 (by rfl) ⟨1010666, by rfl⟩ : syracuseStep 5390221 = 2021333) B2021333
theorem B3194797 : Blo 1120629 3194797 := bstep (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) B1198049
theorem B1261507 : Blo 1120629 1261507 := bstep (se 1 (by rfl) ⟨946130, by rfl⟩ : syracuseStep 1261507 = 1892261) B1892261
theorem B3784643 : Blo 1120629 3784643 := bstep (se 1 (by rfl) ⟨2838482, by rfl⟩ : syracuseStep 3784643 = 5676965) B5676965
theorem B3194957 : Blo 1120629 3194957 := bstep (se 3 (by rfl) ⟨599054, by rfl⟩ : syracuseStep 3194957 = 1198109) B1198109
theorem B1261651 : Blo 1120629 1261651 := bstep (se 1 (by rfl) ⟨946238, by rfl⟩ : syracuseStep 1261651 = 1892477) B1892477
theorem B5685389 : Blo 1120629 5685389 := bstep (se 3 (by rfl) ⟨1066010, by rfl⟩ : syracuseStep 5685389 = 2132021) B2132021
theorem B3784913 : Blo 1120629 3784913 := bstep (se 2 (by rfl) ⟨1419342, by rfl⟩ : syracuseStep 3784913 = 2838685) B2838685
theorem B1261795 : Blo 1120629 1261795 := bstep (se 1 (by rfl) ⟨946346, by rfl⟩ : syracuseStep 1261795 = 1892693) B1892693
theorem B3195139 : Blo 1120629 3195139 := bstep (se 1 (by rfl) ⟨2396354, by rfl⟩ : syracuseStep 3195139 = 4792709) B4792709
theorem B1261939 : Blo 1120629 1261939 := bstep (se 1 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 1261939 = 1892909) B1892909
theorem B5390819 : Blo 1120629 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B1262083 : Blo 1120629 1262083 := bstep (se 1 (by rfl) ⟨946562, by rfl⟩ : syracuseStep 1262083 = 1893125) B1893125
theorem B8536589 : Blo 1120629 8536589 := bstep (se 3 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 8536589 = 3201221) B3201221
theorem B1262227 : Blo 1120629 1262227 := bstep (se 1 (by rfl) ⟨946670, by rfl⟩ : syracuseStep 1262227 = 1893341) B1893341
theorem B3785453 : Blo 1120629 3785453 := bstep (se 3 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 3785453 = 1419545) B1419545
theorem B7684877 : Blo 1120629 7684877 := bstep (se 3 (by rfl) ⟨1440914, by rfl⟩ : syracuseStep 7684877 = 2881829) B2881829
theorem B3785507 : Blo 1120629 3785507 := bstep (se 1 (by rfl) ⟨2839130, by rfl⟩ : syracuseStep 3785507 = 5678261) B5678261
theorem B1262371 : Blo 1120629 1262371 := bstep (se 1 (by rfl) ⟨946778, by rfl⟩ : syracuseStep 1262371 = 1893557) B1893557
theorem B11518861 : Blo 1120629 11518861 := bstep (se 3 (by rfl) ⟨2159786, by rfl⟩ : syracuseStep 11518861 = 4319573) B4319573
theorem B1196947 : Blo 1120629 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B4801457 : Blo 1120629 4801457 := bstep (se 2 (by rfl) ⟨1800546, by rfl⟩ : syracuseStep 4801457 = 3601093) B3601093
theorem B1262515 : Blo 1120629 1262515 := bstep (se 1 (by rfl) ⟨946886, by rfl⟩ : syracuseStep 1262515 = 1893773) B1893773
theorem B4047857 : Blo 1120629 4047857 := bstep (se 2 (by rfl) ⟨1517946, by rfl⟩ : syracuseStep 4047857 = 3035893) B3035893
theorem B3785777 : Blo 1120629 3785777 := bstep (se 2 (by rfl) ⟨1419666, by rfl⟩ : syracuseStep 3785777 = 2839333) B2839333
theorem B1262659 : Blo 1120629 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B1262803 : Blo 1120629 1262803 := bstep (se 1 (by rfl) ⟨947102, by rfl⟩ : syracuseStep 1262803 = 1894205) B1894205
theorem B8209649 : Blo 1120629 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B15385841 : Blo 1120629 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B1197379 : Blo 1120629 1197379 := bstep (se 1 (by rfl) ⟨898034, by rfl⟩ : syracuseStep 1197379 = 1796069) B1796069
theorem B7193933 : Blo 1120629 7193933 := bstep (se 3 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 7193933 = 2697725) B2697725
theorem B1262947 : Blo 1120629 1262947 := bstep (se 1 (by rfl) ⟨947210, by rfl⟩ : syracuseStep 1262947 = 1894421) B1894421
theorem B2278865 : Blo 1120629 2278865 := bstep (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) B1709149
theorem B1263091 : Blo 1120629 1263091 := bstep (se 1 (by rfl) ⟨947318, by rfl⟩ : syracuseStep 1263091 = 1894637) B1894637
theorem B27313685 : Blo 1120629 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B1820209 : Blo 1120629 1820209 := bstep (se 2 (by rfl) ⟨682578, by rfl⟩ : syracuseStep 1820209 = 1365157) B1365157
theorem B3786317 : Blo 1120629 3786317 := bstep (se 3 (by rfl) ⟨709934, by rfl⟩ : syracuseStep 3786317 = 1419869) B1419869
theorem B3196529 : Blo 1120629 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B3786371 : Blo 1120629 3786371 := bstep (se 1 (by rfl) ⟨2839778, by rfl⟩ : syracuseStep 3786371 = 5679557) B5679557
theorem B1263235 : Blo 1120629 1263235 := bstep (se 1 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 1263235 = 1894853) B1894853
theorem B4048547 : Blo 1120629 4048547 := bstep (se 1 (by rfl) ⟨3036410, by rfl⟩ : syracuseStep 4048547 = 6072821) B6072821
theorem B1263379 : Blo 1120629 1263379 := bstep (se 1 (by rfl) ⟨947534, by rfl⟩ : syracuseStep 1263379 = 1895069) B1895069
theorem B3032909 : Blo 1120629 3032909 := bstep (se 3 (by rfl) ⟨568670, by rfl⟩ : syracuseStep 3032909 = 1137341) B1137341
theorem B3786641 : Blo 1120629 3786641 := bstep (se 2 (by rfl) ⟨1419990, by rfl⟩ : syracuseStep 3786641 = 2839981) B2839981
theorem B1263523 : Blo 1120629 1263523 := bstep (se 1 (by rfl) ⟨947642, by rfl⟩ : syracuseStep 1263523 = 1895285) B1895285
theorem B3590189 : Blo 1120629 3590189 := bstep (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) B1346321
theorem B1263667 : Blo 1120629 1263667 := bstep (se 1 (by rfl) ⟨947750, by rfl⟩ : syracuseStep 1263667 = 1895501) B1895501
theorem B4049009 : Blo 1120629 4049009 := bstep (se 2 (by rfl) ⟨1518378, by rfl⟩ : syracuseStep 4049009 = 3036757) B3036757
theorem B1263811 : Blo 1120629 1263811 := bstep (se 1 (by rfl) ⟨947858, by rfl⟩ : syracuseStep 1263811 = 1895717) B1895717
theorem B1263827 : Blo 1120629 1263827 := bstep (se 1 (by rfl) ⟨947870, by rfl⟩ : syracuseStep 1263827 = 1895741) B1895741
theorem B2836721 : Blo 1120629 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B1263955 : Blo 1120629 1263955 := bstep (se 1 (by rfl) ⟨947966, by rfl⟩ : syracuseStep 1263955 = 1895933) B1895933
theorem B3787181 : Blo 1120629 3787181 := bstep (se 3 (by rfl) ⟨710096, by rfl⟩ : syracuseStep 3787181 = 1420193) B1420193
theorem B3787235 : Blo 1120629 3787235 := bstep (se 1 (by rfl) ⟨2840426, by rfl⟩ : syracuseStep 3787235 = 5680853) B5680853
theorem B12470755 : Blo 1120629 12470755 := bstep (se 1 (by rfl) ⟨9353066, by rfl⟩ : syracuseStep 12470755 = 18706133) B18706133
theorem B1264099 : Blo 1120629 1264099 := bstep (se 1 (by rfl) ⟨948074, by rfl⟩ : syracuseStep 1264099 = 1896149) B1896149
theorem B4868579 : Blo 1120629 4868579 := bstep (se 1 (by rfl) ⟨3651434, by rfl⟩ : syracuseStep 4868579 = 7302869) B7302869
theorem B8079857 : Blo 1120629 8079857 := bstep (se 2 (by rfl) ⟨3029946, by rfl⟩ : syracuseStep 8079857 = 6059893) B6059893
theorem B3197485 : Blo 1120629 3197485 := bstep (se 3 (by rfl) ⟨599528, by rfl⟩ : syracuseStep 3197485 = 1199057) B1199057
theorem B1198643 : Blo 1120629 1198643 := bstep (se 1 (by rfl) ⟨898982, by rfl⟩ : syracuseStep 1198643 = 1797965) B1797965
theorem B1264243 : Blo 1120629 1264243 := bstep (se 1 (by rfl) ⟨948182, by rfl⟩ : syracuseStep 1264243 = 1896365) B1896365
theorem B1460867 : Blo 1120629 1460867 := bstep (se 1 (by rfl) ⟨1095650, by rfl⟩ : syracuseStep 1460867 = 2191301) B2191301
theorem B1821361 : Blo 1120629 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B3787505 : Blo 1120629 3787505 := bstep (se 2 (by rfl) ⟨1420314, by rfl⟩ : syracuseStep 3787505 = 2840629) B2840629
theorem B1264387 : Blo 1120629 1264387 := bstep (se 1 (by rfl) ⟨948290, by rfl⟩ : syracuseStep 1264387 = 1896581) B1896581
theorem B3197713 : Blo 1120629 3197713 := bstep (se 2 (by rfl) ⟨1199142, by rfl⟩ : syracuseStep 3197713 = 2398285) B2398285
theorem B1264531 : Blo 1120629 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B3197873 : Blo 1120629 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B1821619 : Blo 1120629 1821619 := bstep (se 1 (by rfl) ⟨1366214, by rfl⟩ : syracuseStep 1821619 = 2732429) B2732429
theorem B5688305 : Blo 1120629 5688305 := bstep (se 2 (by rfl) ⟨2133114, by rfl⟩ : syracuseStep 5688305 = 4266229) B4266229
theorem B3197987 : Blo 1120629 3197987 := bstep (se 1 (by rfl) ⟨2398490, by rfl⟩ : syracuseStep 3197987 = 4796981) B4796981
theorem B1264675 : Blo 1120629 1264675 := bstep (se 1 (by rfl) ⟨948506, by rfl⟩ : syracuseStep 1264675 = 1897013) B1897013
theorem B1264819 : Blo 1120629 1264819 := bstep (se 1 (by rfl) ⟨948614, by rfl⟩ : syracuseStep 1264819 = 1897229) B1897229
theorem B2837713 : Blo 1120629 2837713 := bstep (se 2 (by rfl) ⟨1064142, by rfl⟩ : syracuseStep 2837713 = 2128285) B2128285
theorem B3788045 : Blo 1120629 3788045 := bstep (se 3 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 3788045 = 1420517) B1420517
theorem B1199395 : Blo 1120629 1199395 := bstep (se 1 (by rfl) ⟨899546, by rfl⟩ : syracuseStep 1199395 = 1799093) B1799093
theorem B3788099 : Blo 1120629 3788099 := bstep (se 1 (by rfl) ⟨2841074, by rfl⟩ : syracuseStep 3788099 = 5682149) B5682149
theorem B1264963 : Blo 1120629 1264963 := bstep (se 1 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 1264963 = 1897445) B1897445
theorem B3591533 : Blo 1120629 3591533 := bstep (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) B1346825
theorem B8539505 : Blo 1120629 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B3034531 : Blo 1120629 3034531 := bstep (se 1 (by rfl) ⟨2275898, by rfl⟩ : syracuseStep 3034531 = 4551797) B4551797
theorem B1265107 : Blo 1120629 1265107 := bstep (se 1 (by rfl) ⟨948830, by rfl⟩ : syracuseStep 1265107 = 1897661) B1897661
theorem B2837987 : Blo 1120629 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B1822241 : Blo 1120629 1822241 := bstep (se 2 (by rfl) ⟨683340, by rfl⟩ : syracuseStep 1822241 = 1366681) B1366681
theorem B3788369 : Blo 1120629 3788369 := bstep (se 2 (by rfl) ⟨1420638, by rfl⟩ : syracuseStep 3788369 = 2841277) B2841277
theorem B2838179 : Blo 1120629 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B3198989 : Blo 1120629 3198989 := bstep (se 3 (by rfl) ⟨599810, by rfl⟩ : syracuseStep 3198989 = 1199621) B1199621
theorem B5394509 : Blo 1120629 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B3788909 : Blo 1120629 3788909 := bstep (se 3 (by rfl) ⟨710420, by rfl⟩ : syracuseStep 3788909 = 1420841) B1420841
theorem B3788963 : Blo 1120629 3788963 := bstep (se 1 (by rfl) ⟨2841722, by rfl⟩ : syracuseStep 3788963 = 5683445) B5683445
theorem B3199171 : Blo 1120629 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B4313357 : Blo 1120629 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B1200467 : Blo 1120629 1200467 := bstep (se 1 (by rfl) ⟨900350, by rfl⟩ : syracuseStep 1200467 = 1800701) B1800701
theorem B3199331 : Blo 1120629 3199331 := bstep (se 1 (by rfl) ⟨2399498, by rfl⟩ : syracuseStep 3199331 = 4798997) B4798997
theorem B5689763 : Blo 1120629 5689763 := bstep (se 1 (by rfl) ⟨4267322, by rfl⟩ : syracuseStep 5689763 = 8534645) B8534645
theorem B3789233 : Blo 1120629 3789233 := bstep (se 2 (by rfl) ⟨1420962, by rfl⟩ : syracuseStep 3789233 = 2841925) B2841925
theorem B2839121 : Blo 1120629 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B2839171 : Blo 1120629 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B2839313 : Blo 1120629 2839313 := bstep (se 2 (by rfl) ⟨1064742, by rfl⟩ : syracuseStep 2839313 = 2129485) B2129485
theorem B3593123 : Blo 1120629 3593123 := bstep (se 1 (by rfl) ⟨2694842, by rfl⟩ : syracuseStep 3593123 = 5389685) B5389685
theorem B3789773 : Blo 1120629 3789773 := bstep (se 3 (by rfl) ⟨710582, by rfl⟩ : syracuseStep 3789773 = 1421165) B1421165
theorem B3789827 : Blo 1120629 3789827 := bstep (se 1 (by rfl) ⟨2842370, by rfl⟩ : syracuseStep 3789827 = 5684741) B5684741
theorem B9589859 : Blo 1120629 9589859 := bstep (se 1 (by rfl) ⟨7192394, by rfl⟩ : syracuseStep 9589859 = 14384789) B14384789
theorem B5690573 : Blo 1120629 5690573 := bstep (se 3 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 5690573 = 2133965) B2133965
theorem B7296227 : Blo 1120629 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B3790097 : Blo 1120629 3790097 := bstep (se 2 (by rfl) ⟨1421286, by rfl⟩ : syracuseStep 3790097 = 2842573) B2842573
theorem B7198085 : Blo 1120629 7198085 := bstep (se 4 (by rfl) ⟨674820, by rfl⟩ : syracuseStep 7198085 = 1349641) B1349641
theorem B3200401 : Blo 1120629 3200401 := bstep (se 2 (by rfl) ⟨1200150, by rfl⟩ : syracuseStep 3200401 = 2400301) B2400301
theorem B2020771 : Blo 1120629 2020771 := bstep (se 1 (by rfl) ⟨1515578, by rfl⟩ : syracuseStep 2020771 = 3031157) B3031157
theorem B5199331 : Blo 1120629 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B3462659 : Blo 1120629 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B3593891 : Blo 1120629 3593891 := bstep (se 1 (by rfl) ⟨2695418, by rfl⟩ : syracuseStep 3593891 = 5390837) B5390837
theorem B2840305 : Blo 1120629 2840305 := bstep (se 2 (by rfl) ⟨1065114, by rfl⟩ : syracuseStep 2840305 = 2130229) B2130229
theorem B3790637 : Blo 1120629 3790637 := bstep (se 3 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 3790637 = 1421489) B1421489
theorem B3790691 : Blo 1120629 3790691 := bstep (se 1 (by rfl) ⟨2843018, by rfl⟩ : syracuseStep 3790691 = 5686037) B5686037
theorem B2840579 : Blo 1120629 2840579 := bstep (se 1 (by rfl) ⟨2130434, by rfl⟩ : syracuseStep 2840579 = 4260869) B4260869
theorem B3594289 : Blo 1120629 3594289 := bstep (se 2 (by rfl) ⟨1347858, by rfl⟩ : syracuseStep 3594289 = 2695717) B2695717
theorem B9099377 : Blo 1120629 9099377 := bstep (se 2 (by rfl) ⟨3412266, by rfl⟩ : syracuseStep 9099377 = 6824533) B6824533
theorem B3790961 : Blo 1120629 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B3594403 : Blo 1120629 3594403 := bstep (se 1 (by rfl) ⟨2695802, by rfl⟩ : syracuseStep 3594403 = 5391605) B5391605
theorem B2840771 : Blo 1120629 2840771 := bstep (se 1 (by rfl) ⟨2130578, by rfl⟩ : syracuseStep 2840771 = 4261157) B4261157
theorem B1595713 : Blo 1120629 1595713 := bstep (se 2 (by rfl) ⟨598392, by rfl⟩ : syracuseStep 1595713 = 1196785) B1196785
theorem B1595747 : Blo 1120629 1595747 := bstep (se 1 (by rfl) ⟨1196810, by rfl⟩ : syracuseStep 1595747 = 2393621) B2393621
theorem B3037709 : Blo 1120629 3037709 := bstep (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) B1139141
theorem B3791501 : Blo 1120629 3791501 := bstep (se 3 (by rfl) ⟨710906, by rfl⟩ : syracuseStep 3791501 = 1421813) B1421813
theorem B3201677 : Blo 1120629 3201677 := bstep (se 3 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 3201677 = 1200629) B1200629
theorem B3791555 : Blo 1120629 3791555 := bstep (se 1 (by rfl) ⟨2843666, by rfl⟩ : syracuseStep 3791555 = 5687333) B5687333
theorem B1891073 : Blo 1120629 1891073 := bstep (se 2 (by rfl) ⟨709152, by rfl⟩ : syracuseStep 1891073 = 1418305) B1418305
theorem B3201859 : Blo 1120629 3201859 := bstep (se 1 (by rfl) ⟨2401394, by rfl⟩ : syracuseStep 3201859 = 4802789) B4802789
theorem B3595121 : Blo 1120629 3595121 := bstep (se 2 (by rfl) ⟨1348170, by rfl⟩ : syracuseStep 3595121 = 2696341) B2696341
theorem B3201905 : Blo 1120629 3201905 := bstep (se 2 (by rfl) ⟨1200714, by rfl⟩ : syracuseStep 3201905 = 2401429) B2401429
theorem B1891201 : Blo 1120629 1891201 := bstep (se 2 (by rfl) ⟨709200, by rfl⟩ : syracuseStep 1891201 = 1418401) B1418401
theorem B1596305 : Blo 1120629 1596305 := bstep (se 2 (by rfl) ⟨598614, by rfl⟩ : syracuseStep 1596305 = 1197229) B1197229
theorem B1891235 : Blo 1120629 1891235 := bstep (se 1 (by rfl) ⟨1418426, by rfl⟩ : syracuseStep 1891235 = 2836853) B2836853
theorem B3791825 : Blo 1120629 3791825 := bstep (se 2 (by rfl) ⟨1421934, by rfl⟩ : syracuseStep 3791825 = 2843869) B2843869
theorem B1596385 : Blo 1120629 1596385 := bstep (se 2 (by rfl) ⟨598644, by rfl⟩ : syracuseStep 1596385 = 1197289) B1197289
theorem B1891363 : Blo 1120629 1891363 := bstep (se 1 (by rfl) ⟨1418522, by rfl⟩ : syracuseStep 1891363 = 2837045) B2837045
theorem B2841713 : Blo 1120629 2841713 := bstep (se 2 (by rfl) ⟨1065642, by rfl⟩ : syracuseStep 2841713 = 2131285) B2131285
theorem B2022545 : Blo 1120629 2022545 := bstep (se 2 (by rfl) ⟨758454, by rfl⟩ : syracuseStep 2022545 = 1516909) B1516909
theorem B2841763 : Blo 1120629 2841763 := bstep (se 1 (by rfl) ⟨2131322, by rfl⟩ : syracuseStep 2841763 = 4262645) B4262645
theorem B1891505 : Blo 1120629 1891505 := bstep (se 2 (by rfl) ⟨709314, by rfl⟩ : syracuseStep 1891505 = 1418629) B1418629
theorem B1891633 : Blo 1120629 1891633 := bstep (se 2 (by rfl) ⟨709362, by rfl⟩ : syracuseStep 1891633 = 1418725) B1418725
theorem B2841905 : Blo 1120629 2841905 := bstep (se 2 (by rfl) ⟨1065714, by rfl⟩ : syracuseStep 2841905 = 2131429) B2131429
theorem B1891667 : Blo 1120629 1891667 := bstep (se 1 (by rfl) ⟨1418750, by rfl⟩ : syracuseStep 1891667 = 2837501) B2837501
theorem B3595661 : Blo 1120629 3595661 := bstep (se 3 (by rfl) ⟨674186, by rfl⟩ : syracuseStep 3595661 = 1348373) B1348373
theorem B2022833 : Blo 1120629 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B1891795 : Blo 1120629 1891795 := bstep (se 1 (by rfl) ⟨1418846, by rfl⟩ : syracuseStep 1891795 = 2837693) B2837693
theorem B24305123 : Blo 1120629 24305123 := bstep (se 1 (by rfl) ⟨18228842, by rfl⟩ : syracuseStep 24305123 = 36457685) B36457685
theorem B3792365 : Blo 1120629 3792365 := bstep (se 3 (by rfl) ⟨711068, by rfl⟩ : syracuseStep 3792365 = 1422137) B1422137
theorem B1334803 : Blo 1120629 1334803 := bstep (se 1 (by rfl) ⟨1001102, by rfl⟩ : syracuseStep 1334803 = 2002205) B2002205
theorem B3792419 : Blo 1120629 3792419 := bstep (se 1 (by rfl) ⟨2844314, by rfl⟩ : syracuseStep 3792419 = 5688629) B5688629
theorem B1891937 : Blo 1120629 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B3038833 : Blo 1120629 3038833 := bstep (se 2 (by rfl) ⟨1139562, by rfl⟩ : syracuseStep 3038833 = 2279125) B2279125
theorem B1892065 : Blo 1120629 1892065 := bstep (se 2 (by rfl) ⟨709524, by rfl⟩ : syracuseStep 1892065 = 1419049) B1419049
theorem B1597171 : Blo 1120629 1597171 := bstep (se 1 (by rfl) ⟨1197878, by rfl⟩ : syracuseStep 1597171 = 2395757) B2395757
theorem B1892099 : Blo 1120629 1892099 := bstep (se 1 (by rfl) ⟨1419074, by rfl⟩ : syracuseStep 1892099 = 2838149) B2838149
theorem B3792689 : Blo 1120629 3792689 := bstep (se 2 (by rfl) ⟨1422258, by rfl⟩ : syracuseStep 3792689 = 2844517) B2844517
theorem B1892227 : Blo 1120629 1892227 := bstep (se 1 (by rfl) ⟨1419170, by rfl⟩ : syracuseStep 1892227 = 2838341) B2838341
theorem B1892369 : Blo 1120629 1892369 := bstep (se 2 (by rfl) ⟨709638, by rfl⟩ : syracuseStep 1892369 = 1419277) B1419277
theorem B18702389 : Blo 1120629 18702389 := bstep (se 5 (by rfl) ⟨876674, by rfl⟩ : syracuseStep 18702389 = 1753349) B1753349
theorem B1892497 : Blo 1120629 1892497 := bstep (se 2 (by rfl) ⟨709686, by rfl⟩ : syracuseStep 1892497 = 1419373) B1419373
theorem B1892531 : Blo 1120629 1892531 := bstep (se 1 (by rfl) ⟨1419398, by rfl⟩ : syracuseStep 1892531 = 2838797) B2838797
theorem B1597649 : Blo 1120629 1597649 := bstep (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) B1198237
theorem B2023633 : Blo 1120629 2023633 := bstep (se 2 (by rfl) ⟨758862, by rfl⟩ : syracuseStep 2023633 = 1517725) B1517725
theorem B2842897 : Blo 1120629 2842897 := bstep (se 2 (by rfl) ⟨1066086, by rfl⟩ : syracuseStep 2842897 = 2132173) B2132173
theorem B1138979 : Blo 1120629 1138979 := bstep (se 1 (by rfl) ⟨854234, by rfl⟩ : syracuseStep 1138979 = 1708469) B1708469
theorem B1892659 : Blo 1120629 1892659 := bstep (se 1 (by rfl) ⟨1419494, by rfl⟩ : syracuseStep 1892659 = 2838989) B2838989
theorem B1597763 : Blo 1120629 1597763 := bstep (se 1 (by rfl) ⟨1198322, by rfl⟩ : syracuseStep 1597763 = 2396645) B2396645
theorem B3793229 : Blo 1120629 3793229 := bstep (se 3 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 3793229 = 1422461) B1422461
theorem B2220419 : Blo 1120629 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B3793283 : Blo 1120629 3793283 := bstep (se 1 (by rfl) ⟨2844962, by rfl⟩ : syracuseStep 3793283 = 5689925) B5689925
theorem B1597843 : Blo 1120629 1597843 := bstep (se 1 (by rfl) ⟨1198382, by rfl⟩ : syracuseStep 1597843 = 2396765) B2396765
theorem B1892801 : Blo 1120629 1892801 := bstep (se 2 (by rfl) ⟨709800, by rfl⟩ : syracuseStep 1892801 = 1419601) B1419601
theorem B2843171 : Blo 1120629 2843171 := bstep (se 1 (by rfl) ⟨2132378, by rfl⟩ : syracuseStep 2843171 = 4264757) B4264757
theorem B1892929 : Blo 1120629 1892929 := bstep (se 2 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 1892929 = 1419697) B1419697
theorem B1892963 : Blo 1120629 1892963 := bstep (se 1 (by rfl) ⟨1419722, by rfl⟩ : syracuseStep 1892963 = 2839445) B2839445
theorem B3793553 : Blo 1120629 3793553 := bstep (se 2 (by rfl) ⟨1422582, by rfl⟩ : syracuseStep 3793553 = 2845165) B2845165
theorem B1893091 : Blo 1120629 1893091 := bstep (se 1 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 1893091 = 2839637) B2839637
theorem B2843363 : Blo 1120629 2843363 := bstep (se 1 (by rfl) ⟨2132522, by rfl⟩ : syracuseStep 2843363 = 4265045) B4265045
theorem B1893233 : Blo 1120629 1893233 := bstep (se 2 (by rfl) ⟨709962, by rfl⟩ : syracuseStep 1893233 = 1419925) B1419925
theorem B1598401 : Blo 1120629 1598401 := bstep (se 2 (by rfl) ⟨599400, by rfl⟩ : syracuseStep 1598401 = 1198801) B1198801
theorem B6382577 : Blo 1120629 6382577 := bstep (se 2 (by rfl) ⟨2393466, by rfl⟩ : syracuseStep 6382577 = 4786933) B4786933
theorem B1893361 : Blo 1120629 1893361 := bstep (se 2 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 1893361 = 1420021) B1420021
theorem B1893395 : Blo 1120629 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B1893523 : Blo 1120629 1893523 := bstep (se 1 (by rfl) ⟨1420142, by rfl⟩ : syracuseStep 1893523 = 2840285) B2840285
theorem B3794093 : Blo 1120629 3794093 := bstep (se 3 (by rfl) ⟨711392, by rfl⟩ : syracuseStep 3794093 = 1422785) B1422785
theorem B3794147 : Blo 1120629 3794147 := bstep (se 1 (by rfl) ⟨2845610, by rfl⟩ : syracuseStep 3794147 = 5691221) B5691221
theorem B7202033 : Blo 1120629 7202033 := bstep (se 2 (by rfl) ⟨2700762, by rfl⟩ : syracuseStep 7202033 = 5401525) B5401525
theorem B1795331 : Blo 1120629 1795331 := bstep (se 1 (by rfl) ⟨1346498, by rfl⟩ : syracuseStep 1795331 = 2692997) B2692997
theorem B3597581 : Blo 1120629 3597581 := bstep (se 3 (by rfl) ⟨674546, by rfl⟩ : syracuseStep 3597581 = 1349093) B1349093
theorem B1893665 : Blo 1120629 1893665 := bstep (se 2 (by rfl) ⟨710124, by rfl⟩ : syracuseStep 1893665 = 1420249) B1420249
theorem B1893793 : Blo 1120629 1893793 := bstep (se 2 (by rfl) ⟨710172, by rfl⟩ : syracuseStep 1893793 = 1420345) B1420345
theorem B1893827 : Blo 1120629 1893827 := bstep (se 1 (by rfl) ⟨1420370, by rfl⟩ : syracuseStep 1893827 = 2840741) B2840741
theorem B3794417 : Blo 1120629 3794417 := bstep (se 2 (by rfl) ⟨1422906, by rfl⟩ : syracuseStep 3794417 = 2845813) B2845813
theorem B1893955 : Blo 1120629 1893955 := bstep (se 1 (by rfl) ⟨1420466, by rfl⟩ : syracuseStep 1893955 = 2840933) B2840933
theorem B1599107 : Blo 1120629 1599107 := bstep (se 1 (by rfl) ⟨1199330, by rfl⟩ : syracuseStep 1599107 = 2398661) B2398661
theorem B2844305 : Blo 1120629 2844305 := bstep (se 2 (by rfl) ⟨1066614, by rfl⟩ : syracuseStep 2844305 = 2133229) B2133229
theorem B2844355 : Blo 1120629 2844355 := bstep (se 1 (by rfl) ⟨2133266, by rfl⟩ : syracuseStep 2844355 = 4266533) B4266533
theorem B2025155 : Blo 1120629 2025155 := bstep (se 1 (by rfl) ⟨1518866, by rfl⟩ : syracuseStep 2025155 = 3037733) B3037733
theorem B1894097 : Blo 1120629 1894097 := bstep (se 2 (by rfl) ⟨710286, by rfl⟩ : syracuseStep 1894097 = 1420573) B1420573
theorem B16181045 : Blo 1120629 16181045 := bstep (se 5 (by rfl) ⟨758486, by rfl⟩ : syracuseStep 16181045 = 1516973) B1516973
theorem B1894225 : Blo 1120629 1894225 := bstep (se 2 (by rfl) ⟨710334, by rfl⟩ : syracuseStep 1894225 = 1420669) B1420669
theorem B2844497 : Blo 1120629 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B1894259 : Blo 1120629 1894259 := bstep (se 1 (by rfl) ⟨1420694, by rfl⟩ : syracuseStep 1894259 = 2841389) B2841389
theorem B10250225 : Blo 1120629 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B1894387 : Blo 1120629 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B3794957 : Blo 1120629 3794957 := bstep (se 3 (by rfl) ⟨711554, by rfl⟩ : syracuseStep 3794957 = 1423109) B1423109
theorem B3795011 : Blo 1120629 3795011 := bstep (se 1 (by rfl) ⟨2846258, by rfl⟩ : syracuseStep 3795011 = 5692517) B5692517
theorem B1796177 : Blo 1120629 1796177 := bstep (se 2 (by rfl) ⟨673566, by rfl⟩ : syracuseStep 1796177 = 1347133) B1347133
theorem B58386545 : Blo 1120629 58386545 := bstep (se 2 (by rfl) ⟨21894954, by rfl⟩ : syracuseStep 58386545 = 43789909) B43789909
theorem B1894529 : Blo 1120629 1894529 := bstep (se 2 (by rfl) ⟨710448, by rfl⟩ : syracuseStep 1894529 = 1420897) B1420897
theorem B1894657 : Blo 1120629 1894657 := bstep (se 2 (by rfl) ⟨710496, by rfl⟩ : syracuseStep 1894657 = 1420993) B1420993
theorem B1599745 : Blo 1120629 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B1894691 : Blo 1120629 1894691 := bstep (se 1 (by rfl) ⟨1421018, by rfl⟩ : syracuseStep 1894691 = 2842037) B2842037
theorem B3795281 : Blo 1120629 3795281 := bstep (se 2 (by rfl) ⟨1423230, by rfl⟩ : syracuseStep 3795281 = 2846461) B2846461
theorem B1599859 : Blo 1120629 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B6384035 : Blo 1120629 6384035 := bstep (se 1 (by rfl) ⟨4788026, by rfl⟩ : syracuseStep 6384035 = 9576053) B9576053
theorem B1894819 : Blo 1120629 1894819 := bstep (se 1 (by rfl) ⟨1421114, by rfl⟩ : syracuseStep 1894819 = 2842229) B2842229
theorem B1894961 : Blo 1120629 1894961 := bstep (se 2 (by rfl) ⟨710610, by rfl⟩ : syracuseStep 1894961 = 1421221) B1421221
theorem B1796689 : Blo 1120629 1796689 := bstep (se 2 (by rfl) ⟨673758, by rfl⟩ : syracuseStep 1796689 = 1347517) B1347517
theorem B1895089 : Blo 1120629 1895089 := bstep (se 2 (by rfl) ⟨710658, by rfl⟩ : syracuseStep 1895089 = 1421317) B1421317
theorem B1895123 : Blo 1120629 1895123 := bstep (se 1 (by rfl) ⟨1421342, by rfl⟩ : syracuseStep 1895123 = 2842685) B2842685
theorem B3074861 : Blo 1120629 3074861 := bstep (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) B1153073
theorem B2845489 : Blo 1120629 2845489 := bstep (se 2 (by rfl) ⟨1067058, by rfl⟩ : syracuseStep 2845489 = 2134117) B2134117
theorem B2026307 : Blo 1120629 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B1895251 : Blo 1120629 1895251 := bstep (se 1 (by rfl) ⟨1421438, by rfl⟩ : syracuseStep 1895251 = 2842877) B2842877
theorem B1895393 : Blo 1120629 1895393 := bstep (se 2 (by rfl) ⟨710772, by rfl⟩ : syracuseStep 1895393 = 1421545) B1421545
theorem B2845763 : Blo 1120629 2845763 := bstep (se 1 (by rfl) ⟨2134322, by rfl⟩ : syracuseStep 2845763 = 4268645) B4268645
theorem B1895521 : Blo 1120629 1895521 := bstep (se 2 (by rfl) ⟨710820, by rfl⟩ : syracuseStep 1895521 = 1421641) B1421641
theorem B1895555 : Blo 1120629 1895555 := bstep (se 1 (by rfl) ⟨1421666, by rfl⟩ : syracuseStep 1895555 = 2843333) B2843333
theorem B1797299 : Blo 1120629 1797299 := bstep (se 1 (by rfl) ⟨1347974, by rfl⟩ : syracuseStep 1797299 = 2695949) B2695949
theorem B1895683 : Blo 1120629 1895683 := bstep (se 1 (by rfl) ⟨1421762, by rfl⟩ : syracuseStep 1895683 = 2843525) B2843525
theorem B2845955 : Blo 1120629 2845955 := bstep (se 1 (by rfl) ⟨2134466, by rfl⟩ : syracuseStep 2845955 = 4268933) B4268933
theorem B1895825 : Blo 1120629 1895825 := bstep (se 2 (by rfl) ⟨710934, by rfl⟩ : syracuseStep 1895825 = 1421869) B1421869
theorem B3599761 : Blo 1120629 3599761 := bstep (se 2 (by rfl) ⟨1349910, by rfl⟩ : syracuseStep 3599761 = 2699821) B2699821
theorem B1895953 : Blo 1120629 1895953 := bstep (se 2 (by rfl) ⟨710982, by rfl⟩ : syracuseStep 1895953 = 1421965) B1421965
theorem B1895987 : Blo 1120629 1895987 := bstep (se 1 (by rfl) ⟨1421990, by rfl⟩ : syracuseStep 1895987 = 2843981) B2843981
theorem B3599939 : Blo 1120629 3599939 := bstep (se 1 (by rfl) ⟨2699954, by rfl⟩ : syracuseStep 3599939 = 5399909) B5399909
theorem B2158211 : Blo 1120629 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B1896115 : Blo 1120629 1896115 := bstep (se 1 (by rfl) ⟨1422086, by rfl⟩ : syracuseStep 1896115 = 2844173) B2844173
theorem B1601203 : Blo 1120629 1601203 := bstep (se 1 (by rfl) ⟨1200902, by rfl⟩ : syracuseStep 1601203 = 2401805) B2401805
theorem B4255523 : Blo 1120629 4255523 := bstep (se 1 (by rfl) ⟨3191642, by rfl⟩ : syracuseStep 4255523 = 6383285) B6383285
theorem B4255537 : Blo 1120629 4255537 := bstep (se 2 (by rfl) ⟨1595826, by rfl⟩ : syracuseStep 4255537 = 3191653) B3191653
theorem B1896257 : Blo 1120629 1896257 := bstep (se 2 (by rfl) ⟨711096, by rfl⟩ : syracuseStep 1896257 = 1422193) B1422193
theorem B7597901 : Blo 1120629 7597901 := bstep (se 3 (by rfl) ⟨1424606, by rfl⟩ : syracuseStep 7597901 = 2849213) B2849213
theorem B2158417 : Blo 1120629 2158417 := bstep (se 2 (by rfl) ⟨809406, by rfl⟩ : syracuseStep 2158417 = 1618813) B1618813
theorem B1896385 : Blo 1120629 1896385 := bstep (se 2 (by rfl) ⟨711144, by rfl⟩ : syracuseStep 1896385 = 1422289) B1422289
theorem B1896419 : Blo 1120629 1896419 := bstep (se 1 (by rfl) ⟨1422314, by rfl⟩ : syracuseStep 1896419 = 2844629) B2844629
theorem B1896547 : Blo 1120629 1896547 := bstep (se 1 (by rfl) ⟨1422410, by rfl⟩ : syracuseStep 1896547 = 2844821) B2844821
theorem B1798291 : Blo 1120629 1798291 := bstep (se 1 (by rfl) ⟨1348718, by rfl⟩ : syracuseStep 1798291 = 2697437) B2697437
theorem B1896689 : Blo 1120629 1896689 := bstep (se 2 (by rfl) ⟨711258, by rfl⟩ : syracuseStep 1896689 = 1422517) B1422517
theorem B1732963 : Blo 1120629 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B1896817 : Blo 1120629 1896817 := bstep (se 2 (by rfl) ⟨711306, by rfl⟩ : syracuseStep 1896817 = 1422613) B1422613
theorem B1896851 : Blo 1120629 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B2879921 : Blo 1120629 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B1896979 : Blo 1120629 1896979 := bstep (se 1 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 1896979 = 2845469) B2845469
theorem B1733233 : Blo 1120629 1733233 := bstep (se 2 (by rfl) ⟨649962, by rfl⟩ : syracuseStep 1733233 = 1299925) B1299925
theorem B1897121 : Blo 1120629 1897121 := bstep (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) B1422841
theorem B8090381 : Blo 1120629 8090381 := bstep (se 3 (by rfl) ⟨1516946, by rfl⟩ : syracuseStep 8090381 = 3033893) B3033893
theorem B1897249 : Blo 1120629 1897249 := bstep (se 2 (by rfl) ⟨711468, by rfl⟩ : syracuseStep 1897249 = 1422937) B1422937
theorem B1897283 : Blo 1120629 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B1897411 : Blo 1120629 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B9597923 : Blo 1120629 9597923 := bstep (se 1 (by rfl) ⟨7198442, by rfl⟩ : syracuseStep 9597923 = 14396885) B14396885
theorem B1799201 : Blo 1120629 1799201 := bstep (se 2 (by rfl) ⟨674700, by rfl⟩ : syracuseStep 1799201 = 1349401) B1349401
theorem B1897553 : Blo 1120629 1897553 := bstep (se 2 (by rfl) ⟨711582, by rfl⟩ : syracuseStep 1897553 = 1423165) B1423165
theorem B1799329 : Blo 1120629 1799329 := bstep (se 2 (by rfl) ⟨674748, by rfl⟩ : syracuseStep 1799329 = 1349497) B1349497
theorem B1897681 : Blo 1120629 1897681 := bstep (se 2 (by rfl) ⟨711630, by rfl⟩ : syracuseStep 1897681 = 1423261) B1423261
theorem B4256995 : Blo 1120629 4256995 := bstep (se 1 (by rfl) ⟨3192746, by rfl⟩ : syracuseStep 4256995 = 6385493) B6385493
theorem B1897715 : Blo 1120629 1897715 := bstep (se 1 (by rfl) ⟨1423286, by rfl⟩ : syracuseStep 1897715 = 2846573) B2846573
theorem B3601709 : Blo 1120629 3601709 := bstep (se 3 (by rfl) ⟨675320, by rfl⟩ : syracuseStep 3601709 = 1350641) B1350641
theorem B13661621 : Blo 1120629 13661621 := bstep (se 5 (by rfl) ⟨640388, by rfl⟩ : syracuseStep 13661621 = 1280777) B1280777
theorem B9369101 : Blo 1120629 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B6060109 : Blo 1120629 6060109 := bstep (se 3 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 6060109 = 2272541) B2272541
theorem B1800323 : Blo 1120629 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B4553059 : Blo 1120629 4553059 := bstep (se 1 (by rfl) ⟨3414794, by rfl⟩ : syracuseStep 4553059 = 6829589) B6829589
theorem B2521457 : Blo 1120629 2521457 := bstep (se 2 (by rfl) ⟨945546, by rfl⟩ : syracuseStep 2521457 = 1891093) B1891093
theorem B2521475 : Blo 1120629 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B2128369 : Blo 1120629 2128369 := bstep (se 2 (by rfl) ⟨798138, by rfl⟩ : syracuseStep 2128369 = 1596277) B1596277
theorem B2521745 : Blo 1120629 2521745 := bstep (se 2 (by rfl) ⟨945654, by rfl⟩ : syracuseStep 2521745 = 1891309) B1891309
theorem B2521763 : Blo 1120629 2521763 := bstep (se 1 (by rfl) ⟨1891322, by rfl⟩ : syracuseStep 2521763 = 3782645) B3782645
theorem B2128771 : Blo 1120629 2128771 := bstep (se 1 (by rfl) ⟨1596578, by rfl⟩ : syracuseStep 2128771 = 3193157) B3193157
theorem B2522033 : Blo 1120629 2522033 := bstep (se 2 (by rfl) ⟨945762, by rfl⟩ : syracuseStep 2522033 = 1891525) B1891525
theorem B2128817 : Blo 1120629 2128817 := bstep (se 2 (by rfl) ⟨798306, by rfl⟩ : syracuseStep 2128817 = 1596613) B1596613
theorem B2522051 : Blo 1120629 2522051 := bstep (se 1 (by rfl) ⟨1891538, by rfl⟩ : syracuseStep 2522051 = 3783077) B3783077
theorem B2522321 : Blo 1120629 2522321 := bstep (se 2 (by rfl) ⟨945870, by rfl⟩ : syracuseStep 2522321 = 1891741) B1891741
theorem B2129105 : Blo 1120629 2129105 := bstep (se 2 (by rfl) ⟨798414, by rfl⟩ : syracuseStep 2129105 = 1596829) B1596829
theorem B2522339 : Blo 1120629 2522339 := bstep (se 1 (by rfl) ⟨1891754, by rfl⟩ : syracuseStep 2522339 = 3783509) B3783509
theorem B4095281 : Blo 1120629 4095281 := bstep (se 2 (by rfl) ⟨1535730, by rfl⟩ : syracuseStep 4095281 = 3071461) B3071461
theorem B4259213 : Blo 1120629 4259213 := bstep (se 3 (by rfl) ⟨798602, by rfl⟩ : syracuseStep 4259213 = 1597205) B1597205
theorem B10255843 : Blo 1120629 10255843 := bstep (se 1 (by rfl) ⟨7691882, by rfl⟩ : syracuseStep 10255843 = 15383765) B15383765
theorem B2522609 : Blo 1120629 2522609 := bstep (se 2 (by rfl) ⟨945978, by rfl⟩ : syracuseStep 2522609 = 1891957) B1891957
theorem B2522627 : Blo 1120629 2522627 := bstep (se 1 (by rfl) ⟨1891970, by rfl⟩ : syracuseStep 2522627 = 3783941) B3783941
theorem B11501297 : Blo 1120629 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B2522897 : Blo 1120629 2522897 := bstep (se 2 (by rfl) ⟨946086, by rfl⟩ : syracuseStep 2522897 = 1892173) B1892173
theorem B2522915 : Blo 1120629 2522915 := bstep (se 1 (by rfl) ⟨1892186, by rfl⟩ : syracuseStep 2522915 = 3784373) B3784373
theorem B2129827 : Blo 1120629 2129827 := bstep (se 1 (by rfl) ⟨1597370, by rfl⟩ : syracuseStep 2129827 = 3194741) B3194741
theorem B6913997 : Blo 1120629 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B2129971 : Blo 1120629 2129971 := bstep (se 1 (by rfl) ⟨1597478, by rfl⟩ : syracuseStep 2129971 = 3194957) B3194957
theorem B2523275 : Blo 1120629 2523275 := bstep (se 1 (by rfl) ⟨1892456, by rfl⟩ : syracuseStep 2523275 = 3784913) B3784913
theorem B1704089 : Blo 1120629 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B2523329 : Blo 1120629 2523329 := bstep (se 2 (by rfl) ⟨946248, by rfl⟩ : syracuseStep 2523329 = 1892497) B1892497
theorem B4260185 : Blo 1120629 4260185 := bstep (se 2 (by rfl) ⟨1597569, by rfl⟩ : syracuseStep 4260185 = 3195139) B3195139
theorem B2523545 : Blo 1120629 2523545 := bstep (se 2 (by rfl) ⟨946329, by rfl⟩ : syracuseStep 2523545 = 1892659) B1892659
theorem B2523635 : Blo 1120629 2523635 := bstep (se 1 (by rfl) ⟨1892726, by rfl⟩ : syracuseStep 2523635 = 3785453) B3785453
theorem B2523671 : Blo 1120629 2523671 := bstep (se 1 (by rfl) ⟨1892753, by rfl⟩ : syracuseStep 2523671 = 3785507) B3785507
theorem B2130457 : Blo 1120629 2130457 := bstep (se 2 (by rfl) ⟨798921, by rfl⟩ : syracuseStep 2130457 = 1597843) B1597843
theorem B4260397 : Blo 1120629 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B2523851 : Blo 1120629 2523851 := bstep (se 1 (by rfl) ⟨1892888, by rfl⟩ : syracuseStep 2523851 = 3785777) B3785777
theorem B2523905 : Blo 1120629 2523905 := bstep (se 2 (by rfl) ⟨946464, by rfl⟩ : syracuseStep 2523905 = 1892929) B1892929
theorem B5473099 : Blo 1120629 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B10257227 : Blo 1120629 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B4260701 : Blo 1120629 4260701 := bstep (se 3 (by rfl) ⟨798881, by rfl⟩ : syracuseStep 4260701 = 1597763) B1597763
theorem B2524121 : Blo 1120629 2524121 := bstep (se 2 (by rfl) ⟨946545, by rfl⟩ : syracuseStep 2524121 = 1893091) B1893091
theorem B2524211 : Blo 1120629 2524211 := bstep (se 1 (by rfl) ⟨1893158, by rfl⟩ : syracuseStep 2524211 = 3786317) B3786317
theorem B2131019 : Blo 1120629 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B2524247 : Blo 1120629 2524247 := bstep (se 1 (by rfl) ⟨1893185, by rfl⟩ : syracuseStep 2524247 = 3786371) B3786371
theorem B2131201 : Blo 1120629 2131201 := bstep (se 2 (by rfl) ⟨799200, by rfl⟩ : syracuseStep 2131201 = 1598401) B1598401
theorem B2524427 : Blo 1120629 2524427 := bstep (se 1 (by rfl) ⟨1893320, by rfl⟩ : syracuseStep 2524427 = 3786641) B3786641
theorem B2524481 : Blo 1120629 2524481 := bstep (se 2 (by rfl) ⟨946680, by rfl⟩ : syracuseStep 2524481 = 1893361) B1893361
theorem B2393459 : Blo 1120629 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B8095249 : Blo 1120629 8095249 := bstep (se 2 (by rfl) ⟨3035718, by rfl⟩ : syracuseStep 8095249 = 6071437) B6071437
theorem B2524697 : Blo 1120629 2524697 := bstep (se 2 (by rfl) ⟨946761, by rfl⟩ : syracuseStep 2524697 = 1893523) B1893523
theorem B2524787 : Blo 1120629 2524787 := bstep (se 1 (by rfl) ⟨1893590, by rfl⟩ : syracuseStep 2524787 = 3787181) B3787181
theorem B2524823 : Blo 1120629 2524823 := bstep (se 1 (by rfl) ⟨1893617, by rfl⟩ : syracuseStep 2524823 = 3787235) B3787235
theorem B3245719 : Blo 1120629 3245719 := bstep (se 1 (by rfl) ⟨2434289, by rfl⟩ : syracuseStep 3245719 = 4868579) B4868579
theorem B2525003 : Blo 1120629 2525003 := bstep (se 1 (by rfl) ⟨1893752, by rfl⟩ : syracuseStep 2525003 = 3787505) B3787505
theorem B2525057 : Blo 1120629 2525057 := bstep (se 2 (by rfl) ⟨946896, by rfl⟩ : syracuseStep 2525057 = 1893793) B1893793
theorem B7014275 : Blo 1120629 7014275 := bstep (se 1 (by rfl) ⟨5260706, by rfl⟩ : syracuseStep 7014275 = 10521413) B10521413
theorem B2131915 : Blo 1120629 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B2131991 : Blo 1120629 2131991 := bstep (se 1 (by rfl) ⟨1598993, by rfl⟩ : syracuseStep 2131991 = 3197987) B3197987
theorem B2426945 : Blo 1120629 2426945 := bstep (se 2 (by rfl) ⟨910104, by rfl⟩ : syracuseStep 2426945 = 1820209) B1820209
theorem B2525273 : Blo 1120629 2525273 := bstep (se 2 (by rfl) ⟨946977, by rfl⟩ : syracuseStep 2525273 = 1893955) B1893955
theorem B2525363 : Blo 1120629 2525363 := bstep (se 1 (by rfl) ⟨1894022, by rfl⟩ : syracuseStep 2525363 = 3788045) B3788045
theorem B2525399 : Blo 1120629 2525399 := bstep (se 1 (by rfl) ⟨1894049, by rfl⟩ : syracuseStep 2525399 = 3788099) B3788099
theorem B2394355 : Blo 1120629 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B2525579 : Blo 1120629 2525579 := bstep (se 1 (by rfl) ⟨1894184, by rfl⟩ : syracuseStep 2525579 = 3788369) B3788369
theorem B2525633 : Blo 1120629 2525633 := bstep (se 2 (by rfl) ⟨947112, by rfl⟩ : syracuseStep 2525633 = 1894225) B1894225
theorem B4557329 : Blo 1120629 4557329 := bstep (se 2 (by rfl) ⟨1708998, by rfl⟩ : syracuseStep 4557329 = 3417997) B3417997
theorem B2525849 : Blo 1120629 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B2132659 : Blo 1120629 2132659 := bstep (se 1 (by rfl) ⟨1599494, by rfl⟩ : syracuseStep 2132659 = 3198989) B3198989
theorem B12782285 : Blo 1120629 12782285 := bstep (se 3 (by rfl) ⟨2396678, by rfl⟩ : syracuseStep 12782285 = 4793357) B4793357
theorem B2525939 : Blo 1120629 2525939 := bstep (se 1 (by rfl) ⟨1894454, by rfl⟩ : syracuseStep 2525939 = 3788909) B3788909
theorem B2525975 : Blo 1120629 2525975 := bstep (se 1 (by rfl) ⟨1894481, by rfl⟩ : syracuseStep 2525975 = 3788963) B3788963
theorem B2132887 : Blo 1120629 2132887 := bstep (se 1 (by rfl) ⟨1599665, by rfl⟩ : syracuseStep 2132887 = 3199331) B3199331
theorem B2526155 : Blo 1120629 2526155 := bstep (se 1 (by rfl) ⟨1894616, by rfl⟩ : syracuseStep 2526155 = 3789233) B3789233
theorem B2526209 : Blo 1120629 2526209 := bstep (se 2 (by rfl) ⟨947328, by rfl⟩ : syracuseStep 2526209 = 1894657) B1894657
theorem B2132993 : Blo 1120629 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B4787275 : Blo 1120629 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B2133145 : Blo 1120629 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B2526425 : Blo 1120629 2526425 := bstep (se 2 (by rfl) ⟨947409, by rfl⟩ : syracuseStep 2526425 = 1894819) B1894819
theorem B2395415 : Blo 1120629 2395415 := bstep (se 1 (by rfl) ⟨1796561, by rfl⟩ : syracuseStep 2395415 = 3593123) B3593123
theorem B2526515 : Blo 1120629 2526515 := bstep (se 1 (by rfl) ⟨1894886, by rfl⟩ : syracuseStep 2526515 = 3789773) B3789773
theorem B17272129 : Blo 1120629 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B2526551 : Blo 1120629 2526551 := bstep (se 1 (by rfl) ⟨1894913, by rfl⟩ : syracuseStep 2526551 = 3789827) B3789827
theorem B4787549 : Blo 1120629 4787549 := bstep (se 3 (by rfl) ⟨897665, by rfl⟩ : syracuseStep 4787549 = 1795331) B1795331
theorem B4263299 : Blo 1120629 4263299 := bstep (se 1 (by rfl) ⟨3197474, by rfl⟩ : syracuseStep 4263299 = 6394949) B6394949
theorem B4263313 : Blo 1120629 4263313 := bstep (se 2 (by rfl) ⟨1598742, by rfl⟩ : syracuseStep 4263313 = 3197485) B3197485
theorem B6393239 : Blo 1120629 6393239 := bstep (se 1 (by rfl) ⟨4794929, by rfl⟩ : syracuseStep 6393239 = 9589859) B9589859
theorem B2395585 : Blo 1120629 2395585 := bstep (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) B1796689
theorem B2526731 : Blo 1120629 2526731 := bstep (se 1 (by rfl) ⟨1895048, by rfl⟩ : syracuseStep 2526731 = 3790097) B3790097
theorem B2428481 : Blo 1120629 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B2526785 : Blo 1120629 2526785 := bstep (se 2 (by rfl) ⟨947544, by rfl⟩ : syracuseStep 2526785 = 1895089) B1895089
theorem B4263617 : Blo 1120629 4263617 := bstep (se 2 (by rfl) ⟨1598856, by rfl⟩ : syracuseStep 4263617 = 3197713) B3197713
theorem B2395927 : Blo 1120629 2395927 := bstep (se 1 (by rfl) ⟨1796945, by rfl⟩ : syracuseStep 2395927 = 3593891) B3593891
theorem B2527001 : Blo 1120629 2527001 := bstep (se 2 (by rfl) ⟨947625, by rfl⟩ : syracuseStep 2527001 = 1895251) B1895251
theorem B2527091 : Blo 1120629 2527091 := bstep (se 1 (by rfl) ⟨1895318, by rfl⟩ : syracuseStep 2527091 = 3790637) B3790637
theorem B2527127 : Blo 1120629 2527127 := bstep (se 1 (by rfl) ⟨1895345, by rfl⟩ : syracuseStep 2527127 = 3790691) B3790691
theorem B2428825 : Blo 1120629 2428825 := bstep (se 2 (by rfl) ⟨910809, by rfl⟩ : syracuseStep 2428825 = 1821619) B1821619
theorem B6066251 : Blo 1120629 6066251 := bstep (se 1 (by rfl) ⟨4549688, by rfl⟩ : syracuseStep 6066251 = 9099377) B9099377
theorem B2527307 : Blo 1120629 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B2527361 : Blo 1120629 2527361 := bstep (se 2 (by rfl) ⟨947760, by rfl⟩ : syracuseStep 2527361 = 1895521) B1895521
theorem B8523953 : Blo 1120629 8523953 := bstep (se 2 (by rfl) ⟨3196482, by rfl⟩ : syracuseStep 8523953 = 6392965) B6392965
theorem B2527577 : Blo 1120629 2527577 := bstep (se 2 (by rfl) ⟨947841, by rfl⟩ : syracuseStep 2527577 = 1895683) B1895683
theorem B4264285 : Blo 1120629 4264285 := bstep (se 3 (by rfl) ⟨799553, by rfl⟩ : syracuseStep 4264285 = 1599107) B1599107
theorem B6820247 : Blo 1120629 6820247 := bstep (se 1 (by rfl) ⟨5115185, by rfl⟩ : syracuseStep 6820247 = 10230371) B10230371
theorem B2527667 : Blo 1120629 2527667 := bstep (se 1 (by rfl) ⟨1895750, by rfl⟩ : syracuseStep 2527667 = 3791501) B3791501
theorem B2134451 : Blo 1120629 2134451 := bstep (se 1 (by rfl) ⟨1600838, by rfl⟩ : syracuseStep 2134451 = 3201677) B3201677
theorem B2527703 : Blo 1120629 2527703 := bstep (se 1 (by rfl) ⟨1895777, by rfl⟩ : syracuseStep 2527703 = 3791555) B3791555
theorem B2396747 : Blo 1120629 2396747 := bstep (se 1 (by rfl) ⟨1797560, by rfl⟩ : syracuseStep 2396747 = 3595121) B3595121
theorem B2134603 : Blo 1120629 2134603 := bstep (se 1 (by rfl) ⟨1600952, by rfl⟩ : syracuseStep 2134603 = 3201905) B3201905
theorem B2527883 : Blo 1120629 2527883 := bstep (se 1 (by rfl) ⟨1895912, by rfl⟩ : syracuseStep 2527883 = 3791825) B3791825
theorem B8524439 : Blo 1120629 8524439 := bstep (se 1 (by rfl) ⟨6393329, by rfl⟩ : syracuseStep 8524439 = 12786659) B12786659
theorem B2527937 : Blo 1120629 2527937 := bstep (se 2 (by rfl) ⟨947976, by rfl⟩ : syracuseStep 2527937 = 1895953) B1895953
theorem B1348363 : Blo 1120629 1348363 := bstep (se 1 (by rfl) ⟨1011272, by rfl⟩ : syracuseStep 1348363 = 2022545) B2022545
theorem B2528153 : Blo 1120629 2528153 := bstep (se 2 (by rfl) ⟨948057, by rfl⟩ : syracuseStep 2528153 = 1896115) B1896115
theorem B2134937 : Blo 1120629 2134937 := bstep (se 2 (by rfl) ⟨800601, by rfl⟩ : syracuseStep 2134937 = 1601203) B1601203
theorem B2397107 : Blo 1120629 2397107 := bstep (se 1 (by rfl) ⟨1797830, by rfl⟩ : syracuseStep 2397107 = 3595661) B3595661
theorem B1709003 : Blo 1120629 1709003 := bstep (se 1 (by rfl) ⟨1281752, by rfl⟩ : syracuseStep 1709003 = 2563505) B2563505
theorem B2528243 : Blo 1120629 2528243 := bstep (se 1 (by rfl) ⟨1896182, by rfl⟩ : syracuseStep 2528243 = 3792365) B3792365
theorem B2528279 : Blo 1120629 2528279 := bstep (se 1 (by rfl) ⟨1896209, by rfl⟩ : syracuseStep 2528279 = 3792419) B3792419
theorem B5674049 : Blo 1120629 5674049 := bstep (se 2 (by rfl) ⟨2127768, by rfl⟩ : syracuseStep 5674049 = 4255537) B4255537
theorem B2528459 : Blo 1120629 2528459 := bstep (se 1 (by rfl) ⟨1896344, by rfl⟩ : syracuseStep 2528459 = 3792689) B3792689
theorem B2528513 : Blo 1120629 2528513 := bstep (se 2 (by rfl) ⟨948192, by rfl⟩ : syracuseStep 2528513 = 1896385) B1896385
theorem B2528729 : Blo 1120629 2528729 := bstep (se 2 (by rfl) ⟨948273, by rfl⟩ : syracuseStep 2528729 = 1896547) B1896547
theorem B2528819 : Blo 1120629 2528819 := bstep (se 1 (by rfl) ⟨1896614, by rfl⟩ : syracuseStep 2528819 = 3793229) B3793229
theorem B1480279 : Blo 1120629 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B2528855 : Blo 1120629 2528855 := bstep (se 1 (by rfl) ⟨1896641, by rfl⟩ : syracuseStep 2528855 = 3793283) B3793283
theorem B4265561 : Blo 1120629 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B2529035 : Blo 1120629 2529035 := bstep (se 1 (by rfl) ⟨1896776, by rfl⟩ : syracuseStep 2529035 = 3793553) B3793553
theorem B2529089 : Blo 1120629 2529089 := bstep (se 2 (by rfl) ⟨948408, by rfl⟩ : syracuseStep 2529089 = 1896817) B1896817
theorem B2529305 : Blo 1120629 2529305 := bstep (se 2 (by rfl) ⟨948489, by rfl⟩ : syracuseStep 2529305 = 1896979) B1896979
theorem B2529395 : Blo 1120629 2529395 := bstep (se 1 (by rfl) ⟨1897046, by rfl⟩ : syracuseStep 2529395 = 3794093) B3794093
theorem B2529431 : Blo 1120629 2529431 := bstep (se 1 (by rfl) ⟨1897073, by rfl⟩ : syracuseStep 2529431 = 3794147) B3794147
theorem B7182553 : Blo 1120629 7182553 := bstep (se 2 (by rfl) ⟨2693457, by rfl⟩ : syracuseStep 7182553 = 5386915) B5386915
theorem B2529611 : Blo 1120629 2529611 := bstep (se 1 (by rfl) ⟨1897208, by rfl⟩ : syracuseStep 2529611 = 3794417) B3794417
theorem B1120631 : Blo 1120629 1120631 := bstep (se 1 (by rfl) ⟨840473, by rfl⟩ : syracuseStep 1120631 = 1680947) B1680947
theorem B2529665 : Blo 1120629 2529665 := bstep (se 2 (by rfl) ⟨948624, by rfl⟩ : syracuseStep 2529665 = 1897249) B1897249
theorem B1120651 : Blo 1120629 1120651 := bstep (se 1 (by rfl) ⟨840488, by rfl⟩ : syracuseStep 1120651 = 1680977) B1680977
theorem B1120663 : Blo 1120629 1120663 := bstep (se 1 (by rfl) ⟨840497, by rfl⟩ : syracuseStep 1120663 = 1680995) B1680995
theorem B1120683 : Blo 1120629 1120683 := bstep (se 1 (by rfl) ⟨840512, by rfl⟩ : syracuseStep 1120683 = 1681025) B1681025
theorem B1120695 : Blo 1120629 1120695 := bstep (se 1 (by rfl) ⟨840521, by rfl⟩ : syracuseStep 1120695 = 1681043) B1681043
theorem B1120715 : Blo 1120629 1120715 := bstep (se 1 (by rfl) ⟨840536, by rfl⟩ : syracuseStep 1120715 = 1681073) B1681073
theorem B1120727 : Blo 1120629 1120727 := bstep (se 1 (by rfl) ⟨840545, by rfl⟩ : syracuseStep 1120727 = 1681091) B1681091
theorem B1350103 : Blo 1120629 1350103 := bstep (se 1 (by rfl) ⟨1012577, by rfl⟩ : syracuseStep 1350103 = 2025155) B2025155
theorem B1120747 : Blo 1120629 1120747 := bstep (se 1 (by rfl) ⟨840560, by rfl⟩ : syracuseStep 1120747 = 1681121) B1681121
theorem B1120759 : Blo 1120629 1120759 := bstep (se 1 (by rfl) ⟨840569, by rfl⟩ : syracuseStep 1120759 = 1681139) B1681139
theorem B1120779 : Blo 1120629 1120779 := bstep (se 1 (by rfl) ⟨840584, by rfl⟩ : syracuseStep 1120779 = 1681169) B1681169
theorem B1120791 : Blo 1120629 1120791 := bstep (se 1 (by rfl) ⟨840593, by rfl⟩ : syracuseStep 1120791 = 1681187) B1681187
theorem B10787363 : Blo 1120629 10787363 := bstep (se 1 (by rfl) ⟨8090522, by rfl⟩ : syracuseStep 10787363 = 16181045) B16181045
theorem B1120811 : Blo 1120629 1120811 := bstep (se 1 (by rfl) ⟨840608, by rfl⟩ : syracuseStep 1120811 = 1681217) B1681217
theorem B1120823 : Blo 1120629 1120823 := bstep (se 1 (by rfl) ⟨840617, by rfl⟩ : syracuseStep 1120823 = 1681235) B1681235
theorem B1120843 : Blo 1120629 1120843 := bstep (se 1 (by rfl) ⟨840632, by rfl⟩ : syracuseStep 1120843 = 1681265) B1681265
theorem B1120855 : Blo 1120629 1120855 := bstep (se 1 (by rfl) ⟨840641, by rfl⟩ : syracuseStep 1120855 = 1681283) B1681283
theorem B2529881 : Blo 1120629 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B1120875 : Blo 1120629 1120875 := bstep (se 1 (by rfl) ⟨840656, by rfl⟩ : syracuseStep 1120875 = 1681313) B1681313
theorem B1120887 : Blo 1120629 1120887 := bstep (se 1 (by rfl) ⟨840665, by rfl⟩ : syracuseStep 1120887 = 1681331) B1681331
theorem B1120907 : Blo 1120629 1120907 := bstep (se 1 (by rfl) ⟨840680, by rfl⟩ : syracuseStep 1120907 = 1681361) B1681361
theorem B1120919 : Blo 1120629 1120919 := bstep (se 1 (by rfl) ⟨840689, by rfl⟩ : syracuseStep 1120919 = 1681379) B1681379
theorem B1120939 : Blo 1120629 1120939 := bstep (se 1 (by rfl) ⟨840704, by rfl⟩ : syracuseStep 1120939 = 1681409) B1681409
theorem B2529971 : Blo 1120629 2529971 := bstep (se 1 (by rfl) ⟨1897478, by rfl⟩ : syracuseStep 2529971 = 3794957) B3794957
theorem B1120951 : Blo 1120629 1120951 := bstep (se 1 (by rfl) ⟨840713, by rfl⟩ : syracuseStep 1120951 = 1681427) B1681427
theorem B1120971 : Blo 1120629 1120971 := bstep (se 1 (by rfl) ⟨840728, by rfl⟩ : syracuseStep 1120971 = 1681457) B1681457
theorem B8100557 : Blo 1120629 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B1120983 : Blo 1120629 1120983 := bstep (se 1 (by rfl) ⟨840737, by rfl⟩ : syracuseStep 1120983 = 1681475) B1681475
theorem B2530007 : Blo 1120629 2530007 := bstep (se 1 (by rfl) ⟨1897505, by rfl⟩ : syracuseStep 2530007 = 3795011) B3795011
theorem B1121003 : Blo 1120629 1121003 := bstep (se 1 (by rfl) ⟨840752, by rfl⟩ : syracuseStep 1121003 = 1681505) B1681505
theorem B1121015 : Blo 1120629 1121015 := bstep (se 1 (by rfl) ⟨840761, by rfl⟩ : syracuseStep 1121015 = 1681523) B1681523
theorem B1121035 : Blo 1120629 1121035 := bstep (se 1 (by rfl) ⟨840776, by rfl⟩ : syracuseStep 1121035 = 1681553) B1681553
theorem B1121047 : Blo 1120629 1121047 := bstep (se 1 (by rfl) ⟨840785, by rfl⟩ : syracuseStep 1121047 = 1681571) B1681571
theorem B1121067 : Blo 1120629 1121067 := bstep (se 1 (by rfl) ⟨840800, by rfl⟩ : syracuseStep 1121067 = 1681601) B1681601
theorem B1121079 : Blo 1120629 1121079 := bstep (se 1 (by rfl) ⟨840809, by rfl⟩ : syracuseStep 1121079 = 1681619) B1681619
theorem B1121099 : Blo 1120629 1121099 := bstep (se 1 (by rfl) ⟨840824, by rfl⟩ : syracuseStep 1121099 = 1681649) B1681649
theorem B1121111 : Blo 1120629 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B1121131 : Blo 1120629 1121131 := bstep (se 1 (by rfl) ⟨840848, by rfl⟩ : syracuseStep 1121131 = 1681697) B1681697
theorem B1121143 : Blo 1120629 1121143 := bstep (se 1 (by rfl) ⟨840857, by rfl⟩ : syracuseStep 1121143 = 1681715) B1681715
theorem B2399105 : Blo 1120629 2399105 := bstep (se 2 (by rfl) ⟨899664, by rfl⟩ : syracuseStep 2399105 = 1799329) B1799329
theorem B1121163 : Blo 1120629 1121163 := bstep (se 1 (by rfl) ⟨840872, by rfl⟩ : syracuseStep 1121163 = 1681745) B1681745
theorem B2530187 : Blo 1120629 2530187 := bstep (se 1 (by rfl) ⟨1897640, by rfl⟩ : syracuseStep 2530187 = 3795281) B3795281
theorem B1121175 : Blo 1120629 1121175 := bstep (se 1 (by rfl) ⟨840881, by rfl⟩ : syracuseStep 1121175 = 1681763) B1681763
theorem B1121195 : Blo 1120629 1121195 := bstep (se 1 (by rfl) ⟨840896, by rfl⟩ : syracuseStep 1121195 = 1681793) B1681793
theorem B8100785 : Blo 1120629 8100785 := bstep (se 2 (by rfl) ⟨3037794, by rfl⟩ : syracuseStep 8100785 = 6075589) B6075589
theorem B1121207 : Blo 1120629 1121207 := bstep (se 1 (by rfl) ⟨840905, by rfl⟩ : syracuseStep 1121207 = 1681811) B1681811
theorem B2530241 : Blo 1120629 2530241 := bstep (se 2 (by rfl) ⟨948840, by rfl⟩ : syracuseStep 2530241 = 1897681) B1897681
theorem B1121227 : Blo 1120629 1121227 := bstep (se 1 (by rfl) ⟨840920, by rfl⟩ : syracuseStep 1121227 = 1681841) B1681841
theorem B1121239 : Blo 1120629 1121239 := bstep (se 1 (by rfl) ⟨840929, by rfl⟩ : syracuseStep 1121239 = 1681859) B1681859
theorem B5675993 : Blo 1120629 5675993 := bstep (se 2 (by rfl) ⟨2128497, by rfl⟩ : syracuseStep 5675993 = 4256995) B4256995
theorem B1121259 : Blo 1120629 1121259 := bstep (se 1 (by rfl) ⟨840944, by rfl⟩ : syracuseStep 1121259 = 1681889) B1681889
theorem B1121271 : Blo 1120629 1121271 := bstep (se 1 (by rfl) ⟨840953, by rfl⟩ : syracuseStep 1121271 = 1681907) B1681907
theorem B1121291 : Blo 1120629 1121291 := bstep (se 1 (by rfl) ⟨840968, by rfl⟩ : syracuseStep 1121291 = 1681937) B1681937
theorem B1121303 : Blo 1120629 1121303 := bstep (se 1 (by rfl) ⟨840977, by rfl⟩ : syracuseStep 1121303 = 1681955) B1681955
theorem B1121323 : Blo 1120629 1121323 := bstep (se 1 (by rfl) ⟨840992, by rfl⟩ : syracuseStep 1121323 = 1681985) B1681985
theorem B1121335 : Blo 1120629 1121335 := bstep (se 1 (by rfl) ⟨841001, by rfl⟩ : syracuseStep 1121335 = 1682003) B1682003
theorem B1121355 : Blo 1120629 1121355 := bstep (se 1 (by rfl) ⟨841016, by rfl⟩ : syracuseStep 1121355 = 1682033) B1682033
theorem B1121367 : Blo 1120629 1121367 := bstep (se 1 (by rfl) ⟨841025, by rfl⟩ : syracuseStep 1121367 = 1682051) B1682051
theorem B16194653 : Blo 1120629 16194653 := bstep (se 3 (by rfl) ⟨3036497, by rfl⟩ : syracuseStep 16194653 = 6072995) B6072995
theorem B1121387 : Blo 1120629 1121387 := bstep (se 1 (by rfl) ⟨841040, by rfl⟩ : syracuseStep 1121387 = 1682081) B1682081
theorem B1121399 : Blo 1120629 1121399 := bstep (se 1 (by rfl) ⟨841049, by rfl⟩ : syracuseStep 1121399 = 1682099) B1682099
theorem B1121419 : Blo 1120629 1121419 := bstep (se 1 (by rfl) ⟨841064, by rfl⟩ : syracuseStep 1121419 = 1682129) B1682129
theorem B1121431 : Blo 1120629 1121431 := bstep (se 1 (by rfl) ⟨841073, by rfl⟩ : syracuseStep 1121431 = 1682147) B1682147
theorem B1121451 : Blo 1120629 1121451 := bstep (se 1 (by rfl) ⟨841088, by rfl⟩ : syracuseStep 1121451 = 1682177) B1682177
theorem B4267187 : Blo 1120629 4267187 := bstep (se 1 (by rfl) ⟨3200390, by rfl⟩ : syracuseStep 4267187 = 6400781) B6400781
theorem B1121463 : Blo 1120629 1121463 := bstep (se 1 (by rfl) ⟨841097, by rfl⟩ : syracuseStep 1121463 = 1682195) B1682195
theorem B4267201 : Blo 1120629 4267201 := bstep (se 2 (by rfl) ⟨1600200, by rfl⟩ : syracuseStep 4267201 = 3200401) B3200401
theorem B1121483 : Blo 1120629 1121483 := bstep (se 1 (by rfl) ⟨841112, by rfl⟩ : syracuseStep 1121483 = 1682225) B1682225
theorem B1121495 : Blo 1120629 1121495 := bstep (se 1 (by rfl) ⟨841121, by rfl⟩ : syracuseStep 1121495 = 1682243) B1682243
theorem B1121515 : Blo 1120629 1121515 := bstep (se 1 (by rfl) ⟨841136, by rfl⟩ : syracuseStep 1121515 = 1682273) B1682273
theorem B1121527 : Blo 1120629 1121527 := bstep (se 1 (by rfl) ⟨841145, by rfl⟩ : syracuseStep 1121527 = 1682291) B1682291
theorem B1121547 : Blo 1120629 1121547 := bstep (se 1 (by rfl) ⟨841160, by rfl⟩ : syracuseStep 1121547 = 1682321) B1682321
theorem B1121559 : Blo 1120629 1121559 := bstep (se 1 (by rfl) ⟨841169, by rfl⟩ : syracuseStep 1121559 = 1682339) B1682339
theorem B1121579 : Blo 1120629 1121579 := bstep (se 1 (by rfl) ⟨841184, by rfl⟩ : syracuseStep 1121579 = 1682369) B1682369
theorem B2563379 : Blo 1120629 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B1121591 : Blo 1120629 1121591 := bstep (se 1 (by rfl) ⟨841193, by rfl⟩ : syracuseStep 1121591 = 1682387) B1682387
theorem B1121611 : Blo 1120629 1121611 := bstep (se 1 (by rfl) ⟨841208, by rfl⟩ : syracuseStep 1121611 = 1682417) B1682417
theorem B1121623 : Blo 1120629 1121623 := bstep (se 1 (by rfl) ⟨841217, by rfl⟩ : syracuseStep 1121623 = 1682435) B1682435
theorem B1121643 : Blo 1120629 1121643 := bstep (se 1 (by rfl) ⟨841232, by rfl⟩ : syracuseStep 1121643 = 1682465) B1682465
theorem B1121655 : Blo 1120629 1121655 := bstep (se 1 (by rfl) ⟨841241, by rfl⟩ : syracuseStep 1121655 = 1682483) B1682483
theorem B1121675 : Blo 1120629 1121675 := bstep (se 1 (by rfl) ⟨841256, by rfl⟩ : syracuseStep 1121675 = 1682513) B1682513
theorem B1121687 : Blo 1120629 1121687 := bstep (se 1 (by rfl) ⟨841265, by rfl⟩ : syracuseStep 1121687 = 1682531) B1682531
theorem B1121707 : Blo 1120629 1121707 := bstep (se 1 (by rfl) ⟨841280, by rfl⟩ : syracuseStep 1121707 = 1682561) B1682561
theorem B1121719 : Blo 1120629 1121719 := bstep (se 1 (by rfl) ⟨841289, by rfl⟩ : syracuseStep 1121719 = 1682579) B1682579
theorem B1121739 : Blo 1120629 1121739 := bstep (se 1 (by rfl) ⟨841304, by rfl⟩ : syracuseStep 1121739 = 1682609) B1682609
theorem B1121751 : Blo 1120629 1121751 := bstep (se 1 (by rfl) ⟨841313, by rfl⟩ : syracuseStep 1121751 = 1682627) B1682627
theorem B1121771 : Blo 1120629 1121771 := bstep (se 1 (by rfl) ⟨841328, by rfl⟩ : syracuseStep 1121771 = 1682657) B1682657
theorem B1121783 : Blo 1120629 1121783 := bstep (se 1 (by rfl) ⟨841337, by rfl⟩ : syracuseStep 1121783 = 1682675) B1682675
theorem B1121803 : Blo 1120629 1121803 := bstep (se 1 (by rfl) ⟨841352, by rfl⟩ : syracuseStep 1121803 = 1682705) B1682705
theorem B1121815 : Blo 1120629 1121815 := bstep (se 1 (by rfl) ⟨841361, by rfl⟩ : syracuseStep 1121815 = 1682723) B1682723
theorem B1121835 : Blo 1120629 1121835 := bstep (se 1 (by rfl) ⟨841376, by rfl⟩ : syracuseStep 1121835 = 1682753) B1682753
theorem B1121847 : Blo 1120629 1121847 := bstep (se 1 (by rfl) ⟨841385, by rfl⟩ : syracuseStep 1121847 = 1682771) B1682771
theorem B1121867 : Blo 1120629 1121867 := bstep (se 1 (by rfl) ⟨841400, by rfl⟩ : syracuseStep 1121867 = 1682801) B1682801
theorem B1121879 : Blo 1120629 1121879 := bstep (se 1 (by rfl) ⟨841409, by rfl⟩ : syracuseStep 1121879 = 1682819) B1682819
theorem B1121899 : Blo 1120629 1121899 := bstep (se 1 (by rfl) ⟨841424, by rfl⟩ : syracuseStep 1121899 = 1682849) B1682849
theorem B1121911 : Blo 1120629 1121911 := bstep (se 1 (by rfl) ⟨841433, by rfl⟩ : syracuseStep 1121911 = 1682867) B1682867
theorem B1121931 : Blo 1120629 1121931 := bstep (se 1 (by rfl) ⟨841448, by rfl⟩ : syracuseStep 1121931 = 1682897) B1682897
theorem B1121943 : Blo 1120629 1121943 := bstep (se 1 (by rfl) ⟨841457, by rfl⟩ : syracuseStep 1121943 = 1682915) B1682915
theorem B1121963 : Blo 1120629 1121963 := bstep (se 1 (by rfl) ⟨841472, by rfl⟩ : syracuseStep 1121963 = 1682945) B1682945
theorem B1121975 : Blo 1120629 1121975 := bstep (se 1 (by rfl) ⟨841481, by rfl⟩ : syracuseStep 1121975 = 1682963) B1682963
theorem B1121995 : Blo 1120629 1121995 := bstep (se 1 (by rfl) ⟨841496, by rfl⟩ : syracuseStep 1121995 = 1682993) B1682993
theorem B1122007 : Blo 1120629 1122007 := bstep (se 1 (by rfl) ⟨841505, by rfl⟩ : syracuseStep 1122007 = 1683011) B1683011
theorem B2399959 : Blo 1120629 2399959 := bstep (se 1 (by rfl) ⟨1799969, by rfl⟩ : syracuseStep 2399959 = 3599939) B3599939
theorem B1122027 : Blo 1120629 1122027 := bstep (se 1 (by rfl) ⟨841520, by rfl⟩ : syracuseStep 1122027 = 1683041) B1683041
theorem B1122039 : Blo 1120629 1122039 := bstep (se 1 (by rfl) ⟨841529, by rfl⟩ : syracuseStep 1122039 = 1683059) B1683059
theorem B1122059 : Blo 1120629 1122059 := bstep (se 1 (by rfl) ⟨841544, by rfl⟩ : syracuseStep 1122059 = 1683089) B1683089
theorem B1122071 : Blo 1120629 1122071 := bstep (se 1 (by rfl) ⟨841553, by rfl⟩ : syracuseStep 1122071 = 1683107) B1683107
theorem B1122091 : Blo 1120629 1122091 := bstep (se 1 (by rfl) ⟨841568, by rfl⟩ : syracuseStep 1122091 = 1683137) B1683137
theorem B1122103 : Blo 1120629 1122103 := bstep (se 1 (by rfl) ⟨841577, by rfl⟩ : syracuseStep 1122103 = 1683155) B1683155
theorem B1122123 : Blo 1120629 1122123 := bstep (se 1 (by rfl) ⟨841592, by rfl⟩ : syracuseStep 1122123 = 1683185) B1683185
theorem B1122135 : Blo 1120629 1122135 := bstep (se 1 (by rfl) ⟨841601, by rfl⟩ : syracuseStep 1122135 = 1683203) B1683203
theorem B1122155 : Blo 1120629 1122155 := bstep (se 1 (by rfl) ⟨841616, by rfl⟩ : syracuseStep 1122155 = 1683233) B1683233
theorem B1122167 : Blo 1120629 1122167 := bstep (se 1 (by rfl) ⟨841625, by rfl⟩ : syracuseStep 1122167 = 1683251) B1683251
theorem B1122187 : Blo 1120629 1122187 := bstep (se 1 (by rfl) ⟨841640, by rfl⟩ : syracuseStep 1122187 = 1683281) B1683281
theorem B1122199 : Blo 1120629 1122199 := bstep (se 1 (by rfl) ⟨841649, by rfl⟩ : syracuseStep 1122199 = 1683299) B1683299
theorem B1122219 : Blo 1120629 1122219 := bstep (se 1 (by rfl) ⟨841664, by rfl⟩ : syracuseStep 1122219 = 1683329) B1683329
theorem B1122231 : Blo 1120629 1122231 := bstep (se 1 (by rfl) ⟨841673, by rfl⟩ : syracuseStep 1122231 = 1683347) B1683347
theorem B1122251 : Blo 1120629 1122251 := bstep (se 1 (by rfl) ⟨841688, by rfl⟩ : syracuseStep 1122251 = 1683377) B1683377
theorem B1122263 : Blo 1120629 1122263 := bstep (se 1 (by rfl) ⟨841697, by rfl⟩ : syracuseStep 1122263 = 1683395) B1683395
theorem B1122283 : Blo 1120629 1122283 := bstep (se 1 (by rfl) ⟨841712, by rfl⟩ : syracuseStep 1122283 = 1683425) B1683425
theorem B1122295 : Blo 1120629 1122295 := bstep (se 1 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 1122295 = 1683443) B1683443
theorem B5120003 : Blo 1120629 5120003 := bstep (se 1 (by rfl) ⟨3840002, by rfl⟩ : syracuseStep 5120003 = 7680005) B7680005
theorem B1122315 : Blo 1120629 1122315 := bstep (se 1 (by rfl) ⟨841736, by rfl⟩ : syracuseStep 1122315 = 1683473) B1683473
theorem B1122327 : Blo 1120629 1122327 := bstep (se 1 (by rfl) ⟨841745, by rfl⟩ : syracuseStep 1122327 = 1683491) B1683491
theorem B1122347 : Blo 1120629 1122347 := bstep (se 1 (by rfl) ⟨841760, by rfl⟩ : syracuseStep 1122347 = 1683521) B1683521
theorem B1122359 : Blo 1120629 1122359 := bstep (se 1 (by rfl) ⟨841769, by rfl⟩ : syracuseStep 1122359 = 1683539) B1683539
theorem B4792385 : Blo 1120629 4792385 := bstep (se 2 (by rfl) ⟨1797144, by rfl⟩ : syracuseStep 4792385 = 3594289) B3594289
theorem B1122379 : Blo 1120629 1122379 := bstep (se 1 (by rfl) ⟨841784, by rfl⟩ : syracuseStep 1122379 = 1683569) B1683569
theorem B1122391 : Blo 1120629 1122391 := bstep (se 1 (by rfl) ⟨841793, by rfl⟩ : syracuseStep 1122391 = 1683587) B1683587
theorem B7184477 : Blo 1120629 7184477 := bstep (se 3 (by rfl) ⟨1347089, by rfl⟩ : syracuseStep 7184477 = 2694179) B2694179
theorem B1122411 : Blo 1120629 1122411 := bstep (se 1 (by rfl) ⟨841808, by rfl⟩ : syracuseStep 1122411 = 1683617) B1683617
theorem B1122423 : Blo 1120629 1122423 := bstep (se 1 (by rfl) ⟨841817, by rfl⟩ : syracuseStep 1122423 = 1683635) B1683635
theorem B1122443 : Blo 1120629 1122443 := bstep (se 1 (by rfl) ⟨841832, by rfl⟩ : syracuseStep 1122443 = 1683665) B1683665
theorem B1122455 : Blo 1120629 1122455 := bstep (se 1 (by rfl) ⟨841841, by rfl⟩ : syracuseStep 1122455 = 1683683) B1683683
theorem B1122475 : Blo 1120629 1122475 := bstep (se 1 (by rfl) ⟨841856, by rfl⟩ : syracuseStep 1122475 = 1683713) B1683713
theorem B1122487 : Blo 1120629 1122487 := bstep (se 1 (by rfl) ⟨841865, by rfl⟩ : syracuseStep 1122487 = 1683731) B1683731
theorem B1122507 : Blo 1120629 1122507 := bstep (se 1 (by rfl) ⟨841880, by rfl⟩ : syracuseStep 1122507 = 1683761) B1683761
theorem B1122519 : Blo 1120629 1122519 := bstep (se 1 (by rfl) ⟨841889, by rfl⟩ : syracuseStep 1122519 = 1683779) B1683779
theorem B4792537 : Blo 1120629 4792537 := bstep (se 2 (by rfl) ⟨1797201, by rfl⟩ : syracuseStep 4792537 = 3594403) B3594403
theorem B1122539 : Blo 1120629 1122539 := bstep (se 1 (by rfl) ⟨841904, by rfl⟩ : syracuseStep 1122539 = 1683809) B1683809
theorem B1122551 : Blo 1120629 1122551 := bstep (se 1 (by rfl) ⟨841913, by rfl⟩ : syracuseStep 1122551 = 1683827) B1683827
theorem B1122571 : Blo 1120629 1122571 := bstep (se 1 (by rfl) ⟨841928, by rfl⟩ : syracuseStep 1122571 = 1683857) B1683857
theorem B1122583 : Blo 1120629 1122583 := bstep (se 1 (by rfl) ⟨841937, by rfl⟩ : syracuseStep 1122583 = 1683875) B1683875
theorem B1122603 : Blo 1120629 1122603 := bstep (se 1 (by rfl) ⟨841952, by rfl⟩ : syracuseStep 1122603 = 1683905) B1683905
theorem B1122615 : Blo 1120629 1122615 := bstep (se 1 (by rfl) ⟨841961, by rfl⟩ : syracuseStep 1122615 = 1683923) B1683923
theorem B1122635 : Blo 1120629 1122635 := bstep (se 1 (by rfl) ⟨841976, by rfl⟩ : syracuseStep 1122635 = 1683953) B1683953
theorem B1122647 : Blo 1120629 1122647 := bstep (se 1 (by rfl) ⟨841985, by rfl⟩ : syracuseStep 1122647 = 1683971) B1683971
theorem B1122667 : Blo 1120629 1122667 := bstep (se 1 (by rfl) ⟨842000, by rfl⟩ : syracuseStep 1122667 = 1684001) B1684001
theorem B1122679 : Blo 1120629 1122679 := bstep (se 1 (by rfl) ⟨842009, by rfl⟩ : syracuseStep 1122679 = 1684019) B1684019
theorem B1122699 : Blo 1120629 1122699 := bstep (se 1 (by rfl) ⟨842024, by rfl⟩ : syracuseStep 1122699 = 1684049) B1684049
theorem B1122711 : Blo 1120629 1122711 := bstep (se 1 (by rfl) ⟨842033, by rfl⟩ : syracuseStep 1122711 = 1684067) B1684067
theorem B1122731 : Blo 1120629 1122731 := bstep (se 1 (by rfl) ⟨842048, by rfl⟩ : syracuseStep 1122731 = 1684097) B1684097
theorem B1122743 : Blo 1120629 1122743 := bstep (se 1 (by rfl) ⟨842057, by rfl⟩ : syracuseStep 1122743 = 1684115) B1684115
theorem B1122763 : Blo 1120629 1122763 := bstep (se 1 (by rfl) ⟨842072, by rfl⟩ : syracuseStep 1122763 = 1684145) B1684145
theorem B1122775 : Blo 1120629 1122775 := bstep (se 1 (by rfl) ⟨842081, by rfl⟩ : syracuseStep 1122775 = 1684163) B1684163
theorem B6070745 : Blo 1120629 6070745 := bstep (se 2 (by rfl) ⟨2276529, by rfl⟩ : syracuseStep 6070745 = 4553059) B4553059
theorem B1122795 : Blo 1120629 1122795 := bstep (se 1 (by rfl) ⟨842096, by rfl⟩ : syracuseStep 1122795 = 1684193) B1684193
theorem B1122807 : Blo 1120629 1122807 := bstep (se 1 (by rfl) ⟨842105, by rfl⟩ : syracuseStep 1122807 = 1684211) B1684211
theorem B1122827 : Blo 1120629 1122827 := bstep (se 1 (by rfl) ⟨842120, by rfl⟩ : syracuseStep 1122827 = 1684241) B1684241
theorem B1122839 : Blo 1120629 1122839 := bstep (se 1 (by rfl) ⟨842129, by rfl⟩ : syracuseStep 1122839 = 1684259) B1684259
theorem B1122859 : Blo 1120629 1122859 := bstep (se 1 (by rfl) ⟨842144, by rfl⟩ : syracuseStep 1122859 = 1684289) B1684289
theorem B5677613 : Blo 1120629 5677613 := bstep (se 3 (by rfl) ⟨1064552, by rfl⟩ : syracuseStep 5677613 = 2129105) B2129105
theorem B1122871 : Blo 1120629 1122871 := bstep (se 1 (by rfl) ⟨842153, by rfl⟩ : syracuseStep 1122871 = 1684307) B1684307
theorem B1122891 : Blo 1120629 1122891 := bstep (se 1 (by rfl) ⟨842168, by rfl⟩ : syracuseStep 1122891 = 1684337) B1684337
theorem B1122903 : Blo 1120629 1122903 := bstep (se 1 (by rfl) ⟨842177, by rfl⟩ : syracuseStep 1122903 = 1684355) B1684355
theorem B1122923 : Blo 1120629 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B1122935 : Blo 1120629 1122935 := bstep (se 1 (by rfl) ⟨842201, by rfl⟩ : syracuseStep 1122935 = 1684403) B1684403
theorem B1122955 : Blo 1120629 1122955 := bstep (se 1 (by rfl) ⟨842216, by rfl⟩ : syracuseStep 1122955 = 1684433) B1684433
theorem B1122967 : Blo 1120629 1122967 := bstep (se 1 (by rfl) ⟨842225, by rfl⟩ : syracuseStep 1122967 = 1684451) B1684451
theorem B6398615 : Blo 1120629 6398615 := bstep (se 1 (by rfl) ⟨4798961, by rfl⟩ : syracuseStep 6398615 = 9597923) B9597923
theorem B1122987 : Blo 1120629 1122987 := bstep (se 1 (by rfl) ⟨842240, by rfl⟩ : syracuseStep 1122987 = 1684481) B1684481
theorem B1122999 : Blo 1120629 1122999 := bstep (se 1 (by rfl) ⟨842249, by rfl⟩ : syracuseStep 1122999 = 1684499) B1684499
theorem B3646145 : Blo 1120629 3646145 := bstep (se 2 (by rfl) ⟨1367304, by rfl⟩ : syracuseStep 3646145 = 2734609) B2734609
theorem B1123019 : Blo 1120629 1123019 := bstep (se 1 (by rfl) ⟨842264, by rfl⟩ : syracuseStep 1123019 = 1684529) B1684529
theorem B1123031 : Blo 1120629 1123031 := bstep (se 1 (by rfl) ⟨842273, by rfl⟩ : syracuseStep 1123031 = 1684547) B1684547
theorem B1123051 : Blo 1120629 1123051 := bstep (se 1 (by rfl) ⟨842288, by rfl⟩ : syracuseStep 1123051 = 1684577) B1684577
theorem B1123063 : Blo 1120629 1123063 := bstep (se 1 (by rfl) ⟨842297, by rfl⟩ : syracuseStep 1123063 = 1684595) B1684595
theorem B1123083 : Blo 1120629 1123083 := bstep (se 1 (by rfl) ⟨842312, by rfl⟩ : syracuseStep 1123083 = 1684625) B1684625
theorem B1123095 : Blo 1120629 1123095 := bstep (se 1 (by rfl) ⟨842321, by rfl⟩ : syracuseStep 1123095 = 1684643) B1684643
theorem B1123115 : Blo 1120629 1123115 := bstep (se 1 (by rfl) ⟨842336, by rfl⟩ : syracuseStep 1123115 = 1684673) B1684673
theorem B1123127 : Blo 1120629 1123127 := bstep (se 1 (by rfl) ⟨842345, by rfl⟩ : syracuseStep 1123127 = 1684691) B1684691
theorem B1123147 : Blo 1120629 1123147 := bstep (se 1 (by rfl) ⟨842360, by rfl⟩ : syracuseStep 1123147 = 1684721) B1684721
theorem B1123159 : Blo 1120629 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B1123179 : Blo 1120629 1123179 := bstep (se 1 (by rfl) ⟨842384, by rfl⟩ : syracuseStep 1123179 = 1684769) B1684769
theorem B2401139 : Blo 1120629 2401139 := bstep (se 1 (by rfl) ⟨1800854, by rfl⟩ : syracuseStep 2401139 = 3601709) B3601709
theorem B1123191 : Blo 1120629 1123191 := bstep (se 1 (by rfl) ⟨842393, by rfl⟩ : syracuseStep 1123191 = 1684787) B1684787
theorem B1123211 : Blo 1120629 1123211 := bstep (se 1 (by rfl) ⟨842408, by rfl⟩ : syracuseStep 1123211 = 1684817) B1684817
theorem B1123223 : Blo 1120629 1123223 := bstep (se 1 (by rfl) ⟨842417, by rfl⟩ : syracuseStep 1123223 = 1684835) B1684835
theorem B1123243 : Blo 1120629 1123243 := bstep (se 1 (by rfl) ⟨842432, by rfl⟩ : syracuseStep 1123243 = 1684865) B1684865
theorem B1123255 : Blo 1120629 1123255 := bstep (se 1 (by rfl) ⟨842441, by rfl⟩ : syracuseStep 1123255 = 1684883) B1684883
theorem B1123275 : Blo 1120629 1123275 := bstep (se 1 (by rfl) ⟨842456, by rfl⟩ : syracuseStep 1123275 = 1684913) B1684913
theorem B1123287 : Blo 1120629 1123287 := bstep (se 1 (by rfl) ⟨842465, by rfl⟩ : syracuseStep 1123287 = 1684931) B1684931
theorem B1123307 : Blo 1120629 1123307 := bstep (se 1 (by rfl) ⟨842480, by rfl⟩ : syracuseStep 1123307 = 1684961) B1684961
theorem B1123319 : Blo 1120629 1123319 := bstep (se 1 (by rfl) ⟨842489, by rfl⟩ : syracuseStep 1123319 = 1684979) B1684979
theorem B1123339 : Blo 1120629 1123339 := bstep (se 1 (by rfl) ⟨842504, by rfl⟩ : syracuseStep 1123339 = 1685009) B1685009
theorem B1123351 : Blo 1120629 1123351 := bstep (se 1 (by rfl) ⟨842513, by rfl⟩ : syracuseStep 1123351 = 1685027) B1685027
theorem B1123371 : Blo 1120629 1123371 := bstep (se 1 (by rfl) ⟨842528, by rfl⟩ : syracuseStep 1123371 = 1685057) B1685057
theorem B1123383 : Blo 1120629 1123383 := bstep (se 1 (by rfl) ⟨842537, by rfl⟩ : syracuseStep 1123383 = 1685075) B1685075
theorem B1123403 : Blo 1120629 1123403 := bstep (se 1 (by rfl) ⟨842552, by rfl⟩ : syracuseStep 1123403 = 1685105) B1685105
theorem B4269131 : Blo 1120629 4269131 := bstep (se 1 (by rfl) ⟨3201848, by rfl⟩ : syracuseStep 4269131 = 6403697) B6403697
theorem B1123415 : Blo 1120629 1123415 := bstep (se 1 (by rfl) ⟨842561, by rfl⟩ : syracuseStep 1123415 = 1685123) B1685123
theorem B4269145 : Blo 1120629 4269145 := bstep (se 2 (by rfl) ⟨1600929, by rfl⟩ : syracuseStep 4269145 = 3201859) B3201859
theorem B1123435 : Blo 1120629 1123435 := bstep (se 1 (by rfl) ⟨842576, by rfl⟩ : syracuseStep 1123435 = 1685153) B1685153
theorem B1123447 : Blo 1120629 1123447 := bstep (se 1 (by rfl) ⟨842585, by rfl⟩ : syracuseStep 1123447 = 1685171) B1685171
theorem B1123467 : Blo 1120629 1123467 := bstep (se 1 (by rfl) ⟨842600, by rfl⟩ : syracuseStep 1123467 = 1685201) B1685201
theorem B1123479 : Blo 1120629 1123479 := bstep (se 1 (by rfl) ⟨842609, by rfl⟩ : syracuseStep 1123479 = 1685219) B1685219
theorem B1123499 : Blo 1120629 1123499 := bstep (se 1 (by rfl) ⟨842624, by rfl⟩ : syracuseStep 1123499 = 1685249) B1685249
theorem B1123511 : Blo 1120629 1123511 := bstep (se 1 (by rfl) ⟨842633, by rfl⟩ : syracuseStep 1123511 = 1685267) B1685267
theorem B1123531 : Blo 1120629 1123531 := bstep (se 1 (by rfl) ⟨842648, by rfl⟩ : syracuseStep 1123531 = 1685297) B1685297
theorem B1123543 : Blo 1120629 1123543 := bstep (se 1 (by rfl) ⟨842657, by rfl⟩ : syracuseStep 1123543 = 1685315) B1685315
theorem B1123563 : Blo 1120629 1123563 := bstep (se 1 (by rfl) ⟨842672, by rfl⟩ : syracuseStep 1123563 = 1685345) B1685345
theorem B1123575 : Blo 1120629 1123575 := bstep (se 1 (by rfl) ⟨842681, by rfl⟩ : syracuseStep 1123575 = 1685363) B1685363
theorem B1123595 : Blo 1120629 1123595 := bstep (se 1 (by rfl) ⟨842696, by rfl⟩ : syracuseStep 1123595 = 1685393) B1685393
theorem B1123607 : Blo 1120629 1123607 := bstep (se 1 (by rfl) ⟨842705, by rfl⟩ : syracuseStep 1123607 = 1685411) B1685411
theorem B9577763 : Blo 1120629 9577763 := bstep (se 1 (by rfl) ⟨7183322, by rfl⟩ : syracuseStep 9577763 = 14366645) B14366645
theorem B1123627 : Blo 1120629 1123627 := bstep (se 1 (by rfl) ⟨842720, by rfl⟩ : syracuseStep 1123627 = 1685441) B1685441
theorem B1123639 : Blo 1120629 1123639 := bstep (se 1 (by rfl) ⟨842729, by rfl⟩ : syracuseStep 1123639 = 1685459) B1685459
theorem B1123659 : Blo 1120629 1123659 := bstep (se 1 (by rfl) ⟨842744, by rfl⟩ : syracuseStep 1123659 = 1685489) B1685489
theorem B1123671 : Blo 1120629 1123671 := bstep (se 1 (by rfl) ⟨842753, by rfl⟩ : syracuseStep 1123671 = 1685507) B1685507
theorem B1123691 : Blo 1120629 1123691 := bstep (se 1 (by rfl) ⟨842768, by rfl⟩ : syracuseStep 1123691 = 1685537) B1685537
theorem B1123703 : Blo 1120629 1123703 := bstep (se 1 (by rfl) ⟨842777, by rfl⟩ : syracuseStep 1123703 = 1685555) B1685555
theorem B1123723 : Blo 1120629 1123723 := bstep (se 1 (by rfl) ⟨842792, by rfl⟩ : syracuseStep 1123723 = 1685585) B1685585
theorem B1123735 : Blo 1120629 1123735 := bstep (se 1 (by rfl) ⟨842801, by rfl⟩ : syracuseStep 1123735 = 1685603) B1685603
theorem B1123755 : Blo 1120629 1123755 := bstep (se 1 (by rfl) ⟨842816, by rfl⟩ : syracuseStep 1123755 = 1685633) B1685633
theorem B4859309 : Blo 1120629 4859309 := bstep (se 3 (by rfl) ⟨911120, by rfl⟩ : syracuseStep 4859309 = 1822241) B1822241
theorem B1123767 : Blo 1120629 1123767 := bstep (se 1 (by rfl) ⟨842825, by rfl⟩ : syracuseStep 1123767 = 1685651) B1685651
theorem B1123787 : Blo 1120629 1123787 := bstep (se 1 (by rfl) ⟨842840, by rfl⟩ : syracuseStep 1123787 = 1685681) B1685681
theorem B1123799 : Blo 1120629 1123799 := bstep (se 1 (by rfl) ⟨842849, by rfl⟩ : syracuseStep 1123799 = 1685699) B1685699
theorem B1123819 : Blo 1120629 1123819 := bstep (se 1 (by rfl) ⟨842864, by rfl⟩ : syracuseStep 1123819 = 1685729) B1685729
theorem B1123831 : Blo 1120629 1123831 := bstep (se 1 (by rfl) ⟨842873, by rfl⟩ : syracuseStep 1123831 = 1685747) B1685747
theorem B1123851 : Blo 1120629 1123851 := bstep (se 1 (by rfl) ⟨842888, by rfl⟩ : syracuseStep 1123851 = 1685777) B1685777
theorem B1123863 : Blo 1120629 1123863 := bstep (se 1 (by rfl) ⟨842897, by rfl⟩ : syracuseStep 1123863 = 1685795) B1685795
theorem B1123883 : Blo 1120629 1123883 := bstep (se 1 (by rfl) ⟨842912, by rfl⟩ : syracuseStep 1123883 = 1685825) B1685825
theorem B1123895 : Blo 1120629 1123895 := bstep (se 1 (by rfl) ⟨842921, by rfl⟩ : syracuseStep 1123895 = 1685843) B1685843
theorem B1680971 : Blo 1120629 1680971 := bstep (se 1 (by rfl) ⟨1260728, by rfl⟩ : syracuseStep 1680971 = 2521457) B2521457
theorem B1123915 : Blo 1120629 1123915 := bstep (se 1 (by rfl) ⟨842936, by rfl⟩ : syracuseStep 1123915 = 1685873) B1685873
theorem B1680983 : Blo 1120629 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B1123927 : Blo 1120629 1123927 := bstep (se 1 (by rfl) ⟨842945, by rfl⟩ : syracuseStep 1123927 = 1685891) B1685891
theorem B1123947 : Blo 1120629 1123947 := bstep (se 1 (by rfl) ⟨842960, by rfl⟩ : syracuseStep 1123947 = 1685921) B1685921
theorem B1123959 : Blo 1120629 1123959 := bstep (se 1 (by rfl) ⟨842969, by rfl⟩ : syracuseStep 1123959 = 1685939) B1685939
theorem B1123979 : Blo 1120629 1123979 := bstep (se 1 (by rfl) ⟨842984, by rfl⟩ : syracuseStep 1123979 = 1685969) B1685969
theorem B1123991 : Blo 1120629 1123991 := bstep (se 1 (by rfl) ⟨842993, by rfl⟩ : syracuseStep 1123991 = 1685987) B1685987
theorem B1681049 : Blo 1120629 1681049 := bstep (se 2 (by rfl) ⟨630393, by rfl⟩ : syracuseStep 1681049 = 1260787) B1260787
theorem B1124011 : Blo 1120629 1124011 := bstep (se 1 (by rfl) ⟨843008, by rfl⟩ : syracuseStep 1124011 = 1686017) B1686017
theorem B1124023 : Blo 1120629 1124023 := bstep (se 1 (by rfl) ⟨843017, by rfl⟩ : syracuseStep 1124023 = 1686035) B1686035
theorem B1124043 : Blo 1120629 1124043 := bstep (se 1 (by rfl) ⟨843032, by rfl⟩ : syracuseStep 1124043 = 1686065) B1686065
theorem B1124055 : Blo 1120629 1124055 := bstep (se 1 (by rfl) ⟨843041, by rfl⟩ : syracuseStep 1124055 = 1686083) B1686083
theorem B1124075 : Blo 1120629 1124075 := bstep (se 1 (by rfl) ⟨843056, by rfl⟩ : syracuseStep 1124075 = 1686113) B1686113
theorem B1124087 : Blo 1120629 1124087 := bstep (se 1 (by rfl) ⟨843065, by rfl⟩ : syracuseStep 1124087 = 1686131) B1686131
theorem B1681163 : Blo 1120629 1681163 := bstep (se 1 (by rfl) ⟨1260872, by rfl⟩ : syracuseStep 1681163 = 2521745) B2521745
theorem B1124107 : Blo 1120629 1124107 := bstep (se 1 (by rfl) ⟨843080, by rfl⟩ : syracuseStep 1124107 = 1686161) B1686161
theorem B1681175 : Blo 1120629 1681175 := bstep (se 1 (by rfl) ⟨1260881, by rfl⟩ : syracuseStep 1681175 = 2521763) B2521763
theorem B1124119 : Blo 1120629 1124119 := bstep (se 1 (by rfl) ⟨843089, by rfl⟩ : syracuseStep 1124119 = 1686179) B1686179
theorem B1124139 : Blo 1120629 1124139 := bstep (se 1 (by rfl) ⟨843104, by rfl⟩ : syracuseStep 1124139 = 1686209) B1686209
theorem B1124151 : Blo 1120629 1124151 := bstep (se 1 (by rfl) ⟨843113, by rfl⟩ : syracuseStep 1124151 = 1686227) B1686227
theorem B1124171 : Blo 1120629 1124171 := bstep (se 1 (by rfl) ⟨843128, by rfl⟩ : syracuseStep 1124171 = 1686257) B1686257
theorem B1124183 : Blo 1120629 1124183 := bstep (se 1 (by rfl) ⟨843137, by rfl⟩ : syracuseStep 1124183 = 1686275) B1686275
theorem B1681241 : Blo 1120629 1681241 := bstep (se 2 (by rfl) ⟨630465, by rfl⟩ : syracuseStep 1681241 = 1260931) B1260931
theorem B1124203 : Blo 1120629 1124203 := bstep (se 1 (by rfl) ⟨843152, by rfl⟩ : syracuseStep 1124203 = 1686305) B1686305
theorem B1124215 : Blo 1120629 1124215 := bstep (se 1 (by rfl) ⟨843161, by rfl⟩ : syracuseStep 1124215 = 1686323) B1686323
theorem B1124235 : Blo 1120629 1124235 := bstep (se 1 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 1124235 = 1686353) B1686353
theorem B1124247 : Blo 1120629 1124247 := bstep (se 1 (by rfl) ⟨843185, by rfl⟩ : syracuseStep 1124247 = 1686371) B1686371
theorem B1124267 : Blo 1120629 1124267 := bstep (se 1 (by rfl) ⟨843200, by rfl⟩ : syracuseStep 1124267 = 1686401) B1686401
theorem B1124279 : Blo 1120629 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B1681355 : Blo 1120629 1681355 := bstep (se 1 (by rfl) ⟨1261016, by rfl⟩ : syracuseStep 1681355 = 2522033) B2522033
theorem B1419211 : Blo 1120629 1419211 := bstep (se 1 (by rfl) ⟨1064408, by rfl⟩ : syracuseStep 1419211 = 2128817) B2128817
theorem B1124299 : Blo 1120629 1124299 := bstep (se 1 (by rfl) ⟨843224, by rfl⟩ : syracuseStep 1124299 = 1686449) B1686449
theorem B1681367 : Blo 1120629 1681367 := bstep (se 1 (by rfl) ⟨1261025, by rfl⟩ : syracuseStep 1681367 = 2522051) B2522051
theorem B1124311 : Blo 1120629 1124311 := bstep (se 1 (by rfl) ⟨843233, by rfl⟩ : syracuseStep 1124311 = 1686467) B1686467
theorem B13674457 : Blo 1120629 13674457 := bstep (se 2 (by rfl) ⟨5127921, by rfl⟩ : syracuseStep 13674457 = 10255843) B10255843
theorem B1124331 : Blo 1120629 1124331 := bstep (se 1 (by rfl) ⟨843248, by rfl⟩ : syracuseStep 1124331 = 1686497) B1686497
theorem B1124343 : Blo 1120629 1124343 := bstep (se 1 (by rfl) ⟨843257, by rfl⟩ : syracuseStep 1124343 = 1686515) B1686515
theorem B1124363 : Blo 1120629 1124363 := bstep (se 1 (by rfl) ⟨843272, by rfl⟩ : syracuseStep 1124363 = 1686545) B1686545
theorem B9578513 : Blo 1120629 9578513 := bstep (se 2 (by rfl) ⟨3591942, by rfl⟩ : syracuseStep 9578513 = 7183885) B7183885
theorem B1124375 : Blo 1120629 1124375 := bstep (se 1 (by rfl) ⟨843281, by rfl⟩ : syracuseStep 1124375 = 1686563) B1686563
theorem B1681433 : Blo 1120629 1681433 := bstep (se 2 (by rfl) ⟨630537, by rfl⟩ : syracuseStep 1681433 = 1261075) B1261075
theorem B1779737 : Blo 1120629 1779737 := bstep (se 2 (by rfl) ⟨667401, by rfl⟩ : syracuseStep 1779737 = 1334803) B1334803
theorem B1124395 : Blo 1120629 1124395 := bstep (se 1 (by rfl) ⟨843296, by rfl⟩ : syracuseStep 1124395 = 1686593) B1686593
theorem B1124407 : Blo 1120629 1124407 := bstep (se 1 (by rfl) ⟨843305, by rfl⟩ : syracuseStep 1124407 = 1686611) B1686611
theorem B1124427 : Blo 1120629 1124427 := bstep (se 1 (by rfl) ⟨843320, by rfl⟩ : syracuseStep 1124427 = 1686641) B1686641
theorem B1124439 : Blo 1120629 1124439 := bstep (se 1 (by rfl) ⟨843329, by rfl⟩ : syracuseStep 1124439 = 1686659) B1686659
theorem B1124459 : Blo 1120629 1124459 := bstep (se 1 (by rfl) ⟨843344, by rfl⟩ : syracuseStep 1124459 = 1686689) B1686689
theorem B1124471 : Blo 1120629 1124471 := bstep (se 1 (by rfl) ⟨843353, by rfl⟩ : syracuseStep 1124471 = 1686707) B1686707
theorem B1681547 : Blo 1120629 1681547 := bstep (se 1 (by rfl) ⟨1261160, by rfl⟩ : syracuseStep 1681547 = 2522321) B2522321
theorem B1124491 : Blo 1120629 1124491 := bstep (se 1 (by rfl) ⟨843368, by rfl⟩ : syracuseStep 1124491 = 1686737) B1686737
theorem B1681559 : Blo 1120629 1681559 := bstep (se 1 (by rfl) ⟨1261169, by rfl⟩ : syracuseStep 1681559 = 2522339) B2522339
theorem B1124503 : Blo 1120629 1124503 := bstep (se 1 (by rfl) ⟨843377, by rfl⟩ : syracuseStep 1124503 = 1686755) B1686755
theorem B1124523 : Blo 1120629 1124523 := bstep (se 1 (by rfl) ⟨843392, by rfl⟩ : syracuseStep 1124523 = 1686785) B1686785
theorem B1124535 : Blo 1120629 1124535 := bstep (se 1 (by rfl) ⟨843401, by rfl⟩ : syracuseStep 1124535 = 1686803) B1686803
theorem B2730187 : Blo 1120629 2730187 := bstep (se 1 (by rfl) ⟨2047640, by rfl⟩ : syracuseStep 2730187 = 4095281) B4095281
theorem B1124555 : Blo 1120629 1124555 := bstep (se 1 (by rfl) ⟨843416, by rfl⟩ : syracuseStep 1124555 = 1686833) B1686833
theorem B1124567 : Blo 1120629 1124567 := bstep (se 1 (by rfl) ⟨843425, by rfl⟩ : syracuseStep 1124567 = 1686851) B1686851
theorem B1681625 : Blo 1120629 1681625 := bstep (se 2 (by rfl) ⟨630609, by rfl⟩ : syracuseStep 1681625 = 1261219) B1261219
theorem B1124587 : Blo 1120629 1124587 := bstep (se 1 (by rfl) ⟨843440, by rfl⟩ : syracuseStep 1124587 = 1686881) B1686881
theorem B1124599 : Blo 1120629 1124599 := bstep (se 1 (by rfl) ⟨843449, by rfl⟩ : syracuseStep 1124599 = 1686899) B1686899
theorem B1124619 : Blo 1120629 1124619 := bstep (se 1 (by rfl) ⟨843464, by rfl⟩ : syracuseStep 1124619 = 1686929) B1686929
theorem B1681739 : Blo 1120629 1681739 := bstep (se 1 (by rfl) ⟨1261304, by rfl⟩ : syracuseStep 1681739 = 2522609) B2522609
theorem B1681751 : Blo 1120629 1681751 := bstep (se 1 (by rfl) ⟨1261313, by rfl⟩ : syracuseStep 1681751 = 2522627) B2522627
theorem B4041053 : Blo 1120629 4041053 := bstep (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) B1515395
theorem B2075033 : Blo 1120629 2075033 := bstep (se 2 (by rfl) ⟨778137, by rfl⟩ : syracuseStep 2075033 = 1556275) B1556275
theorem B1681817 : Blo 1120629 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B1681931 : Blo 1120629 1681931 := bstep (se 1 (by rfl) ⟨1261448, by rfl⟩ : syracuseStep 1681931 = 2522897) B2522897
theorem B7186961 : Blo 1120629 7186961 := bstep (se 2 (by rfl) ⟨2695110, by rfl⟩ : syracuseStep 7186961 = 5390221) B5390221
theorem B6400529 : Blo 1120629 6400529 := bstep (se 2 (by rfl) ⟨2400198, by rfl⟩ : syracuseStep 6400529 = 4800397) B4800397
theorem B1681943 : Blo 1120629 1681943 := bstep (se 1 (by rfl) ⟨1261457, by rfl⟩ : syracuseStep 1681943 = 2522915) B2522915
theorem B1682009 : Blo 1120629 1682009 := bstep (se 2 (by rfl) ⟨630753, by rfl⟩ : syracuseStep 1682009 = 1261507) B1261507
theorem B1682123 : Blo 1120629 1682123 := bstep (se 1 (by rfl) ⟨1261592, by rfl⟩ : syracuseStep 1682123 = 2523185) B2523185
theorem B1682135 : Blo 1120629 1682135 := bstep (se 1 (by rfl) ⟨1261601, by rfl⟩ : syracuseStep 1682135 = 2523203) B2523203
theorem B1682201 : Blo 1120629 1682201 := bstep (se 2 (by rfl) ⟨630825, by rfl⟩ : syracuseStep 1682201 = 1261651) B1261651
theorem B1682315 : Blo 1120629 1682315 := bstep (se 1 (by rfl) ⟨1261736, by rfl⟩ : syracuseStep 1682315 = 2523473) B2523473
theorem B1682327 : Blo 1120629 1682327 := bstep (se 1 (by rfl) ⟨1261745, by rfl⟩ : syracuseStep 1682327 = 2523491) B2523491
theorem B1420183 : Blo 1120629 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B1682393 : Blo 1120629 1682393 := bstep (se 2 (by rfl) ⟨630897, by rfl⟩ : syracuseStep 1682393 = 1261795) B1261795
theorem B4041731 : Blo 1120629 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B7482385 : Blo 1120629 7482385 := bstep (se 2 (by rfl) ⟨2805894, by rfl⟩ : syracuseStep 7482385 = 5611789) B5611789
theorem B1682507 : Blo 1120629 1682507 := bstep (se 1 (by rfl) ⟨1261880, by rfl⟩ : syracuseStep 1682507 = 2523761) B2523761
theorem B1682519 : Blo 1120629 1682519 := bstep (se 1 (by rfl) ⟨1261889, by rfl⟩ : syracuseStep 1682519 = 2523779) B2523779
theorem B4041859 : Blo 1120629 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B1682585 : Blo 1120629 1682585 := bstep (se 2 (by rfl) ⟨630969, by rfl⟩ : syracuseStep 1682585 = 1261939) B1261939
theorem B5123251 : Blo 1120629 5123251 := bstep (se 1 (by rfl) ⟨3842438, by rfl⟩ : syracuseStep 5123251 = 7684877) B7684877
theorem B1682699 : Blo 1120629 1682699 := bstep (se 1 (by rfl) ⟨1262024, by rfl⟩ : syracuseStep 1682699 = 2524049) B2524049
theorem B1682711 : Blo 1120629 1682711 := bstep (se 1 (by rfl) ⟨1262033, by rfl⟩ : syracuseStep 1682711 = 2524067) B2524067
theorem B2698571 : Blo 1120629 2698571 := bstep (se 1 (by rfl) ⟨2023928, by rfl⟩ : syracuseStep 2698571 = 4047857) B4047857
theorem B1682777 : Blo 1120629 1682777 := bstep (se 2 (by rfl) ⟨631041, by rfl⟩ : syracuseStep 1682777 = 1262083) B1262083
theorem B1682891 : Blo 1120629 1682891 := bstep (se 1 (by rfl) ⟨1262168, by rfl⟩ : syracuseStep 1682891 = 2524337) B2524337
theorem B1682903 : Blo 1120629 1682903 := bstep (se 1 (by rfl) ⟨1262177, by rfl⟩ : syracuseStep 1682903 = 2524355) B2524355
theorem B1682969 : Blo 1120629 1682969 := bstep (se 2 (by rfl) ⟨631113, by rfl⟩ : syracuseStep 1682969 = 1262227) B1262227
theorem B4795955 : Blo 1120629 4795955 := bstep (se 1 (by rfl) ⟨3596966, by rfl⟩ : syracuseStep 4795955 = 7193933) B7193933
theorem B2272897 : Blo 1120629 2272897 := bstep (se 2 (by rfl) ⟨852336, by rfl⟩ : syracuseStep 2272897 = 1704673) B1704673
theorem B1683083 : Blo 1120629 1683083 := bstep (se 1 (by rfl) ⟨1262312, by rfl⟩ : syracuseStep 1683083 = 2524625) B2524625
theorem B1683095 : Blo 1120629 1683095 := bstep (se 1 (by rfl) ⟨1262321, by rfl⟩ : syracuseStep 1683095 = 2524643) B2524643
theorem B1421003 : Blo 1120629 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B1683161 : Blo 1120629 1683161 := bstep (se 2 (by rfl) ⟨631185, by rfl⟩ : syracuseStep 1683161 = 1262371) B1262371
theorem B10792709 : Blo 1120629 10792709 := bstep (se 4 (by rfl) ⟨1011816, by rfl⟩ : syracuseStep 10792709 = 2023633) B2023633
theorem B8531729 : Blo 1120629 8531729 := bstep (se 2 (by rfl) ⟨3199398, by rfl⟩ : syracuseStep 8531729 = 6398797) B6398797
theorem B1683275 : Blo 1120629 1683275 := bstep (se 1 (by rfl) ⟨1262456, by rfl⟩ : syracuseStep 1683275 = 2524913) B2524913
theorem B1683287 : Blo 1120629 1683287 := bstep (se 1 (by rfl) ⟨1262465, by rfl⟩ : syracuseStep 1683287 = 2524931) B2524931
theorem B1683353 : Blo 1120629 1683353 := bstep (se 2 (by rfl) ⟨631257, by rfl⟩ : syracuseStep 1683353 = 1262515) B1262515
theorem B1683467 : Blo 1120629 1683467 := bstep (se 1 (by rfl) ⟨1262600, by rfl⟩ : syracuseStep 1683467 = 2525201) B2525201
theorem B1683479 : Blo 1120629 1683479 := bstep (se 1 (by rfl) ⟨1262609, by rfl⟩ : syracuseStep 1683479 = 2525219) B2525219
theorem B2699339 : Blo 1120629 2699339 := bstep (se 1 (by rfl) ⟨2024504, by rfl⟩ : syracuseStep 2699339 = 4049009) B4049009
theorem B1683545 : Blo 1120629 1683545 := bstep (se 2 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 1683545 = 1262659) B1262659
theorem B4042955 : Blo 1120629 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B1683659 : Blo 1120629 1683659 := bstep (se 1 (by rfl) ⟨1262744, by rfl⟩ : syracuseStep 1683659 = 2525489) B2525489
theorem B1683671 : Blo 1120629 1683671 := bstep (se 1 (by rfl) ⟨1262753, by rfl⟩ : syracuseStep 1683671 = 2525507) B2525507
theorem B5386513 : Blo 1120629 5386513 := bstep (se 2 (by rfl) ⟨2019942, by rfl⟩ : syracuseStep 5386513 = 4039885) B4039885
theorem B1683737 : Blo 1120629 1683737 := bstep (se 2 (by rfl) ⟨631401, by rfl⟩ : syracuseStep 1683737 = 1262803) B1262803
theorem B5386571 : Blo 1120629 5386571 := bstep (se 1 (by rfl) ⟨4039928, by rfl⟩ : syracuseStep 5386571 = 8079857) B8079857
theorem B5681501 : Blo 1120629 5681501 := bstep (se 3 (by rfl) ⟨1065281, by rfl⟩ : syracuseStep 5681501 = 2130563) B2130563
theorem B2273675 : Blo 1120629 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B1683851 : Blo 1120629 1683851 := bstep (se 1 (by rfl) ⟨1262888, by rfl⟩ : syracuseStep 1683851 = 2525777) B2525777
theorem B1421707 : Blo 1120629 1421707 := bstep (se 1 (by rfl) ⟨1066280, by rfl⟩ : syracuseStep 1421707 = 2132561) B2132561
theorem B1683863 : Blo 1120629 1683863 := bstep (se 1 (by rfl) ⟨1262897, by rfl⟩ : syracuseStep 1683863 = 2525795) B2525795
theorem B1683929 : Blo 1120629 1683929 := bstep (se 2 (by rfl) ⟨631473, by rfl⟩ : syracuseStep 1683929 = 1262947) B1262947
theorem B1684043 : Blo 1120629 1684043 := bstep (se 1 (by rfl) ⟨1263032, by rfl⟩ : syracuseStep 1684043 = 2526065) B2526065
theorem B1684055 : Blo 1120629 1684055 := bstep (se 1 (by rfl) ⟨1263041, by rfl⟩ : syracuseStep 1684055 = 2526083) B2526083
theorem B1421975 : Blo 1120629 1421975 := bstep (se 1 (by rfl) ⟨1066481, by rfl⟩ : syracuseStep 1421975 = 2132963) B2132963
theorem B1684121 : Blo 1120629 1684121 := bstep (se 2 (by rfl) ⟨631545, by rfl⟩ : syracuseStep 1684121 = 1263091) B1263091
theorem B1684235 : Blo 1120629 1684235 := bstep (se 1 (by rfl) ⟨1263176, by rfl⟩ : syracuseStep 1684235 = 2526353) B2526353
theorem B1684247 : Blo 1120629 1684247 := bstep (se 1 (by rfl) ⟨1263185, by rfl⟩ : syracuseStep 1684247 = 2526371) B2526371
theorem B1684313 : Blo 1120629 1684313 := bstep (se 2 (by rfl) ⟨631617, by rfl⟩ : syracuseStep 1684313 = 1263235) B1263235
theorem B9581489 : Blo 1120629 9581489 := bstep (se 2 (by rfl) ⟨3593058, by rfl⟩ : syracuseStep 9581489 = 7186117) B7186117
theorem B1684427 : Blo 1120629 1684427 := bstep (se 1 (by rfl) ⟨1263320, by rfl⟩ : syracuseStep 1684427 = 2526641) B2526641
theorem B1684439 : Blo 1120629 1684439 := bstep (se 1 (by rfl) ⟨1263329, by rfl⟩ : syracuseStep 1684439 = 2526659) B2526659
theorem B1684505 : Blo 1120629 1684505 := bstep (se 2 (by rfl) ⟨631689, by rfl⟩ : syracuseStep 1684505 = 1263379) B1263379
theorem B1684619 : Blo 1120629 1684619 := bstep (se 1 (by rfl) ⟨1263464, by rfl⟩ : syracuseStep 1684619 = 2526929) B2526929
theorem B1684631 : Blo 1120629 1684631 := bstep (se 1 (by rfl) ⟨1263473, by rfl⟩ : syracuseStep 1684631 = 2526947) B2526947
theorem B1684697 : Blo 1120629 1684697 := bstep (se 2 (by rfl) ⟨631761, by rfl⟩ : syracuseStep 1684697 = 1263523) B1263523
theorem B1684811 : Blo 1120629 1684811 := bstep (se 1 (by rfl) ⟨1263608, by rfl⟩ : syracuseStep 1684811 = 2527217) B2527217
theorem B1684823 : Blo 1120629 1684823 := bstep (se 1 (by rfl) ⟨1263617, by rfl⟩ : syracuseStep 1684823 = 2527235) B2527235
theorem B1422679 : Blo 1120629 1422679 := bstep (se 1 (by rfl) ⟨1067009, by rfl⟩ : syracuseStep 1422679 = 2134019) B2134019
theorem B1684889 : Blo 1120629 1684889 := bstep (se 2 (by rfl) ⟨631833, by rfl⟩ : syracuseStep 1684889 = 1263667) B1263667
theorem B3192281 : Blo 1120629 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B1685003 : Blo 1120629 1685003 := bstep (se 1 (by rfl) ⟨1263752, by rfl⟩ : syracuseStep 1685003 = 2527505) B2527505
theorem B1685015 : Blo 1120629 1685015 := bstep (se 1 (by rfl) ⟨1263761, by rfl⟩ : syracuseStep 1685015 = 2527523) B2527523
theorem B1947223 : Blo 1120629 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B1685081 : Blo 1120629 1685081 := bstep (se 2 (by rfl) ⟨631905, by rfl⟩ : syracuseStep 1685081 = 1263811) B1263811
theorem B1685195 : Blo 1120629 1685195 := bstep (se 1 (by rfl) ⟨1263896, by rfl⟩ : syracuseStep 1685195 = 2527793) B2527793
theorem B1685207 : Blo 1120629 1685207 := bstep (se 1 (by rfl) ⟨1263905, by rfl⟩ : syracuseStep 1685207 = 2527811) B2527811
theorem B1685273 : Blo 1120629 1685273 := bstep (se 2 (by rfl) ⟨631977, by rfl⟩ : syracuseStep 1685273 = 1263955) B1263955
theorem B1685387 : Blo 1120629 1685387 := bstep (se 1 (by rfl) ⟨1264040, by rfl⟩ : syracuseStep 1685387 = 2528081) B2528081
theorem B1685399 : Blo 1120629 1685399 := bstep (se 1 (by rfl) ⟨1264049, by rfl⟩ : syracuseStep 1685399 = 2528099) B2528099
theorem B24262577 : Blo 1120629 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B16627673 : Blo 1120629 16627673 := bstep (se 2 (by rfl) ⟨6235377, by rfl⟩ : syracuseStep 16627673 = 12470755) B12470755
theorem B1685465 : Blo 1120629 1685465 := bstep (se 2 (by rfl) ⟨632049, by rfl⟩ : syracuseStep 1685465 = 1264099) B1264099
theorem B1685579 : Blo 1120629 1685579 := bstep (se 1 (by rfl) ⟨1264184, by rfl⟩ : syracuseStep 1685579 = 2528369) B2528369
theorem B1685591 : Blo 1120629 1685591 := bstep (se 1 (by rfl) ⟨1264193, by rfl⟩ : syracuseStep 1685591 = 2528387) B2528387
theorem B12793949 : Blo 1120629 12793949 := bstep (se 3 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 12793949 = 4797731) B4797731
theorem B3782807 : Blo 1120629 3782807 := bstep (se 1 (by rfl) ⟨2837105, by rfl⟩ : syracuseStep 3782807 = 5674211) B5674211
theorem B4864151 : Blo 1120629 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B1685657 : Blo 1120629 1685657 := bstep (se 2 (by rfl) ⟨632121, by rfl⟩ : syracuseStep 1685657 = 1264243) B1264243
theorem B4044973 : Blo 1120629 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B4798723 : Blo 1120629 4798723 := bstep (se 1 (by rfl) ⟨3599042, by rfl⟩ : syracuseStep 4798723 = 7198085) B7198085
theorem B1685771 : Blo 1120629 1685771 := bstep (se 1 (by rfl) ⟨1264328, by rfl⟩ : syracuseStep 1685771 = 2528657) B2528657
theorem B3193111 : Blo 1120629 3193111 := bstep (se 1 (by rfl) ⟨2394833, by rfl⟩ : syracuseStep 3193111 = 4789667) B4789667
theorem B1685783 : Blo 1120629 1685783 := bstep (se 1 (by rfl) ⟨1264337, by rfl⟩ : syracuseStep 1685783 = 2528675) B2528675
theorem B2308439 : Blo 1120629 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B1685849 : Blo 1120629 1685849 := bstep (se 2 (by rfl) ⟨632193, by rfl⟩ : syracuseStep 1685849 = 1264387) B1264387
theorem B5683607 : Blo 1120629 5683607 := bstep (se 1 (by rfl) ⟨4262705, by rfl⟩ : syracuseStep 5683607 = 8525411) B8525411
theorem B1685963 : Blo 1120629 1685963 := bstep (se 1 (by rfl) ⟨1264472, by rfl⟩ : syracuseStep 1685963 = 2528945) B2528945
theorem B1685975 : Blo 1120629 1685975 := bstep (se 1 (by rfl) ⟨1264481, by rfl⟩ : syracuseStep 1685975 = 2528963) B2528963
theorem B5388761 : Blo 1120629 5388761 := bstep (se 2 (by rfl) ⟨2020785, by rfl⟩ : syracuseStep 5388761 = 4041571) B4041571
theorem B6076889 : Blo 1120629 6076889 := bstep (se 2 (by rfl) ⟨2278833, by rfl⟩ : syracuseStep 6076889 = 4557667) B4557667
theorem B1686041 : Blo 1120629 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B6076973 : Blo 1120629 6076973 := bstep (se 3 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 6076973 = 2278865) B2278865
theorem B1686155 : Blo 1120629 1686155 := bstep (se 1 (by rfl) ⟨1264616, by rfl⟩ : syracuseStep 1686155 = 2529233) B2529233
theorem B1686167 : Blo 1120629 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B3783347 : Blo 1120629 3783347 := bstep (se 1 (by rfl) ⟨2837510, by rfl⟩ : syracuseStep 3783347 = 5675021) B5675021
theorem B1686233 : Blo 1120629 1686233 := bstep (se 2 (by rfl) ⟨632337, by rfl⟩ : syracuseStep 1686233 = 1264675) B1264675
theorem B1686347 : Blo 1120629 1686347 := bstep (se 1 (by rfl) ⟨1264760, by rfl⟩ : syracuseStep 1686347 = 2529521) B2529521
theorem B1686359 : Blo 1120629 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B1686425 : Blo 1120629 1686425 := bstep (se 2 (by rfl) ⟨632409, by rfl⟩ : syracuseStep 1686425 = 1264819) B1264819
theorem B3783617 : Blo 1120629 3783617 := bstep (se 2 (by rfl) ⟨1418856, by rfl⟩ : syracuseStep 3783617 = 2837713) B2837713
theorem B1686539 : Blo 1120629 1686539 := bstep (se 1 (by rfl) ⟨1264904, by rfl⟩ : syracuseStep 1686539 = 2529809) B2529809
theorem B1686551 : Blo 1120629 1686551 := bstep (se 1 (by rfl) ⟨1264913, by rfl⟩ : syracuseStep 1686551 = 2529827) B2529827
theorem B3193931 : Blo 1120629 3193931 := bstep (se 1 (by rfl) ⟨2395448, by rfl⟩ : syracuseStep 3193931 = 4790897) B4790897
theorem B1686617 : Blo 1120629 1686617 := bstep (se 2 (by rfl) ⟨632481, by rfl⟩ : syracuseStep 1686617 = 1264963) B1264963
theorem B1260715 : Blo 1120629 1260715 := bstep (se 1 (by rfl) ⟨945536, by rfl⟩ : syracuseStep 1260715 = 1891073) B1891073
theorem B4799681 : Blo 1120629 4799681 := bstep (se 2 (by rfl) ⟨1799880, by rfl⟩ : syracuseStep 4799681 = 3599761) B3599761
theorem B1686731 : Blo 1120629 1686731 := bstep (se 1 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 1686731 = 2530097) B2530097
theorem B1686743 : Blo 1120629 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B4046041 : Blo 1120629 4046041 := bstep (se 2 (by rfl) ⟨1517265, by rfl⟩ : syracuseStep 4046041 = 3034531) B3034531
theorem B1260823 : Blo 1120629 1260823 := bstep (se 1 (by rfl) ⟨945617, by rfl⟩ : syracuseStep 1260823 = 1891235) B1891235
theorem B1686809 : Blo 1120629 1686809 := bstep (se 2 (by rfl) ⟨632553, by rfl⟩ : syracuseStep 1686809 = 1265107) B1265107
theorem B1686923 : Blo 1120629 1686923 := bstep (se 1 (by rfl) ⟨1265192, by rfl⟩ : syracuseStep 1686923 = 2530385) B2530385
theorem B1686935 : Blo 1120629 1686935 := bstep (se 1 (by rfl) ⟨1265201, by rfl⟩ : syracuseStep 1686935 = 2530403) B2530403
theorem B1261003 : Blo 1120629 1261003 := bstep (se 1 (by rfl) ⟨945752, by rfl⟩ : syracuseStep 1261003 = 1891505) B1891505
theorem B3784157 : Blo 1120629 3784157 := bstep (se 3 (by rfl) ⟨709529, by rfl⟩ : syracuseStep 3784157 = 1419059) B1419059
theorem B1261111 : Blo 1120629 1261111 := bstep (se 1 (by rfl) ⟨945833, by rfl⟩ : syracuseStep 1261111 = 1891667) B1891667
theorem B8535617 : Blo 1120629 8535617 := bstep (se 2 (by rfl) ⟨3200856, by rfl⟩ : syracuseStep 8535617 = 6401713) B6401713
theorem B16203415 : Blo 1120629 16203415 := bstep (se 1 (by rfl) ⟨12152561, by rfl⟩ : syracuseStep 16203415 = 24305123) B24305123
theorem B1261291 : Blo 1120629 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B1261399 : Blo 1120629 1261399 := bstep (se 1 (by rfl) ⟨946049, by rfl⟩ : syracuseStep 1261399 = 1892099) B1892099
theorem B1261579 : Blo 1120629 1261579 := bstep (se 1 (by rfl) ⟨946184, by rfl⟩ : syracuseStep 1261579 = 1892369) B1892369
theorem B12468259 : Blo 1120629 12468259 := bstep (se 1 (by rfl) ⟨9351194, by rfl⟩ : syracuseStep 12468259 = 18702389) B18702389
theorem B1261687 : Blo 1120629 1261687 := bstep (se 1 (by rfl) ⟨946265, by rfl⟩ : syracuseStep 1261687 = 1892531) B1892531
theorem B1261867 : Blo 1120629 1261867 := bstep (se 1 (by rfl) ⟨946400, by rfl⟩ : syracuseStep 1261867 = 1892801) B1892801
theorem B7192907 : Blo 1120629 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B1261975 : Blo 1120629 1261975 := bstep (se 1 (by rfl) ⟨946481, by rfl⟩ : syracuseStep 1261975 = 1892963) B1892963
theorem B2310617 : Blo 1120629 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B3785291 : Blo 1120629 3785291 := bstep (se 1 (by rfl) ⟨2838968, by rfl⟩ : syracuseStep 3785291 = 5677937) B5677937
theorem B1262155 : Blo 1120629 1262155 := bstep (se 1 (by rfl) ⟨946616, by rfl⟩ : syracuseStep 1262155 = 1893233) B1893233
theorem B2278039 : Blo 1120629 2278039 := bstep (se 1 (by rfl) ⟨1708529, by rfl⟩ : syracuseStep 2278039 = 3417059) B3417059
theorem B1262263 : Blo 1120629 1262263 := bstep (se 1 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 1262263 = 1893395) B1893395
theorem B9093923 : Blo 1120629 9093923 := bstep (se 1 (by rfl) ⟨6820442, by rfl⟩ : syracuseStep 9093923 = 13640885) B13640885
theorem B2736947 : Blo 1120629 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B2310977 : Blo 1120629 2310977 := bstep (se 2 (by rfl) ⟨866616, by rfl⟩ : syracuseStep 2310977 = 1733233) B1733233
theorem B4801355 : Blo 1120629 4801355 := bstep (se 1 (by rfl) ⟨3601016, by rfl⟩ : syracuseStep 4801355 = 7202033) B7202033
theorem B3785561 : Blo 1120629 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B1262443 : Blo 1120629 1262443 := bstep (se 1 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 1262443 = 1893665) B1893665
theorem B1262551 : Blo 1120629 1262551 := bstep (se 1 (by rfl) ⟨946913, by rfl⟩ : syracuseStep 1262551 = 1893827) B1893827
theorem B16172045 : Blo 1120629 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B1262731 : Blo 1120629 1262731 := bstep (se 1 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 1262731 = 1894097) B1894097
theorem B1262839 : Blo 1120629 1262839 := bstep (se 1 (by rfl) ⟨947129, by rfl⟩ : syracuseStep 1262839 = 1894259) B1894259
theorem B6833483 : Blo 1120629 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B15582581 : Blo 1120629 15582581 := bstep (se 5 (by rfl) ⟨730433, by rfl⟩ : syracuseStep 15582581 = 1460867) B1460867
theorem B1197451 : Blo 1120629 1197451 := bstep (se 1 (by rfl) ⟨898088, by rfl⟩ : syracuseStep 1197451 = 1796177) B1796177
theorem B1263019 : Blo 1120629 1263019 := bstep (se 1 (by rfl) ⟨947264, by rfl⟩ : syracuseStep 1263019 = 1894529) B1894529
theorem B7194035 : Blo 1120629 7194035 := bstep (se 1 (by rfl) ⟨5395526, by rfl⟩ : syracuseStep 7194035 = 10791053) B10791053
theorem B8537561 : Blo 1120629 8537561 := bstep (se 2 (by rfl) ⟨3201585, by rfl⟩ : syracuseStep 8537561 = 6403171) B6403171
theorem B3196381 : Blo 1120629 3196381 := bstep (se 3 (by rfl) ⟨599321, by rfl⟩ : syracuseStep 3196381 = 1198643) B1198643
theorem B3786263 : Blo 1120629 3786263 := bstep (se 1 (by rfl) ⟨2839697, by rfl⟩ : syracuseStep 3786263 = 5679395) B5679395
theorem B1263127 : Blo 1120629 1263127 := bstep (se 1 (by rfl) ⟨947345, by rfl⟩ : syracuseStep 1263127 = 1894691) B1894691
theorem B1263307 : Blo 1120629 1263307 := bstep (se 1 (by rfl) ⟨947480, by rfl⟩ : syracuseStep 1263307 = 1894961) B1894961
theorem B2279191 : Blo 1120629 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B1263415 : Blo 1120629 1263415 := bstep (se 1 (by rfl) ⟨947561, by rfl⟩ : syracuseStep 1263415 = 1895123) B1895123
theorem B2049907 : Blo 1120629 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B5687171 : Blo 1120629 5687171 := bstep (se 1 (by rfl) ⟨4265378, by rfl⟩ : syracuseStep 5687171 = 8530757) B8530757
theorem B6932441 : Blo 1120629 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B1263595 : Blo 1120629 1263595 := bstep (se 1 (by rfl) ⟨947696, by rfl⟩ : syracuseStep 1263595 = 1895393) B1895393
theorem B3786803 : Blo 1120629 3786803 := bstep (se 1 (by rfl) ⟨2840102, by rfl⟩ : syracuseStep 3786803 = 5680205) B5680205
theorem B1263703 : Blo 1120629 1263703 := bstep (se 1 (by rfl) ⟨947777, by rfl⟩ : syracuseStep 1263703 = 1895555) B1895555
theorem B1198199 : Blo 1120629 1198199 := bstep (se 1 (by rfl) ⟨898649, by rfl⟩ : syracuseStep 1198199 = 1797299) B1797299
theorem B1263883 : Blo 1120629 1263883 := bstep (se 1 (by rfl) ⟨947912, by rfl⟩ : syracuseStep 1263883 = 1895825) B1895825
theorem B3787073 : Blo 1120629 3787073 := bstep (se 2 (by rfl) ⟨1420152, by rfl⟩ : syracuseStep 3787073 = 2840305) B2840305
theorem B1263991 : Blo 1120629 1263991 := bstep (se 1 (by rfl) ⟨947993, by rfl⟩ : syracuseStep 1263991 = 1895987) B1895987
theorem B4671917 : Blo 1120629 4671917 := bstep (se 3 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 4671917 = 1751969) B1751969
theorem B2279897 : Blo 1120629 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B2837015 : Blo 1120629 2837015 := bstep (se 1 (by rfl) ⟨2127761, by rfl⟩ : syracuseStep 2837015 = 4255523) B4255523
theorem B1264171 : Blo 1120629 1264171 := bstep (se 1 (by rfl) ⟨948128, by rfl⟩ : syracuseStep 1264171 = 1896257) B1896257
theorem B5065267 : Blo 1120629 5065267 := bstep (se 1 (by rfl) ⟨3798950, by rfl⟩ : syracuseStep 5065267 = 7597901) B7597901
theorem B4049459 : Blo 1120629 4049459 := bstep (se 1 (by rfl) ⟨3037094, by rfl⟩ : syracuseStep 4049459 = 6074189) B6074189
theorem B1264279 : Blo 1120629 1264279 := bstep (se 1 (by rfl) ⟨948209, by rfl⟩ : syracuseStep 1264279 = 1896419) B1896419
theorem B3197657 : Blo 1120629 3197657 := bstep (se 2 (by rfl) ⟨1199121, by rfl⟩ : syracuseStep 3197657 = 2398243) B2398243
theorem B8080145 : Blo 1120629 8080145 := bstep (se 2 (by rfl) ⟨3030054, by rfl⟩ : syracuseStep 8080145 = 6060109) B6060109
theorem B1264459 : Blo 1120629 1264459 := bstep (se 1 (by rfl) ⟨948344, by rfl⟩ : syracuseStep 1264459 = 1896689) B1896689
theorem B3787613 : Blo 1120629 3787613 := bstep (se 3 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 3787613 = 1420355) B1420355
theorem B1264567 : Blo 1120629 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B1919947 : Blo 1120629 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B9096257 : Blo 1120629 9096257 := bstep (se 2 (by rfl) ⟨3411096, by rfl⟩ : syracuseStep 9096257 = 6822193) B6822193
theorem B1264747 : Blo 1120629 1264747 := bstep (se 1 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 1264747 = 1897121) B1897121
theorem B5393587 : Blo 1120629 5393587 := bstep (se 1 (by rfl) ⟨4045190, by rfl⟩ : syracuseStep 5393587 = 8090381) B8090381
theorem B1264855 : Blo 1120629 1264855 := bstep (se 1 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 1264855 = 1897283) B1897283
theorem B2837825 : Blo 1120629 2837825 := bstep (se 2 (by rfl) ⟨1064184, by rfl⟩ : syracuseStep 2837825 = 2128369) B2128369
theorem B1199467 : Blo 1120629 1199467 := bstep (se 1 (by rfl) ⟨899600, by rfl⟩ : syracuseStep 1199467 = 1799201) B1799201
theorem B1265035 : Blo 1120629 1265035 := bstep (se 1 (by rfl) ⟨948776, by rfl⟩ : syracuseStep 1265035 = 1897553) B1897553
theorem B1265143 : Blo 1120629 1265143 := bstep (se 1 (by rfl) ⟨948857, by rfl⟩ : syracuseStep 1265143 = 1897715) B1897715
theorem B6246067 : Blo 1120629 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B5394221 : Blo 1120629 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B2838361 : Blo 1120629 2838361 := bstep (se 2 (by rfl) ⟨1064385, by rfl⟩ : syracuseStep 2838361 = 2128771) B2128771
theorem B3788747 : Blo 1120629 3788747 := bstep (se 1 (by rfl) ⟨2841560, by rfl⟩ : syracuseStep 3788747 = 5683121) B5683121
theorem B1200215 : Blo 1120629 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B3789017 : Blo 1120629 3789017 := bstep (se 2 (by rfl) ⟨1420881, by rfl⟩ : syracuseStep 3789017 = 2841763) B2841763
theorem B35049773 : Blo 1120629 35049773 := bstep (se 3 (by rfl) ⟨6571832, by rfl⟩ : syracuseStep 35049773 = 13143665) B13143665
theorem B3199297 : Blo 1120629 3199297 := bstep (se 2 (by rfl) ⟨1199736, by rfl⟩ : syracuseStep 3199297 = 2399473) B2399473
theorem B12767705 : Blo 1120629 12767705 := bstep (se 2 (by rfl) ⟨4787889, by rfl⟩ : syracuseStep 12767705 = 9575779) B9575779
theorem B2019863 : Blo 1120629 2019863 := bstep (se 1 (by rfl) ⟨1514897, by rfl⟩ : syracuseStep 2019863 = 3029795) B3029795
theorem B4051777 : Blo 1120629 4051777 := bstep (se 2 (by rfl) ⟨1519416, by rfl⟩ : syracuseStep 4051777 = 3038833) B3038833
theorem B3789719 : Blo 1120629 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B2839475 : Blo 1120629 2839475 := bstep (se 1 (by rfl) ⟨2129606, by rfl⟩ : syracuseStep 2839475 = 4259213) B4259213
theorem B16176145 : Blo 1120629 16176145 := bstep (se 2 (by rfl) ⟨6066054, by rfl⟩ : syracuseStep 16176145 = 12132109) B12132109
theorem B2020555 : Blo 1120629 2020555 := bstep (se 1 (by rfl) ⟨1515416, by rfl⟩ : syracuseStep 2020555 = 3030833) B3030833
theorem B2839769 : Blo 1120629 2839769 := bstep (se 2 (by rfl) ⟨1064913, by rfl⟩ : syracuseStep 2839769 = 2129827) B2129827
theorem B4052227 : Blo 1120629 4052227 := bstep (se 1 (by rfl) ⟨3039170, by rfl⟩ : syracuseStep 4052227 = 6078341) B6078341
theorem B4609331 : Blo 1120629 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B10245527 : Blo 1120629 10245527 := bstep (se 1 (by rfl) ⟨7684145, by rfl⟩ : syracuseStep 10245527 = 15368291) B15368291
theorem B3790259 : Blo 1120629 3790259 := bstep (se 1 (by rfl) ⟨2842694, by rfl⟩ : syracuseStep 3790259 = 5685389) B5685389
theorem B5690897 : Blo 1120629 5690897 := bstep (se 2 (by rfl) ⟨2134086, by rfl⟩ : syracuseStep 5690897 = 4268173) B4268173
theorem B3593879 : Blo 1120629 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B10245811 : Blo 1120629 10245811 := bstep (se 1 (by rfl) ⟨7684358, by rfl⟩ : syracuseStep 10245811 = 15368717) B15368717
theorem B5691059 : Blo 1120629 5691059 := bstep (se 1 (by rfl) ⟨4268294, by rfl⟩ : syracuseStep 5691059 = 8536589) B8536589
theorem B3790529 : Blo 1120629 3790529 := bstep (se 2 (by rfl) ⟨1421448, by rfl⟩ : syracuseStep 3790529 = 2842897) B2842897
theorem B4151243 : Blo 1120629 4151243 := bstep (se 1 (by rfl) ⟨3113432, by rfl⟩ : syracuseStep 4151243 = 6226865) B6226865
theorem B3200971 : Blo 1120629 3200971 := bstep (se 1 (by rfl) ⟨2400728, by rfl⟩ : syracuseStep 3200971 = 4801457) B4801457
theorem B87447605 : Blo 1120629 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B3037277 : Blo 1120629 3037277 := bstep (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) B1138979
theorem B9590885 : Blo 1120629 9590885 := bstep (se 4 (by rfl) ⟨899145, by rfl⟩ : syracuseStep 9590885 = 1798291) B1798291
theorem B2021593 : Blo 1120629 2021593 := bstep (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) B1516195
theorem B3791069 : Blo 1120629 3791069 := bstep (se 3 (by rfl) ⟨710825, by rfl⟩ : syracuseStep 3791069 = 1421651) B1421651
theorem B3201245 : Blo 1120629 3201245 := bstep (se 3 (by rfl) ⟨600233, by rfl⟩ : syracuseStep 3201245 = 1200467) B1200467
theorem B18209123 : Blo 1120629 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B9099697 : Blo 1120629 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B15358481 : Blo 1120629 15358481 := bstep (se 2 (by rfl) ⟨5759430, by rfl⟩ : syracuseStep 15358481 = 11518861) B11518861
theorem B2021939 : Blo 1120629 2021939 := bstep (se 1 (by rfl) ⟨1516454, by rfl⟩ : syracuseStep 2021939 = 3032909) B3032909
theorem B1137451 : Blo 1120629 1137451 := bstep (se 1 (by rfl) ⟨853088, by rfl⟩ : syracuseStep 1137451 = 1706177) B1706177
theorem B1891147 : Blo 1120629 1891147 := bstep (se 1 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 1891147 = 2836721) B2836721
theorem B2841419 : Blo 1120629 2841419 := bstep (se 1 (by rfl) ⟨2131064, by rfl⟩ : syracuseStep 2841419 = 4262129) B4262129
theorem B1891289 : Blo 1120629 1891289 := bstep (se 2 (by rfl) ⟨709233, by rfl⟩ : syracuseStep 1891289 = 1418467) B1418467
theorem B2022401 : Blo 1120629 2022401 := bstep (se 2 (by rfl) ⟨758400, by rfl⟩ : syracuseStep 2022401 = 1516801) B1516801
theorem B1891417 : Blo 1120629 1891417 := bstep (se 2 (by rfl) ⟨709281, by rfl⟩ : syracuseStep 1891417 = 1418563) B1418563
theorem B1596505 : Blo 1120629 1596505 := bstep (se 2 (by rfl) ⟨598689, by rfl⟩ : syracuseStep 1596505 = 1197379) B1197379
theorem B2022617 : Blo 1120629 2022617 := bstep (se 2 (by rfl) ⟨758481, by rfl⟩ : syracuseStep 2022617 = 1516963) B1516963
theorem B3792203 : Blo 1120629 3792203 := bstep (se 1 (by rfl) ⟨2844152, by rfl⟩ : syracuseStep 3792203 = 5688305) B5688305
theorem B5397911 : Blo 1120629 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B5693003 : Blo 1120629 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B3792473 : Blo 1120629 3792473 := bstep (se 2 (by rfl) ⟨1422177, by rfl⟩ : syracuseStep 3792473 = 2844355) B2844355
theorem B1891991 : Blo 1120629 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B1892119 : Blo 1120629 1892119 := bstep (se 1 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 1892119 = 2838179) B2838179
theorem B2842391 : Blo 1120629 2842391 := bstep (se 1 (by rfl) ⟨2131793, by rfl⟩ : syracuseStep 2842391 = 4263587) B4263587
theorem B3596339 : Blo 1120629 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B2875571 : Blo 1120629 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B3793175 : Blo 1120629 3793175 := bstep (se 1 (by rfl) ⟨2844881, by rfl⟩ : syracuseStep 3793175 = 5689763) B5689763
theorem B1892747 : Blo 1120629 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B2843059 : Blo 1120629 2843059 := bstep (se 1 (by rfl) ⟨2132294, by rfl⟩ : syracuseStep 2843059 = 4264589) B4264589
theorem B3596761 : Blo 1120629 3596761 := bstep (se 2 (by rfl) ⟨1348785, by rfl⟩ : syracuseStep 3596761 = 2697571) B2697571
theorem B1892875 : Blo 1120629 1892875 := bstep (se 1 (by rfl) ⟨1419656, by rfl⟩ : syracuseStep 1892875 = 2839313) B2839313
theorem B1597963 : Blo 1120629 1597963 := bstep (se 1 (by rfl) ⟨1198472, by rfl⟩ : syracuseStep 1597963 = 2396945) B2396945
theorem B2843201 : Blo 1120629 2843201 := bstep (se 2 (by rfl) ⟨1066200, by rfl⟩ : syracuseStep 2843201 = 2132401) B2132401
theorem B8774245 : Blo 1120629 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B1893017 : Blo 1120629 1893017 := bstep (se 2 (by rfl) ⟨709881, by rfl⟩ : syracuseStep 1893017 = 1419763) B1419763
theorem B3596993 : Blo 1120629 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B9593549 : Blo 1120629 9593549 := bstep (se 3 (by rfl) ⟨1798790, by rfl⟩ : syracuseStep 9593549 = 3597581) B3597581
theorem B1893145 : Blo 1120629 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B3793715 : Blo 1120629 3793715 := bstep (se 1 (by rfl) ⟨2845286, by rfl⟩ : syracuseStep 3793715 = 5690573) B5690573
theorem B3793985 : Blo 1120629 3793985 := bstep (se 2 (by rfl) ⟨1422744, by rfl⟩ : syracuseStep 3793985 = 2845489) B2845489
theorem B1139863 : Blo 1120629 1139863 := bstep (se 1 (by rfl) ⟨854897, by rfl⟩ : syracuseStep 1139863 = 1709795) B1709795
theorem B1893719 : Blo 1120629 1893719 := bstep (se 1 (by rfl) ⟨1420289, by rfl⟩ : syracuseStep 1893719 = 2840579) B2840579
theorem B1893847 : Blo 1120629 1893847 := bstep (se 1 (by rfl) ⟨1420385, by rfl⟩ : syracuseStep 1893847 = 2840771) B2840771
theorem B3794525 : Blo 1120629 3794525 := bstep (se 3 (by rfl) ⟨711473, by rfl⟩ : syracuseStep 3794525 = 1422947) B1422947
theorem B7300787 : Blo 1120629 7300787 := bstep (se 1 (by rfl) ⟨5475590, by rfl⟩ : syracuseStep 7300787 = 10951181) B10951181
theorem B1599193 : Blo 1120629 1599193 := bstep (se 2 (by rfl) ⟨599697, by rfl⟩ : syracuseStep 1599193 = 1199395) B1199395
theorem B2844467 : Blo 1120629 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B10250077 : Blo 1120629 10250077 := bstep (se 3 (by rfl) ⟨1921889, by rfl⟩ : syracuseStep 10250077 = 3843779) B3843779
theorem B1894475 : Blo 1120629 1894475 := bstep (se 1 (by rfl) ⟨1420856, by rfl⟩ : syracuseStep 1894475 = 2841713) B2841713
theorem B6383717 : Blo 1120629 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B1894603 : Blo 1120629 1894603 := bstep (se 1 (by rfl) ⟨1420952, by rfl⟩ : syracuseStep 1894603 = 2841905) B2841905
theorem B2845003 : Blo 1120629 2845003 := bstep (se 1 (by rfl) ⟨2133752, by rfl⟩ : syracuseStep 2845003 = 4267505) B4267505
theorem B1894745 : Blo 1120629 1894745 := bstep (se 2 (by rfl) ⟨710529, by rfl⟩ : syracuseStep 1894745 = 1421059) B1421059
theorem B4221335 : Blo 1120629 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B2877889 : Blo 1120629 2877889 := bstep (se 2 (by rfl) ⟨1079208, by rfl⟩ : syracuseStep 2877889 = 2158417) B2158417
theorem B1894873 : Blo 1120629 1894873 := bstep (se 2 (by rfl) ⟨710577, by rfl⟩ : syracuseStep 1894873 = 1421155) B1421155
theorem B2845145 : Blo 1120629 2845145 := bstep (se 2 (by rfl) ⟨1066929, by rfl⟩ : syracuseStep 2845145 = 2133859) B2133859
theorem B1600087 : Blo 1120629 1600087 := bstep (se 1 (by rfl) ⟨1200065, by rfl⟩ : syracuseStep 1600087 = 2400131) B2400131
theorem B1895447 : Blo 1120629 1895447 := bstep (se 1 (by rfl) ⟨1421585, by rfl⟩ : syracuseStep 1895447 = 2843171) B2843171
theorem B3599453 : Blo 1120629 3599453 := bstep (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) B1349795
theorem B1600651 : Blo 1120629 1600651 := bstep (se 1 (by rfl) ⟨1200488, by rfl⟩ : syracuseStep 1600651 = 2400977) B2400977
theorem B1895575 : Blo 1120629 1895575 := bstep (se 1 (by rfl) ⟨1421681, by rfl⟩ : syracuseStep 1895575 = 2843363) B2843363
theorem B3370205 : Blo 1120629 3370205 := bstep (se 3 (by rfl) ⟨631913, by rfl⟩ : syracuseStep 3370205 = 1263827) B1263827
theorem B2845975 : Blo 1120629 2845975 := bstep (se 1 (by rfl) ⟨2134481, by rfl⟩ : syracuseStep 2845975 = 4268963) B4268963
theorem B4255051 : Blo 1120629 4255051 := bstep (se 1 (by rfl) ⟨3191288, by rfl⟩ : syracuseStep 4255051 = 6382577) B6382577
theorem B19426661 : Blo 1120629 19426661 := bstep (se 4 (by rfl) ⟨1821249, by rfl⟩ : syracuseStep 19426661 = 3642499) B3642499
theorem B4255325 : Blo 1120629 4255325 := bstep (se 3 (by rfl) ⟨797873, by rfl⟩ : syracuseStep 4255325 = 1595747) B1595747
theorem B2846411 : Blo 1120629 2846411 := bstep (se 1 (by rfl) ⟨2134808, by rfl⟩ : syracuseStep 2846411 = 4269617) B4269617
theorem B1896203 : Blo 1120629 1896203 := bstep (se 1 (by rfl) ⟨1422152, by rfl⟩ : syracuseStep 1896203 = 2844305) B2844305
theorem B1896331 : Blo 1120629 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B1896473 : Blo 1120629 1896473 := bstep (se 2 (by rfl) ⟨711177, by rfl⟩ : syracuseStep 1896473 = 1422355) B1422355
theorem B9105473 : Blo 1120629 9105473 := bstep (se 2 (by rfl) ⟨3414552, by rfl⟩ : syracuseStep 9105473 = 6829105) B6829105
theorem B38924363 : Blo 1120629 38924363 := bstep (se 1 (by rfl) ⟨29193272, by rfl⟩ : syracuseStep 38924363 = 58386545) B58386545
theorem B1896601 : Blo 1120629 1896601 := bstep (se 2 (by rfl) ⟨711225, by rfl⟩ : syracuseStep 1896601 = 1422451) B1422451
theorem B4256023 : Blo 1120629 4256023 := bstep (se 1 (by rfl) ⟨3192017, by rfl⟩ : syracuseStep 4256023 = 6384035) B6384035
theorem B43184501 : Blo 1120629 43184501 := bstep (se 5 (by rfl) ⟨2024273, by rfl⟩ : syracuseStep 43184501 = 4048547) B4048547
theorem B1897175 : Blo 1120629 1897175 := bstep (se 1 (by rfl) ⟨1422881, by rfl⟩ : syracuseStep 1897175 = 2845763) B2845763
theorem B1897303 : Blo 1120629 1897303 := bstep (se 1 (by rfl) ⟨1422977, by rfl⟩ : syracuseStep 1897303 = 2845955) B2845955
theorem B5403485 : Blo 1120629 5403485 := bstep (se 3 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 5403485 = 2026307) B2026307
theorem B10777445 : Blo 1120629 10777445 := bstep (se 4 (by rfl) ⟨1010385, by rfl⟩ : syracuseStep 10777445 = 2020771) B2020771
theorem B5403523 : Blo 1120629 5403523 := bstep (se 1 (by rfl) ⟨4052642, by rfl⟩ : syracuseStep 5403523 = 8105285) B8105285
theorem B4256813 : Blo 1120629 4256813 := bstep (se 3 (by rfl) ⟨798152, by rfl⟩ : syracuseStep 4256813 = 1596305) B1596305
theorem B4060205 : Blo 1120629 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B1438807 : Blo 1120629 1438807 := bstep (se 1 (by rfl) ⟨1079105, by rfl⟩ : syracuseStep 1438807 = 2158211) B2158211
theorem B8746163 : Blo 1120629 8746163 := bstep (se 1 (by rfl) ⟨6559622, by rfl⟩ : syracuseStep 8746163 = 13119245) B13119245
theorem B4552139 : Blo 1120629 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B2127617 : Blo 1120629 2127617 := bstep (se 2 (by rfl) ⟨797856, by rfl⟩ : syracuseStep 2127617 = 1595713) B1595713
theorem B2127883 : Blo 1120629 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B9107747 : Blo 1120629 9107747 := bstep (se 1 (by rfl) ⟨6830810, by rfl⟩ : syracuseStep 9107747 = 13661621) B13661621
theorem B4258241 : Blo 1120629 4258241 := bstep (se 2 (by rfl) ⟨1596840, by rfl⟩ : syracuseStep 4258241 = 3193681) B3193681
theorem B2521547 : Blo 1120629 2521547 := bstep (se 1 (by rfl) ⟨1891160, by rfl⟩ : syracuseStep 2521547 = 3782321) B3782321
theorem B2128331 : Blo 1120629 2128331 := bstep (se 1 (by rfl) ⟨1596248, by rfl⟩ : syracuseStep 2128331 = 3192497) B3192497
theorem B2521601 : Blo 1120629 2521601 := bstep (se 2 (by rfl) ⟨945600, by rfl⟩ : syracuseStep 2521601 = 1891201) B1891201
theorem B2128513 : Blo 1120629 2128513 := bstep (se 2 (by rfl) ⟨798192, by rfl⟩ : syracuseStep 2128513 = 1596385) B1596385
theorem B2521817 : Blo 1120629 2521817 := bstep (se 2 (by rfl) ⟨945681, by rfl⟩ : syracuseStep 2521817 = 1891363) B1891363
theorem B2521907 : Blo 1120629 2521907 := bstep (se 1 (by rfl) ⟨1891430, by rfl⟩ : syracuseStep 2521907 = 3782861) B3782861
theorem B2521943 : Blo 1120629 2521943 := bstep (se 1 (by rfl) ⟨1891457, by rfl⟩ : syracuseStep 2521943 = 3782915) B3782915
theorem B1801111 : Blo 1120629 1801111 := bstep (se 1 (by rfl) ⟨1350833, by rfl⟩ : syracuseStep 1801111 = 2701667) B2701667
theorem B2128855 : Blo 1120629 2128855 := bstep (se 1 (by rfl) ⟨1596641, by rfl⟩ : syracuseStep 2128855 = 3193283) B3193283
theorem B2522123 : Blo 1120629 2522123 := bstep (se 1 (by rfl) ⟨1891592, by rfl⟩ : syracuseStep 2522123 = 3783185) B3783185
theorem B2522177 : Blo 1120629 2522177 := bstep (se 2 (by rfl) ⟨945816, by rfl⟩ : syracuseStep 2522177 = 1891633) B1891633
theorem B1801367 : Blo 1120629 1801367 := bstep (se 1 (by rfl) ⟨1351025, by rfl⟩ : syracuseStep 1801367 = 2702051) B2702051
theorem B2129075 : Blo 1120629 2129075 := bstep (se 1 (by rfl) ⟨1596806, by rfl⟩ : syracuseStep 2129075 = 3193613) B3193613
theorem B2522393 : Blo 1120629 2522393 := bstep (se 2 (by rfl) ⟨945897, by rfl⟩ : syracuseStep 2522393 = 1891795) B1891795
theorem B2522483 : Blo 1120629 2522483 := bstep (se 1 (by rfl) ⟨1891862, by rfl⟩ : syracuseStep 2522483 = 3783725) B3783725
theorem B2522519 : Blo 1120629 2522519 := bstep (se 1 (by rfl) ⟨1891889, by rfl⟩ : syracuseStep 2522519 = 3783779) B3783779
theorem B2129303 : Blo 1120629 2129303 := bstep (se 1 (by rfl) ⟨1596977, by rfl⟩ : syracuseStep 2129303 = 3193955) B3193955
theorem B2522699 : Blo 1120629 2522699 := bstep (se 1 (by rfl) ⟨1892024, by rfl⟩ : syracuseStep 2522699 = 3784049) B3784049
theorem B2522753 : Blo 1120629 2522753 := bstep (se 2 (by rfl) ⟨946032, by rfl⟩ : syracuseStep 2522753 = 1892065) B1892065
theorem B2129561 : Blo 1120629 2129561 := bstep (se 2 (by rfl) ⟨798585, by rfl⟩ : syracuseStep 2129561 = 1597171) B1597171
theorem B6389549 : Blo 1120629 6389549 := bstep (se 3 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 6389549 = 2396081) B2396081
theorem B7667531 : Blo 1120629 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B2522969 : Blo 1120629 2522969 := bstep (se 2 (by rfl) ⟨946113, by rfl⟩ : syracuseStep 2522969 = 1892227) B1892227
theorem B4259729 : Blo 1120629 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B2523059 : Blo 1120629 2523059 := bstep (se 1 (by rfl) ⟨1892294, by rfl⟩ : syracuseStep 2523059 = 3784589) B3784589
theorem B2523095 : Blo 1120629 2523095 := bstep (se 1 (by rfl) ⟨1892321, by rfl⟩ : syracuseStep 2523095 = 3784643) B3784643
theorem B6390049 : Blo 1120629 6390049 := bstep (se 2 (by rfl) ⟨2396268, by rfl⟩ : syracuseStep 6390049 = 4792537) B4792537
theorem B2523527 : Blo 1120629 2523527 := bstep (se 1 (by rfl) ⟨1892645, by rfl⟩ : syracuseStep 2523527 = 3785291) B3785291
theorem B6062615 : Blo 1120629 6062615 := bstep (se 1 (by rfl) ⟨4546961, by rfl⟩ : syracuseStep 6062615 = 9093923) B9093923
theorem B932774453 : Blo 1120629 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B2523707 : Blo 1120629 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B10781363 : Blo 1120629 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B25887413 : Blo 1120629 25887413 := bstep (se 5 (by rfl) ⟨1213472, by rfl⟩ : syracuseStep 25887413 = 2426945) B2426945
theorem B2523833 : Blo 1120629 2523833 := bstep (se 2 (by rfl) ⟨946437, by rfl⟩ : syracuseStep 2523833 = 1892875) B1892875
theorem B2130617 : Blo 1120629 2130617 := bstep (se 2 (by rfl) ⟨798981, by rfl⟩ : syracuseStep 2130617 = 1597963) B1597963
theorem B11698993 : Blo 1120629 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B4555655 : Blo 1120629 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B10388387 : Blo 1120629 10388387 := bstep (se 1 (by rfl) ⟨7791290, by rfl⟩ : syracuseStep 10388387 = 15582581) B15582581
theorem B2524175 : Blo 1120629 2524175 := bstep (se 1 (by rfl) ⟨1893131, by rfl⟩ : syracuseStep 2524175 = 3786263) B3786263
theorem B2524193 : Blo 1120629 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B18187325 : Blo 1120629 18187325 := bstep (se 3 (by rfl) ⟨3410123, by rfl⟩ : syracuseStep 18187325 = 6820247) B6820247
theorem B16188653 : Blo 1120629 16188653 := bstep (se 3 (by rfl) ⟨3035372, by rfl⟩ : syracuseStep 16188653 = 6070745) B6070745
theorem B6161645 : Blo 1120629 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B4621627 : Blo 1120629 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B2524535 : Blo 1120629 2524535 := bstep (se 1 (by rfl) ⟨1893401, by rfl⟩ : syracuseStep 2524535 = 3786803) B3786803
theorem B6391325 : Blo 1120629 6391325 := bstep (se 3 (by rfl) ⟨1198373, by rfl⟩ : syracuseStep 6391325 = 2396747) B2396747
theorem B2524715 : Blo 1120629 2524715 := bstep (se 1 (by rfl) ⟨1893536, by rfl⟩ : syracuseStep 2524715 = 3787073) B3787073
theorem B3114611 : Blo 1120629 3114611 := bstep (se 1 (by rfl) ⟨2335958, by rfl⟩ : syracuseStep 3114611 = 4671917) B4671917
theorem B8521523 : Blo 1120629 8521523 := bstep (se 1 (by rfl) ⟨6391142, by rfl⟩ : syracuseStep 8521523 = 12782285) B12782285
theorem B2131771 : Blo 1120629 2131771 := bstep (se 1 (by rfl) ⟨1598828, by rfl⟩ : syracuseStep 2131771 = 3197657) B3197657
theorem B2525075 : Blo 1120629 2525075 := bstep (se 1 (by rfl) ⟨1893806, by rfl⟩ : syracuseStep 2525075 = 3787613) B3787613
theorem B2525129 : Blo 1120629 2525129 := bstep (se 2 (by rfl) ⟨946923, by rfl⟩ : syracuseStep 2525129 = 1893847) B1893847
theorem B4261841 : Blo 1120629 4261841 := bstep (se 2 (by rfl) ⟨1598190, by rfl⟩ : syracuseStep 4261841 = 3196381) B3196381
theorem B6162605 : Blo 1120629 6162605 := bstep (se 3 (by rfl) ⟨1155488, by rfl⟩ : syracuseStep 6162605 = 2310977) B2310977
theorem B4327625 : Blo 1120629 4327625 := bstep (se 2 (by rfl) ⟨1622859, by rfl⟩ : syracuseStep 4327625 = 3245719) B3245719
theorem B4262159 : Blo 1120629 4262159 := bstep (se 1 (by rfl) ⟨3196619, by rfl⟩ : syracuseStep 4262159 = 6393239) B6393239
theorem B2132257 : Blo 1120629 2132257 := bstep (se 2 (by rfl) ⟨799596, by rfl⟩ : syracuseStep 2132257 = 1599193) B1599193
theorem B13666769 : Blo 1120629 13666769 := bstep (se 2 (by rfl) ⟨5125038, by rfl⟩ : syracuseStep 13666769 = 10250077) B10250077
theorem B4557341 : Blo 1120629 4557341 := bstep (se 3 (by rfl) ⟨854501, by rfl⟩ : syracuseStep 4557341 = 1709003) B1709003
theorem B2525831 : Blo 1120629 2525831 := bstep (se 1 (by rfl) ⟨1894373, by rfl⟩ : syracuseStep 2525831 = 3788747) B3788747
theorem B2526011 : Blo 1120629 2526011 := bstep (se 1 (by rfl) ⟨1894508, by rfl⟩ : syracuseStep 2526011 = 3789017) B3789017
theorem B3640249 : Blo 1120629 3640249 := bstep (se 2 (by rfl) ⟨1365093, by rfl⟩ : syracuseStep 3640249 = 2730187) B2730187
theorem B2526137 : Blo 1120629 2526137 := bstep (se 2 (by rfl) ⟨947301, by rfl⟩ : syracuseStep 2526137 = 1894603) B1894603
theorem B3837185 : Blo 1120629 3837185 := bstep (se 2 (by rfl) ⟨1438944, by rfl⟩ : syracuseStep 3837185 = 2877889) B2877889
theorem B2526479 : Blo 1120629 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B2526497 : Blo 1120629 2526497 := bstep (se 2 (by rfl) ⟨947436, by rfl⟩ : syracuseStep 2526497 = 1894873) B1894873
theorem B6753689 : Blo 1120629 6753689 := bstep (se 2 (by rfl) ⟨2532633, by rfl⟩ : syracuseStep 6753689 = 5065267) B5065267
theorem B2133449 : Blo 1120629 2133449 := bstep (se 2 (by rfl) ⟨800043, by rfl⟩ : syracuseStep 2133449 = 1600087) B1600087
theorem B2526839 : Blo 1120629 2526839 := bstep (se 1 (by rfl) ⟨1895129, by rfl⟩ : syracuseStep 2526839 = 3790259) B3790259
theorem B2395919 : Blo 1120629 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B2527019 : Blo 1120629 2527019 := bstep (se 1 (by rfl) ⟨1895264, by rfl⟩ : syracuseStep 2527019 = 3790529) B3790529
theorem B2559929 : Blo 1120629 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B6393923 : Blo 1120629 6393923 := bstep (se 1 (by rfl) ⟨4795442, by rfl⟩ : syracuseStep 6393923 = 9590885) B9590885
theorem B24252533 : Blo 1120629 24252533 := bstep (se 5 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 24252533 = 2273675) B2273675
theorem B2527379 : Blo 1120629 2527379 := bstep (se 1 (by rfl) ⟨1895534, by rfl⟩ : syracuseStep 2527379 = 3791069) B3791069
theorem B2134163 : Blo 1120629 2134163 := bstep (se 1 (by rfl) ⟨1600622, by rfl⟩ : syracuseStep 2134163 = 3201245) B3201245
theorem B2134201 : Blo 1120629 2134201 := bstep (se 2 (by rfl) ⟨800325, by rfl⟩ : syracuseStep 2134201 = 1600651) B1600651
theorem B2527433 : Blo 1120629 2527433 := bstep (se 2 (by rfl) ⟨947787, by rfl⟩ : syracuseStep 2527433 = 1895575) B1895575
theorem B1347959 : Blo 1120629 1347959 := bstep (se 1 (by rfl) ⟨1010969, by rfl⟩ : syracuseStep 1347959 = 2021939) B2021939
theorem B5673401 : Blo 1120629 5673401 := bstep (se 2 (by rfl) ⟨2127525, by rfl⟩ : syracuseStep 5673401 = 4255051) B4255051
theorem B19468765 : Blo 1120629 19468765 := bstep (se 3 (by rfl) ⟨3650393, by rfl⟩ : syracuseStep 19468765 = 7300787) B7300787
theorem B1348267 : Blo 1120629 1348267 := bstep (se 1 (by rfl) ⟨1011200, by rfl⟩ : syracuseStep 1348267 = 2022401) B2022401
theorem B1348411 : Blo 1120629 1348411 := bstep (se 1 (by rfl) ⟨1011308, by rfl⟩ : syracuseStep 1348411 = 2022617) B2022617
theorem B1708919 : Blo 1120629 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B2528135 : Blo 1120629 2528135 := bstep (se 1 (by rfl) ⟨1896101, by rfl⟩ : syracuseStep 2528135 = 3792203) B3792203
theorem B8328089 : Blo 1120629 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B2528315 : Blo 1120629 2528315 := bstep (se 1 (by rfl) ⟨1896236, by rfl⟩ : syracuseStep 2528315 = 3792473) B3792473
theorem B2528441 : Blo 1120629 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B3413335 : Blo 1120629 3413335 := bstep (se 1 (by rfl) ⟨2560001, by rfl⟩ : syracuseStep 3413335 = 5120003) B5120003
theorem B4789651 : Blo 1120629 4789651 := bstep (se 1 (by rfl) ⟨3592238, by rfl⟩ : syracuseStep 4789651 = 7184477) B7184477
theorem B2528783 : Blo 1120629 2528783 := bstep (se 1 (by rfl) ⟨1896587, by rfl⟩ : syracuseStep 2528783 = 3793175) B3793175
theorem B2528801 : Blo 1120629 2528801 := bstep (se 2 (by rfl) ⟨948300, by rfl⟩ : syracuseStep 2528801 = 1896601) B1896601
theorem B7182017 : Blo 1120629 7182017 := bstep (se 2 (by rfl) ⟨2693256, by rfl⟩ : syracuseStep 7182017 = 5386513) B5386513
theorem B5674697 : Blo 1120629 5674697 := bstep (se 2 (by rfl) ⟨2128011, by rfl⟩ : syracuseStep 5674697 = 4256023) B4256023
theorem B4265729 : Blo 1120629 4265729 := bstep (se 2 (by rfl) ⟨1599648, by rfl⟩ : syracuseStep 4265729 = 3199297) B3199297
theorem B4265743 : Blo 1120629 4265743 := bstep (se 1 (by rfl) ⟨3199307, by rfl⟩ : syracuseStep 4265743 = 6398615) B6398615
theorem B2397995 : Blo 1120629 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B6395699 : Blo 1120629 6395699 := bstep (se 1 (by rfl) ⟨4796774, by rfl⟩ : syracuseStep 6395699 = 9593549) B9593549
theorem B2529143 : Blo 1120629 2529143 := bstep (se 1 (by rfl) ⟨1896857, by rfl⟩ : syracuseStep 2529143 = 3793715) B3793715
theorem B2529323 : Blo 1120629 2529323 := bstep (se 1 (by rfl) ⟨1896992, by rfl⟩ : syracuseStep 2529323 = 3793985) B3793985
theorem B1120647 : Blo 1120629 1120647 := bstep (se 1 (by rfl) ⟨840485, by rfl⟩ : syracuseStep 1120647 = 1680971) B1680971
theorem B1120655 : Blo 1120629 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B2529683 : Blo 1120629 2529683 := bstep (se 1 (by rfl) ⟨1897262, by rfl⟩ : syracuseStep 2529683 = 3794525) B3794525
theorem B1120699 : Blo 1120629 1120699 := bstep (se 1 (by rfl) ⟨840524, by rfl⟩ : syracuseStep 1120699 = 1681049) B1681049
theorem B2529737 : Blo 1120629 2529737 := bstep (se 2 (by rfl) ⟨948651, by rfl⟩ : syracuseStep 2529737 = 1897303) B1897303
theorem B1120775 : Blo 1120629 1120775 := bstep (se 1 (by rfl) ⟨840581, by rfl⟩ : syracuseStep 1120775 = 1681163) B1681163
theorem B1120783 : Blo 1120629 1120783 := bstep (se 1 (by rfl) ⟨840587, by rfl⟩ : syracuseStep 1120783 = 1681175) B1681175
theorem B1120827 : Blo 1120629 1120827 := bstep (se 1 (by rfl) ⟨840620, by rfl⟩ : syracuseStep 1120827 = 1681241) B1681241
theorem B1120903 : Blo 1120629 1120903 := bstep (se 1 (by rfl) ⟨840677, by rfl⟩ : syracuseStep 1120903 = 1681355) B1681355
theorem B1120911 : Blo 1120629 1120911 := bstep (se 1 (by rfl) ⟨840683, by rfl⟩ : syracuseStep 1120911 = 1681367) B1681367
theorem B1120955 : Blo 1120629 1120955 := bstep (se 1 (by rfl) ⟨840716, by rfl⟩ : syracuseStep 1120955 = 1681433) B1681433
theorem B21568193 : Blo 1120629 21568193 := bstep (se 2 (by rfl) ⟨8088072, by rfl⟩ : syracuseStep 21568193 = 16176145) B16176145
theorem B1121031 : Blo 1120629 1121031 := bstep (se 1 (by rfl) ⟨840773, by rfl⟩ : syracuseStep 1121031 = 1681547) B1681547
theorem B1121039 : Blo 1120629 1121039 := bstep (se 1 (by rfl) ⟨840779, by rfl⟩ : syracuseStep 1121039 = 1681559) B1681559
theorem B1121083 : Blo 1120629 1121083 := bstep (se 1 (by rfl) ⟨840812, by rfl⟩ : syracuseStep 1121083 = 1681625) B1681625
theorem B1121159 : Blo 1120629 1121159 := bstep (se 1 (by rfl) ⟨840869, by rfl⟩ : syracuseStep 1121159 = 1681739) B1681739
theorem B1121167 : Blo 1120629 1121167 := bstep (se 1 (by rfl) ⟨840875, by rfl⟩ : syracuseStep 1121167 = 1681751) B1681751
theorem B2694035 : Blo 1120629 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B2694073 : Blo 1120629 2694073 := bstep (se 2 (by rfl) ⟨1010277, by rfl⟩ : syracuseStep 2694073 = 2020555) B2020555
theorem B1383355 : Blo 1120629 1383355 := bstep (se 1 (by rfl) ⟨1037516, by rfl⟩ : syracuseStep 1383355 = 2075033) B2075033
theorem B1121211 : Blo 1120629 1121211 := bstep (se 1 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 1121211 = 1681817) B1681817
theorem B1121287 : Blo 1120629 1121287 := bstep (se 1 (by rfl) ⟨840965, by rfl⟩ : syracuseStep 1121287 = 1681931) B1681931
theorem B4791307 : Blo 1120629 4791307 := bstep (se 1 (by rfl) ⟨3593480, by rfl⟩ : syracuseStep 4791307 = 7186961) B7186961
theorem B4267019 : Blo 1120629 4267019 := bstep (se 1 (by rfl) ⟨3200264, by rfl⟩ : syracuseStep 4267019 = 6400529) B6400529
theorem B1121295 : Blo 1120629 1121295 := bstep (se 1 (by rfl) ⟨840971, by rfl⟩ : syracuseStep 1121295 = 1681943) B1681943
theorem B1121339 : Blo 1120629 1121339 := bstep (se 1 (by rfl) ⟨841004, by rfl⟩ : syracuseStep 1121339 = 1682009) B1682009
theorem B1121415 : Blo 1120629 1121415 := bstep (se 1 (by rfl) ⟨841061, by rfl⟩ : syracuseStep 1121415 = 1682123) B1682123
theorem B1121423 : Blo 1120629 1121423 := bstep (se 1 (by rfl) ⟨841067, by rfl⟩ : syracuseStep 1121423 = 1682135) B1682135
theorem B1121467 : Blo 1120629 1121467 := bstep (se 1 (by rfl) ⟨841100, by rfl⟩ : syracuseStep 1121467 = 1682201) B1682201
theorem B6397157 : Blo 1120629 6397157 := bstep (se 4 (by rfl) ⟨599733, by rfl⟩ : syracuseStep 6397157 = 1199467) B1199467
theorem B1121543 : Blo 1120629 1121543 := bstep (se 1 (by rfl) ⟨841157, by rfl⟩ : syracuseStep 1121543 = 1682315) B1682315
theorem B1121551 : Blo 1120629 1121551 := bstep (se 1 (by rfl) ⟨841163, by rfl⟩ : syracuseStep 1121551 = 1682327) B1682327
theorem B1121595 : Blo 1120629 1121595 := bstep (se 1 (by rfl) ⟨841196, by rfl⟩ : syracuseStep 1121595 = 1682393) B1682393
theorem B2694487 : Blo 1120629 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B1121671 : Blo 1120629 1121671 := bstep (se 1 (by rfl) ⟨841253, by rfl⟩ : syracuseStep 1121671 = 1682507) B1682507
theorem B1121679 : Blo 1120629 1121679 := bstep (se 1 (by rfl) ⟨841259, by rfl⟩ : syracuseStep 1121679 = 1682519) B1682519
theorem B2399635 : Blo 1120629 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B1121723 : Blo 1120629 1121723 := bstep (se 1 (by rfl) ⟨841292, by rfl⟩ : syracuseStep 1121723 = 1682585) B1682585
theorem B1973705 : Blo 1120629 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B1121799 : Blo 1120629 1121799 := bstep (se 1 (by rfl) ⟨841349, by rfl⟩ : syracuseStep 1121799 = 1682699) B1682699
theorem B1121807 : Blo 1120629 1121807 := bstep (se 1 (by rfl) ⟨841355, by rfl⟩ : syracuseStep 1121807 = 1682711) B1682711
theorem B1121851 : Blo 1120629 1121851 := bstep (se 1 (by rfl) ⟨841388, by rfl⟩ : syracuseStep 1121851 = 1682777) B1682777
theorem B12951107 : Blo 1120629 12951107 := bstep (se 1 (by rfl) ⟨9713330, by rfl⟩ : syracuseStep 12951107 = 19426661) B19426661
theorem B1121927 : Blo 1120629 1121927 := bstep (se 1 (by rfl) ⟨841445, by rfl⟩ : syracuseStep 1121927 = 1682891) B1682891
theorem B1121935 : Blo 1120629 1121935 := bstep (se 1 (by rfl) ⟨841451, by rfl⟩ : syracuseStep 1121935 = 1682903) B1682903
theorem B6397613 : Blo 1120629 6397613 := bstep (se 3 (by rfl) ⟨1199552, by rfl⟩ : syracuseStep 6397613 = 2399105) B2399105
theorem B1121979 : Blo 1120629 1121979 := bstep (se 1 (by rfl) ⟨841484, by rfl⟩ : syracuseStep 1121979 = 1682969) B1682969
theorem B1122055 : Blo 1120629 1122055 := bstep (se 1 (by rfl) ⟨841541, by rfl⟩ : syracuseStep 1122055 = 1683083) B1683083
theorem B1122063 : Blo 1120629 1122063 := bstep (se 1 (by rfl) ⟨841547, by rfl⟩ : syracuseStep 1122063 = 1683095) B1683095
theorem B1122107 : Blo 1120629 1122107 := bstep (se 1 (by rfl) ⟨841580, by rfl⟩ : syracuseStep 1122107 = 1683161) B1683161
theorem B1122183 : Blo 1120629 1122183 := bstep (se 1 (by rfl) ⟨841637, by rfl⟩ : syracuseStep 1122183 = 1683275) B1683275
theorem B1122191 : Blo 1120629 1122191 := bstep (se 1 (by rfl) ⟨841643, by rfl⟩ : syracuseStep 1122191 = 1683287) B1683287
theorem B4267961 : Blo 1120629 4267961 := bstep (se 2 (by rfl) ⟨1600485, by rfl⟩ : syracuseStep 4267961 = 3200971) B3200971
theorem B1122235 : Blo 1120629 1122235 := bstep (se 1 (by rfl) ⟨841676, by rfl⟩ : syracuseStep 1122235 = 1683353) B1683353
theorem B1122311 : Blo 1120629 1122311 := bstep (se 1 (by rfl) ⟨841733, by rfl⟩ : syracuseStep 1122311 = 1683467) B1683467
theorem B1122319 : Blo 1120629 1122319 := bstep (se 1 (by rfl) ⟨841739, by rfl⟩ : syracuseStep 1122319 = 1683479) B1683479
theorem B6070315 : Blo 1120629 6070315 := bstep (se 1 (by rfl) ⟨4552736, by rfl⟩ : syracuseStep 6070315 = 9105473) B9105473
theorem B1122363 : Blo 1120629 1122363 := bstep (se 1 (by rfl) ⟨841772, by rfl⟩ : syracuseStep 1122363 = 1683545) B1683545
theorem B2695303 : Blo 1120629 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B1122439 : Blo 1120629 1122439 := bstep (se 1 (by rfl) ⟨841829, by rfl⟩ : syracuseStep 1122439 = 1683659) B1683659
theorem B1122447 : Blo 1120629 1122447 := bstep (se 1 (by rfl) ⟨841835, by rfl⟩ : syracuseStep 1122447 = 1683671) B1683671
theorem B24256685 : Blo 1120629 24256685 := bstep (se 3 (by rfl) ⟨4548128, by rfl⟩ : syracuseStep 24256685 = 9096257) B9096257
theorem B1122491 : Blo 1120629 1122491 := bstep (se 1 (by rfl) ⟨841868, by rfl⟩ : syracuseStep 1122491 = 1683737) B1683737
theorem B1122567 : Blo 1120629 1122567 := bstep (se 1 (by rfl) ⟨841925, by rfl⟩ : syracuseStep 1122567 = 1683851) B1683851
theorem B1122575 : Blo 1120629 1122575 := bstep (se 1 (by rfl) ⟨841931, by rfl⟩ : syracuseStep 1122575 = 1683863) B1683863
theorem B9576737 : Blo 1120629 9576737 := bstep (se 2 (by rfl) ⟨3591276, by rfl⟩ : syracuseStep 9576737 = 7182553) B7182553
theorem B2695457 : Blo 1120629 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B1122619 : Blo 1120629 1122619 := bstep (se 1 (by rfl) ⟨841964, by rfl⟩ : syracuseStep 1122619 = 1683929) B1683929
theorem B6398297 : Blo 1120629 6398297 := bstep (se 2 (by rfl) ⟨2399361, by rfl⟩ : syracuseStep 6398297 = 4798723) B4798723
theorem B1122695 : Blo 1120629 1122695 := bstep (se 1 (by rfl) ⟨842021, by rfl⟩ : syracuseStep 1122695 = 1684043) B1684043
theorem B1122703 : Blo 1120629 1122703 := bstep (se 1 (by rfl) ⟨842027, by rfl⟩ : syracuseStep 1122703 = 1684055) B1684055
theorem B1122747 : Blo 1120629 1122747 := bstep (se 1 (by rfl) ⟨842060, by rfl⟩ : syracuseStep 1122747 = 1684121) B1684121
theorem B1122823 : Blo 1120629 1122823 := bstep (se 1 (by rfl) ⟨842117, by rfl⟩ : syracuseStep 1122823 = 1684235) B1684235
theorem B1122831 : Blo 1120629 1122831 := bstep (se 1 (by rfl) ⟨842123, by rfl⟩ : syracuseStep 1122831 = 1684247) B1684247
theorem B1122875 : Blo 1120629 1122875 := bstep (se 1 (by rfl) ⟨842156, by rfl⟩ : syracuseStep 1122875 = 1684313) B1684313
theorem B12132929 : Blo 1120629 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B7184963 : Blo 1120629 7184963 := bstep (se 1 (by rfl) ⟨5388722, by rfl⟩ : syracuseStep 7184963 = 10777445) B10777445
theorem B8987213 : Blo 1120629 8987213 := bstep (se 3 (by rfl) ⟨1685102, by rfl⟩ : syracuseStep 8987213 = 3370205) B3370205
theorem B1122951 : Blo 1120629 1122951 := bstep (se 1 (by rfl) ⟨842213, by rfl⟩ : syracuseStep 1122951 = 1684427) B1684427
theorem B1122959 : Blo 1120629 1122959 := bstep (se 1 (by rfl) ⟨842219, by rfl⟩ : syracuseStep 1122959 = 1684439) B1684439
theorem B1123003 : Blo 1120629 1123003 := bstep (se 1 (by rfl) ⟨842252, by rfl⟩ : syracuseStep 1123003 = 1684505) B1684505
theorem B1123079 : Blo 1120629 1123079 := bstep (se 1 (by rfl) ⟨842309, by rfl⟩ : syracuseStep 1123079 = 1684619) B1684619
theorem B1123087 : Blo 1120629 1123087 := bstep (se 1 (by rfl) ⟨842315, by rfl⟩ : syracuseStep 1123087 = 1684631) B1684631
theorem B1123131 : Blo 1120629 1123131 := bstep (se 1 (by rfl) ⟨842348, by rfl⟩ : syracuseStep 1123131 = 1684697) B1684697
theorem B1123207 : Blo 1120629 1123207 := bstep (se 1 (by rfl) ⟨842405, by rfl⟩ : syracuseStep 1123207 = 1684811) B1684811
theorem B1123215 : Blo 1120629 1123215 := bstep (se 1 (by rfl) ⟨842411, by rfl⟩ : syracuseStep 1123215 = 1684823) B1684823
theorem B1123259 : Blo 1120629 1123259 := bstep (se 1 (by rfl) ⟨842444, by rfl⟩ : syracuseStep 1123259 = 1684889) B1684889
theorem B1123335 : Blo 1120629 1123335 := bstep (se 1 (by rfl) ⟨842501, by rfl⟩ : syracuseStep 1123335 = 1685003) B1685003
theorem B1123343 : Blo 1120629 1123343 := bstep (se 1 (by rfl) ⟨842507, by rfl⟩ : syracuseStep 1123343 = 1685015) B1685015
theorem B1516601 : Blo 1120629 1516601 := bstep (se 2 (by rfl) ⟨568725, by rfl⟩ : syracuseStep 1516601 = 1137451) B1137451
theorem B1123387 : Blo 1120629 1123387 := bstep (se 1 (by rfl) ⟨842540, by rfl⟩ : syracuseStep 1123387 = 1685081) B1685081
theorem B1123463 : Blo 1120629 1123463 := bstep (se 1 (by rfl) ⟨842597, by rfl⟩ : syracuseStep 1123463 = 1685195) B1685195
theorem B1123471 : Blo 1120629 1123471 := bstep (se 1 (by rfl) ⟨842603, by rfl⟩ : syracuseStep 1123471 = 1685207) B1685207
theorem B1418411 : Blo 1120629 1418411 := bstep (se 1 (by rfl) ⟨1063808, by rfl⟩ : syracuseStep 1418411 = 2127617) B2127617
theorem B1123515 : Blo 1120629 1123515 := bstep (se 1 (by rfl) ⟨842636, by rfl⟩ : syracuseStep 1123515 = 1685273) B1685273
theorem B2401481 : Blo 1120629 2401481 := bstep (se 2 (by rfl) ⟨900555, by rfl⟩ : syracuseStep 2401481 = 1801111) B1801111
theorem B1123591 : Blo 1120629 1123591 := bstep (se 1 (by rfl) ⟨842693, by rfl⟩ : syracuseStep 1123591 = 1685387) B1685387
theorem B1123599 : Blo 1120629 1123599 := bstep (se 1 (by rfl) ⟨842699, by rfl⟩ : syracuseStep 1123599 = 1685399) B1685399
theorem B11085115 : Blo 1120629 11085115 := bstep (se 1 (by rfl) ⟨8313836, by rfl⟩ : syracuseStep 11085115 = 16627673) B16627673
theorem B1123643 : Blo 1120629 1123643 := bstep (se 1 (by rfl) ⟨842732, by rfl⟩ : syracuseStep 1123643 = 1685465) B1685465
theorem B1123719 : Blo 1120629 1123719 := bstep (se 1 (by rfl) ⟨842789, by rfl⟩ : syracuseStep 1123719 = 1685579) B1685579
theorem B1123727 : Blo 1120629 1123727 := bstep (se 1 (by rfl) ⟨842795, by rfl⟩ : syracuseStep 1123727 = 1685591) B1685591
theorem B8529299 : Blo 1120629 8529299 := bstep (se 1 (by rfl) ⟨6396974, by rfl⟩ : syracuseStep 8529299 = 12793949) B12793949
theorem B1123771 : Blo 1120629 1123771 := bstep (se 1 (by rfl) ⟨842828, by rfl⟩ : syracuseStep 1123771 = 1685657) B1685657
theorem B1123847 : Blo 1120629 1123847 := bstep (se 1 (by rfl) ⟨842885, by rfl⟩ : syracuseStep 1123847 = 1685771) B1685771
theorem B1123855 : Blo 1120629 1123855 := bstep (se 1 (by rfl) ⟨842891, by rfl⟩ : syracuseStep 1123855 = 1685783) B1685783
theorem B6071831 : Blo 1120629 6071831 := bstep (se 1 (by rfl) ⟨4553873, by rfl⟩ : syracuseStep 6071831 = 9107747) B9107747
theorem B1680953 : Blo 1120629 1680953 := bstep (se 2 (by rfl) ⟨630357, by rfl⟩ : syracuseStep 1680953 = 1260715) B1260715
theorem B1123899 : Blo 1120629 1123899 := bstep (se 1 (by rfl) ⟨842924, by rfl⟩ : syracuseStep 1123899 = 1685849) B1685849
theorem B1681031 : Blo 1120629 1681031 := bstep (se 1 (by rfl) ⟨1260773, by rfl⟩ : syracuseStep 1681031 = 2521547) B2521547
theorem B1418887 : Blo 1120629 1418887 := bstep (se 1 (by rfl) ⟨1064165, by rfl⟩ : syracuseStep 1418887 = 2128331) B2128331
theorem B1123975 : Blo 1120629 1123975 := bstep (se 1 (by rfl) ⟨842981, by rfl⟩ : syracuseStep 1123975 = 1685963) B1685963
theorem B1123983 : Blo 1120629 1123983 := bstep (se 1 (by rfl) ⟨842987, by rfl⟩ : syracuseStep 1123983 = 1685975) B1685975
theorem B1681067 : Blo 1120629 1681067 := bstep (se 1 (by rfl) ⟨1260800, by rfl⟩ : syracuseStep 1681067 = 2521601) B2521601
theorem B1124027 : Blo 1120629 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B1681097 : Blo 1120629 1681097 := bstep (se 2 (by rfl) ⟨630411, by rfl⟩ : syracuseStep 1681097 = 1260823) B1260823
theorem B1124103 : Blo 1120629 1124103 := bstep (se 1 (by rfl) ⟨843077, by rfl⟩ : syracuseStep 1124103 = 1686155) B1686155
theorem B1124111 : Blo 1120629 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B1681211 : Blo 1120629 1681211 := bstep (se 1 (by rfl) ⟨1260908, by rfl⟩ : syracuseStep 1681211 = 2521817) B2521817
theorem B1124155 : Blo 1120629 1124155 := bstep (se 1 (by rfl) ⟨843116, by rfl⟩ : syracuseStep 1124155 = 1686233) B1686233
theorem B1681271 : Blo 1120629 1681271 := bstep (se 1 (by rfl) ⟨1260953, by rfl⟩ : syracuseStep 1681271 = 2521907) B2521907
theorem B1124231 : Blo 1120629 1124231 := bstep (se 1 (by rfl) ⟨843173, by rfl⟩ : syracuseStep 1124231 = 1686347) B1686347
theorem B1681295 : Blo 1120629 1681295 := bstep (se 1 (by rfl) ⟨1260971, by rfl⟩ : syracuseStep 1681295 = 2521943) B2521943
theorem B1124239 : Blo 1120629 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B1681337 : Blo 1120629 1681337 := bstep (se 2 (by rfl) ⟨630501, by rfl⟩ : syracuseStep 1681337 = 1261003) B1261003
theorem B1124283 : Blo 1120629 1124283 := bstep (se 1 (by rfl) ⟨843212, by rfl⟩ : syracuseStep 1124283 = 1686425) B1686425
theorem B1681415 : Blo 1120629 1681415 := bstep (se 1 (by rfl) ⟨1261061, by rfl⟩ : syracuseStep 1681415 = 2522123) B2522123
theorem B1124359 : Blo 1120629 1124359 := bstep (se 1 (by rfl) ⟨843269, by rfl⟩ : syracuseStep 1124359 = 1686539) B1686539
theorem B1124367 : Blo 1120629 1124367 := bstep (se 1 (by rfl) ⟨843275, by rfl⟩ : syracuseStep 1124367 = 1686551) B1686551
theorem B1681451 : Blo 1120629 1681451 := bstep (se 1 (by rfl) ⟨1261088, by rfl⟩ : syracuseStep 1681451 = 2522177) B2522177
theorem B1124411 : Blo 1120629 1124411 := bstep (se 1 (by rfl) ⟨843308, by rfl⟩ : syracuseStep 1124411 = 1686617) B1686617
theorem B1681481 : Blo 1120629 1681481 := bstep (se 2 (by rfl) ⟨630555, by rfl⟩ : syracuseStep 1681481 = 1261111) B1261111
theorem B1419383 : Blo 1120629 1419383 := bstep (se 1 (by rfl) ⟨1064537, by rfl⟩ : syracuseStep 1419383 = 2129075) B2129075
theorem B1124487 : Blo 1120629 1124487 := bstep (se 1 (by rfl) ⟨843365, by rfl⟩ : syracuseStep 1124487 = 1686731) B1686731
theorem B1124495 : Blo 1120629 1124495 := bstep (se 1 (by rfl) ⟨843371, by rfl⟩ : syracuseStep 1124495 = 1686743) B1686743
theorem B1681595 : Blo 1120629 1681595 := bstep (se 1 (by rfl) ⟨1261196, by rfl⟩ : syracuseStep 1681595 = 2522393) B2522393
theorem B1124539 : Blo 1120629 1124539 := bstep (se 1 (by rfl) ⟨843404, by rfl⟩ : syracuseStep 1124539 = 1686809) B1686809
theorem B21604553 : Blo 1120629 21604553 := bstep (se 2 (by rfl) ⟨8101707, by rfl⟩ : syracuseStep 21604553 = 16203415) B16203415
theorem B1681655 : Blo 1120629 1681655 := bstep (se 1 (by rfl) ⟨1261241, by rfl⟩ : syracuseStep 1681655 = 2522483) B2522483
theorem B1124615 : Blo 1120629 1124615 := bstep (se 1 (by rfl) ⟨843461, by rfl⟩ : syracuseStep 1124615 = 1686923) B1686923
theorem B1681679 : Blo 1120629 1681679 := bstep (se 1 (by rfl) ⟨1261259, by rfl⟩ : syracuseStep 1681679 = 2522519) B2522519
theorem B1419535 : Blo 1120629 1419535 := bstep (se 1 (by rfl) ⟨1064651, by rfl⟩ : syracuseStep 1419535 = 2129303) B2129303
theorem B1124623 : Blo 1120629 1124623 := bstep (se 1 (by rfl) ⟨843467, by rfl⟩ : syracuseStep 1124623 = 1686935) B1686935
theorem B1681721 : Blo 1120629 1681721 := bstep (se 2 (by rfl) ⟨630645, by rfl⟩ : syracuseStep 1681721 = 1261291) B1261291
theorem B1681799 : Blo 1120629 1681799 := bstep (se 1 (by rfl) ⟨1261349, by rfl⟩ : syracuseStep 1681799 = 2522699) B2522699
theorem B1681835 : Blo 1120629 1681835 := bstep (se 1 (by rfl) ⟨1261376, by rfl⟩ : syracuseStep 1681835 = 2522753) B2522753
theorem B1419707 : Blo 1120629 1419707 := bstep (se 1 (by rfl) ⟨1064780, by rfl⟩ : syracuseStep 1419707 = 2129561) B2129561
theorem B1681865 : Blo 1120629 1681865 := bstep (se 2 (by rfl) ⟨630699, by rfl⟩ : syracuseStep 1681865 = 1261399) B1261399
theorem B1681979 : Blo 1120629 1681979 := bstep (se 1 (by rfl) ⟨1261484, by rfl⟩ : syracuseStep 1681979 = 2522969) B2522969
theorem B1682039 : Blo 1120629 1682039 := bstep (se 1 (by rfl) ⟨1261529, by rfl⟩ : syracuseStep 1682039 = 2523059) B2523059
theorem B1682063 : Blo 1120629 1682063 := bstep (se 1 (by rfl) ⟨1261547, by rfl⟩ : syracuseStep 1682063 = 2523095) B2523095
theorem B1682105 : Blo 1120629 1682105 := bstep (se 2 (by rfl) ⟨630789, by rfl⟩ : syracuseStep 1682105 = 1261579) B1261579
theorem B1682183 : Blo 1120629 1682183 := bstep (se 1 (by rfl) ⟨1261637, by rfl⟩ : syracuseStep 1682183 = 2523275) B2523275
theorem B1682219 : Blo 1120629 1682219 := bstep (se 1 (by rfl) ⟨1261664, by rfl⟩ : syracuseStep 1682219 = 2523329) B2523329
theorem B1682249 : Blo 1120629 1682249 := bstep (se 2 (by rfl) ⟨630843, by rfl⟩ : syracuseStep 1682249 = 1261687) B1261687
theorem B66497381 : Blo 1120629 66497381 := bstep (se 4 (by rfl) ⟨6234129, by rfl⟩ : syracuseStep 66497381 = 12468259) B12468259
theorem B4795271 : Blo 1120629 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B1682363 : Blo 1120629 1682363 := bstep (se 1 (by rfl) ⟨1261772, by rfl⟩ : syracuseStep 1682363 = 2523545) B2523545
theorem B1682423 : Blo 1120629 1682423 := bstep (se 1 (by rfl) ⟨1261817, by rfl⟩ : syracuseStep 1682423 = 2523635) B2523635
theorem B1682447 : Blo 1120629 1682447 := bstep (se 1 (by rfl) ⟨1261835, by rfl⟩ : syracuseStep 1682447 = 2523671) B2523671
theorem B1682489 : Blo 1120629 1682489 := bstep (se 2 (by rfl) ⟨630933, by rfl⟩ : syracuseStep 1682489 = 1261867) B1261867
theorem B1682567 : Blo 1120629 1682567 := bstep (se 1 (by rfl) ⟨1261925, by rfl⟩ : syracuseStep 1682567 = 2523851) B2523851
theorem B1682603 : Blo 1120629 1682603 := bstep (se 1 (by rfl) ⟨1261952, by rfl⟩ : syracuseStep 1682603 = 2523905) B2523905
theorem B1682633 : Blo 1120629 1682633 := bstep (se 2 (by rfl) ⟨630987, by rfl⟩ : syracuseStep 1682633 = 1261975) B1261975
theorem B4795681 : Blo 1120629 4795681 := bstep (se 2 (by rfl) ⟨1798380, by rfl⟩ : syracuseStep 4795681 = 3596761) B3596761
theorem B1682747 : Blo 1120629 1682747 := bstep (se 1 (by rfl) ⟨1262060, by rfl⟩ : syracuseStep 1682747 = 2524121) B2524121
theorem B1682807 : Blo 1120629 1682807 := bstep (se 1 (by rfl) ⟨1262105, by rfl⟩ : syracuseStep 1682807 = 2524211) B2524211
theorem B1420679 : Blo 1120629 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B1682831 : Blo 1120629 1682831 := bstep (se 1 (by rfl) ⟨1262123, by rfl⟩ : syracuseStep 1682831 = 2524247) B2524247
theorem B5680529 : Blo 1120629 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B1682873 : Blo 1120629 1682873 := bstep (se 2 (by rfl) ⟨631077, by rfl⟩ : syracuseStep 1682873 = 1262155) B1262155
theorem B93466061 : Blo 1120629 93466061 := bstep (se 3 (by rfl) ⟨17524886, by rfl⟩ : syracuseStep 93466061 = 35049773) B35049773
theorem B1682951 : Blo 1120629 1682951 := bstep (se 1 (by rfl) ⟨1262213, by rfl⟩ : syracuseStep 1682951 = 2524427) B2524427
theorem B1682987 : Blo 1120629 1682987 := bstep (se 1 (by rfl) ⟨1262240, by rfl⟩ : syracuseStep 1682987 = 2524481) B2524481
theorem B1683017 : Blo 1120629 1683017 := bstep (se 2 (by rfl) ⟨631131, by rfl⟩ : syracuseStep 1683017 = 1262263) B1262263
theorem B4796023 : Blo 1120629 4796023 := bstep (se 1 (by rfl) ⟨3597017, by rfl⟩ : syracuseStep 4796023 = 7194035) B7194035
theorem B1683131 : Blo 1120629 1683131 := bstep (se 1 (by rfl) ⟨1262348, by rfl⟩ : syracuseStep 1683131 = 2524697) B2524697
theorem B1683191 : Blo 1120629 1683191 := bstep (se 1 (by rfl) ⟨1262393, by rfl⟩ : syracuseStep 1683191 = 2524787) B2524787
theorem B1683215 : Blo 1120629 1683215 := bstep (se 1 (by rfl) ⟨1262411, by rfl⟩ : syracuseStep 1683215 = 2524823) B2524823
theorem B1683257 : Blo 1120629 1683257 := bstep (se 2 (by rfl) ⟨631221, by rfl⟩ : syracuseStep 1683257 = 1262443) B1262443
theorem B1683335 : Blo 1120629 1683335 := bstep (se 1 (by rfl) ⟨1262501, by rfl⟩ : syracuseStep 1683335 = 2525003) B2525003
theorem B1683371 : Blo 1120629 1683371 := bstep (se 1 (by rfl) ⟨1262528, by rfl⟩ : syracuseStep 1683371 = 2525057) B2525057
theorem B1683401 : Blo 1120629 1683401 := bstep (se 2 (by rfl) ⟨631275, by rfl⟩ : syracuseStep 1683401 = 1262551) B1262551
theorem B1421327 : Blo 1120629 1421327 := bstep (se 1 (by rfl) ⟨1065995, by rfl⟩ : syracuseStep 1421327 = 2131991) B2131991
theorem B1683515 : Blo 1120629 1683515 := bstep (se 1 (by rfl) ⟨1262636, by rfl⟩ : syracuseStep 1683515 = 2525273) B2525273
theorem B5386301 : Blo 1120629 5386301 := bstep (se 3 (by rfl) ⟨1009931, by rfl⟩ : syracuseStep 5386301 = 2019863) B2019863
theorem B1683575 : Blo 1120629 1683575 := bstep (se 1 (by rfl) ⟨1262681, by rfl⟩ : syracuseStep 1683575 = 2525363) B2525363
theorem B1683599 : Blo 1120629 1683599 := bstep (se 1 (by rfl) ⟨1262699, by rfl⟩ : syracuseStep 1683599 = 2525399) B2525399
theorem B1683641 : Blo 1120629 1683641 := bstep (se 2 (by rfl) ⟨631365, by rfl⟩ : syracuseStep 1683641 = 1262731) B1262731
theorem B1519817 : Blo 1120629 1519817 := bstep (se 2 (by rfl) ⟨569931, by rfl⟩ : syracuseStep 1519817 = 1139863) B1139863
theorem B1683719 : Blo 1120629 1683719 := bstep (se 1 (by rfl) ⟨1262789, by rfl⟩ : syracuseStep 1683719 = 2525579) B2525579
theorem B1683755 : Blo 1120629 1683755 := bstep (se 1 (by rfl) ⟨1262816, by rfl⟩ : syracuseStep 1683755 = 2525633) B2525633
theorem B1519931 : Blo 1120629 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B1683785 : Blo 1120629 1683785 := bstep (se 2 (by rfl) ⟨631419, by rfl⟩ : syracuseStep 1683785 = 1262839) B1262839
theorem B2699639 : Blo 1120629 2699639 := bstep (se 1 (by rfl) ⟨2024729, by rfl⟩ : syracuseStep 2699639 = 4049459) B4049459
theorem B1683899 : Blo 1120629 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B1683959 : Blo 1120629 1683959 := bstep (se 1 (by rfl) ⟨1262969, by rfl⟩ : syracuseStep 1683959 = 2525939) B2525939
theorem B5386763 : Blo 1120629 5386763 := bstep (se 1 (by rfl) ⟨4040072, by rfl⟩ : syracuseStep 5386763 = 8080145) B8080145
theorem B1683983 : Blo 1120629 1683983 := bstep (se 1 (by rfl) ⟨1262987, by rfl⟩ : syracuseStep 1683983 = 2525975) B2525975
theorem B1684025 : Blo 1120629 1684025 := bstep (se 2 (by rfl) ⟨631509, by rfl⟩ : syracuseStep 1684025 = 1263019) B1263019
theorem B1684103 : Blo 1120629 1684103 := bstep (se 1 (by rfl) ⟨1263077, by rfl⟩ : syracuseStep 1684103 = 2526155) B2526155
theorem B1684139 : Blo 1120629 1684139 := bstep (se 1 (by rfl) ⟨1263104, by rfl⟩ : syracuseStep 1684139 = 2526209) B2526209
theorem B10793665 : Blo 1120629 10793665 := bstep (se 2 (by rfl) ⟨4047624, by rfl⟩ : syracuseStep 10793665 = 8095249) B8095249
theorem B1684169 : Blo 1120629 1684169 := bstep (se 2 (by rfl) ⟨631563, by rfl⟩ : syracuseStep 1684169 = 1263127) B1263127
theorem B1684283 : Blo 1120629 1684283 := bstep (se 1 (by rfl) ⟨1263212, by rfl⟩ : syracuseStep 1684283 = 2526425) B2526425
theorem B1684343 : Blo 1120629 1684343 := bstep (se 1 (by rfl) ⟨1263257, by rfl⟩ : syracuseStep 1684343 = 2526515) B2526515
theorem B1684367 : Blo 1120629 1684367 := bstep (se 1 (by rfl) ⟨1263275, by rfl⟩ : syracuseStep 1684367 = 2526551) B2526551
theorem B3191699 : Blo 1120629 3191699 := bstep (se 1 (by rfl) ⟨2393774, by rfl⟩ : syracuseStep 3191699 = 4787549) B4787549
theorem B1684409 : Blo 1120629 1684409 := bstep (se 2 (by rfl) ⟨631653, by rfl⟩ : syracuseStep 1684409 = 1263307) B1263307
theorem B1684487 : Blo 1120629 1684487 := bstep (se 1 (by rfl) ⟨1263365, by rfl⟩ : syracuseStep 1684487 = 2526731) B2526731
theorem B1684523 : Blo 1120629 1684523 := bstep (se 1 (by rfl) ⟨1263392, by rfl⟩ : syracuseStep 1684523 = 2526785) B2526785
theorem B1684553 : Blo 1120629 1684553 := bstep (se 2 (by rfl) ⟨631707, by rfl⟩ : syracuseStep 1684553 = 1263415) B1263415
theorem B2733209 : Blo 1120629 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B1684667 : Blo 1120629 1684667 := bstep (se 1 (by rfl) ⟨1263500, by rfl⟩ : syracuseStep 1684667 = 2527001) B2527001
theorem B1684727 : Blo 1120629 1684727 := bstep (se 1 (by rfl) ⟨1263545, by rfl⟩ : syracuseStep 1684727 = 2527091) B2527091
theorem B1684751 : Blo 1120629 1684751 := bstep (se 1 (by rfl) ⟨1263563, by rfl⟩ : syracuseStep 1684751 = 2527127) B2527127
theorem B18232609 : Blo 1120629 18232609 := bstep (se 2 (by rfl) ⟨6837228, by rfl⟩ : syracuseStep 18232609 = 13674457) B13674457
theorem B1684793 : Blo 1120629 1684793 := bstep (se 2 (by rfl) ⟨631797, by rfl⟩ : syracuseStep 1684793 = 1263595) B1263595
theorem B4044167 : Blo 1120629 4044167 := bstep (se 1 (by rfl) ⟨3033125, by rfl⟩ : syracuseStep 4044167 = 6066251) B6066251
theorem B1684871 : Blo 1120629 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B1684907 : Blo 1120629 1684907 := bstep (se 1 (by rfl) ⟨1263680, by rfl⟩ : syracuseStep 1684907 = 2527361) B2527361
theorem B1684937 : Blo 1120629 1684937 := bstep (se 2 (by rfl) ⟨631851, by rfl⟩ : syracuseStep 1684937 = 1263703) B1263703
theorem B5682635 : Blo 1120629 5682635 := bstep (se 1 (by rfl) ⟨4261976, by rfl⟩ : syracuseStep 5682635 = 8523953) B8523953
theorem B1685051 : Blo 1120629 1685051 := bstep (se 1 (by rfl) ⟨1263788, by rfl⟩ : syracuseStep 1685051 = 2527577) B2527577
theorem B1685111 : Blo 1120629 1685111 := bstep (se 1 (by rfl) ⟨1263833, by rfl⟩ : syracuseStep 1685111 = 2527667) B2527667
theorem B1685135 : Blo 1120629 1685135 := bstep (se 1 (by rfl) ⟨1263851, by rfl⟩ : syracuseStep 1685135 = 2527703) B2527703
theorem B3192473 : Blo 1120629 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B1685177 : Blo 1120629 1685177 := bstep (se 2 (by rfl) ⟨631941, by rfl⟩ : syracuseStep 1685177 = 1263883) B1263883
theorem B1685255 : Blo 1120629 1685255 := bstep (se 1 (by rfl) ⟨1263941, by rfl⟩ : syracuseStep 1685255 = 2527883) B2527883
theorem B5682959 : Blo 1120629 5682959 := bstep (se 1 (by rfl) ⟨4262219, by rfl⟩ : syracuseStep 5682959 = 8524439) B8524439
theorem B1685291 : Blo 1120629 1685291 := bstep (se 1 (by rfl) ⟨1263968, by rfl⟩ : syracuseStep 1685291 = 2527937) B2527937
theorem B1685321 : Blo 1120629 1685321 := bstep (se 2 (by rfl) ⟨631995, by rfl⟩ : syracuseStep 1685321 = 1263991) B1263991
theorem B1685435 : Blo 1120629 1685435 := bstep (se 1 (by rfl) ⟨1264076, by rfl⟩ : syracuseStep 1685435 = 2528153) B2528153
theorem B1685495 : Blo 1120629 1685495 := bstep (se 1 (by rfl) ⟨1264121, by rfl⟩ : syracuseStep 1685495 = 2528243) B2528243
theorem B1685519 : Blo 1120629 1685519 := bstep (se 1 (by rfl) ⟨1264139, by rfl⟩ : syracuseStep 1685519 = 2528279) B2528279
theorem B3782699 : Blo 1120629 3782699 := bstep (se 1 (by rfl) ⟨2837024, by rfl⟩ : syracuseStep 3782699 = 5674049) B5674049
theorem B1685561 : Blo 1120629 1685561 := bstep (se 2 (by rfl) ⟨632085, by rfl⟩ : syracuseStep 1685561 = 1264171) B1264171
theorem B1685639 : Blo 1120629 1685639 := bstep (se 1 (by rfl) ⟨1264229, by rfl⟩ : syracuseStep 1685639 = 2528459) B2528459
theorem B1685675 : Blo 1120629 1685675 := bstep (se 1 (by rfl) ⟨1264256, by rfl⟩ : syracuseStep 1685675 = 2528513) B2528513
theorem B1685705 : Blo 1120629 1685705 := bstep (se 2 (by rfl) ⟨632139, by rfl⟩ : syracuseStep 1685705 = 1264279) B1264279
theorem B6830351 : Blo 1120629 6830351 := bstep (se 1 (by rfl) ⟨5122763, by rfl⟩ : syracuseStep 6830351 = 10245527) B10245527
theorem B1685819 : Blo 1120629 1685819 := bstep (se 1 (by rfl) ⟨1264364, by rfl⟩ : syracuseStep 1685819 = 2528729) B2528729
theorem B1685879 : Blo 1120629 1685879 := bstep (se 1 (by rfl) ⟨1264409, by rfl⟩ : syracuseStep 1685879 = 2528819) B2528819
theorem B1685903 : Blo 1120629 1685903 := bstep (se 1 (by rfl) ⟨1264427, by rfl⟩ : syracuseStep 1685903 = 2528855) B2528855
theorem B1685945 : Blo 1120629 1685945 := bstep (se 2 (by rfl) ⟨632229, by rfl⟩ : syracuseStep 1685945 = 1264459) B1264459
theorem B12958157 : Blo 1120629 12958157 := bstep (se 3 (by rfl) ⟨2429654, by rfl⟩ : syracuseStep 12958157 = 4859309) B4859309
theorem B1686023 : Blo 1120629 1686023 := bstep (se 1 (by rfl) ⟨1264517, by rfl⟩ : syracuseStep 1686023 = 2529035) B2529035
theorem B1686059 : Blo 1120629 1686059 := bstep (se 1 (by rfl) ⟨1264544, by rfl⟩ : syracuseStep 1686059 = 2529089) B2529089
theorem B1686089 : Blo 1120629 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B2767495 : Blo 1120629 2767495 := bstep (se 1 (by rfl) ⟨2075621, by rfl⟩ : syracuseStep 2767495 = 4151243) B4151243
theorem B1686203 : Blo 1120629 1686203 := bstep (se 1 (by rfl) ⟨1264652, by rfl⟩ : syracuseStep 1686203 = 2529305) B2529305
theorem B1686263 : Blo 1120629 1686263 := bstep (se 1 (by rfl) ⟨1264697, by rfl⟩ : syracuseStep 1686263 = 2529395) B2529395
theorem B1686287 : Blo 1120629 1686287 := bstep (se 1 (by rfl) ⟨1264715, by rfl⟩ : syracuseStep 1686287 = 2529431) B2529431
theorem B1686329 : Blo 1120629 1686329 := bstep (se 2 (by rfl) ⟨632373, by rfl⟩ : syracuseStep 1686329 = 1264747) B1264747
theorem B5389145 : Blo 1120629 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B1686407 : Blo 1120629 1686407 := bstep (se 1 (by rfl) ⟨1264805, by rfl⟩ : syracuseStep 1686407 = 2529611) B2529611
theorem B12139415 : Blo 1120629 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B7191449 : Blo 1120629 7191449 := bstep (se 2 (by rfl) ⟨2696793, by rfl⟩ : syracuseStep 7191449 = 5393587) B5393587
theorem B6831001 : Blo 1120629 6831001 := bstep (se 2 (by rfl) ⟨2561625, by rfl⟩ : syracuseStep 6831001 = 5123251) B5123251
theorem B1686443 : Blo 1120629 1686443 := bstep (se 1 (by rfl) ⟨1264832, by rfl⟩ : syracuseStep 1686443 = 2529665) B2529665
theorem B1686473 : Blo 1120629 1686473 := bstep (se 2 (by rfl) ⟨632427, by rfl⟩ : syracuseStep 1686473 = 1264855) B1264855
theorem B10238987 : Blo 1120629 10238987 := bstep (se 1 (by rfl) ⟨7679240, by rfl⟩ : syracuseStep 10238987 = 15358481) B15358481
theorem B7191575 : Blo 1120629 7191575 := bstep (se 1 (by rfl) ⟨5393681, by rfl⟩ : syracuseStep 7191575 = 10787363) B10787363
theorem B1686587 : Blo 1120629 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B1686647 : Blo 1120629 1686647 := bstep (se 1 (by rfl) ⟨1264985, by rfl⟩ : syracuseStep 1686647 = 2529971) B2529971
theorem B1686671 : Blo 1120629 1686671 := bstep (se 1 (by rfl) ⟨1265003, by rfl⟩ : syracuseStep 1686671 = 2530007) B2530007
theorem B1686713 : Blo 1120629 1686713 := bstep (se 2 (by rfl) ⟨632517, by rfl⟩ : syracuseStep 1686713 = 1265035) B1265035
theorem B5684417 : Blo 1120629 5684417 := bstep (se 2 (by rfl) ⟨2131656, by rfl⟩ : syracuseStep 5684417 = 4263313) B4263313
theorem B1686791 : Blo 1120629 1686791 := bstep (se 1 (by rfl) ⟨1265093, by rfl⟩ : syracuseStep 1686791 = 2530187) B2530187
theorem B1686827 : Blo 1120629 1686827 := bstep (se 1 (by rfl) ⟨1265120, by rfl⟩ : syracuseStep 1686827 = 2530241) B2530241
theorem B1260859 : Blo 1120629 1260859 := bstep (se 1 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 1260859 = 1891289) B1891289
theorem B3783995 : Blo 1120629 3783995 := bstep (se 1 (by rfl) ⟨2837996, by rfl⟩ : syracuseStep 3783995 = 5675993) B5675993
theorem B1686857 : Blo 1120629 1686857 := bstep (se 2 (by rfl) ⟨632571, by rfl⟩ : syracuseStep 1686857 = 1265143) B1265143
theorem B10796435 : Blo 1120629 10796435 := bstep (se 1 (by rfl) ⟨8097326, by rfl⟩ : syracuseStep 10796435 = 16194653) B16194653
theorem B3030529 : Blo 1120629 3030529 := bstep (se 2 (by rfl) ⟨1136448, by rfl⟩ : syracuseStep 3030529 = 2272897) B2272897
theorem B3194569 : Blo 1120629 3194569 := bstep (se 2 (by rfl) ⟨1197963, by rfl⟩ : syracuseStep 3194569 = 2395927) B2395927
theorem B1261327 : Blo 1120629 1261327 := bstep (se 1 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 1261327 = 1891991) B1891991
theorem B3784481 : Blo 1120629 3784481 := bstep (se 2 (by rfl) ⟨1419180, by rfl⟩ : syracuseStep 3784481 = 2838361) B2838361
theorem B3194923 : Blo 1120629 3194923 := bstep (se 1 (by rfl) ⟨2396192, by rfl⟩ : syracuseStep 3194923 = 4792385) B4792385
theorem B1917047 : Blo 1120629 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1261831 : Blo 1120629 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B3195197 : Blo 1120629 3195197 := bstep (se 3 (by rfl) ⟨599099, by rfl⟩ : syracuseStep 3195197 = 1198199) B1198199
theorem B3785075 : Blo 1120629 3785075 := bstep (se 1 (by rfl) ⟨2838806, by rfl⟩ : syracuseStep 3785075 = 5677613) B5677613
theorem B1262011 : Blo 1120629 1262011 := bstep (se 1 (by rfl) ⟨946508, by rfl⟩ : syracuseStep 1262011 = 1893017) B1893017
theorem B5685713 : Blo 1120629 5685713 := bstep (se 2 (by rfl) ⟨2132142, by rfl⟩ : syracuseStep 5685713 = 4264285) B4264285
theorem B1262479 : Blo 1120629 1262479 := bstep (se 1 (by rfl) ⟨946859, by rfl⟩ : syracuseStep 1262479 = 1893719) B1893719
theorem B11256893 : Blo 1120629 11256893 := bstep (se 3 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 11256893 = 4221335) B4221335
theorem B1262983 : Blo 1120629 1262983 := bstep (se 1 (by rfl) ⟨947237, by rfl⟩ : syracuseStep 1262983 = 1894475) B1894475
theorem B1918409 : Blo 1120629 1918409 := bstep (se 2 (by rfl) ⟨719403, by rfl⟩ : syracuseStep 1918409 = 1438807) B1438807
theorem B1263163 : Blo 1120629 1263163 := bstep (se 1 (by rfl) ⟨947372, by rfl⟩ : syracuseStep 1263163 = 1894745) B1894745
theorem B1263631 : Blo 1120629 1263631 := bstep (se 1 (by rfl) ⟨947723, by rfl⟩ : syracuseStep 1263631 = 1895447) B1895447
theorem B3197303 : Blo 1120629 3197303 := bstep (se 1 (by rfl) ⟨2397977, by rfl⟩ : syracuseStep 3197303 = 4795955) B4795955
theorem B2836883 : Blo 1120629 2836883 := bstep (se 1 (by rfl) ⟨2127662, by rfl⟩ : syracuseStep 2836883 = 4255325) B4255325
theorem B7195139 : Blo 1120629 7195139 := bstep (se 1 (by rfl) ⟨5396354, by rfl⟩ : syracuseStep 7195139 = 10792709) B10792709
theorem B1264135 : Blo 1120629 1264135 := bstep (se 1 (by rfl) ⟨948101, by rfl⟩ : syracuseStep 1264135 = 1896203) B1896203
theorem B5687819 : Blo 1120629 5687819 := bstep (se 1 (by rfl) ⟨4265864, by rfl⟩ : syracuseStep 5687819 = 8531729) B8531729
theorem B5687981 : Blo 1120629 5687981 := bstep (se 3 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 5687981 = 2132993) B2132993
theorem B2837177 : Blo 1120629 2837177 := bstep (se 2 (by rfl) ⟨1063941, by rfl⟩ : syracuseStep 2837177 = 2127883) B2127883
theorem B1264315 : Blo 1120629 1264315 := bstep (se 1 (by rfl) ⟨948236, by rfl⟩ : syracuseStep 1264315 = 1896473) B1896473
theorem B3591047 : Blo 1120629 3591047 := bstep (se 1 (by rfl) ⟨2693285, by rfl⟩ : syracuseStep 3591047 = 5386571) B5386571
theorem B5393297 : Blo 1120629 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B3787667 : Blo 1120629 3787667 := bstep (se 1 (by rfl) ⟨2840750, by rfl⟩ : syracuseStep 3787667 = 5681501) B5681501
theorem B28789667 : Blo 1120629 28789667 := bstep (se 1 (by rfl) ⟨21592250, by rfl⟩ : syracuseStep 28789667 = 43184501) B43184501
theorem B1264783 : Blo 1120629 1264783 := bstep (se 1 (by rfl) ⟨948587, by rfl⟩ : syracuseStep 1264783 = 1897175) B1897175
theorem B2837875 : Blo 1120629 2837875 := bstep (se 1 (by rfl) ⟨2128406, by rfl⟩ : syracuseStep 2837875 = 4256813) B4256813
theorem B2706803 : Blo 1120629 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B2838017 : Blo 1120629 2838017 := bstep (se 2 (by rfl) ⟨1064256, by rfl⟩ : syracuseStep 2838017 = 2128513) B2128513
theorem B3034759 : Blo 1120629 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B12799781 : Blo 1120629 12799781 := bstep (se 4 (by rfl) ⟨1199979, by rfl⟩ : syracuseStep 12799781 = 2399959) B2399959
theorem B2838473 : Blo 1120629 2838473 := bstep (se 2 (by rfl) ⟨1064427, by rfl⟩ : syracuseStep 2838473 = 2128855) B2128855
theorem B16175051 : Blo 1120629 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B6475949 : Blo 1120629 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B5689601 : Blo 1120629 5689601 := bstep (se 2 (by rfl) ⟨2133600, by rfl⟩ : syracuseStep 5689601 = 4267201) B4267201
theorem B3789071 : Blo 1120629 3789071 := bstep (se 1 (by rfl) ⟨2841803, by rfl⟩ : syracuseStep 3789071 = 5683607) B5683607
theorem B5394721 : Blo 1120629 5394721 := bstep (se 2 (by rfl) ⟨2023020, by rfl⟩ : syracuseStep 5394721 = 4046041) B4046041
theorem B2838827 : Blo 1120629 2838827 := bstep (se 1 (by rfl) ⟨2129120, by rfl⟩ : syracuseStep 2838827 = 4258241) B4258241
theorem B3592507 : Blo 1120629 3592507 := bstep (se 1 (by rfl) ⟨2694380, by rfl⟩ : syracuseStep 3592507 = 5388761) B5388761
theorem B4051259 : Blo 1120629 4051259 := bstep (se 1 (by rfl) ⟨3038444, by rfl⟩ : syracuseStep 4051259 = 6076889) B6076889
theorem B4051315 : Blo 1120629 4051315 := bstep (se 1 (by rfl) ⟨3038486, by rfl⟩ : syracuseStep 4051315 = 6076973) B6076973
theorem B3789341 : Blo 1120629 3789341 := bstep (se 3 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 3789341 = 1421003) B1421003
theorem B1200911 : Blo 1120629 1200911 := bstep (se 1 (by rfl) ⟨900683, by rfl⟩ : syracuseStep 1200911 = 1801367) B1801367
theorem B3199787 : Blo 1120629 3199787 := bstep (se 1 (by rfl) ⟨2399840, by rfl⟩ : syracuseStep 3199787 = 4799681) B4799681
theorem B5690411 : Blo 1120629 5690411 := bstep (se 1 (by rfl) ⟨4267808, by rfl⟩ : syracuseStep 5690411 = 8535617) B8535617
theorem B2839819 : Blo 1120629 2839819 := bstep (se 1 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 2839819 = 4259729) B4259729
theorem B2839961 : Blo 1120629 2839961 := bstep (se 2 (by rfl) ⟨1064985, by rfl⟩ : syracuseStep 2839961 = 2129971) B2129971
theorem B1136059 : Blo 1120629 1136059 := bstep (se 1 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 1136059 = 1704089) B1704089
theorem B9590237 : Blo 1120629 9590237 := bstep (se 3 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 9590237 = 3596339) B3596339
theorem B7198237 : Blo 1120629 7198237 := bstep (se 3 (by rfl) ⟨1349669, by rfl⟩ : syracuseStep 7198237 = 2699339) B2699339
theorem B2840123 : Blo 1120629 2840123 := bstep (se 1 (by rfl) ⟨2130092, by rfl⟩ : syracuseStep 2840123 = 4260185) B4260185
theorem B3200573 : Blo 1120629 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B1824631 : Blo 1120629 1824631 := bstep (se 1 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 1824631 = 2736947) B2736947
theorem B3200903 : Blo 1120629 3200903 := bstep (se 1 (by rfl) ⟨2400677, by rfl⟩ : syracuseStep 3200903 = 4801355) B4801355
theorem B6838151 : Blo 1120629 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B2840467 : Blo 1120629 2840467 := bstep (se 1 (by rfl) ⟨2130350, by rfl⟩ : syracuseStep 2840467 = 4260701) B4260701
theorem B3790745 : Blo 1120629 3790745 := bstep (se 2 (by rfl) ⟨1421529, by rfl⟩ : syracuseStep 3790745 = 2843059) B2843059
theorem B2840609 : Blo 1120629 2840609 := bstep (se 2 (by rfl) ⟨1065228, by rfl⟩ : syracuseStep 2840609 = 2130457) B2130457
theorem B3037385 : Blo 1120629 3037385 := bstep (se 2 (by rfl) ⟨1139019, by rfl⟩ : syracuseStep 3037385 = 2278039) B2278039
theorem B1595639 : Blo 1120629 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B5691707 : Blo 1120629 5691707 := bstep (se 1 (by rfl) ⟨4268780, by rfl⟩ : syracuseStep 5691707 = 8537561) B8537561
theorem B7297465 : Blo 1120629 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B5691869 : Blo 1120629 5691869 := bstep (se 3 (by rfl) ⟨1067225, by rfl⟩ : syracuseStep 5691869 = 2134451) B2134451
theorem B4676183 : Blo 1120629 4676183 := bstep (se 1 (by rfl) ⟨3507137, by rfl⟩ : syracuseStep 4676183 = 7014275) B7014275
theorem B3791447 : Blo 1120629 3791447 := bstep (se 1 (by rfl) ⟨2843585, by rfl⟩ : syracuseStep 3791447 = 5687171) B5687171
theorem B5692193 : Blo 1120629 5692193 := bstep (se 2 (by rfl) ⟨2134572, by rfl⟩ : syracuseStep 5692193 = 4269145) B4269145
theorem B2841601 : Blo 1120629 2841601 := bstep (se 2 (by rfl) ⟨1065600, by rfl⟩ : syracuseStep 2841601 = 2131201) B2131201
theorem B3038219 : Blo 1120629 3038219 := bstep (se 1 (by rfl) ⟨2278664, by rfl⟩ : syracuseStep 3038219 = 4557329) B4557329
theorem B1891343 : Blo 1120629 1891343 := bstep (se 1 (by rfl) ⟨1418507, by rfl⟩ : syracuseStep 1891343 = 2837015) B2837015
theorem B3791933 : Blo 1120629 3791933 := bstep (se 3 (by rfl) ⟨710987, by rfl⟩ : syracuseStep 3791933 = 1421975) B1421975
theorem B9723053 : Blo 1120629 9723053 := bstep (se 3 (by rfl) ⟨1823072, by rfl⟩ : syracuseStep 9723053 = 3646145) B3646145
theorem B1596601 : Blo 1120629 1596601 := bstep (se 2 (by rfl) ⟨598725, by rfl⟩ : syracuseStep 1596601 = 1197451) B1197451
theorem B1596943 : Blo 1120629 1596943 := bstep (se 1 (by rfl) ⟨1197707, by rfl⟩ : syracuseStep 1596943 = 2395415) B2395415
theorem B1891883 : Blo 1120629 1891883 := bstep (se 1 (by rfl) ⟨1418912, by rfl⟩ : syracuseStep 1891883 = 2837825) B2837825
theorem B2842199 : Blo 1120629 2842199 := bstep (se 1 (by rfl) ⟨2131649, by rfl⟩ : syracuseStep 2842199 = 4263299) B4263299
theorem B3038921 : Blo 1120629 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B5693165 : Blo 1120629 5693165 := bstep (se 3 (by rfl) ⟨1067468, by rfl⟩ : syracuseStep 5693165 = 2134937) B2134937
theorem B2842411 : Blo 1120629 2842411 := bstep (se 1 (by rfl) ⟨2131808, by rfl⟩ : syracuseStep 2842411 = 4263617) B4263617
theorem B3596147 : Blo 1120629 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B1892281 : Blo 1120629 1892281 := bstep (se 2 (by rfl) ⟨709605, by rfl⟩ : syracuseStep 1892281 = 1419211) B1419211
theorem B2842553 : Blo 1120629 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B8511803 : Blo 1120629 8511803 := bstep (se 1 (by rfl) ⟨6383852, by rfl⟩ : syracuseStep 8511803 = 12767705) B12767705
theorem B3793337 : Blo 1120629 3793337 := bstep (se 2 (by rfl) ⟨1422501, by rfl⟩ : syracuseStep 3793337 = 2845003) B2845003
theorem B1892983 : Blo 1120629 1892983 := bstep (se 1 (by rfl) ⟨1419737, by rfl⟩ : syracuseStep 1892983 = 2839475) B2839475
theorem B1598071 : Blo 1120629 1598071 := bstep (se 1 (by rfl) ⟨1198553, by rfl⟩ : syracuseStep 1598071 = 2397107) B2397107
theorem B1893179 : Blo 1120629 1893179 := bstep (se 1 (by rfl) ⟨1419884, by rfl⟩ : syracuseStep 1893179 = 2839769) B2839769
theorem B3072887 : Blo 1120629 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B2843545 : Blo 1120629 2843545 := bstep (se 2 (by rfl) ⟨1066329, by rfl⟩ : syracuseStep 2843545 = 2132659) B2132659
theorem B3793931 : Blo 1120629 3793931 := bstep (se 1 (by rfl) ⟨2845448, by rfl⟩ : syracuseStep 3793931 = 5690897) B5690897
theorem B2843707 : Blo 1120629 2843707 := bstep (se 1 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 2843707 = 4265561) B4265561
theorem B3794039 : Blo 1120629 3794039 := bstep (se 1 (by rfl) ⟨2845529, by rfl⟩ : syracuseStep 3794039 = 5691059) B5691059
theorem B1893577 : Blo 1120629 1893577 := bstep (se 2 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 1893577 = 1420183) B1420183
theorem B2843849 : Blo 1120629 2843849 := bstep (se 2 (by rfl) ⟨1066443, by rfl⟩ : syracuseStep 2843849 = 2132887) B2132887
theorem B2024851 : Blo 1120629 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B6383033 : Blo 1120629 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B2844193 : Blo 1120629 2844193 := bstep (se 2 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 2844193 = 2133145) B2133145
theorem B3794633 : Blo 1120629 3794633 := bstep (se 2 (by rfl) ⟨1422987, by rfl⟩ : syracuseStep 3794633 = 2845975) B2845975
theorem B23029505 : Blo 1120629 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B5400371 : Blo 1120629 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B1894279 : Blo 1120629 1894279 := bstep (se 1 (by rfl) ⟨1420709, by rfl⟩ : syracuseStep 1894279 = 2841419) B2841419
theorem B5400523 : Blo 1120629 5400523 := bstep (se 1 (by rfl) ⟨4050392, by rfl⟩ : syracuseStep 5400523 = 8100785) B8100785
theorem B2844791 : Blo 1120629 2844791 := bstep (se 1 (by rfl) ⟨2133593, by rfl⟩ : syracuseStep 2844791 = 4267187) B4267187
theorem B3598607 : Blo 1120629 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B3795335 : Blo 1120629 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B1894927 : Blo 1120629 1894927 := bstep (se 1 (by rfl) ⟨1421195, by rfl⟩ : syracuseStep 1894927 = 2842391) B2842391
theorem B3238433 : Blo 1120629 3238433 := bstep (se 2 (by rfl) ⟨1214412, by rfl⟩ : syracuseStep 3238433 = 2428825) B2428825
theorem B4745965 : Blo 1120629 4745965 := bstep (se 3 (by rfl) ⟨889868, by rfl⟩ : syracuseStep 4745965 = 1779737) B1779737
theorem B39906053 : Blo 1120629 39906053 := bstep (se 4 (by rfl) ⟨3741192, by rfl⟩ : syracuseStep 39906053 = 7482385) B7482385
theorem B1895467 : Blo 1120629 1895467 := bstep (se 1 (by rfl) ⟨1421600, by rfl⟩ : syracuseStep 1895467 = 2843201) B2843201
theorem B1895609 : Blo 1120629 1895609 := bstep (se 2 (by rfl) ⟨710853, by rfl⟩ : syracuseStep 1895609 = 1421707) B1421707
theorem B1600759 : Blo 1120629 1600759 := bstep (se 1 (by rfl) ⟨1200569, by rfl⟩ : syracuseStep 1600759 = 2401139) B2401139
theorem B2846087 : Blo 1120629 2846087 := bstep (se 1 (by rfl) ⟨2134565, by rfl⟩ : syracuseStep 2846087 = 4269131) B4269131
theorem B2846137 : Blo 1120629 2846137 := bstep (se 2 (by rfl) ⟨1067301, by rfl⟩ : syracuseStep 2846137 = 2134603) B2134603
theorem B6385175 : Blo 1120629 6385175 := bstep (se 1 (by rfl) ⟨4788881, by rfl⟩ : syracuseStep 6385175 = 9577763) B9577763
theorem B6155837 : Blo 1120629 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B1797817 : Blo 1120629 1797817 := bstep (se 2 (by rfl) ⟨674181, by rfl⟩ : syracuseStep 1797817 = 1348363) B1348363
theorem B5402369 : Blo 1120629 5402369 := bstep (se 2 (by rfl) ⟨2025888, by rfl⟩ : syracuseStep 5402369 = 4051777) B4051777
theorem B7204697 : Blo 1120629 7204697 := bstep (se 2 (by rfl) ⟨2701761, by rfl⟩ : syracuseStep 7204697 = 5403523) B5403523
theorem B1896311 : Blo 1120629 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B6385675 : Blo 1120629 6385675 := bstep (se 1 (by rfl) ⟨4789256, by rfl⟩ : syracuseStep 6385675 = 9578513) B9578513
theorem B4255811 : Blo 1120629 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B1896763 : Blo 1120629 1896763 := bstep (se 1 (by rfl) ⟨1422572, by rfl⟩ : syracuseStep 1896763 = 2845145) B2845145
theorem B5402969 : Blo 1120629 5402969 := bstep (se 2 (by rfl) ⟨2026113, by rfl⟩ : syracuseStep 5402969 = 4052227) B4052227
theorem B1896905 : Blo 1120629 1896905 := bstep (se 2 (by rfl) ⟨711339, by rfl⟩ : syracuseStep 1896905 = 1422679) B1422679
theorem B1799047 : Blo 1120629 1799047 := bstep (se 1 (by rfl) ⟨1349285, by rfl⟩ : syracuseStep 1799047 = 2698571) B2698571
theorem B13661081 : Blo 1120629 13661081 := bstep (se 2 (by rfl) ⟨5122905, by rfl⟩ : syracuseStep 13661081 = 10245811) B10245811
theorem B12776453 : Blo 1120629 12776453 := bstep (se 4 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 12776453 = 2395585) B2395585
theorem B1897607 : Blo 1120629 1897607 := bstep (se 1 (by rfl) ⟨1423205, by rfl⟩ : syracuseStep 1897607 = 2846411) B2846411
theorem B25949575 : Blo 1120629 25949575 := bstep (se 1 (by rfl) ⟨19462181, by rfl⟩ : syracuseStep 25949575 = 38924363) B38924363
theorem B8517149 : Blo 1120629 8517149 := bstep (se 3 (by rfl) ⟨1596965, by rfl⟩ : syracuseStep 8517149 = 3193931) B3193931
theorem B4257481 : Blo 1120629 4257481 := bstep (se 2 (by rfl) ⟨1596555, by rfl⟩ : syracuseStep 4257481 = 3193111) B3193111
theorem B10385189 : Blo 1120629 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B3602323 : Blo 1120629 3602323 := bstep (se 1 (by rfl) ⟨2701742, by rfl⟩ : syracuseStep 3602323 = 5403485) B5403485
theorem B1800137 : Blo 1120629 1800137 := bstep (se 2 (by rfl) ⟨675051, by rfl⟩ : syracuseStep 1800137 = 1350103) B1350103
theorem B6387659 : Blo 1120629 6387659 := bstep (se 1 (by rfl) ⟨4790744, by rfl⟩ : syracuseStep 6387659 = 9581489) B9581489
theorem B5830775 : Blo 1120629 5830775 := bstep (se 1 (by rfl) ⟨4373081, by rfl⟩ : syracuseStep 5830775 = 8746163) B8746163
theorem B2128187 : Blo 1120629 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B2521529 : Blo 1120629 2521529 := bstep (se 2 (by rfl) ⟨945573, by rfl⟩ : syracuseStep 2521529 = 1891147) B1891147
theorem B2521871 : Blo 1120629 2521871 := bstep (se 1 (by rfl) ⟨1891403, by rfl⟩ : syracuseStep 2521871 = 3782807) B3782807
theorem B3242767 : Blo 1120629 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B2521889 : Blo 1120629 2521889 := bstep (se 2 (by rfl) ⟨945708, by rfl⟩ : syracuseStep 2521889 = 1891417) B1891417
theorem B2128673 : Blo 1120629 2128673 := bstep (se 2 (by rfl) ⟨798252, by rfl⟩ : syracuseStep 2128673 = 1596505) B1596505
theorem B2522231 : Blo 1120629 2522231 := bstep (se 1 (by rfl) ⟨1891673, by rfl⟩ : syracuseStep 2522231 = 3783347) B3783347
theorem B2522411 : Blo 1120629 2522411 := bstep (se 1 (by rfl) ⟨1891808, by rfl⟩ : syracuseStep 2522411 = 3783617) B3783617
theorem B2522771 : Blo 1120629 2522771 := bstep (se 1 (by rfl) ⟨1892078, by rfl⟩ : syracuseStep 2522771 = 3784157) B3784157
theorem B2522825 : Blo 1120629 2522825 := bstep (se 2 (by rfl) ⟨946059, by rfl⟩ : syracuseStep 2522825 = 1892119) B1892119
theorem B4259699 : Blo 1120629 4259699 := bstep (se 1 (by rfl) ⟨3194774, by rfl⟩ : syracuseStep 4259699 = 6389549) B6389549
theorem B5111687 : Blo 1120629 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B4259897 : Blo 1120629 4259897 := bstep (se 2 (by rfl) ⟨1597461, by rfl⟩ : syracuseStep 4259897 = 3194923) B3194923
theorem B8093753 : Blo 1120629 8093753 := bstep (se 2 (by rfl) ⟨3035157, by rfl⟩ : syracuseStep 8093753 = 6070315) B6070315
theorem B1278031 : Blo 1120629 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B2130131 : Blo 1120629 2130131 := bstep (se 1 (by rfl) ⟨1597598, by rfl⟩ : syracuseStep 2130131 = 3195197) B3195197
theorem B2523383 : Blo 1120629 2523383 := bstep (se 1 (by rfl) ⟨1892537, by rfl⟩ : syracuseStep 2523383 = 3785075) B3785075
theorem B8520065 : Blo 1120629 8520065 := bstep (se 2 (by rfl) ⟨3195024, by rfl⟩ : syracuseStep 8520065 = 6390049) B6390049
theorem B12124883 : Blo 1120629 12124883 := bstep (se 1 (by rfl) ⟨9093662, by rfl⟩ : syracuseStep 12124883 = 18187325) B18187325
theorem B7504595 : Blo 1120629 7504595 := bstep (se 1 (by rfl) ⟨5628446, by rfl⟩ : syracuseStep 7504595 = 11256893) B11256893
theorem B2523977 : Blo 1120629 2523977 := bstep (se 2 (by rfl) ⟨946491, by rfl⟩ : syracuseStep 2523977 = 1892983) B1892983
theorem B2130761 : Blo 1120629 2130761 := bstep (se 2 (by rfl) ⟨799035, by rfl⟩ : syracuseStep 2130761 = 1598071) B1598071
theorem B4260883 : Blo 1120629 4260883 := bstep (se 1 (by rfl) ⟨3195662, by rfl⟩ : syracuseStep 4260883 = 6391325) B6391325
theorem B15598657 : Blo 1120629 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B2131535 : Blo 1120629 2131535 := bstep (se 1 (by rfl) ⟨1598651, by rfl⟩ : syracuseStep 2131535 = 3197303) B3197303
theorem B2524769 : Blo 1120629 2524769 := bstep (se 2 (by rfl) ⟨946788, by rfl⟩ : syracuseStep 2524769 = 1893577) B1893577
theorem B9111179 : Blo 1120629 9111179 := bstep (se 1 (by rfl) ⟨6833384, by rfl⟩ : syracuseStep 9111179 = 13666769) B13666769
theorem B14780153 : Blo 1120629 14780153 := bstep (se 2 (by rfl) ⟨5542557, by rfl⟩ : syracuseStep 14780153 = 11085115) B11085115
theorem B6162169 : Blo 1120629 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B2394031 : Blo 1120629 2394031 := bstep (se 1 (by rfl) ⟨1795523, by rfl⟩ : syracuseStep 2394031 = 3591047) B3591047
theorem B2525111 : Blo 1120629 2525111 := bstep (se 1 (by rfl) ⟨1893833, by rfl⟩ : syracuseStep 2525111 = 3787667) B3787667
theorem B2558123 : Blo 1120629 2558123 := bstep (se 1 (by rfl) ⟨1918592, by rfl⟩ : syracuseStep 2558123 = 3837185) B3837185
theorem B1804535 : Blo 1120629 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B2525705 : Blo 1120629 2525705 := bstep (se 2 (by rfl) ⟨947139, by rfl⟩ : syracuseStep 2525705 = 1894279) B1894279
theorem B10783367 : Blo 1120629 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B4262615 : Blo 1120629 4262615 := bstep (se 1 (by rfl) ⟨3196961, by rfl⟩ : syracuseStep 4262615 = 6393923) B6393923
theorem B2526047 : Blo 1120629 2526047 := bstep (se 1 (by rfl) ⟨1894535, by rfl⟩ : syracuseStep 2526047 = 3789071) B3789071
theorem B2526227 : Blo 1120629 2526227 := bstep (se 1 (by rfl) ⟨1894670, by rfl⟩ : syracuseStep 2526227 = 3789341) B3789341
theorem B2133191 : Blo 1120629 2133191 := bstep (se 1 (by rfl) ⟨1599893, by rfl⟩ : syracuseStep 2133191 = 3199787) B3199787
theorem B2526569 : Blo 1120629 2526569 := bstep (se 2 (by rfl) ⟨947463, by rfl⟩ : syracuseStep 2526569 = 1894927) B1894927
theorem B6327953 : Blo 1120629 6327953 := bstep (se 2 (by rfl) ⟨2372982, by rfl⟩ : syracuseStep 6327953 = 4745965) B4745965
theorem B6393491 : Blo 1120629 6393491 := bstep (se 1 (by rfl) ⟨4795118, by rfl⟩ : syracuseStep 6393491 = 9590237) B9590237
theorem B2133715 : Blo 1120629 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B4788011 : Blo 1120629 4788011 := bstep (se 1 (by rfl) ⟨3591008, by rfl⟩ : syracuseStep 4788011 = 7182017) B7182017
theorem B5115757 : Blo 1120629 5115757 := bstep (se 3 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 5115757 = 1918409) B1918409
theorem B4263799 : Blo 1120629 4263799 := bstep (se 1 (by rfl) ⟨3197849, by rfl⟩ : syracuseStep 4263799 = 6395699) B6395699
theorem B4853665 : Blo 1120629 4853665 := bstep (se 2 (by rfl) ⟨1820124, by rfl⟩ : syracuseStep 4853665 = 3640249) B3640249
theorem B2133935 : Blo 1120629 2133935 := bstep (se 1 (by rfl) ⟨1600451, by rfl⟩ : syracuseStep 2133935 = 3200903) B3200903
theorem B2527163 : Blo 1120629 2527163 := bstep (se 1 (by rfl) ⟨1895372, by rfl⟩ : syracuseStep 2527163 = 3790745) B3790745
theorem B2527289 : Blo 1120629 2527289 := bstep (se 2 (by rfl) ⟨947733, by rfl⟩ : syracuseStep 2527289 = 1895467) B1895467
theorem B2134345 : Blo 1120629 2134345 := bstep (se 2 (by rfl) ⟨800379, by rfl⟩ : syracuseStep 2134345 = 1600759) B1600759
theorem B6394241 : Blo 1120629 6394241 := bstep (se 2 (by rfl) ⟨2397840, by rfl⟩ : syracuseStep 6394241 = 4795681) B4795681
theorem B3117455 : Blo 1120629 3117455 := bstep (se 1 (by rfl) ⟨2338091, by rfl⟩ : syracuseStep 3117455 = 4676183) B4676183
theorem B2527631 : Blo 1120629 2527631 := bstep (se 1 (by rfl) ⟨1895723, by rfl⟩ : syracuseStep 2527631 = 3791447) B3791447
theorem B2527955 : Blo 1120629 2527955 := bstep (se 1 (by rfl) ⟨1895966, by rfl⟩ : syracuseStep 2527955 = 3791933) B3791933
theorem B4264771 : Blo 1120629 4264771 := bstep (se 1 (by rfl) ⟨3198578, by rfl⟩ : syracuseStep 4264771 = 6397157) B6397157
theorem B6394697 : Blo 1120629 6394697 := bstep (se 2 (by rfl) ⟨2398011, by rfl⟩ : syracuseStep 6394697 = 4796023) B4796023
theorem B2397089 : Blo 1120629 2397089 := bstep (se 2 (by rfl) ⟨898908, by rfl⟩ : syracuseStep 2397089 = 1797817) B1797817
theorem B4265075 : Blo 1120629 4265075 := bstep (se 1 (by rfl) ⟨3198806, by rfl⟩ : syracuseStep 4265075 = 6397613) B6397613
theorem B2397431 : Blo 1120629 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B5674535 : Blo 1120629 5674535 := bstep (se 1 (by rfl) ⟨4255901, by rfl⟩ : syracuseStep 5674535 = 8511803) B8511803
theorem B4265531 : Blo 1120629 4265531 := bstep (se 1 (by rfl) ⟨3199148, by rfl⟩ : syracuseStep 4265531 = 6398297) B6398297
theorem B2528891 : Blo 1120629 2528891 := bstep (se 1 (by rfl) ⟨1896668, by rfl⟩ : syracuseStep 2528891 = 3793337) B3793337
theorem B4789975 : Blo 1120629 4789975 := bstep (se 1 (by rfl) ⟨3592481, by rfl⟩ : syracuseStep 4789975 = 7184963) B7184963
theorem B4790009 : Blo 1120629 4790009 := bstep (se 2 (by rfl) ⟨1796253, by rfl⟩ : syracuseStep 4790009 = 3592507) B3592507
theorem B2529017 : Blo 1120629 2529017 := bstep (se 2 (by rfl) ⟨948381, by rfl⟩ : syracuseStep 2529017 = 1896763) B1896763
theorem B11540333 : Blo 1120629 11540333 := bstep (se 3 (by rfl) ⟨2163812, by rfl⟩ : syracuseStep 11540333 = 4327625) B4327625
theorem B25958353 : Blo 1120629 25958353 := bstep (se 2 (by rfl) ⟨9734382, by rfl⟩ : syracuseStep 25958353 = 19468765) B19468765
theorem B2529287 : Blo 1120629 2529287 := bstep (se 1 (by rfl) ⟨1896965, by rfl⟩ : syracuseStep 2529287 = 3793931) B3793931
theorem B2529359 : Blo 1120629 2529359 := bstep (se 1 (by rfl) ⟨1897019, by rfl⟩ : syracuseStep 2529359 = 3794039) B3794039
theorem B14391553 : Blo 1120629 14391553 := bstep (se 2 (by rfl) ⟨5396832, by rfl⟩ : syracuseStep 14391553 = 10793665) B10793665
theorem B1120635 : Blo 1120629 1120635 := bstep (se 1 (by rfl) ⟨840476, by rfl⟩ : syracuseStep 1120635 = 1680953) B1680953
theorem B1120687 : Blo 1120629 1120687 := bstep (se 1 (by rfl) ⟨840515, by rfl⟩ : syracuseStep 1120687 = 1681031) B1681031
theorem B1120711 : Blo 1120629 1120711 := bstep (se 1 (by rfl) ⟨840533, by rfl⟩ : syracuseStep 1120711 = 1681067) B1681067
theorem B1120731 : Blo 1120629 1120731 := bstep (se 1 (by rfl) ⟨840548, by rfl⟩ : syracuseStep 1120731 = 1681097) B1681097
theorem B2529755 : Blo 1120629 2529755 := bstep (se 1 (by rfl) ⟨1897316, by rfl⟩ : syracuseStep 2529755 = 3794633) B3794633
theorem B2398729 : Blo 1120629 2398729 := bstep (se 2 (by rfl) ⟨899523, by rfl⟩ : syracuseStep 2398729 = 1799047) B1799047
theorem B1120807 : Blo 1120629 1120807 := bstep (se 1 (by rfl) ⟨840605, by rfl⟩ : syracuseStep 1120807 = 1681211) B1681211
theorem B1120847 : Blo 1120629 1120847 := bstep (se 1 (by rfl) ⟨840635, by rfl⟩ : syracuseStep 1120847 = 1681271) B1681271
theorem B1120863 : Blo 1120629 1120863 := bstep (se 1 (by rfl) ⟨840647, by rfl⟩ : syracuseStep 1120863 = 1681295) B1681295
theorem B1120891 : Blo 1120629 1120891 := bstep (se 1 (by rfl) ⟨840668, by rfl⟩ : syracuseStep 1120891 = 1681337) B1681337
theorem B1120943 : Blo 1120629 1120943 := bstep (se 1 (by rfl) ⟨840707, by rfl⟩ : syracuseStep 1120943 = 1681415) B1681415
theorem B1120967 : Blo 1120629 1120967 := bstep (se 1 (by rfl) ⟨840725, by rfl⟩ : syracuseStep 1120967 = 1681451) B1681451
theorem B1120987 : Blo 1120629 1120987 := bstep (se 1 (by rfl) ⟨840740, by rfl⟩ : syracuseStep 1120987 = 1681481) B1681481
theorem B1121063 : Blo 1120629 1121063 := bstep (se 1 (by rfl) ⟨840797, by rfl⟩ : syracuseStep 1121063 = 1681595) B1681595
theorem B1121103 : Blo 1120629 1121103 := bstep (se 1 (by rfl) ⟨840827, by rfl⟩ : syracuseStep 1121103 = 1681655) B1681655
theorem B1121119 : Blo 1120629 1121119 := bstep (se 1 (by rfl) ⟨840839, by rfl⟩ : syracuseStep 1121119 = 1681679) B1681679
theorem B2399071 : Blo 1120629 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B1121147 : Blo 1120629 1121147 := bstep (se 1 (by rfl) ⟨840860, by rfl⟩ : syracuseStep 1121147 = 1681721) B1681721
theorem B1121199 : Blo 1120629 1121199 := bstep (se 1 (by rfl) ⟨840899, by rfl⟩ : syracuseStep 1121199 = 1681799) B1681799
theorem B2530223 : Blo 1120629 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B1121223 : Blo 1120629 1121223 := bstep (se 1 (by rfl) ⟨840917, by rfl⟩ : syracuseStep 1121223 = 1681835) B1681835
theorem B1121243 : Blo 1120629 1121243 := bstep (se 1 (by rfl) ⟨840932, by rfl⟩ : syracuseStep 1121243 = 1681865) B1681865
theorem B1121319 : Blo 1120629 1121319 := bstep (se 1 (by rfl) ⟨840989, by rfl⟩ : syracuseStep 1121319 = 1681979) B1681979
theorem B1121359 : Blo 1120629 1121359 := bstep (se 1 (by rfl) ⟨841019, by rfl⟩ : syracuseStep 1121359 = 1682039) B1682039
theorem B1121375 : Blo 1120629 1121375 := bstep (se 1 (by rfl) ⟨841031, by rfl⟩ : syracuseStep 1121375 = 1682063) B1682063
theorem B1121403 : Blo 1120629 1121403 := bstep (se 1 (by rfl) ⟨841052, by rfl⟩ : syracuseStep 1121403 = 1682105) B1682105
theorem B1121455 : Blo 1120629 1121455 := bstep (se 1 (by rfl) ⟨841091, by rfl⟩ : syracuseStep 1121455 = 1682183) B1682183
theorem B1121479 : Blo 1120629 1121479 := bstep (se 1 (by rfl) ⟨841109, by rfl⟩ : syracuseStep 1121479 = 1682219) B1682219
theorem B1121499 : Blo 1120629 1121499 := bstep (se 1 (by rfl) ⟨841124, by rfl⟩ : syracuseStep 1121499 = 1682249) B1682249
theorem B1121575 : Blo 1120629 1121575 := bstep (se 1 (by rfl) ⟨841181, by rfl⟩ : syracuseStep 1121575 = 1682363) B1682363
theorem B1121615 : Blo 1120629 1121615 := bstep (se 1 (by rfl) ⟨841211, by rfl⟩ : syracuseStep 1121615 = 1682423) B1682423
theorem B1121631 : Blo 1120629 1121631 := bstep (se 1 (by rfl) ⟨841223, by rfl⟩ : syracuseStep 1121631 = 1682447) B1682447
theorem B1121659 : Blo 1120629 1121659 := bstep (se 1 (by rfl) ⟨841244, by rfl⟩ : syracuseStep 1121659 = 1682489) B1682489
theorem B1121711 : Blo 1120629 1121711 := bstep (se 1 (by rfl) ⟨841283, by rfl⟩ : syracuseStep 1121711 = 1682567) B1682567
theorem B1121735 : Blo 1120629 1121735 := bstep (se 1 (by rfl) ⟨841301, by rfl⟩ : syracuseStep 1121735 = 1682603) B1682603
theorem B1121755 : Blo 1120629 1121755 := bstep (se 1 (by rfl) ⟨841316, by rfl⟩ : syracuseStep 1121755 = 1682633) B1682633
theorem B1121831 : Blo 1120629 1121831 := bstep (se 1 (by rfl) ⟨841373, by rfl⟩ : syracuseStep 1121831 = 1682747) B1682747
theorem B1121871 : Blo 1120629 1121871 := bstep (se 1 (by rfl) ⟨841403, by rfl⟩ : syracuseStep 1121871 = 1682807) B1682807
theorem B1121887 : Blo 1120629 1121887 := bstep (se 1 (by rfl) ⟨841415, by rfl⟩ : syracuseStep 1121887 = 1682831) B1682831
theorem B5676641 : Blo 1120629 5676641 := bstep (se 2 (by rfl) ⟨2128740, by rfl⟩ : syracuseStep 5676641 = 4257481) B4257481
theorem B1121915 : Blo 1120629 1121915 := bstep (se 1 (by rfl) ⟨841436, by rfl⟩ : syracuseStep 1121915 = 1682873) B1682873
theorem B1121967 : Blo 1120629 1121967 := bstep (se 1 (by rfl) ⟨841475, by rfl⟩ : syracuseStep 1121967 = 1682951) B1682951
theorem B1121991 : Blo 1120629 1121991 := bstep (se 1 (by rfl) ⟨841493, by rfl⟩ : syracuseStep 1121991 = 1682987) B1682987
theorem B4103891 : Blo 1120629 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B1122011 : Blo 1120629 1122011 := bstep (se 1 (by rfl) ⟨841508, by rfl⟩ : syracuseStep 1122011 = 1683017) B1683017
theorem B1122087 : Blo 1120629 1122087 := bstep (se 1 (by rfl) ⟨841565, by rfl⟩ : syracuseStep 1122087 = 1683131) B1683131
theorem B1122127 : Blo 1120629 1122127 := bstep (se 1 (by rfl) ⟨841595, by rfl⟩ : syracuseStep 1122127 = 1683191) B1683191
theorem B1122143 : Blo 1120629 1122143 := bstep (se 1 (by rfl) ⟨841607, by rfl⟩ : syracuseStep 1122143 = 1683215) B1683215
theorem B1122171 : Blo 1120629 1122171 := bstep (se 1 (by rfl) ⟨841628, by rfl⟩ : syracuseStep 1122171 = 1683257) B1683257
theorem B1122223 : Blo 1120629 1122223 := bstep (se 1 (by rfl) ⟨841667, by rfl⟩ : syracuseStep 1122223 = 1683335) B1683335
theorem B1122247 : Blo 1120629 1122247 := bstep (se 1 (by rfl) ⟨841685, by rfl⟩ : syracuseStep 1122247 = 1683371) B1683371
theorem B1122267 : Blo 1120629 1122267 := bstep (se 1 (by rfl) ⟨841700, by rfl⟩ : syracuseStep 1122267 = 1683401) B1683401
theorem B27303965 : Blo 1120629 27303965 := bstep (se 3 (by rfl) ⟨5119493, by rfl⟩ : syracuseStep 27303965 = 10238987) B10238987
theorem B1122343 : Blo 1120629 1122343 := bstep (se 1 (by rfl) ⟨841757, by rfl⟩ : syracuseStep 1122343 = 1683515) B1683515
theorem B1122383 : Blo 1120629 1122383 := bstep (se 1 (by rfl) ⟨841787, by rfl⟩ : syracuseStep 1122383 = 1683575) B1683575
theorem B1122399 : Blo 1120629 1122399 := bstep (se 1 (by rfl) ⟨841799, by rfl⟩ : syracuseStep 1122399 = 1683599) B1683599
theorem B1122427 : Blo 1120629 1122427 := bstep (se 1 (by rfl) ⟨841820, by rfl⟩ : syracuseStep 1122427 = 1683641) B1683641
theorem B1122479 : Blo 1120629 1122479 := bstep (se 1 (by rfl) ⟨841859, by rfl⟩ : syracuseStep 1122479 = 1683719) B1683719
theorem B1122503 : Blo 1120629 1122503 := bstep (se 1 (by rfl) ⟨841877, by rfl⟩ : syracuseStep 1122503 = 1683755) B1683755
theorem B1122523 : Blo 1120629 1122523 := bstep (se 1 (by rfl) ⟨841892, by rfl⟩ : syracuseStep 1122523 = 1683785) B1683785
theorem B1122599 : Blo 1120629 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B1122639 : Blo 1120629 1122639 := bstep (se 1 (by rfl) ⟨841979, by rfl⟩ : syracuseStep 1122639 = 1683959) B1683959
theorem B1122655 : Blo 1120629 1122655 := bstep (se 1 (by rfl) ⟨841991, by rfl⟩ : syracuseStep 1122655 = 1683983) B1683983
theorem B1122683 : Blo 1120629 1122683 := bstep (se 1 (by rfl) ⟨842012, by rfl⟩ : syracuseStep 1122683 = 1684025) B1684025
theorem B1122735 : Blo 1120629 1122735 := bstep (se 1 (by rfl) ⟨842051, by rfl⟩ : syracuseStep 1122735 = 1684103) B1684103
theorem B1122759 : Blo 1120629 1122759 := bstep (se 1 (by rfl) ⟨842069, by rfl⟩ : syracuseStep 1122759 = 1684139) B1684139
theorem B1122779 : Blo 1120629 1122779 := bstep (se 1 (by rfl) ⟨842084, by rfl⟩ : syracuseStep 1122779 = 1684169) B1684169
theorem B1122855 : Blo 1120629 1122855 := bstep (se 1 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 1122855 = 1684283) B1684283
theorem B1122895 : Blo 1120629 1122895 := bstep (se 1 (by rfl) ⟨842171, by rfl⟩ : syracuseStep 1122895 = 1684343) B1684343
theorem B1122911 : Blo 1120629 1122911 := bstep (se 1 (by rfl) ⟨842183, by rfl⟩ : syracuseStep 1122911 = 1684367) B1684367
theorem B1122939 : Blo 1120629 1122939 := bstep (se 1 (by rfl) ⟨842204, by rfl⟩ : syracuseStep 1122939 = 1684409) B1684409
theorem B1122991 : Blo 1120629 1122991 := bstep (se 1 (by rfl) ⟨842243, by rfl⟩ : syracuseStep 1122991 = 1684487) B1684487
theorem B1123015 : Blo 1120629 1123015 := bstep (se 1 (by rfl) ⟨842261, by rfl⟩ : syracuseStep 1123015 = 1684523) B1684523
theorem B1123035 : Blo 1120629 1123035 := bstep (se 1 (by rfl) ⟨842276, by rfl⟩ : syracuseStep 1123035 = 1684553) B1684553
theorem B1123111 : Blo 1120629 1123111 := bstep (se 1 (by rfl) ⟨842333, by rfl⟩ : syracuseStep 1123111 = 1684667) B1684667
theorem B1123151 : Blo 1120629 1123151 := bstep (se 1 (by rfl) ⟨842363, by rfl⟩ : syracuseStep 1123151 = 1684727) B1684727
theorem B1123167 : Blo 1120629 1123167 := bstep (se 1 (by rfl) ⟨842375, by rfl⟩ : syracuseStep 1123167 = 1684751) B1684751
theorem B1123195 : Blo 1120629 1123195 := bstep (se 1 (by rfl) ⟨842396, by rfl⟩ : syracuseStep 1123195 = 1684793) B1684793
theorem B2696111 : Blo 1120629 2696111 := bstep (se 1 (by rfl) ⟨2022083, by rfl⟩ : syracuseStep 2696111 = 4044167) B4044167
theorem B1123247 : Blo 1120629 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B1123271 : Blo 1120629 1123271 := bstep (se 1 (by rfl) ⟨842453, by rfl⟩ : syracuseStep 1123271 = 1684907) B1684907
theorem B1123291 : Blo 1120629 1123291 := bstep (se 1 (by rfl) ⟨842468, by rfl⟩ : syracuseStep 1123291 = 1684937) B1684937
theorem B5678099 : Blo 1120629 5678099 := bstep (se 1 (by rfl) ⟨4258574, by rfl⟩ : syracuseStep 5678099 = 8517149) B8517149
theorem B1123367 : Blo 1120629 1123367 := bstep (se 1 (by rfl) ⟨842525, by rfl⟩ : syracuseStep 1123367 = 1685051) B1685051
theorem B1123407 : Blo 1120629 1123407 := bstep (se 1 (by rfl) ⟨842555, by rfl⟩ : syracuseStep 1123407 = 1685111) B1685111
theorem B1123423 : Blo 1120629 1123423 := bstep (se 1 (by rfl) ⟨842567, by rfl⟩ : syracuseStep 1123423 = 1685135) B1685135
theorem B1123451 : Blo 1120629 1123451 := bstep (se 1 (by rfl) ⟨842588, by rfl⟩ : syracuseStep 1123451 = 1685177) B1685177
theorem B1123503 : Blo 1120629 1123503 := bstep (se 1 (by rfl) ⟨842627, by rfl⟩ : syracuseStep 1123503 = 1685255) B1685255
theorem B6923459 : Blo 1120629 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B1123527 : Blo 1120629 1123527 := bstep (se 1 (by rfl) ⟨842645, by rfl⟩ : syracuseStep 1123527 = 1685291) B1685291
theorem B1123547 : Blo 1120629 1123547 := bstep (se 1 (by rfl) ⟨842660, by rfl⟩ : syracuseStep 1123547 = 1685321) B1685321
theorem B1844473 : Blo 1120629 1844473 := bstep (se 2 (by rfl) ⟨691677, by rfl⟩ : syracuseStep 1844473 = 1383355) B1383355
theorem B1123623 : Blo 1120629 1123623 := bstep (se 1 (by rfl) ⟨842717, by rfl⟩ : syracuseStep 1123623 = 1685435) B1685435
theorem B1123663 : Blo 1120629 1123663 := bstep (se 1 (by rfl) ⟨842747, by rfl⟩ : syracuseStep 1123663 = 1685495) B1685495
theorem B1123679 : Blo 1120629 1123679 := bstep (se 1 (by rfl) ⟨842759, by rfl⟩ : syracuseStep 1123679 = 1685519) B1685519
theorem B1123707 : Blo 1120629 1123707 := bstep (se 1 (by rfl) ⟨842780, by rfl⟩ : syracuseStep 1123707 = 1685561) B1685561
theorem B1123759 : Blo 1120629 1123759 := bstep (se 1 (by rfl) ⟨842819, by rfl⟩ : syracuseStep 1123759 = 1685639) B1685639
theorem B1123783 : Blo 1120629 1123783 := bstep (se 1 (by rfl) ⟨842837, by rfl⟩ : syracuseStep 1123783 = 1685675) B1685675
theorem B1123803 : Blo 1120629 1123803 := bstep (se 1 (by rfl) ⟨842852, by rfl⟩ : syracuseStep 1123803 = 1685705) B1685705
theorem B1418791 : Blo 1120629 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B1123879 : Blo 1120629 1123879 := bstep (se 1 (by rfl) ⟨842909, by rfl⟩ : syracuseStep 1123879 = 1685819) B1685819
theorem B1123919 : Blo 1120629 1123919 := bstep (se 1 (by rfl) ⟨842939, by rfl⟩ : syracuseStep 1123919 = 1685879) B1685879
theorem B1123935 : Blo 1120629 1123935 := bstep (se 1 (by rfl) ⟨842951, by rfl⟩ : syracuseStep 1123935 = 1685903) B1685903
theorem B1681019 : Blo 1120629 1681019 := bstep (se 1 (by rfl) ⟨1260764, by rfl⟩ : syracuseStep 1681019 = 2521529) B2521529
theorem B1123963 : Blo 1120629 1123963 := bstep (se 1 (by rfl) ⟨842972, by rfl⟩ : syracuseStep 1123963 = 1685945) B1685945
theorem B1124015 : Blo 1120629 1124015 := bstep (se 1 (by rfl) ⟨843011, by rfl⟩ : syracuseStep 1124015 = 1686023) B1686023
theorem B1124039 : Blo 1120629 1124039 := bstep (se 1 (by rfl) ⟨843029, by rfl⟩ : syracuseStep 1124039 = 1686059) B1686059
theorem B1124059 : Blo 1120629 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B1681145 : Blo 1120629 1681145 := bstep (se 2 (by rfl) ⟨630429, by rfl⟩ : syracuseStep 1681145 = 1260859) B1260859
theorem B1124135 : Blo 1120629 1124135 := bstep (se 1 (by rfl) ⟨843101, by rfl⟩ : syracuseStep 1124135 = 1686203) B1686203
theorem B1124175 : Blo 1120629 1124175 := bstep (se 1 (by rfl) ⟨843131, by rfl⟩ : syracuseStep 1124175 = 1686263) B1686263
theorem B1681247 : Blo 1120629 1681247 := bstep (se 1 (by rfl) ⟨1260935, by rfl⟩ : syracuseStep 1681247 = 2521871) B2521871
theorem B1124191 : Blo 1120629 1124191 := bstep (se 1 (by rfl) ⟨843143, by rfl⟩ : syracuseStep 1124191 = 1686287) B1686287
theorem B1681259 : Blo 1120629 1681259 := bstep (se 1 (by rfl) ⟨1260944, by rfl⟩ : syracuseStep 1681259 = 2521889) B2521889
theorem B1419115 : Blo 1120629 1419115 := bstep (se 1 (by rfl) ⟨1064336, by rfl⟩ : syracuseStep 1419115 = 2128673) B2128673
theorem B1124219 : Blo 1120629 1124219 := bstep (se 1 (by rfl) ⟨843164, by rfl⟩ : syracuseStep 1124219 = 1686329) B1686329
theorem B1124271 : Blo 1120629 1124271 := bstep (se 1 (by rfl) ⟨843203, by rfl⟩ : syracuseStep 1124271 = 1686407) B1686407
theorem B4794299 : Blo 1120629 4794299 := bstep (se 1 (by rfl) ⟨3595724, by rfl⟩ : syracuseStep 4794299 = 7191449) B7191449
theorem B1124295 : Blo 1120629 1124295 := bstep (se 1 (by rfl) ⟨843221, by rfl⟩ : syracuseStep 1124295 = 1686443) B1686443
theorem B1124315 : Blo 1120629 1124315 := bstep (se 1 (by rfl) ⟨843236, by rfl⟩ : syracuseStep 1124315 = 1686473) B1686473
theorem B4040705 : Blo 1120629 4040705 := bstep (se 2 (by rfl) ⟨1515264, by rfl⟩ : syracuseStep 4040705 = 3030529) B3030529
theorem B4794383 : Blo 1120629 4794383 := bstep (se 1 (by rfl) ⟨3595787, by rfl⟩ : syracuseStep 4794383 = 7191575) B7191575
theorem B1124391 : Blo 1120629 1124391 := bstep (se 1 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 1124391 = 1686587) B1686587
theorem B1681487 : Blo 1120629 1681487 := bstep (se 1 (by rfl) ⟨1261115, by rfl⟩ : syracuseStep 1681487 = 2522231) B2522231
theorem B1124431 : Blo 1120629 1124431 := bstep (se 1 (by rfl) ⟨843323, by rfl⟩ : syracuseStep 1124431 = 1686647) B1686647
theorem B1124447 : Blo 1120629 1124447 := bstep (se 1 (by rfl) ⟨843335, by rfl⟩ : syracuseStep 1124447 = 1686671) B1686671
theorem B1124475 : Blo 1120629 1124475 := bstep (se 1 (by rfl) ⟨843356, by rfl⟩ : syracuseStep 1124475 = 1686713) B1686713
theorem B1124527 : Blo 1120629 1124527 := bstep (se 1 (by rfl) ⟨843395, by rfl⟩ : syracuseStep 1124527 = 1686791) B1686791
theorem B1681607 : Blo 1120629 1681607 := bstep (se 1 (by rfl) ⟨1261205, by rfl⟩ : syracuseStep 1681607 = 2522411) B2522411
theorem B1124551 : Blo 1120629 1124551 := bstep (se 1 (by rfl) ⟨843413, by rfl⟩ : syracuseStep 1124551 = 1686827) B1686827
theorem B1124571 : Blo 1120629 1124571 := bstep (se 1 (by rfl) ⟨843428, by rfl⟩ : syracuseStep 1124571 = 1686857) B1686857
theorem B1681769 : Blo 1120629 1681769 := bstep (se 2 (by rfl) ⟨630663, by rfl⟩ : syracuseStep 1681769 = 1261327) B1261327
theorem B1681847 : Blo 1120629 1681847 := bstep (se 1 (by rfl) ⟨1261385, by rfl⟩ : syracuseStep 1681847 = 2522771) B2522771
theorem B1681883 : Blo 1120629 1681883 := bstep (se 1 (by rfl) ⟨1261412, by rfl⟩ : syracuseStep 1681883 = 2522825) B2522825
theorem B6826477 : Blo 1120629 6826477 := bstep (se 3 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 6826477 = 2559929) B2559929
theorem B1682351 : Blo 1120629 1682351 := bstep (se 1 (by rfl) ⟨1261763, by rfl⟩ : syracuseStep 1682351 = 2523527) B2523527
theorem B1682441 : Blo 1120629 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B4041743 : Blo 1120629 4041743 := bstep (se 1 (by rfl) ⟨3031307, by rfl⟩ : syracuseStep 4041743 = 6062615) B6062615
theorem B621849635 : Blo 1120629 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B1682471 : Blo 1120629 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B1682555 : Blo 1120629 1682555 := bstep (se 1 (by rfl) ⟨1261916, by rfl⟩ : syracuseStep 1682555 = 2523833) B2523833
theorem B1420411 : Blo 1120629 1420411 := bstep (se 1 (by rfl) ⟨1065308, by rfl⟩ : syracuseStep 1420411 = 2130617) B2130617
theorem B1682681 : Blo 1120629 1682681 := bstep (se 2 (by rfl) ⟨631005, by rfl⟩ : syracuseStep 1682681 = 1262011) B1262011
theorem B6925591 : Blo 1120629 6925591 := bstep (se 1 (by rfl) ⟨5194193, by rfl⟩ : syracuseStep 6925591 = 10388387) B10388387
theorem B1682783 : Blo 1120629 1682783 := bstep (se 1 (by rfl) ⟨1262087, by rfl⟩ : syracuseStep 1682783 = 2524175) B2524175
theorem B1682795 : Blo 1120629 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B7187885 : Blo 1120629 7187885 := bstep (se 3 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 7187885 = 2695457) B2695457
theorem B10792435 : Blo 1120629 10792435 := bstep (se 1 (by rfl) ⟨8094326, by rfl⟩ : syracuseStep 10792435 = 16188653) B16188653
theorem B4107763 : Blo 1120629 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B1683023 : Blo 1120629 1683023 := bstep (se 1 (by rfl) ⟨1262267, by rfl⟩ : syracuseStep 1683023 = 2524535) B2524535
theorem B1683143 : Blo 1120629 1683143 := bstep (se 1 (by rfl) ⟨1262357, by rfl⟩ : syracuseStep 1683143 = 2524715) B2524715
theorem B2076407 : Blo 1120629 2076407 := bstep (se 1 (by rfl) ⟨1557305, by rfl⟩ : syracuseStep 2076407 = 3114611) B3114611
theorem B1683305 : Blo 1120629 1683305 := bstep (se 2 (by rfl) ⟨631239, by rfl⟩ : syracuseStep 1683305 = 1262479) B1262479
theorem B5681015 : Blo 1120629 5681015 := bstep (se 1 (by rfl) ⟨4260761, by rfl⟩ : syracuseStep 5681015 = 8521523) B8521523
theorem B1683383 : Blo 1120629 1683383 := bstep (se 1 (by rfl) ⟨1262537, by rfl⟩ : syracuseStep 1683383 = 2525075) B2525075
theorem B1683419 : Blo 1120629 1683419 := bstep (se 1 (by rfl) ⟨1262564, by rfl⟩ : syracuseStep 1683419 = 2525129) B2525129
theorem B4108403 : Blo 1120629 4108403 := bstep (se 1 (by rfl) ⟨3081302, by rfl⟩ : syracuseStep 4108403 = 6162605) B6162605
theorem B32354477 : Blo 1120629 32354477 := bstep (se 3 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 32354477 = 12132929) B12132929
theorem B4796759 : Blo 1120629 4796759 := bstep (se 1 (by rfl) ⟨3597569, by rfl⟩ : syracuseStep 4796759 = 7195139) B7195139
theorem B1683887 : Blo 1120629 1683887 := bstep (se 1 (by rfl) ⟨1262915, by rfl⟩ : syracuseStep 1683887 = 2525831) B2525831
theorem B28750301 : Blo 1120629 28750301 := bstep (se 3 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 28750301 = 10781363) B10781363
theorem B1683977 : Blo 1120629 1683977 := bstep (se 2 (by rfl) ⟨631491, by rfl⟩ : syracuseStep 1683977 = 1262983) B1262983
theorem B2699801 : Blo 1120629 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B1684007 : Blo 1120629 1684007 := bstep (se 1 (by rfl) ⟨1263005, by rfl⟩ : syracuseStep 1684007 = 2526011) B2526011
theorem B21607013 : Blo 1120629 21607013 := bstep (se 4 (by rfl) ⟨2025657, by rfl⟩ : syracuseStep 21607013 = 4051315) B4051315
theorem B1684091 : Blo 1120629 1684091 := bstep (se 1 (by rfl) ⟨1263068, by rfl⟩ : syracuseStep 1684091 = 2526137) B2526137
theorem B1684217 : Blo 1120629 1684217 := bstep (se 2 (by rfl) ⟨631581, by rfl⟩ : syracuseStep 1684217 = 1263163) B1263163
theorem B1684319 : Blo 1120629 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B1684331 : Blo 1120629 1684331 := bstep (se 1 (by rfl) ⟨1263248, by rfl⟩ : syracuseStep 1684331 = 2526497) B2526497
theorem B4502459 : Blo 1120629 4502459 := bstep (se 1 (by rfl) ⟨3376844, by rfl⟩ : syracuseStep 4502459 = 6753689) B6753689
theorem B1422299 : Blo 1120629 1422299 := bstep (se 1 (by rfl) ⟨1066724, by rfl⟩ : syracuseStep 1422299 = 2133449) B2133449
theorem B1684559 : Blo 1120629 1684559 := bstep (se 1 (by rfl) ⟨1263419, by rfl⟩ : syracuseStep 1684559 = 2526839) B2526839
theorem B8533187 : Blo 1120629 8533187 := bstep (se 1 (by rfl) ⟨6399890, by rfl⟩ : syracuseStep 8533187 = 12799781) B12799781
theorem B1684679 : Blo 1120629 1684679 := bstep (se 1 (by rfl) ⟨1263509, by rfl⟩ : syracuseStep 1684679 = 2527019) B2527019
theorem B1684841 : Blo 1120629 1684841 := bstep (se 2 (by rfl) ⟨631815, by rfl⟩ : syracuseStep 1684841 = 1263631) B1263631
theorem B16168355 : Blo 1120629 16168355 := bstep (se 1 (by rfl) ⟨12126266, by rfl⟩ : syracuseStep 16168355 = 24252533) B24252533
theorem B1684919 : Blo 1120629 1684919 := bstep (se 1 (by rfl) ⟨1263689, by rfl⟩ : syracuseStep 1684919 = 2527379) B2527379
theorem B1422775 : Blo 1120629 1422775 := bstep (se 1 (by rfl) ⟨1067081, by rfl⟩ : syracuseStep 1422775 = 2134163) B2134163
theorem B1684955 : Blo 1120629 1684955 := bstep (se 1 (by rfl) ⟨1263716, by rfl⟩ : syracuseStep 1684955 = 2527433) B2527433
theorem B4044269 : Blo 1120629 4044269 := bstep (se 3 (by rfl) ⟨758300, by rfl⟩ : syracuseStep 4044269 = 1516601) B1516601
theorem B2700839 : Blo 1120629 2700839 := bstep (se 1 (by rfl) ⟨2025629, by rfl⟩ : syracuseStep 2700839 = 4051259) B4051259
theorem B3782267 : Blo 1120629 3782267 := bstep (se 1 (by rfl) ⟨2836700, by rfl⟩ : syracuseStep 3782267 = 5673401) B5673401
theorem B3782429 : Blo 1120629 3782429 := bstep (se 3 (by rfl) ⟨709205, by rfl⟩ : syracuseStep 3782429 = 1418411) B1418411
theorem B1685423 : Blo 1120629 1685423 := bstep (se 1 (by rfl) ⟨1264067, by rfl⟩ : syracuseStep 1685423 = 2528135) B2528135
theorem B5552059 : Blo 1120629 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B1685513 : Blo 1120629 1685513 := bstep (se 2 (by rfl) ⟨632067, by rfl⟩ : syracuseStep 1685513 = 1264135) B1264135
theorem B1685543 : Blo 1120629 1685543 := bstep (se 1 (by rfl) ⟨1264157, by rfl⟩ : syracuseStep 1685543 = 2528315) B2528315
theorem B1685627 : Blo 1120629 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B1685753 : Blo 1120629 1685753 := bstep (se 2 (by rfl) ⟨632157, by rfl⟩ : syracuseStep 1685753 = 1264315) B1264315
theorem B1685855 : Blo 1120629 1685855 := bstep (se 1 (by rfl) ⟨1264391, by rfl⟩ : syracuseStep 1685855 = 2528783) B2528783
theorem B1685867 : Blo 1120629 1685867 := bstep (se 1 (by rfl) ⟨1264400, by rfl⟩ : syracuseStep 1685867 = 2528801) B2528801
theorem B3783131 : Blo 1120629 3783131 := bstep (se 1 (by rfl) ⟨2837348, by rfl⟩ : syracuseStep 3783131 = 5674697) B5674697
theorem B1686095 : Blo 1120629 1686095 := bstep (se 1 (by rfl) ⟨1264571, by rfl⟩ : syracuseStep 1686095 = 2529143) B2529143
theorem B1686215 : Blo 1120629 1686215 := bstep (se 1 (by rfl) ⟨1264661, by rfl⟩ : syracuseStep 1686215 = 2529323) B2529323
theorem B1686377 : Blo 1120629 1686377 := bstep (se 2 (by rfl) ⟨632391, by rfl⟩ : syracuseStep 1686377 = 1264783) B1264783
theorem B1686455 : Blo 1120629 1686455 := bstep (se 1 (by rfl) ⟨1264841, by rfl⟩ : syracuseStep 1686455 = 2529683) B2529683
theorem B1686491 : Blo 1120629 1686491 := bstep (se 1 (by rfl) ⟨1264868, by rfl⟩ : syracuseStep 1686491 = 2529737) B2529737
theorem B3783833 : Blo 1120629 3783833 := bstep (se 2 (by rfl) ⟨1418937, by rfl⟩ : syracuseStep 3783833 = 2837875) B2837875
theorem B1260895 : Blo 1120629 1260895 := bstep (se 1 (by rfl) ⟨945671, by rfl⟩ : syracuseStep 1260895 = 1891343) B1891343
theorem B21052853 : Blo 1120629 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B4046345 : Blo 1120629 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B1261255 : Blo 1120629 1261255 := bstep (se 1 (by rfl) ⟨945941, by rfl⟩ : syracuseStep 1261255 = 1891883) B1891883
theorem B8634071 : Blo 1120629 8634071 := bstep (se 1 (by rfl) ⟨6475553, by rfl⟩ : syracuseStep 8634071 = 12951107) B12951107
theorem B16171123 : Blo 1120629 16171123 := bstep (se 1 (by rfl) ⟨12128342, by rfl⟩ : syracuseStep 16171123 = 24256685) B24256685
theorem B3785021 : Blo 1120629 3785021 := bstep (se 3 (by rfl) ⟨709691, by rfl⟩ : syracuseStep 3785021 = 1419383) B1419383
theorem B7192961 : Blo 1120629 7192961 := bstep (se 2 (by rfl) ⟨2697360, by rfl⟩ : syracuseStep 7192961 = 5394721) B5394721
theorem B1262119 : Blo 1120629 1262119 := bstep (se 1 (by rfl) ⟨946589, by rfl⟩ : syracuseStep 1262119 = 1893179) B1893179
theorem B2048591 : Blo 1120629 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B5686199 : Blo 1120629 5686199 := bstep (se 1 (by rfl) ⟨4264649, by rfl⟩ : syracuseStep 5686199 = 8529299) B8529299
theorem B4047887 : Blo 1120629 4047887 := bstep (se 1 (by rfl) ⟨3035915, by rfl⟩ : syracuseStep 4047887 = 6071831) B6071831
theorem B3785885 : Blo 1120629 3785885 := bstep (se 3 (by rfl) ⟨709853, by rfl⟩ : syracuseStep 3785885 = 1419707) B1419707
theorem B15353003 : Blo 1120629 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B34555085 : Blo 1120629 34555085 := bstep (se 3 (by rfl) ⟨6479078, by rfl⟩ : syracuseStep 34555085 = 12958157) B12958157
theorem B14403035 : Blo 1120629 14403035 := bstep (se 1 (by rfl) ⟨10802276, by rfl⟩ : syracuseStep 14403035 = 21604553) B21604553
theorem B3786425 : Blo 1120629 3786425 := bstep (se 2 (by rfl) ⟨1419909, by rfl⟩ : syracuseStep 3786425 = 2839819) B2839819
theorem B3196847 : Blo 1120629 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B1263739 : Blo 1120629 1263739 := bstep (se 1 (by rfl) ⟨947804, by rfl⟩ : syracuseStep 1263739 = 1895609) B1895609
theorem B3787019 : Blo 1120629 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B62310707 : Blo 1120629 62310707 := bstep (se 1 (by rfl) ⟨46733030, by rfl⟩ : syracuseStep 62310707 = 93466061) B93466061
theorem B5687657 : Blo 1120629 5687657 := bstep (se 2 (by rfl) ⟨2132871, by rfl⟩ : syracuseStep 5687657 = 4265743) B4265743
theorem B3787289 : Blo 1120629 3787289 := bstep (se 2 (by rfl) ⟨1420233, by rfl⟩ : syracuseStep 3787289 = 2840467) B2840467
theorem B4803097 : Blo 1120629 4803097 := bstep (se 2 (by rfl) ⟨1801161, by rfl⟩ : syracuseStep 4803097 = 3602323) B3602323
theorem B4803131 : Blo 1120629 4803131 := bstep (se 1 (by rfl) ⟨3602348, by rfl⟩ : syracuseStep 4803131 = 7204697) B7204697
theorem B1264207 : Blo 1120629 1264207 := bstep (se 1 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 1264207 = 1896311) B1896311
theorem B3590867 : Blo 1120629 3590867 := bstep (se 1 (by rfl) ⟨2693150, by rfl⟩ : syracuseStep 3590867 = 5386301) B5386301
theorem B2837207 : Blo 1120629 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B1264603 : Blo 1120629 1264603 := bstep (se 1 (by rfl) ⟨948452, by rfl⟩ : syracuseStep 1264603 = 1896905) B1896905
theorem B3591175 : Blo 1120629 3591175 := bstep (se 1 (by rfl) ⟨2693381, by rfl⟩ : syracuseStep 3591175 = 5386763) B5386763
theorem B1265071 : Blo 1120629 1265071 := bstep (se 1 (by rfl) ⟨948803, by rfl⟩ : syracuseStep 1265071 = 1897607) B1897607
theorem B1822139 : Blo 1120629 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B3689993 : Blo 1120629 3689993 := bstep (se 2 (by rfl) ⟨1383747, by rfl⟩ : syracuseStep 3689993 = 2767495) B2767495
theorem B3788423 : Blo 1120629 3788423 := bstep (se 1 (by rfl) ⟨2841317, by rfl⟩ : syracuseStep 3788423 = 5682635) B5682635
theorem B3788477 : Blo 1120629 3788477 := bstep (se 3 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 3788477 = 1420679) B1420679
theorem B3788639 : Blo 1120629 3788639 := bstep (se 1 (by rfl) ⟨2841479, by rfl⟩ : syracuseStep 3788639 = 5682959) B5682959
theorem B3592097 : Blo 1120629 3592097 := bstep (se 2 (by rfl) ⟨1347036, by rfl⟩ : syracuseStep 3592097 = 2694073) B2694073
theorem B1200091 : Blo 1120629 1200091 := bstep (se 1 (by rfl) ⟨900068, by rfl⟩ : syracuseStep 1200091 = 1800137) B1800137
theorem B3788801 : Blo 1120629 3788801 := bstep (se 2 (by rfl) ⟨1420800, by rfl⟩ : syracuseStep 3788801 = 2841601) B2841601
theorem B3887183 : Blo 1120629 3887183 := bstep (se 1 (by rfl) ⟨2915387, by rfl⟩ : syracuseStep 3887183 = 5830775) B5830775
theorem B3592649 : Blo 1120629 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B3199513 : Blo 1120629 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B3592763 : Blo 1120629 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B3789611 : Blo 1120629 3789611 := bstep (se 1 (by rfl) ⟨2842208, by rfl⟩ : syracuseStep 3789611 = 5684417) B5684417
theorem B7197623 : Blo 1120629 7197623 := bstep (se 1 (by rfl) ⟨5398217, by rfl⟩ : syracuseStep 7197623 = 10796435) B10796435
theorem B3789881 : Blo 1120629 3789881 := bstep (se 2 (by rfl) ⟨1421205, by rfl⟩ : syracuseStep 3789881 = 2842411) B2842411
theorem B2839799 : Blo 1120629 2839799 := bstep (se 1 (by rfl) ⟨2129849, by rfl⟩ : syracuseStep 2839799 = 4259699) B4259699
theorem B3790205 : Blo 1120629 3790205 := bstep (se 3 (by rfl) ⟨710663, by rfl⟩ : syracuseStep 3790205 = 1421327) B1421327
theorem B3593737 : Blo 1120629 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B3790475 : Blo 1120629 3790475 := bstep (se 1 (by rfl) ⟨2842856, by rfl⟩ : syracuseStep 3790475 = 5685713) B5685713
theorem B17258275 : Blo 1120629 17258275 := bstep (se 1 (by rfl) ⟨12943706, by rfl⟩ : syracuseStep 17258275 = 25887413) B25887413
theorem B4052845 : Blo 1120629 4052845 := bstep (se 3 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 4052845 = 1519817) B1519817
theorem B3037103 : Blo 1120629 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B4053149 : Blo 1120629 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B3594557 : Blo 1120629 3594557 := bstep (se 3 (by rfl) ⟨673979, by rfl⟩ : syracuseStep 3594557 = 1347959) B1347959
theorem B3791393 : Blo 1120629 3791393 := bstep (se 2 (by rfl) ⟨1421772, by rfl⟩ : syracuseStep 3791393 = 2843545) B2843545
theorem B2841227 : Blo 1120629 2841227 := bstep (se 1 (by rfl) ⟨2130920, by rfl⟩ : syracuseStep 2841227 = 4261841) B4261841
theorem B3791609 : Blo 1120629 3791609 := bstep (se 2 (by rfl) ⟨1421853, by rfl⟩ : syracuseStep 3791609 = 2843707) B2843707
theorem B2841439 : Blo 1120629 2841439 := bstep (se 1 (by rfl) ⟨2131079, by rfl⟩ : syracuseStep 2841439 = 4262159) B4262159
theorem B1891255 : Blo 1120629 1891255 := bstep (se 1 (by rfl) ⟨1418441, by rfl⟩ : syracuseStep 1891255 = 2836883) B2836883
theorem B3791879 : Blo 1120629 3791879 := bstep (se 1 (by rfl) ⟨2843909, by rfl⟩ : syracuseStep 3791879 = 5687819) B5687819
theorem B3791987 : Blo 1120629 3791987 := bstep (se 1 (by rfl) ⟨2843990, by rfl⟩ : syracuseStep 3791987 = 5687981) B5687981
theorem B1891451 : Blo 1120629 1891451 := bstep (se 1 (by rfl) ⟨1418588, by rfl⟩ : syracuseStep 1891451 = 2837177) B2837177
theorem B3595531 : Blo 1120629 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B19193111 : Blo 1120629 19193111 := bstep (se 1 (by rfl) ⟨14394833, by rfl⟩ : syracuseStep 19193111 = 28789667) B28789667
theorem B3202429 : Blo 1120629 3202429 := bstep (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) B1200911
theorem B3792257 : Blo 1120629 3792257 := bstep (se 2 (by rfl) ⟨1422096, by rfl⟩ : syracuseStep 3792257 = 2844193) B2844193
theorem B1891849 : Blo 1120629 1891849 := bstep (se 2 (by rfl) ⟨709443, by rfl⟩ : syracuseStep 1891849 = 1418887) B1418887
theorem B1892011 : Blo 1120629 1892011 := bstep (se 1 (by rfl) ⟨1419008, by rfl⟩ : syracuseStep 1892011 = 2838017) B2838017
theorem B2842361 : Blo 1120629 2842361 := bstep (se 2 (by rfl) ⟨1065885, by rfl⟩ : syracuseStep 2842361 = 2131771) B2131771
theorem B1892315 : Blo 1120629 1892315 := bstep (se 1 (by rfl) ⟨1419236, by rfl⟩ : syracuseStep 1892315 = 2838473) B2838473
theorem B4317299 : Blo 1120629 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B3793067 : Blo 1120629 3793067 := bstep (se 1 (by rfl) ⟨2844800, by rfl⟩ : syracuseStep 3793067 = 5689601) B5689601
theorem B1892551 : Blo 1120629 1892551 := bstep (se 1 (by rfl) ⟨1419413, by rfl⟩ : syracuseStep 1892551 = 2838827) B2838827
theorem B1892713 : Blo 1120629 1892713 := bstep (se 2 (by rfl) ⟨709767, by rfl⟩ : syracuseStep 1892713 = 1419535) B1419535
theorem B2843009 : Blo 1120629 2843009 := bstep (se 2 (by rfl) ⟨1066128, by rfl⟩ : syracuseStep 2843009 = 2132257) B2132257
theorem B1139279 : Blo 1120629 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B3793607 : Blo 1120629 3793607 := bstep (se 1 (by rfl) ⟨2845205, by rfl⟩ : syracuseStep 3793607 = 5690411) B5690411
theorem B1893307 : Blo 1120629 1893307 := bstep (se 1 (by rfl) ⟨1419980, by rfl⟩ : syracuseStep 1893307 = 2839961) B2839961
theorem B1893415 : Blo 1120629 1893415 := bstep (se 1 (by rfl) ⟨1420061, by rfl⟩ : syracuseStep 1893415 = 2840123) B2840123
theorem B2843819 : Blo 1120629 2843819 := bstep (se 1 (by rfl) ⟨2132864, by rfl⟩ : syracuseStep 2843819 = 4265729) B4265729
theorem B1598663 : Blo 1120629 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B1893739 : Blo 1120629 1893739 := bstep (se 1 (by rfl) ⟨1420304, by rfl⟩ : syracuseStep 1893739 = 2840609) B2840609
theorem B2024923 : Blo 1120629 2024923 := bstep (se 1 (by rfl) ⟨1518692, by rfl⟩ : syracuseStep 2024923 = 3037385) B3037385
theorem B3794471 : Blo 1120629 3794471 := bstep (se 1 (by rfl) ⟨2845853, by rfl⟩ : syracuseStep 3794471 = 5691707) B5691707
theorem B3794579 : Blo 1120629 3794579 := bstep (se 1 (by rfl) ⟨2845934, by rfl⟩ : syracuseStep 3794579 = 5691869) B5691869
theorem B8513261 : Blo 1120629 8513261 := bstep (se 3 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 8513261 = 3192473) B3192473
theorem B14378795 : Blo 1120629 14378795 := bstep (se 1 (by rfl) ⟨10784096, by rfl⟩ : syracuseStep 14378795 = 21568193) B21568193
theorem B3794795 : Blo 1120629 3794795 := bstep (se 1 (by rfl) ⟨2846096, by rfl⟩ : syracuseStep 3794795 = 5692193) B5692193
theorem B3794849 : Blo 1120629 3794849 := bstep (se 2 (by rfl) ⟨1423068, by rfl⟩ : syracuseStep 3794849 = 2846137) B2846137
theorem B1796023 : Blo 1120629 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B2844679 : Blo 1120629 2844679 := bstep (se 1 (by rfl) ⟨2133509, by rfl⟩ : syracuseStep 2844679 = 4267019) B4267019
theorem B2025479 : Blo 1120629 2025479 := bstep (se 1 (by rfl) ⟨1519109, by rfl⟩ : syracuseStep 2025479 = 3038219) B3038219
theorem B6482035 : Blo 1120629 6482035 := bstep (se 1 (by rfl) ⟨4861526, by rfl⟩ : syracuseStep 6482035 = 9723053) B9723053
theorem B1894799 : Blo 1120629 1894799 := bstep (se 1 (by rfl) ⟨1421099, by rfl⟩ : syracuseStep 1894799 = 2842199) B2842199
theorem B2025947 : Blo 1120629 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B3795443 : Blo 1120629 3795443 := bstep (se 1 (by rfl) ⟨2846582, by rfl⟩ : syracuseStep 3795443 = 5693165) B5693165
theorem B1895035 : Blo 1120629 1895035 := bstep (se 1 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 1895035 = 2842553) B2842553
theorem B2845307 : Blo 1120629 2845307 := bstep (se 1 (by rfl) ⟨2133980, by rfl⟩ : syracuseStep 2845307 = 4267961) B4267961
theorem B8514233 : Blo 1120629 8514233 := bstep (se 2 (by rfl) ⟨3192837, by rfl⟩ : syracuseStep 8514233 = 6385675) B6385675
theorem B6384491 : Blo 1120629 6384491 := bstep (se 1 (by rfl) ⟨4788368, by rfl⟩ : syracuseStep 6384491 = 9576737) B9576737
theorem B2845601 : Blo 1120629 2845601 := bstep (se 2 (by rfl) ⟨1067100, by rfl⟩ : syracuseStep 2845601 = 2134201) B2134201
theorem B5991475 : Blo 1120629 5991475 := bstep (se 1 (by rfl) ⟨4493606, by rfl⟩ : syracuseStep 5991475 = 8987213) B8987213
theorem B4255037 : Blo 1120629 4255037 := bstep (se 3 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 4255037 = 1595639) B1595639
theorem B1895899 : Blo 1120629 1895899 := bstep (se 1 (by rfl) ⟨1421924, by rfl⟩ : syracuseStep 1895899 = 2843849) B2843849
theorem B1600987 : Blo 1120629 1600987 := bstep (se 1 (by rfl) ⟨1200740, by rfl⟩ : syracuseStep 1600987 = 2401481) B2401481
theorem B1797689 : Blo 1120629 1797689 := bstep (se 2 (by rfl) ⟨674133, by rfl⟩ : syracuseStep 1797689 = 1348267) B1348267
theorem B4255355 : Blo 1120629 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B8515205 : Blo 1120629 8515205 := bstep (se 4 (by rfl) ⟨798300, by rfl⟩ : syracuseStep 8515205 = 1596601) B1596601
theorem B1797881 : Blo 1120629 1797881 := bstep (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) B1348411
theorem B3600247 : Blo 1120629 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B12152909 : Blo 1120629 12152909 := bstep (se 3 (by rfl) ⟨2278670, by rfl⟩ : syracuseStep 12152909 = 4557341) B4557341
theorem B1896527 : Blo 1120629 1896527 := bstep (se 1 (by rfl) ⟨1422395, by rfl⟩ : syracuseStep 1896527 = 2844791) B2844791
theorem B2158955 : Blo 1120629 2158955 := bstep (se 1 (by rfl) ⟨1619216, by rfl⟩ : syracuseStep 2158955 = 3238433) B3238433
theorem B24310145 : Blo 1120629 24310145 := bstep (se 2 (by rfl) ⟨9116304, by rfl⟩ : syracuseStep 24310145 = 18232609) B18232609
theorem B4551113 : Blo 1120629 4551113 := bstep (se 2 (by rfl) ⟨1706667, by rfl⟩ : syracuseStep 4551113 = 3413335) B3413335
theorem B26604035 : Blo 1120629 26604035 := bstep (se 1 (by rfl) ⟨19953026, by rfl⟩ : syracuseStep 26604035 = 39906053) B39906053
theorem B34599433 : Blo 1120629 34599433 := bstep (se 2 (by rfl) ⟨12974787, by rfl⟩ : syracuseStep 34599433 = 25949575) B25949575
theorem B6386201 : Blo 1120629 6386201 := bstep (se 2 (by rfl) ⟨2394825, by rfl⟩ : syracuseStep 6386201 = 4789651) B4789651
theorem B44331587 : Blo 1120629 44331587 := bstep (se 1 (by rfl) ⟨33248690, by rfl⟩ : syracuseStep 44331587 = 66497381) B66497381
theorem B9597649 : Blo 1120629 9597649 := bstep (se 2 (by rfl) ⟨3599118, by rfl⟩ : syracuseStep 9597649 = 7198237) B7198237
theorem B1897391 : Blo 1120629 1897391 := bstep (se 1 (by rfl) ⟨1423043, by rfl⟩ : syracuseStep 1897391 = 2846087) B2846087
theorem B6058981 : Blo 1120629 6058981 := bstep (se 4 (by rfl) ⟨568029, by rfl⟩ : syracuseStep 6058981 = 1136059) B1136059
theorem B4256783 : Blo 1120629 4256783 := bstep (se 1 (by rfl) ⟨3192587, by rfl⟩ : syracuseStep 4256783 = 6385175) B6385175
theorem B38925461 : Blo 1120629 38925461 := bstep (se 6 (by rfl) ⟨912315, by rfl⟩ : syracuseStep 38925461 = 1824631) B1824631
theorem B3601579 : Blo 1120629 3601579 := bstep (se 1 (by rfl) ⟨2701184, by rfl⟩ : syracuseStep 3601579 = 5402369) B5402369
theorem B3601979 : Blo 1120629 3601979 := bstep (se 1 (by rfl) ⟨2701484, by rfl⟩ : syracuseStep 3601979 = 5402969) B5402969
theorem B1799759 : Blo 1120629 1799759 := bstep (se 1 (by rfl) ⟨1349819, by rfl⟩ : syracuseStep 1799759 = 2699639) B2699639
theorem B9729953 : Blo 1120629 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B2127799 : Blo 1120629 2127799 := bstep (se 1 (by rfl) ⟨1595849, by rfl⟩ : syracuseStep 2127799 = 3191699) B3191699
theorem B9107387 : Blo 1120629 9107387 := bstep (se 1 (by rfl) ⟨6830540, by rfl⟩ : syracuseStep 9107387 = 13661081) B13661081
theorem B8517635 : Blo 1120629 8517635 := bstep (se 1 (by rfl) ⟨6388226, by rfl⟩ : syracuseStep 8517635 = 12776453) B12776453
theorem B4323689 : Blo 1120629 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B9108001 : Blo 1120629 9108001 := bstep (se 2 (by rfl) ⟨3415500, by rfl⟩ : syracuseStep 9108001 = 6831001) B6831001
theorem B4258439 : Blo 1120629 4258439 := bstep (se 1 (by rfl) ⟨3193829, by rfl⟩ : syracuseStep 4258439 = 6387659) B6387659
theorem B6388409 : Blo 1120629 6388409 := bstep (se 2 (by rfl) ⟨2395653, by rfl⟩ : syracuseStep 6388409 = 4791307) B4791307
theorem B2521799 : Blo 1120629 2521799 := bstep (se 1 (by rfl) ⟨1891349, by rfl⟩ : syracuseStep 2521799 = 3782699) B3782699
theorem B72940277 : Blo 1120629 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B4553567 : Blo 1120629 4553567 := bstep (se 1 (by rfl) ⟨3415175, by rfl⟩ : syracuseStep 4553567 = 6830351) B6830351
theorem B8092943 : Blo 1120629 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B2129257 : Blo 1120629 2129257 := bstep (se 2 (by rfl) ⟨798471, by rfl⟩ : syracuseStep 2129257 = 1596943) B1596943
theorem B6389117 : Blo 1120629 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B2522663 : Blo 1120629 2522663 := bstep (se 1 (by rfl) ⟨1891997, by rfl⟩ : syracuseStep 2522663 = 3783995) B3783995
theorem B4259425 : Blo 1120629 4259425 := bstep (se 2 (by rfl) ⟨1597284, by rfl⟩ : syracuseStep 4259425 = 3194569) B3194569
theorem B28802789 : Blo 1120629 28802789 := bstep (se 4 (by rfl) ⟨2700261, by rfl⟩ : syracuseStep 28802789 = 5400523) B5400523
theorem B2522987 : Blo 1120629 2522987 := bstep (se 1 (by rfl) ⟨1892240, by rfl⟩ : syracuseStep 2522987 = 3784481) B3784481
theorem B2523041 : Blo 1120629 2523041 := bstep (se 2 (by rfl) ⟨946140, by rfl⟩ : syracuseStep 2523041 = 1892281) B1892281
theorem B3407791 : Blo 1120629 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B1704041 : Blo 1120629 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B21561497 : Blo 1120629 21561497 := bstep (se 2 (by rfl) ⟨8085561, by rfl⟩ : syracuseStep 21561497 = 16171123) B16171123
theorem B2523347 : Blo 1120629 2523347 := bstep (se 1 (by rfl) ⟨1892510, by rfl⟩ : syracuseStep 2523347 = 3785021) B3785021
theorem B2523401 : Blo 1120629 2523401 := bstep (se 2 (by rfl) ⟨946275, by rfl⟩ : syracuseStep 2523401 = 1892551) B1892551
theorem B2523617 : Blo 1120629 2523617 := bstep (se 2 (by rfl) ⟨946356, by rfl⟩ : syracuseStep 2523617 = 1892713) B1892713
theorem B2523923 : Blo 1120629 2523923 := bstep (se 1 (by rfl) ⟨1892942, by rfl⟩ : syracuseStep 2523923 = 3785885) B3785885
theorem B23036723 : Blo 1120629 23036723 := bstep (se 1 (by rfl) ⟨17277542, by rfl⟩ : syracuseStep 23036723 = 34555085) B34555085
theorem B9602023 : Blo 1120629 9602023 := bstep (se 1 (by rfl) ⟨7201517, by rfl⟩ : syracuseStep 9602023 = 14403035) B14403035
theorem B2524283 : Blo 1120629 2524283 := bstep (se 1 (by rfl) ⟨1893212, by rfl⟩ : syracuseStep 2524283 = 3786425) B3786425
theorem B2524409 : Blo 1120629 2524409 := bstep (se 2 (by rfl) ⟨946653, by rfl⟩ : syracuseStep 2524409 = 1893307) B1893307
theorem B2524553 : Blo 1120629 2524553 := bstep (se 2 (by rfl) ⟨946707, by rfl⟩ : syracuseStep 2524553 = 1893415) B1893415
theorem B1705415 : Blo 1120629 1705415 := bstep (se 1 (by rfl) ⟨1279061, by rfl⟩ : syracuseStep 1705415 = 2558123) B2558123
theorem B2524679 : Blo 1120629 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B2459297 : Blo 1120629 2459297 := bstep (se 2 (by rfl) ⟨922236, by rfl⟩ : syracuseStep 2459297 = 1844473) B1844473
theorem B2524859 : Blo 1120629 2524859 := bstep (se 1 (by rfl) ⟨1893644, by rfl⟩ : syracuseStep 2524859 = 3787289) B3787289
theorem B2393911 : Blo 1120629 2393911 := bstep (se 1 (by rfl) ⟨1795433, by rfl⟩ : syracuseStep 2393911 = 3590867) B3590867
theorem B2524985 : Blo 1120629 2524985 := bstep (se 2 (by rfl) ⟨946869, by rfl⟩ : syracuseStep 2524985 = 1893739) B1893739
theorem B1214759 : Blo 1120629 1214759 := bstep (se 1 (by rfl) ⟨911069, by rfl⟩ : syracuseStep 1214759 = 1822139) B1822139
theorem B2525615 : Blo 1120629 2525615 := bstep (se 1 (by rfl) ⟨1894211, by rfl⟩ : syracuseStep 2525615 = 3788423) B3788423
theorem B4262327 : Blo 1120629 4262327 := bstep (se 1 (by rfl) ⟨3196745, by rfl⟩ : syracuseStep 4262327 = 6393491) B6393491
theorem B2525651 : Blo 1120629 2525651 := bstep (se 1 (by rfl) ⟨1894238, by rfl⟩ : syracuseStep 2525651 = 3788477) B3788477
theorem B2525759 : Blo 1120629 2525759 := bstep (se 1 (by rfl) ⟨1894319, by rfl⟩ : syracuseStep 2525759 = 3788639) B3788639
theorem B2394697 : Blo 1120629 2394697 := bstep (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) B1796023
theorem B2394731 : Blo 1120629 2394731 := bstep (se 1 (by rfl) ⟨1796048, by rfl⟩ : syracuseStep 2394731 = 3592097) B3592097
theorem B2525867 : Blo 1120629 2525867 := bstep (se 1 (by rfl) ⟨1894400, by rfl⟩ : syracuseStep 2525867 = 3788801) B3788801
theorem B2591455 : Blo 1120629 2591455 := bstep (se 1 (by rfl) ⟨1943591, by rfl⟩ : syracuseStep 2591455 = 3887183) B3887183
theorem B4262827 : Blo 1120629 4262827 := bstep (se 1 (by rfl) ⟨3197120, by rfl⟩ : syracuseStep 4262827 = 6394241) B6394241
theorem B2395099 : Blo 1120629 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B2395175 : Blo 1120629 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B4263101 : Blo 1120629 4263101 := bstep (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) B1598663
theorem B2526407 : Blo 1120629 2526407 := bstep (se 1 (by rfl) ⟨1894805, by rfl⟩ : syracuseStep 2526407 = 3789611) B3789611
theorem B4263131 : Blo 1120629 4263131 := bstep (se 1 (by rfl) ⟨3197348, by rfl⟩ : syracuseStep 4263131 = 6394697) B6394697
theorem B2526587 : Blo 1120629 2526587 := bstep (se 1 (by rfl) ⟨1894940, by rfl⟩ : syracuseStep 2526587 = 3789881) B3789881
theorem B2526713 : Blo 1120629 2526713 := bstep (se 2 (by rfl) ⟨947517, by rfl⟩ : syracuseStep 2526713 = 1895035) B1895035
theorem B2526803 : Blo 1120629 2526803 := bstep (se 1 (by rfl) ⟨1895102, by rfl⟩ : syracuseStep 2526803 = 3790205) B3790205
theorem B2526983 : Blo 1120629 2526983 := bstep (se 1 (by rfl) ⟨1895237, by rfl⟩ : syracuseStep 2526983 = 3790475) B3790475
theorem B4788233 : Blo 1120629 4788233 := bstep (se 2 (by rfl) ⟨1795587, by rfl⟩ : syracuseStep 4788233 = 3591175) B3591175
theorem B2527595 : Blo 1120629 2527595 := bstep (se 1 (by rfl) ⟨1895696, by rfl⟩ : syracuseStep 2527595 = 3791393) B3791393
theorem B2527739 : Blo 1120629 2527739 := bstep (se 1 (by rfl) ⟨1895804, by rfl⟩ : syracuseStep 2527739 = 3791609) B3791609
theorem B2527865 : Blo 1120629 2527865 := bstep (se 2 (by rfl) ⟨947949, by rfl⟩ : syracuseStep 2527865 = 1895899) B1895899
theorem B2134649 : Blo 1120629 2134649 := bstep (se 2 (by rfl) ⟨800493, by rfl⟩ : syracuseStep 2134649 = 1600987) B1600987
theorem B14389913 : Blo 1120629 14389913 := bstep (se 2 (by rfl) ⟨5396217, by rfl⟩ : syracuseStep 14389913 = 10792435) B10792435
theorem B2527919 : Blo 1120629 2527919 := bstep (se 1 (by rfl) ⟨1895939, by rfl⟩ : syracuseStep 2527919 = 3791879) B3791879
theorem B2527991 : Blo 1120629 2527991 := bstep (se 1 (by rfl) ⟨1895993, by rfl⟩ : syracuseStep 2527991 = 3791987) B3791987
theorem B2528171 : Blo 1120629 2528171 := bstep (se 1 (by rfl) ⟨1896128, by rfl⟩ : syracuseStep 2528171 = 3792257) B3792257
theorem B8524925 : Blo 1120629 8524925 := bstep (se 3 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 8524925 = 3196847) B3196847
theorem B6821009 : Blo 1120629 6821009 := bstep (se 2 (by rfl) ⟨2557878, by rfl⟩ : syracuseStep 6821009 = 5115757) B5115757
theorem B32314565 : Blo 1120629 32314565 := bstep (se 4 (by rfl) ⟨3029490, by rfl⟩ : syracuseStep 32314565 = 6058981) B6058981
theorem B2528711 : Blo 1120629 2528711 := bstep (se 1 (by rfl) ⟨1896533, by rfl⟩ : syracuseStep 2528711 = 3793067) B3793067
theorem B2529071 : Blo 1120629 2529071 := bstep (se 1 (by rfl) ⟨1896803, by rfl⟩ : syracuseStep 2529071 = 3793607) B3793607
theorem B4266017 : Blo 1120629 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B2529647 : Blo 1120629 2529647 := bstep (se 1 (by rfl) ⟨1897235, by rfl⟩ : syracuseStep 2529647 = 3794471) B3794471
theorem B1120679 : Blo 1120629 1120679 := bstep (se 1 (by rfl) ⟨840509, by rfl⟩ : syracuseStep 1120679 = 1681019) B1681019
theorem B2529719 : Blo 1120629 2529719 := bstep (se 1 (by rfl) ⟨1897289, by rfl⟩ : syracuseStep 2529719 = 3794579) B3794579
theorem B5675507 : Blo 1120629 5675507 := bstep (se 1 (by rfl) ⟨4256630, by rfl⟩ : syracuseStep 5675507 = 8513261) B8513261
theorem B1120763 : Blo 1120629 1120763 := bstep (se 1 (by rfl) ⟨840572, by rfl⟩ : syracuseStep 1120763 = 1681145) B1681145
theorem B1120831 : Blo 1120629 1120831 := bstep (se 1 (by rfl) ⟨840623, by rfl⟩ : syracuseStep 1120831 = 1681247) B1681247
theorem B1120839 : Blo 1120629 1120839 := bstep (se 1 (by rfl) ⟨840629, by rfl⟩ : syracuseStep 1120839 = 1681259) B1681259
theorem B2529863 : Blo 1120629 2529863 := bstep (se 1 (by rfl) ⟨1897397, by rfl⟩ : syracuseStep 2529863 = 3794795) B3794795
theorem B2529899 : Blo 1120629 2529899 := bstep (se 1 (by rfl) ⟨1897424, by rfl⟩ : syracuseStep 2529899 = 3794849) B3794849
theorem B1350319 : Blo 1120629 1350319 := bstep (se 1 (by rfl) ⟨1012739, by rfl⟩ : syracuseStep 1350319 = 2025479) B2025479
theorem B1120991 : Blo 1120629 1120991 := bstep (se 1 (by rfl) ⟨840743, by rfl⟩ : syracuseStep 1120991 = 1681487) B1681487
theorem B36936485 : Blo 1120629 36936485 := bstep (se 4 (by rfl) ⟨3462795, by rfl⟩ : syracuseStep 36936485 = 6925591) B6925591
theorem B1121071 : Blo 1120629 1121071 := bstep (se 1 (by rfl) ⟨840803, by rfl⟩ : syracuseStep 1121071 = 1681607) B1681607
theorem B1121179 : Blo 1120629 1121179 := bstep (se 1 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 1121179 = 1681769) B1681769
theorem B1121231 : Blo 1120629 1121231 := bstep (se 1 (by rfl) ⟨840923, by rfl⟩ : syracuseStep 1121231 = 1681847) B1681847
theorem B1121255 : Blo 1120629 1121255 := bstep (se 1 (by rfl) ⟨840941, by rfl⟩ : syracuseStep 1121255 = 1681883) B1681883
theorem B1350631 : Blo 1120629 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B2530295 : Blo 1120629 2530295 := bstep (se 1 (by rfl) ⟨1897721, by rfl⟩ : syracuseStep 2530295 = 3795443) B3795443
theorem B5676155 : Blo 1120629 5676155 := bstep (se 1 (by rfl) ⟨4257116, by rfl⟩ : syracuseStep 5676155 = 8514233) B8514233
theorem B1121567 : Blo 1120629 1121567 := bstep (se 1 (by rfl) ⟨841175, by rfl⟩ : syracuseStep 1121567 = 1682351) B1682351
theorem B1121627 : Blo 1120629 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B4791649 : Blo 1120629 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B1121647 : Blo 1120629 1121647 := bstep (se 1 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 1121647 = 1682471) B1682471
theorem B1121703 : Blo 1120629 1121703 := bstep (se 1 (by rfl) ⟨841277, by rfl⟩ : syracuseStep 1121703 = 1682555) B1682555
theorem B1121787 : Blo 1120629 1121787 := bstep (se 1 (by rfl) ⟨841340, by rfl⟩ : syracuseStep 1121787 = 1682681) B1682681
theorem B1121855 : Blo 1120629 1121855 := bstep (se 1 (by rfl) ⟨841391, by rfl⟩ : syracuseStep 1121855 = 1682783) B1682783
theorem B1121863 : Blo 1120629 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B4791923 : Blo 1120629 4791923 := bstep (se 1 (by rfl) ⟨3593942, by rfl⟩ : syracuseStep 4791923 = 7187885) B7187885
theorem B1122015 : Blo 1120629 1122015 := bstep (se 1 (by rfl) ⟨841511, by rfl⟩ : syracuseStep 1122015 = 1683023) B1683023
theorem B5676803 : Blo 1120629 5676803 := bstep (se 1 (by rfl) ⟨4257602, by rfl⟩ : syracuseStep 5676803 = 8515205) B8515205
theorem B1122095 : Blo 1120629 1122095 := bstep (se 1 (by rfl) ⟨841571, by rfl⟩ : syracuseStep 1122095 = 1683143) B1683143
theorem B1384271 : Blo 1120629 1384271 := bstep (se 1 (by rfl) ⟨1038203, by rfl⟩ : syracuseStep 1384271 = 2076407) B2076407
theorem B1122203 : Blo 1120629 1122203 := bstep (se 1 (by rfl) ⟨841652, by rfl⟩ : syracuseStep 1122203 = 1683305) B1683305
theorem B34611137 : Blo 1120629 34611137 := bstep (se 2 (by rfl) ⟨12979176, by rfl⟩ : syracuseStep 34611137 = 25958353) B25958353
theorem B1122255 : Blo 1120629 1122255 := bstep (se 1 (by rfl) ⟨841691, by rfl⟩ : syracuseStep 1122255 = 1683383) B1683383
theorem B1122279 : Blo 1120629 1122279 := bstep (se 1 (by rfl) ⟨841709, by rfl⟩ : syracuseStep 1122279 = 1683419) B1683419
theorem B8101939 : Blo 1120629 8101939 := bstep (se 1 (by rfl) ⟨6076454, by rfl⟩ : syracuseStep 8101939 = 12152909) B12152909
theorem B21569651 : Blo 1120629 21569651 := bstep (se 1 (by rfl) ⟨16177238, by rfl⟩ : syracuseStep 21569651 = 32354477) B32354477
theorem B1122591 : Blo 1120629 1122591 := bstep (se 1 (by rfl) ⟨841943, by rfl⟩ : syracuseStep 1122591 = 1683887) B1683887
theorem B17736023 : Blo 1120629 17736023 := bstep (se 1 (by rfl) ⟨13302017, by rfl⟩ : syracuseStep 17736023 = 26604035) B26604035
theorem B1122651 : Blo 1120629 1122651 := bstep (se 1 (by rfl) ⟨841988, by rfl⟩ : syracuseStep 1122651 = 1683977) B1683977
theorem B1122671 : Blo 1120629 1122671 := bstep (se 1 (by rfl) ⟨842003, by rfl⟩ : syracuseStep 1122671 = 1684007) B1684007
theorem B1122727 : Blo 1120629 1122727 := bstep (se 1 (by rfl) ⟨842045, by rfl⟩ : syracuseStep 1122727 = 1684091) B1684091
theorem B1122811 : Blo 1120629 1122811 := bstep (se 1 (by rfl) ⟨842108, by rfl⟩ : syracuseStep 1122811 = 1684217) B1684217
theorem B1122879 : Blo 1120629 1122879 := bstep (se 1 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 1122879 = 1684319) B1684319
theorem B1122887 : Blo 1120629 1122887 := bstep (se 1 (by rfl) ⟨842165, by rfl⟩ : syracuseStep 1122887 = 1684331) B1684331
theorem B1123039 : Blo 1120629 1123039 := bstep (se 1 (by rfl) ⟨842279, by rfl⟩ : syracuseStep 1123039 = 1684559) B1684559
theorem B1123119 : Blo 1120629 1123119 := bstep (se 1 (by rfl) ⟨842339, by rfl⟩ : syracuseStep 1123119 = 1684679) B1684679
theorem B1123227 : Blo 1120629 1123227 := bstep (se 1 (by rfl) ⟨842420, by rfl⟩ : syracuseStep 1123227 = 1684841) B1684841
theorem B1123279 : Blo 1120629 1123279 := bstep (se 1 (by rfl) ⟨842459, by rfl⟩ : syracuseStep 1123279 = 1684919) B1684919
theorem B1123303 : Blo 1120629 1123303 := bstep (se 1 (by rfl) ⟨842477, by rfl⟩ : syracuseStep 1123303 = 1684955) B1684955
theorem B2696179 : Blo 1120629 2696179 := bstep (se 1 (by rfl) ⟨2022134, by rfl⟩ : syracuseStep 2696179 = 4044269) B4044269
theorem B2401319 : Blo 1120629 2401319 := bstep (se 1 (by rfl) ⟨1800989, by rfl⟩ : syracuseStep 2401319 = 3601979) B3601979
theorem B1123615 : Blo 1120629 1123615 := bstep (se 1 (by rfl) ⟨842711, by rfl⟩ : syracuseStep 1123615 = 1685423) B1685423
theorem B6071591 : Blo 1120629 6071591 := bstep (se 1 (by rfl) ⟨4553693, by rfl⟩ : syracuseStep 6071591 = 9107387) B9107387
theorem B5678423 : Blo 1120629 5678423 := bstep (se 1 (by rfl) ⟨4258817, by rfl⟩ : syracuseStep 5678423 = 8517635) B8517635
theorem B1123675 : Blo 1120629 1123675 := bstep (se 1 (by rfl) ⟨842756, by rfl⟩ : syracuseStep 1123675 = 1685513) B1685513
theorem B9839981 : Blo 1120629 9839981 := bstep (se 3 (by rfl) ⟨1844996, by rfl⟩ : syracuseStep 9839981 = 3689993) B3689993
theorem B1123695 : Blo 1120629 1123695 := bstep (se 1 (by rfl) ⟨842771, by rfl⟩ : syracuseStep 1123695 = 1685543) B1685543
theorem B1123751 : Blo 1120629 1123751 := bstep (se 1 (by rfl) ⟨842813, by rfl⟩ : syracuseStep 1123751 = 1685627) B1685627
theorem B1123835 : Blo 1120629 1123835 := bstep (se 1 (by rfl) ⟨842876, by rfl⟩ : syracuseStep 1123835 = 1685753) B1685753
theorem B1123903 : Blo 1120629 1123903 := bstep (se 1 (by rfl) ⟨842927, by rfl⟩ : syracuseStep 1123903 = 1685855) B1685855
theorem B1123911 : Blo 1120629 1123911 := bstep (se 1 (by rfl) ⟨842933, by rfl⟩ : syracuseStep 1123911 = 1685867) B1685867
theorem B4794041 : Blo 1120629 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B1124063 : Blo 1120629 1124063 := bstep (se 1 (by rfl) ⟨843047, by rfl⟩ : syracuseStep 1124063 = 1686095) B1686095
theorem B1681193 : Blo 1120629 1681193 := bstep (se 2 (by rfl) ⟨630447, by rfl⟩ : syracuseStep 1681193 = 1260895) B1260895
theorem B1681199 : Blo 1120629 1681199 := bstep (se 1 (by rfl) ⟨1260899, by rfl⟩ : syracuseStep 1681199 = 2521799) B2521799
theorem B1124143 : Blo 1120629 1124143 := bstep (se 1 (by rfl) ⟨843107, by rfl⟩ : syracuseStep 1124143 = 1686215) B1686215
theorem B4269905 : Blo 1120629 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B1124251 : Blo 1120629 1124251 := bstep (se 1 (by rfl) ⟨843188, by rfl⟩ : syracuseStep 1124251 = 1686377) B1686377
theorem B1124303 : Blo 1120629 1124303 := bstep (se 1 (by rfl) ⟨843227, by rfl⟩ : syracuseStep 1124303 = 1686455) B1686455
theorem B1124327 : Blo 1120629 1124327 := bstep (se 1 (by rfl) ⟨843245, by rfl⟩ : syracuseStep 1124327 = 1686491) B1686491
theorem B4794349 : Blo 1120629 4794349 := bstep (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) B1797881
theorem B5679233 : Blo 1120629 5679233 := bstep (se 2 (by rfl) ⟨2129712, by rfl⟩ : syracuseStep 5679233 = 4259425) B4259425
theorem B1681673 : Blo 1120629 1681673 := bstep (se 2 (by rfl) ⟨630627, by rfl⟩ : syracuseStep 1681673 = 1261255) B1261255
theorem B14035235 : Blo 1120629 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B2697563 : Blo 1120629 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B1681775 : Blo 1120629 1681775 := bstep (se 1 (by rfl) ⟨1261331, by rfl⟩ : syracuseStep 1681775 = 2522663) B2522663
theorem B1681991 : Blo 1120629 1681991 := bstep (se 1 (by rfl) ⟨1261493, by rfl⟩ : syracuseStep 1681991 = 2522987) B2522987
theorem B1682027 : Blo 1120629 1682027 := bstep (se 1 (by rfl) ⟨1261520, by rfl⟩ : syracuseStep 1682027 = 2523041) B2523041
theorem B1420087 : Blo 1120629 1420087 := bstep (se 1 (by rfl) ⟨1065065, by rfl⟩ : syracuseStep 1420087 = 2130131) B2130131
theorem B1682255 : Blo 1120629 1682255 := bstep (se 1 (by rfl) ⟨1261691, by rfl⟩ : syracuseStep 1682255 = 2523383) B2523383
theorem B5680043 : Blo 1120629 5680043 := bstep (se 1 (by rfl) ⟨4260032, by rfl⟩ : syracuseStep 5680043 = 8520065) B8520065
theorem B4795307 : Blo 1120629 4795307 := bstep (se 1 (by rfl) ⟨3596480, by rfl⟩ : syracuseStep 4795307 = 7192961) B7192961
theorem B1682651 : Blo 1120629 1682651 := bstep (se 1 (by rfl) ⟨1261988, by rfl⟩ : syracuseStep 1682651 = 2523977) B2523977
theorem B1420507 : Blo 1120629 1420507 := bstep (se 1 (by rfl) ⟨1065380, by rfl⟩ : syracuseStep 1420507 = 2130761) B2130761
theorem B2698591 : Blo 1120629 2698591 := bstep (se 1 (by rfl) ⟨2023943, by rfl⟩ : syracuseStep 2698591 = 4047887) B4047887
theorem B1682825 : Blo 1120629 1682825 := bstep (se 2 (by rfl) ⟨631059, by rfl⟩ : syracuseStep 1682825 = 1262119) B1262119
theorem B10235335 : Blo 1120629 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B1683179 : Blo 1120629 1683179 := bstep (se 1 (by rfl) ⟨1262384, by rfl⟩ : syracuseStep 1683179 = 2524769) B2524769
theorem B6074119 : Blo 1120629 6074119 := bstep (se 1 (by rfl) ⟨4555589, by rfl⟩ : syracuseStep 6074119 = 9111179) B9111179
theorem B12136301 : Blo 1120629 12136301 := bstep (se 3 (by rfl) ⟨2275556, by rfl⟩ : syracuseStep 12136301 = 4551113) B4551113
theorem B1683407 : Blo 1120629 1683407 := bstep (se 1 (by rfl) ⟨1262555, by rfl⟩ : syracuseStep 1683407 = 2525111) B2525111
theorem B5681177 : Blo 1120629 5681177 := bstep (se 2 (by rfl) ⟨2130441, by rfl⟩ : syracuseStep 5681177 = 4260883) B4260883
theorem B1683803 : Blo 1120629 1683803 := bstep (se 1 (by rfl) ⟨1262852, by rfl⟩ : syracuseStep 1683803 = 2525705) B2525705
theorem B7188911 : Blo 1120629 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B1684031 : Blo 1120629 1684031 := bstep (se 1 (by rfl) ⟨1263023, by rfl⟩ : syracuseStep 1684031 = 2526047) B2526047
theorem B2699897 : Blo 1120629 2699897 := bstep (se 2 (by rfl) ⟨1012461, by rfl⟩ : syracuseStep 2699897 = 2024923) B2024923
theorem B1684151 : Blo 1120629 1684151 := bstep (se 1 (by rfl) ⟨1263113, by rfl⟩ : syracuseStep 1684151 = 2526227) B2526227
theorem B1422127 : Blo 1120629 1422127 := bstep (se 1 (by rfl) ⟨1066595, by rfl⟩ : syracuseStep 1422127 = 2133191) B2133191
theorem B1684379 : Blo 1120629 1684379 := bstep (se 1 (by rfl) ⟨1263284, by rfl⟩ : syracuseStep 1684379 = 2526569) B2526569
theorem B3192007 : Blo 1120629 3192007 := bstep (se 1 (by rfl) ⟨2394005, by rfl⟩ : syracuseStep 3192007 = 4788011) B4788011
theorem B3192041 : Blo 1120629 3192041 := bstep (se 2 (by rfl) ⟨1197015, by rfl⟩ : syracuseStep 3192041 = 2394031) B2394031
theorem B1422623 : Blo 1120629 1422623 := bstep (se 1 (by rfl) ⟨1066967, by rfl⟩ : syracuseStep 1422623 = 2133935) B2133935
theorem B1684775 : Blo 1120629 1684775 := bstep (se 1 (by rfl) ⟨1263581, by rfl⟩ : syracuseStep 1684775 = 2527163) B2527163
theorem B1684859 : Blo 1120629 1684859 := bstep (se 1 (by rfl) ⟨1263644, by rfl⟩ : syracuseStep 1684859 = 2527289) B2527289
theorem B1684985 : Blo 1120629 1684985 := bstep (se 2 (by rfl) ⟨631869, by rfl⟩ : syracuseStep 1684985 = 1263739) B1263739
theorem B2078303 : Blo 1120629 2078303 := bstep (se 1 (by rfl) ⟨1558727, by rfl⟩ : syracuseStep 2078303 = 3117455) B3117455
theorem B1685087 : Blo 1120629 1685087 := bstep (se 1 (by rfl) ⟨1263815, by rfl⟩ : syracuseStep 1685087 = 2527631) B2527631
theorem B1685303 : Blo 1120629 1685303 := bstep (se 1 (by rfl) ⟨1263977, by rfl⟩ : syracuseStep 1685303 = 2527955) B2527955
theorem B4798415 : Blo 1120629 4798415 := bstep (se 1 (by rfl) ⟨3598811, by rfl⟩ : syracuseStep 4798415 = 7197623) B7197623
theorem B6404129 : Blo 1120629 6404129 := bstep (se 2 (by rfl) ⟨2401548, by rfl⟩ : syracuseStep 6404129 = 4803097) B4803097
theorem B1685609 : Blo 1120629 1685609 := bstep (se 2 (by rfl) ⟨632103, by rfl⟩ : syracuseStep 1685609 = 1264207) B1264207
theorem B3783023 : Blo 1120629 3783023 := bstep (se 1 (by rfl) ⟨2837267, by rfl⟩ : syracuseStep 3783023 = 5674535) B5674535
theorem B1685927 : Blo 1120629 1685927 := bstep (se 1 (by rfl) ⟨1264445, by rfl⟩ : syracuseStep 1685927 = 2528891) B2528891
theorem B3193339 : Blo 1120629 3193339 := bstep (se 1 (by rfl) ⟨2395004, by rfl⟩ : syracuseStep 3193339 = 4790009) B4790009
theorem B1686011 : Blo 1120629 1686011 := bstep (se 1 (by rfl) ⟨1264508, by rfl⟩ : syracuseStep 1686011 = 2529017) B2529017
theorem B1686137 : Blo 1120629 1686137 := bstep (se 2 (by rfl) ⟨632301, by rfl⟩ : syracuseStep 1686137 = 1264603) B1264603
theorem B1686191 : Blo 1120629 1686191 := bstep (se 1 (by rfl) ⟨1264643, by rfl⟩ : syracuseStep 1686191 = 2529287) B2529287
theorem B1686239 : Blo 1120629 1686239 := bstep (se 1 (by rfl) ⟨1264679, by rfl⟩ : syracuseStep 1686239 = 2529359) B2529359
theorem B2702099 : Blo 1120629 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B5684093 : Blo 1120629 5684093 := bstep (se 3 (by rfl) ⟨1065767, by rfl⟩ : syracuseStep 5684093 = 2131535) B2131535
theorem B4799357 : Blo 1120629 4799357 := bstep (se 3 (by rfl) ⟨899879, by rfl⟩ : syracuseStep 4799357 = 1799759) B1799759
theorem B1686503 : Blo 1120629 1686503 := bstep (se 1 (by rfl) ⟨1264877, by rfl⟩ : syracuseStep 1686503 = 2529755) B2529755
theorem B1686761 : Blo 1120629 1686761 := bstep (se 2 (by rfl) ⟨632535, by rfl⟩ : syracuseStep 1686761 = 1265071) B1265071
theorem B1686815 : Blo 1120629 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B1260967 : Blo 1120629 1260967 := bstep (se 1 (by rfl) ⟨945725, by rfl⟩ : syracuseStep 1260967 = 1891451) B1891451
theorem B12795407 : Blo 1120629 12795407 := bstep (se 1 (by rfl) ⟨9596555, by rfl⟩ : syracuseStep 12795407 = 19193111) B19193111
theorem B3784427 : Blo 1120629 3784427 := bstep (se 1 (by rfl) ⟨2838320, by rfl⟩ : syracuseStep 3784427 = 5676641) B5676641
theorem B2735927 : Blo 1120629 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B5685065 : Blo 1120629 5685065 := bstep (se 2 (by rfl) ⟨2131899, by rfl⟩ : syracuseStep 5685065 = 4263799) B4263799
theorem B4800329 : Blo 1120629 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B1261543 : Blo 1120629 1261543 := bstep (se 1 (by rfl) ⟨946157, by rfl⟩ : syracuseStep 1261543 = 1892315) B1892315
theorem B18202643 : Blo 1120629 18202643 := bstep (se 1 (by rfl) ⟨13651982, by rfl⟩ : syracuseStep 18202643 = 27303965) B27303965
theorem B3785399 : Blo 1120629 3785399 := bstep (se 1 (by rfl) ⟨2839049, by rfl⟩ : syracuseStep 3785399 = 5678099) B5678099
theorem B9585485 : Blo 1120629 9585485 := bstep (se 3 (by rfl) ⟨1797278, by rfl⟩ : syracuseStep 9585485 = 3594557) B3594557
theorem B12796865 : Blo 1120629 12796865 := bstep (se 2 (by rfl) ⟨4798824, by rfl⟩ : syracuseStep 12796865 = 9597649) B9597649
theorem B5686361 : Blo 1120629 5686361 := bstep (se 2 (by rfl) ⟨2132385, by rfl⟩ : syracuseStep 5686361 = 4264771) B4264771
theorem B9585863 : Blo 1120629 9585863 := bstep (se 1 (by rfl) ⟨7189397, by rfl⟩ : syracuseStep 9585863 = 14378795) B14378795
theorem B3196199 : Blo 1120629 3196199 := bstep (se 1 (by rfl) ⟨2397149, by rfl⟩ : syracuseStep 3196199 = 4794299) B4794299
theorem B3196255 : Blo 1120629 3196255 := bstep (se 1 (by rfl) ⟨2397191, by rfl⟩ : syracuseStep 3196255 = 4794383) B4794383
theorem B4802105 : Blo 1120629 4802105 := bstep (se 2 (by rfl) ⟨1800789, by rfl⟩ : syracuseStep 4802105 = 3601579) B3601579
theorem B1263199 : Blo 1120629 1263199 := bstep (se 1 (by rfl) ⟨947399, by rfl⟩ : syracuseStep 1263199 = 1894799) B1894799
theorem B414566423 : Blo 1120629 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B2836691 : Blo 1120629 2836691 := bstep (se 1 (by rfl) ⟨2127518, by rfl⟩ : syracuseStep 2836691 = 4255037) B4255037
theorem B1198459 : Blo 1120629 1198459 := bstep (se 1 (by rfl) ⟨898844, by rfl⟩ : syracuseStep 1198459 = 1797689) B1797689
theorem B2836903 : Blo 1120629 2836903 := bstep (se 1 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 2836903 = 4255355) B4255355
theorem B2837065 : Blo 1120629 2837065 := bstep (se 2 (by rfl) ⟨1063899, by rfl⟩ : syracuseStep 2837065 = 2127799) B2127799
theorem B3787343 : Blo 1120629 3787343 := bstep (se 1 (by rfl) ⟨2840507, by rfl⟩ : syracuseStep 3787343 = 5681015) B5681015
theorem B21908069 : Blo 1120629 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B1264351 : Blo 1120629 1264351 := bstep (se 1 (by rfl) ⟨948263, by rfl⟩ : syracuseStep 1264351 = 1896527) B1896527
theorem B2738935 : Blo 1120629 2738935 := bstep (se 1 (by rfl) ⟨2054201, by rfl⟩ : syracuseStep 2738935 = 4108403) B4108403
theorem B3197839 : Blo 1120629 3197839 := bstep (se 1 (by rfl) ⟨2398379, by rfl⟩ : syracuseStep 3197839 = 4796759) B4796759
theorem B16206763 : Blo 1120629 16206763 := bstep (se 1 (by rfl) ⟨12155072, by rfl⟩ : syracuseStep 16206763 = 24310145) B24310145
theorem B19188737 : Blo 1120629 19188737 := bstep (se 2 (by rfl) ⟨7195776, by rfl⟩ : syracuseStep 19188737 = 14391553) B14391553
theorem B14404675 : Blo 1120629 14404675 := bstep (se 1 (by rfl) ⟨10803506, by rfl⟩ : syracuseStep 14404675 = 21607013) B21607013
theorem B1264927 : Blo 1120629 1264927 := bstep (se 1 (by rfl) ⟨948695, by rfl⟩ : syracuseStep 1264927 = 1897391) B1897391
theorem B3001639 : Blo 1120629 3001639 := bstep (se 1 (by rfl) ⟨2251229, by rfl⟩ : syracuseStep 3001639 = 4502459) B4502459
theorem B2837855 : Blo 1120629 2837855 := bstep (se 1 (by rfl) ⟨2128391, by rfl⟩ : syracuseStep 2837855 = 4256783) B4256783
theorem B3198305 : Blo 1120629 3198305 := bstep (se 2 (by rfl) ⟨1199364, by rfl⟩ : syracuseStep 3198305 = 2398729) B2398729
theorem B12144001 : Blo 1120629 12144001 := bstep (se 2 (by rfl) ⟨4554000, by rfl⟩ : syracuseStep 12144001 = 9108001) B9108001
theorem B5688791 : Blo 1120629 5688791 := bstep (se 1 (by rfl) ⟨4266593, by rfl⟩ : syracuseStep 5688791 = 8533187) B8533187
theorem B3788585 : Blo 1120629 3788585 := bstep (se 2 (by rfl) ⟨1420719, by rfl⟩ : syracuseStep 3788585 = 2841439) B2841439
theorem B3198761 : Blo 1120629 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B2838959 : Blo 1120629 2838959 := bstep (se 1 (by rfl) ⟨2129219, by rfl⟩ : syracuseStep 2838959 = 4258439) B4258439
theorem B2839009 : Blo 1120629 2839009 := bstep (se 2 (by rfl) ⟨1064628, by rfl⟩ : syracuseStep 2839009 = 2129257) B2129257
theorem B23024189 : Blo 1120629 23024189 := bstep (se 3 (by rfl) ⟨4317035, by rfl⟩ : syracuseStep 23024189 = 8634071) B8634071
theorem B3035711 : Blo 1120629 3035711 := bstep (se 1 (by rfl) ⟨2276783, by rfl⟩ : syracuseStep 3035711 = 4553567) B4553567
theorem B5395295 : Blo 1120629 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B4543721 : Blo 1120629 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B2839931 : Blo 1120629 2839931 := bstep (se 1 (by rfl) ⟨2129948, by rfl⟩ : syracuseStep 2839931 = 4259897) B4259897
theorem B5395835 : Blo 1120629 5395835 := bstep (se 1 (by rfl) ⟨4046876, by rfl⟩ : syracuseStep 5395835 = 8093753) B8093753
theorem B1365727 : Blo 1120629 1365727 := bstep (se 1 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 1365727 = 2048591) B2048591
theorem B8083255 : Blo 1120629 8083255 := bstep (se 1 (by rfl) ⟨6062441, by rfl⟩ : syracuseStep 8083255 = 12124883) B12124883
theorem B5003063 : Blo 1120629 5003063 := bstep (se 1 (by rfl) ⟨3752297, by rfl⟩ : syracuseStep 5003063 = 7504595) B7504595
theorem B3790799 : Blo 1120629 3790799 := bstep (se 1 (by rfl) ⟨2843099, by rfl⟩ : syracuseStep 3790799 = 5686199) B5686199
theorem B9853435 : Blo 1120629 9853435 := bstep (se 1 (by rfl) ⟨7390076, by rfl⟩ : syracuseStep 9853435 = 14780153) B14780153
theorem B20798209 : Blo 1120629 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B1203023 : Blo 1120629 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B41540471 : Blo 1120629 41540471 := bstep (se 1 (by rfl) ⟨31155353, by rfl⟩ : syracuseStep 41540471 = 62310707) B62310707
theorem B3038077 : Blo 1120629 3038077 := bstep (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) B1139279
theorem B3791771 : Blo 1120629 3791771 := bstep (se 1 (by rfl) ⟨2843828, by rfl⟩ : syracuseStep 3791771 = 5687657) B5687657
theorem B3202087 : Blo 1120629 3202087 := bstep (se 1 (by rfl) ⟨2401565, by rfl⟩ : syracuseStep 3202087 = 4803131) B4803131
theorem B1891471 : Blo 1120629 1891471 := bstep (se 1 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 1891471 = 2837207) B2837207
theorem B2841743 : Blo 1120629 2841743 := bstep (se 1 (by rfl) ⟨2131307, by rfl⟩ : syracuseStep 2841743 = 4262615) B4262615
theorem B1891721 : Blo 1120629 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B8216225 : Blo 1120629 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B4218635 : Blo 1120629 4218635 := bstep (se 1 (by rfl) ⟨3163976, by rfl⟩ : syracuseStep 4218635 = 6327953) B6327953
theorem B1892153 : Blo 1120629 1892153 := bstep (se 2 (by rfl) ⟨709557, by rfl⟩ : syracuseStep 1892153 = 1419115) B1419115
theorem B3792797 : Blo 1120629 3792797 := bstep (se 3 (by rfl) ⟨711149, by rfl⟩ : syracuseStep 3792797 = 1422299) B1422299
theorem B3792905 : Blo 1120629 3792905 := bstep (se 2 (by rfl) ⟨1422339, by rfl⟩ : syracuseStep 3792905 = 2844679) B2844679
theorem B8642713 : Blo 1120629 8642713 := bstep (se 2 (by rfl) ⟨3241017, by rfl⟩ : syracuseStep 8642713 = 6482035) B6482035
theorem B1598059 : Blo 1120629 1598059 := bstep (se 1 (by rfl) ⟨1198544, by rfl⟩ : syracuseStep 1598059 = 2397089) B2397089
theorem B9101969 : Blo 1120629 9101969 := bstep (se 2 (by rfl) ⟨3413238, by rfl⟩ : syracuseStep 9101969 = 6826477) B6826477
theorem B2843383 : Blo 1120629 2843383 := bstep (se 1 (by rfl) ⟨2132537, by rfl⟩ : syracuseStep 2843383 = 4265075) B4265075
theorem B1893199 : Blo 1120629 1893199 := bstep (se 1 (by rfl) ⟨1419899, by rfl⟩ : syracuseStep 1893199 = 2839799) B2839799
theorem B1598287 : Blo 1120629 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B2843687 : Blo 1120629 2843687 := bstep (se 1 (by rfl) ⟨2132765, by rfl⟩ : syracuseStep 2843687 = 4265531) B4265531
theorem B7693555 : Blo 1120629 7693555 := bstep (se 1 (by rfl) ⟨5770166, by rfl⟩ : syracuseStep 7693555 = 11540333) B11540333
theorem B2024735 : Blo 1120629 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B7988633 : Blo 1120629 7988633 := bstep (se 2 (by rfl) ⟨2995737, by rfl⟩ : syracuseStep 7988633 = 5991475) B5991475
theorem B1893881 : Blo 1120629 1893881 := bstep (se 2 (by rfl) ⟨710205, by rfl⟩ : syracuseStep 1893881 = 1420411) B1420411
theorem B1894151 : Blo 1120629 1894151 := bstep (se 1 (by rfl) ⟨1420613, by rfl⟩ : syracuseStep 1894151 = 2841227) B2841227
theorem B2844953 : Blo 1120629 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B1894907 : Blo 1120629 1894907 := bstep (se 1 (by rfl) ⟨1421180, by rfl⟩ : syracuseStep 1894907 = 2842361) B2842361
theorem B1600121 : Blo 1120629 1600121 := bstep (se 2 (by rfl) ⟨600045, by rfl⟩ : syracuseStep 1600121 = 1200091) B1200091
theorem B10775213 : Blo 1120629 10775213 := bstep (se 3 (by rfl) ⟨2020352, by rfl⟩ : syracuseStep 10775213 = 4040705) B4040705
theorem B2878199 : Blo 1120629 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B1895339 : Blo 1120629 1895339 := bstep (se 1 (by rfl) ⟨1421504, by rfl⟩ : syracuseStep 1895339 = 2843009) B2843009
theorem B2845793 : Blo 1120629 2845793 := bstep (se 2 (by rfl) ⟨1067172, by rfl⟩ : syracuseStep 2845793 = 2134345) B2134345
theorem B1797407 : Blo 1120629 1797407 := bstep (se 1 (by rfl) ⟨1348055, by rfl⟩ : syracuseStep 1797407 = 2696111) B2696111
theorem B46132577 : Blo 1120629 46132577 := bstep (se 2 (by rfl) ⟨17299716, by rfl⟩ : syracuseStep 46132577 = 34599433) B34599433
theorem B1895879 : Blo 1120629 1895879 := bstep (se 1 (by rfl) ⟨1421909, by rfl⟩ : syracuseStep 1895879 = 2843819) B2843819
theorem B4615639 : Blo 1120629 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B1896871 : Blo 1120629 1896871 := bstep (se 1 (by rfl) ⟨1422653, by rfl⟩ : syracuseStep 1896871 = 2845307) B2845307
theorem B4256327 : Blo 1120629 4256327 := bstep (se 1 (by rfl) ⟨3192245, by rfl⟩ : syracuseStep 4256327 = 6384491) B6384491
theorem B1897033 : Blo 1120629 1897033 := bstep (se 2 (by rfl) ⟨711387, by rfl⟩ : syracuseStep 1897033 = 1422775) B1422775
theorem B1897067 : Blo 1120629 1897067 := bstep (se 1 (by rfl) ⟨1422800, by rfl⟩ : syracuseStep 1897067 = 2845601) B2845601
theorem B6386633 : Blo 1120629 6386633 := bstep (se 2 (by rfl) ⟨2394987, by rfl⟩ : syracuseStep 6386633 = 4789975) B4789975
theorem B5403793 : Blo 1120629 5403793 := bstep (se 2 (by rfl) ⟨2026422, by rfl⟩ : syracuseStep 5403793 = 4052845) B4052845
theorem B7402745 : Blo 1120629 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B10777981 : Blo 1120629 10777981 := bstep (se 3 (by rfl) ⟨2020871, by rfl⟩ : syracuseStep 10777981 = 4041743) B4041743
theorem B1439303 : Blo 1120629 1439303 := bstep (se 1 (by rfl) ⟨1079477, by rfl⟩ : syracuseStep 1439303 = 2158955) B2158955
theorem B19166867 : Blo 1120629 19166867 := bstep (se 1 (by rfl) ⟨14375150, by rfl⟩ : syracuseStep 19166867 = 28750301) B28750301
theorem B4257467 : Blo 1120629 4257467 := bstep (se 1 (by rfl) ⟨3193100, by rfl⟩ : syracuseStep 4257467 = 6386201) B6386201
theorem B1799867 : Blo 1120629 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B29554391 : Blo 1120629 29554391 := bstep (se 1 (by rfl) ⟨22165793, by rfl⟩ : syracuseStep 29554391 = 44331587) B44331587
theorem B25950307 : Blo 1120629 25950307 := bstep (se 1 (by rfl) ⟨19462730, by rfl⟩ : syracuseStep 25950307 = 38925461) B38925461
theorem B10778903 : Blo 1120629 10778903 := bstep (se 1 (by rfl) ⟨8084177, by rfl⟩ : syracuseStep 10778903 = 16168355) B16168355
theorem B1800559 : Blo 1120629 1800559 := bstep (se 1 (by rfl) ⟨1350419, by rfl⟩ : syracuseStep 1800559 = 2700839) B2700839
theorem B2521511 : Blo 1120629 2521511 := bstep (se 1 (by rfl) ⟨1891133, by rfl⟩ : syracuseStep 2521511 = 3782267) B3782267
theorem B2521619 : Blo 1120629 2521619 := bstep (se 1 (by rfl) ⟨1891214, by rfl⟩ : syracuseStep 2521619 = 3782429) B3782429
theorem B2521673 : Blo 1120629 2521673 := bstep (se 2 (by rfl) ⟨945627, by rfl⟩ : syracuseStep 2521673 = 1891255) B1891255
theorem B6486635 : Blo 1120629 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B92044133 : Blo 1120629 92044133 := bstep (se 4 (by rfl) ⟨8629137, by rfl⟩ : syracuseStep 92044133 = 17258275) B17258275
theorem B2882459 : Blo 1120629 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B2522087 : Blo 1120629 2522087 := bstep (se 1 (by rfl) ⟨1891565, by rfl⟩ : syracuseStep 2522087 = 3783131) B3783131
theorem B4258939 : Blo 1120629 4258939 := bstep (se 1 (by rfl) ⟨3194204, by rfl⟩ : syracuseStep 4258939 = 6388409) B6388409
theorem B48626851 : Blo 1120629 48626851 := bstep (se 1 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 48626851 = 72940277) B72940277
theorem B2522465 : Blo 1120629 2522465 := bstep (se 2 (by rfl) ⟨945924, by rfl⟩ : syracuseStep 2522465 = 1891849) B1891849
theorem B2522555 : Blo 1120629 2522555 := bstep (se 1 (by rfl) ⟨1891916, by rfl⟩ : syracuseStep 2522555 = 3783833) B3783833
theorem B25886213 : Blo 1120629 25886213 := bstep (se 4 (by rfl) ⟨2426832, by rfl⟩ : syracuseStep 25886213 = 4853665) B4853665
theorem B2522681 : Blo 1120629 2522681 := bstep (se 2 (by rfl) ⟨946005, by rfl⟩ : syracuseStep 2522681 = 1892011) B1892011
theorem B4259411 : Blo 1120629 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B19201859 : Blo 1120629 19201859 := bstep (se 1 (by rfl) ⟨14401394, by rfl⟩ : syracuseStep 19201859 = 28802789) B28802789
theorem B2523599 : Blo 1120629 2523599 := bstep (se 1 (by rfl) ⟨1892699, by rfl⟩ : syracuseStep 2523599 = 3785399) B3785399
theorem B6390323 : Blo 1120629 6390323 := bstep (se 1 (by rfl) ⟨4792742, by rfl⟩ : syracuseStep 6390323 = 9585485) B9585485
theorem B6390575 : Blo 1120629 6390575 := bstep (se 1 (by rfl) ⟨4792931, by rfl⟩ : syracuseStep 6390575 = 9585863) B9585863
theorem B2130799 : Blo 1120629 2130799 := bstep (se 1 (by rfl) ⟨1598099, by rfl⟩ : syracuseStep 2130799 = 3196199) B3196199
theorem B2524265 : Blo 1120629 2524265 := bstep (se 2 (by rfl) ⟨946599, by rfl⟩ : syracuseStep 2524265 = 1893199) B1893199
theorem B2131049 : Blo 1120629 2131049 := bstep (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) B1598287
theorem B1639531 : Blo 1120629 1639531 := bstep (se 1 (by rfl) ⟨1229648, by rfl⟩ : syracuseStep 1639531 = 2459297) B2459297
theorem B10258073 : Blo 1120629 10258073 := bstep (se 2 (by rfl) ⟨3846777, by rfl⟩ : syracuseStep 10258073 = 7693555) B7693555
theorem B2524895 : Blo 1120629 2524895 := bstep (se 1 (by rfl) ⟨1893671, by rfl⟩ : syracuseStep 2524895 = 3787343) B3787343
theorem B4261673 : Blo 1120629 4261673 := bstep (se 2 (by rfl) ⟨1598127, by rfl⟩ : syracuseStep 4261673 = 3196255) B3196255
theorem B9602981 : Blo 1120629 9602981 := bstep (se 4 (by rfl) ⟨900279, by rfl⟩ : syracuseStep 9602981 = 1800559) B1800559
theorem B6391781 : Blo 1120629 6391781 := bstep (se 4 (by rfl) ⟨599229, by rfl⟩ : syracuseStep 6391781 = 1198459) B1198459
theorem B14387453 : Blo 1120629 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B2525723 : Blo 1120629 2525723 := bstep (se 1 (by rfl) ⟨1894292, by rfl⟩ : syracuseStep 2525723 = 3788585) B3788585
theorem B2132507 : Blo 1120629 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B6392465 : Blo 1120629 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B8522981 : Blo 1120629 8522981 := bstep (se 4 (by rfl) ⟨799029, by rfl⟩ : syracuseStep 8522981 = 1598059) B1598059
theorem B4263785 : Blo 1120629 4263785 := bstep (se 2 (by rfl) ⟨1598919, by rfl⟩ : syracuseStep 4263785 = 3197839) B3197839
theorem B2527199 : Blo 1120629 2527199 := bstep (se 1 (by rfl) ⟨1895399, by rfl⟩ : syracuseStep 2527199 = 3790799) B3790799
theorem B19206233 : Blo 1120629 19206233 := bstep (se 2 (by rfl) ⟨7202337, by rfl⟩ : syracuseStep 19206233 = 14404675) B14404675
theorem B3838141 : Blo 1120629 3838141 := bstep (se 3 (by rfl) ⟨719651, by rfl⟩ : syracuseStep 3838141 = 1439303) B1439303
theorem B5542141 : Blo 1120629 5542141 := bstep (se 3 (by rfl) ⟨1039151, by rfl⟩ : syracuseStep 5542141 = 2078303) B2078303
theorem B4002185 : Blo 1120629 4002185 := bstep (se 2 (by rfl) ⟨1500819, by rfl⟩ : syracuseStep 4002185 = 3001639) B3001639
theorem B16192001 : Blo 1120629 16192001 := bstep (se 2 (by rfl) ⟨6072000, by rfl⟩ : syracuseStep 16192001 = 12144001) B12144001
theorem B27693647 : Blo 1120629 27693647 := bstep (se 1 (by rfl) ⟨20770235, by rfl⟩ : syracuseStep 27693647 = 41540471) B41540471
theorem B2527847 : Blo 1120629 2527847 := bstep (se 1 (by rfl) ⟨1895885, by rfl⟩ : syracuseStep 2527847 = 3791771) B3791771
theorem B5477483 : Blo 1120629 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B2528531 : Blo 1120629 2528531 := bstep (se 1 (by rfl) ⟨1896398, by rfl⟩ : syracuseStep 2528531 = 3792797) B3792797
theorem B23074091 : Blo 1120629 23074091 := bstep (se 1 (by rfl) ⟨17305568, by rfl⟩ : syracuseStep 23074091 = 34611137) B34611137
theorem B2528603 : Blo 1120629 2528603 := bstep (se 1 (by rfl) ⟨1896452, by rfl⟩ : syracuseStep 2528603 = 3792905) B3792905
theorem B6067979 : Blo 1120629 6067979 := bstep (se 1 (by rfl) ⟨4550984, by rfl⟩ : syracuseStep 6067979 = 9101969) B9101969
theorem B2529161 : Blo 1120629 2529161 := bstep (se 2 (by rfl) ⟨948435, by rfl⟩ : syracuseStep 2529161 = 1896871) B1896871
theorem B37427293 : Blo 1120629 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B2529377 : Blo 1120629 2529377 := bstep (se 2 (by rfl) ⟨948516, by rfl⟩ : syracuseStep 2529377 = 1897033) B1897033
theorem B6559987 : Blo 1120629 6559987 := bstep (se 1 (by rfl) ⟨4919990, by rfl⟩ : syracuseStep 6559987 = 9839981) B9839981
theorem B1120795 : Blo 1120629 1120795 := bstep (se 1 (by rfl) ⟨840596, by rfl⟩ : syracuseStep 1120795 = 1681193) B1681193
theorem B1120799 : Blo 1120629 1120799 := bstep (se 1 (by rfl) ⟨840599, by rfl⟩ : syracuseStep 1120799 = 1681199) B1681199
theorem B1121115 : Blo 1120629 1121115 := bstep (se 1 (by rfl) ⟨840836, by rfl⟩ : syracuseStep 1121115 = 1681673) B1681673
theorem B1121183 : Blo 1120629 1121183 := bstep (se 1 (by rfl) ⟨840887, by rfl⟩ : syracuseStep 1121183 = 1681775) B1681775
theorem B4266989 : Blo 1120629 4266989 := bstep (se 3 (by rfl) ⟨800060, by rfl⟩ : syracuseStep 4266989 = 1600121) B1600121
theorem B1121327 : Blo 1120629 1121327 := bstep (se 1 (by rfl) ⟨840995, by rfl⟩ : syracuseStep 1121327 = 1681991) B1681991
theorem B1121351 : Blo 1120629 1121351 := bstep (se 1 (by rfl) ⟨841013, by rfl⟩ : syracuseStep 1121351 = 1682027) B1682027
theorem B7183475 : Blo 1120629 7183475 := bstep (se 1 (by rfl) ⟨5387606, by rfl⟩ : syracuseStep 7183475 = 10775213) B10775213
theorem B1121503 : Blo 1120629 1121503 := bstep (se 1 (by rfl) ⟨841127, by rfl⟩ : syracuseStep 1121503 = 1682255) B1682255
theorem B1121767 : Blo 1120629 1121767 := bstep (se 1 (by rfl) ⟨841325, by rfl⟩ : syracuseStep 1121767 = 1682651) B1682651
theorem B1121883 : Blo 1120629 1121883 := bstep (se 1 (by rfl) ⟨841412, by rfl⟩ : syracuseStep 1121883 = 1682825) B1682825
theorem B1122119 : Blo 1120629 1122119 := bstep (se 1 (by rfl) ⟨841589, by rfl⟩ : syracuseStep 1122119 = 1683179) B1683179
theorem B1122271 : Blo 1120629 1122271 := bstep (se 1 (by rfl) ⟨841703, by rfl⟩ : syracuseStep 1122271 = 1683407) B1683407
theorem B1122535 : Blo 1120629 1122535 := bstep (se 1 (by rfl) ⟨841901, by rfl⟩ : syracuseStep 1122535 = 1683803) B1683803
theorem B4792607 : Blo 1120629 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B1122687 : Blo 1120629 1122687 := bstep (se 1 (by rfl) ⟨842015, by rfl⟩ : syracuseStep 1122687 = 1684031) B1684031
theorem B1122767 : Blo 1120629 1122767 := bstep (se 1 (by rfl) ⟨842075, by rfl⟩ : syracuseStep 1122767 = 1684151) B1684151
theorem B1122919 : Blo 1120629 1122919 := bstep (se 1 (by rfl) ⟨842189, by rfl⟩ : syracuseStep 1122919 = 1684379) B1684379
theorem B1123183 : Blo 1120629 1123183 := bstep (se 1 (by rfl) ⟨842387, by rfl⟩ : syracuseStep 1123183 = 1684775) B1684775
theorem B1123239 : Blo 1120629 1123239 := bstep (se 1 (by rfl) ⟨842429, by rfl⟩ : syracuseStep 1123239 = 1684859) B1684859
theorem B8528813 : Blo 1120629 8528813 := bstep (se 3 (by rfl) ⟨1599152, by rfl⟩ : syracuseStep 8528813 = 3198305) B3198305
theorem B1123323 : Blo 1120629 1123323 := bstep (se 1 (by rfl) ⟨842492, by rfl⟩ : syracuseStep 1123323 = 1684985) B1684985
theorem B27730945 : Blo 1120629 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B1123391 : Blo 1120629 1123391 := bstep (se 1 (by rfl) ⟨842543, by rfl⟩ : syracuseStep 1123391 = 1685087) B1685087
theorem B19702927 : Blo 1120629 19702927 := bstep (se 1 (by rfl) ⟨14777195, by rfl⟩ : syracuseStep 19702927 = 29554391) B29554391
theorem B1123535 : Blo 1120629 1123535 := bstep (se 1 (by rfl) ⟨842651, by rfl⟩ : syracuseStep 1123535 = 1685303) B1685303
theorem B4269419 : Blo 1120629 4269419 := bstep (se 1 (by rfl) ⟨3202064, by rfl⟩ : syracuseStep 4269419 = 6404129) B6404129
theorem B4269449 : Blo 1120629 4269449 := bstep (se 2 (by rfl) ⟨1601043, by rfl⟩ : syracuseStep 4269449 = 3202087) B3202087
theorem B1123739 : Blo 1120629 1123739 := bstep (se 1 (by rfl) ⟨842804, by rfl⟩ : syracuseStep 1123739 = 1685609) B1685609
theorem B5678585 : Blo 1120629 5678585 := bstep (se 2 (by rfl) ⟨2129469, by rfl⟩ : syracuseStep 5678585 = 4258939) B4258939
theorem B7185935 : Blo 1120629 7185935 := bstep (se 1 (by rfl) ⟨5389451, by rfl⟩ : syracuseStep 7185935 = 10778903) B10778903
theorem B1681007 : Blo 1120629 1681007 := bstep (se 1 (by rfl) ⟨1260755, by rfl⟩ : syracuseStep 1681007 = 2521511) B2521511
theorem B1123951 : Blo 1120629 1123951 := bstep (se 1 (by rfl) ⟨842963, by rfl⟩ : syracuseStep 1123951 = 1685927) B1685927
theorem B1124007 : Blo 1120629 1124007 := bstep (se 1 (by rfl) ⟨843005, by rfl⟩ : syracuseStep 1124007 = 1686011) B1686011
theorem B1681079 : Blo 1120629 1681079 := bstep (se 1 (by rfl) ⟨1260809, by rfl⟩ : syracuseStep 1681079 = 2521619) B2521619
theorem B1681115 : Blo 1120629 1681115 := bstep (se 1 (by rfl) ⟨1260836, by rfl⟩ : syracuseStep 1681115 = 2521673) B2521673
theorem B1124091 : Blo 1120629 1124091 := bstep (se 1 (by rfl) ⟨843068, by rfl⟩ : syracuseStep 1124091 = 1686137) B1686137
theorem B1124127 : Blo 1120629 1124127 := bstep (se 1 (by rfl) ⟨843095, by rfl⟩ : syracuseStep 1124127 = 1686191) B1686191
theorem B1124159 : Blo 1120629 1124159 := bstep (se 1 (by rfl) ⟨843119, by rfl⟩ : syracuseStep 1124159 = 1686239) B1686239
theorem B1681289 : Blo 1120629 1681289 := bstep (se 2 (by rfl) ⟨630483, by rfl⟩ : syracuseStep 1681289 = 1260967) B1260967
theorem B1681391 : Blo 1120629 1681391 := bstep (se 1 (by rfl) ⟨1261043, by rfl⟩ : syracuseStep 1681391 = 2522087) B2522087
theorem B1124335 : Blo 1120629 1124335 := bstep (se 1 (by rfl) ⟨843251, by rfl⟩ : syracuseStep 1124335 = 1686503) B1686503
theorem B1124507 : Blo 1120629 1124507 := bstep (se 1 (by rfl) ⟨843380, by rfl⟩ : syracuseStep 1124507 = 1686761) B1686761
theorem B1124543 : Blo 1120629 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B1681643 : Blo 1120629 1681643 := bstep (se 1 (by rfl) ⟨1261232, by rfl⟩ : syracuseStep 1681643 = 2522465) B2522465
theorem B1681703 : Blo 1120629 1681703 := bstep (se 1 (by rfl) ⟨1261277, by rfl⟩ : syracuseStep 1681703 = 2522555) B2522555
theorem B8530271 : Blo 1120629 8530271 := bstep (se 1 (by rfl) ⟨6397703, by rfl⟩ : syracuseStep 8530271 = 12795407) B12795407
theorem B1681787 : Blo 1120629 1681787 := bstep (se 1 (by rfl) ⟨1261340, by rfl⟩ : syracuseStep 1681787 = 2522681) B2522681
theorem B1682057 : Blo 1120629 1682057 := bstep (se 2 (by rfl) ⟨630771, by rfl⟩ : syracuseStep 1682057 = 1261543) B1261543
theorem B12135095 : Blo 1120629 12135095 := bstep (se 1 (by rfl) ⟨9101321, by rfl⟩ : syracuseStep 12135095 = 18202643) B18202643
theorem B1682231 : Blo 1120629 1682231 := bstep (se 1 (by rfl) ⟨1261673, by rfl⟩ : syracuseStep 1682231 = 2523347) B2523347
theorem B1682267 : Blo 1120629 1682267 := bstep (se 1 (by rfl) ⟨1261700, by rfl⟩ : syracuseStep 1682267 = 2523401) B2523401
theorem B1682411 : Blo 1120629 1682411 := bstep (se 1 (by rfl) ⟨1261808, by rfl⟩ : syracuseStep 1682411 = 2523617) B2523617
theorem B1682615 : Blo 1120629 1682615 := bstep (se 1 (by rfl) ⟨1261961, by rfl⟩ : syracuseStep 1682615 = 2523923) B2523923
theorem B8531243 : Blo 1120629 8531243 := bstep (se 1 (by rfl) ⟨6398432, by rfl⟩ : syracuseStep 8531243 = 12796865) B12796865
theorem B1682855 : Blo 1120629 1682855 := bstep (se 1 (by rfl) ⟨1262141, by rfl⟩ : syracuseStep 1682855 = 2524283) B2524283
theorem B1682939 : Blo 1120629 1682939 := bstep (se 1 (by rfl) ⟨1262204, by rfl⟩ : syracuseStep 1682939 = 2524409) B2524409
theorem B1683035 : Blo 1120629 1683035 := bstep (se 1 (by rfl) ⟨1262276, by rfl⟩ : syracuseStep 1683035 = 2524553) B2524553
theorem B1683119 : Blo 1120629 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B1683239 : Blo 1120629 1683239 := bstep (se 1 (by rfl) ⟨1262429, by rfl⟩ : syracuseStep 1683239 = 2524859) B2524859
theorem B1683323 : Blo 1120629 1683323 := bstep (se 1 (by rfl) ⟨1262492, by rfl⟩ : syracuseStep 1683323 = 2524985) B2524985
theorem B276377615 : Blo 1120629 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B1683743 : Blo 1120629 1683743 := bstep (se 1 (by rfl) ⟨1262807, by rfl⟩ : syracuseStep 1683743 = 2525615) B2525615
theorem B1683767 : Blo 1120629 1683767 := bstep (se 1 (by rfl) ⟨1262825, by rfl⟩ : syracuseStep 1683767 = 2525651) B2525651
theorem B1683839 : Blo 1120629 1683839 := bstep (se 1 (by rfl) ⟨1262879, by rfl⟩ : syracuseStep 1683839 = 2525759) B2525759
theorem B1683911 : Blo 1120629 1683911 := bstep (se 1 (by rfl) ⟨1262933, by rfl⟩ : syracuseStep 1683911 = 2525867) B2525867
theorem B12792491 : Blo 1120629 12792491 := bstep (se 1 (by rfl) ⟨9594368, by rfl⟩ : syracuseStep 12792491 = 19188737) B19188737
theorem B1684265 : Blo 1120629 1684265 := bstep (se 2 (by rfl) ⟨631599, by rfl⟩ : syracuseStep 1684265 = 1263199) B1263199
theorem B1684271 : Blo 1120629 1684271 := bstep (se 1 (by rfl) ⟨1263203, by rfl⟩ : syracuseStep 1684271 = 2526407) B2526407
theorem B1684391 : Blo 1120629 1684391 := bstep (se 1 (by rfl) ⟨1263293, by rfl⟩ : syracuseStep 1684391 = 2526587) B2526587
theorem B1684475 : Blo 1120629 1684475 := bstep (se 1 (by rfl) ⟨1263356, by rfl⟩ : syracuseStep 1684475 = 2526713) B2526713
theorem B1684535 : Blo 1120629 1684535 := bstep (se 1 (by rfl) ⟨1263401, by rfl⟩ : syracuseStep 1684535 = 2526803) B2526803
theorem B3191881 : Blo 1120629 3191881 := bstep (se 2 (by rfl) ⟨1196955, by rfl⟩ : syracuseStep 3191881 = 2393911) B2393911
theorem B1684655 : Blo 1120629 1684655 := bstep (se 1 (by rfl) ⟨1263491, by rfl⟩ : syracuseStep 1684655 = 2526983) B2526983
theorem B3192155 : Blo 1120629 3192155 := bstep (se 1 (by rfl) ⟨2394116, by rfl⟩ : syracuseStep 3192155 = 4788233) B4788233
theorem B1685063 : Blo 1120629 1685063 := bstep (se 1 (by rfl) ⟨1263797, by rfl⟩ : syracuseStep 1685063 = 2527595) B2527595
theorem B1685159 : Blo 1120629 1685159 := bstep (se 1 (by rfl) ⟨1263869, by rfl⟩ : syracuseStep 1685159 = 2527739) B2527739
theorem B15349459 : Blo 1120629 15349459 := bstep (se 1 (by rfl) ⟨11512094, by rfl⟩ : syracuseStep 15349459 = 23024189) B23024189
theorem B1685243 : Blo 1120629 1685243 := bstep (se 1 (by rfl) ⟨1263932, by rfl⟩ : syracuseStep 1685243 = 2527865) B2527865
theorem B1423099 : Blo 1120629 1423099 := bstep (se 1 (by rfl) ⟨1067324, by rfl⟩ : syracuseStep 1423099 = 2134649) B2134649
theorem B1685279 : Blo 1120629 1685279 := bstep (se 1 (by rfl) ⟨1263959, by rfl⟩ : syracuseStep 1685279 = 2527919) B2527919
theorem B1685327 : Blo 1120629 1685327 := bstep (se 1 (by rfl) ⟨1263995, by rfl⟩ : syracuseStep 1685327 = 2527991) B2527991
theorem B3782537 : Blo 1120629 3782537 := bstep (se 2 (by rfl) ⟨1418451, by rfl⟩ : syracuseStep 3782537 = 2836903) B2836903
theorem B1685447 : Blo 1120629 1685447 := bstep (se 1 (by rfl) ⟨1264085, by rfl⟩ : syracuseStep 1685447 = 2528171) B2528171
theorem B59062229 : Blo 1120629 59062229 := bstep (se 7 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 59062229 = 1384271) B1384271
theorem B5683283 : Blo 1120629 5683283 := bstep (se 1 (by rfl) ⟨4262462, by rfl⟩ : syracuseStep 5683283 = 8524925) B8524925
theorem B3782753 : Blo 1120629 3782753 := bstep (se 2 (by rfl) ⟨1418532, by rfl⟩ : syracuseStep 3782753 = 2837065) B2837065
theorem B3192929 : Blo 1120629 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B21543043 : Blo 1120629 21543043 := bstep (se 1 (by rfl) ⟨16157282, by rfl⟩ : syracuseStep 21543043 = 32314565) B32314565
theorem B3029147 : Blo 1120629 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B3455273 : Blo 1120629 3455273 := bstep (se 2 (by rfl) ⟨1295727, by rfl⟩ : syracuseStep 3455273 = 2591455) B2591455
theorem B1685801 : Blo 1120629 1685801 := bstep (se 2 (by rfl) ⟨632175, by rfl⟩ : syracuseStep 1685801 = 1264351) B1264351
theorem B1685807 : Blo 1120629 1685807 := bstep (se 1 (by rfl) ⟨1264355, by rfl⟩ : syracuseStep 1685807 = 2528711) B2528711
theorem B3651913 : Blo 1120629 3651913 := bstep (se 2 (by rfl) ⟨1369467, by rfl⟩ : syracuseStep 3651913 = 2738935) B2738935
theorem B1686047 : Blo 1120629 1686047 := bstep (se 1 (by rfl) ⟨1264535, by rfl⟩ : syracuseStep 1686047 = 2529071) B2529071
theorem B5683769 : Blo 1120629 5683769 := bstep (se 2 (by rfl) ⟨2131413, by rfl⟩ : syracuseStep 5683769 = 4262827) B4262827
theorem B21609017 : Blo 1120629 21609017 := bstep (se 2 (by rfl) ⟨8103381, by rfl⟩ : syracuseStep 21609017 = 16206763) B16206763
theorem B3193465 : Blo 1120629 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B1686431 : Blo 1120629 1686431 := bstep (se 1 (by rfl) ⟨1264823, by rfl⟩ : syracuseStep 1686431 = 2529647) B2529647
theorem B1686479 : Blo 1120629 1686479 := bstep (se 1 (by rfl) ⟨1264859, by rfl⟩ : syracuseStep 1686479 = 2529719) B2529719
theorem B3783671 : Blo 1120629 3783671 := bstep (se 1 (by rfl) ⟨2837753, by rfl⟩ : syracuseStep 3783671 = 5675507) B5675507
theorem B1686569 : Blo 1120629 1686569 := bstep (se 2 (by rfl) ⟨632463, by rfl⟩ : syracuseStep 1686569 = 1264927) B1264927
theorem B1686575 : Blo 1120629 1686575 := bstep (se 1 (by rfl) ⟨1264931, by rfl⟩ : syracuseStep 1686575 = 2529863) B2529863
theorem B1686599 : Blo 1120629 1686599 := bstep (se 1 (by rfl) ⟨1264949, by rfl⟩ : syracuseStep 1686599 = 2529899) B2529899
theorem B4799645 : Blo 1120629 4799645 := bstep (se 3 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 4799645 = 1799867) B1799867
theorem B24624323 : Blo 1120629 24624323 := bstep (se 1 (by rfl) ⟨18468242, by rfl⟩ : syracuseStep 24624323 = 36936485) B36936485
theorem B13647113 : Blo 1120629 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B1686863 : Blo 1120629 1686863 := bstep (se 1 (by rfl) ⟨1265147, by rfl⟩ : syracuseStep 1686863 = 2530295) B2530295
theorem B3784103 : Blo 1120629 3784103 := bstep (se 1 (by rfl) ⟨2838077, by rfl⟩ : syracuseStep 3784103 = 5676155) B5676155
theorem B1261147 : Blo 1120629 1261147 := bstep (se 1 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 1261147 = 1891721) B1891721
theorem B3194615 : Blo 1120629 3194615 := bstep (se 1 (by rfl) ⟨2395961, by rfl⟩ : syracuseStep 3194615 = 4791923) B4791923
theorem B3784535 : Blo 1120629 3784535 := bstep (se 1 (by rfl) ⟨2838401, by rfl⟩ : syracuseStep 3784535 = 5676803) B5676803
theorem B1261435 : Blo 1120629 1261435 := bstep (se 1 (by rfl) ⟨946076, by rfl⟩ : syracuseStep 1261435 = 1892153) B1892153
theorem B3785345 : Blo 1120629 3785345 := bstep (se 2 (by rfl) ⟨1419504, by rfl⟩ : syracuseStep 3785345 = 2839009) B2839009
theorem B4047727 : Blo 1120629 4047727 := bstep (se 1 (by rfl) ⟨3035795, by rfl⟩ : syracuseStep 4047727 = 6071591) B6071591
theorem B3785615 : Blo 1120629 3785615 := bstep (se 1 (by rfl) ⟨2839211, by rfl⟩ : syracuseStep 3785615 = 5678423) B5678423
theorem B5325755 : Blo 1120629 5325755 := bstep (se 1 (by rfl) ⟨3994316, by rfl⟩ : syracuseStep 5325755 = 7988633) B7988633
theorem B1262587 : Blo 1120629 1262587 := bstep (se 1 (by rfl) ⟨946940, by rfl⟩ : syracuseStep 1262587 = 1893881) B1893881
theorem B3196027 : Blo 1120629 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B1262767 : Blo 1120629 1262767 := bstep (se 1 (by rfl) ⟨947075, by rfl⟩ : syracuseStep 1262767 = 1894151) B1894151
theorem B3786155 : Blo 1120629 3786155 := bstep (se 1 (by rfl) ⟨2839616, by rfl⟩ : syracuseStep 3786155 = 5679233) B5679233
theorem B1263271 : Blo 1120629 1263271 := bstep (se 1 (by rfl) ⟨947453, by rfl⟩ : syracuseStep 1263271 = 1894907) B1894907
theorem B1918799 : Blo 1120629 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B14370641 : Blo 1120629 14370641 := bstep (se 2 (by rfl) ⟨5388990, by rfl⟩ : syracuseStep 14370641 = 10777981) B10777981
theorem B3786695 : Blo 1120629 3786695 := bstep (se 1 (by rfl) ⟨2840021, by rfl⟩ : syracuseStep 3786695 = 5680043) B5680043
theorem B3196871 : Blo 1120629 3196871 := bstep (se 1 (by rfl) ⟨2397653, by rfl⟩ : syracuseStep 3196871 = 4795307) B4795307
theorem B1263559 : Blo 1120629 1263559 := bstep (se 1 (by rfl) ⟨947669, by rfl⟩ : syracuseStep 1263559 = 1895339) B1895339
theorem B1198271 : Blo 1120629 1198271 := bstep (se 1 (by rfl) ⟨898703, by rfl⟩ : syracuseStep 1198271 = 1797407) B1797407
theorem B30755051 : Blo 1120629 30755051 := bstep (se 1 (by rfl) ⟨23066288, by rfl⟩ : syracuseStep 30755051 = 46132577) B46132577
theorem B1820969 : Blo 1120629 1820969 := bstep (se 2 (by rfl) ⟨682863, by rfl⟩ : syracuseStep 1820969 = 1365727) B1365727
theorem B1263919 : Blo 1120629 1263919 := bstep (se 1 (by rfl) ⟨947939, by rfl⟩ : syracuseStep 1263919 = 1895879) B1895879
theorem B3787451 : Blo 1120629 3787451 := bstep (se 1 (by rfl) ⟨2840588, by rfl⟩ : syracuseStep 3787451 = 5681177) B5681177
theorem B2837551 : Blo 1120629 2837551 := bstep (se 1 (by rfl) ⟨2128163, by rfl⟩ : syracuseStep 2837551 = 4256327) B4256327
theorem B1264711 : Blo 1120629 1264711 := bstep (se 1 (by rfl) ⟨948533, by rfl⟩ : syracuseStep 1264711 = 1897067) B1897067
theorem B4935163 : Blo 1120629 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B2838311 : Blo 1120629 2838311 := bstep (se 1 (by rfl) ⟨2128733, by rfl⟩ : syracuseStep 2838311 = 4257467) B4257467
theorem B4050769 : Blo 1120629 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B3198943 : Blo 1120629 3198943 := bstep (se 1 (by rfl) ⟨2399207, by rfl⟩ : syracuseStep 3198943 = 4798415) B4798415
theorem B32395301 : Blo 1120629 32395301 := bstep (se 4 (by rfl) ⟨3037059, by rfl⟩ : syracuseStep 32395301 = 6074119) B6074119
theorem B64835801 : Blo 1120629 64835801 := bstep (se 2 (by rfl) ⟨24313425, by rfl⟩ : syracuseStep 64835801 = 48626851) B48626851
theorem B61362755 : Blo 1120629 61362755 := bstep (se 1 (by rfl) ⟨46022066, by rfl⟩ : syracuseStep 61362755 = 92044133) B92044133
theorem B3789395 : Blo 1120629 3789395 := bstep (se 1 (by rfl) ⟨2842046, by rfl⟩ : syracuseStep 3789395 = 5684093) B5684093
theorem B3199571 : Blo 1120629 3199571 := bstep (se 1 (by rfl) ⟨2399678, by rfl⟩ : syracuseStep 3199571 = 4799357) B4799357
theorem B1921639 : Blo 1120629 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B17257475 : Blo 1120629 17257475 := bstep (se 1 (by rfl) ⟨12943106, by rfl⟩ : syracuseStep 17257475 = 25886213) B25886213
theorem B2839607 : Blo 1120629 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B1823951 : Blo 1120629 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B12801239 : Blo 1120629 12801239 := bstep (se 1 (by rfl) ⟨9600929, by rfl⟩ : syracuseStep 12801239 = 19201859) B19201859
theorem B3790043 : Blo 1120629 3790043 := bstep (se 1 (by rfl) ⟨2842532, by rfl⟩ : syracuseStep 3790043 = 5685065) B5685065
theorem B3200219 : Blo 1120629 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B10802585 : Blo 1120629 10802585 := bstep (se 2 (by rfl) ⟨4050969, by rfl⟩ : syracuseStep 10802585 = 8101939) B8101939
theorem B1136027 : Blo 1120629 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B14374331 : Blo 1120629 14374331 := bstep (se 1 (by rfl) ⟨10780748, by rfl⟩ : syracuseStep 14374331 = 21561497) B21561497
theorem B11523617 : Blo 1120629 11523617 := bstep (se 2 (by rfl) ⟨4321356, by rfl⟩ : syracuseStep 11523617 = 8642713) B8642713
theorem B15357815 : Blo 1120629 15357815 := bstep (se 1 (by rfl) ⟨11518361, by rfl⟩ : syracuseStep 15357815 = 23036723) B23036723
theorem B3790907 : Blo 1120629 3790907 := bstep (se 1 (by rfl) ⟨2843180, by rfl⟩ : syracuseStep 3790907 = 5686361) B5686361
theorem B3791177 : Blo 1120629 3791177 := bstep (se 2 (by rfl) ⟨1421691, by rfl⟩ : syracuseStep 3791177 = 2843383) B2843383
theorem B12802697 : Blo 1120629 12802697 := bstep (se 2 (by rfl) ⟨4801011, by rfl⟩ : syracuseStep 12802697 = 9602023) B9602023
theorem B3594905 : Blo 1120629 3594905 := bstep (se 2 (by rfl) ⟨1348089, by rfl⟩ : syracuseStep 3594905 = 2696179) B2696179
theorem B1891127 : Blo 1120629 1891127 := bstep (se 1 (by rfl) ⟨1418345, by rfl⟩ : syracuseStep 1891127 = 2836691) B2836691
theorem B2841551 : Blo 1120629 2841551 := bstep (se 1 (by rfl) ⟨2131163, by rfl⟩ : syracuseStep 2841551 = 4262327) B4262327
theorem B7199725 : Blo 1120629 7199725 := bstep (se 3 (by rfl) ⟨1349948, by rfl⟩ : syracuseStep 7199725 = 2699897) B2699897
theorem B14605379 : Blo 1120629 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B2842067 : Blo 1120629 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B2842087 : Blo 1120629 2842087 := bstep (se 1 (by rfl) ⟨2131565, by rfl⟩ : syracuseStep 2842087 = 4263131) B4263131
theorem B1891903 : Blo 1120629 1891903 := bstep (se 1 (by rfl) ⟨1418927, by rfl⟩ : syracuseStep 1891903 = 2837855) B2837855
theorem B3792527 : Blo 1120629 3792527 := bstep (se 1 (by rfl) ⟨2844395, by rfl⟩ : syracuseStep 3792527 = 5688791) B5688791
theorem B1892639 : Blo 1120629 1892639 := bstep (se 1 (by rfl) ⟨1419479, by rfl⟩ : syracuseStep 1892639 = 2838959) B2838959
theorem B2023807 : Blo 1120629 2023807 := bstep (se 1 (by rfl) ⟨1517855, by rfl⟩ : syracuseStep 2023807 = 3035711) B3035711
theorem B9593275 : Blo 1120629 9593275 := bstep (se 1 (by rfl) ⟨7194956, by rfl⟩ : syracuseStep 9593275 = 14389913) B14389913
theorem B5399293 : Blo 1120629 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B3793661 : Blo 1120629 3793661 := bstep (se 3 (by rfl) ⟨711311, by rfl⟩ : syracuseStep 3793661 = 1422623) B1422623
theorem B4547339 : Blo 1120629 4547339 := bstep (se 1 (by rfl) ⟨3410504, by rfl⟩ : syracuseStep 4547339 = 6821009) B6821009
theorem B1893287 : Blo 1120629 1893287 := bstep (se 1 (by rfl) ⟨1419965, by rfl⟩ : syracuseStep 1893287 = 2839931) B2839931
theorem B3597223 : Blo 1120629 3597223 := bstep (se 1 (by rfl) ⟨2697917, by rfl⟩ : syracuseStep 3597223 = 5395835) B5395835
theorem B1893449 : Blo 1120629 1893449 := bstep (se 2 (by rfl) ⟨710043, by rfl⟩ : syracuseStep 1893449 = 1420087) B1420087
theorem B4547773 : Blo 1120629 4547773 := bstep (se 3 (by rfl) ⟨852707, by rfl⟩ : syracuseStep 4547773 = 1705415) B1705415
theorem B3335375 : Blo 1120629 3335375 := bstep (se 1 (by rfl) ⟨2501531, by rfl⟩ : syracuseStep 3335375 = 5003063) B5003063
theorem B2844011 : Blo 1120629 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B12805613 : Blo 1120629 12805613 := bstep (se 3 (by rfl) ⟨2401052, by rfl⟩ : syracuseStep 12805613 = 4802105) B4802105
theorem B1894009 : Blo 1120629 1894009 := bstep (se 2 (by rfl) ⟨710253, by rfl⟩ : syracuseStep 1894009 = 1420507) B1420507
theorem B3598121 : Blo 1120629 3598121 := bstep (se 2 (by rfl) ⟨1349295, by rfl⟩ : syracuseStep 3598121 = 2698591) B2698591
theorem B1894495 : Blo 1120629 1894495 := bstep (se 1 (by rfl) ⟨1420871, by rfl⟩ : syracuseStep 1894495 = 2841743) B2841743
theorem B2812423 : Blo 1120629 2812423 := bstep (se 1 (by rfl) ⟨2109317, by rfl⟩ : syracuseStep 2812423 = 4218635) B4218635
theorem B14379767 : Blo 1120629 14379767 := bstep (se 1 (by rfl) ⟨10784825, by rfl⟩ : syracuseStep 14379767 = 21569651) B21569651
theorem B11824015 : Blo 1120629 11824015 := bstep (se 1 (by rfl) ⟨8868011, by rfl⟩ : syracuseStep 11824015 = 17736023) B17736023
theorem B1895791 : Blo 1120629 1895791 := bstep (se 1 (by rfl) ⟨1421843, by rfl⟩ : syracuseStep 1895791 = 2843687) B2843687
theorem B1600879 : Blo 1120629 1600879 := bstep (se 1 (by rfl) ⟨1200659, by rfl⟩ : syracuseStep 1600879 = 2401319) B2401319
theorem B3239357 : Blo 1120629 3239357 := bstep (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) B1214759
theorem B1896169 : Blo 1120629 1896169 := bstep (se 2 (by rfl) ⟨711063, by rfl⟩ : syracuseStep 1896169 = 1422127) B1422127
theorem B2846603 : Blo 1120629 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B1896635 : Blo 1120629 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B7205057 : Blo 1120629 7205057 := bstep (se 2 (by rfl) ⟨2701896, by rfl⟩ : syracuseStep 7205057 = 5403793) B5403793
theorem B1798375 : Blo 1120629 1798375 := bstep (se 1 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 1798375 = 2697563) B2697563
theorem B4256009 : Blo 1120629 4256009 := bstep (se 2 (by rfl) ⟨1596003, by rfl⟩ : syracuseStep 4256009 = 3192007) B3192007
theorem B6385949 : Blo 1120629 6385949 := bstep (se 3 (by rfl) ⟨1197365, by rfl⟩ : syracuseStep 6385949 = 2394731) B2394731
theorem B7205597 : Blo 1120629 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B1897195 : Blo 1120629 1897195 := bstep (se 1 (by rfl) ⟨1422896, by rfl⟩ : syracuseStep 1897195 = 2845793) B2845793
theorem B3208061 : Blo 1120629 3208061 := bstep (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) B1203023
theorem B10777673 : Blo 1120629 10777673 := bstep (se 2 (by rfl) ⟨4041627, by rfl⟩ : syracuseStep 10777673 = 8083255) B8083255
theorem B8090867 : Blo 1120629 8090867 := bstep (se 1 (by rfl) ⟨6068150, by rfl⟩ : syracuseStep 8090867 = 12136301) B12136301
theorem B6387133 : Blo 1120629 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B34600409 : Blo 1120629 34600409 := bstep (se 2 (by rfl) ⟨12975153, by rfl⟩ : syracuseStep 34600409 = 25950307) B25950307
theorem B4257755 : Blo 1120629 4257755 := bstep (se 1 (by rfl) ⟨3193316, by rfl⟩ : syracuseStep 4257755 = 6386633) B6386633
theorem B4257785 : Blo 1120629 4257785 := bstep (se 2 (by rfl) ⟨1596669, by rfl⟩ : syracuseStep 4257785 = 3193339) B3193339
theorem B13137913 : Blo 1120629 13137913 := bstep (se 2 (by rfl) ⟨4926717, by rfl⟩ : syracuseStep 13137913 = 9853435) B9853435
theorem B2128027 : Blo 1120629 2128027 := bstep (se 1 (by rfl) ⟨1596020, by rfl⟩ : syracuseStep 2128027 = 3192041) B3192041
theorem B1800425 : Blo 1120629 1800425 := bstep (se 2 (by rfl) ⟨675159, by rfl⟩ : syracuseStep 1800425 = 1350319) B1350319
theorem B12777911 : Blo 1120629 12777911 := bstep (se 1 (by rfl) ⟨9583433, by rfl⟩ : syracuseStep 12777911 = 19166867) B19166867
theorem B1800841 : Blo 1120629 1800841 := bstep (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) B1350631
theorem B2521961 : Blo 1120629 2521961 := bstep (se 2 (by rfl) ⟨945735, by rfl⟩ : syracuseStep 2521961 = 1891471) B1891471
theorem B2522015 : Blo 1120629 2522015 := bstep (se 1 (by rfl) ⟨1891511, by rfl⟩ : syracuseStep 2522015 = 3783023) B3783023
theorem B4324423 : Blo 1120629 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B6388865 : Blo 1120629 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B98466965 : Blo 1120629 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B2522951 : Blo 1120629 2522951 := bstep (se 1 (by rfl) ⟨1892213, by rfl⟩ : syracuseStep 2522951 = 3784427) B3784427
theorem B4260215 : Blo 1120629 4260215 := bstep (se 1 (by rfl) ⟨3195161, by rfl⟩ : syracuseStep 4260215 = 6390323) B6390323
theorem B2523563 : Blo 1120629 2523563 := bstep (se 1 (by rfl) ⟨1892672, by rfl⟩ : syracuseStep 2523563 = 3785345) B3785345
theorem B4260383 : Blo 1120629 4260383 := bstep (se 1 (by rfl) ⟨3195287, by rfl⟩ : syracuseStep 4260383 = 6390575) B6390575
theorem B2523743 : Blo 1120629 2523743 := bstep (se 1 (by rfl) ⟨1892807, by rfl⟩ : syracuseStep 2523743 = 3785615) B3785615
theorem B2524103 : Blo 1120629 2524103 := bstep (se 1 (by rfl) ⟨1893077, by rfl⟩ : syracuseStep 2524103 = 3786155) B3786155
theorem B1279199 : Blo 1120629 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B2524463 : Blo 1120629 2524463 := bstep (se 1 (by rfl) ⟨1893347, by rfl⟩ : syracuseStep 2524463 = 3786695) B3786695
theorem B2131247 : Blo 1120629 2131247 := bstep (se 1 (by rfl) ⟨1598435, by rfl⟩ : syracuseStep 2131247 = 3196871) B3196871
theorem B4261187 : Blo 1120629 4261187 := bstep (se 1 (by rfl) ⟨3195890, by rfl⟩ : syracuseStep 4261187 = 6391781) B6391781
theorem B4261369 : Blo 1120629 4261369 := bstep (se 2 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 4261369 = 3196027) B3196027
theorem B1213979 : Blo 1120629 1213979 := bstep (se 1 (by rfl) ⟨910484, by rfl⟩ : syracuseStep 1213979 = 1820969) B1820969
theorem B6063697 : Blo 1120629 6063697 := bstep (se 2 (by rfl) ⟨2273886, by rfl⟩ : syracuseStep 6063697 = 4547773) B4547773
theorem B4261643 : Blo 1120629 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B2524967 : Blo 1120629 2524967 := bstep (se 1 (by rfl) ⟨1893725, by rfl⟩ : syracuseStep 2524967 = 3787451) B3787451
theorem B2525345 : Blo 1120629 2525345 := bstep (se 2 (by rfl) ⟨947004, by rfl⟩ : syracuseStep 2525345 = 1894009) B1894009
theorem B21596867 : Blo 1120629 21596867 := bstep (se 1 (by rfl) ⟨16197650, by rfl⟩ : syracuseStep 21596867 = 32395301) B32395301
theorem B2525993 : Blo 1120629 2525993 := bstep (se 2 (by rfl) ⟨947247, by rfl⟩ : syracuseStep 2525993 = 1894495) B1894495
theorem B43223867 : Blo 1120629 43223867 := bstep (se 1 (by rfl) ⟨32417900, by rfl⟩ : syracuseStep 43223867 = 64835801) B64835801
theorem B2526263 : Blo 1120629 2526263 := bstep (se 1 (by rfl) ⟨1894697, by rfl⟩ : syracuseStep 2526263 = 3789395) B3789395
theorem B2133047 : Blo 1120629 2133047 := bstep (se 1 (by rfl) ⟨1599785, by rfl⟩ : syracuseStep 2133047 = 3199571) B3199571
theorem B1215967 : Blo 1120629 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B2526695 : Blo 1120629 2526695 := bstep (se 1 (by rfl) ⟨1895021, by rfl⟩ : syracuseStep 2526695 = 3790043) B3790043
theorem B2133479 : Blo 1120629 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B15765353 : Blo 1120629 15765353 := bstep (se 2 (by rfl) ⟨5912007, by rfl⟩ : syracuseStep 15765353 = 11824015) B11824015
theorem B2527271 : Blo 1120629 2527271 := bstep (se 1 (by rfl) ⟨1895453, by rfl⟩ : syracuseStep 2527271 = 3790907) B3790907
theorem B2527451 : Blo 1120629 2527451 := bstep (se 1 (by rfl) ⟨1895588, by rfl⟩ : syracuseStep 2527451 = 3791177) B3791177
theorem B2396603 : Blo 1120629 2396603 := bstep (se 1 (by rfl) ⟨1797452, by rfl⟩ : syracuseStep 2396603 = 3594905) B3594905
theorem B2527721 : Blo 1120629 2527721 := bstep (se 2 (by rfl) ⟨947895, by rfl⟩ : syracuseStep 2527721 = 1895791) B1895791
theorem B2134505 : Blo 1120629 2134505 := bstep (se 2 (by rfl) ⟨800439, by rfl⟩ : syracuseStep 2134505 = 1600879) B1600879
theorem B9736919 : Blo 1120629 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B4788983 : Blo 1120629 4788983 := bstep (se 1 (by rfl) ⟨3591737, by rfl⟩ : syracuseStep 4788983 = 7183475) B7183475
theorem B2528225 : Blo 1120629 2528225 := bstep (se 2 (by rfl) ⟨948084, by rfl⟩ : syracuseStep 2528225 = 1896169) B1896169
theorem B2528351 : Blo 1120629 2528351 := bstep (se 1 (by rfl) ⟨1896263, by rfl⟩ : syracuseStep 2528351 = 3792527) B3792527
theorem B4265257 : Blo 1120629 4265257 := bstep (se 2 (by rfl) ⟨1599471, by rfl⟩ : syracuseStep 4265257 = 3198943) B3198943
theorem B5117521 : Blo 1120629 5117521 := bstep (se 2 (by rfl) ⟨1919070, by rfl⟩ : syracuseStep 5117521 = 3838141) B3838141
theorem B2397833 : Blo 1120629 2397833 := bstep (se 2 (by rfl) ⟨899187, by rfl⟩ : syracuseStep 2397833 = 1798375) B1798375
theorem B2529107 : Blo 1120629 2529107 := bstep (se 1 (by rfl) ⟨1896830, by rfl⟩ : syracuseStep 2529107 = 3793661) B3793661
theorem B2562185 : Blo 1120629 2562185 := bstep (se 2 (by rfl) ⟨960819, by rfl⟩ : syracuseStep 2562185 = 1921639) B1921639
theorem B2529593 : Blo 1120629 2529593 := bstep (se 2 (by rfl) ⟨948597, by rfl⟩ : syracuseStep 2529593 = 1897195) B1897195
theorem B1120671 : Blo 1120629 1120671 := bstep (se 1 (by rfl) ⟨840503, by rfl⟩ : syracuseStep 1120671 = 1681007) B1681007
theorem B1120719 : Blo 1120629 1120719 := bstep (se 1 (by rfl) ⟨840539, by rfl⟩ : syracuseStep 1120719 = 1681079) B1681079
theorem B1120743 : Blo 1120629 1120743 := bstep (se 1 (by rfl) ⟨840557, by rfl⟩ : syracuseStep 1120743 = 1681115) B1681115
theorem B2398747 : Blo 1120629 2398747 := bstep (se 1 (by rfl) ⟨1799060, by rfl⟩ : syracuseStep 2398747 = 3598121) B3598121
theorem B1120859 : Blo 1120629 1120859 := bstep (se 1 (by rfl) ⟨840644, by rfl⟩ : syracuseStep 1120859 = 1681289) B1681289
theorem B1120927 : Blo 1120629 1120927 := bstep (se 1 (by rfl) ⟨840695, by rfl⟩ : syracuseStep 1120927 = 1681391) B1681391
theorem B1121095 : Blo 1120629 1121095 := bstep (se 1 (by rfl) ⟨840821, by rfl⟩ : syracuseStep 1121095 = 1681643) B1681643
theorem B1121135 : Blo 1120629 1121135 := bstep (se 1 (by rfl) ⟨840851, by rfl⟩ : syracuseStep 1121135 = 1681703) B1681703
theorem B1121191 : Blo 1120629 1121191 := bstep (se 1 (by rfl) ⟨840893, by rfl⟩ : syracuseStep 1121191 = 1681787) B1681787
theorem B1121371 : Blo 1120629 1121371 := bstep (se 1 (by rfl) ⟨841028, by rfl⟩ : syracuseStep 1121371 = 1682057) B1682057
theorem B1121487 : Blo 1120629 1121487 := bstep (se 1 (by rfl) ⟨841115, by rfl⟩ : syracuseStep 1121487 = 1682231) B1682231
theorem B1121511 : Blo 1120629 1121511 := bstep (se 1 (by rfl) ⟨841133, by rfl⟩ : syracuseStep 1121511 = 1682267) B1682267
theorem B1121607 : Blo 1120629 1121607 := bstep (se 1 (by rfl) ⟨841205, by rfl⟩ : syracuseStep 1121607 = 1682411) B1682411
theorem B1121743 : Blo 1120629 1121743 := bstep (se 1 (by rfl) ⟨841307, by rfl⟩ : syracuseStep 1121743 = 1682615) B1682615
theorem B1121903 : Blo 1120629 1121903 := bstep (se 1 (by rfl) ⟨841427, by rfl⟩ : syracuseStep 1121903 = 1682855) B1682855
theorem B1121959 : Blo 1120629 1121959 := bstep (se 1 (by rfl) ⟨841469, by rfl⟩ : syracuseStep 1121959 = 1682939) B1682939
theorem B1122023 : Blo 1120629 1122023 := bstep (se 1 (by rfl) ⟨841517, by rfl⟩ : syracuseStep 1122023 = 1683035) B1683035
theorem B1122079 : Blo 1120629 1122079 := bstep (se 1 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 1122079 = 1683119) B1683119
theorem B1122159 : Blo 1120629 1122159 := bstep (se 1 (by rfl) ⟨841619, by rfl⟩ : syracuseStep 1122159 = 1683239) B1683239
theorem B1122215 : Blo 1120629 1122215 := bstep (se 1 (by rfl) ⟨841661, by rfl⟩ : syracuseStep 1122215 = 1683323) B1683323
theorem B1122495 : Blo 1120629 1122495 := bstep (se 1 (by rfl) ⟨841871, by rfl⟩ : syracuseStep 1122495 = 1683743) B1683743
theorem B1122511 : Blo 1120629 1122511 := bstep (se 1 (by rfl) ⟨841883, by rfl⟩ : syracuseStep 1122511 = 1683767) B1683767
theorem B1122559 : Blo 1120629 1122559 := bstep (se 1 (by rfl) ⟨841919, by rfl⟩ : syracuseStep 1122559 = 1683839) B1683839
theorem B1122607 : Blo 1120629 1122607 := bstep (se 1 (by rfl) ⟨841955, by rfl⟩ : syracuseStep 1122607 = 1683911) B1683911
theorem B8528327 : Blo 1120629 8528327 := bstep (se 1 (by rfl) ⟨6396245, by rfl⟩ : syracuseStep 8528327 = 12792491) B12792491
theorem B1122843 : Blo 1120629 1122843 := bstep (se 1 (by rfl) ⟨842132, by rfl⟩ : syracuseStep 1122843 = 1684265) B1684265
theorem B1122847 : Blo 1120629 1122847 := bstep (se 1 (by rfl) ⟨842135, by rfl⟩ : syracuseStep 1122847 = 1684271) B1684271
theorem B2138707 : Blo 1120629 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1122927 : Blo 1120629 1122927 := bstep (se 1 (by rfl) ⟨842195, by rfl⟩ : syracuseStep 1122927 = 1684391) B1684391
theorem B1122983 : Blo 1120629 1122983 := bstep (se 1 (by rfl) ⟨842237, by rfl⟩ : syracuseStep 1122983 = 1684475) B1684475
theorem B1123023 : Blo 1120629 1123023 := bstep (se 1 (by rfl) ⟨842267, by rfl⟩ : syracuseStep 1123023 = 1684535) B1684535
theorem B7185115 : Blo 1120629 7185115 := bstep (se 1 (by rfl) ⟨5388836, by rfl⟩ : syracuseStep 7185115 = 10777673) B10777673
theorem B1123103 : Blo 1120629 1123103 := bstep (se 1 (by rfl) ⟨842327, by rfl⟩ : syracuseStep 1123103 = 1684655) B1684655
theorem B2401121 : Blo 1120629 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B1123375 : Blo 1120629 1123375 := bstep (se 1 (by rfl) ⟨842531, by rfl⟩ : syracuseStep 1123375 = 1685063) B1685063
theorem B1123439 : Blo 1120629 1123439 := bstep (se 1 (by rfl) ⟨842579, by rfl⟩ : syracuseStep 1123439 = 1685159) B1685159
theorem B1123495 : Blo 1120629 1123495 := bstep (se 1 (by rfl) ⟨842621, by rfl⟩ : syracuseStep 1123495 = 1685243) B1685243
theorem B1123519 : Blo 1120629 1123519 := bstep (se 1 (by rfl) ⟨842639, by rfl⟩ : syracuseStep 1123519 = 1685279) B1685279
theorem B1123551 : Blo 1120629 1123551 := bstep (se 1 (by rfl) ⟨842663, by rfl⟩ : syracuseStep 1123551 = 1685327) B1685327
theorem B1123631 : Blo 1120629 1123631 := bstep (se 1 (by rfl) ⟨842723, by rfl⟩ : syracuseStep 1123631 = 1685447) B1685447
theorem B2303515 : Blo 1120629 2303515 := bstep (se 1 (by rfl) ⟨1727636, by rfl⟩ : syracuseStep 2303515 = 3455273) B3455273
theorem B1123867 : Blo 1120629 1123867 := bstep (se 1 (by rfl) ⟨842900, by rfl⟩ : syracuseStep 1123867 = 1685801) B1685801
theorem B1123871 : Blo 1120629 1123871 := bstep (se 1 (by rfl) ⟨842903, by rfl⟩ : syracuseStep 1123871 = 1685807) B1685807
theorem B1124031 : Blo 1120629 1124031 := bstep (se 1 (by rfl) ⟨843023, by rfl⟩ : syracuseStep 1124031 = 1686047) B1686047
theorem B1681307 : Blo 1120629 1681307 := bstep (se 1 (by rfl) ⟨1260980, by rfl⟩ : syracuseStep 1681307 = 2521961) B2521961
theorem B1681343 : Blo 1120629 1681343 := bstep (se 1 (by rfl) ⟨1261007, by rfl⟩ : syracuseStep 1681343 = 2522015) B2522015
theorem B1124287 : Blo 1120629 1124287 := bstep (se 1 (by rfl) ⟨843215, by rfl⟩ : syracuseStep 1124287 = 1686431) B1686431
theorem B1124319 : Blo 1120629 1124319 := bstep (se 1 (by rfl) ⟨843239, by rfl⟩ : syracuseStep 1124319 = 1686479) B1686479
theorem B1124379 : Blo 1120629 1124379 := bstep (se 1 (by rfl) ⟨843284, by rfl⟩ : syracuseStep 1124379 = 1686569) B1686569
theorem B1124383 : Blo 1120629 1124383 := bstep (se 1 (by rfl) ⟨843287, by rfl⟩ : syracuseStep 1124383 = 1686575) B1686575
theorem B1124399 : Blo 1120629 1124399 := bstep (se 1 (by rfl) ⟨843299, by rfl⟩ : syracuseStep 1124399 = 1686599) B1686599
theorem B65644643 : Blo 1120629 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B1681529 : Blo 1120629 1681529 := bstep (se 2 (by rfl) ⟨630573, by rfl⟩ : syracuseStep 1681529 = 1261147) B1261147
theorem B1124575 : Blo 1120629 1124575 := bstep (se 1 (by rfl) ⟨843431, by rfl⟩ : syracuseStep 1124575 = 1686863) B1686863
theorem B1681913 : Blo 1120629 1681913 := bstep (se 2 (by rfl) ⟨630717, by rfl⟩ : syracuseStep 1681913 = 1261435) B1261435
theorem B1681967 : Blo 1120629 1681967 := bstep (se 1 (by rfl) ⟨1261475, by rfl⟩ : syracuseStep 1681967 = 2522951) B2522951
theorem B1682399 : Blo 1120629 1682399 := bstep (se 1 (by rfl) ⟨1261799, by rfl⟩ : syracuseStep 1682399 = 2523599) B2523599
theorem B2698409 : Blo 1120629 2698409 := bstep (se 2 (by rfl) ⟨1011903, by rfl⟩ : syracuseStep 2698409 = 2023807) B2023807
theorem B12791033 : Blo 1120629 12791033 := bstep (se 2 (by rfl) ⟨4796637, by rfl⟩ : syracuseStep 12791033 = 9593275) B9593275
theorem B1682843 : Blo 1120629 1682843 := bstep (se 1 (by rfl) ⟨1262132, by rfl⟩ : syracuseStep 1682843 = 2524265) B2524265
theorem B1683263 : Blo 1120629 1683263 := bstep (se 1 (by rfl) ⟨1262447, by rfl⟩ : syracuseStep 1683263 = 2524895) B2524895
theorem B4796297 : Blo 1120629 4796297 := bstep (se 2 (by rfl) ⟨1798611, by rfl⟩ : syracuseStep 4796297 = 3597223) B3597223
theorem B9580427 : Blo 1120629 9580427 := bstep (se 1 (by rfl) ⟨7185320, by rfl⟩ : syracuseStep 9580427 = 14370641) B14370641
theorem B6401987 : Blo 1120629 6401987 := bstep (se 1 (by rfl) ⟨4801490, by rfl⟩ : syracuseStep 6401987 = 9602981) B9602981
theorem B1683449 : Blo 1120629 1683449 := bstep (se 2 (by rfl) ⟨631293, by rfl⟩ : syracuseStep 1683449 = 1262587) B1262587
theorem B36974593 : Blo 1120629 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B1683689 : Blo 1120629 1683689 := bstep (se 2 (by rfl) ⟨631383, by rfl⟩ : syracuseStep 1683689 = 1262767) B1262767
theorem B1683815 : Blo 1120629 1683815 := bstep (se 1 (by rfl) ⟨1262861, by rfl⟩ : syracuseStep 1683815 = 2525723) B2525723
theorem B5681987 : Blo 1120629 5681987 := bstep (se 1 (by rfl) ⟨4261490, by rfl⟩ : syracuseStep 5681987 = 8522981) B8522981
theorem B1684361 : Blo 1120629 1684361 := bstep (se 2 (by rfl) ⟨631635, by rfl⟩ : syracuseStep 1684361 = 1263271) B1263271
theorem B14202013 : Blo 1120629 14202013 := bstep (se 3 (by rfl) ⟨2662877, by rfl⟩ : syracuseStep 14202013 = 5325755) B5325755
theorem B1684745 : Blo 1120629 1684745 := bstep (se 2 (by rfl) ⟨631779, by rfl⟩ : syracuseStep 1684745 = 1263559) B1263559
theorem B1684799 : Blo 1120629 1684799 := bstep (se 1 (by rfl) ⟨1263599, by rfl⟩ : syracuseStep 1684799 = 2527199) B2527199
theorem B46019933 : Blo 1120629 46019933 := bstep (se 3 (by rfl) ⟨8628737, by rfl⟩ : syracuseStep 46019933 = 17257475) B17257475
theorem B2668123 : Blo 1120629 2668123 := bstep (se 1 (by rfl) ⟨2001092, by rfl⟩ : syracuseStep 2668123 = 4002185) B4002185
theorem B5682797 : Blo 1120629 5682797 := bstep (se 3 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 5682797 = 2131049) B2131049
theorem B10794667 : Blo 1120629 10794667 := bstep (se 1 (by rfl) ⟨8096000, by rfl⟩ : syracuseStep 10794667 = 16192001) B16192001
theorem B40908503 : Blo 1120629 40908503 := bstep (se 1 (by rfl) ⟨30681377, by rfl⟩ : syracuseStep 40908503 = 61362755) B61362755
theorem B18462431 : Blo 1120629 18462431 := bstep (se 1 (by rfl) ⟨13846823, by rfl⟩ : syracuseStep 18462431 = 27693647) B27693647
theorem B1685225 : Blo 1120629 1685225 := bstep (se 2 (by rfl) ⟨631959, by rfl⟩ : syracuseStep 1685225 = 1263919) B1263919
theorem B1685231 : Blo 1120629 1685231 := bstep (se 1 (by rfl) ⟨1263923, by rfl⟩ : syracuseStep 1685231 = 2527847) B2527847
theorem B8894333 : Blo 1120629 8894333 := bstep (se 3 (by rfl) ⟨1667687, by rfl⟩ : syracuseStep 8894333 = 3335375) B3335375
theorem B21575645 : Blo 1120629 21575645 := bstep (se 3 (by rfl) ⟨4045433, by rfl⟩ : syracuseStep 21575645 = 8090867) B8090867
theorem B3749897 : Blo 1120629 3749897 := bstep (se 2 (by rfl) ⟨1406211, by rfl⟩ : syracuseStep 3749897 = 2812423) B2812423
theorem B3651655 : Blo 1120629 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B8534159 : Blo 1120629 8534159 := bstep (se 1 (by rfl) ⟨6400619, by rfl⟩ : syracuseStep 8534159 = 12801239) B12801239
theorem B1685687 : Blo 1120629 1685687 := bstep (se 1 (by rfl) ⟨1264265, by rfl⟩ : syracuseStep 1685687 = 2528531) B2528531
theorem B15382727 : Blo 1120629 15382727 := bstep (se 1 (by rfl) ⟨11537045, by rfl⟩ : syracuseStep 15382727 = 23074091) B23074091
theorem B1685735 : Blo 1120629 1685735 := bstep (se 1 (by rfl) ⟨1264301, by rfl⟩ : syracuseStep 1685735 = 2528603) B2528603
theorem B9582887 : Blo 1120629 9582887 := bstep (se 1 (by rfl) ⟨7187165, by rfl⟩ : syracuseStep 9582887 = 14374331) B14374331
theorem B7682411 : Blo 1120629 7682411 := bstep (se 1 (by rfl) ⟨5761808, by rfl⟩ : syracuseStep 7682411 = 11523617) B11523617
theorem B3029405 : Blo 1120629 3029405 := bstep (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) B1136027
theorem B4045319 : Blo 1120629 4045319 := bstep (se 1 (by rfl) ⟨3033989, by rfl⟩ : syracuseStep 4045319 = 6067979) B6067979
theorem B10238543 : Blo 1120629 10238543 := bstep (se 1 (by rfl) ⟨7678907, by rfl⟩ : syracuseStep 10238543 = 15357815) B15357815
theorem B1686107 : Blo 1120629 1686107 := bstep (se 1 (by rfl) ⟨1264580, by rfl⟩ : syracuseStep 1686107 = 2529161) B2529161
theorem B3783401 : Blo 1120629 3783401 := bstep (se 2 (by rfl) ⟨1418775, by rfl⟩ : syracuseStep 3783401 = 2837551) B2837551
theorem B1686251 : Blo 1120629 1686251 := bstep (se 1 (by rfl) ⟨1264688, by rfl⟩ : syracuseStep 1686251 = 2529377) B2529377
theorem B1686281 : Blo 1120629 1686281 := bstep (se 2 (by rfl) ⟨632355, by rfl⟩ : syracuseStep 1686281 = 1264711) B1264711
theorem B8535131 : Blo 1120629 8535131 := bstep (se 1 (by rfl) ⟨6401348, by rfl⟩ : syracuseStep 8535131 = 12802697) B12802697
theorem B1260751 : Blo 1120629 1260751 := bstep (se 1 (by rfl) ⟨945563, by rfl⟩ : syracuseStep 1260751 = 1891127) B1891127
theorem B1261759 : Blo 1120629 1261759 := bstep (se 1 (by rfl) ⟨946319, by rfl⟩ : syracuseStep 1261759 = 1892639) B1892639
theorem B3195071 : Blo 1120629 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B7389521 : Blo 1120629 7389521 := bstep (se 2 (by rfl) ⟨2771070, by rfl⟩ : syracuseStep 7389521 = 5542141) B5542141
theorem B3195389 : Blo 1120629 3195389 := bstep (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) B1198271
theorem B3031559 : Blo 1120629 3031559 := bstep (se 1 (by rfl) ⟨2273669, by rfl⟩ : syracuseStep 3031559 = 4547339) B4547339
theorem B4801133 : Blo 1120629 4801133 := bstep (se 3 (by rfl) ⟨900212, by rfl⟩ : syracuseStep 4801133 = 1800425) B1800425
theorem B1262191 : Blo 1120629 1262191 := bstep (se 1 (by rfl) ⟨946643, by rfl⟩ : syracuseStep 1262191 = 1893287) B1893287
theorem B5685875 : Blo 1120629 5685875 := bstep (se 1 (by rfl) ⟨4264406, by rfl⟩ : syracuseStep 5685875 = 8528813) B8528813
theorem B1262299 : Blo 1120629 1262299 := bstep (se 1 (by rfl) ⟨946724, by rfl⟩ : syracuseStep 1262299 = 1893449) B1893449
theorem B8537075 : Blo 1120629 8537075 := bstep (se 1 (by rfl) ⟨6402806, by rfl⟩ : syracuseStep 8537075 = 12805613) B12805613
theorem B3785723 : Blo 1120629 3785723 := bstep (se 1 (by rfl) ⟨2839292, by rfl⟩ : syracuseStep 3785723 = 5678585) B5678585
theorem B5686685 : Blo 1120629 5686685 := bstep (se 3 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 5686685 = 2132507) B2132507
theorem B5686847 : Blo 1120629 5686847 := bstep (se 1 (by rfl) ⟨4265135, by rfl⟩ : syracuseStep 5686847 = 8530271) B8530271
theorem B9586511 : Blo 1120629 9586511 := bstep (se 1 (by rfl) ⟨7189883, by rfl⟩ : syracuseStep 9586511 = 14379767) B14379767
theorem B5687495 : Blo 1120629 5687495 := bstep (se 1 (by rfl) ⟨4265621, by rfl⟩ : syracuseStep 5687495 = 8531243) B8531243
theorem B20465945 : Blo 1120629 20465945 := bstep (se 2 (by rfl) ⟨7674729, by rfl⟩ : syracuseStep 20465945 = 15349459) B15349459
theorem B17517217 : Blo 1120629 17517217 := bstep (se 2 (by rfl) ⟨6568956, by rfl⟩ : syracuseStep 17517217 = 13137913) B13137913
theorem B1264423 : Blo 1120629 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B4803371 : Blo 1120629 4803371 := bstep (se 1 (by rfl) ⟨3602528, by rfl⟩ : syracuseStep 4803371 = 7205057) B7205057
theorem B28724057 : Blo 1120629 28724057 := bstep (se 2 (by rfl) ⟨10771521, by rfl⟩ : syracuseStep 28724057 = 21543043) B21543043
theorem B2837339 : Blo 1120629 2837339 := bstep (se 1 (by rfl) ⟨2128004, by rfl⟩ : syracuseStep 2837339 = 4256009) B4256009
theorem B2837369 : Blo 1120629 2837369 := bstep (se 2 (by rfl) ⟨1064013, by rfl⟩ : syracuseStep 2837369 = 2128027) B2128027
theorem B4869217 : Blo 1120629 4869217 := bstep (se 2 (by rfl) ⟨1825956, by rfl⟩ : syracuseStep 4869217 = 3651913) B3651913
theorem B4803731 : Blo 1120629 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B8638285 : Blo 1120629 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B39374819 : Blo 1120629 39374819 := bstep (se 1 (by rfl) ⟨29531114, by rfl⟩ : syracuseStep 39374819 = 59062229) B59062229
theorem B2838503 : Blo 1120629 2838503 := bstep (se 1 (by rfl) ⟨2128877, by rfl⟩ : syracuseStep 2838503 = 4257755) B4257755
theorem B2838523 : Blo 1120629 2838523 := bstep (se 1 (by rfl) ⟨2128892, by rfl⟩ : syracuseStep 2838523 = 4257785) B4257785
theorem B3788855 : Blo 1120629 3788855 := bstep (se 1 (by rfl) ⟨2841641, by rfl⟩ : syracuseStep 3788855 = 5683283) B5683283
theorem B2019431 : Blo 1120629 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B3789179 : Blo 1120629 3789179 := bstep (se 1 (by rfl) ⟨2841884, by rfl⟩ : syracuseStep 3789179 = 5683769) B5683769
theorem B14406011 : Blo 1120629 14406011 := bstep (se 1 (by rfl) ⟨10804508, by rfl⟩ : syracuseStep 14406011 = 21609017) B21609017
theorem B3789449 : Blo 1120629 3789449 := bstep (se 2 (by rfl) ⟨1421043, by rfl⟩ : syracuseStep 3789449 = 2842087) B2842087
theorem B3199763 : Blo 1120629 3199763 := bstep (se 1 (by rfl) ⟨2399822, by rfl⟩ : syracuseStep 3199763 = 4799645) B4799645
theorem B9098075 : Blo 1120629 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B7199057 : Blo 1120629 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B6838715 : Blo 1120629 6838715 := bstep (se 1 (by rfl) ⟨5129036, by rfl⟩ : syracuseStep 6838715 = 10258073) B10258073
theorem B2841065 : Blo 1120629 2841065 := bstep (se 2 (by rfl) ⟨1065399, by rfl⟩ : syracuseStep 2841065 = 2130799) B2130799
theorem B5396969 : Blo 1120629 5396969 := bstep (se 2 (by rfl) ⟨2023863, by rfl⟩ : syracuseStep 5396969 = 4047727) B4047727
theorem B2841115 : Blo 1120629 2841115 := bstep (se 1 (by rfl) ⟨2130836, by rfl⟩ : syracuseStep 2841115 = 4261673) B4261673
theorem B2186041 : Blo 1120629 2186041 := bstep (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) B1639531
theorem B20503367 : Blo 1120629 20503367 := bstep (se 1 (by rfl) ⟨15377525, by rfl⟩ : syracuseStep 20503367 = 30755051) B30755051
theorem B9591635 : Blo 1120629 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B26270569 : Blo 1120629 26270569 := bstep (se 2 (by rfl) ⟨9851463, by rfl⟩ : syracuseStep 26270569 = 19702927) B19702927
theorem B1892207 : Blo 1120629 1892207 := bstep (se 1 (by rfl) ⟨1419155, by rfl⟩ : syracuseStep 1892207 = 2838311) B2838311
theorem B2842523 : Blo 1120629 2842523 := bstep (se 1 (by rfl) ⟨2131892, by rfl⟩ : syracuseStep 2842523 = 4263785) B4263785
theorem B12804155 : Blo 1120629 12804155 := bstep (se 1 (by rfl) ⟨9603116, by rfl⟩ : syracuseStep 12804155 = 19206233) B19206233
theorem B1893071 : Blo 1120629 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B7201723 : Blo 1120629 7201723 := bstep (se 1 (by rfl) ⟨5401292, by rfl⟩ : syracuseStep 7201723 = 10802585) B10802585
theorem B19162493 : Blo 1120629 19162493 := bstep (se 3 (by rfl) ⟨3592967, by rfl⟩ : syracuseStep 19162493 = 7185935) B7185935
theorem B1894367 : Blo 1120629 1894367 := bstep (se 1 (by rfl) ⟨1420775, by rfl⟩ : syracuseStep 1894367 = 2841551) B2841551
theorem B2844659 : Blo 1120629 2844659 := bstep (se 1 (by rfl) ⟨2133494, by rfl⟩ : syracuseStep 2844659 = 4266989) B4266989
theorem B6580217 : Blo 1120629 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B1894711 : Blo 1120629 1894711 := bstep (se 1 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 1894711 = 2842067) B2842067
theorem B5401025 : Blo 1120629 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B1896007 : Blo 1120629 1896007 := bstep (se 1 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 1896007 = 2844011) B2844011
theorem B2846279 : Blo 1120629 2846279 := bstep (se 1 (by rfl) ⟨2134709, by rfl⟩ : syracuseStep 2846279 = 4269419) B4269419
theorem B2846299 : Blo 1120629 2846299 := bstep (se 1 (by rfl) ⟨2134724, by rfl⟩ : syracuseStep 2846299 = 4269449) B4269449
theorem B4255841 : Blo 1120629 4255841 := bstep (se 2 (by rfl) ⟨1595940, by rfl⟩ : syracuseStep 4255841 = 3191881) B3191881
theorem B8090063 : Blo 1120629 8090063 := bstep (se 1 (by rfl) ⟨6067547, by rfl⟩ : syracuseStep 8090063 = 12135095) B12135095
theorem B8516177 : Blo 1120629 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B1897465 : Blo 1120629 1897465 := bstep (se 2 (by rfl) ⟨711549, by rfl⟩ : syracuseStep 1897465 = 1423099) B1423099
theorem B1897735 : Blo 1120629 1897735 := bstep (se 1 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 1897735 = 2846603) B2846603
theorem B184251743 : Blo 1120629 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B49903057 : Blo 1120629 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B4257299 : Blo 1120629 4257299 := bstep (se 1 (by rfl) ⟨3192974, by rfl⟩ : syracuseStep 4257299 = 6385949) B6385949
theorem B8746649 : Blo 1120629 8746649 := bstep (se 2 (by rfl) ⟨3279993, by rfl⟩ : syracuseStep 8746649 = 6559987) B6559987
theorem B4257953 : Blo 1120629 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B2128103 : Blo 1120629 2128103 := bstep (se 1 (by rfl) ⟨1596077, by rfl⟩ : syracuseStep 2128103 = 3192155) B3192155
theorem B23066939 : Blo 1120629 23066939 := bstep (se 1 (by rfl) ⟨17300204, by rfl⟩ : syracuseStep 23066939 = 34600409) B34600409
theorem B2521691 : Blo 1120629 2521691 := bstep (se 1 (by rfl) ⟨1891268, by rfl⟩ : syracuseStep 2521691 = 3782537) B3782537
theorem B9599633 : Blo 1120629 9599633 := bstep (se 2 (by rfl) ⟨3599862, by rfl⟩ : syracuseStep 9599633 = 7199725) B7199725
theorem B2521835 : Blo 1120629 2521835 := bstep (se 1 (by rfl) ⟨1891376, by rfl⟩ : syracuseStep 2521835 = 3782753) B3782753
theorem B2128619 : Blo 1120629 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B5765897 : Blo 1120629 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B8518607 : Blo 1120629 8518607 := bstep (se 1 (by rfl) ⟨6388955, by rfl⟩ : syracuseStep 8518607 = 12777911) B12777911
theorem B2522447 : Blo 1120629 2522447 := bstep (se 1 (by rfl) ⟨1891835, by rfl⟩ : syracuseStep 2522447 = 3783671) B3783671
theorem B2522537 : Blo 1120629 2522537 := bstep (se 2 (by rfl) ⟨945951, by rfl⟩ : syracuseStep 2522537 = 1891903) B1891903
theorem B4259243 : Blo 1120629 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B16416215 : Blo 1120629 16416215 := bstep (se 1 (by rfl) ⟨12312161, by rfl⟩ : syracuseStep 16416215 = 24624323) B24624323
theorem B2522735 : Blo 1120629 2522735 := bstep (se 1 (by rfl) ⟨1892051, by rfl⟩ : syracuseStep 2522735 = 3784103) B3784103
theorem B2129743 : Blo 1120629 2129743 := bstep (se 1 (by rfl) ⟨1597307, by rfl⟩ : syracuseStep 2129743 = 3194615) B3194615
theorem B2523023 : Blo 1120629 2523023 := bstep (se 1 (by rfl) ⟨1892267, by rfl⟩ : syracuseStep 2523023 = 3784535) B3784535
theorem B2130047 : Blo 1120629 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B2523815 : Blo 1120629 2523815 := bstep (se 1 (by rfl) ⟨1892861, by rfl⟩ : syracuseStep 2523815 = 3785723) B3785723
theorem B2851609 : Blo 1120629 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B6391007 : Blo 1120629 6391007 := bstep (se 1 (by rfl) ⟨4793255, by rfl⟩ : syracuseStep 6391007 = 9586511) B9586511
theorem B9602297 : Blo 1120629 9602297 := bstep (se 2 (by rfl) ⟨3600861, by rfl⟩ : syracuseStep 9602297 = 7201723) B7201723
theorem B8521037 : Blo 1120629 8521037 := bstep (se 3 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 8521037 = 3195389) B3195389
theorem B26249879 : Blo 1120629 26249879 := bstep (se 1 (by rfl) ⟨19687409, by rfl⟩ : syracuseStep 26249879 = 39374819) B39374819
theorem B2525903 : Blo 1120629 2525903 := bstep (se 1 (by rfl) ⟨1894427, by rfl⟩ : syracuseStep 2525903 = 3788855) B3788855
theorem B1346287 : Blo 1120629 1346287 := bstep (se 1 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 1346287 = 2019431) B2019431
theorem B2526119 : Blo 1120629 2526119 := bstep (se 1 (by rfl) ⟨1894589, by rfl⟩ : syracuseStep 2526119 = 3789179) B3789179
theorem B9604007 : Blo 1120629 9604007 := bstep (se 1 (by rfl) ⟨7203005, by rfl⟩ : syracuseStep 9604007 = 14406011) B14406011
theorem B2526281 : Blo 1120629 2526281 := bstep (se 2 (by rfl) ⟨947355, by rfl⟩ : syracuseStep 2526281 = 1894711) B1894711
theorem B2526299 : Blo 1120629 2526299 := bstep (se 1 (by rfl) ⟨1894724, by rfl⟩ : syracuseStep 2526299 = 3789449) B3789449
theorem B6491279 : Blo 1120629 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B6065383 : Blo 1120629 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B3411197 : Blo 1120629 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B1708123 : Blo 1120629 1708123 := bstep (se 1 (by rfl) ⟨1281092, by rfl⟩ : syracuseStep 1708123 = 2562185) B2562185
theorem B13668911 : Blo 1120629 13668911 := bstep (se 1 (by rfl) ⟨10251683, by rfl⟩ : syracuseStep 13668911 = 20503367) B20503367
theorem B6394423 : Blo 1120629 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B2528009 : Blo 1120629 2528009 := bstep (se 2 (by rfl) ⟨948003, by rfl⟩ : syracuseStep 2528009 = 1896007) B1896007
theorem B12949109 : Blo 1120629 12949109 := bstep (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) B1213979
theorem B20486429 : Blo 1120629 20486429 := bstep (se 3 (by rfl) ⟨3841205, by rfl⟩ : syracuseStep 20486429 = 7682411) B7682411
theorem B1120871 : Blo 1120629 1120871 := bstep (se 1 (by rfl) ⟨840653, by rfl⟩ : syracuseStep 1120871 = 1681307) B1681307
theorem B14391917 : Blo 1120629 14391917 := bstep (se 3 (by rfl) ⟨2698484, by rfl⟩ : syracuseStep 14391917 = 5396969) B5396969
theorem B1120895 : Blo 1120629 1120895 := bstep (se 1 (by rfl) ⟨840671, by rfl⟩ : syracuseStep 1120895 = 1681343) B1681343
theorem B2529953 : Blo 1120629 2529953 := bstep (se 2 (by rfl) ⟨948732, by rfl⟩ : syracuseStep 2529953 = 1897465) B1897465
theorem B1121019 : Blo 1120629 1121019 := bstep (se 1 (by rfl) ⟨840764, by rfl⟩ : syracuseStep 1121019 = 1681529) B1681529
theorem B1121275 : Blo 1120629 1121275 := bstep (se 1 (by rfl) ⟨840956, by rfl⟩ : syracuseStep 1121275 = 1681913) B1681913
theorem B2530313 : Blo 1120629 2530313 := bstep (se 2 (by rfl) ⟨948867, by rfl⟩ : syracuseStep 2530313 = 1897735) B1897735
theorem B1121311 : Blo 1120629 1121311 := bstep (se 1 (by rfl) ⟨840983, by rfl⟩ : syracuseStep 1121311 = 1681967) B1681967
theorem B5676317 : Blo 1120629 5676317 := bstep (se 3 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 5676317 = 2128619) B2128619
theorem B1121599 : Blo 1120629 1121599 := bstep (se 1 (by rfl) ⟨841199, by rfl⟩ : syracuseStep 1121599 = 1682399) B1682399
theorem B6823361 : Blo 1120629 6823361 := bstep (se 2 (by rfl) ⟨2558760, by rfl⟩ : syracuseStep 6823361 = 5117521) B5117521
theorem B8527355 : Blo 1120629 8527355 := bstep (se 1 (by rfl) ⟨6395516, by rfl⟩ : syracuseStep 8527355 = 12791033) B12791033
theorem B14392889 : Blo 1120629 14392889 := bstep (se 2 (by rfl) ⟨5397333, by rfl⟩ : syracuseStep 14392889 = 10794667) B10794667
theorem B1121895 : Blo 1120629 1121895 := bstep (se 1 (by rfl) ⟨841421, by rfl⟩ : syracuseStep 1121895 = 1682843) B1682843
theorem B1122175 : Blo 1120629 1122175 := bstep (se 1 (by rfl) ⟨841631, by rfl⟩ : syracuseStep 1122175 = 1683263) B1683263
theorem B4267991 : Blo 1120629 4267991 := bstep (se 1 (by rfl) ⟨3200993, by rfl⟩ : syracuseStep 4267991 = 6401987) B6401987
theorem B1122299 : Blo 1120629 1122299 := bstep (se 1 (by rfl) ⟨841724, by rfl⟩ : syracuseStep 1122299 = 1683449) B1683449
theorem B1122459 : Blo 1120629 1122459 := bstep (se 1 (by rfl) ⟨841844, by rfl⟩ : syracuseStep 1122459 = 1683689) B1683689
theorem B1122543 : Blo 1120629 1122543 := bstep (se 1 (by rfl) ⟨841907, by rfl⟩ : syracuseStep 1122543 = 1683815) B1683815
theorem B5677451 : Blo 1120629 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B14229989 : Blo 1120629 14229989 := bstep (se 4 (by rfl) ⟨1334061, by rfl⟩ : syracuseStep 14229989 = 2668123) B2668123
theorem B1122907 : Blo 1120629 1122907 := bstep (se 1 (by rfl) ⟨842180, by rfl⟩ : syracuseStep 1122907 = 1684361) B1684361
theorem B1123163 : Blo 1120629 1123163 := bstep (se 1 (by rfl) ⟨842372, by rfl⟩ : syracuseStep 1123163 = 1684745) B1684745
theorem B1123199 : Blo 1120629 1123199 := bstep (se 1 (by rfl) ⟨842399, by rfl⟩ : syracuseStep 1123199 = 1684799) B1684799
theorem B30679955 : Blo 1120629 30679955 := bstep (se 1 (by rfl) ⟨23009966, by rfl⟩ : syracuseStep 30679955 = 46019933) B46019933
theorem B27272335 : Blo 1120629 27272335 := bstep (se 1 (by rfl) ⟨20454251, by rfl⟩ : syracuseStep 27272335 = 40908503) B40908503
theorem B1123483 : Blo 1120629 1123483 := bstep (se 1 (by rfl) ⟨842612, by rfl⟩ : syracuseStep 1123483 = 1685225) B1685225
theorem B1123487 : Blo 1120629 1123487 := bstep (se 1 (by rfl) ⟨842615, by rfl⟩ : syracuseStep 1123487 = 1685231) B1685231
theorem B2499931 : Blo 1120629 2499931 := bstep (se 1 (by rfl) ⟨1874948, by rfl⟩ : syracuseStep 2499931 = 3749897) B3749897
theorem B1123791 : Blo 1120629 1123791 := bstep (se 1 (by rfl) ⟨842843, by rfl⟩ : syracuseStep 1123791 = 1685687) B1685687
theorem B1418735 : Blo 1120629 1418735 := bstep (se 1 (by rfl) ⟨1064051, by rfl⟩ : syracuseStep 1418735 = 2128103) B2128103
theorem B1123823 : Blo 1120629 1123823 := bstep (se 1 (by rfl) ⟨842867, by rfl⟩ : syracuseStep 1123823 = 1685735) B1685735
theorem B15377959 : Blo 1120629 15377959 := bstep (se 1 (by rfl) ⟨11533469, by rfl⟩ : syracuseStep 15377959 = 23066939) B23066939
theorem B1681001 : Blo 1120629 1681001 := bstep (se 2 (by rfl) ⟨630375, by rfl⟩ : syracuseStep 1681001 = 1260751) B1260751
theorem B2696879 : Blo 1120629 2696879 := bstep (se 1 (by rfl) ⟨2022659, by rfl⟩ : syracuseStep 2696879 = 4045319) B4045319
theorem B1681127 : Blo 1120629 1681127 := bstep (se 1 (by rfl) ⟨1260845, by rfl⟩ : syracuseStep 1681127 = 2521691) B2521691
theorem B1124071 : Blo 1120629 1124071 := bstep (se 1 (by rfl) ⟨843053, by rfl⟩ : syracuseStep 1124071 = 1686107) B1686107
theorem B6399755 : Blo 1120629 6399755 := bstep (se 1 (by rfl) ⟨4799816, by rfl⟩ : syracuseStep 6399755 = 9599633) B9599633
theorem B1681223 : Blo 1120629 1681223 := bstep (se 1 (by rfl) ⟨1260917, by rfl⟩ : syracuseStep 1681223 = 2521835) B2521835
theorem B1124167 : Blo 1120629 1124167 := bstep (se 1 (by rfl) ⟨843125, by rfl⟩ : syracuseStep 1124167 = 1686251) B1686251
theorem B3843931 : Blo 1120629 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B1124187 : Blo 1120629 1124187 := bstep (se 1 (by rfl) ⟨843140, by rfl⟩ : syracuseStep 1124187 = 1686281) B1686281
theorem B5679071 : Blo 1120629 5679071 := bstep (se 1 (by rfl) ⟨4259303, by rfl⟩ : syracuseStep 5679071 = 8518607) B8518607
theorem B1681631 : Blo 1120629 1681631 := bstep (se 1 (by rfl) ⟨1261223, by rfl⟩ : syracuseStep 1681631 = 2522447) B2522447
theorem B1681691 : Blo 1120629 1681691 := bstep (se 1 (by rfl) ⟨1261268, by rfl⟩ : syracuseStep 1681691 = 2522537) B2522537
theorem B1681823 : Blo 1120629 1681823 := bstep (se 1 (by rfl) ⟨1261367, by rfl⟩ : syracuseStep 1681823 = 2522735) B2522735
theorem B1682015 : Blo 1120629 1682015 := bstep (se 1 (by rfl) ⟨1261511, by rfl⟩ : syracuseStep 1682015 = 2523023) B2523023
theorem B4926347 : Blo 1120629 4926347 := bstep (se 1 (by rfl) ⟨3694760, by rfl⟩ : syracuseStep 4926347 = 7389521) B7389521
theorem B1682345 : Blo 1120629 1682345 := bstep (se 2 (by rfl) ⟨630879, by rfl⟩ : syracuseStep 1682345 = 1261759) B1261759
theorem B1682375 : Blo 1120629 1682375 := bstep (se 1 (by rfl) ⟨1261781, by rfl⟩ : syracuseStep 1682375 = 2523563) B2523563
theorem B1682495 : Blo 1120629 1682495 := bstep (se 1 (by rfl) ⟨1261871, by rfl⟩ : syracuseStep 1682495 = 2523743) B2523743
theorem B1682735 : Blo 1120629 1682735 := bstep (se 1 (by rfl) ⟨1262051, by rfl⟩ : syracuseStep 1682735 = 2524103) B2524103
theorem B1682921 : Blo 1120629 1682921 := bstep (se 2 (by rfl) ⟨631095, by rfl⟩ : syracuseStep 1682921 = 1262191) B1262191
theorem B1682975 : Blo 1120629 1682975 := bstep (se 1 (by rfl) ⟨1262231, by rfl⟩ : syracuseStep 1682975 = 2524463) B2524463
theorem B1420831 : Blo 1120629 1420831 := bstep (se 1 (by rfl) ⟨1065623, by rfl⟩ : syracuseStep 1420831 = 2131247) B2131247
theorem B9580153 : Blo 1120629 9580153 := bstep (se 2 (by rfl) ⟨3592557, by rfl⟩ : syracuseStep 9580153 = 7185115) B7185115
theorem B1683065 : Blo 1120629 1683065 := bstep (se 2 (by rfl) ⟨631149, by rfl⟩ : syracuseStep 1683065 = 1262299) B1262299
theorem B1683311 : Blo 1120629 1683311 := bstep (se 1 (by rfl) ⟨1262483, by rfl⟩ : syracuseStep 1683311 = 2524967) B2524967
theorem B1683563 : Blo 1120629 1683563 := bstep (se 1 (by rfl) ⟨1262672, by rfl⟩ : syracuseStep 1683563 = 2525345) B2525345
theorem B13643963 : Blo 1120629 13643963 := bstep (se 1 (by rfl) ⟨10232972, by rfl⟩ : syracuseStep 13643963 = 20465945) B20465945
theorem B14397911 : Blo 1120629 14397911 := bstep (se 1 (by rfl) ⟨10798433, by rfl⟩ : syracuseStep 14397911 = 21596867) B21596867
theorem B1683995 : Blo 1120629 1683995 := bstep (se 1 (by rfl) ⟨1262996, by rfl⟩ : syracuseStep 1683995 = 2525993) B2525993
theorem B28815911 : Blo 1120629 28815911 := bstep (se 1 (by rfl) ⟨21611933, by rfl⟩ : syracuseStep 28815911 = 43223867) B43223867
theorem B19149371 : Blo 1120629 19149371 := bstep (se 1 (by rfl) ⟨14362028, by rfl⟩ : syracuseStep 19149371 = 28724057) B28724057
theorem B5681825 : Blo 1120629 5681825 := bstep (se 2 (by rfl) ⟨2130684, by rfl⟩ : syracuseStep 5681825 = 4261369) B4261369
theorem B1684175 : Blo 1120629 1684175 := bstep (se 1 (by rfl) ⟨1263131, by rfl⟩ : syracuseStep 1684175 = 2526263) B2526263
theorem B1422031 : Blo 1120629 1422031 := bstep (se 1 (by rfl) ⟨1066523, by rfl⟩ : syracuseStep 1422031 = 2133047) B2133047
theorem B8532701 : Blo 1120629 8532701 := bstep (se 3 (by rfl) ⟨1599881, by rfl⟩ : syracuseStep 8532701 = 3199763) B3199763
theorem B6402989 : Blo 1120629 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B1684463 : Blo 1120629 1684463 := bstep (se 1 (by rfl) ⟨1263347, by rfl⟩ : syracuseStep 1684463 = 2526695) B2526695
theorem B1684847 : Blo 1120629 1684847 := bstep (se 1 (by rfl) ⟨1263635, by rfl⟩ : syracuseStep 1684847 = 2527271) B2527271
theorem B1684967 : Blo 1120629 1684967 := bstep (se 1 (by rfl) ⟨1263725, by rfl⟩ : syracuseStep 1684967 = 2527451) B2527451
theorem B1685147 : Blo 1120629 1685147 := bstep (se 1 (by rfl) ⟨1263860, by rfl⟩ : syracuseStep 1685147 = 2527721) B2527721
theorem B1423003 : Blo 1120629 1423003 := bstep (se 1 (by rfl) ⟨1067252, by rfl⟩ : syracuseStep 1423003 = 2134505) B2134505
theorem B1685483 : Blo 1120629 1685483 := bstep (se 1 (by rfl) ⟨1264112, by rfl⟩ : syracuseStep 1685483 = 2528225) B2528225
theorem B1685567 : Blo 1120629 1685567 := bstep (se 1 (by rfl) ⟨1264175, by rfl⟩ : syracuseStep 1685567 = 2528351) B2528351
theorem B1685897 : Blo 1120629 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B1686071 : Blo 1120629 1686071 := bstep (se 1 (by rfl) ⟨1264553, by rfl⟩ : syracuseStep 1686071 = 2529107) B2529107
theorem B1686395 : Blo 1120629 1686395 := bstep (se 1 (by rfl) ⟨1264796, by rfl⟩ : syracuseStep 1686395 = 2529593) B2529593
theorem B1621289 : Blo 1120629 1621289 := bstep (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) B1215967
theorem B11517713 : Blo 1120629 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B1261471 : Blo 1120629 1261471 := bstep (se 1 (by rfl) ⟨946103, by rfl⟩ : syracuseStep 1261471 = 1892207) B1892207
theorem B3784697 : Blo 1120629 3784697 := bstep (se 2 (by rfl) ⟨1419261, by rfl⟩ : syracuseStep 3784697 = 2838523) B2838523
theorem B49299457 : Blo 1120629 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B8536103 : Blo 1120629 8536103 := bstep (se 1 (by rfl) ⟨6402077, by rfl⟩ : syracuseStep 8536103 = 12804155) B12804155
theorem B5685551 : Blo 1120629 5685551 := bstep (se 1 (by rfl) ⟨4264163, by rfl⟩ : syracuseStep 5685551 = 8528327) B8528327
theorem B1262047 : Blo 1120629 1262047 := bstep (se 1 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 1262047 = 1893071) B1893071
theorem B25969157 : Blo 1120629 25969157 := bstep (se 4 (by rfl) ⟨2434608, by rfl⟩ : syracuseStep 25969157 = 4869217) B4869217
theorem B8078413 : Blo 1120629 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B18236573 : Blo 1120629 18236573 := bstep (se 3 (by rfl) ⟨3419357, by rfl⟩ : syracuseStep 18236573 = 6838715) B6838715
theorem B1262911 : Blo 1120629 1262911 := bstep (se 1 (by rfl) ⟨947183, by rfl⟩ : syracuseStep 1262911 = 1894367) B1894367
theorem B43763095 : Blo 1120629 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B5687009 : Blo 1120629 5687009 := bstep (se 2 (by rfl) ⟨2132628, by rfl⟩ : syracuseStep 5687009 = 4265257) B4265257
theorem B66537409 : Blo 1120629 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B3197531 : Blo 1120629 3197531 := bstep (se 1 (by rfl) ⟨2398148, by rfl⟩ : syracuseStep 3197531 = 4796297) B4796297
theorem B2837227 : Blo 1120629 2837227 := bstep (se 1 (by rfl) ⟨2127920, by rfl⟩ : syracuseStep 2837227 = 4255841) B4255841
theorem B4868873 : Blo 1120629 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B5393375 : Blo 1120629 5393375 := bstep (se 1 (by rfl) ⟨4045031, by rfl⟩ : syracuseStep 5393375 = 8090063) B8090063
theorem B3787991 : Blo 1120629 3787991 := bstep (se 1 (by rfl) ⟨2840993, by rfl⟩ : syracuseStep 3787991 = 5681987) B5681987
theorem B3788153 : Blo 1120629 3788153 := bstep (se 2 (by rfl) ⟨1420557, by rfl⟩ : syracuseStep 3788153 = 2841115) B2841115
theorem B3198329 : Blo 1120629 3198329 := bstep (se 2 (by rfl) ⟨1199373, by rfl⟩ : syracuseStep 3198329 = 2398747) B2398747
theorem B122834495 : Blo 1120629 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B2838199 : Blo 1120629 2838199 := bstep (se 1 (by rfl) ⟨2128649, by rfl⟩ : syracuseStep 2838199 = 4257299) B4257299
theorem B3788531 : Blo 1120629 3788531 := bstep (se 1 (by rfl) ⟨2841398, by rfl⟩ : syracuseStep 3788531 = 5682797) B5682797
theorem B12308287 : Blo 1120629 12308287 := bstep (se 1 (by rfl) ⟨9231215, by rfl⟩ : syracuseStep 12308287 = 18462431) B18462431
theorem B5689277 : Blo 1120629 5689277 := bstep (se 3 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 5689277 = 2133479) B2133479
theorem B5689439 : Blo 1120629 5689439 := bstep (se 1 (by rfl) ⟨4267079, by rfl⟩ : syracuseStep 5689439 = 8534159) B8534159
theorem B2838635 : Blo 1120629 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B5690087 : Blo 1120629 5690087 := bstep (se 1 (by rfl) ⟨4267565, by rfl⟩ : syracuseStep 5690087 = 8535131) B8535131
theorem B2839495 : Blo 1120629 2839495 := bstep (se 1 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 2839495 = 4259243) B4259243
theorem B2839657 : Blo 1120629 2839657 := bstep (se 2 (by rfl) ⟨1064871, by rfl⟩ : syracuseStep 2839657 = 2129743) B2129743
theorem B2840143 : Blo 1120629 2840143 := bstep (se 1 (by rfl) ⟨2130107, by rfl⟩ : syracuseStep 2840143 = 4260215) B4260215
theorem B2021039 : Blo 1120629 2021039 := bstep (se 1 (by rfl) ⟨1515779, by rfl⟩ : syracuseStep 2021039 = 3031559) B3031559
theorem B2840255 : Blo 1120629 2840255 := bstep (se 1 (by rfl) ⟨2130191, by rfl⟩ : syracuseStep 2840255 = 4260383) B4260383
theorem B3200755 : Blo 1120629 3200755 := bstep (se 1 (by rfl) ⟨2400566, by rfl⟩ : syracuseStep 3200755 = 4801133) B4801133
theorem B3790583 : Blo 1120629 3790583 := bstep (se 1 (by rfl) ⟨2842937, by rfl⟩ : syracuseStep 3790583 = 5685875) B5685875
theorem B5691383 : Blo 1120629 5691383 := bstep (se 1 (by rfl) ⟨4268537, by rfl⟩ : syracuseStep 5691383 = 8537075) B8537075
theorem B2840791 : Blo 1120629 2840791 := bstep (se 1 (by rfl) ⟨2130593, by rfl⟩ : syracuseStep 2840791 = 4261187) B4261187
theorem B3791123 : Blo 1120629 3791123 := bstep (se 1 (by rfl) ⟨2843342, by rfl⟩ : syracuseStep 3791123 = 5686685) B5686685
theorem B3791231 : Blo 1120629 3791231 := bstep (se 1 (by rfl) ⟨2843423, by rfl⟩ : syracuseStep 3791231 = 5686847) B5686847
theorem B2841095 : Blo 1120629 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B3791663 : Blo 1120629 3791663 := bstep (se 1 (by rfl) ⟨2843747, by rfl⟩ : syracuseStep 3791663 = 5687495) B5687495
theorem B3202247 : Blo 1120629 3202247 := bstep (se 1 (by rfl) ⟨2401685, by rfl⟩ : syracuseStep 3202247 = 4803371) B4803371
theorem B1891559 : Blo 1120629 1891559 := bstep (se 1 (by rfl) ⟨1418669, by rfl⟩ : syracuseStep 1891559 = 2837339) B2837339
theorem B1891579 : Blo 1120629 1891579 := bstep (se 1 (by rfl) ⟨1418684, by rfl⟩ : syracuseStep 1891579 = 2837369) B2837369
theorem B12770621 : Blo 1120629 12770621 := bstep (se 3 (by rfl) ⟨2394491, by rfl⟩ : syracuseStep 12770621 = 4788983) B4788983
theorem B3071353 : Blo 1120629 3071353 := bstep (se 2 (by rfl) ⟨1151757, by rfl⟩ : syracuseStep 3071353 = 2303515) B2303515
theorem B3202487 : Blo 1120629 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B8084929 : Blo 1120629 8084929 := bstep (se 2 (by rfl) ⟨3031848, by rfl⟩ : syracuseStep 8084929 = 6063697) B6063697
theorem B10510235 : Blo 1120629 10510235 := bstep (se 1 (by rfl) ⟨7882676, by rfl⟩ : syracuseStep 10510235 = 15765353) B15765353
theorem B1892335 : Blo 1120629 1892335 := bstep (se 1 (by rfl) ⟨1419251, by rfl⟩ : syracuseStep 1892335 = 2838503) B2838503
theorem B1597735 : Blo 1120629 1597735 := bstep (se 1 (by rfl) ⟨1198301, by rfl⟩ : syracuseStep 1597735 = 2396603) B2396603
theorem B23356289 : Blo 1120629 23356289 := bstep (se 2 (by rfl) ⟨8758608, by rfl⟩ : syracuseStep 23356289 = 17517217) B17517217
theorem B1598555 : Blo 1120629 1598555 := bstep (se 1 (by rfl) ⟨1198916, by rfl⟩ : syracuseStep 1598555 = 2397833) B2397833
theorem B1894043 : Blo 1120629 1894043 := bstep (se 1 (by rfl) ⟨1420532, by rfl⟩ : syracuseStep 1894043 = 2841065) B2841065
theorem B3795065 : Blo 1120629 3795065 := bstep (se 2 (by rfl) ⟨1423149, by rfl⟩ : syracuseStep 3795065 = 2846299) B2846299
theorem B23718221 : Blo 1120629 23718221 := bstep (se 3 (by rfl) ⟨4447166, by rfl⟩ : syracuseStep 23718221 = 8894333) B8894333
theorem B1895015 : Blo 1120629 1895015 := bstep (se 1 (by rfl) ⟨1421261, by rfl⟩ : syracuseStep 1895015 = 2842523) B2842523
theorem B109211125 : Blo 1120629 109211125 := bstep (se 5 (by rfl) ⟨5119271, by rfl⟩ : syracuseStep 109211125 = 10238543) B10238543
theorem B19197485 : Blo 1120629 19197485 := bstep (se 3 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 19197485 = 7199057) B7199057
theorem B12774995 : Blo 1120629 12774995 := bstep (se 1 (by rfl) ⟨9581246, by rfl⟩ : syracuseStep 12774995 = 19162493) B19162493
theorem B1896439 : Blo 1120629 1896439 := bstep (se 1 (by rfl) ⟨1422329, by rfl⟩ : syracuseStep 1896439 = 2844659) B2844659
theorem B4386811 : Blo 1120629 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B18936017 : Blo 1120629 18936017 := bstep (se 2 (by rfl) ⟨7101006, by rfl⟩ : syracuseStep 18936017 = 14202013) B14202013
theorem B3600683 : Blo 1120629 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B1798939 : Blo 1120629 1798939 := bstep (se 1 (by rfl) ⟨1349204, by rfl⟩ : syracuseStep 1798939 = 2698409) B2698409
theorem B1897519 : Blo 1120629 1897519 := bstep (se 1 (by rfl) ⟨1423139, by rfl⟩ : syracuseStep 1897519 = 2846279) B2846279
theorem B6386951 : Blo 1120629 6386951 := bstep (se 1 (by rfl) ⟨4790213, by rfl⟩ : syracuseStep 6386951 = 9580427) B9580427
theorem B2914721 : Blo 1120629 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B5831099 : Blo 1120629 5831099 := bstep (se 1 (by rfl) ⟨4373324, by rfl⟩ : syracuseStep 5831099 = 8746649) B8746649
theorem B35027425 : Blo 1120629 35027425 := bstep (se 2 (by rfl) ⟨13135284, by rfl⟩ : syracuseStep 35027425 = 26270569) B26270569
theorem B14383763 : Blo 1120629 14383763 := bstep (se 1 (by rfl) ⟨10787822, by rfl⟩ : syracuseStep 14383763 = 21575645) B21575645
theorem B10255151 : Blo 1120629 10255151 := bstep (se 1 (by rfl) ⟨7691363, by rfl⟩ : syracuseStep 10255151 = 15382727) B15382727
theorem B6388591 : Blo 1120629 6388591 := bstep (se 1 (by rfl) ⟨4791443, by rfl⟩ : syracuseStep 6388591 = 9582887) B9582887
theorem B2522267 : Blo 1120629 2522267 := bstep (se 1 (by rfl) ⟨1891700, by rfl⟩ : syracuseStep 2522267 = 3783401) B3783401
theorem B10944143 : Blo 1120629 10944143 := bstep (se 1 (by rfl) ⟨8208107, by rfl⟩ : syracuseStep 10944143 = 16416215) B16416215
theorem B65732609 : Blo 1120629 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B2130313 : Blo 1120629 2130313 := bstep (se 2 (by rfl) ⟨798867, by rfl⟩ : syracuseStep 2130313 = 1597735) B1597735
theorem B12157715 : Blo 1120629 12157715 := bstep (se 1 (by rfl) ⟨9118286, by rfl⟩ : syracuseStep 12157715 = 18236573) B18236573
theorem B4260671 : Blo 1120629 4260671 := bstep (se 1 (by rfl) ⟨3195503, by rfl⟩ : syracuseStep 4260671 = 6391007) B6391007
theorem B3802145 : Blo 1120629 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B2131687 : Blo 1120629 2131687 := bstep (se 1 (by rfl) ⟨1598765, by rfl⟩ : syracuseStep 2131687 = 3197531) B3197531
theorem B17499919 : Blo 1120629 17499919 := bstep (se 1 (by rfl) ⟨13124939, by rfl⟩ : syracuseStep 17499919 = 26249879) B26249879
theorem B3245915 : Blo 1120629 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B4327519 : Blo 1120629 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B2525327 : Blo 1120629 2525327 := bstep (se 1 (by rfl) ⟨1893995, by rfl⟩ : syracuseStep 2525327 = 3787991) B3787991
theorem B2525435 : Blo 1120629 2525435 := bstep (se 1 (by rfl) ⟨1894076, by rfl⟩ : syracuseStep 2525435 = 3788153) B3788153
theorem B2132219 : Blo 1120629 2132219 := bstep (se 1 (by rfl) ⟨1599164, by rfl⟩ : syracuseStep 2132219 = 3198329) B3198329
theorem B81889663 : Blo 1120629 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B2525687 : Blo 1120629 2525687 := bstep (se 1 (by rfl) ⟨1894265, by rfl⟩ : syracuseStep 2525687 = 3788531) B3788531
theorem B4262813 : Blo 1120629 4262813 := bstep (se 3 (by rfl) ⟨799277, by rfl⟩ : syracuseStep 4262813 = 1598555) B1598555
theorem B9112607 : Blo 1120629 9112607 := bstep (se 1 (by rfl) ⟨6834455, by rfl⟩ : syracuseStep 9112607 = 13668911) B13668911
theorem B1347359 : Blo 1120629 1347359 := bstep (se 1 (by rfl) ⟨1010519, by rfl⟩ : syracuseStep 1347359 = 2021039) B2021039
theorem B2527055 : Blo 1120629 2527055 := bstep (se 1 (by rfl) ⟨1895291, by rfl⟩ : syracuseStep 2527055 = 3790583) B3790583
theorem B2527415 : Blo 1120629 2527415 := bstep (se 1 (by rfl) ⟨1895561, by rfl⟩ : syracuseStep 2527415 = 3791123) B3791123
theorem B2527487 : Blo 1120629 2527487 := bstep (se 1 (by rfl) ⟨1895615, by rfl⟩ : syracuseStep 2527487 = 3791231) B3791231
theorem B2527775 : Blo 1120629 2527775 := bstep (se 1 (by rfl) ⟨1895831, by rfl⟩ : syracuseStep 2527775 = 3791663) B3791663
theorem B2134831 : Blo 1120629 2134831 := bstep (se 1 (by rfl) ⟨1601123, by rfl⟩ : syracuseStep 2134831 = 3202247) B3202247
theorem B2134991 : Blo 1120629 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B2528585 : Blo 1120629 2528585 := bstep (se 2 (by rfl) ⟨948219, by rfl⟩ : syracuseStep 2528585 = 1896439) B1896439
theorem B20453303 : Blo 1120629 20453303 := bstep (se 1 (by rfl) ⟨15339977, by rfl⟩ : syracuseStep 20453303 = 30679955) B30679955
theorem B8525897 : Blo 1120629 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B2398585 : Blo 1120629 2398585 := bstep (se 2 (by rfl) ⟨899469, by rfl⟩ : syracuseStep 2398585 = 1798939) B1798939
theorem B1120667 : Blo 1120629 1120667 := bstep (se 1 (by rfl) ⟨840500, by rfl⟩ : syracuseStep 1120667 = 1681001) B1681001
theorem B1120751 : Blo 1120629 1120751 := bstep (se 1 (by rfl) ⟨840563, by rfl⟩ : syracuseStep 1120751 = 1681127) B1681127
theorem B4266503 : Blo 1120629 4266503 := bstep (se 1 (by rfl) ⟨3199877, by rfl⟩ : syracuseStep 4266503 = 6399755) B6399755
theorem B1120815 : Blo 1120629 1120815 := bstep (se 1 (by rfl) ⟨840611, by rfl⟩ : syracuseStep 1120815 = 1681223) B1681223
theorem B2530025 : Blo 1120629 2530025 := bstep (se 2 (by rfl) ⟨948759, by rfl⟩ : syracuseStep 2530025 = 1897519) B1897519
theorem B2530043 : Blo 1120629 2530043 := bstep (se 1 (by rfl) ⟨1897532, by rfl⟩ : syracuseStep 2530043 = 3795065) B3795065
theorem B1121087 : Blo 1120629 1121087 := bstep (se 1 (by rfl) ⟨840815, by rfl⟩ : syracuseStep 1121087 = 1681631) B1681631
theorem B1121127 : Blo 1120629 1121127 := bstep (se 1 (by rfl) ⟨840845, by rfl⟩ : syracuseStep 1121127 = 1681691) B1681691
theorem B1121215 : Blo 1120629 1121215 := bstep (se 1 (by rfl) ⟨840911, by rfl⟩ : syracuseStep 1121215 = 1681823) B1681823
theorem B1121343 : Blo 1120629 1121343 := bstep (se 1 (by rfl) ⟨841007, by rfl⟩ : syracuseStep 1121343 = 1682015) B1682015
theorem B3284231 : Blo 1120629 3284231 := bstep (se 1 (by rfl) ⟨2463173, by rfl⟩ : syracuseStep 3284231 = 4926347) B4926347
theorem B1121563 : Blo 1120629 1121563 := bstep (se 1 (by rfl) ⟨841172, by rfl⟩ : syracuseStep 1121563 = 1682345) B1682345
theorem B1121583 : Blo 1120629 1121583 := bstep (se 1 (by rfl) ⟨841187, by rfl⟩ : syracuseStep 1121583 = 1682375) B1682375
theorem B1121663 : Blo 1120629 1121663 := bstep (se 1 (by rfl) ⟨841247, by rfl⟩ : syracuseStep 1121663 = 1682495) B1682495
theorem B1121823 : Blo 1120629 1121823 := bstep (se 1 (by rfl) ⟨841367, by rfl⟩ : syracuseStep 1121823 = 1682735) B1682735
theorem B4267673 : Blo 1120629 4267673 := bstep (se 2 (by rfl) ⟨1600377, by rfl⟩ : syracuseStep 4267673 = 3200755) B3200755
theorem B1121947 : Blo 1120629 1121947 := bstep (se 1 (by rfl) ⟨841460, by rfl⟩ : syracuseStep 1121947 = 1682921) B1682921
theorem B1121983 : Blo 1120629 1121983 := bstep (se 1 (by rfl) ⟨841487, by rfl⟩ : syracuseStep 1121983 = 1682975) B1682975
theorem B1122043 : Blo 1120629 1122043 := bstep (se 1 (by rfl) ⟨841532, by rfl⟩ : syracuseStep 1122043 = 1683065) B1683065
theorem B1122207 : Blo 1120629 1122207 := bstep (se 1 (by rfl) ⟨841655, by rfl⟩ : syracuseStep 1122207 = 1683311) B1683311
theorem B1122375 : Blo 1120629 1122375 := bstep (se 1 (by rfl) ⟨841781, by rfl⟩ : syracuseStep 1122375 = 1683563) B1683563
theorem B12624011 : Blo 1120629 12624011 := bstep (se 1 (by rfl) ⟨9468008, by rfl⟩ : syracuseStep 12624011 = 18936017) B18936017
theorem B2400455 : Blo 1120629 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B1122663 : Blo 1120629 1122663 := bstep (se 1 (by rfl) ⟨841997, by rfl⟩ : syracuseStep 1122663 = 1683995) B1683995
theorem B19210607 : Blo 1120629 19210607 := bstep (se 1 (by rfl) ⟨14407955, by rfl⟩ : syracuseStep 19210607 = 28815911) B28815911
theorem B1122783 : Blo 1120629 1122783 := bstep (se 1 (by rfl) ⟨842087, by rfl⟩ : syracuseStep 1122783 = 1684175) B1684175
theorem B4268659 : Blo 1120629 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B46703233 : Blo 1120629 46703233 := bstep (se 2 (by rfl) ⟨17513712, by rfl⟩ : syracuseStep 46703233 = 35027425) B35027425
theorem B1122975 : Blo 1120629 1122975 := bstep (se 1 (by rfl) ⟨842231, by rfl⟩ : syracuseStep 1122975 = 1684463) B1684463
theorem B1123231 : Blo 1120629 1123231 := bstep (se 1 (by rfl) ⟨842423, by rfl⟩ : syracuseStep 1123231 = 1684847) B1684847
theorem B1123311 : Blo 1120629 1123311 := bstep (se 1 (by rfl) ⟨842483, by rfl⟩ : syracuseStep 1123311 = 1684967) B1684967
theorem B1123431 : Blo 1120629 1123431 := bstep (se 1 (by rfl) ⟨842573, by rfl⟩ : syracuseStep 1123431 = 1685147) B1685147
theorem B1123655 : Blo 1120629 1123655 := bstep (se 1 (by rfl) ⟨842741, by rfl⟩ : syracuseStep 1123655 = 1685483) B1685483
theorem B1123711 : Blo 1120629 1123711 := bstep (se 1 (by rfl) ⟨842783, by rfl⟩ : syracuseStep 1123711 = 1685567) B1685567
theorem B1123931 : Blo 1120629 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B1943147 : Blo 1120629 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B1124047 : Blo 1120629 1124047 := bstep (se 1 (by rfl) ⟨843035, by rfl⟩ : syracuseStep 1124047 = 1686071) B1686071
theorem B1124263 : Blo 1120629 1124263 := bstep (se 1 (by rfl) ⟨843197, by rfl⟩ : syracuseStep 1124263 = 1686395) B1686395
theorem B1681511 : Blo 1120629 1681511 := bstep (se 1 (by rfl) ⟨1261133, by rfl⟩ : syracuseStep 1681511 = 2522267) B2522267
theorem B7678475 : Blo 1120629 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B1681961 : Blo 1120629 1681961 := bstep (se 2 (by rfl) ⟨630735, by rfl⟩ : syracuseStep 1681961 = 1261471) B1261471
theorem B1420031 : Blo 1120629 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B17312771 : Blo 1120629 17312771 := bstep (se 1 (by rfl) ⟨12984578, by rfl⟩ : syracuseStep 17312771 = 25969157) B25969157
theorem B1682543 : Blo 1120629 1682543 := bstep (se 1 (by rfl) ⟨1261907, by rfl⟩ : syracuseStep 1682543 = 2523815) B2523815
theorem B1682729 : Blo 1120629 1682729 := bstep (se 2 (by rfl) ⟨631023, by rfl⟩ : syracuseStep 1682729 = 1262047) B1262047
theorem B6401531 : Blo 1120629 6401531 := bstep (se 1 (by rfl) ⟨4801148, by rfl⟩ : syracuseStep 6401531 = 9602297) B9602297
theorem B5680691 : Blo 1120629 5680691 := bstep (se 1 (by rfl) ⟨4260518, by rfl⟩ : syracuseStep 5680691 = 8521037) B8521037
theorem B1683881 : Blo 1120629 1683881 := bstep (se 2 (by rfl) ⟨631455, by rfl⟩ : syracuseStep 1683881 = 1262911) B1262911
theorem B1683935 : Blo 1120629 1683935 := bstep (se 1 (by rfl) ⟨1262951, by rfl⟩ : syracuseStep 1683935 = 2525903) B2525903
theorem B1684079 : Blo 1120629 1684079 := bstep (se 1 (by rfl) ⟨1263059, by rfl⟩ : syracuseStep 1684079 = 2526119) B2526119
theorem B6402671 : Blo 1120629 6402671 := bstep (se 1 (by rfl) ⟨4802003, by rfl⟩ : syracuseStep 6402671 = 9604007) B9604007
theorem B1684187 : Blo 1120629 1684187 := bstep (se 1 (by rfl) ⟨1263140, by rfl⟩ : syracuseStep 1684187 = 2526281) B2526281
theorem B1684199 : Blo 1120629 1684199 := bstep (se 1 (by rfl) ⟨1263149, by rfl⟩ : syracuseStep 1684199 = 2526299) B2526299
theorem B2274131 : Blo 1120629 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B5125241 : Blo 1120629 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B88716545 : Blo 1120629 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B1685339 : Blo 1120629 1685339 := bstep (se 1 (by rfl) ⟨1264004, by rfl⟩ : syracuseStep 1685339 = 2528009) B2528009
theorem B3782969 : Blo 1120629 3782969 := bstep (se 2 (by rfl) ⟨1418613, by rfl⟩ : syracuseStep 3782969 = 2837227) B2837227
theorem B8632739 : Blo 1120629 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B3783293 : Blo 1120629 3783293 := bstep (se 3 (by rfl) ⟨709367, by rfl⟩ : syracuseStep 3783293 = 1418735) B1418735
theorem B1686635 : Blo 1120629 1686635 := bstep (se 1 (by rfl) ⟨1264976, by rfl⟩ : syracuseStep 1686635 = 2529953) B2529953
theorem B1686875 : Blo 1120629 1686875 := bstep (se 1 (by rfl) ⟨1265156, by rfl⟩ : syracuseStep 1686875 = 2530313) B2530313
theorem B1261039 : Blo 1120629 1261039 := bstep (se 1 (by rfl) ⟨945779, by rfl⟩ : syracuseStep 1261039 = 1891559) B1891559
theorem B3784211 : Blo 1120629 3784211 := bstep (se 1 (by rfl) ⟨2838158, by rfl⟩ : syracuseStep 3784211 = 5676317) B5676317
theorem B3784265 : Blo 1120629 3784265 := bstep (se 2 (by rfl) ⟨1419099, by rfl⟩ : syracuseStep 3784265 = 2838199) B2838199
theorem B5684903 : Blo 1120629 5684903 := bstep (se 1 (by rfl) ⟨4263677, by rfl⟩ : syracuseStep 5684903 = 8527355) B8527355
theorem B5849081 : Blo 1120629 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B2277497 : Blo 1120629 2277497 := bstep (se 2 (by rfl) ⟨854061, by rfl⟩ : syracuseStep 2277497 = 1708123) B1708123
theorem B3784967 : Blo 1120629 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B9486659 : Blo 1120629 9486659 := bstep (se 1 (by rfl) ⟨7114994, by rfl⟩ : syracuseStep 9486659 = 14229989) B14229989
theorem B1262695 : Blo 1120629 1262695 := bstep (se 1 (by rfl) ⟨947021, by rfl⟩ : syracuseStep 1262695 = 1894043) B1894043
theorem B3785993 : Blo 1120629 3785993 := bstep (se 2 (by rfl) ⟨1419747, by rfl⟩ : syracuseStep 3785993 = 2839495) B2839495
theorem B3786047 : Blo 1120629 3786047 := bstep (se 1 (by rfl) ⟨2839535, by rfl⟩ : syracuseStep 3786047 = 5679071) B5679071
theorem B3786209 : Blo 1120629 3786209 := bstep (se 2 (by rfl) ⟨1419828, by rfl⟩ : syracuseStep 3786209 = 2839657) B2839657
theorem B15812147 : Blo 1120629 15812147 := bstep (se 1 (by rfl) ⟨11859110, by rfl⟩ : syracuseStep 15812147 = 23718221) B23718221
theorem B1263343 : Blo 1120629 1263343 := bstep (se 1 (by rfl) ⟨947507, by rfl⟩ : syracuseStep 1263343 = 1895015) B1895015
theorem B3786857 : Blo 1120629 3786857 := bstep (se 2 (by rfl) ⟨1420071, by rfl⟩ : syracuseStep 3786857 = 2840143) B2840143
theorem B12798323 : Blo 1120629 12798323 := bstep (se 1 (by rfl) ⟨9598742, by rfl⟩ : syracuseStep 12798323 = 19197485) B19197485
theorem B9095975 : Blo 1120629 9095975 := bstep (se 1 (by rfl) ⟨6821981, by rfl⟩ : syracuseStep 9095975 = 13643963) B13643963
theorem B3787721 : Blo 1120629 3787721 := bstep (se 2 (by rfl) ⟨1420395, by rfl⟩ : syracuseStep 3787721 = 2840791) B2840791
theorem B12766247 : Blo 1120629 12766247 := bstep (se 1 (by rfl) ⟨9574685, by rfl⟩ : syracuseStep 12766247 = 19149371) B19149371
theorem B3787883 : Blo 1120629 3787883 := bstep (se 1 (by rfl) ⟨2840912, by rfl⟩ : syracuseStep 3787883 = 5681825) B5681825
theorem B5688467 : Blo 1120629 5688467 := bstep (se 1 (by rfl) ⟨4266350, by rfl⟩ : syracuseStep 5688467 = 8532701) B8532701
theorem B3887399 : Blo 1120629 3887399 := bstep (se 1 (by rfl) ⟨2915549, by rfl⟩ : syracuseStep 3887399 = 5831099) B5831099
theorem B9589175 : Blo 1120629 9589175 := bstep (se 1 (by rfl) ⟨7191881, by rfl⟩ : syracuseStep 9589175 = 14383763) B14383763
theorem B6836767 : Blo 1120629 6836767 := bstep (se 1 (by rfl) ⟨5127575, by rfl⟩ : syracuseStep 6836767 = 10255151) B10255151
theorem B7296095 : Blo 1120629 7296095 := bstep (se 1 (by rfl) ⟨5472071, by rfl⟩ : syracuseStep 7296095 = 10944143) B10944143
theorem B5690735 : Blo 1120629 5690735 := bstep (se 1 (by rfl) ⟨4268051, by rfl⟩ : syracuseStep 5690735 = 8536103) B8536103
theorem B3790367 : Blo 1120629 3790367 := bstep (se 1 (by rfl) ⟨2842775, by rfl⟩ : syracuseStep 3790367 = 5685551) B5685551
theorem B3791339 : Blo 1120629 3791339 := bstep (se 1 (by rfl) ⟨2843504, by rfl⟩ : syracuseStep 3791339 = 5687009) B5687009
theorem B10771217 : Blo 1120629 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B36363113 : Blo 1120629 36363113 := bstep (se 2 (by rfl) ⟨13636167, by rfl⟩ : syracuseStep 36363113 = 27272335) B27272335
theorem B3333241 : Blo 1120629 3333241 := bstep (se 2 (by rfl) ⟨1249965, by rfl⟩ : syracuseStep 3333241 = 2499931) B2499931
theorem B58350793 : Blo 1120629 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B3595583 : Blo 1120629 3595583 := bstep (se 1 (by rfl) ⟨2696687, by rfl⟩ : syracuseStep 3595583 = 5393375) B5393375
theorem B20503945 : Blo 1120629 20503945 := bstep (se 2 (by rfl) ⟨7688979, by rfl⟩ : syracuseStep 20503945 = 15377959) B15377959
theorem B62283437 : Blo 1120629 62283437 := bstep (se 3 (by rfl) ⟨11678144, by rfl⟩ : syracuseStep 62283437 = 23356289) B23356289
theorem B3792851 : Blo 1120629 3792851 := bstep (se 1 (by rfl) ⟨2844638, by rfl⟩ : syracuseStep 3792851 = 5689277) B5689277
theorem B3792959 : Blo 1120629 3792959 := bstep (se 1 (by rfl) ⟨2844719, by rfl⟩ : syracuseStep 3792959 = 5689439) B5689439
theorem B1892423 : Blo 1120629 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B3793391 : Blo 1120629 3793391 := bstep (se 1 (by rfl) ⟨2845043, by rfl⟩ : syracuseStep 3793391 = 5690087) B5690087
theorem B1795049 : Blo 1120629 1795049 := bstep (se 2 (by rfl) ⟨673143, by rfl⟩ : syracuseStep 1795049 = 1346287) B1346287
theorem B1893503 : Blo 1120629 1893503 := bstep (se 1 (by rfl) ⟨1420127, by rfl⟩ : syracuseStep 1893503 = 2840255) B2840255
theorem B3794255 : Blo 1120629 3794255 := bstep (se 1 (by rfl) ⟨2845691, by rfl⟩ : syracuseStep 3794255 = 5691383) B5691383
theorem B13657619 : Blo 1120629 13657619 := bstep (se 1 (by rfl) ⟨10243214, by rfl⟩ : syracuseStep 13657619 = 20486429) B20486429
theorem B8087177 : Blo 1120629 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B1894063 : Blo 1120629 1894063 := bstep (se 1 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 1894063 = 2841095) B2841095
theorem B9594611 : Blo 1120629 9594611 := bstep (se 1 (by rfl) ⟨7195958, by rfl⟩ : syracuseStep 9594611 = 14391917) B14391917
theorem B145614833 : Blo 1120629 145614833 := bstep (se 2 (by rfl) ⟨54605562, by rfl⟩ : syracuseStep 145614833 = 109211125) B109211125
theorem B1894441 : Blo 1120629 1894441 := bstep (se 2 (by rfl) ⟨710415, by rfl⟩ : syracuseStep 1894441 = 1420831) B1420831
theorem B12773537 : Blo 1120629 12773537 := bstep (se 2 (by rfl) ⟨4790076, by rfl⟩ : syracuseStep 12773537 = 9580153) B9580153
theorem B8513747 : Blo 1120629 8513747 := bstep (se 1 (by rfl) ⟨6385310, by rfl⟩ : syracuseStep 8513747 = 12770621) B12770621
theorem B4548907 : Blo 1120629 4548907 := bstep (se 1 (by rfl) ⟨3411680, by rfl⟩ : syracuseStep 4548907 = 6823361) B6823361
theorem B9595259 : Blo 1120629 9595259 := bstep (se 1 (by rfl) ⟨7196444, by rfl⟩ : syracuseStep 9595259 = 14392889) B14392889
theorem B16411049 : Blo 1120629 16411049 := bstep (se 2 (by rfl) ⟨6154143, by rfl⟩ : syracuseStep 16411049 = 12308287) B12308287
theorem B7006823 : Blo 1120629 7006823 := bstep (se 1 (by rfl) ⟨5255117, by rfl⟩ : syracuseStep 7006823 = 10510235) B10510235
theorem B2845327 : Blo 1120629 2845327 := bstep (se 1 (by rfl) ⟨2133995, by rfl⟩ : syracuseStep 2845327 = 4267991) B4267991
theorem B1896041 : Blo 1120629 1896041 := bstep (se 2 (by rfl) ⟨711015, by rfl⟩ : syracuseStep 1896041 = 1422031) B1422031
theorem B1797919 : Blo 1120629 1797919 := bstep (se 1 (by rfl) ⟨1348439, by rfl⟩ : syracuseStep 1797919 = 2696879) B2696879
theorem B1897337 : Blo 1120629 1897337 := bstep (se 2 (by rfl) ⟨711501, by rfl⟩ : syracuseStep 1897337 = 1423003) B1423003
theorem B8516663 : Blo 1120629 8516663 := bstep (se 1 (by rfl) ⟨6387497, by rfl⟩ : syracuseStep 8516663 = 12774995) B12774995
theorem B9598607 : Blo 1120629 9598607 := bstep (se 1 (by rfl) ⟨7198955, by rfl⟩ : syracuseStep 9598607 = 14397911) B14397911
theorem B4323437 : Blo 1120629 4323437 := bstep (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) B1621289
theorem B4257967 : Blo 1120629 4257967 := bstep (se 1 (by rfl) ⟨3193475, by rfl⟩ : syracuseStep 4257967 = 6386951) B6386951
theorem B8518121 : Blo 1120629 8518121 := bstep (se 2 (by rfl) ⟨3194295, by rfl⟩ : syracuseStep 8518121 = 6388591) B6388591
theorem B2522105 : Blo 1120629 2522105 := bstep (se 2 (by rfl) ⟨945789, by rfl⟩ : syracuseStep 2522105 = 1891579) B1891579
theorem B4095137 : Blo 1120629 4095137 := bstep (se 2 (by rfl) ⟨1535676, by rfl⟩ : syracuseStep 4095137 = 3071353) B3071353
theorem B10779905 : Blo 1120629 10779905 := bstep (se 2 (by rfl) ⟨4042464, by rfl⟩ : syracuseStep 10779905 = 8084929) B8084929
theorem B2523113 : Blo 1120629 2523113 := bstep (se 2 (by rfl) ⟨946167, by rfl⟩ : syracuseStep 2523113 = 1892335) B1892335
theorem B2523131 : Blo 1120629 2523131 := bstep (se 1 (by rfl) ⟨1892348, by rfl⟩ : syracuseStep 2523131 = 3784697) B3784697
theorem B2523311 : Blo 1120629 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B6324439 : Blo 1120629 6324439 := bstep (se 1 (by rfl) ⟨4743329, by rfl⟩ : syracuseStep 6324439 = 9486659) B9486659
theorem B2523995 : Blo 1120629 2523995 := bstep (se 1 (by rfl) ⟨1892996, by rfl⟩ : syracuseStep 2523995 = 3785993) B3785993
theorem B2524031 : Blo 1120629 2524031 := bstep (se 1 (by rfl) ⟨1893023, by rfl⟩ : syracuseStep 2524031 = 3786047) B3786047
theorem B2524139 : Blo 1120629 2524139 := bstep (se 1 (by rfl) ⟨1893104, by rfl⟩ : syracuseStep 2524139 = 3786209) B3786209
theorem B2163943 : Blo 1120629 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B2524571 : Blo 1120629 2524571 := bstep (se 1 (by rfl) ⟨1893428, by rfl⟩ : syracuseStep 2524571 = 3786857) B3786857
theorem B6063983 : Blo 1120629 6063983 := bstep (se 1 (by rfl) ⟨4547987, by rfl⟩ : syracuseStep 6063983 = 9095975) B9095975
theorem B2525147 : Blo 1120629 2525147 := bstep (se 1 (by rfl) ⟨1893860, by rfl⟩ : syracuseStep 2525147 = 3787721) B3787721
theorem B2525255 : Blo 1120629 2525255 := bstep (se 1 (by rfl) ⟨1893941, by rfl⟩ : syracuseStep 2525255 = 3787883) B3787883
theorem B2525417 : Blo 1120629 2525417 := bstep (se 2 (by rfl) ⟨947031, by rfl⟩ : syracuseStep 2525417 = 1894063) B1894063
theorem B23333225 : Blo 1120629 23333225 := bstep (se 2 (by rfl) ⟨8749959, by rfl⟩ : syracuseStep 23333225 = 17499919) B17499919
theorem B2525921 : Blo 1120629 2525921 := bstep (se 2 (by rfl) ⟨947220, by rfl⟩ : syracuseStep 2525921 = 1894441) B1894441
theorem B5770025 : Blo 1120629 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B6392783 : Blo 1120629 6392783 := bstep (se 1 (by rfl) ⟨4794587, by rfl⟩ : syracuseStep 6392783 = 9589175) B9589175
theorem B6065209 : Blo 1120629 6065209 := bstep (se 2 (by rfl) ⟨2274453, by rfl⟩ : syracuseStep 6065209 = 4548907) B4548907
theorem B109186217 : Blo 1120629 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B2526911 : Blo 1120629 2526911 := bstep (se 1 (by rfl) ⟨1895183, by rfl⟩ : syracuseStep 2526911 = 3790367) B3790367
theorem B13635535 : Blo 1120629 13635535 := bstep (se 1 (by rfl) ⟨10226651, by rfl⟩ : syracuseStep 13635535 = 20453303) B20453303
theorem B5181725 : Blo 1120629 5181725 := bstep (se 3 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 5181725 = 1943147) B1943147
theorem B2527559 : Blo 1120629 2527559 := bstep (se 1 (by rfl) ⟨1895669, by rfl⟩ : syracuseStep 2527559 = 3791339) B3791339
theorem B7180811 : Blo 1120629 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B2397055 : Blo 1120629 2397055 := bstep (se 1 (by rfl) ⟨1797791, by rfl⟩ : syracuseStep 2397055 = 3595583) B3595583
theorem B41522291 : Blo 1120629 41522291 := bstep (se 1 (by rfl) ⟨31141718, by rfl⟩ : syracuseStep 41522291 = 62283437) B62283437
theorem B2528567 : Blo 1120629 2528567 := bstep (se 1 (by rfl) ⟨1896425, by rfl⟩ : syracuseStep 2528567 = 3792851) B3792851
theorem B2528639 : Blo 1120629 2528639 := bstep (se 1 (by rfl) ⟨1896479, by rfl⟩ : syracuseStep 2528639 = 3792959) B3792959
theorem B2528927 : Blo 1120629 2528927 := bstep (se 1 (by rfl) ⟨1896695, by rfl⟩ : syracuseStep 2528927 = 3793391) B3793391
theorem B2529503 : Blo 1120629 2529503 := bstep (se 1 (by rfl) ⟨1897127, by rfl⟩ : syracuseStep 2529503 = 3794255) B3794255
theorem B6396407 : Blo 1120629 6396407 := bstep (se 1 (by rfl) ⟨4797305, by rfl⟩ : syracuseStep 6396407 = 9594611) B9594611
theorem B1121007 : Blo 1120629 1121007 := bstep (se 1 (by rfl) ⟨840755, by rfl⟩ : syracuseStep 1121007 = 1681511) B1681511
theorem B5675831 : Blo 1120629 5675831 := bstep (se 1 (by rfl) ⟨4256873, by rfl⟩ : syracuseStep 5675831 = 8513747) B8513747
theorem B6396839 : Blo 1120629 6396839 := bstep (se 1 (by rfl) ⟨4797629, by rfl⟩ : syracuseStep 6396839 = 9595259) B9595259
theorem B5118983 : Blo 1120629 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B1121307 : Blo 1120629 1121307 := bstep (se 1 (by rfl) ⟨840980, by rfl⟩ : syracuseStep 1121307 = 1681961) B1681961
theorem B11541847 : Blo 1120629 11541847 := bstep (se 1 (by rfl) ⟨8656385, by rfl⟩ : syracuseStep 11541847 = 17312771) B17312771
theorem B109354373 : Blo 1120629 109354373 := bstep (se 4 (by rfl) ⟨10251972, by rfl⟩ : syracuseStep 109354373 = 20503945) B20503945
theorem B1121695 : Blo 1120629 1121695 := bstep (se 1 (by rfl) ⟨841271, by rfl⟩ : syracuseStep 1121695 = 1682543) B1682543
theorem B1121819 : Blo 1120629 1121819 := bstep (se 1 (by rfl) ⟨841364, by rfl⟩ : syracuseStep 1121819 = 1682729) B1682729
theorem B4267687 : Blo 1120629 4267687 := bstep (se 1 (by rfl) ⟨3200765, by rfl⟩ : syracuseStep 4267687 = 6401531) B6401531
theorem B5677289 : Blo 1120629 5677289 := bstep (se 2 (by rfl) ⟨2128983, by rfl⟩ : syracuseStep 5677289 = 4257967) B4257967
theorem B1122587 : Blo 1120629 1122587 := bstep (se 1 (by rfl) ⟨841940, by rfl⟩ : syracuseStep 1122587 = 1683881) B1683881
theorem B1122623 : Blo 1120629 1122623 := bstep (se 1 (by rfl) ⟨841967, by rfl⟩ : syracuseStep 1122623 = 1683935) B1683935
theorem B1122719 : Blo 1120629 1122719 := bstep (se 1 (by rfl) ⟨842039, by rfl⟩ : syracuseStep 1122719 = 1684079) B1684079
theorem B4268447 : Blo 1120629 4268447 := bstep (se 1 (by rfl) ⟨3201335, by rfl⟩ : syracuseStep 4268447 = 6402671) B6402671
theorem B10920365 : Blo 1120629 10920365 := bstep (se 3 (by rfl) ⟨2047568, by rfl⟩ : syracuseStep 10920365 = 4095137) B4095137
theorem B1122791 : Blo 1120629 1122791 := bstep (se 1 (by rfl) ⟨842093, by rfl⟩ : syracuseStep 1122791 = 1684187) B1684187
theorem B1122799 : Blo 1120629 1122799 := bstep (se 1 (by rfl) ⟨842099, by rfl⟩ : syracuseStep 1122799 = 1684199) B1684199
theorem B1516087 : Blo 1120629 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B8757949 : Blo 1120629 8757949 := bstep (se 3 (by rfl) ⟨1642115, by rfl⟩ : syracuseStep 8757949 = 3284231) B3284231
theorem B5677775 : Blo 1120629 5677775 := bstep (se 1 (by rfl) ⟨4258331, by rfl⟩ : syracuseStep 5677775 = 8516663) B8516663
theorem B3416827 : Blo 1120629 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B6399071 : Blo 1120629 6399071 := bstep (se 1 (by rfl) ⟨4799303, by rfl⟩ : syracuseStep 6399071 = 9598607) B9598607
theorem B1123559 : Blo 1120629 1123559 := bstep (se 1 (by rfl) ⟨842669, by rfl⟩ : syracuseStep 1123559 = 1685339) B1685339
theorem B77801057 : Blo 1120629 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B5678747 : Blo 1120629 5678747 := bstep (se 1 (by rfl) ⟨4259060, by rfl⟩ : syracuseStep 5678747 = 8518121) B8518121
theorem B1681385 : Blo 1120629 1681385 := bstep (se 2 (by rfl) ⟨630519, by rfl⟩ : syracuseStep 1681385 = 1261039) B1261039
theorem B1681403 : Blo 1120629 1681403 := bstep (se 1 (by rfl) ⟨1261052, by rfl⟩ : syracuseStep 1681403 = 2522105) B2522105
theorem B1124423 : Blo 1120629 1124423 := bstep (se 1 (by rfl) ⟨843317, by rfl⟩ : syracuseStep 1124423 = 1686635) B1686635
theorem B7186603 : Blo 1120629 7186603 := bstep (se 1 (by rfl) ⟨5389952, by rfl⟩ : syracuseStep 7186603 = 10779905) B10779905
theorem B1124583 : Blo 1120629 1124583 := bstep (se 1 (by rfl) ⟨843437, by rfl⟩ : syracuseStep 1124583 = 1686875) B1686875
theorem B1682075 : Blo 1120629 1682075 := bstep (se 1 (by rfl) ⟨1261556, by rfl⟩ : syracuseStep 1682075 = 2523113) B2523113
theorem B1682087 : Blo 1120629 1682087 := bstep (se 1 (by rfl) ⟨1261565, by rfl⟩ : syracuseStep 1682087 = 2523131) B2523131
theorem B43821739 : Blo 1120629 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B1518331 : Blo 1120629 1518331 := bstep (se 1 (by rfl) ⟨1138748, by rfl⟩ : syracuseStep 1518331 = 2277497) B2277497
theorem B8105143 : Blo 1120629 8105143 := bstep (se 1 (by rfl) ⟨6078857, by rfl⟩ : syracuseStep 8105143 = 12157715) B12157715
theorem B6401213 : Blo 1120629 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B10366397 : Blo 1120629 10366397 := bstep (se 3 (by rfl) ⟨1943699, by rfl⟩ : syracuseStep 10366397 = 3887399) B3887399
theorem B1683551 : Blo 1120629 1683551 := bstep (se 1 (by rfl) ⟨1262663, by rfl⟩ : syracuseStep 1683551 = 2525327) B2525327
theorem B1683593 : Blo 1120629 1683593 := bstep (se 2 (by rfl) ⟨631347, by rfl⟩ : syracuseStep 1683593 = 1262695) B1262695
theorem B1683623 : Blo 1120629 1683623 := bstep (se 1 (by rfl) ⟨1262717, by rfl⟩ : syracuseStep 1683623 = 2525435) B2525435
theorem B1421479 : Blo 1120629 1421479 := bstep (se 1 (by rfl) ⟨1066109, by rfl⟩ : syracuseStep 1421479 = 2132219) B2132219
theorem B8532215 : Blo 1120629 8532215 := bstep (se 1 (by rfl) ⟨6399161, by rfl⟩ : syracuseStep 8532215 = 12798323) B12798323
theorem B1683791 : Blo 1120629 1683791 := bstep (se 1 (by rfl) ⟨1262843, by rfl⟩ : syracuseStep 1683791 = 2525687) B2525687
theorem B6075071 : Blo 1120629 6075071 := bstep (se 1 (by rfl) ⟨4556303, by rfl⟩ : syracuseStep 6075071 = 9112607) B9112607
theorem B1684457 : Blo 1120629 1684457 := bstep (se 2 (by rfl) ⟨631671, by rfl⟩ : syracuseStep 1684457 = 1263343) B1263343
theorem B1684703 : Blo 1120629 1684703 := bstep (se 1 (by rfl) ⟨1263527, by rfl⟩ : syracuseStep 1684703 = 2527055) B2527055
theorem B10139053 : Blo 1120629 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B1684943 : Blo 1120629 1684943 := bstep (se 1 (by rfl) ⟨1263707, by rfl⟩ : syracuseStep 1684943 = 2527415) B2527415
theorem B1684991 : Blo 1120629 1684991 := bstep (se 1 (by rfl) ⟨1263743, by rfl⟩ : syracuseStep 1684991 = 2527487) B2527487
theorem B1685183 : Blo 1120629 1685183 := bstep (se 1 (by rfl) ⟨1263887, by rfl⟩ : syracuseStep 1685183 = 2527775) B2527775
theorem B1423327 : Blo 1120629 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B249083909 : Blo 1120629 249083909 := bstep (se 4 (by rfl) ⟨23351616, by rfl⟩ : syracuseStep 249083909 = 46703233) B46703233
theorem B4864063 : Blo 1120629 4864063 := bstep (se 1 (by rfl) ⟨3648047, by rfl⟩ : syracuseStep 4864063 = 7296095) B7296095
theorem B1685723 : Blo 1120629 1685723 := bstep (se 1 (by rfl) ⟨1264292, by rfl⟩ : syracuseStep 1685723 = 2528585) B2528585
theorem B5683931 : Blo 1120629 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B36420317 : Blo 1120629 36420317 := bstep (se 3 (by rfl) ⟨6828809, by rfl⟩ : syracuseStep 36420317 = 13657619) B13657619
theorem B1686683 : Blo 1120629 1686683 := bstep (se 1 (by rfl) ⟨1265012, by rfl⟩ : syracuseStep 1686683 = 2530025) B2530025
theorem B1686695 : Blo 1120629 1686695 := bstep (se 1 (by rfl) ⟨1265021, by rfl⟩ : syracuseStep 1686695 = 2530043) B2530043
theorem B1261615 : Blo 1120629 1261615 := bstep (se 1 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 1261615 = 1892423) B1892423
theorem B1196699 : Blo 1120629 1196699 := bstep (se 1 (by rfl) ⟨897524, by rfl⟩ : syracuseStep 1196699 = 1795049) B1795049
theorem B1262335 : Blo 1120629 1262335 := bstep (se 1 (by rfl) ⟨946751, by rfl⟩ : syracuseStep 1262335 = 1893503) B1893503
theorem B5391451 : Blo 1120629 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B97076555 : Blo 1120629 97076555 := bstep (se 1 (by rfl) ⟨72807416, by rfl⟩ : syracuseStep 97076555 = 145614833) B145614833
theorem B4671215 : Blo 1120629 4671215 := bstep (se 1 (by rfl) ⟨3503411, by rfl⟩ : syracuseStep 4671215 = 7006823) B7006823
theorem B3786749 : Blo 1120629 3786749 := bstep (se 3 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 3786749 = 1420031) B1420031
theorem B3787127 : Blo 1120629 3787127 := bstep (se 1 (by rfl) ⟨2840345, by rfl⟩ : syracuseStep 3787127 = 5680691) B5680691
theorem B1264027 : Blo 1120629 1264027 := bstep (se 1 (by rfl) ⟨948020, by rfl⟩ : syracuseStep 1264027 = 1896041) B1896041
theorem B3198113 : Blo 1120629 3198113 := bstep (se 2 (by rfl) ⟨1199292, by rfl⟩ : syracuseStep 3198113 = 2398585) B2398585
theorem B1264891 : Blo 1120629 1264891 := bstep (se 1 (by rfl) ⟨948668, by rfl⟩ : syracuseStep 1264891 = 1897337) B1897337
theorem B4444321 : Blo 1120629 4444321 := bstep (se 2 (by rfl) ⟨1666620, by rfl⟩ : syracuseStep 4444321 = 3333241) B3333241
theorem B9588901 : Blo 1120629 9588901 := bstep (se 4 (by rfl) ⟨898959, by rfl⟩ : syracuseStep 9588901 = 1797919) B1797919
theorem B5755159 : Blo 1120629 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B3592957 : Blo 1120629 3592957 := bstep (se 3 (by rfl) ⟨673679, by rfl⟩ : syracuseStep 3592957 = 1347359) B1347359
theorem B3789935 : Blo 1120629 3789935 := bstep (se 1 (by rfl) ⟨2842451, by rfl⟩ : syracuseStep 3789935 = 5684903) B5684903
theorem B2840417 : Blo 1120629 2840417 := bstep (se 2 (by rfl) ⟨1065156, by rfl⟩ : syracuseStep 2840417 = 2130313) B2130313
theorem B2840447 : Blo 1120629 2840447 := bstep (se 1 (by rfl) ⟨2130335, by rfl⟩ : syracuseStep 2840447 = 4260671) B4260671
theorem B5691545 : Blo 1120629 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B10541431 : Blo 1120629 10541431 := bstep (se 1 (by rfl) ⟨7906073, by rfl⟩ : syracuseStep 10541431 = 15812147) B15812147
theorem B3899387 : Blo 1120629 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B2841875 : Blo 1120629 2841875 := bstep (se 1 (by rfl) ⟨2131406, by rfl⟩ : syracuseStep 2841875 = 4262813) B4262813
theorem B8510831 : Blo 1120629 8510831 := bstep (se 1 (by rfl) ⟨6383123, by rfl⟩ : syracuseStep 8510831 = 12766247) B12766247
theorem B3792311 : Blo 1120629 3792311 := bstep (se 1 (by rfl) ⟨2844233, by rfl⟩ : syracuseStep 3792311 = 5688467) B5688467
theorem B2842249 : Blo 1120629 2842249 := bstep (se 2 (by rfl) ⟨1065843, by rfl⟩ : syracuseStep 2842249 = 2131687) B2131687
theorem B36462757 : Blo 1120629 36462757 := bstep (se 4 (by rfl) ⟨3418383, by rfl⟩ : syracuseStep 36462757 = 6836767) B6836767
theorem B3793769 : Blo 1120629 3793769 := bstep (se 2 (by rfl) ⟨1422663, by rfl⟩ : syracuseStep 3793769 = 2845327) B2845327
theorem B3793823 : Blo 1120629 3793823 := bstep (se 1 (by rfl) ⟨2845367, by rfl⟩ : syracuseStep 3793823 = 5690735) B5690735
theorem B2844335 : Blo 1120629 2844335 := bstep (se 1 (by rfl) ⟨2133251, by rfl⟩ : syracuseStep 2844335 = 4266503) B4266503
theorem B24242075 : Blo 1120629 24242075 := bstep (se 1 (by rfl) ⟨18181556, by rfl⟩ : syracuseStep 24242075 = 36363113) B36363113
theorem B2845115 : Blo 1120629 2845115 := bstep (se 1 (by rfl) ⟨2133836, by rfl⟩ : syracuseStep 2845115 = 4267673) B4267673
theorem B8416007 : Blo 1120629 8416007 := bstep (se 1 (by rfl) ⟨6312005, by rfl⟩ : syracuseStep 8416007 = 12624011) B12624011
theorem B12807071 : Blo 1120629 12807071 := bstep (se 1 (by rfl) ⟨9605303, by rfl⟩ : syracuseStep 12807071 = 19210607) B19210607
theorem B2846441 : Blo 1120629 2846441 := bstep (se 2 (by rfl) ⟨1067415, by rfl⟩ : syracuseStep 2846441 = 2134831) B2134831
theorem B8515691 : Blo 1120629 8515691 := bstep (se 1 (by rfl) ⟨6386768, by rfl⟩ : syracuseStep 8515691 = 12773537) B12773537
theorem B10940699 : Blo 1120629 10940699 := bstep (se 1 (by rfl) ⟨8205524, by rfl⟩ : syracuseStep 10940699 = 16411049) B16411049
theorem B59144363 : Blo 1120629 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B2882291 : Blo 1120629 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B2521979 : Blo 1120629 2521979 := bstep (se 1 (by rfl) ⟨1891484, by rfl⟩ : syracuseStep 2521979 = 3782969) B3782969
theorem B2522195 : Blo 1120629 2522195 := bstep (se 1 (by rfl) ⟨1891646, by rfl⟩ : syracuseStep 2522195 = 3783293) B3783293
theorem B2522807 : Blo 1120629 2522807 := bstep (se 1 (by rfl) ⟨1892105, by rfl⟩ : syracuseStep 2522807 = 3784211) B3784211
theorem B2522843 : Blo 1120629 2522843 := bstep (se 1 (by rfl) ⟨1892132, by rfl⟩ : syracuseStep 2522843 = 3784265) B3784265
theorem B64717703 : Blo 1120629 64717703 := bstep (se 1 (by rfl) ⟨48538277, by rfl⟩ : syracuseStep 64717703 = 97076555) B97076555
theorem B4555769 : Blo 1120629 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B3114143 : Blo 1120629 3114143 := bstep (se 1 (by rfl) ⟨2335607, by rfl⟩ : syracuseStep 3114143 = 4671215) B4671215
theorem B2524499 : Blo 1120629 2524499 := bstep (se 1 (by rfl) ⟨1893374, by rfl⟩ : syracuseStep 2524499 = 3786749) B3786749
theorem B2524751 : Blo 1120629 2524751 := bstep (se 1 (by rfl) ⟨1893563, by rfl⟩ : syracuseStep 2524751 = 3787127) B3787127
theorem B2885257 : Blo 1120629 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B4261855 : Blo 1120629 4261855 := bstep (se 1 (by rfl) ⟨3196391, by rfl⟩ : syracuseStep 4261855 = 6392783) B6392783
theorem B2132075 : Blo 1120629 2132075 := bstep (se 1 (by rfl) ⟨1599056, by rfl⟩ : syracuseStep 2132075 = 3198113) B3198113
theorem B4787207 : Blo 1120629 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B2526623 : Blo 1120629 2526623 := bstep (se 1 (by rfl) ⟨1894967, by rfl⟩ : syracuseStep 2526623 = 3789935) B3789935
theorem B58428985 : Blo 1120629 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B4264271 : Blo 1120629 4264271 := bstep (se 1 (by rfl) ⟨3198203, by rfl⟩ : syracuseStep 4264271 = 6396407) B6396407
theorem B4264559 : Blo 1120629 4264559 := bstep (se 1 (by rfl) ⟨3198419, by rfl⟩ : syracuseStep 4264559 = 6396839) B6396839
theorem B3412655 : Blo 1120629 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B5673887 : Blo 1120629 5673887 := bstep (se 1 (by rfl) ⟨4255415, by rfl⟩ : syracuseStep 5673887 = 8510831) B8510831
theorem B2528207 : Blo 1120629 2528207 := bstep (se 1 (by rfl) ⟨1896155, by rfl⟩ : syracuseStep 2528207 = 3792311) B3792311
theorem B12785201 : Blo 1120629 12785201 := bstep (se 2 (by rfl) ⟨4794450, by rfl⟩ : syracuseStep 12785201 = 9588901) B9588901
theorem B7280243 : Blo 1120629 7280243 := bstep (se 1 (by rfl) ⟨5460182, by rfl⟩ : syracuseStep 7280243 = 10920365) B10920365
theorem B32347781 : Blo 1120629 32347781 := bstep (se 4 (by rfl) ⟨3032604, by rfl⟩ : syracuseStep 32347781 = 6065209) B6065209
theorem B7673545 : Blo 1120629 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B2529179 : Blo 1120629 2529179 := bstep (se 1 (by rfl) ⟨1896884, by rfl⟩ : syracuseStep 2529179 = 3793769) B3793769
theorem B2529215 : Blo 1120629 2529215 := bstep (se 1 (by rfl) ⟨1896911, by rfl⟩ : syracuseStep 2529215 = 3793823) B3793823
theorem B4266047 : Blo 1120629 4266047 := bstep (se 1 (by rfl) ⟨3199535, by rfl⟩ : syracuseStep 4266047 = 6399071) B6399071
theorem B4790609 : Blo 1120629 4790609 := bstep (se 2 (by rfl) ⟨1796478, by rfl⟩ : syracuseStep 4790609 = 3592957) B3592957
theorem B16161383 : Blo 1120629 16161383 := bstep (se 1 (by rfl) ⟨12121037, by rfl⟩ : syracuseStep 16161383 = 24242075) B24242075
theorem B1120923 : Blo 1120629 1120923 := bstep (se 1 (by rfl) ⟨840692, by rfl⟩ : syracuseStep 1120923 = 1681385) B1681385
theorem B1120935 : Blo 1120629 1120935 := bstep (se 1 (by rfl) ⟨840701, by rfl⟩ : syracuseStep 1120935 = 1681403) B1681403
theorem B1121383 : Blo 1120629 1121383 := bstep (se 1 (by rfl) ⟨841037, by rfl⟩ : syracuseStep 1121383 = 1682075) B1682075
theorem B1121391 : Blo 1120629 1121391 := bstep (se 1 (by rfl) ⟨841043, by rfl⟩ : syracuseStep 1121391 = 1682087) B1682087
theorem B5610671 : Blo 1120629 5610671 := bstep (se 1 (by rfl) ⟨4208003, by rfl⟩ : syracuseStep 5610671 = 8416007) B8416007
theorem B4267475 : Blo 1120629 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B1122367 : Blo 1120629 1122367 := bstep (se 1 (by rfl) ⟨841775, by rfl⟩ : syracuseStep 1122367 = 1683551) B1683551
theorem B5677127 : Blo 1120629 5677127 := bstep (se 1 (by rfl) ⟨4257845, by rfl⟩ : syracuseStep 5677127 = 8515691) B8515691
theorem B1122395 : Blo 1120629 1122395 := bstep (se 1 (by rfl) ⟨841796, by rfl⟩ : syracuseStep 1122395 = 1683593) B1683593
theorem B1122415 : Blo 1120629 1122415 := bstep (se 1 (by rfl) ⟨841811, by rfl⟩ : syracuseStep 1122415 = 1683623) B1683623
theorem B1122527 : Blo 1120629 1122527 := bstep (se 1 (by rfl) ⟨841895, by rfl⟩ : syracuseStep 1122527 = 1683791) B1683791
theorem B1122971 : Blo 1120629 1122971 := bstep (se 1 (by rfl) ⟨842228, by rfl⟩ : syracuseStep 1122971 = 1684457) B1684457
theorem B1123135 : Blo 1120629 1123135 := bstep (se 1 (by rfl) ⟨842351, by rfl⟩ : syracuseStep 1123135 = 1684703) B1684703
theorem B1123295 : Blo 1120629 1123295 := bstep (se 1 (by rfl) ⟨842471, by rfl⟩ : syracuseStep 1123295 = 1684943) B1684943
theorem B1123327 : Blo 1120629 1123327 := bstep (se 1 (by rfl) ⟨842495, by rfl⟩ : syracuseStep 1123327 = 1684991) B1684991
theorem B1123455 : Blo 1120629 1123455 := bstep (se 1 (by rfl) ⟨842591, by rfl⟩ : syracuseStep 1123455 = 1685183) B1685183
theorem B39429575 : Blo 1120629 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B1123815 : Blo 1120629 1123815 := bstep (se 1 (by rfl) ⟨842861, by rfl⟩ : syracuseStep 1123815 = 1685723) B1685723
theorem B1681319 : Blo 1120629 1681319 := bstep (se 1 (by rfl) ⟨1260989, by rfl⟩ : syracuseStep 1681319 = 2521979) B2521979
theorem B1681463 : Blo 1120629 1681463 := bstep (se 1 (by rfl) ⟨1261097, by rfl⟩ : syracuseStep 1681463 = 2522195) B2522195
theorem B1124455 : Blo 1120629 1124455 := bstep (se 1 (by rfl) ⟨843341, by rfl⟩ : syracuseStep 1124455 = 1686683) B1686683
theorem B1124463 : Blo 1120629 1124463 := bstep (se 1 (by rfl) ⟨843347, by rfl⟩ : syracuseStep 1124463 = 1686695) B1686695
theorem B1681871 : Blo 1120629 1681871 := bstep (se 1 (by rfl) ⟨1261403, by rfl⟩ : syracuseStep 1681871 = 2522807) B2522807
theorem B1681895 : Blo 1120629 1681895 := bstep (se 1 (by rfl) ⟨1261421, by rfl⟩ : syracuseStep 1681895 = 2522843) B2522843
theorem B10398365 : Blo 1120629 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B1682153 : Blo 1120629 1682153 := bstep (se 2 (by rfl) ⟨630807, by rfl⟩ : syracuseStep 1682153 = 1261615) B1261615
theorem B1682207 : Blo 1120629 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B8432585 : Blo 1120629 8432585 := bstep (se 2 (by rfl) ⟨3162219, by rfl⟩ : syracuseStep 8432585 = 6324439) B6324439
theorem B1682663 : Blo 1120629 1682663 := bstep (se 1 (by rfl) ⟨1261997, by rfl⟩ : syracuseStep 1682663 = 2523995) B2523995
theorem B1682687 : Blo 1120629 1682687 := bstep (se 1 (by rfl) ⟨1262015, by rfl⟩ : syracuseStep 1682687 = 2524031) B2524031
theorem B1682759 : Blo 1120629 1682759 := bstep (se 1 (by rfl) ⟨1262069, by rfl⟩ : syracuseStep 1682759 = 2524139) B2524139
theorem B11677265 : Blo 1120629 11677265 := bstep (se 2 (by rfl) ⟨4378974, by rfl⟩ : syracuseStep 11677265 = 8757949) B8757949
theorem B1683047 : Blo 1120629 1683047 := bstep (se 1 (by rfl) ⟨1262285, by rfl⟩ : syracuseStep 1683047 = 2524571) B2524571
theorem B1683113 : Blo 1120629 1683113 := bstep (se 2 (by rfl) ⟨631167, by rfl⟩ : syracuseStep 1683113 = 1262335) B1262335
theorem B4042655 : Blo 1120629 4042655 := bstep (se 1 (by rfl) ⟨3031991, by rfl⟩ : syracuseStep 4042655 = 6063983) B6063983
theorem B1683431 : Blo 1120629 1683431 := bstep (se 1 (by rfl) ⟨1262573, by rfl⟩ : syracuseStep 1683431 = 2525147) B2525147
theorem B1683503 : Blo 1120629 1683503 := bstep (se 1 (by rfl) ⟨1262627, by rfl⟩ : syracuseStep 1683503 = 2525255) B2525255
theorem B7188601 : Blo 1120629 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B1683611 : Blo 1120629 1683611 := bstep (se 1 (by rfl) ⟨1262708, by rfl⟩ : syracuseStep 1683611 = 2525417) B2525417
theorem B1683947 : Blo 1120629 1683947 := bstep (se 1 (by rfl) ⟨1262960, by rfl⟩ : syracuseStep 1683947 = 2525921) B2525921
theorem B3846683 : Blo 1120629 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B72790811 : Blo 1120629 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B1684607 : Blo 1120629 1684607 := bstep (se 1 (by rfl) ⟨1263455, by rfl⟩ : syracuseStep 1684607 = 2526911) B2526911
theorem B3454483 : Blo 1120629 3454483 := bstep (se 1 (by rfl) ⟨2590862, by rfl⟩ : syracuseStep 3454483 = 5181725) B5181725
theorem B1685039 : Blo 1120629 1685039 := bstep (se 1 (by rfl) ⟨1263779, by rfl⟩ : syracuseStep 1685039 = 2527559) B2527559
theorem B9582137 : Blo 1120629 9582137 := bstep (se 2 (by rfl) ⟨3593301, by rfl⟩ : syracuseStep 9582137 = 7186603) B7186603
theorem B1685369 : Blo 1120629 1685369 := bstep (se 2 (by rfl) ⟨632013, by rfl⟩ : syracuseStep 1685369 = 1264027) B1264027
theorem B1685711 : Blo 1120629 1685711 := bstep (se 1 (by rfl) ⟨1264283, by rfl⟩ : syracuseStep 1685711 = 2528567) B2528567
theorem B1685759 : Blo 1120629 1685759 := bstep (se 1 (by rfl) ⟨1264319, by rfl⟩ : syracuseStep 1685759 = 2528639) B2528639
theorem B1685951 : Blo 1120629 1685951 := bstep (se 1 (by rfl) ⟨1264463, by rfl⟩ : syracuseStep 1685951 = 2528927) B2528927
theorem B1686335 : Blo 1120629 1686335 := bstep (se 1 (by rfl) ⟨1264751, by rfl⟩ : syracuseStep 1686335 = 2529503) B2529503
theorem B1686521 : Blo 1120629 1686521 := bstep (se 2 (by rfl) ⟨632445, by rfl⟩ : syracuseStep 1686521 = 1264891) B1264891
theorem B3783887 : Blo 1120629 3783887 := bstep (se 1 (by rfl) ⟨2837915, by rfl⟩ : syracuseStep 3783887 = 5675831) B5675831
theorem B3784859 : Blo 1120629 3784859 := bstep (se 1 (by rfl) ⟨2838644, by rfl⟩ : syracuseStep 3784859 = 5677289) B5677289
theorem B3785183 : Blo 1120629 3785183 := bstep (se 1 (by rfl) ⟨2838887, by rfl⟩ : syracuseStep 3785183 = 5677775) B5677775
theorem B3785831 : Blo 1120629 3785831 := bstep (se 1 (by rfl) ⟨2839373, by rfl⟩ : syracuseStep 3785831 = 5678747) B5678747
theorem B3196073 : Blo 1120629 3196073 := bstep (se 2 (by rfl) ⟨1198527, by rfl⟩ : syracuseStep 3196073 = 2397055) B2397055
theorem B12764789 : Blo 1120629 12764789 := bstep (se 5 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 12764789 = 1196699) B1196699
theorem B13518737 : Blo 1120629 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B8538047 : Blo 1120629 8538047 := bstep (se 1 (by rfl) ⟨6403535, by rfl⟩ : syracuseStep 8538047 = 12807071) B12807071
theorem B7686109 : Blo 1120629 7686109 := bstep (se 3 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 7686109 = 2882291) B2882291
theorem B5688143 : Blo 1120629 5688143 := bstep (se 1 (by rfl) ⟨4266107, by rfl⟩ : syracuseStep 5688143 = 8532215) B8532215
theorem B7293799 : Blo 1120629 7293799 := bstep (se 1 (by rfl) ⟨5470349, by rfl⟩ : syracuseStep 7293799 = 10940699) B10940699
theorem B4050047 : Blo 1120629 4050047 := bstep (se 1 (by rfl) ⟨3037535, by rfl⟩ : syracuseStep 4050047 = 6075071) B6075071
theorem B166055939 : Blo 1120629 166055939 := bstep (se 1 (by rfl) ⟨124541954, by rfl⟩ : syracuseStep 166055939 = 249083909) B249083909
theorem B15389129 : Blo 1120629 15389129 := bstep (se 2 (by rfl) ⟨5770923, by rfl⟩ : syracuseStep 15389129 = 11541847) B11541847
theorem B3789287 : Blo 1120629 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B3789665 : Blo 1120629 3789665 := bstep (se 2 (by rfl) ⟨1421124, by rfl⟩ : syracuseStep 3789665 = 2842249) B2842249
theorem B5690249 : Blo 1120629 5690249 := bstep (se 2 (by rfl) ⟨2133843, by rfl⟩ : syracuseStep 5690249 = 4267687) B4267687
theorem B48617009 : Blo 1120629 48617009 := bstep (se 2 (by rfl) ⟨18231378, by rfl⟩ : syracuseStep 48617009 = 36462757) B36462757
theorem B2021449 : Blo 1120629 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B27681527 : Blo 1120629 27681527 := bstep (se 1 (by rfl) ⟨20761145, by rfl⟩ : syracuseStep 27681527 = 41522291) B41522291
theorem B2024441 : Blo 1120629 2024441 := bstep (se 2 (by rfl) ⟨759165, by rfl⟩ : syracuseStep 2024441 = 1518331) B1518331
theorem B1893611 : Blo 1120629 1893611 := bstep (se 1 (by rfl) ⟨1420208, by rfl⟩ : syracuseStep 1893611 = 2840417) B2840417
theorem B1893631 : Blo 1120629 1893631 := bstep (se 1 (by rfl) ⟨1420223, by rfl⟩ : syracuseStep 1893631 = 2840447) B2840447
theorem B3794363 : Blo 1120629 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B10806857 : Blo 1120629 10806857 := bstep (se 2 (by rfl) ⟨4052571, by rfl⟩ : syracuseStep 10806857 = 8105143) B8105143
theorem B1894583 : Blo 1120629 1894583 := bstep (se 1 (by rfl) ⟨1420937, by rfl⟩ : syracuseStep 1894583 = 2841875) B2841875
theorem B72902915 : Blo 1120629 72902915 := bstep (se 1 (by rfl) ⟨54677186, by rfl⟩ : syracuseStep 72902915 = 109354373) B109354373
theorem B18180713 : Blo 1120629 18180713 := bstep (se 2 (by rfl) ⟨6817767, by rfl⟩ : syracuseStep 18180713 = 13635535) B13635535
theorem B5925761 : Blo 1120629 5925761 := bstep (se 2 (by rfl) ⟨2222160, by rfl⟩ : syracuseStep 5925761 = 4444321) B4444321
theorem B1895305 : Blo 1120629 1895305 := bstep (se 2 (by rfl) ⟨710739, by rfl⟩ : syracuseStep 1895305 = 1421479) B1421479
theorem B2845631 : Blo 1120629 2845631 := bstep (se 1 (by rfl) ⟨2134223, by rfl⟩ : syracuseStep 2845631 = 4268447) B4268447
theorem B62221933 : Blo 1120629 62221933 := bstep (se 3 (by rfl) ⟨11666612, by rfl⟩ : syracuseStep 62221933 = 23333225) B23333225
theorem B51867371 : Blo 1120629 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B1896223 : Blo 1120629 1896223 := bstep (se 1 (by rfl) ⟨1422167, by rfl⟩ : syracuseStep 1896223 = 2844335) B2844335
theorem B1896743 : Blo 1120629 1896743 := bstep (se 1 (by rfl) ⟨1422557, by rfl⟩ : syracuseStep 1896743 = 2845115) B2845115
theorem B6910931 : Blo 1120629 6910931 := bstep (se 1 (by rfl) ⟨5183198, by rfl⟩ : syracuseStep 6910931 = 10366397) B10366397
theorem B1897627 : Blo 1120629 1897627 := bstep (se 1 (by rfl) ⟨1423220, by rfl⟩ : syracuseStep 1897627 = 2846441) B2846441
theorem B1897769 : Blo 1120629 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B6485417 : Blo 1120629 6485417 := bstep (se 2 (by rfl) ⟨2432031, by rfl⟩ : syracuseStep 6485417 = 4864063) B4864063
theorem B14055241 : Blo 1120629 14055241 := bstep (se 2 (by rfl) ⟨5270715, by rfl⟩ : syracuseStep 14055241 = 10541431) B10541431
theorem B24280211 : Blo 1120629 24280211 := bstep (se 1 (by rfl) ⟨18210158, by rfl⟩ : syracuseStep 24280211 = 36420317) B36420317
theorem B2523239 : Blo 1120629 2523239 := bstep (se 1 (by rfl) ⟨1892429, by rfl⟩ : syracuseStep 2523239 = 3784859) B3784859
theorem B2523455 : Blo 1120629 2523455 := bstep (se 1 (by rfl) ⟨1892591, by rfl⟩ : syracuseStep 2523455 = 3785183) B3785183
theorem B2523887 : Blo 1120629 2523887 := bstep (se 1 (by rfl) ⟨1892915, by rfl⟩ : syracuseStep 2523887 = 3785831) B3785831
theorem B2130715 : Blo 1120629 2130715 := bstep (se 1 (by rfl) ⟨1598036, by rfl⟩ : syracuseStep 2130715 = 3196073) B3196073
theorem B9012491 : Blo 1120629 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B2524841 : Blo 1120629 2524841 := bstep (se 2 (by rfl) ⟨946815, by rfl⟩ : syracuseStep 2524841 = 1893631) B1893631
theorem B10259419 : Blo 1120629 10259419 := bstep (se 1 (by rfl) ⟨7694564, by rfl⟩ : syracuseStep 10259419 = 15389129) B15389129
theorem B2526191 : Blo 1120629 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B2526443 : Blo 1120629 2526443 := bstep (se 1 (by rfl) ⟨1894832, by rfl⟩ : syracuseStep 2526443 = 3789665) B3789665
theorem B8523467 : Blo 1120629 8523467 := bstep (se 1 (by rfl) ⟨6392600, by rfl⟩ : syracuseStep 8523467 = 12785201) B12785201
theorem B32411339 : Blo 1120629 32411339 := bstep (se 1 (by rfl) ⟨24308504, by rfl⟩ : syracuseStep 32411339 = 48617009) B48617009
theorem B4853495 : Blo 1120629 4853495 := bstep (se 1 (by rfl) ⟨3640121, by rfl⟩ : syracuseStep 4853495 = 7280243) B7280243
theorem B21565187 : Blo 1120629 21565187 := bstep (se 1 (by rfl) ⟨16173890, by rfl⟩ : syracuseStep 21565187 = 32347781) B32347781
theorem B2527073 : Blo 1120629 2527073 := bstep (se 2 (by rfl) ⟨947652, by rfl⟩ : syracuseStep 2527073 = 1895305) B1895305
theorem B3740447 : Blo 1120629 3740447 := bstep (se 1 (by rfl) ⟨2805335, by rfl⟩ : syracuseStep 3740447 = 5610671) B5610671
theorem B2528297 : Blo 1120629 2528297 := bstep (se 2 (by rfl) ⟨948111, by rfl⟩ : syracuseStep 2528297 = 1896223) B1896223
theorem B18454351 : Blo 1120629 18454351 := bstep (se 1 (by rfl) ⟨13840763, by rfl⟩ : syracuseStep 18454351 = 27681527) B27681527
theorem B1349627 : Blo 1120629 1349627 := bstep (se 1 (by rfl) ⟨1012220, by rfl⟩ : syracuseStep 1349627 = 2024441) B2024441
theorem B2529575 : Blo 1120629 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B26286383 : Blo 1120629 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B1120879 : Blo 1120629 1120879 := bstep (se 1 (by rfl) ⟨840659, by rfl⟩ : syracuseStep 1120879 = 1681319) B1681319
theorem B1120975 : Blo 1120629 1120975 := bstep (se 1 (by rfl) ⟨840731, by rfl⟩ : syracuseStep 1120975 = 1681463) B1681463
theorem B48601943 : Blo 1120629 48601943 := bstep (se 1 (by rfl) ⟨36451457, by rfl⟩ : syracuseStep 48601943 = 72902915) B72902915
theorem B2530169 : Blo 1120629 2530169 := bstep (se 2 (by rfl) ⟨948813, by rfl⟩ : syracuseStep 2530169 = 1897627) B1897627
theorem B1121247 : Blo 1120629 1121247 := bstep (se 1 (by rfl) ⟨840935, by rfl⟩ : syracuseStep 1121247 = 1681871) B1681871
theorem B1121263 : Blo 1120629 1121263 := bstep (se 1 (by rfl) ⟨840947, by rfl⟩ : syracuseStep 1121263 = 1681895) B1681895
theorem B1121435 : Blo 1120629 1121435 := bstep (se 1 (by rfl) ⟨841076, by rfl⟩ : syracuseStep 1121435 = 1682153) B1682153
theorem B1121471 : Blo 1120629 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B1121775 : Blo 1120629 1121775 := bstep (se 1 (by rfl) ⟨841331, by rfl⟩ : syracuseStep 1121775 = 1682663) B1682663
theorem B1121791 : Blo 1120629 1121791 := bstep (se 1 (by rfl) ⟨841343, by rfl⟩ : syracuseStep 1121791 = 1682687) B1682687
theorem B1121839 : Blo 1120629 1121839 := bstep (se 1 (by rfl) ⟨841379, by rfl⟩ : syracuseStep 1121839 = 1682759) B1682759
theorem B1122031 : Blo 1120629 1122031 := bstep (se 1 (by rfl) ⟨841523, by rfl⟩ : syracuseStep 1122031 = 1683047) B1683047
theorem B1122075 : Blo 1120629 1122075 := bstep (se 1 (by rfl) ⟨841556, by rfl⟩ : syracuseStep 1122075 = 1683113) B1683113
theorem B34578247 : Blo 1120629 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B2695103 : Blo 1120629 2695103 := bstep (se 1 (by rfl) ⟨2021327, by rfl⟩ : syracuseStep 2695103 = 4042655) B4042655
theorem B1122287 : Blo 1120629 1122287 := bstep (se 1 (by rfl) ⟨841715, by rfl⟩ : syracuseStep 1122287 = 1683431) B1683431
theorem B1122335 : Blo 1120629 1122335 := bstep (se 1 (by rfl) ⟨841751, by rfl⟩ : syracuseStep 1122335 = 1683503) B1683503
theorem B2695265 : Blo 1120629 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B1122407 : Blo 1120629 1122407 := bstep (se 1 (by rfl) ⟨841805, by rfl⟩ : syracuseStep 1122407 = 1683611) B1683611
theorem B1122631 : Blo 1120629 1122631 := bstep (se 1 (by rfl) ⟨841973, by rfl⟩ : syracuseStep 1122631 = 1683947) B1683947
theorem B2564455 : Blo 1120629 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B1123071 : Blo 1120629 1123071 := bstep (se 1 (by rfl) ⟨842303, by rfl⟩ : syracuseStep 1123071 = 1684607) B1684607
theorem B1123359 : Blo 1120629 1123359 := bstep (se 1 (by rfl) ⟨842519, by rfl⟩ : syracuseStep 1123359 = 1685039) B1685039
theorem B1123579 : Blo 1120629 1123579 := bstep (se 1 (by rfl) ⟨842684, by rfl⟩ : syracuseStep 1123579 = 1685369) B1685369
theorem B1123807 : Blo 1120629 1123807 := bstep (se 1 (by rfl) ⟨842855, by rfl⟩ : syracuseStep 1123807 = 1685711) B1685711
theorem B1123839 : Blo 1120629 1123839 := bstep (se 1 (by rfl) ⟨842879, by rfl⟩ : syracuseStep 1123839 = 1685759) B1685759
theorem B1123967 : Blo 1120629 1123967 := bstep (se 1 (by rfl) ⟨842975, by rfl⟩ : syracuseStep 1123967 = 1685951) B1685951
theorem B1124223 : Blo 1120629 1124223 := bstep (se 1 (by rfl) ⟨843167, by rfl⟩ : syracuseStep 1124223 = 1686335) B1686335
theorem B1124347 : Blo 1120629 1124347 := bstep (se 1 (by rfl) ⟨843260, by rfl⟩ : syracuseStep 1124347 = 1686521) B1686521
theorem B2076095 : Blo 1120629 2076095 := bstep (se 1 (by rfl) ⟨1557071, by rfl⟩ : syracuseStep 2076095 = 3114143) B3114143
theorem B1682999 : Blo 1120629 1682999 := bstep (se 1 (by rfl) ⟨1262249, by rfl⟩ : syracuseStep 1682999 = 2524499) B2524499
theorem B1683167 : Blo 1120629 1683167 := bstep (se 1 (by rfl) ⟨1262375, by rfl⟩ : syracuseStep 1683167 = 2524751) B2524751
theorem B1421383 : Blo 1120629 1421383 := bstep (se 1 (by rfl) ⟨1066037, by rfl⟩ : syracuseStep 1421383 = 2132075) B2132075
theorem B3191471 : Blo 1120629 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B3847009 : Blo 1120629 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B1684415 : Blo 1120629 1684415 := bstep (se 1 (by rfl) ⟨1263311, by rfl⟩ : syracuseStep 1684415 = 2526623) B2526623
theorem B18429149 : Blo 1120629 18429149 := bstep (se 3 (by rfl) ⟨3455465, by rfl⟩ : syracuseStep 18429149 = 6910931) B6910931
theorem B5682473 : Blo 1120629 5682473 := bstep (se 2 (by rfl) ⟨2130927, by rfl⟩ : syracuseStep 5682473 = 4261855) B4261855
theorem B110703959 : Blo 1120629 110703959 := bstep (se 1 (by rfl) ⟨83027969, by rfl⟩ : syracuseStep 110703959 = 166055939) B166055939
theorem B2275103 : Blo 1120629 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B3782591 : Blo 1120629 3782591 := bstep (se 1 (by rfl) ⟨2836943, by rfl⟩ : syracuseStep 3782591 = 5673887) B5673887
theorem B1685471 : Blo 1120629 1685471 := bstep (se 1 (by rfl) ⟨1264103, by rfl⟩ : syracuseStep 1685471 = 2528207) B2528207
theorem B1686119 : Blo 1120629 1686119 := bstep (se 1 (by rfl) ⟨1264589, by rfl⟩ : syracuseStep 1686119 = 2529179) B2529179
theorem B1686143 : Blo 1120629 1686143 := bstep (se 1 (by rfl) ⟨1264607, by rfl⟩ : syracuseStep 1686143 = 2529215) B2529215
theorem B3193739 : Blo 1120629 3193739 := bstep (se 1 (by rfl) ⟨2395304, by rfl⟩ : syracuseStep 3193739 = 4790609) B4790609
theorem B77905313 : Blo 1120629 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B3784751 : Blo 1120629 3784751 := bstep (se 1 (by rfl) ⟨2838563, by rfl⟩ : syracuseStep 3784751 = 5677127) B5677127
theorem B9584801 : Blo 1120629 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B1262407 : Blo 1120629 1262407 := bstep (se 1 (by rfl) ⟨946805, by rfl⟩ : syracuseStep 1262407 = 1893611) B1893611
theorem B1263055 : Blo 1120629 1263055 := bstep (se 1 (by rfl) ⟨947291, by rfl⟩ : syracuseStep 1263055 = 1894583) B1894583
theorem B6932243 : Blo 1120629 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B3950507 : Blo 1120629 3950507 := bstep (se 1 (by rfl) ⟨2962880, by rfl⟩ : syracuseStep 3950507 = 5925761) B5925761
theorem B5621723 : Blo 1120629 5621723 := bstep (se 1 (by rfl) ⟨4216292, by rfl⟩ : syracuseStep 5621723 = 8432585) B8432585
theorem B4605977 : Blo 1120629 4605977 := bstep (se 2 (by rfl) ⟨1727241, by rfl⟩ : syracuseStep 4605977 = 3454483) B3454483
theorem B7784843 : Blo 1120629 7784843 := bstep (se 1 (by rfl) ⟨5838632, by rfl⟩ : syracuseStep 7784843 = 11677265) B11677265
theorem B1264495 : Blo 1120629 1264495 := bstep (se 1 (by rfl) ⟨948371, by rfl⟩ : syracuseStep 1264495 = 1896743) B1896743
theorem B10800125 : Blo 1120629 10800125 := bstep (se 3 (by rfl) ⟨2025023, by rfl⟩ : syracuseStep 10800125 = 4050047) B4050047
theorem B1265179 : Blo 1120629 1265179 := bstep (se 1 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 1265179 = 1897769) B1897769
theorem B43145135 : Blo 1120629 43145135 := bstep (se 1 (by rfl) ⟨32358851, by rfl⟩ : syracuseStep 43145135 = 64717703) B64717703
theorem B8509859 : Blo 1120629 8509859 := bstep (se 1 (by rfl) ⟨6382394, by rfl⟩ : syracuseStep 8509859 = 12764789) B12764789
theorem B5692031 : Blo 1120629 5692031 := bstep (se 1 (by rfl) ⟨4269023, by rfl⟩ : syracuseStep 5692031 = 8538047) B8538047
theorem B3792095 : Blo 1120629 3792095 := bstep (se 1 (by rfl) ⟨2844071, by rfl⟩ : syracuseStep 3792095 = 5688143) B5688143
theorem B12148717 : Blo 1120629 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B2842847 : Blo 1120629 2842847 := bstep (se 1 (by rfl) ⟨2132135, by rfl⟩ : syracuseStep 2842847 = 4264271) B4264271
theorem B2843039 : Blo 1120629 2843039 := bstep (se 1 (by rfl) ⟨2132279, by rfl⟩ : syracuseStep 2843039 = 4264559) B4264559
theorem B3793499 : Blo 1120629 3793499 := bstep (se 1 (by rfl) ⟨2845124, by rfl⟩ : syracuseStep 3793499 = 5690249) B5690249
theorem B9725065 : Blo 1120629 9725065 := bstep (se 2 (by rfl) ⟨3646899, by rfl⟩ : syracuseStep 9725065 = 7293799) B7293799
theorem B2844031 : Blo 1120629 2844031 := bstep (se 1 (by rfl) ⟨2133023, by rfl⟩ : syracuseStep 2844031 = 4266047) B4266047
theorem B10774255 : Blo 1120629 10774255 := bstep (se 1 (by rfl) ⟨8080691, by rfl⟩ : syracuseStep 10774255 = 16161383) B16161383
theorem B82962577 : Blo 1120629 82962577 := bstep (se 2 (by rfl) ⟨31110966, by rfl⟩ : syracuseStep 82962577 = 62221933) B62221933
theorem B2844983 : Blo 1120629 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B7204571 : Blo 1120629 7204571 := bstep (se 1 (by rfl) ⟨5403428, by rfl⟩ : syracuseStep 7204571 = 10806857) B10806857
theorem B12120475 : Blo 1120629 12120475 := bstep (se 1 (by rfl) ⟨9090356, by rfl⟩ : syracuseStep 12120475 = 18180713) B18180713
theorem B1897087 : Blo 1120629 1897087 := bstep (se 1 (by rfl) ⟨1422815, by rfl⟩ : syracuseStep 1897087 = 2845631) B2845631
theorem B18740321 : Blo 1120629 18740321 := bstep (se 2 (by rfl) ⟨7027620, by rfl⟩ : syracuseStep 18740321 = 14055241) B14055241
theorem B48527207 : Blo 1120629 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B4323611 : Blo 1120629 4323611 := bstep (se 1 (by rfl) ⟨3242708, by rfl⟩ : syracuseStep 4323611 = 6485417) B6485417
theorem B6388091 : Blo 1120629 6388091 := bstep (se 1 (by rfl) ⟨4791068, by rfl⟩ : syracuseStep 6388091 = 9582137) B9582137
theorem B40925573 : Blo 1120629 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B16186807 : Blo 1120629 16186807 := bstep (se 1 (by rfl) ⟨12140105, by rfl⟩ : syracuseStep 16186807 = 24280211) B24280211
theorem B2522591 : Blo 1120629 2522591 := bstep (se 1 (by rfl) ⟨1891943, by rfl⟩ : syracuseStep 2522591 = 3783887) B3783887
theorem B40992581 : Blo 1120629 40992581 := bstep (se 4 (by rfl) ⟨3843054, by rfl⟩ : syracuseStep 40992581 = 7686109) B7686109
theorem B2523167 : Blo 1120629 2523167 := bstep (se 1 (by rfl) ⟨1892375, by rfl⟩ : syracuseStep 2523167 = 3784751) B3784751
theorem B6389867 : Blo 1120629 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B2493631 : Blo 1120629 2493631 := bstep (se 1 (by rfl) ⟨1870223, by rfl⟩ : syracuseStep 2493631 = 3740447) B3740447
theorem B5673239 : Blo 1120629 5673239 := bstep (se 1 (by rfl) ⟨4254929, by rfl⟩ : syracuseStep 5673239 = 8509859) B8509859
theorem B18485981 : Blo 1120629 18485981 := bstep (se 3 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 18485981 = 6932243) B6932243
theorem B2528063 : Blo 1120629 2528063 := bstep (se 1 (by rfl) ⟨1896047, by rfl⟩ : syracuseStep 2528063 = 3792095) B3792095
theorem B2528999 : Blo 1120629 2528999 := bstep (se 1 (by rfl) ⟨1896749, by rfl⟩ : syracuseStep 2528999 = 3793499) B3793499
theorem B16160633 : Blo 1120629 16160633 := bstep (se 2 (by rfl) ⟨6060237, by rfl⟩ : syracuseStep 16160633 = 12120475) B12120475
theorem B2529449 : Blo 1120629 2529449 := bstep (se 2 (by rfl) ⟨948543, by rfl⟩ : syracuseStep 2529449 = 1897087) B1897087
theorem B1121999 : Blo 1120629 1121999 := bstep (se 1 (by rfl) ⟨841499, by rfl⟩ : syracuseStep 1121999 = 1682999) B1682999
theorem B1122111 : Blo 1120629 1122111 := bstep (se 1 (by rfl) ⟨841583, by rfl⟩ : syracuseStep 1122111 = 1683167) B1683167
theorem B1122943 : Blo 1120629 1122943 := bstep (se 1 (by rfl) ⟨842207, by rfl⟩ : syracuseStep 1122943 = 1684415) B1684415
theorem B12493547 : Blo 1120629 12493547 := bstep (se 1 (by rfl) ⟨9370160, by rfl⟩ : syracuseStep 12493547 = 18740321) B18740321
theorem B73802639 : Blo 1120629 73802639 := bstep (se 1 (by rfl) ⟨55351979, by rfl⟩ : syracuseStep 73802639 = 110703959) B110703959
theorem B1516735 : Blo 1120629 1516735 := bstep (se 1 (by rfl) ⟨1137551, by rfl⟩ : syracuseStep 1516735 = 2275103) B2275103
theorem B32351471 : Blo 1120629 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B1123647 : Blo 1120629 1123647 := bstep (se 1 (by rfl) ⟨842735, by rfl⟩ : syracuseStep 1123647 = 1685471) B1685471
theorem B1124079 : Blo 1120629 1124079 := bstep (se 1 (by rfl) ⟨843059, by rfl⟩ : syracuseStep 1124079 = 1686119) B1686119
theorem B1124095 : Blo 1120629 1124095 := bstep (se 1 (by rfl) ⟨843071, by rfl⟩ : syracuseStep 1124095 = 1686143) B1686143
theorem B1681727 : Blo 1120629 1681727 := bstep (se 1 (by rfl) ⟨1261295, by rfl⟩ : syracuseStep 1681727 = 2522591) B2522591
theorem B16198289 : Blo 1120629 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B1682159 : Blo 1120629 1682159 := bstep (se 1 (by rfl) ⟨1261619, by rfl⟩ : syracuseStep 1682159 = 2523239) B2523239
theorem B1682303 : Blo 1120629 1682303 := bstep (se 1 (by rfl) ⟨1261727, by rfl⟩ : syracuseStep 1682303 = 2523455) B2523455
theorem B3419273 : Blo 1120629 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B1682591 : Blo 1120629 1682591 := bstep (se 1 (by rfl) ⟨1261943, by rfl⟩ : syracuseStep 1682591 = 2523887) B2523887
theorem B6008327 : Blo 1120629 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B1683209 : Blo 1120629 1683209 := bstep (se 2 (by rfl) ⟨631203, by rfl⟩ : syracuseStep 1683209 = 1262407) B1262407
theorem B1683227 : Blo 1120629 1683227 := bstep (se 1 (by rfl) ⟨1262420, by rfl⟩ : syracuseStep 1683227 = 2524841) B2524841
theorem B2633671 : Blo 1120629 2633671 := bstep (se 1 (by rfl) ⟨1975253, by rfl⟩ : syracuseStep 2633671 = 3950507) B3950507
theorem B3747815 : Blo 1120629 3747815 := bstep (se 1 (by rfl) ⟨2810861, by rfl⟩ : syracuseStep 3747815 = 5621723) B5621723
theorem B1684073 : Blo 1120629 1684073 := bstep (se 2 (by rfl) ⟨631527, by rfl⟩ : syracuseStep 1684073 = 1263055) B1263055
theorem B1684127 : Blo 1120629 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B1684295 : Blo 1120629 1684295 := bstep (se 1 (by rfl) ⟨1263221, by rfl⟩ : syracuseStep 1684295 = 2526443) B2526443
theorem B14365673 : Blo 1120629 14365673 := bstep (se 2 (by rfl) ⟨5387127, by rfl⟩ : syracuseStep 14365673 = 10774255) B10774255
theorem B5682311 : Blo 1120629 5682311 := bstep (se 1 (by rfl) ⟨4261733, by rfl⟩ : syracuseStep 5682311 = 8523467) B8523467
theorem B21607559 : Blo 1120629 21607559 := bstep (se 1 (by rfl) ⟨16205669, by rfl⟩ : syracuseStep 21607559 = 32411339) B32411339
theorem B1684715 : Blo 1120629 1684715 := bstep (se 1 (by rfl) ⟨1263536, by rfl⟩ : syracuseStep 1684715 = 2527073) B2527073
theorem B1685531 : Blo 1120629 1685531 := bstep (se 1 (by rfl) ⟨1264148, by rfl⟩ : syracuseStep 1685531 = 2528297) B2528297
theorem B1685993 : Blo 1120629 1685993 := bstep (se 2 (by rfl) ⟨632247, by rfl⟩ : syracuseStep 1685993 = 1264495) B1264495
theorem B13679225 : Blo 1120629 13679225 := bstep (se 2 (by rfl) ⟨5129709, by rfl⟩ : syracuseStep 13679225 = 10259419) B10259419
theorem B1686383 : Blo 1120629 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B1686779 : Blo 1120629 1686779 := bstep (se 1 (by rfl) ⟨1265084, by rfl⟩ : syracuseStep 1686779 = 2530169) B2530169
theorem B1686905 : Blo 1120629 1686905 := bstep (se 2 (by rfl) ⟨632589, by rfl⟩ : syracuseStep 1686905 = 1265179) B1265179
theorem B20759581 : Blo 1120629 20759581 := bstep (se 3 (by rfl) ⟨3892421, by rfl⟩ : syracuseStep 20759581 = 7784843) B7784843
theorem B5129345 : Blo 1120629 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B4803047 : Blo 1120629 4803047 := bstep (se 1 (by rfl) ⟨3602285, by rfl⟩ : syracuseStep 4803047 = 7204571) B7204571
theorem B3788315 : Blo 1120629 3788315 := bstep (se 1 (by rfl) ⟨2841236, by rfl⟩ : syracuseStep 3788315 = 5682473) B5682473
theorem B27283715 : Blo 1120629 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B21582409 : Blo 1120629 21582409 := bstep (se 2 (by rfl) ⟨8093403, by rfl⟩ : syracuseStep 21582409 = 16186807) B16186807
theorem B2840953 : Blo 1120629 2840953 := bstep (se 2 (by rfl) ⟨1065357, by rfl⟩ : syracuseStep 2840953 = 2130715) B2130715
theorem B3070651 : Blo 1120629 3070651 := bstep (se 1 (by rfl) ⟨2302988, by rfl⟩ : syracuseStep 3070651 = 4605977) B4605977
theorem B3792041 : Blo 1120629 3792041 := bstep (se 2 (by rfl) ⟨1422015, by rfl⟩ : syracuseStep 3792041 = 2844031) B2844031
theorem B7200083 : Blo 1120629 7200083 := bstep (se 1 (by rfl) ⟨5400062, by rfl⟩ : syracuseStep 7200083 = 10800125) B10800125
theorem B3235663 : Blo 1120629 3235663 := bstep (se 1 (by rfl) ⟨2426747, by rfl⟩ : syracuseStep 3235663 = 4853495) B4853495
theorem B14376791 : Blo 1120629 14376791 := bstep (se 1 (by rfl) ⟨10782593, by rfl⟩ : syracuseStep 14376791 = 21565187) B21565187
theorem B110616769 : Blo 1120629 110616769 := bstep (se 2 (by rfl) ⟨41481288, by rfl⟩ : syracuseStep 110616769 = 82962577) B82962577
theorem B28763423 : Blo 1120629 28763423 := bstep (se 1 (by rfl) ⟨21572567, by rfl⟩ : syracuseStep 28763423 = 43145135) B43145135
theorem B17524255 : Blo 1120629 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B3794687 : Blo 1120629 3794687 := bstep (se 1 (by rfl) ⟨2846015, by rfl⟩ : syracuseStep 3794687 = 5692031) B5692031
theorem B32401295 : Blo 1120629 32401295 := bstep (se 1 (by rfl) ⟨24300971, by rfl⟩ : syracuseStep 32401295 = 48601943) B48601943
theorem B1796735 : Blo 1120629 1796735 := bstep (se 1 (by rfl) ⟨1347551, by rfl⟩ : syracuseStep 1796735 = 2695103) B2695103
theorem B3599005 : Blo 1120629 3599005 := bstep (se 3 (by rfl) ⟨674813, by rfl⟩ : syracuseStep 3599005 = 1349627) B1349627
theorem B1796843 : Blo 1120629 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B1895177 : Blo 1120629 1895177 := bstep (se 2 (by rfl) ⟨710691, by rfl⟩ : syracuseStep 1895177 = 1421383) B1421383
theorem B1895231 : Blo 1120629 1895231 := bstep (se 1 (by rfl) ⟨1421423, by rfl⟩ : syracuseStep 1895231 = 2842847) B2842847
theorem B1895359 : Blo 1120629 1895359 := bstep (se 1 (by rfl) ⟨1421519, by rfl⟩ : syracuseStep 1895359 = 2843039) B2843039
theorem B51867013 : Blo 1120629 51867013 := bstep (se 4 (by rfl) ⟨4862532, by rfl⟩ : syracuseStep 51867013 = 9725065) B9725065
theorem B1896655 : Blo 1120629 1896655 := bstep (se 1 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 1896655 = 2844983) B2844983
theorem B24605801 : Blo 1120629 24605801 := bstep (se 2 (by rfl) ⟨9227175, by rfl⟩ : syracuseStep 24605801 = 18454351) B18454351
theorem B2127647 : Blo 1120629 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B12286099 : Blo 1120629 12286099 := bstep (se 1 (by rfl) ⟨9214574, by rfl⟩ : syracuseStep 12286099 = 18429149) B18429149
theorem B5536253 : Blo 1120629 5536253 := bstep (se 3 (by rfl) ⟨1038047, by rfl⟩ : syracuseStep 5536253 = 2076095) B2076095
theorem B2521727 : Blo 1120629 2521727 := bstep (se 1 (by rfl) ⟨1891295, by rfl⟩ : syracuseStep 2521727 = 3782591) B3782591
theorem B2882407 : Blo 1120629 2882407 := bstep (se 1 (by rfl) ⟨2161805, by rfl⟩ : syracuseStep 2882407 = 4323611) B4323611
theorem B4258727 : Blo 1120629 4258727 := bstep (se 1 (by rfl) ⟨3194045, by rfl⟩ : syracuseStep 4258727 = 6388091) B6388091
theorem B2129159 : Blo 1120629 2129159 := bstep (se 1 (by rfl) ⟨1596869, by rfl⟩ : syracuseStep 2129159 = 3193739) B3193739
theorem B51936875 : Blo 1120629 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B46104329 : Blo 1120629 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B27328387 : Blo 1120629 27328387 := bstep (se 1 (by rfl) ⟨20496290, by rfl⟩ : syracuseStep 27328387 = 40992581) B40992581
theorem B4259911 : Blo 1120629 4259911 := bstep (se 1 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 4259911 = 6389867) B6389867
theorem B147489025 : Blo 1120629 147489025 := bstep (se 2 (by rfl) ⟨55308384, by rfl⟩ : syracuseStep 147489025 = 110616769) B110616769
theorem B23365673 : Blo 1120629 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B2525543 : Blo 1120629 2525543 := bstep (se 1 (by rfl) ⟨1894157, by rfl⟩ : syracuseStep 2525543 = 3788315) B3788315
theorem B18189143 : Blo 1120629 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B12323987 : Blo 1120629 12323987 := bstep (se 1 (by rfl) ⟨9242990, by rfl⟩ : syracuseStep 12323987 = 18485981) B18485981
theorem B2527145 : Blo 1120629 2527145 := bstep (se 2 (by rfl) ⟨947679, by rfl⟩ : syracuseStep 2527145 = 1895359) B1895359
theorem B5673725 : Blo 1120629 5673725 := bstep (se 3 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 5673725 = 2127647) B2127647
theorem B2528027 : Blo 1120629 2528027 := bstep (se 1 (by rfl) ⟨1896020, by rfl⟩ : syracuseStep 2528027 = 3792041) B3792041
theorem B3511561 : Blo 1120629 3511561 := bstep (se 2 (by rfl) ⟨1316835, by rfl⟩ : syracuseStep 3511561 = 2633671) B2633671
theorem B2528873 : Blo 1120629 2528873 := bstep (se 2 (by rfl) ⟨948327, by rfl⟩ : syracuseStep 2528873 = 1896655) B1896655
theorem B8329031 : Blo 1120629 8329031 := bstep (se 1 (by rfl) ⟨6246773, by rfl⟩ : syracuseStep 8329031 = 12493547) B12493547
theorem B28776545 : Blo 1120629 28776545 := bstep (se 2 (by rfl) ⟨10791204, by rfl⟩ : syracuseStep 28776545 = 21582409) B21582409
theorem B21567647 : Blo 1120629 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B19175615 : Blo 1120629 19175615 := bstep (se 1 (by rfl) ⟨14381711, by rfl⟩ : syracuseStep 19175615 = 28763423) B28763423
theorem B2529791 : Blo 1120629 2529791 := bstep (se 1 (by rfl) ⟨1897343, by rfl⟩ : syracuseStep 2529791 = 3794687) B3794687
theorem B21600863 : Blo 1120629 21600863 := bstep (se 1 (by rfl) ⟨16200647, by rfl⟩ : syracuseStep 21600863 = 32401295) B32401295
theorem B1121151 : Blo 1120629 1121151 := bstep (se 1 (by rfl) ⟨840863, by rfl⟩ : syracuseStep 1121151 = 1681727) B1681727
theorem B1121439 : Blo 1120629 1121439 := bstep (se 1 (by rfl) ⟨841079, by rfl⟩ : syracuseStep 1121439 = 1682159) B1682159
theorem B1121535 : Blo 1120629 1121535 := bstep (se 1 (by rfl) ⟨841151, by rfl⟩ : syracuseStep 1121535 = 1682303) B1682303
theorem B4791581 : Blo 1120629 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B1121727 : Blo 1120629 1121727 := bstep (se 1 (by rfl) ⟨841295, by rfl⟩ : syracuseStep 1121727 = 1682591) B1682591
theorem B4005551 : Blo 1120629 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B1122139 : Blo 1120629 1122139 := bstep (se 1 (by rfl) ⟨841604, by rfl⟩ : syracuseStep 1122139 = 1683209) B1683209
theorem B1122151 : Blo 1120629 1122151 := bstep (se 1 (by rfl) ⟨841613, by rfl⟩ : syracuseStep 1122151 = 1683227) B1683227
theorem B2498543 : Blo 1120629 2498543 := bstep (se 1 (by rfl) ⟨1873907, by rfl⟩ : syracuseStep 2498543 = 3747815) B3747815
theorem B1122715 : Blo 1120629 1122715 := bstep (se 1 (by rfl) ⟨842036, by rfl⟩ : syracuseStep 1122715 = 1684073) B1684073
theorem B1122751 : Blo 1120629 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B1122863 : Blo 1120629 1122863 := bstep (se 1 (by rfl) ⟨842147, by rfl⟩ : syracuseStep 1122863 = 1684295) B1684295
theorem B9577115 : Blo 1120629 9577115 := bstep (se 1 (by rfl) ⟨7182836, by rfl⟩ : syracuseStep 9577115 = 14365673) B14365673
theorem B1123143 : Blo 1120629 1123143 := bstep (se 1 (by rfl) ⟨842357, by rfl⟩ : syracuseStep 1123143 = 1684715) B1684715
theorem B3843209 : Blo 1120629 3843209 := bstep (se 2 (by rfl) ⟨1441203, by rfl⟩ : syracuseStep 3843209 = 2882407) B2882407
theorem B1123687 : Blo 1120629 1123687 := bstep (se 1 (by rfl) ⟨842765, by rfl⟩ : syracuseStep 1123687 = 1685531) B1685531
theorem B1123995 : Blo 1120629 1123995 := bstep (se 1 (by rfl) ⟨842996, by rfl⟩ : syracuseStep 1123995 = 1685993) B1685993
theorem B9119483 : Blo 1120629 9119483 := bstep (se 1 (by rfl) ⟨6839612, by rfl⟩ : syracuseStep 9119483 = 13679225) B13679225
theorem B1681151 : Blo 1120629 1681151 := bstep (se 1 (by rfl) ⟨1260863, by rfl⟩ : syracuseStep 1681151 = 2521727) B2521727
theorem B1124255 : Blo 1120629 1124255 := bstep (se 1 (by rfl) ⟨843191, by rfl⟩ : syracuseStep 1124255 = 1686383) B1686383
theorem B1124519 : Blo 1120629 1124519 := bstep (se 1 (by rfl) ⟨843389, by rfl⟩ : syracuseStep 1124519 = 1686779) B1686779
theorem B1419439 : Blo 1120629 1419439 := bstep (se 1 (by rfl) ⟨1064579, by rfl⟩ : syracuseStep 1419439 = 2129159) B2129159
theorem B1124603 : Blo 1120629 1124603 := bstep (se 1 (by rfl) ⟨843452, by rfl⟩ : syracuseStep 1124603 = 1686905) B1686905
theorem B1682111 : Blo 1120629 1682111 := bstep (se 1 (by rfl) ⟨1261583, by rfl⟩ : syracuseStep 1682111 = 2523167) B2523167
theorem B3419563 : Blo 1120629 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B3782159 : Blo 1120629 3782159 := bstep (se 1 (by rfl) ⟨2836619, by rfl⟩ : syracuseStep 3782159 = 5673239) B5673239
theorem B1685375 : Blo 1120629 1685375 := bstep (se 1 (by rfl) ⟨1264031, by rfl⟩ : syracuseStep 1685375 = 2528063) B2528063
theorem B4798673 : Blo 1120629 4798673 := bstep (se 2 (by rfl) ⟨1799502, by rfl⟩ : syracuseStep 4798673 = 3599005) B3599005
theorem B1685999 : Blo 1120629 1685999 := bstep (se 1 (by rfl) ⟨1264499, by rfl⟩ : syracuseStep 1685999 = 2528999) B2528999
theorem B1686299 : Blo 1120629 1686299 := bstep (se 1 (by rfl) ⟨1264724, by rfl⟩ : syracuseStep 1686299 = 2529449) B2529449
theorem B69156017 : Blo 1120629 69156017 := bstep (se 2 (by rfl) ⟨25933506, by rfl⟩ : syracuseStep 69156017 = 51867013) B51867013
theorem B4800055 : Blo 1120629 4800055 := bstep (se 1 (by rfl) ⟨3600041, by rfl⟩ : syracuseStep 4800055 = 7200083) B7200083
theorem B9584527 : Blo 1120629 9584527 := bstep (se 1 (by rfl) ⟨7188395, by rfl⟩ : syracuseStep 9584527 = 14376791) B14376791
theorem B49201759 : Blo 1120629 49201759 := bstep (se 1 (by rfl) ⟨36901319, by rfl⟩ : syracuseStep 49201759 = 73802639) B73802639
theorem B1197823 : Blo 1120629 1197823 := bstep (se 1 (by rfl) ⟨898367, by rfl⟩ : syracuseStep 1197823 = 1796735) B1796735
theorem B10798859 : Blo 1120629 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B1263451 : Blo 1120629 1263451 := bstep (se 1 (by rfl) ⟨947588, by rfl⟩ : syracuseStep 1263451 = 1895177) B1895177
theorem B1263487 : Blo 1120629 1263487 := bstep (se 1 (by rfl) ⟨947615, by rfl⟩ : syracuseStep 1263487 = 1895231) B1895231
theorem B2279515 : Blo 1120629 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B3787937 : Blo 1120629 3787937 := bstep (se 2 (by rfl) ⟨1420476, by rfl⟩ : syracuseStep 3787937 = 2840953) B2840953
theorem B16403867 : Blo 1120629 16403867 := bstep (se 1 (by rfl) ⟨12302900, by rfl⟩ : syracuseStep 16403867 = 24605801) B24605801
theorem B3788207 : Blo 1120629 3788207 := bstep (se 1 (by rfl) ⟨2841155, by rfl⟩ : syracuseStep 3788207 = 5682311) B5682311
theorem B14405039 : Blo 1120629 14405039 := bstep (se 1 (by rfl) ⟨10803779, by rfl⟩ : syracuseStep 14405039 = 21607559) B21607559
theorem B3690835 : Blo 1120629 3690835 := bstep (se 1 (by rfl) ⟨2768126, by rfl⟩ : syracuseStep 3690835 = 5536253) B5536253
theorem B2839151 : Blo 1120629 2839151 := bstep (se 1 (by rfl) ⟨2129363, by rfl⟩ : syracuseStep 2839151 = 4258727) B4258727
theorem B34624583 : Blo 1120629 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B4314217 : Blo 1120629 4314217 := bstep (se 2 (by rfl) ⟨1617831, by rfl⟩ : syracuseStep 4314217 = 3235663) B3235663
theorem B65525861 : Blo 1120629 65525861 := bstep (se 4 (by rfl) ⟨6143049, by rfl⟩ : syracuseStep 65525861 = 12286099) B12286099
theorem B3202031 : Blo 1120629 3202031 := bstep (se 1 (by rfl) ⟨2401523, by rfl⟩ : syracuseStep 3202031 = 4803047) B4803047
theorem B10773755 : Blo 1120629 10773755 := bstep (se 1 (by rfl) ⟨8080316, by rfl⟩ : syracuseStep 10773755 = 16160633) B16160633
theorem B110717765 : Blo 1120629 110717765 := bstep (se 4 (by rfl) ⟨10379790, by rfl⟩ : syracuseStep 110717765 = 20759581) B20759581
theorem B13299365 : Blo 1120629 13299365 := bstep (se 4 (by rfl) ⟨1246815, by rfl⟩ : syracuseStep 13299365 = 2493631) B2493631
theorem B8089253 : Blo 1120629 8089253 := bstep (se 4 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 8089253 = 1516735) B1516735
theorem B4094201 : Blo 1120629 4094201 := bstep (se 2 (by rfl) ⟨1535325, by rfl⟩ : syracuseStep 4094201 = 3070651) B3070651
theorem B36437849 : Blo 1120629 36437849 := bstep (se 2 (by rfl) ⟨13664193, by rfl⟩ : syracuseStep 36437849 = 27328387) B27328387
theorem B30736219 : Blo 1120629 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B12126095 : Blo 1120629 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B2525291 : Blo 1120629 2525291 := bstep (se 1 (by rfl) ⟨1893968, by rfl⟩ : syracuseStep 2525291 = 3787937) B3787937
theorem B2525471 : Blo 1120629 2525471 := bstep (se 1 (by rfl) ⟨1894103, by rfl⟩ : syracuseStep 2525471 = 3788207) B3788207
theorem B9603359 : Blo 1120629 9603359 := bstep (se 1 (by rfl) ⟨7202519, by rfl⟩ : syracuseStep 9603359 = 14405039) B14405039
theorem B262409381 : Blo 1120629 262409381 := bstep (se 4 (by rfl) ⟨24600879, by rfl⟩ : syracuseStep 262409381 = 49201759) B49201759
theorem B12783743 : Blo 1120629 12783743 := bstep (se 1 (by rfl) ⟨9587807, by rfl⟩ : syracuseStep 12783743 = 19175615) B19175615
theorem B4559417 : Blo 1120629 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B2134687 : Blo 1120629 2134687 := bstep (se 1 (by rfl) ⟨1601015, by rfl⟩ : syracuseStep 2134687 = 3202031) B3202031
theorem B2562139 : Blo 1120629 2562139 := bstep (se 1 (by rfl) ⟨1921604, by rfl⟩ : syracuseStep 2562139 = 3843209) B3843209
theorem B7182503 : Blo 1120629 7182503 := bstep (se 1 (by rfl) ⟨5386877, by rfl⟩ : syracuseStep 7182503 = 10773755) B10773755
theorem B1120767 : Blo 1120629 1120767 := bstep (se 1 (by rfl) ⟨840575, by rfl⟩ : syracuseStep 1120767 = 1681151) B1681151
theorem B1121407 : Blo 1120629 1121407 := bstep (se 1 (by rfl) ⟨841055, by rfl⟩ : syracuseStep 1121407 = 1682111) B1682111
theorem B1123583 : Blo 1120629 1123583 := bstep (se 1 (by rfl) ⟨842687, by rfl⟩ : syracuseStep 1123583 = 1685375) B1685375
theorem B2729467 : Blo 1120629 2729467 := bstep (se 1 (by rfl) ⟨2047100, by rfl⟩ : syracuseStep 2729467 = 4094201) B4094201
theorem B1123999 : Blo 1120629 1123999 := bstep (se 1 (by rfl) ⟨842999, by rfl⟩ : syracuseStep 1123999 = 1685999) B1685999
theorem B35464973 : Blo 1120629 35464973 := bstep (se 3 (by rfl) ⟨6649682, by rfl⟩ : syracuseStep 35464973 = 13299365) B13299365
theorem B1124199 : Blo 1120629 1124199 := bstep (se 1 (by rfl) ⟨843149, by rfl⟩ : syracuseStep 1124199 = 1686299) B1686299
theorem B6400073 : Blo 1120629 6400073 := bstep (se 2 (by rfl) ⟨2400027, by rfl⟩ : syracuseStep 6400073 = 4800055) B4800055
theorem B24291899 : Blo 1120629 24291899 := bstep (se 1 (by rfl) ⟨18218924, by rfl⟩ : syracuseStep 24291899 = 36437849) B36437849
theorem B5679881 : Blo 1120629 5679881 := bstep (se 2 (by rfl) ⟨2129955, by rfl⟩ : syracuseStep 5679881 = 4259911) B4259911
theorem B196652033 : Blo 1120629 196652033 := bstep (se 2 (by rfl) ⟨73744512, by rfl⟩ : syracuseStep 196652033 = 147489025) B147489025
theorem B15577115 : Blo 1120629 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B1683695 : Blo 1120629 1683695 := bstep (se 1 (by rfl) ⟨1262771, by rfl⟩ : syracuseStep 1683695 = 2525543) B2525543
theorem B1684601 : Blo 1120629 1684601 := bstep (se 2 (by rfl) ⟨631725, by rfl⟩ : syracuseStep 1684601 = 1263451) B1263451
theorem B1684649 : Blo 1120629 1684649 := bstep (se 2 (by rfl) ⟨631743, by rfl⟩ : syracuseStep 1684649 = 1263487) B1263487
theorem B1684763 : Blo 1120629 1684763 := bstep (se 1 (by rfl) ⟨1263572, by rfl⟩ : syracuseStep 1684763 = 2527145) B2527145
theorem B3782483 : Blo 1120629 3782483 := bstep (se 1 (by rfl) ⟨2836862, by rfl⟩ : syracuseStep 3782483 = 5673725) B5673725
theorem B1685351 : Blo 1120629 1685351 := bstep (se 1 (by rfl) ⟨1264013, by rfl⟩ : syracuseStep 1685351 = 2528027) B2528027
theorem B23083055 : Blo 1120629 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B1685915 : Blo 1120629 1685915 := bstep (se 1 (by rfl) ⟨1264436, by rfl⟩ : syracuseStep 1685915 = 2528873) B2528873
theorem B5552687 : Blo 1120629 5552687 := bstep (se 1 (by rfl) ⟨4164515, by rfl⟩ : syracuseStep 5552687 = 8329031) B8329031
theorem B19184363 : Blo 1120629 19184363 := bstep (se 1 (by rfl) ⟨14388272, by rfl⟩ : syracuseStep 19184363 = 28776545) B28776545
theorem B1686527 : Blo 1120629 1686527 := bstep (se 1 (by rfl) ⟨1264895, by rfl⟩ : syracuseStep 1686527 = 2529791) B2529791
theorem B14400575 : Blo 1120629 14400575 := bstep (se 1 (by rfl) ⟨10800431, by rfl⟩ : syracuseStep 14400575 = 21600863) B21600863
theorem B3194387 : Blo 1120629 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B174735629 : Blo 1120629 174735629 := bstep (se 3 (by rfl) ⟨32762930, by rfl⟩ : syracuseStep 174735629 = 65525861) B65525861
theorem B6079655 : Blo 1120629 6079655 := bstep (se 1 (by rfl) ⟨4559741, by rfl⟩ : syracuseStep 6079655 = 9119483) B9119483
theorem B5752289 : Blo 1120629 5752289 := bstep (se 2 (by rfl) ⟨2157108, by rfl⟩ : syracuseStep 5752289 = 4314217) B4314217
theorem B73811843 : Blo 1120629 73811843 := bstep (se 1 (by rfl) ⟨55358882, by rfl⟩ : syracuseStep 73811843 = 110717765) B110717765
theorem B5392835 : Blo 1120629 5392835 := bstep (se 1 (by rfl) ⟨4044626, by rfl⟩ : syracuseStep 5392835 = 8089253) B8089253
theorem B3199115 : Blo 1120629 3199115 := bstep (se 1 (by rfl) ⟨2399336, by rfl⟩ : syracuseStep 3199115 = 4798673) B4798673
theorem B40981625 : Blo 1120629 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B7199239 : Blo 1120629 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B19684453 : Blo 1120629 19684453 := bstep (se 4 (by rfl) ⟨1845417, by rfl⟩ : syracuseStep 19684453 = 3690835) B3690835
theorem B8215991 : Blo 1120629 8215991 := bstep (se 1 (by rfl) ⟨6161993, by rfl⟩ : syracuseStep 8215991 = 12323987) B12323987
theorem B10935911 : Blo 1120629 10935911 := bstep (se 1 (by rfl) ⟨8201933, by rfl⟩ : syracuseStep 10935911 = 16403867) B16403867
theorem B1597097 : Blo 1120629 1597097 := bstep (se 2 (by rfl) ⟨598911, by rfl⟩ : syracuseStep 1597097 = 1197823) B1197823
theorem B3039353 : Blo 1120629 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B1892585 : Blo 1120629 1892585 := bstep (se 2 (by rfl) ⟨709719, by rfl⟩ : syracuseStep 1892585 = 1419439) B1419439
theorem B1892767 : Blo 1120629 1892767 := bstep (se 1 (by rfl) ⟨1419575, by rfl⟩ : syracuseStep 1892767 = 2839151) B2839151
theorem B14378431 : Blo 1120629 14378431 := bstep (se 1 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 14378431 = 21567647) B21567647
theorem B1665695 : Blo 1120629 1665695 := bstep (se 1 (by rfl) ⟨1249271, by rfl⟩ : syracuseStep 1665695 = 2498543) B2498543
theorem B6384743 : Blo 1120629 6384743 := bstep (se 1 (by rfl) ⟨4788557, by rfl⟩ : syracuseStep 6384743 = 9577115) B9577115
theorem B4682081 : Blo 1120629 4682081 := bstep (se 2 (by rfl) ⟨1755780, by rfl⟩ : syracuseStep 4682081 = 3511561) B3511561
theorem B2521439 : Blo 1120629 2521439 := bstep (se 1 (by rfl) ⟨1891079, by rfl⟩ : syracuseStep 2521439 = 3782159) B3782159
theorem B10681469 : Blo 1120629 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B46104011 : Blo 1120629 46104011 := bstep (se 1 (by rfl) ⟨34578008, by rfl⟩ : syracuseStep 46104011 = 69156017) B69156017
theorem B12779369 : Blo 1120629 12779369 := bstep (se 2 (by rfl) ⟨4792263, by rfl⟩ : syracuseStep 12779369 = 9584527) B9584527
theorem B116490419 : Blo 1120629 116490419 := bstep (se 1 (by rfl) ⟨87367814, by rfl⟩ : syracuseStep 116490419 = 174735629) B174735629
theorem B2523689 : Blo 1120629 2523689 := bstep (se 2 (by rfl) ⟨946383, by rfl⟩ : syracuseStep 2523689 = 1892767) B1892767
theorem B12485549 : Blo 1120629 12485549 := bstep (se 3 (by rfl) ⟨2341040, by rfl⟩ : syracuseStep 12485549 = 4682081) B4682081
theorem B3834859 : Blo 1120629 3834859 := bstep (se 1 (by rfl) ⟨2876144, by rfl⟩ : syracuseStep 3834859 = 5752289) B5752289
theorem B19171241 : Blo 1120629 19171241 := bstep (se 2 (by rfl) ⟨7189215, by rfl⟩ : syracuseStep 19171241 = 14378431) B14378431
theorem B3639289 : Blo 1120629 3639289 := bstep (se 2 (by rfl) ⟨1364733, by rfl⟩ : syracuseStep 3639289 = 2729467) B2729467
theorem B8522495 : Blo 1120629 8522495 := bstep (se 1 (by rfl) ⟨6391871, by rfl⟩ : syracuseStep 8522495 = 12783743) B12783743
theorem B2132743 : Blo 1120629 2132743 := bstep (se 1 (by rfl) ⟨1599557, by rfl⟩ : syracuseStep 2132743 = 3199115) B3199115
theorem B4788335 : Blo 1120629 4788335 := bstep (se 1 (by rfl) ⟨3591251, by rfl⟩ : syracuseStep 4788335 = 7182503) B7182503
theorem B94573261 : Blo 1120629 94573261 := bstep (se 3 (by rfl) ⟨17732486, by rfl⟩ : syracuseStep 94573261 = 35464973) B35464973
theorem B5477327 : Blo 1120629 5477327 := bstep (se 1 (by rfl) ⟨4107995, by rfl⟩ : syracuseStep 5477327 = 8215991) B8215991
theorem B4266715 : Blo 1120629 4266715 := bstep (se 1 (by rfl) ⟨3200036, by rfl⟩ : syracuseStep 4266715 = 6400073) B6400073
theorem B16194599 : Blo 1120629 16194599 := bstep (se 1 (by rfl) ⟨12145949, by rfl⟩ : syracuseStep 16194599 = 24291899) B24291899
theorem B3416185 : Blo 1120629 3416185 := bstep (se 2 (by rfl) ⟨1281069, by rfl⟩ : syracuseStep 3416185 = 2562139) B2562139
theorem B1122463 : Blo 1120629 1122463 := bstep (se 1 (by rfl) ⟨841847, by rfl⟩ : syracuseStep 1122463 = 1683695) B1683695
theorem B1123067 : Blo 1120629 1123067 := bstep (se 1 (by rfl) ⟨842300, by rfl⟩ : syracuseStep 1123067 = 1684601) B1684601
theorem B1123099 : Blo 1120629 1123099 := bstep (se 1 (by rfl) ⟨842324, by rfl⟩ : syracuseStep 1123099 = 1684649) B1684649
theorem B1123175 : Blo 1120629 1123175 := bstep (se 1 (by rfl) ⟨842381, by rfl⟩ : syracuseStep 1123175 = 1684763) B1684763
theorem B1123567 : Blo 1120629 1123567 := bstep (se 1 (by rfl) ⟨842675, by rfl⟩ : syracuseStep 1123567 = 1685351) B1685351
theorem B1680959 : Blo 1120629 1680959 := bstep (se 1 (by rfl) ⟨1260719, by rfl⟩ : syracuseStep 1680959 = 2521439) B2521439
theorem B1123943 : Blo 1120629 1123943 := bstep (se 1 (by rfl) ⟨842957, by rfl⟩ : syracuseStep 1123943 = 1685915) B1685915
theorem B12789575 : Blo 1120629 12789575 := bstep (se 1 (by rfl) ⟨9592181, by rfl⟩ : syracuseStep 12789575 = 19184363) B19184363
theorem B1124351 : Blo 1120629 1124351 := bstep (se 1 (by rfl) ⟨843263, by rfl⟩ : syracuseStep 1124351 = 1686527) B1686527
theorem B7120979 : Blo 1120629 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B1683527 : Blo 1120629 1683527 := bstep (se 1 (by rfl) ⟨1262645, by rfl⟩ : syracuseStep 1683527 = 2525291) B2525291
theorem B1683647 : Blo 1120629 1683647 := bstep (se 1 (by rfl) ⟨1262735, by rfl⟩ : syracuseStep 1683647 = 2525471) B2525471
theorem B6402239 : Blo 1120629 6402239 := bstep (se 1 (by rfl) ⟨4801679, by rfl⟩ : syracuseStep 6402239 = 9603359) B9603359
theorem B1261723 : Blo 1120629 1261723 := bstep (se 1 (by rfl) ⟨946292, by rfl⟩ : syracuseStep 1261723 = 1892585) B1892585
theorem B4441853 : Blo 1120629 4441853 := bstep (se 3 (by rfl) ⟨832847, by rfl⟩ : syracuseStep 4441853 = 1665695) B1665695
theorem B3786587 : Blo 1120629 3786587 := bstep (se 1 (by rfl) ⟨2839940, by rfl⟩ : syracuseStep 3786587 = 5679881) B5679881
theorem B15388703 : Blo 1120629 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B41538973 : Blo 1120629 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B49207895 : Blo 1120629 49207895 := bstep (se 1 (by rfl) ⟨36905921, by rfl⟩ : syracuseStep 49207895 = 73811843) B73811843
theorem B8084063 : Blo 1120629 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B3595223 : Blo 1120629 3595223 := bstep (se 1 (by rfl) ⟨2696417, by rfl⟩ : syracuseStep 3595223 = 5392835) B5392835
theorem B174939587 : Blo 1120629 174939587 := bstep (se 1 (by rfl) ⟨131204690, by rfl⟩ : syracuseStep 174939587 = 262409381) B262409381
theorem B3039611 : Blo 1120629 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B16212413 : Blo 1120629 16212413 := bstep (se 3 (by rfl) ⟨3039827, by rfl⟩ : syracuseStep 16212413 = 6079655) B6079655
theorem B27321083 : Blo 1120629 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B2026235 : Blo 1120629 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B2846249 : Blo 1120629 2846249 := bstep (se 2 (by rfl) ⟨1067343, by rfl⟩ : syracuseStep 2846249 = 2134687) B2134687
theorem B131101355 : Blo 1120629 131101355 := bstep (se 1 (by rfl) ⟨98326016, by rfl⟩ : syracuseStep 131101355 = 196652033) B196652033
theorem B4256495 : Blo 1120629 4256495 := bstep (se 1 (by rfl) ⟨3192371, by rfl⟩ : syracuseStep 4256495 = 6384743) B6384743
theorem B9598985 : Blo 1120629 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B2521655 : Blo 1120629 2521655 := bstep (se 1 (by rfl) ⟨1891241, by rfl⟩ : syracuseStep 2521655 = 3782483) B3782483
theorem B26245937 : Blo 1120629 26245937 := bstep (se 2 (by rfl) ⟨9842226, by rfl⟩ : syracuseStep 26245937 = 19684453) B19684453
theorem B29162429 : Blo 1120629 29162429 := bstep (se 3 (by rfl) ⟨5467955, by rfl⟩ : syracuseStep 29162429 = 10935911) B10935911
theorem B3701791 : Blo 1120629 3701791 := bstep (se 1 (by rfl) ⟨2776343, by rfl⟩ : syracuseStep 3701791 = 5552687) B5552687
theorem B4258925 : Blo 1120629 4258925 := bstep (se 3 (by rfl) ⟨798548, by rfl⟩ : syracuseStep 4258925 = 1597097) B1597097
theorem B9600383 : Blo 1120629 9600383 := bstep (se 1 (by rfl) ⟨7200287, by rfl⟩ : syracuseStep 9600383 = 14400575) B14400575
theorem B30736007 : Blo 1120629 30736007 := bstep (se 1 (by rfl) ⟨23052005, by rfl⟩ : syracuseStep 30736007 = 46104011) B46104011
theorem B2129591 : Blo 1120629 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B8519579 : Blo 1120629 8519579 := bstep (se 1 (by rfl) ⟨6389684, by rfl⟩ : syracuseStep 8519579 = 12779369) B12779369
theorem B77660279 : Blo 1120629 77660279 := bstep (se 1 (by rfl) ⟨58245209, by rfl⟩ : syracuseStep 77660279 = 116490419) B116490419
theorem B4554913 : Blo 1120629 4554913 := bstep (se 2 (by rfl) ⟨1708092, by rfl⟩ : syracuseStep 4554913 = 3416185) B3416185
theorem B2524391 : Blo 1120629 2524391 := bstep (se 1 (by rfl) ⟨1893293, by rfl⟩ : syracuseStep 2524391 = 3786587) B3786587
theorem B12780827 : Blo 1120629 12780827 := bstep (se 1 (by rfl) ⟨9585620, by rfl⟩ : syracuseStep 12780827 = 19171241) B19171241
theorem B5113145 : Blo 1120629 5113145 := bstep (se 2 (by rfl) ⟨1917429, by rfl⟩ : syracuseStep 5113145 = 3834859) B3834859
theorem B33294797 : Blo 1120629 33294797 := bstep (se 3 (by rfl) ⟨6242774, by rfl⟩ : syracuseStep 33294797 = 12485549) B12485549
theorem B4852385 : Blo 1120629 4852385 := bstep (se 2 (by rfl) ⟨1819644, by rfl⟩ : syracuseStep 4852385 = 3639289) B3639289
theorem B10259135 : Blo 1120629 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B32805263 : Blo 1120629 32805263 := bstep (se 1 (by rfl) ⟨24603947, by rfl⟩ : syracuseStep 32805263 = 49207895) B49207895
theorem B116626391 : Blo 1120629 116626391 := bstep (se 1 (by rfl) ⟨87469793, by rfl⟩ : syracuseStep 116626391 = 174939587) B174939587
theorem B126097681 : Blo 1120629 126097681 := bstep (se 2 (by rfl) ⟨47286630, by rfl⟩ : syracuseStep 126097681 = 94573261) B94573261
theorem B1120639 : Blo 1120629 1120639 := bstep (se 1 (by rfl) ⟨840479, by rfl⟩ : syracuseStep 1120639 = 1680959) B1680959
theorem B8526383 : Blo 1120629 8526383 := bstep (se 1 (by rfl) ⟨6394787, by rfl⟩ : syracuseStep 8526383 = 12789575) B12789575
theorem B55385297 : Blo 1120629 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B1122351 : Blo 1120629 1122351 := bstep (se 1 (by rfl) ⟨841763, by rfl⟩ : syracuseStep 1122351 = 1683527) B1683527
theorem B1122431 : Blo 1120629 1122431 := bstep (se 1 (by rfl) ⟨841823, by rfl⟩ : syracuseStep 1122431 = 1683647) B1683647
theorem B4268159 : Blo 1120629 4268159 := bstep (se 1 (by rfl) ⟨3201119, by rfl⟩ : syracuseStep 4268159 = 6402239) B6402239
theorem B87400903 : Blo 1120629 87400903 := bstep (se 1 (by rfl) ⟨65550677, by rfl⟩ : syracuseStep 87400903 = 131101355) B131101355
theorem B6399323 : Blo 1120629 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B1681103 : Blo 1120629 1681103 := bstep (se 1 (by rfl) ⟨1260827, by rfl⟩ : syracuseStep 1681103 = 2521655) B2521655
theorem B5678909 : Blo 1120629 5678909 := bstep (se 3 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 5678909 = 2129591) B2129591
theorem B19441619 : Blo 1120629 19441619 := bstep (se 1 (by rfl) ⟨14581214, by rfl⟩ : syracuseStep 19441619 = 29162429) B29162429
theorem B6400255 : Blo 1120629 6400255 := bstep (se 1 (by rfl) ⟨4800191, by rfl⟩ : syracuseStep 6400255 = 9600383) B9600383
theorem B20490671 : Blo 1120629 20490671 := bstep (se 1 (by rfl) ⟨15368003, by rfl⟩ : syracuseStep 20490671 = 30736007) B30736007
theorem B5679719 : Blo 1120629 5679719 := bstep (se 1 (by rfl) ⟨4259789, by rfl⟩ : syracuseStep 5679719 = 8519579) B8519579
theorem B1682297 : Blo 1120629 1682297 := bstep (se 2 (by rfl) ⟨630861, by rfl⟩ : syracuseStep 1682297 = 1261723) B1261723
theorem B1682459 : Blo 1120629 1682459 := bstep (se 1 (by rfl) ⟨1261844, by rfl⟩ : syracuseStep 1682459 = 2523689) B2523689
theorem B2961235 : Blo 1120629 2961235 := bstep (se 1 (by rfl) ⟨2220926, by rfl⟩ : syracuseStep 2961235 = 4441853) B4441853
theorem B5681663 : Blo 1120629 5681663 := bstep (se 1 (by rfl) ⟨4261247, by rfl⟩ : syracuseStep 5681663 = 8522495) B8522495
theorem B3192223 : Blo 1120629 3192223 := bstep (se 1 (by rfl) ⟨2394167, by rfl⟩ : syracuseStep 3192223 = 4788335) B4788335
theorem B3651551 : Blo 1120629 3651551 := bstep (se 1 (by rfl) ⟨2738663, by rfl⟩ : syracuseStep 3651551 = 5477327) B5477327
theorem B32422517 : Blo 1120629 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B10796399 : Blo 1120629 10796399 := bstep (se 1 (by rfl) ⟨8097299, by rfl⟩ : syracuseStep 10796399 = 16194599) B16194599
theorem B19742885 : Blo 1120629 19742885 := bstep (se 4 (by rfl) ⟨1850895, by rfl⟩ : syracuseStep 19742885 = 3701791) B3701791
theorem B9587261 : Blo 1120629 9587261 := bstep (se 3 (by rfl) ⟨1797611, by rfl⟩ : syracuseStep 9587261 = 3595223) B3595223
theorem B2837663 : Blo 1120629 2837663 := bstep (se 1 (by rfl) ⟨2128247, by rfl⟩ : syracuseStep 2837663 = 4256495) B4256495
theorem B5688953 : Blo 1120629 5688953 := bstep (se 2 (by rfl) ⟨2133357, by rfl⟩ : syracuseStep 5688953 = 4266715) B4266715
theorem B2839283 : Blo 1120629 2839283 := bstep (se 1 (by rfl) ⟨2129462, by rfl⟩ : syracuseStep 2839283 = 4258925) B4258925
theorem B2843657 : Blo 1120629 2843657 := bstep (se 2 (by rfl) ⟨1066371, by rfl⟩ : syracuseStep 2843657 = 2132743) B2132743
theorem B10808275 : Blo 1120629 10808275 := bstep (se 1 (by rfl) ⟨8106206, by rfl⟩ : syracuseStep 10808275 = 16212413) B16212413
theorem B18214055 : Blo 1120629 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B4747319 : Blo 1120629 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B21557501 : Blo 1120629 21557501 := bstep (se 3 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 21557501 = 8084063) B8084063
theorem B5403293 : Blo 1120629 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B1897499 : Blo 1120629 1897499 := bstep (se 1 (by rfl) ⟨1423124, by rfl⟩ : syracuseStep 1897499 = 2846249) B2846249
theorem B17497291 : Blo 1120629 17497291 := bstep (se 1 (by rfl) ⟨13122968, by rfl⟩ : syracuseStep 17497291 = 26245937) B26245937
theorem B51773519 : Blo 1120629 51773519 := bstep (se 1 (by rfl) ⟨38830139, by rfl⟩ : syracuseStep 51773519 = 77660279) B77660279
theorem B8520551 : Blo 1120629 8520551 := bstep (se 1 (by rfl) ⟨6390413, by rfl⟩ : syracuseStep 8520551 = 12780827) B12780827
theorem B3408763 : Blo 1120629 3408763 := bstep (se 1 (by rfl) ⟨2556572, by rfl⟩ : syracuseStep 3408763 = 5113145) B5113145
theorem B6391507 : Blo 1120629 6391507 := bstep (se 1 (by rfl) ⟨4793630, by rfl⟩ : syracuseStep 6391507 = 9587261) B9587261
theorem B4266215 : Blo 1120629 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B1120735 : Blo 1120629 1120735 := bstep (se 1 (by rfl) ⟨840551, by rfl⟩ : syracuseStep 1120735 = 1681103) B1681103
theorem B1121531 : Blo 1120629 1121531 := bstep (se 1 (by rfl) ⟨841148, by rfl⟩ : syracuseStep 1121531 = 1682297) B1682297
theorem B1121639 : Blo 1120629 1121639 := bstep (se 1 (by rfl) ⟨841229, by rfl⟩ : syracuseStep 1121639 = 1682459) B1682459
theorem B2434367 : Blo 1120629 2434367 := bstep (se 1 (by rfl) ⟨1825775, by rfl⟩ : syracuseStep 2434367 = 3651551) B3651551
theorem B6073217 : Blo 1120629 6073217 := bstep (se 2 (by rfl) ⟨2277456, by rfl⟩ : syracuseStep 6073217 = 4554913) B4554913
theorem B116534537 : Blo 1120629 116534537 := bstep (se 2 (by rfl) ⟨43700451, by rfl⟩ : syracuseStep 116534537 = 87400903) B87400903
theorem B1682927 : Blo 1120629 1682927 := bstep (se 1 (by rfl) ⟨1262195, by rfl⟩ : syracuseStep 1682927 = 2524391) B2524391
theorem B22196531 : Blo 1120629 22196531 := bstep (se 1 (by rfl) ⟨16647398, by rfl⟩ : syracuseStep 22196531 = 33294797) B33294797
theorem B21870175 : Blo 1120629 21870175 := bstep (se 1 (by rfl) ⟨16402631, by rfl⟩ : syracuseStep 21870175 = 32805263) B32805263
theorem B8533673 : Blo 1120629 8533673 := bstep (se 2 (by rfl) ⟨3200127, by rfl⟩ : syracuseStep 8533673 = 6400255) B6400255
theorem B5684255 : Blo 1120629 5684255 := bstep (se 1 (by rfl) ⟨4263191, by rfl⟩ : syracuseStep 5684255 = 8526383) B8526383
theorem B3948313 : Blo 1120629 3948313 := bstep (se 2 (by rfl) ⟨1480617, by rfl⟩ : syracuseStep 3948313 = 2961235) B2961235
theorem B3785939 : Blo 1120629 3785939 := bstep (se 1 (by rfl) ⟨2839454, by rfl⟩ : syracuseStep 3785939 = 5678909) B5678909
theorem B12961079 : Blo 1120629 12961079 := bstep (se 1 (by rfl) ⟨9720809, by rfl⟩ : syracuseStep 12961079 = 19441619) B19441619
theorem B3786479 : Blo 1120629 3786479 := bstep (se 1 (by rfl) ⟨2839859, by rfl⟩ : syracuseStep 3786479 = 5679719) B5679719
theorem B12142703 : Blo 1120629 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B3164879 : Blo 1120629 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B14371667 : Blo 1120629 14371667 := bstep (se 1 (by rfl) ⟨10778750, by rfl⟩ : syracuseStep 14371667 = 21557501) B21557501
theorem B3787775 : Blo 1120629 3787775 := bstep (se 1 (by rfl) ⟨2840831, by rfl⟩ : syracuseStep 3787775 = 5681663) B5681663
theorem B1264999 : Blo 1120629 1264999 := bstep (se 1 (by rfl) ⟨948749, by rfl⟩ : syracuseStep 1264999 = 1897499) B1897499
theorem B21615011 : Blo 1120629 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B7197599 : Blo 1120629 7197599 := bstep (se 1 (by rfl) ⟨5398199, by rfl⟩ : syracuseStep 7197599 = 10796399) B10796399
theorem B13161923 : Blo 1120629 13161923 := bstep (se 1 (by rfl) ⟨9871442, by rfl⟩ : syracuseStep 13161923 = 19742885) B19742885
theorem B3234923 : Blo 1120629 3234923 := bstep (se 1 (by rfl) ⟨2426192, by rfl⟩ : syracuseStep 3234923 = 4852385) B4852385
theorem B6839423 : Blo 1120629 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B1891775 : Blo 1120629 1891775 := bstep (se 1 (by rfl) ⟨1418831, by rfl⟩ : syracuseStep 1891775 = 2837663) B2837663
theorem B3792635 : Blo 1120629 3792635 := bstep (se 1 (by rfl) ⟨2844476, by rfl⟩ : syracuseStep 3792635 = 5688953) B5688953
theorem B1892855 : Blo 1120629 1892855 := bstep (se 1 (by rfl) ⟨1419641, by rfl⟩ : syracuseStep 1892855 = 2839283) B2839283
theorem B77750927 : Blo 1120629 77750927 := bstep (se 1 (by rfl) ⟨58313195, by rfl⟩ : syracuseStep 77750927 = 116626391) B116626391
theorem B14411033 : Blo 1120629 14411033 := bstep (se 2 (by rfl) ⟨5404137, by rfl⟩ : syracuseStep 14411033 = 10808275) B10808275
theorem B36923531 : Blo 1120629 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B2845439 : Blo 1120629 2845439 := bstep (se 1 (by rfl) ⟨2134079, by rfl⟩ : syracuseStep 2845439 = 4268159) B4268159
theorem B1895771 : Blo 1120629 1895771 := bstep (se 1 (by rfl) ⟨1421828, by rfl⟩ : syracuseStep 1895771 = 2843657) B2843657
theorem B13660447 : Blo 1120629 13660447 := bstep (se 1 (by rfl) ⟨10245335, by rfl⟩ : syracuseStep 13660447 = 20490671) B20490671
theorem B4256297 : Blo 1120629 4256297 := bstep (se 2 (by rfl) ⟨1596111, by rfl⟩ : syracuseStep 4256297 = 3192223) B3192223
theorem B168130241 : Blo 1120629 168130241 := bstep (se 2 (by rfl) ⟨63048840, by rfl⟩ : syracuseStep 168130241 = 126097681) B126097681
theorem B3602195 : Blo 1120629 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B23329721 : Blo 1120629 23329721 := bstep (se 2 (by rfl) ⟨8748645, by rfl⟩ : syracuseStep 23329721 = 17497291) B17497291
theorem B2523959 : Blo 1120629 2523959 := bstep (se 1 (by rfl) ⟨1892969, by rfl⟩ : syracuseStep 2523959 = 3785939) B3785939
theorem B2524319 : Blo 1120629 2524319 := bstep (se 1 (by rfl) ⟨1893239, by rfl⟩ : syracuseStep 2524319 = 3786479) B3786479
theorem B8095135 : Blo 1120629 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B2525183 : Blo 1120629 2525183 := bstep (se 1 (by rfl) ⟨1893887, by rfl⟩ : syracuseStep 2525183 = 3787775) B3787775
theorem B8522009 : Blo 1120629 8522009 := bstep (se 2 (by rfl) ⟨3195753, by rfl⟩ : syracuseStep 8522009 = 6391507) B6391507
theorem B4559615 : Blo 1120629 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B2528423 : Blo 1120629 2528423 := bstep (se 1 (by rfl) ⟨1896317, by rfl⟩ : syracuseStep 2528423 = 3792635) B3792635
theorem B9607355 : Blo 1120629 9607355 := bstep (se 1 (by rfl) ⟨7205516, by rfl⟩ : syracuseStep 9607355 = 14411033) B14411033
theorem B1121951 : Blo 1120629 1121951 := bstep (se 1 (by rfl) ⟨841463, by rfl⟩ : syracuseStep 1121951 = 1682927) B1682927
theorem B2401463 : Blo 1120629 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B34515679 : Blo 1120629 34515679 := bstep (se 1 (by rfl) ⟨25886759, by rfl⟩ : syracuseStep 34515679 = 51773519) B51773519
theorem B5680367 : Blo 1120629 5680367 := bstep (se 1 (by rfl) ⟨4260275, by rfl⟩ : syracuseStep 5680367 = 8520551) B8520551
theorem B9581111 : Blo 1120629 9581111 := bstep (se 1 (by rfl) ⟨7185833, by rfl⟩ : syracuseStep 9581111 = 14371667) B14371667
theorem B4798399 : Blo 1120629 4798399 := bstep (se 1 (by rfl) ⟨3598799, by rfl⟩ : syracuseStep 4798399 = 7197599) B7197599
theorem B1686665 : Blo 1120629 1686665 := bstep (se 2 (by rfl) ⟨632499, by rfl⟩ : syracuseStep 1686665 = 1264999) B1264999
theorem B1261183 : Blo 1120629 1261183 := bstep (se 1 (by rfl) ⟨945887, by rfl⟩ : syracuseStep 1261183 = 1891775) B1891775
theorem B1261903 : Blo 1120629 1261903 := bstep (se 1 (by rfl) ⟨946427, by rfl⟩ : syracuseStep 1261903 = 1892855) B1892855
theorem B1622911 : Blo 1120629 1622911 := bstep (se 1 (by rfl) ⟨1217183, by rfl⟩ : syracuseStep 1622911 = 2434367) B2434367
theorem B8439677 : Blo 1120629 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B4048811 : Blo 1120629 4048811 := bstep (se 1 (by rfl) ⟨3036608, by rfl⟩ : syracuseStep 4048811 = 6073217) B6073217
theorem B1263847 : Blo 1120629 1263847 := bstep (se 1 (by rfl) ⟨947885, by rfl⟩ : syracuseStep 1263847 = 1895771) B1895771
theorem B14797687 : Blo 1120629 14797687 := bstep (se 1 (by rfl) ⟨11098265, by rfl⟩ : syracuseStep 14797687 = 22196531) B22196531
theorem B2837531 : Blo 1120629 2837531 := bstep (se 1 (by rfl) ⟨2128148, by rfl⟩ : syracuseStep 2837531 = 4256297) B4256297
theorem B5689115 : Blo 1120629 5689115 := bstep (se 1 (by rfl) ⟨4266836, by rfl⟩ : syracuseStep 5689115 = 8533673) B8533673
theorem B112086827 : Blo 1120629 112086827 := bstep (se 1 (by rfl) ⟨84065120, by rfl⟩ : syracuseStep 112086827 = 168130241) B168130241
theorem B15553147 : Blo 1120629 15553147 := bstep (se 1 (by rfl) ⟨11664860, by rfl⟩ : syracuseStep 15553147 = 23329721) B23329721
theorem B3789503 : Blo 1120629 3789503 := bstep (se 1 (by rfl) ⟨2842127, by rfl⟩ : syracuseStep 3789503 = 5684255) B5684255
theorem B5264417 : Blo 1120629 5264417 := bstep (se 2 (by rfl) ⟨1974156, by rfl⟩ : syracuseStep 5264417 = 3948313) B3948313
theorem B8640719 : Blo 1120629 8640719 := bstep (se 1 (by rfl) ⟨6480539, by rfl⟩ : syracuseStep 8640719 = 12961079) B12961079
theorem B4545017 : Blo 1120629 4545017 := bstep (se 2 (by rfl) ⟨1704381, by rfl⟩ : syracuseStep 4545017 = 3408763) B3408763
theorem B14410007 : Blo 1120629 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B8774615 : Blo 1120629 8774615 := bstep (se 1 (by rfl) ⟨6580961, by rfl⟩ : syracuseStep 8774615 = 13161923) B13161923
theorem B2844143 : Blo 1120629 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B2156615 : Blo 1120629 2156615 := bstep (se 1 (by rfl) ⟨1617461, by rfl⟩ : syracuseStep 2156615 = 3234923) B3234923
theorem B98462749 : Blo 1120629 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B18213929 : Blo 1120629 18213929 := bstep (se 2 (by rfl) ⟨6830223, by rfl⟩ : syracuseStep 18213929 = 13660447) B13660447
theorem B51833951 : Blo 1120629 51833951 := bstep (se 1 (by rfl) ⟨38875463, by rfl⟩ : syracuseStep 51833951 = 77750927) B77750927
theorem B1896959 : Blo 1120629 1896959 := bstep (se 1 (by rfl) ⟨1422719, by rfl⟩ : syracuseStep 1896959 = 2845439) B2845439
theorem B29160233 : Blo 1120629 29160233 := bstep (se 2 (by rfl) ⟨10935087, by rfl⟩ : syracuseStep 29160233 = 21870175) B21870175
theorem B77689691 : Blo 1120629 77689691 := bstep (se 1 (by rfl) ⟨58267268, by rfl⟩ : syracuseStep 77689691 = 116534537) B116534537
theorem B2163881 : Blo 1120629 2163881 := bstep (se 2 (by rfl) ⟨811455, by rfl⟩ : syracuseStep 2163881 = 1622911) B1622911
theorem B2526335 : Blo 1120629 2526335 := bstep (se 1 (by rfl) ⟨1894751, by rfl⟩ : syracuseStep 2526335 = 3789503) B3789503
theorem B3509611 : Blo 1120629 3509611 := bstep (se 1 (by rfl) ⟨2632208, by rfl⟩ : syracuseStep 3509611 = 5264417) B5264417
theorem B19730249 : Blo 1120629 19730249 := bstep (se 2 (by rfl) ⟨7398843, by rfl⟩ : syracuseStep 19730249 = 14797687) B14797687
theorem B9606671 : Blo 1120629 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B6397865 : Blo 1120629 6397865 := bstep (se 2 (by rfl) ⟨2399199, by rfl⟩ : syracuseStep 6397865 = 4798399) B4798399
theorem B19440155 : Blo 1120629 19440155 := bstep (se 1 (by rfl) ⟨14580116, by rfl⟩ : syracuseStep 19440155 = 29160233) B29160233
theorem B1124443 : Blo 1120629 1124443 := bstep (se 1 (by rfl) ⟨843332, by rfl⟩ : syracuseStep 1124443 = 1686665) B1686665
theorem B1681577 : Blo 1120629 1681577 := bstep (se 2 (by rfl) ⟨630591, by rfl⟩ : syracuseStep 1681577 = 1261183) B1261183
theorem B1682537 : Blo 1120629 1682537 := bstep (se 2 (by rfl) ⟨630951, by rfl⟩ : syracuseStep 1682537 = 1261903) B1261903
theorem B1682639 : Blo 1120629 1682639 := bstep (se 1 (by rfl) ⟨1261979, by rfl⟩ : syracuseStep 1682639 = 2523959) B2523959
theorem B1682879 : Blo 1120629 1682879 := bstep (se 1 (by rfl) ⟨1262159, by rfl⟩ : syracuseStep 1682879 = 2524319) B2524319
theorem B2699207 : Blo 1120629 2699207 := bstep (se 1 (by rfl) ⟨2024405, by rfl⟩ : syracuseStep 2699207 = 4048811) B4048811
theorem B1683455 : Blo 1120629 1683455 := bstep (se 1 (by rfl) ⟨1262591, by rfl⟩ : syracuseStep 1683455 = 2525183) B2525183
theorem B5681339 : Blo 1120629 5681339 := bstep (se 1 (by rfl) ⟨4261004, by rfl⟩ : syracuseStep 5681339 = 8522009) B8522009
theorem B10793513 : Blo 1120629 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B74724551 : Blo 1120629 74724551 := bstep (se 1 (by rfl) ⟨56043413, by rfl⟩ : syracuseStep 74724551 = 112086827) B112086827
theorem B1685129 : Blo 1120629 1685129 := bstep (se 2 (by rfl) ⟨631923, by rfl⟩ : syracuseStep 1685129 = 1263847) B1263847
theorem B1685615 : Blo 1120629 1685615 := bstep (se 1 (by rfl) ⟨1264211, by rfl⟩ : syracuseStep 1685615 = 2528423) B2528423
theorem B46020905 : Blo 1120629 46020905 := bstep (se 2 (by rfl) ⟨17257839, by rfl⟩ : syracuseStep 46020905 = 34515679) B34515679
theorem B131283665 : Blo 1120629 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B6404903 : Blo 1120629 6404903 := bstep (se 1 (by rfl) ⟨4803677, by rfl⟩ : syracuseStep 6404903 = 9607355) B9607355
theorem B3030011 : Blo 1120629 3030011 := bstep (se 1 (by rfl) ⟨2272508, by rfl⟩ : syracuseStep 3030011 = 4545017) B4545017
theorem B5849743 : Blo 1120629 5849743 := bstep (se 1 (by rfl) ⟨4387307, by rfl⟩ : syracuseStep 5849743 = 8774615) B8774615
theorem B12142619 : Blo 1120629 12142619 := bstep (se 1 (by rfl) ⟨9106964, by rfl⟩ : syracuseStep 12142619 = 18213929) B18213929
theorem B34555967 : Blo 1120629 34555967 := bstep (se 1 (by rfl) ⟨25916975, by rfl⟩ : syracuseStep 34555967 = 51833951) B51833951
theorem B3786911 : Blo 1120629 3786911 := bstep (se 1 (by rfl) ⟨2840183, by rfl⟩ : syracuseStep 3786911 = 5680367) B5680367
theorem B1264639 : Blo 1120629 1264639 := bstep (se 1 (by rfl) ⟨948479, by rfl⟩ : syracuseStep 1264639 = 1896959) B1896959
theorem B51793127 : Blo 1120629 51793127 := bstep (se 1 (by rfl) ⟨38844845, by rfl⟩ : syracuseStep 51793127 = 77689691) B77689691
theorem B5626451 : Blo 1120629 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B1891687 : Blo 1120629 1891687 := bstep (se 1 (by rfl) ⟨1418765, by rfl⟩ : syracuseStep 1891687 = 2837531) B2837531
theorem B3792743 : Blo 1120629 3792743 := bstep (se 1 (by rfl) ⟨2844557, by rfl⟩ : syracuseStep 3792743 = 5689115) B5689115
theorem B3039743 : Blo 1120629 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B5760479 : Blo 1120629 5760479 := bstep (se 1 (by rfl) ⟨4320359, by rfl⟩ : syracuseStep 5760479 = 8640719) B8640719
theorem B1600975 : Blo 1120629 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B20737529 : Blo 1120629 20737529 := bstep (se 2 (by rfl) ⟨7776573, by rfl⟩ : syracuseStep 20737529 = 15553147) B15553147
theorem B1896095 : Blo 1120629 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B1437743 : Blo 1120629 1437743 := bstep (se 1 (by rfl) ⟨1078307, by rfl⟩ : syracuseStep 1437743 = 2156615) B2156615
theorem B6387407 : Blo 1120629 6387407 := bstep (se 1 (by rfl) ⟨4790555, by rfl⟩ : syracuseStep 6387407 = 9581111) B9581111
theorem B3833981 : Blo 1120629 3833981 := bstep (se 3 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 3833981 = 1437743) B1437743
theorem B7799657 : Blo 1120629 7799657 := bstep (se 2 (by rfl) ⟨2924871, by rfl⟩ : syracuseStep 7799657 = 5849743) B5849743
theorem B8095079 : Blo 1120629 8095079 := bstep (se 1 (by rfl) ⟨6071309, by rfl⟩ : syracuseStep 8095079 = 12142619) B12142619
theorem B23037311 : Blo 1120629 23037311 := bstep (se 1 (by rfl) ⟨17277983, by rfl⟩ : syracuseStep 23037311 = 34555967) B34555967
theorem B2524607 : Blo 1120629 2524607 := bstep (se 1 (by rfl) ⟨1893455, by rfl⟩ : syracuseStep 2524607 = 3786911) B3786911
theorem B5770349 : Blo 1120629 5770349 := bstep (se 3 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 5770349 = 2163881) B2163881
theorem B2528495 : Blo 1120629 2528495 := bstep (se 1 (by rfl) ⟨1896371, by rfl⟩ : syracuseStep 2528495 = 3792743) B3792743
theorem B4265243 : Blo 1120629 4265243 := bstep (se 1 (by rfl) ⟨3198932, by rfl⟩ : syracuseStep 4265243 = 6397865) B6397865
theorem B3840319 : Blo 1120629 3840319 := bstep (se 1 (by rfl) ⟨2880239, by rfl⟩ : syracuseStep 3840319 = 5760479) B5760479
theorem B1121051 : Blo 1120629 1121051 := bstep (se 1 (by rfl) ⟨840788, by rfl⟩ : syracuseStep 1121051 = 1681577) B1681577
theorem B18717925 : Blo 1120629 18717925 := bstep (se 4 (by rfl) ⟨1754805, by rfl⟩ : syracuseStep 18717925 = 3509611) B3509611
theorem B1121691 : Blo 1120629 1121691 := bstep (se 1 (by rfl) ⟨841268, by rfl⟩ : syracuseStep 1121691 = 1682537) B1682537
theorem B1121759 : Blo 1120629 1121759 := bstep (se 1 (by rfl) ⟨841319, by rfl⟩ : syracuseStep 1121759 = 1682639) B1682639
theorem B1121919 : Blo 1120629 1121919 := bstep (se 1 (by rfl) ⟨841439, by rfl⟩ : syracuseStep 1121919 = 1682879) B1682879
theorem B1122303 : Blo 1120629 1122303 := bstep (se 1 (by rfl) ⟨841727, by rfl⟩ : syracuseStep 1122303 = 1683455) B1683455
theorem B49816367 : Blo 1120629 49816367 := bstep (se 1 (by rfl) ⟨37362275, by rfl⟩ : syracuseStep 49816367 = 74724551) B74724551
theorem B1123419 : Blo 1120629 1123419 := bstep (se 1 (by rfl) ⟨842564, by rfl⟩ : syracuseStep 1123419 = 1685129) B1685129
theorem B1123743 : Blo 1120629 1123743 := bstep (se 1 (by rfl) ⟨842807, by rfl⟩ : syracuseStep 1123743 = 1685615) B1685615
theorem B30680603 : Blo 1120629 30680603 := bstep (se 1 (by rfl) ⟨23010452, by rfl⟩ : syracuseStep 30680603 = 46020905) B46020905
theorem B4269935 : Blo 1120629 4269935 := bstep (se 1 (by rfl) ⟨3202451, by rfl⟩ : syracuseStep 4269935 = 6404903) B6404903
theorem B1684223 : Blo 1120629 1684223 := bstep (se 1 (by rfl) ⟨1263167, by rfl⟩ : syracuseStep 1684223 = 2526335) B2526335
theorem B13153499 : Blo 1120629 13153499 := bstep (se 1 (by rfl) ⟨9865124, by rfl⟩ : syracuseStep 13153499 = 19730249) B19730249
theorem B6404447 : Blo 1120629 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B1686185 : Blo 1120629 1686185 := bstep (se 2 (by rfl) ⟨632319, by rfl⟩ : syracuseStep 1686185 = 1264639) B1264639
theorem B3750967 : Blo 1120629 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B12960103 : Blo 1120629 12960103 := bstep (se 1 (by rfl) ⟨9720077, by rfl⟩ : syracuseStep 12960103 = 19440155) B19440155
theorem B8538533 : Blo 1120629 8538533 := bstep (se 4 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 8538533 = 1600975) B1600975
theorem B1264063 : Blo 1120629 1264063 := bstep (se 1 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 1264063 = 1896095) B1896095
theorem B3787559 : Blo 1120629 3787559 := bstep (se 1 (by rfl) ⟨2840669, by rfl⟩ : syracuseStep 3787559 = 5681339) B5681339
theorem B7195675 : Blo 1120629 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B2020007 : Blo 1120629 2020007 := bstep (se 1 (by rfl) ⟨1515005, by rfl⟩ : syracuseStep 2020007 = 3030011) B3030011
theorem B34528751 : Blo 1120629 34528751 := bstep (se 1 (by rfl) ⟨25896563, by rfl⟩ : syracuseStep 34528751 = 51793127) B51793127
theorem B2026495 : Blo 1120629 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B13825019 : Blo 1120629 13825019 := bstep (se 1 (by rfl) ⟨10368764, by rfl⟩ : syracuseStep 13825019 = 20737529) B20737529
theorem B1799471 : Blo 1120629 1799471 := bstep (se 1 (by rfl) ⟨1349603, by rfl⟩ : syracuseStep 1799471 = 2699207) B2699207
theorem B4258271 : Blo 1120629 4258271 := bstep (se 1 (by rfl) ⟨3193703, by rfl⟩ : syracuseStep 4258271 = 6387407) B6387407
theorem B2522249 : Blo 1120629 2522249 := bstep (se 2 (by rfl) ⟨945843, by rfl⟩ : syracuseStep 2522249 = 1891687) B1891687
theorem B87522443 : Blo 1120629 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B2555987 : Blo 1120629 2555987 := bstep (se 1 (by rfl) ⟨1916990, by rfl⟩ : syracuseStep 2555987 = 3833981) B3833981
theorem B2525039 : Blo 1120629 2525039 := bstep (se 1 (by rfl) ⟨1893779, by rfl⟩ : syracuseStep 2525039 = 3787559) B3787559
theorem B1346671 : Blo 1120629 1346671 := bstep (se 1 (by rfl) ⟨1010003, by rfl⟩ : syracuseStep 1346671 = 2020007) B2020007
theorem B20453735 : Blo 1120629 20453735 := bstep (se 1 (by rfl) ⟨15340301, by rfl⟩ : syracuseStep 20453735 = 30680603) B30680603
theorem B5120425 : Blo 1120629 5120425 := bstep (se 2 (by rfl) ⟨1920159, by rfl⟩ : syracuseStep 5120425 = 3840319) B3840319
theorem B1122815 : Blo 1120629 1122815 := bstep (se 1 (by rfl) ⟨842111, by rfl⟩ : syracuseStep 1122815 = 1684223) B1684223
theorem B9216679 : Blo 1120629 9216679 := bstep (se 1 (by rfl) ⟨6912509, by rfl⟩ : syracuseStep 9216679 = 13825019) B13825019
theorem B4269631 : Blo 1120629 4269631 := bstep (se 1 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 4269631 = 6404447) B6404447
theorem B1124123 : Blo 1120629 1124123 := bstep (se 1 (by rfl) ⟨843092, by rfl⟩ : syracuseStep 1124123 = 1686185) B1686185
theorem B1681499 : Blo 1120629 1681499 := bstep (se 1 (by rfl) ⟨1261124, by rfl⟩ : syracuseStep 1681499 = 2522249) B2522249
theorem B17280137 : Blo 1120629 17280137 := bstep (se 2 (by rfl) ⟨6480051, by rfl⟩ : syracuseStep 17280137 = 12960103) B12960103
theorem B1683071 : Blo 1120629 1683071 := bstep (se 1 (by rfl) ⟨1262303, by rfl⟩ : syracuseStep 1683071 = 2524607) B2524607
theorem B3846899 : Blo 1120629 3846899 := bstep (se 1 (by rfl) ⟨2885174, by rfl⟩ : syracuseStep 3846899 = 5770349) B5770349
theorem B1685417 : Blo 1120629 1685417 := bstep (se 2 (by rfl) ⟨632031, by rfl⟩ : syracuseStep 1685417 = 1264063) B1264063
theorem B1685663 : Blo 1120629 1685663 := bstep (se 1 (by rfl) ⟨1264247, by rfl⟩ : syracuseStep 1685663 = 2528495) B2528495
theorem B2701993 : Blo 1120629 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B23019167 : Blo 1120629 23019167 := bstep (se 1 (by rfl) ⟨17264375, by rfl⟩ : syracuseStep 23019167 = 34528751) B34528751
theorem B20005157 : Blo 1120629 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B33210911 : Blo 1120629 33210911 := bstep (se 1 (by rfl) ⟨24908183, by rfl⟩ : syracuseStep 33210911 = 49816367) B49816367
theorem B8768999 : Blo 1120629 8768999 := bstep (se 1 (by rfl) ⟨6576749, by rfl⟩ : syracuseStep 8768999 = 13153499) B13153499
theorem B1199647 : Blo 1120629 1199647 := bstep (se 1 (by rfl) ⟨899735, by rfl⟩ : syracuseStep 1199647 = 1799471) B1799471
theorem B24957233 : Blo 1120629 24957233 := bstep (se 2 (by rfl) ⟨9358962, by rfl⟩ : syracuseStep 24957233 = 18717925) B18717925
theorem B2838847 : Blo 1120629 2838847 := bstep (se 1 (by rfl) ⟨2129135, by rfl⟩ : syracuseStep 2838847 = 4258271) B4258271
theorem B58348295 : Blo 1120629 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B5396719 : Blo 1120629 5396719 := bstep (se 1 (by rfl) ⟨4047539, by rfl⟩ : syracuseStep 5396719 = 8095079) B8095079
theorem B5692355 : Blo 1120629 5692355 := bstep (se 1 (by rfl) ⟨4269266, by rfl⟩ : syracuseStep 5692355 = 8538533) B8538533
theorem B2843495 : Blo 1120629 2843495 := bstep (se 1 (by rfl) ⟨2132621, by rfl⟩ : syracuseStep 2843495 = 4265243) B4265243
theorem B61432829 : Blo 1120629 61432829 := bstep (se 3 (by rfl) ⟨11518655, by rfl⟩ : syracuseStep 61432829 = 23037311) B23037311
theorem B9594233 : Blo 1120629 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B2846623 : Blo 1120629 2846623 := bstep (se 1 (by rfl) ⟨2134967, by rfl⟩ : syracuseStep 2846623 = 4269935) B4269935
theorem B83196341 : Blo 1120629 83196341 := bstep (se 5 (by rfl) ⟨3899828, by rfl⟩ : syracuseStep 83196341 = 7799657) B7799657
theorem B13336771 : Blo 1120629 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B27263861 : Blo 1120629 27263861 := bstep (se 5 (by rfl) ⟨1277993, by rfl⟩ : syracuseStep 27263861 = 2555987) B2555987
theorem B12288905 : Blo 1120629 12288905 := bstep (se 2 (by rfl) ⟨4608339, by rfl⟩ : syracuseStep 12288905 = 9216679) B9216679
theorem B10258397 : Blo 1120629 10258397 := bstep (se 3 (by rfl) ⟨1923449, by rfl⟩ : syracuseStep 10258397 = 3846899) B3846899
theorem B38898863 : Blo 1120629 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B13635823 : Blo 1120629 13635823 := bstep (se 1 (by rfl) ⟨10226867, by rfl⟩ : syracuseStep 13635823 = 20453735) B20453735
theorem B7182245 : Blo 1120629 7182245 := bstep (se 4 (by rfl) ⟨673335, by rfl⟩ : syracuseStep 7182245 = 1346671) B1346671
theorem B6396155 : Blo 1120629 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B1120999 : Blo 1120629 1120999 := bstep (se 1 (by rfl) ⟨840749, by rfl⟩ : syracuseStep 1120999 = 1681499) B1681499
theorem B1122047 : Blo 1120629 1122047 := bstep (se 1 (by rfl) ⟨841535, by rfl⟩ : syracuseStep 1122047 = 1683071) B1683071
theorem B1123611 : Blo 1120629 1123611 := bstep (se 1 (by rfl) ⟨842708, by rfl⟩ : syracuseStep 1123611 = 1685417) B1685417
theorem B1123775 : Blo 1120629 1123775 := bstep (se 1 (by rfl) ⟨842831, by rfl⟩ : syracuseStep 1123775 = 1685663) B1685663
theorem B15346111 : Blo 1120629 15346111 := bstep (se 1 (by rfl) ⟨11509583, by rfl⟩ : syracuseStep 15346111 = 23019167) B23019167
theorem B1683359 : Blo 1120629 1683359 := bstep (se 1 (by rfl) ⟨1262519, by rfl⟩ : syracuseStep 1683359 = 2525039) B2525039
theorem B27308933 : Blo 1120629 27308933 := bstep (se 4 (by rfl) ⟨2560212, by rfl⟩ : syracuseStep 27308933 = 5120425) B5120425
theorem B3785129 : Blo 1120629 3785129 := bstep (se 2 (by rfl) ⟨1419423, by rfl⟩ : syracuseStep 3785129 = 2838847) B2838847
theorem B11520091 : Blo 1120629 11520091 := bstep (se 1 (by rfl) ⟨8640068, by rfl⟩ : syracuseStep 11520091 = 17280137) B17280137
theorem B7195625 : Blo 1120629 7195625 := bstep (se 2 (by rfl) ⟨2698359, by rfl⟩ : syracuseStep 7195625 = 5396719) B5396719
theorem B23383997 : Blo 1120629 23383997 := bstep (se 3 (by rfl) ⟨4384499, by rfl⟩ : syracuseStep 23383997 = 8768999) B8768999
theorem B55464227 : Blo 1120629 55464227 := bstep (se 1 (by rfl) ⟨41598170, by rfl⟩ : syracuseStep 55464227 = 83196341) B83196341
theorem B88562429 : Blo 1120629 88562429 := bstep (se 3 (by rfl) ⟨16605455, by rfl⟩ : syracuseStep 88562429 = 33210911) B33210911
theorem B5692841 : Blo 1120629 5692841 := bstep (se 2 (by rfl) ⟨2134815, by rfl⟩ : syracuseStep 5692841 = 4269631) B4269631
theorem B16638155 : Blo 1120629 16638155 := bstep (se 1 (by rfl) ⟨12478616, by rfl⟩ : syracuseStep 16638155 = 24957233) B24957233
theorem B3794903 : Blo 1120629 3794903 := bstep (se 1 (by rfl) ⟨2846177, by rfl⟩ : syracuseStep 3794903 = 5692355) B5692355
theorem B1599529 : Blo 1120629 1599529 := bstep (se 2 (by rfl) ⟨599823, by rfl⟩ : syracuseStep 1599529 = 1199647) B1199647
theorem B3795497 : Blo 1120629 3795497 := bstep (se 2 (by rfl) ⟨1423311, by rfl⟩ : syracuseStep 3795497 = 2846623) B2846623
theorem B1895663 : Blo 1120629 1895663 := bstep (se 1 (by rfl) ⟨1421747, by rfl⟩ : syracuseStep 1895663 = 2843495) B2843495
theorem B40955219 : Blo 1120629 40955219 := bstep (se 1 (by rfl) ⟨30716414, by rfl⟩ : syracuseStep 40955219 = 61432829) B61432829
theorem B3602657 : Blo 1120629 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B2523419 : Blo 1120629 2523419 := bstep (se 1 (by rfl) ⟨1892564, by rfl⟩ : syracuseStep 2523419 = 3785129) B3785129
theorem B8192603 : Blo 1120629 8192603 := bstep (se 1 (by rfl) ⟨6144452, by rfl⟩ : syracuseStep 8192603 = 12288905) B12288905
theorem B2132705 : Blo 1120629 2132705 := bstep (se 2 (by rfl) ⟨799764, by rfl⟩ : syracuseStep 2132705 = 1599529) B1599529
theorem B4788163 : Blo 1120629 4788163 := bstep (se 1 (by rfl) ⟨3591122, by rfl⟩ : syracuseStep 4788163 = 7182245) B7182245
theorem B4264103 : Blo 1120629 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B2529935 : Blo 1120629 2529935 := bstep (se 1 (by rfl) ⟨1897451, by rfl⟩ : syracuseStep 2529935 = 3794903) B3794903
theorem B2530331 : Blo 1120629 2530331 := bstep (se 1 (by rfl) ⟨1897748, by rfl⟩ : syracuseStep 2530331 = 3795497) B3795497
theorem B27303479 : Blo 1120629 27303479 := bstep (se 1 (by rfl) ⟨20477609, by rfl⟩ : syracuseStep 27303479 = 40955219) B40955219
theorem B1122239 : Blo 1120629 1122239 := bstep (se 1 (by rfl) ⟨841679, by rfl⟩ : syracuseStep 1122239 = 1683359) B1683359
theorem B2401771 : Blo 1120629 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B4797083 : Blo 1120629 4797083 := bstep (se 1 (by rfl) ⟨3597812, by rfl⟩ : syracuseStep 4797083 = 7195625) B7195625
theorem B25932575 : Blo 1120629 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B36976151 : Blo 1120629 36976151 := bstep (se 1 (by rfl) ⟨27732113, by rfl⟩ : syracuseStep 36976151 = 55464227) B55464227
theorem B20461481 : Blo 1120629 20461481 := bstep (se 2 (by rfl) ⟨7673055, by rfl⟩ : syracuseStep 20461481 = 15346111) B15346111
theorem B11092103 : Blo 1120629 11092103 := bstep (se 1 (by rfl) ⟨8319077, by rfl⟩ : syracuseStep 11092103 = 16638155) B16638155
theorem B1263775 : Blo 1120629 1263775 := bstep (se 1 (by rfl) ⟨947831, by rfl⟩ : syracuseStep 1263775 = 1895663) B1895663
theorem B18205955 : Blo 1120629 18205955 := bstep (se 1 (by rfl) ⟨13654466, by rfl⟩ : syracuseStep 18205955 = 27308933) B27308933
theorem B17782361 : Blo 1120629 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B18175907 : Blo 1120629 18175907 := bstep (se 1 (by rfl) ⟨13631930, by rfl⟩ : syracuseStep 18175907 = 27263861) B27263861
theorem B6838931 : Blo 1120629 6838931 := bstep (se 1 (by rfl) ⟨5129198, by rfl⟩ : syracuseStep 6838931 = 10258397) B10258397
theorem B15589331 : Blo 1120629 15589331 := bstep (se 1 (by rfl) ⟨11691998, by rfl⟩ : syracuseStep 15589331 = 23383997) B23383997
theorem B15360121 : Blo 1120629 15360121 := bstep (se 2 (by rfl) ⟨5760045, by rfl⟩ : syracuseStep 15360121 = 11520091) B11520091
theorem B59041619 : Blo 1120629 59041619 := bstep (se 1 (by rfl) ⟨44281214, by rfl⟩ : syracuseStep 59041619 = 88562429) B88562429
theorem B3795227 : Blo 1120629 3795227 := bstep (se 1 (by rfl) ⟨2846420, by rfl⟩ : syracuseStep 3795227 = 5692841) B5692841
theorem B18181097 : Blo 1120629 18181097 := bstep (se 2 (by rfl) ⟨6817911, by rfl⟩ : syracuseStep 18181097 = 13635823) B13635823
theorem B81920645 : Blo 1120629 81920645 := bstep (se 4 (by rfl) ⟨7680060, by rfl⟩ : syracuseStep 81920645 = 15360121) B15360121
theorem B10392887 : Blo 1120629 10392887 := bstep (se 1 (by rfl) ⟨7794665, by rfl⟩ : syracuseStep 10392887 = 15589331) B15589331
theorem B39361079 : Blo 1120629 39361079 := bstep (se 1 (by rfl) ⟨29520809, by rfl⟩ : syracuseStep 39361079 = 59041619) B59041619
theorem B2530151 : Blo 1120629 2530151 := bstep (se 1 (by rfl) ⟨1897613, by rfl⟩ : syracuseStep 2530151 = 3795227) B3795227
theorem B24650767 : Blo 1120629 24650767 := bstep (se 1 (by rfl) ⟨18488075, by rfl⟩ : syracuseStep 24650767 = 36976151) B36976151
theorem B13640987 : Blo 1120629 13640987 := bstep (se 1 (by rfl) ⟨10230740, by rfl⟩ : syracuseStep 13640987 = 20461481) B20461481
theorem B1682279 : Blo 1120629 1682279 := bstep (se 1 (by rfl) ⟨1261709, by rfl⟩ : syracuseStep 1682279 = 2523419) B2523419
theorem B1421803 : Blo 1120629 1421803 := bstep (se 1 (by rfl) ⟨1066352, by rfl⟩ : syracuseStep 1421803 = 2132705) B2132705
theorem B69153533 : Blo 1120629 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B12137303 : Blo 1120629 12137303 := bstep (se 1 (by rfl) ⟨9102977, by rfl⟩ : syracuseStep 12137303 = 18205955) B18205955
theorem B1685033 : Blo 1120629 1685033 := bstep (se 2 (by rfl) ⟨631887, by rfl⟩ : syracuseStep 1685033 = 1263775) B1263775
theorem B1686623 : Blo 1120629 1686623 := bstep (se 1 (by rfl) ⟨1264967, by rfl⟩ : syracuseStep 1686623 = 2529935) B2529935
theorem B1686887 : Blo 1120629 1686887 := bstep (se 1 (by rfl) ⟨1265165, by rfl⟩ : syracuseStep 1686887 = 2530331) B2530331
theorem B18202319 : Blo 1120629 18202319 := bstep (se 1 (by rfl) ⟨13651739, by rfl⟩ : syracuseStep 18202319 = 27303479) B27303479
theorem B18237149 : Blo 1120629 18237149 := bstep (se 3 (by rfl) ⟨3419465, by rfl⟩ : syracuseStep 18237149 = 6838931) B6838931
theorem B3198055 : Blo 1120629 3198055 := bstep (se 1 (by rfl) ⟨2398541, by rfl⟩ : syracuseStep 3198055 = 4797083) B4797083
theorem B7394735 : Blo 1120629 7394735 := bstep (se 1 (by rfl) ⟨5546051, by rfl⟩ : syracuseStep 7394735 = 11092103) B11092103
theorem B5461735 : Blo 1120629 5461735 := bstep (se 1 (by rfl) ⟨4096301, by rfl⟩ : syracuseStep 5461735 = 8192603) B8192603
theorem B3202361 : Blo 1120629 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B2842735 : Blo 1120629 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B11854907 : Blo 1120629 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B12117271 : Blo 1120629 12117271 := bstep (se 1 (by rfl) ⟨9087953, by rfl⟩ : syracuseStep 12117271 = 18175907) B18175907
theorem B6384217 : Blo 1120629 6384217 := bstep (se 2 (by rfl) ⟨2394081, by rfl⟩ : syracuseStep 6384217 = 4788163) B4788163
theorem B12120731 : Blo 1120629 12120731 := bstep (se 1 (by rfl) ⟨9090548, by rfl⟩ : syracuseStep 12120731 = 18181097) B18181097
theorem B12158099 : Blo 1120629 12158099 := bstep (se 1 (by rfl) ⟨9118574, by rfl⟩ : syracuseStep 12158099 = 18237149) B18237149
theorem B32867689 : Blo 1120629 32867689 := bstep (se 2 (by rfl) ⟨12325383, by rfl⟩ : syracuseStep 32867689 = 24650767) B24650767
theorem B16156361 : Blo 1120629 16156361 := bstep (se 2 (by rfl) ⟨6058635, by rfl⟩ : syracuseStep 16156361 = 12117271) B12117271
theorem B4264073 : Blo 1120629 4264073 := bstep (se 2 (by rfl) ⟨1599027, by rfl⟩ : syracuseStep 4264073 = 3198055) B3198055
theorem B2134907 : Blo 1120629 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B7903271 : Blo 1120629 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B1121519 : Blo 1120629 1121519 := bstep (se 1 (by rfl) ⟨841139, by rfl⟩ : syracuseStep 1121519 = 1682279) B1682279
theorem B7282313 : Blo 1120629 7282313 := bstep (se 2 (by rfl) ⟨2730867, by rfl⟩ : syracuseStep 7282313 = 5461735) B5461735
theorem B1123355 : Blo 1120629 1123355 := bstep (se 1 (by rfl) ⟨842516, by rfl⟩ : syracuseStep 1123355 = 1685033) B1685033
theorem B1124415 : Blo 1120629 1124415 := bstep (se 1 (by rfl) ⟨843311, by rfl⟩ : syracuseStep 1124415 = 1686623) B1686623
theorem B1124591 : Blo 1120629 1124591 := bstep (se 1 (by rfl) ⟨843443, by rfl⟩ : syracuseStep 1124591 = 1686887) B1686887
theorem B12134879 : Blo 1120629 12134879 := bstep (se 1 (by rfl) ⟨9101159, by rfl⟩ : syracuseStep 12134879 = 18202319) B18202319
theorem B6928591 : Blo 1120629 6928591 := bstep (se 1 (by rfl) ⟨5196443, by rfl⟩ : syracuseStep 6928591 = 10392887) B10392887
theorem B4929823 : Blo 1120629 4929823 := bstep (se 1 (by rfl) ⟨3697367, by rfl⟩ : syracuseStep 4929823 = 7394735) B7394735
theorem B1686767 : Blo 1120629 1686767 := bstep (se 1 (by rfl) ⟨1265075, by rfl⟩ : syracuseStep 1686767 = 2530151) B2530151
theorem B9093991 : Blo 1120629 9093991 := bstep (se 1 (by rfl) ⟨6820493, by rfl⟩ : syracuseStep 9093991 = 13640987) B13640987
theorem B8080487 : Blo 1120629 8080487 := bstep (se 1 (by rfl) ⟨6060365, by rfl⟩ : syracuseStep 8080487 = 12120731) B12120731
theorem B3790313 : Blo 1120629 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B54613763 : Blo 1120629 54613763 := bstep (se 1 (by rfl) ⟨40960322, by rfl⟩ : syracuseStep 54613763 = 81920645) B81920645
theorem B8512289 : Blo 1120629 8512289 := bstep (se 2 (by rfl) ⟨3192108, by rfl⟩ : syracuseStep 8512289 = 6384217) B6384217
theorem B26240719 : Blo 1120629 26240719 := bstep (se 1 (by rfl) ⟨19680539, by rfl⟩ : syracuseStep 26240719 = 39361079) B39361079
theorem B1895737 : Blo 1120629 1895737 := bstep (se 2 (by rfl) ⟨710901, by rfl⟩ : syracuseStep 1895737 = 1421803) B1421803
theorem B46102355 : Blo 1120629 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B8091535 : Blo 1120629 8091535 := bstep (se 1 (by rfl) ⟨6068651, by rfl⟩ : syracuseStep 8091535 = 12137303) B12137303
theorem B12125321 : Blo 1120629 12125321 := bstep (se 2 (by rfl) ⟨4546995, by rfl⟩ : syracuseStep 12125321 = 9093991) B9093991
theorem B2526875 : Blo 1120629 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B36409175 : Blo 1120629 36409175 := bstep (se 1 (by rfl) ⟨27306881, by rfl⟩ : syracuseStep 36409175 = 54613763) B54613763
theorem B2527649 : Blo 1120629 2527649 := bstep (se 2 (by rfl) ⟨947868, by rfl⟩ : syracuseStep 2527649 = 1895737) B1895737
theorem B4854875 : Blo 1120629 4854875 := bstep (se 1 (by rfl) ⟨3641156, by rfl⟩ : syracuseStep 4854875 = 7282313) B7282313
theorem B5674859 : Blo 1120629 5674859 := bstep (se 1 (by rfl) ⟨4256144, by rfl⟩ : syracuseStep 5674859 = 8512289) B8512289
theorem B10788713 : Blo 1120629 10788713 := bstep (se 2 (by rfl) ⟨4045767, by rfl⟩ : syracuseStep 10788713 = 8091535) B8091535
theorem B1124511 : Blo 1120629 1124511 := bstep (se 1 (by rfl) ⟨843383, by rfl⟩ : syracuseStep 1124511 = 1686767) B1686767
theorem B8105399 : Blo 1120629 8105399 := bstep (se 1 (by rfl) ⟨6079049, by rfl⟩ : syracuseStep 8105399 = 12158099) B12158099
theorem B43823585 : Blo 1120629 43823585 := bstep (se 2 (by rfl) ⟨16433844, by rfl⟩ : syracuseStep 43823585 = 32867689) B32867689
theorem B5386991 : Blo 1120629 5386991 := bstep (se 1 (by rfl) ⟨4040243, by rfl⟩ : syracuseStep 5386991 = 8080487) B8080487
theorem B1423271 : Blo 1120629 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B6573097 : Blo 1120629 6573097 := bstep (se 2 (by rfl) ⟨2464911, by rfl⟩ : syracuseStep 6573097 = 4929823) B4929823
theorem B10770907 : Blo 1120629 10770907 := bstep (se 1 (by rfl) ⟨8078180, by rfl⟩ : syracuseStep 10770907 = 16156361) B16156361
theorem B34987625 : Blo 1120629 34987625 := bstep (se 2 (by rfl) ⟨13120359, by rfl⟩ : syracuseStep 34987625 = 26240719) B26240719
theorem B2842715 : Blo 1120629 2842715 := bstep (se 1 (by rfl) ⟨2132036, by rfl⟩ : syracuseStep 2842715 = 4264073) B4264073
theorem B5268847 : Blo 1120629 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B8089919 : Blo 1120629 8089919 := bstep (se 1 (by rfl) ⟨6067439, by rfl⟩ : syracuseStep 8089919 = 12134879) B12134879
theorem B9238121 : Blo 1120629 9238121 := bstep (se 2 (by rfl) ⟨3464295, by rfl⟩ : syracuseStep 9238121 = 6928591) B6928591
theorem B30734903 : Blo 1120629 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B14361209 : Blo 1120629 14361209 := bstep (se 2 (by rfl) ⟨5385453, by rfl⟩ : syracuseStep 14361209 = 10770907) B10770907
theorem B20489935 : Blo 1120629 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B51785333 : Blo 1120629 51785333 := bstep (se 5 (by rfl) ⟨2427437, by rfl⟩ : syracuseStep 51785333 = 4854875) B4854875
theorem B7025129 : Blo 1120629 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B14365309 : Blo 1120629 14365309 := bstep (se 3 (by rfl) ⟨2693495, by rfl⟩ : syracuseStep 14365309 = 5386991) B5386991
theorem B1684583 : Blo 1120629 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B1685099 : Blo 1120629 1685099 := bstep (se 1 (by rfl) ⟨1263824, by rfl⟩ : syracuseStep 1685099 = 2527649) B2527649
theorem B3783239 : Blo 1120629 3783239 := bstep (se 1 (by rfl) ⟨2837429, by rfl⟩ : syracuseStep 3783239 = 5674859) B5674859
theorem B8764129 : Blo 1120629 8764129 := bstep (se 2 (by rfl) ⟨3286548, by rfl⟩ : syracuseStep 8764129 = 6573097) B6573097
theorem B7192475 : Blo 1120629 7192475 := bstep (se 1 (by rfl) ⟨5394356, by rfl⟩ : syracuseStep 7192475 = 10788713) B10788713
theorem B5393279 : Blo 1120629 5393279 := bstep (se 1 (by rfl) ⟨4044959, by rfl⟩ : syracuseStep 5393279 = 8089919) B8089919
theorem B29215723 : Blo 1120629 29215723 := bstep (se 1 (by rfl) ⟨21911792, by rfl⟩ : syracuseStep 29215723 = 43823585) B43823585
theorem B8083547 : Blo 1120629 8083547 := bstep (se 1 (by rfl) ⟨6062660, by rfl⟩ : syracuseStep 8083547 = 12125321) B12125321
theorem B24272783 : Blo 1120629 24272783 := bstep (se 1 (by rfl) ⟨18204587, by rfl⟩ : syracuseStep 24272783 = 36409175) B36409175
theorem B23325083 : Blo 1120629 23325083 := bstep (se 1 (by rfl) ⟨17493812, by rfl⟩ : syracuseStep 23325083 = 34987625) B34987625
theorem B3795389 : Blo 1120629 3795389 := bstep (se 3 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 3795389 = 1423271) B1423271
theorem B1895143 : Blo 1120629 1895143 := bstep (se 1 (by rfl) ⟨1421357, by rfl⟩ : syracuseStep 1895143 = 2842715) B2842715
theorem B5403599 : Blo 1120629 5403599 := bstep (se 1 (by rfl) ⟨4052699, by rfl⟩ : syracuseStep 5403599 = 8105399) B8105399
theorem B6158747 : Blo 1120629 6158747 := bstep (se 1 (by rfl) ⟨4619060, by rfl⟩ : syracuseStep 6158747 = 9238121) B9238121
theorem B2526857 : Blo 1120629 2526857 := bstep (se 2 (by rfl) ⟨947571, by rfl⟩ : syracuseStep 2526857 = 1895143) B1895143
theorem B9574139 : Blo 1120629 9574139 := bstep (se 1 (by rfl) ⟨7180604, by rfl⟩ : syracuseStep 9574139 = 14361209) B14361209
theorem B2530259 : Blo 1120629 2530259 := bstep (se 1 (by rfl) ⟨1897694, by rfl⟩ : syracuseStep 2530259 = 3795389) B3795389
theorem B1123055 : Blo 1120629 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B1123399 : Blo 1120629 1123399 := bstep (se 1 (by rfl) ⟨842549, by rfl⟩ : syracuseStep 1123399 = 1685099) B1685099
theorem B4105831 : Blo 1120629 4105831 := bstep (se 1 (by rfl) ⟨3079373, by rfl⟩ : syracuseStep 4105831 = 6158747) B6158747
theorem B4794983 : Blo 1120629 4794983 := bstep (se 1 (by rfl) ⟨3596237, by rfl⟩ : syracuseStep 4794983 = 7192475) B7192475
theorem B46742021 : Blo 1120629 46742021 := bstep (se 4 (by rfl) ⟨4382064, by rfl⟩ : syracuseStep 46742021 = 8764129) B8764129
theorem B5389031 : Blo 1120629 5389031 := bstep (se 1 (by rfl) ⟨4041773, by rfl⟩ : syracuseStep 5389031 = 8083547) B8083547
theorem B19153745 : Blo 1120629 19153745 := bstep (se 2 (by rfl) ⟨7182654, by rfl⟩ : syracuseStep 19153745 = 14365309) B14365309
theorem B15550055 : Blo 1120629 15550055 := bstep (se 1 (by rfl) ⟨11662541, by rfl⟩ : syracuseStep 15550055 = 23325083) B23325083
theorem B34523555 : Blo 1120629 34523555 := bstep (se 1 (by rfl) ⟨25892666, by rfl⟩ : syracuseStep 34523555 = 51785333) B51785333
theorem B3595519 : Blo 1120629 3595519 := bstep (se 1 (by rfl) ⟨2696639, by rfl⟩ : syracuseStep 3595519 = 5393279) B5393279
theorem B27319913 : Blo 1120629 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B38954297 : Blo 1120629 38954297 := bstep (se 2 (by rfl) ⟨14607861, by rfl⟩ : syracuseStep 38954297 = 29215723) B29215723
theorem B16181855 : Blo 1120629 16181855 := bstep (se 1 (by rfl) ⟨12136391, by rfl⟩ : syracuseStep 16181855 = 24272783) B24272783
theorem B4683419 : Blo 1120629 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B3602399 : Blo 1120629 3602399 := bstep (se 1 (by rfl) ⟨2701799, by rfl⟩ : syracuseStep 3602399 = 5403599) B5403599
theorem B2522159 : Blo 1120629 2522159 := bstep (se 1 (by rfl) ⟨1891619, by rfl⟩ : syracuseStep 2522159 = 3783239) B3783239
theorem B5474441 : Blo 1120629 5474441 := bstep (se 2 (by rfl) ⟨2052915, by rfl⟩ : syracuseStep 5474441 = 4105831) B4105831
theorem B9606397 : Blo 1120629 9606397 := bstep (se 3 (by rfl) ⟨1801199, by rfl⟩ : syracuseStep 9606397 = 3602399) B3602399
theorem B10787903 : Blo 1120629 10787903 := bstep (se 1 (by rfl) ⟨8090927, by rfl⟩ : syracuseStep 10787903 = 16181855) B16181855
theorem B3122279 : Blo 1120629 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B4794025 : Blo 1120629 4794025 := bstep (se 2 (by rfl) ⟨1797759, by rfl⟩ : syracuseStep 4794025 = 3595519) B3595519
theorem B1681439 : Blo 1120629 1681439 := bstep (se 1 (by rfl) ⟨1261079, by rfl⟩ : syracuseStep 1681439 = 2522159) B2522159
theorem B10366703 : Blo 1120629 10366703 := bstep (se 1 (by rfl) ⟨7775027, by rfl⟩ : syracuseStep 10366703 = 15550055) B15550055
theorem B1684571 : Blo 1120629 1684571 := bstep (se 1 (by rfl) ⟨1263428, by rfl⟩ : syracuseStep 1684571 = 2526857) B2526857
theorem B1686839 : Blo 1120629 1686839 := bstep (se 1 (by rfl) ⟨1265129, by rfl⟩ : syracuseStep 1686839 = 2530259) B2530259
theorem B25969531 : Blo 1120629 25969531 := bstep (se 1 (by rfl) ⟨19477148, by rfl⟩ : syracuseStep 25969531 = 38954297) B38954297
theorem B92062813 : Blo 1120629 92062813 := bstep (se 3 (by rfl) ⟨17261777, by rfl⟩ : syracuseStep 92062813 = 34523555) B34523555
theorem B3196655 : Blo 1120629 3196655 := bstep (se 1 (by rfl) ⟨2397491, by rfl⟩ : syracuseStep 3196655 = 4794983) B4794983
theorem B3592687 : Blo 1120629 3592687 := bstep (se 1 (by rfl) ⟨2694515, by rfl⟩ : syracuseStep 3592687 = 5389031) B5389031
theorem B12769163 : Blo 1120629 12769163 := bstep (se 1 (by rfl) ⟨9576872, by rfl⟩ : syracuseStep 12769163 = 19153745) B19153745
theorem B6382759 : Blo 1120629 6382759 := bstep (se 1 (by rfl) ⟨4787069, by rfl⟩ : syracuseStep 6382759 = 9574139) B9574139
theorem B18213275 : Blo 1120629 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B31161347 : Blo 1120629 31161347 := bstep (se 1 (by rfl) ⟨23371010, by rfl⟩ : syracuseStep 31161347 = 46742021) B46742021
theorem B2131103 : Blo 1120629 2131103 := bstep (se 1 (by rfl) ⟨1598327, by rfl⟩ : syracuseStep 2131103 = 3196655) B3196655
theorem B122750417 : Blo 1120629 122750417 := bstep (se 2 (by rfl) ⟨46031406, by rfl⟩ : syracuseStep 122750417 = 92062813) B92062813
theorem B6392033 : Blo 1120629 6392033 := bstep (se 2 (by rfl) ⟨2397012, by rfl⟩ : syracuseStep 6392033 = 4794025) B4794025
theorem B4790249 : Blo 1120629 4790249 := bstep (se 2 (by rfl) ⟨1796343, by rfl⟩ : syracuseStep 4790249 = 3592687) B3592687
theorem B1120959 : Blo 1120629 1120959 := bstep (se 1 (by rfl) ⟨840719, by rfl⟩ : syracuseStep 1120959 = 1681439) B1681439
theorem B1123047 : Blo 1120629 1123047 := bstep (se 1 (by rfl) ⟨842285, by rfl⟩ : syracuseStep 1123047 = 1684571) B1684571
theorem B1124559 : Blo 1120629 1124559 := bstep (se 1 (by rfl) ⟨843419, by rfl⟩ : syracuseStep 1124559 = 1686839) B1686839
theorem B3649627 : Blo 1120629 3649627 := bstep (se 1 (by rfl) ⟨2737220, by rfl⟩ : syracuseStep 3649627 = 5474441) B5474441
theorem B7191935 : Blo 1120629 7191935 := bstep (se 1 (by rfl) ⟨5393951, by rfl⟩ : syracuseStep 7191935 = 10787903) B10787903
theorem B2081519 : Blo 1120629 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B12142183 : Blo 1120629 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B34626041 : Blo 1120629 34626041 := bstep (se 2 (by rfl) ⟨12984765, by rfl⟩ : syracuseStep 34626041 = 25969531) B25969531
theorem B8510345 : Blo 1120629 8510345 := bstep (se 2 (by rfl) ⟨3191379, by rfl⟩ : syracuseStep 8510345 = 6382759) B6382759
theorem B8512775 : Blo 1120629 8512775 := bstep (se 1 (by rfl) ⟨6384581, by rfl⟩ : syracuseStep 8512775 = 12769163) B12769163
theorem B12808529 : Blo 1120629 12808529 := bstep (se 2 (by rfl) ⟨4803198, by rfl⟩ : syracuseStep 12808529 = 9606397) B9606397
theorem B6911135 : Blo 1120629 6911135 := bstep (se 1 (by rfl) ⟨5183351, by rfl⟩ : syracuseStep 6911135 = 10366703) B10366703
theorem B20774231 : Blo 1120629 20774231 := bstep (se 1 (by rfl) ⟨15580673, by rfl⟩ : syracuseStep 20774231 = 31161347) B31161347
theorem B19464677 : Blo 1120629 19464677 := bstep (se 4 (by rfl) ⟨1824813, by rfl⟩ : syracuseStep 19464677 = 3649627) B3649627
theorem B4261355 : Blo 1120629 4261355 := bstep (se 1 (by rfl) ⟨3196016, by rfl⟩ : syracuseStep 4261355 = 6392033) B6392033
theorem B16189577 : Blo 1120629 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B5673563 : Blo 1120629 5673563 := bstep (se 1 (by rfl) ⟨4255172, by rfl⟩ : syracuseStep 5673563 = 8510345) B8510345
theorem B5675183 : Blo 1120629 5675183 := bstep (se 1 (by rfl) ⟨4256387, by rfl⟩ : syracuseStep 5675183 = 8512775) B8512775
theorem B4794623 : Blo 1120629 4794623 := bstep (se 1 (by rfl) ⟨3595967, by rfl⟩ : syracuseStep 4794623 = 7191935) B7191935
theorem B1420735 : Blo 1120629 1420735 := bstep (se 1 (by rfl) ⟨1065551, by rfl⟩ : syracuseStep 1420735 = 2131103) B2131103
theorem B81833611 : Blo 1120629 81833611 := bstep (se 1 (by rfl) ⟨61375208, by rfl⟩ : syracuseStep 81833611 = 122750417) B122750417
theorem B3193499 : Blo 1120629 3193499 := bstep (se 1 (by rfl) ⟨2395124, by rfl⟩ : syracuseStep 3193499 = 4790249) B4790249
theorem B23084027 : Blo 1120629 23084027 := bstep (se 1 (by rfl) ⟨17313020, by rfl⟩ : syracuseStep 23084027 = 34626041) B34626041
theorem B22202869 : Blo 1120629 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B8539019 : Blo 1120629 8539019 := bstep (se 1 (by rfl) ⟨6404264, by rfl⟩ : syracuseStep 8539019 = 12808529) B12808529
theorem B4607423 : Blo 1120629 4607423 := bstep (se 1 (by rfl) ⟨3455567, by rfl⟩ : syracuseStep 4607423 = 6911135) B6911135
theorem B13849487 : Blo 1120629 13849487 := bstep (se 1 (by rfl) ⟨10387115, by rfl⟩ : syracuseStep 13849487 = 20774231) B20774231
theorem B12976451 : Blo 1120629 12976451 := bstep (se 1 (by rfl) ⟨9732338, by rfl⟩ : syracuseStep 12976451 = 19464677) B19464677
theorem B10793051 : Blo 1120629 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B3782375 : Blo 1120629 3782375 := bstep (se 1 (by rfl) ⟨2836781, by rfl⟩ : syracuseStep 3782375 = 5673563) B5673563
theorem B29603825 : Blo 1120629 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B3783455 : Blo 1120629 3783455 := bstep (se 1 (by rfl) ⟨2837591, by rfl⟩ : syracuseStep 3783455 = 5675183) B5675183
theorem B3196415 : Blo 1120629 3196415 := bstep (se 1 (by rfl) ⟨2397311, by rfl⟩ : syracuseStep 3196415 = 4794623) B4794623
theorem B15389351 : Blo 1120629 15389351 := bstep (se 1 (by rfl) ⟨11542013, by rfl⟩ : syracuseStep 15389351 = 23084027) B23084027
theorem B2840903 : Blo 1120629 2840903 := bstep (se 1 (by rfl) ⟨2130677, by rfl⟩ : syracuseStep 2840903 = 4261355) B4261355
theorem B5692679 : Blo 1120629 5692679 := bstep (se 1 (by rfl) ⟨4269509, by rfl⟩ : syracuseStep 5692679 = 8539019) B8539019
theorem B3071615 : Blo 1120629 3071615 := bstep (se 1 (by rfl) ⟨2303711, by rfl⟩ : syracuseStep 3071615 = 4607423) B4607423
theorem B9232991 : Blo 1120629 9232991 := bstep (se 1 (by rfl) ⟨6924743, by rfl⟩ : syracuseStep 9232991 = 13849487) B13849487
theorem B1894313 : Blo 1120629 1894313 := bstep (se 2 (by rfl) ⟨710367, by rfl⟩ : syracuseStep 1894313 = 1420735) B1420735
theorem B109111481 : Blo 1120629 109111481 := bstep (se 2 (by rfl) ⟨40916805, by rfl⟩ : syracuseStep 109111481 = 81833611) B81833611
theorem B2128999 : Blo 1120629 2128999 := bstep (se 1 (by rfl) ⟨1596749, by rfl⟩ : syracuseStep 2128999 = 3193499) B3193499
theorem B8650967 : Blo 1120629 8650967 := bstep (se 1 (by rfl) ⟨6488225, by rfl⟩ : syracuseStep 8650967 = 12976451) B12976451
theorem B2130943 : Blo 1120629 2130943 := bstep (se 1 (by rfl) ⟨1598207, by rfl⟩ : syracuseStep 2130943 = 3196415) B3196415
theorem B10259567 : Blo 1120629 10259567 := bstep (se 1 (by rfl) ⟨7694675, by rfl⟩ : syracuseStep 10259567 = 15389351) B15389351
theorem B19735883 : Blo 1120629 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B1262875 : Blo 1120629 1262875 := bstep (se 1 (by rfl) ⟨947156, by rfl⟩ : syracuseStep 1262875 = 1894313) B1894313
theorem B7195367 : Blo 1120629 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B2838665 : Blo 1120629 2838665 := bstep (se 2 (by rfl) ⟨1064499, by rfl⟩ : syracuseStep 2838665 = 2128999) B2128999
theorem B1893935 : Blo 1120629 1893935 := bstep (se 1 (by rfl) ⟨1420451, by rfl⟩ : syracuseStep 1893935 = 2840903) B2840903
theorem B3795119 : Blo 1120629 3795119 := bstep (se 1 (by rfl) ⟨2846339, by rfl⟩ : syracuseStep 3795119 = 5692679) B5692679
theorem B6155327 : Blo 1120629 6155327 := bstep (se 1 (by rfl) ⟨4616495, by rfl⟩ : syracuseStep 6155327 = 9232991) B9232991
theorem B72740987 : Blo 1120629 72740987 := bstep (se 1 (by rfl) ⟨54555740, by rfl⟩ : syracuseStep 72740987 = 109111481) B109111481
theorem B2521583 : Blo 1120629 2521583 := bstep (se 1 (by rfl) ⟨1891187, by rfl⟩ : syracuseStep 2521583 = 3782375) B3782375
theorem B8190973 : Blo 1120629 8190973 := bstep (se 3 (by rfl) ⟨1535807, by rfl⟩ : syracuseStep 8190973 = 3071615) B3071615
theorem B2522303 : Blo 1120629 2522303 := bstep (se 1 (by rfl) ⟨1891727, by rfl⟩ : syracuseStep 2522303 = 3783455) B3783455
theorem B92276981 : Blo 1120629 92276981 := bstep (se 5 (by rfl) ⟨4325483, by rfl⟩ : syracuseStep 92276981 = 8650967) B8650967
theorem B43685189 : Blo 1120629 43685189 := bstep (se 4 (by rfl) ⟨4095486, by rfl⟩ : syracuseStep 43685189 = 8190973) B8190973
theorem B2530079 : Blo 1120629 2530079 := bstep (se 1 (by rfl) ⟨1897559, by rfl⟩ : syracuseStep 2530079 = 3795119) B3795119
theorem B4103551 : Blo 1120629 4103551 := bstep (se 1 (by rfl) ⟨3077663, by rfl⟩ : syracuseStep 4103551 = 6155327) B6155327
theorem B1681055 : Blo 1120629 1681055 := bstep (se 1 (by rfl) ⟨1260791, by rfl⟩ : syracuseStep 1681055 = 2521583) B2521583
theorem B1681535 : Blo 1120629 1681535 := bstep (se 1 (by rfl) ⟨1261151, by rfl⟩ : syracuseStep 1681535 = 2522303) B2522303
theorem B1683833 : Blo 1120629 1683833 := bstep (se 2 (by rfl) ⟨631437, by rfl⟩ : syracuseStep 1683833 = 1262875) B1262875
theorem B4796911 : Blo 1120629 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B13157255 : Blo 1120629 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B1262623 : Blo 1120629 1262623 := bstep (se 1 (by rfl) ⟨946967, by rfl⟩ : syracuseStep 1262623 = 1893935) B1893935
theorem B2841257 : Blo 1120629 2841257 := bstep (se 2 (by rfl) ⟨1065471, by rfl⟩ : syracuseStep 2841257 = 2130943) B2130943
theorem B6839711 : Blo 1120629 6839711 := bstep (se 1 (by rfl) ⟨5129783, by rfl⟩ : syracuseStep 6839711 = 10259567) B10259567
theorem B1892443 : Blo 1120629 1892443 := bstep (se 1 (by rfl) ⟨1419332, by rfl⟩ : syracuseStep 1892443 = 2838665) B2838665
theorem B48493991 : Blo 1120629 48493991 := bstep (se 1 (by rfl) ⟨36370493, by rfl⟩ : syracuseStep 48493991 = 72740987) B72740987
theorem B2523257 : Blo 1120629 2523257 := bstep (se 2 (by rfl) ⟨946221, by rfl⟩ : syracuseStep 2523257 = 1892443) B1892443
theorem B4559807 : Blo 1120629 4559807 := bstep (se 1 (by rfl) ⟨3419855, by rfl⟩ : syracuseStep 4559807 = 6839711) B6839711
theorem B6395881 : Blo 1120629 6395881 := bstep (se 2 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 6395881 = 4796911) B4796911
theorem B1120703 : Blo 1120629 1120703 := bstep (se 1 (by rfl) ⟨840527, by rfl⟩ : syracuseStep 1120703 = 1681055) B1681055
theorem B1121023 : Blo 1120629 1121023 := bstep (se 1 (by rfl) ⟨840767, by rfl⟩ : syracuseStep 1121023 = 1681535) B1681535
theorem B1122555 : Blo 1120629 1122555 := bstep (se 1 (by rfl) ⟨841916, by rfl⟩ : syracuseStep 1122555 = 1683833) B1683833
theorem B1683497 : Blo 1120629 1683497 := bstep (se 2 (by rfl) ⟨631311, by rfl⟩ : syracuseStep 1683497 = 1262623) B1262623
theorem B61517987 : Blo 1120629 61517987 := bstep (se 1 (by rfl) ⟨46138490, by rfl⟩ : syracuseStep 61517987 = 92276981) B92276981
theorem B1686719 : Blo 1120629 1686719 := bstep (se 1 (by rfl) ⟨1265039, by rfl⟩ : syracuseStep 1686719 = 2530079) B2530079
theorem B32329327 : Blo 1120629 32329327 := bstep (se 1 (by rfl) ⟨24246995, by rfl⟩ : syracuseStep 32329327 = 48493991) B48493991
theorem B8771503 : Blo 1120629 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B29123459 : Blo 1120629 29123459 := bstep (se 1 (by rfl) ⟨21842594, by rfl⟩ : syracuseStep 29123459 = 43685189) B43685189
theorem B1894171 : Blo 1120629 1894171 := bstep (se 1 (by rfl) ⟨1420628, by rfl⟩ : syracuseStep 1894171 = 2841257) B2841257
theorem B5471401 : Blo 1120629 5471401 := bstep (se 2 (by rfl) ⟨2051775, by rfl⟩ : syracuseStep 5471401 = 4103551) B4103551
theorem B2525561 : Blo 1120629 2525561 := bstep (se 2 (by rfl) ⟨947085, by rfl⟩ : syracuseStep 2525561 = 1894171) B1894171
theorem B8527841 : Blo 1120629 8527841 := bstep (se 2 (by rfl) ⟨3197940, by rfl⟩ : syracuseStep 8527841 = 6395881) B6395881
theorem B1122331 : Blo 1120629 1122331 := bstep (se 1 (by rfl) ⟨841748, by rfl⟩ : syracuseStep 1122331 = 1683497) B1683497
theorem B1124479 : Blo 1120629 1124479 := bstep (se 1 (by rfl) ⟨843359, by rfl⟩ : syracuseStep 1124479 = 1686719) B1686719
theorem B1682171 : Blo 1120629 1682171 := bstep (se 1 (by rfl) ⟨1261628, by rfl⟩ : syracuseStep 1682171 = 2523257) B2523257
theorem B43105769 : Blo 1120629 43105769 := bstep (se 2 (by rfl) ⟨16164663, by rfl⟩ : syracuseStep 43105769 = 32329327) B32329327
theorem B19415639 : Blo 1120629 19415639 := bstep (se 1 (by rfl) ⟨14561729, by rfl⟩ : syracuseStep 19415639 = 29123459) B29123459
theorem B41011991 : Blo 1120629 41011991 := bstep (se 1 (by rfl) ⟨30758993, by rfl⟩ : syracuseStep 41011991 = 61517987) B61517987
theorem B7295201 : Blo 1120629 7295201 := bstep (se 2 (by rfl) ⟨2735700, by rfl⟩ : syracuseStep 7295201 = 5471401) B5471401
theorem B3039871 : Blo 1120629 3039871 := bstep (se 1 (by rfl) ⟨2279903, by rfl⟩ : syracuseStep 3039871 = 4559807) B4559807
theorem B11695337 : Blo 1120629 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B12943759 : Blo 1120629 12943759 := bstep (se 1 (by rfl) ⟨9707819, by rfl⟩ : syracuseStep 12943759 = 19415639) B19415639
theorem B1121447 : Blo 1120629 1121447 := bstep (se 1 (by rfl) ⟨841085, by rfl⟩ : syracuseStep 1121447 = 1682171) B1682171
theorem B1683707 : Blo 1120629 1683707 := bstep (se 1 (by rfl) ⟨1262780, by rfl⟩ : syracuseStep 1683707 = 2525561) B2525561
theorem B27341327 : Blo 1120629 27341327 := bstep (se 1 (by rfl) ⟨20505995, by rfl⟩ : syracuseStep 27341327 = 41011991) B41011991
theorem B4863467 : Blo 1120629 4863467 := bstep (se 1 (by rfl) ⟨3647600, by rfl⟩ : syracuseStep 4863467 = 7295201) B7295201
theorem B5685227 : Blo 1120629 5685227 := bstep (se 1 (by rfl) ⟨4263920, by rfl⟩ : syracuseStep 5685227 = 8527841) B8527841
theorem B4053161 : Blo 1120629 4053161 := bstep (se 2 (by rfl) ⟨1519935, by rfl⟩ : syracuseStep 4053161 = 3039871) B3039871
theorem B7796891 : Blo 1120629 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B28737179 : Blo 1120629 28737179 := bstep (se 1 (by rfl) ⟨21552884, by rfl⟩ : syracuseStep 28737179 = 43105769) B43105769
theorem B1122471 : Blo 1120629 1122471 := bstep (se 1 (by rfl) ⟨841853, by rfl⟩ : syracuseStep 1122471 = 1683707) B1683707
theorem B18227551 : Blo 1120629 18227551 := bstep (se 1 (by rfl) ⟨13670663, by rfl⟩ : syracuseStep 18227551 = 27341327) B27341327
theorem B2702107 : Blo 1120629 2702107 := bstep (se 1 (by rfl) ⟨2026580, by rfl⟩ : syracuseStep 2702107 = 4053161) B4053161
theorem B5197927 : Blo 1120629 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B19158119 : Blo 1120629 19158119 := bstep (se 1 (by rfl) ⟨14368589, by rfl⟩ : syracuseStep 19158119 = 28737179) B28737179
theorem B3790151 : Blo 1120629 3790151 := bstep (se 1 (by rfl) ⟨2842613, by rfl⟩ : syracuseStep 3790151 = 5685227) B5685227
theorem B17258345 : Blo 1120629 17258345 := bstep (se 2 (by rfl) ⟨6471879, by rfl⟩ : syracuseStep 17258345 = 12943759) B12943759
theorem B3242311 : Blo 1120629 3242311 := bstep (se 1 (by rfl) ⟨2431733, by rfl⟩ : syracuseStep 3242311 = 4863467) B4863467
theorem B2526767 : Blo 1120629 2526767 := bstep (se 1 (by rfl) ⟨1895075, by rfl⟩ : syracuseStep 2526767 = 3790151) B3790151
theorem B11505563 : Blo 1120629 11505563 := bstep (se 1 (by rfl) ⟨8629172, by rfl⟩ : syracuseStep 11505563 = 17258345) B17258345
theorem B6930569 : Blo 1120629 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B24303401 : Blo 1120629 24303401 := bstep (se 2 (by rfl) ⟨9113775, by rfl⟩ : syracuseStep 24303401 = 18227551) B18227551
theorem B17292325 : Blo 1120629 17292325 := bstep (se 4 (by rfl) ⟨1621155, by rfl⟩ : syracuseStep 17292325 = 3242311) B3242311
theorem B12772079 : Blo 1120629 12772079 := bstep (se 1 (by rfl) ⟨9579059, by rfl⟩ : syracuseStep 12772079 = 19158119) B19158119
theorem B3602809 : Blo 1120629 3602809 := bstep (se 2 (by rfl) ⟨1351053, by rfl⟩ : syracuseStep 3602809 = 2702107) B2702107
theorem B18481517 : Blo 1120629 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B7670375 : Blo 1120629 7670375 := bstep (se 1 (by rfl) ⟨5752781, by rfl⟩ : syracuseStep 7670375 = 11505563) B11505563
theorem B19214981 : Blo 1120629 19214981 := bstep (se 4 (by rfl) ⟨1801404, by rfl⟩ : syracuseStep 19214981 = 3602809) B3602809
theorem B1684511 : Blo 1120629 1684511 := bstep (se 1 (by rfl) ⟨1263383, by rfl⟩ : syracuseStep 1684511 = 2526767) B2526767
theorem B16202267 : Blo 1120629 16202267 := bstep (se 1 (by rfl) ⟨12151700, by rfl⟩ : syracuseStep 16202267 = 24303401) B24303401
theorem B23056433 : Blo 1120629 23056433 := bstep (se 2 (by rfl) ⟨8646162, by rfl⟩ : syracuseStep 23056433 = 17292325) B17292325
theorem B8514719 : Blo 1120629 8514719 := bstep (se 1 (by rfl) ⟨6386039, by rfl⟩ : syracuseStep 8514719 = 12772079) B12772079
theorem B12321011 : Blo 1120629 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B5113583 : Blo 1120629 5113583 := bstep (se 1 (by rfl) ⟨3835187, by rfl⟩ : syracuseStep 5113583 = 7670375) B7670375
theorem B15370955 : Blo 1120629 15370955 := bstep (se 1 (by rfl) ⟨11528216, by rfl⟩ : syracuseStep 15370955 = 23056433) B23056433
theorem B5676479 : Blo 1120629 5676479 := bstep (se 1 (by rfl) ⟨4257359, by rfl⟩ : syracuseStep 5676479 = 8514719) B8514719
theorem B1123007 : Blo 1120629 1123007 := bstep (se 1 (by rfl) ⟨842255, by rfl⟩ : syracuseStep 1123007 = 1684511) B1684511
theorem B10801511 : Blo 1120629 10801511 := bstep (se 1 (by rfl) ⟨8101133, by rfl⟩ : syracuseStep 10801511 = 16202267) B16202267
theorem B12809987 : Blo 1120629 12809987 := bstep (se 1 (by rfl) ⟨9607490, by rfl⟩ : syracuseStep 12809987 = 19214981) B19214981
theorem B3409055 : Blo 1120629 3409055 := bstep (se 1 (by rfl) ⟨2556791, by rfl⟩ : syracuseStep 3409055 = 5113583) B5113583
theorem B3784319 : Blo 1120629 3784319 := bstep (se 1 (by rfl) ⟨2838239, by rfl⟩ : syracuseStep 3784319 = 5676479) B5676479
theorem B8539991 : Blo 1120629 8539991 := bstep (se 1 (by rfl) ⟨6404993, by rfl⟩ : syracuseStep 8539991 = 12809987) B12809987
theorem B8214007 : Blo 1120629 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B10247303 : Blo 1120629 10247303 := bstep (se 1 (by rfl) ⟨7685477, by rfl⟩ : syracuseStep 10247303 = 15370955) B15370955
theorem B7201007 : Blo 1120629 7201007 := bstep (se 1 (by rfl) ⟨5400755, by rfl⟩ : syracuseStep 7201007 = 10801511) B10801511
theorem B10952009 : Blo 1120629 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B2272703 : Blo 1120629 2272703 := bstep (se 1 (by rfl) ⟨1704527, by rfl⟩ : syracuseStep 2272703 = 3409055) B3409055
theorem B6831535 : Blo 1120629 6831535 := bstep (se 1 (by rfl) ⟨5123651, by rfl⟩ : syracuseStep 6831535 = 10247303) B10247303
theorem B4800671 : Blo 1120629 4800671 := bstep (se 1 (by rfl) ⟨3600503, by rfl⟩ : syracuseStep 4800671 = 7201007) B7201007
theorem B5693327 : Blo 1120629 5693327 := bstep (se 1 (by rfl) ⟨4269995, by rfl⟩ : syracuseStep 5693327 = 8539991) B8539991
theorem B2522879 : Blo 1120629 2522879 := bstep (se 1 (by rfl) ⟨1892159, by rfl⟩ : syracuseStep 2522879 = 3784319) B3784319
theorem B1681919 : Blo 1120629 1681919 := bstep (se 1 (by rfl) ⟨1261439, by rfl⟩ : syracuseStep 1681919 = 2522879) B2522879
theorem B3200447 : Blo 1120629 3200447 := bstep (se 1 (by rfl) ⟨2400335, by rfl⟩ : syracuseStep 3200447 = 4800671) B4800671
theorem B7301339 : Blo 1120629 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B3795551 : Blo 1120629 3795551 := bstep (se 1 (by rfl) ⟨2846663, by rfl⟩ : syracuseStep 3795551 = 5693327) B5693327
theorem B6060541 : Blo 1120629 6060541 := bstep (se 3 (by rfl) ⟨1136351, by rfl⟩ : syracuseStep 6060541 = 2272703) B2272703
theorem B9108713 : Blo 1120629 9108713 := bstep (se 2 (by rfl) ⟨3415767, by rfl⟩ : syracuseStep 9108713 = 6831535) B6831535
theorem B2133631 : Blo 1120629 2133631 := bstep (se 1 (by rfl) ⟨1600223, by rfl⟩ : syracuseStep 2133631 = 3200447) B3200447
theorem B1121279 : Blo 1120629 1121279 := bstep (se 1 (by rfl) ⟨840959, by rfl⟩ : syracuseStep 1121279 = 1681919) B1681919
theorem B2530367 : Blo 1120629 2530367 := bstep (se 1 (by rfl) ⟨1897775, by rfl⟩ : syracuseStep 2530367 = 3795551) B3795551
theorem B24289901 : Blo 1120629 24289901 := bstep (se 3 (by rfl) ⟨4554356, by rfl⟩ : syracuseStep 24289901 = 9108713) B9108713
theorem B4867559 : Blo 1120629 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B8080721 : Blo 1120629 8080721 := bstep (se 2 (by rfl) ⟨3030270, by rfl⟩ : syracuseStep 8080721 = 6060541) B6060541
theorem B3245039 : Blo 1120629 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B16193267 : Blo 1120629 16193267 := bstep (se 1 (by rfl) ⟨12144950, by rfl⟩ : syracuseStep 16193267 = 24289901) B24289901
theorem B5387147 : Blo 1120629 5387147 := bstep (se 1 (by rfl) ⟨4040360, by rfl⟩ : syracuseStep 5387147 = 8080721) B8080721
theorem B1686911 : Blo 1120629 1686911 := bstep (se 1 (by rfl) ⟨1265183, by rfl⟩ : syracuseStep 1686911 = 2530367) B2530367
theorem B2844841 : Blo 1120629 2844841 := bstep (se 2 (by rfl) ⟨1066815, by rfl⟩ : syracuseStep 2844841 = 2133631) B2133631
theorem B2163359 : Blo 1120629 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B1124607 : Blo 1120629 1124607 := bstep (se 1 (by rfl) ⟨843455, by rfl⟩ : syracuseStep 1124607 = 1686911) B1686911
theorem B10795511 : Blo 1120629 10795511 := bstep (se 1 (by rfl) ⟨8096633, by rfl⟩ : syracuseStep 10795511 = 16193267) B16193267
theorem B3591431 : Blo 1120629 3591431 := bstep (se 1 (by rfl) ⟨2693573, by rfl⟩ : syracuseStep 3591431 = 5387147) B5387147
theorem B3793121 : Blo 1120629 3793121 := bstep (se 2 (by rfl) ⟨1422420, by rfl⟩ : syracuseStep 3793121 = 2844841) B2844841
theorem B5768957 : Blo 1120629 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B2394287 : Blo 1120629 2394287 := bstep (se 1 (by rfl) ⟨1795715, by rfl⟩ : syracuseStep 2394287 = 3591431) B3591431
theorem B2528747 : Blo 1120629 2528747 := bstep (se 1 (by rfl) ⟨1896560, by rfl⟩ : syracuseStep 2528747 = 3793121) B3793121
theorem B7197007 : Blo 1120629 7197007 := bstep (se 1 (by rfl) ⟨5397755, by rfl⟩ : syracuseStep 7197007 = 10795511) B10795511
theorem B3845971 : Blo 1120629 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B1685831 : Blo 1120629 1685831 := bstep (se 1 (by rfl) ⟨1264373, by rfl⟩ : syracuseStep 1685831 = 2528747) B2528747
theorem B1596191 : Blo 1120629 1596191 := bstep (se 1 (by rfl) ⟨1197143, by rfl⟩ : syracuseStep 1596191 = 2394287) B2394287
theorem B9596009 : Blo 1120629 9596009 := bstep (se 2 (by rfl) ⟨3598503, by rfl⟩ : syracuseStep 9596009 = 7197007) B7197007
theorem B6397339 : Blo 1120629 6397339 := bstep (se 1 (by rfl) ⟨4798004, by rfl⟩ : syracuseStep 6397339 = 9596009) B9596009
theorem B1123887 : Blo 1120629 1123887 := bstep (se 1 (by rfl) ⟨842915, by rfl⟩ : syracuseStep 1123887 = 1685831) B1685831
theorem B5127961 : Blo 1120629 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B4256509 : Blo 1120629 4256509 := bstep (se 3 (by rfl) ⟨798095, by rfl⟩ : syracuseStep 4256509 = 1596191) B1596191
theorem B5675345 : Blo 1120629 5675345 := bstep (se 2 (by rfl) ⟨2128254, by rfl⟩ : syracuseStep 5675345 = 4256509) B4256509
theorem B8529785 : Blo 1120629 8529785 := bstep (se 2 (by rfl) ⟨3198669, by rfl⟩ : syracuseStep 8529785 = 6397339) B6397339
theorem B6837281 : Blo 1120629 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B4558187 : Blo 1120629 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B3783563 : Blo 1120629 3783563 := bstep (se 1 (by rfl) ⟨2837672, by rfl⟩ : syracuseStep 3783563 = 5675345) B5675345
theorem B5686523 : Blo 1120629 5686523 := bstep (se 1 (by rfl) ⟨4264892, by rfl⟩ : syracuseStep 5686523 = 8529785) B8529785
theorem B3791015 : Blo 1120629 3791015 := bstep (se 1 (by rfl) ⟨2843261, by rfl⟩ : syracuseStep 3791015 = 5686523) B5686523
theorem B3038791 : Blo 1120629 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B2522375 : Blo 1120629 2522375 := bstep (se 1 (by rfl) ⟨1891781, by rfl⟩ : syracuseStep 2522375 = 3783563) B3783563
theorem B2527343 : Blo 1120629 2527343 := bstep (se 1 (by rfl) ⟨1895507, by rfl⟩ : syracuseStep 2527343 = 3791015) B3791015
theorem B1681583 : Blo 1120629 1681583 := bstep (se 1 (by rfl) ⟨1261187, by rfl⟩ : syracuseStep 1681583 = 2522375) B2522375
theorem B4051721 : Blo 1120629 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B1121055 : Blo 1120629 1121055 := bstep (se 1 (by rfl) ⟨840791, by rfl⟩ : syracuseStep 1121055 = 1681583) B1681583
theorem B1684895 : Blo 1120629 1684895 := bstep (se 1 (by rfl) ⟨1263671, by rfl⟩ : syracuseStep 1684895 = 2527343) B2527343
theorem B2701147 : Blo 1120629 2701147 := bstep (se 1 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 2701147 = 4051721) B4051721
theorem B1123263 : Blo 1120629 1123263 := bstep (se 1 (by rfl) ⟨842447, by rfl⟩ : syracuseStep 1123263 = 1684895) B1684895
theorem B3601529 : Blo 1120629 3601529 := bstep (se 2 (by rfl) ⟨1350573, by rfl⟩ : syracuseStep 3601529 = 2701147) B2701147
theorem B2401019 : Blo 1120629 2401019 := bstep (se 1 (by rfl) ⟨1800764, by rfl⟩ : syracuseStep 2401019 = 3601529) B3601529
theorem B1600679 : Blo 1120629 1600679 := bstep (se 1 (by rfl) ⟨1200509, by rfl⟩ : syracuseStep 1600679 = 2401019) B2401019
theorem B4268477 : Blo 1120629 4268477 := bstep (se 3 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 4268477 = 1600679) B1600679
theorem B2845651 : Blo 1120629 2845651 := bstep (se 1 (by rfl) ⟨2134238, by rfl⟩ : syracuseStep 2845651 = 4268477) B4268477
theorem B3794201 : Blo 1120629 3794201 := bstep (se 2 (by rfl) ⟨1422825, by rfl⟩ : syracuseStep 3794201 = 2845651) B2845651
theorem B2529467 : Blo 1120629 2529467 := bstep (se 1 (by rfl) ⟨1897100, by rfl⟩ : syracuseStep 2529467 = 3794201) B3794201
theorem B1686311 : Blo 1120629 1686311 := bstep (se 1 (by rfl) ⟨1264733, by rfl⟩ : syracuseStep 1686311 = 2529467) B2529467
theorem B1124207 : Blo 1120629 1124207 := bstep (se 1 (by rfl) ⟨843155, by rfl⟩ : syracuseStep 1124207 = 1686311) B1686311

theorem C0 (j : ℕ) (h1 : 280157 ≤ j) (h2 : j ≤ 280856) : Blo 1120629 (4 * j + 3) := by
  interval_cases j
  · exact B1120631
  · exact B1120635
  · exact B1120639
  · exact B1120643
  · exact B1120647
  · exact B1120651
  · exact B1120655
  · exact B1120659
  · exact B1120663
  · exact B1120667
  · exact B1120671
  · exact B1120675
  · exact B1120679
  · exact B1120683
  · exact B1120687
  · exact B1120691
  · exact B1120695
  · exact B1120699
  · exact B1120703
  · exact B1120707
  · exact B1120711
  · exact B1120715
  · exact B1120719
  · exact B1120723
  · exact B1120727
  · exact B1120731
  · exact B1120735
  · exact B1120739
  · exact B1120743
  · exact B1120747
  · exact B1120751
  · exact B1120755
  · exact B1120759
  · exact B1120763
  · exact B1120767
  · exact B1120771
  · exact B1120775
  · exact B1120779
  · exact B1120783
  · exact B1120787
  · exact B1120791
  · exact B1120795
  · exact B1120799
  · exact B1120803
  · exact B1120807
  · exact B1120811
  · exact B1120815
  · exact B1120819
  · exact B1120823
  · exact B1120827
  · exact B1120831
  · exact B1120835
  · exact B1120839
  · exact B1120843
  · exact B1120847
  · exact B1120851
  · exact B1120855
  · exact B1120859
  · exact B1120863
  · exact B1120867
  · exact B1120871
  · exact B1120875
  · exact B1120879
  · exact B1120883
  · exact B1120887
  · exact B1120891
  · exact B1120895
  · exact B1120899
  · exact B1120903
  · exact B1120907
  · exact B1120911
  · exact B1120915
  · exact B1120919
  · exact B1120923
  · exact B1120927
  · exact B1120931
  · exact B1120935
  · exact B1120939
  · exact B1120943
  · exact B1120947
  · exact B1120951
  · exact B1120955
  · exact B1120959
  · exact B1120963
  · exact B1120967
  · exact B1120971
  · exact B1120975
  · exact B1120979
  · exact B1120983
  · exact B1120987
  · exact B1120991
  · exact B1120995
  · exact B1120999
  · exact B1121003
  · exact B1121007
  · exact B1121011
  · exact B1121015
  · exact B1121019
  · exact B1121023
  · exact B1121027
  · exact B1121031
  · exact B1121035
  · exact B1121039
  · exact B1121043
  · exact B1121047
  · exact B1121051
  · exact B1121055
  · exact B1121059
  · exact B1121063
  · exact B1121067
  · exact B1121071
  · exact B1121075
  · exact B1121079
  · exact B1121083
  · exact B1121087
  · exact B1121091
  · exact B1121095
  · exact B1121099
  · exact B1121103
  · exact B1121107
  · exact B1121111
  · exact B1121115
  · exact B1121119
  · exact B1121123
  · exact B1121127
  · exact B1121131
  · exact B1121135
  · exact B1121139
  · exact B1121143
  · exact B1121147
  · exact B1121151
  · exact B1121155
  · exact B1121159
  · exact B1121163
  · exact B1121167
  · exact B1121171
  · exact B1121175
  · exact B1121179
  · exact B1121183
  · exact B1121187
  · exact B1121191
  · exact B1121195
  · exact B1121199
  · exact B1121203
  · exact B1121207
  · exact B1121211
  · exact B1121215
  · exact B1121219
  · exact B1121223
  · exact B1121227
  · exact B1121231
  · exact B1121235
  · exact B1121239
  · exact B1121243
  · exact B1121247
  · exact B1121251
  · exact B1121255
  · exact B1121259
  · exact B1121263
  · exact B1121267
  · exact B1121271
  · exact B1121275
  · exact B1121279
  · exact B1121283
  · exact B1121287
  · exact B1121291
  · exact B1121295
  · exact B1121299
  · exact B1121303
  · exact B1121307
  · exact B1121311
  · exact B1121315
  · exact B1121319
  · exact B1121323
  · exact B1121327
  · exact B1121331
  · exact B1121335
  · exact B1121339
  · exact B1121343
  · exact B1121347
  · exact B1121351
  · exact B1121355
  · exact B1121359
  · exact B1121363
  · exact B1121367
  · exact B1121371
  · exact B1121375
  · exact B1121379
  · exact B1121383
  · exact B1121387
  · exact B1121391
  · exact B1121395
  · exact B1121399
  · exact B1121403
  · exact B1121407
  · exact B1121411
  · exact B1121415
  · exact B1121419
  · exact B1121423
  · exact B1121427
  · exact B1121431
  · exact B1121435
  · exact B1121439
  · exact B1121443
  · exact B1121447
  · exact B1121451
  · exact B1121455
  · exact B1121459
  · exact B1121463
  · exact B1121467
  · exact B1121471
  · exact B1121475
  · exact B1121479
  · exact B1121483
  · exact B1121487
  · exact B1121491
  · exact B1121495
  · exact B1121499
  · exact B1121503
  · exact B1121507
  · exact B1121511
  · exact B1121515
  · exact B1121519
  · exact B1121523
  · exact B1121527
  · exact B1121531
  · exact B1121535
  · exact B1121539
  · exact B1121543
  · exact B1121547
  · exact B1121551
  · exact B1121555
  · exact B1121559
  · exact B1121563
  · exact B1121567
  · exact B1121571
  · exact B1121575
  · exact B1121579
  · exact B1121583
  · exact B1121587
  · exact B1121591
  · exact B1121595
  · exact B1121599
  · exact B1121603
  · exact B1121607
  · exact B1121611
  · exact B1121615
  · exact B1121619
  · exact B1121623
  · exact B1121627
  · exact B1121631
  · exact B1121635
  · exact B1121639
  · exact B1121643
  · exact B1121647
  · exact B1121651
  · exact B1121655
  · exact B1121659
  · exact B1121663
  · exact B1121667
  · exact B1121671
  · exact B1121675
  · exact B1121679
  · exact B1121683
  · exact B1121687
  · exact B1121691
  · exact B1121695
  · exact B1121699
  · exact B1121703
  · exact B1121707
  · exact B1121711
  · exact B1121715
  · exact B1121719
  · exact B1121723
  · exact B1121727
  · exact B1121731
  · exact B1121735
  · exact B1121739
  · exact B1121743
  · exact B1121747
  · exact B1121751
  · exact B1121755
  · exact B1121759
  · exact B1121763
  · exact B1121767
  · exact B1121771
  · exact B1121775
  · exact B1121779
  · exact B1121783
  · exact B1121787
  · exact B1121791
  · exact B1121795
  · exact B1121799
  · exact B1121803
  · exact B1121807
  · exact B1121811
  · exact B1121815
  · exact B1121819
  · exact B1121823
  · exact B1121827
  · exact B1121831
  · exact B1121835
  · exact B1121839
  · exact B1121843
  · exact B1121847
  · exact B1121851
  · exact B1121855
  · exact B1121859
  · exact B1121863
  · exact B1121867
  · exact B1121871
  · exact B1121875
  · exact B1121879
  · exact B1121883
  · exact B1121887
  · exact B1121891
  · exact B1121895
  · exact B1121899
  · exact B1121903
  · exact B1121907
  · exact B1121911
  · exact B1121915
  · exact B1121919
  · exact B1121923
  · exact B1121927
  · exact B1121931
  · exact B1121935
  · exact B1121939
  · exact B1121943
  · exact B1121947
  · exact B1121951
  · exact B1121955
  · exact B1121959
  · exact B1121963
  · exact B1121967
  · exact B1121971
  · exact B1121975
  · exact B1121979
  · exact B1121983
  · exact B1121987
  · exact B1121991
  · exact B1121995
  · exact B1121999
  · exact B1122003
  · exact B1122007
  · exact B1122011
  · exact B1122015
  · exact B1122019
  · exact B1122023
  · exact B1122027
  · exact B1122031
  · exact B1122035
  · exact B1122039
  · exact B1122043
  · exact B1122047
  · exact B1122051
  · exact B1122055
  · exact B1122059
  · exact B1122063
  · exact B1122067
  · exact B1122071
  · exact B1122075
  · exact B1122079
  · exact B1122083
  · exact B1122087
  · exact B1122091
  · exact B1122095
  · exact B1122099
  · exact B1122103
  · exact B1122107
  · exact B1122111
  · exact B1122115
  · exact B1122119
  · exact B1122123
  · exact B1122127
  · exact B1122131
  · exact B1122135
  · exact B1122139
  · exact B1122143
  · exact B1122147
  · exact B1122151
  · exact B1122155
  · exact B1122159
  · exact B1122163
  · exact B1122167
  · exact B1122171
  · exact B1122175
  · exact B1122179
  · exact B1122183
  · exact B1122187
  · exact B1122191
  · exact B1122195
  · exact B1122199
  · exact B1122203
  · exact B1122207
  · exact B1122211
  · exact B1122215
  · exact B1122219
  · exact B1122223
  · exact B1122227
  · exact B1122231
  · exact B1122235
  · exact B1122239
  · exact B1122243
  · exact B1122247
  · exact B1122251
  · exact B1122255
  · exact B1122259
  · exact B1122263
  · exact B1122267
  · exact B1122271
  · exact B1122275
  · exact B1122279
  · exact B1122283
  · exact B1122287
  · exact B1122291
  · exact B1122295
  · exact B1122299
  · exact B1122303
  · exact B1122307
  · exact B1122311
  · exact B1122315
  · exact B1122319
  · exact B1122323
  · exact B1122327
  · exact B1122331
  · exact B1122335
  · exact B1122339
  · exact B1122343
  · exact B1122347
  · exact B1122351
  · exact B1122355
  · exact B1122359
  · exact B1122363
  · exact B1122367
  · exact B1122371
  · exact B1122375
  · exact B1122379
  · exact B1122383
  · exact B1122387
  · exact B1122391
  · exact B1122395
  · exact B1122399
  · exact B1122403
  · exact B1122407
  · exact B1122411
  · exact B1122415
  · exact B1122419
  · exact B1122423
  · exact B1122427
  · exact B1122431
  · exact B1122435
  · exact B1122439
  · exact B1122443
  · exact B1122447
  · exact B1122451
  · exact B1122455
  · exact B1122459
  · exact B1122463
  · exact B1122467
  · exact B1122471
  · exact B1122475
  · exact B1122479
  · exact B1122483
  · exact B1122487
  · exact B1122491
  · exact B1122495
  · exact B1122499
  · exact B1122503
  · exact B1122507
  · exact B1122511
  · exact B1122515
  · exact B1122519
  · exact B1122523
  · exact B1122527
  · exact B1122531
  · exact B1122535
  · exact B1122539
  · exact B1122543
  · exact B1122547
  · exact B1122551
  · exact B1122555
  · exact B1122559
  · exact B1122563
  · exact B1122567
  · exact B1122571
  · exact B1122575
  · exact B1122579
  · exact B1122583
  · exact B1122587
  · exact B1122591
  · exact B1122595
  · exact B1122599
  · exact B1122603
  · exact B1122607
  · exact B1122611
  · exact B1122615
  · exact B1122619
  · exact B1122623
  · exact B1122627
  · exact B1122631
  · exact B1122635
  · exact B1122639
  · exact B1122643
  · exact B1122647
  · exact B1122651
  · exact B1122655
  · exact B1122659
  · exact B1122663
  · exact B1122667
  · exact B1122671
  · exact B1122675
  · exact B1122679
  · exact B1122683
  · exact B1122687
  · exact B1122691
  · exact B1122695
  · exact B1122699
  · exact B1122703
  · exact B1122707
  · exact B1122711
  · exact B1122715
  · exact B1122719
  · exact B1122723
  · exact B1122727
  · exact B1122731
  · exact B1122735
  · exact B1122739
  · exact B1122743
  · exact B1122747
  · exact B1122751
  · exact B1122755
  · exact B1122759
  · exact B1122763
  · exact B1122767
  · exact B1122771
  · exact B1122775
  · exact B1122779
  · exact B1122783
  · exact B1122787
  · exact B1122791
  · exact B1122795
  · exact B1122799
  · exact B1122803
  · exact B1122807
  · exact B1122811
  · exact B1122815
  · exact B1122819
  · exact B1122823
  · exact B1122827
  · exact B1122831
  · exact B1122835
  · exact B1122839
  · exact B1122843
  · exact B1122847
  · exact B1122851
  · exact B1122855
  · exact B1122859
  · exact B1122863
  · exact B1122867
  · exact B1122871
  · exact B1122875
  · exact B1122879
  · exact B1122883
  · exact B1122887
  · exact B1122891
  · exact B1122895
  · exact B1122899
  · exact B1122903
  · exact B1122907
  · exact B1122911
  · exact B1122915
  · exact B1122919
  · exact B1122923
  · exact B1122927
  · exact B1122931
  · exact B1122935
  · exact B1122939
  · exact B1122943
  · exact B1122947
  · exact B1122951
  · exact B1122955
  · exact B1122959
  · exact B1122963
  · exact B1122967
  · exact B1122971
  · exact B1122975
  · exact B1122979
  · exact B1122983
  · exact B1122987
  · exact B1122991
  · exact B1122995
  · exact B1122999
  · exact B1123003
  · exact B1123007
  · exact B1123011
  · exact B1123015
  · exact B1123019
  · exact B1123023
  · exact B1123027
  · exact B1123031
  · exact B1123035
  · exact B1123039
  · exact B1123043
  · exact B1123047
  · exact B1123051
  · exact B1123055
  · exact B1123059
  · exact B1123063
  · exact B1123067
  · exact B1123071
  · exact B1123075
  · exact B1123079
  · exact B1123083
  · exact B1123087
  · exact B1123091
  · exact B1123095
  · exact B1123099
  · exact B1123103
  · exact B1123107
  · exact B1123111
  · exact B1123115
  · exact B1123119
  · exact B1123123
  · exact B1123127
  · exact B1123131
  · exact B1123135
  · exact B1123139
  · exact B1123143
  · exact B1123147
  · exact B1123151
  · exact B1123155
  · exact B1123159
  · exact B1123163
  · exact B1123167
  · exact B1123171
  · exact B1123175
  · exact B1123179
  · exact B1123183
  · exact B1123187
  · exact B1123191
  · exact B1123195
  · exact B1123199
  · exact B1123203
  · exact B1123207
  · exact B1123211
  · exact B1123215
  · exact B1123219
  · exact B1123223
  · exact B1123227
  · exact B1123231
  · exact B1123235
  · exact B1123239
  · exact B1123243
  · exact B1123247
  · exact B1123251
  · exact B1123255
  · exact B1123259
  · exact B1123263
  · exact B1123267
  · exact B1123271
  · exact B1123275
  · exact B1123279
  · exact B1123283
  · exact B1123287
  · exact B1123291
  · exact B1123295
  · exact B1123299
  · exact B1123303
  · exact B1123307
  · exact B1123311
  · exact B1123315
  · exact B1123319
  · exact B1123323
  · exact B1123327
  · exact B1123331
  · exact B1123335
  · exact B1123339
  · exact B1123343
  · exact B1123347
  · exact B1123351
  · exact B1123355
  · exact B1123359
  · exact B1123363
  · exact B1123367
  · exact B1123371
  · exact B1123375
  · exact B1123379
  · exact B1123383
  · exact B1123387
  · exact B1123391
  · exact B1123395
  · exact B1123399
  · exact B1123403
  · exact B1123407
  · exact B1123411
  · exact B1123415
  · exact B1123419
  · exact B1123423
  · exact B1123427

theorem C1 (j : ℕ) (h1 : 280857 ≤ j) (h2 : j ≤ 281156) : Blo 1120629 (4 * j + 3) := by
  interval_cases j
  · exact B1123431
  · exact B1123435
  · exact B1123439
  · exact B1123443
  · exact B1123447
  · exact B1123451
  · exact B1123455
  · exact B1123459
  · exact B1123463
  · exact B1123467
  · exact B1123471
  · exact B1123475
  · exact B1123479
  · exact B1123483
  · exact B1123487
  · exact B1123491
  · exact B1123495
  · exact B1123499
  · exact B1123503
  · exact B1123507
  · exact B1123511
  · exact B1123515
  · exact B1123519
  · exact B1123523
  · exact B1123527
  · exact B1123531
  · exact B1123535
  · exact B1123539
  · exact B1123543
  · exact B1123547
  · exact B1123551
  · exact B1123555
  · exact B1123559
  · exact B1123563
  · exact B1123567
  · exact B1123571
  · exact B1123575
  · exact B1123579
  · exact B1123583
  · exact B1123587
  · exact B1123591
  · exact B1123595
  · exact B1123599
  · exact B1123603
  · exact B1123607
  · exact B1123611
  · exact B1123615
  · exact B1123619
  · exact B1123623
  · exact B1123627
  · exact B1123631
  · exact B1123635
  · exact B1123639
  · exact B1123643
  · exact B1123647
  · exact B1123651
  · exact B1123655
  · exact B1123659
  · exact B1123663
  · exact B1123667
  · exact B1123671
  · exact B1123675
  · exact B1123679
  · exact B1123683
  · exact B1123687
  · exact B1123691
  · exact B1123695
  · exact B1123699
  · exact B1123703
  · exact B1123707
  · exact B1123711
  · exact B1123715
  · exact B1123719
  · exact B1123723
  · exact B1123727
  · exact B1123731
  · exact B1123735
  · exact B1123739
  · exact B1123743
  · exact B1123747
  · exact B1123751
  · exact B1123755
  · exact B1123759
  · exact B1123763
  · exact B1123767
  · exact B1123771
  · exact B1123775
  · exact B1123779
  · exact B1123783
  · exact B1123787
  · exact B1123791
  · exact B1123795
  · exact B1123799
  · exact B1123803
  · exact B1123807
  · exact B1123811
  · exact B1123815
  · exact B1123819
  · exact B1123823
  · exact B1123827
  · exact B1123831
  · exact B1123835
  · exact B1123839
  · exact B1123843
  · exact B1123847
  · exact B1123851
  · exact B1123855
  · exact B1123859
  · exact B1123863
  · exact B1123867
  · exact B1123871
  · exact B1123875
  · exact B1123879
  · exact B1123883
  · exact B1123887
  · exact B1123891
  · exact B1123895
  · exact B1123899
  · exact B1123903
  · exact B1123907
  · exact B1123911
  · exact B1123915
  · exact B1123919
  · exact B1123923
  · exact B1123927
  · exact B1123931
  · exact B1123935
  · exact B1123939
  · exact B1123943
  · exact B1123947
  · exact B1123951
  · exact B1123955
  · exact B1123959
  · exact B1123963
  · exact B1123967
  · exact B1123971
  · exact B1123975
  · exact B1123979
  · exact B1123983
  · exact B1123987
  · exact B1123991
  · exact B1123995
  · exact B1123999
  · exact B1124003
  · exact B1124007
  · exact B1124011
  · exact B1124015
  · exact B1124019
  · exact B1124023
  · exact B1124027
  · exact B1124031
  · exact B1124035
  · exact B1124039
  · exact B1124043
  · exact B1124047
  · exact B1124051
  · exact B1124055
  · exact B1124059
  · exact B1124063
  · exact B1124067
  · exact B1124071
  · exact B1124075
  · exact B1124079
  · exact B1124083
  · exact B1124087
  · exact B1124091
  · exact B1124095
  · exact B1124099
  · exact B1124103
  · exact B1124107
  · exact B1124111
  · exact B1124115
  · exact B1124119
  · exact B1124123
  · exact B1124127
  · exact B1124131
  · exact B1124135
  · exact B1124139
  · exact B1124143
  · exact B1124147
  · exact B1124151
  · exact B1124155
  · exact B1124159
  · exact B1124163
  · exact B1124167
  · exact B1124171
  · exact B1124175
  · exact B1124179
  · exact B1124183
  · exact B1124187
  · exact B1124191
  · exact B1124195
  · exact B1124199
  · exact B1124203
  · exact B1124207
  · exact B1124211
  · exact B1124215
  · exact B1124219
  · exact B1124223
  · exact B1124227
  · exact B1124231
  · exact B1124235
  · exact B1124239
  · exact B1124243
  · exact B1124247
  · exact B1124251
  · exact B1124255
  · exact B1124259
  · exact B1124263
  · exact B1124267
  · exact B1124271
  · exact B1124275
  · exact B1124279
  · exact B1124283
  · exact B1124287
  · exact B1124291
  · exact B1124295
  · exact B1124299
  · exact B1124303
  · exact B1124307
  · exact B1124311
  · exact B1124315
  · exact B1124319
  · exact B1124323
  · exact B1124327
  · exact B1124331
  · exact B1124335
  · exact B1124339
  · exact B1124343
  · exact B1124347
  · exact B1124351
  · exact B1124355
  · exact B1124359
  · exact B1124363
  · exact B1124367
  · exact B1124371
  · exact B1124375
  · exact B1124379
  · exact B1124383
  · exact B1124387
  · exact B1124391
  · exact B1124395
  · exact B1124399
  · exact B1124403
  · exact B1124407
  · exact B1124411
  · exact B1124415
  · exact B1124419
  · exact B1124423
  · exact B1124427
  · exact B1124431
  · exact B1124435
  · exact B1124439
  · exact B1124443
  · exact B1124447
  · exact B1124451
  · exact B1124455
  · exact B1124459
  · exact B1124463
  · exact B1124467
  · exact B1124471
  · exact B1124475
  · exact B1124479
  · exact B1124483
  · exact B1124487
  · exact B1124491
  · exact B1124495
  · exact B1124499
  · exact B1124503
  · exact B1124507
  · exact B1124511
  · exact B1124515
  · exact B1124519
  · exact B1124523
  · exact B1124527
  · exact B1124531
  · exact B1124535
  · exact B1124539
  · exact B1124543
  · exact B1124547
  · exact B1124551
  · exact B1124555
  · exact B1124559
  · exact B1124563
  · exact B1124567
  · exact B1124571
  · exact B1124575
  · exact B1124579
  · exact B1124583
  · exact B1124587
  · exact B1124591
  · exact B1124595
  · exact B1124599
  · exact B1124603
  · exact B1124607
  · exact B1124611
  · exact B1124615
  · exact B1124619
  · exact B1124623
  · exact B1124627

theorem solution (m : ℕ) (hlo : 1120629 ≤ m) (hhi : m ≤ 1124629) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 280157 ≤ j := by omega
    have hj2 : j ≤ 281156 := by omega
    have hb : Blo 1120629 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 280857 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
