-- Prove2me | solution 1 for syracuse_descends_range_790340_794340
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:34.075911+00:00
-- url     : https://prove2.me/submissions/45a67770-892e-4409-8564-f233f41306b6

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


theorem B8257589 : Blo 790340 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B1507405 : Blo 790340 1507405 := bbase (se 3 (by rfl) ⟨282638, by rfl⟩ : syracuseStep 1507405 = 565277) (by norm_num)
theorem B1900709 : Blo 790340 1900709 := bbase (se 4 (by rfl) ⟨178191, by rfl⟩ : syracuseStep 1900709 = 356383) (by norm_num)
theorem B2031797 : Blo 790340 2031797 := bbase (se 5 (by rfl) ⟨95240, by rfl⟩ : syracuseStep 2031797 = 190481) (by norm_num)
theorem B1507565 : Blo 790340 1507565 := bbase (se 3 (by rfl) ⟨282668, by rfl⟩ : syracuseStep 1507565 = 565337) (by norm_num)
theorem B2031877 : Blo 790340 2031877 := bbase (se 4 (by rfl) ⟨190488, by rfl⟩ : syracuseStep 2031877 = 380977) (by norm_num)
theorem B1507709 : Blo 790340 1507709 := bbase (se 3 (by rfl) ⟨282695, by rfl⟩ : syracuseStep 1507709 = 565391) (by norm_num)
theorem B1901045 : Blo 790340 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B1901141 : Blo 790340 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B950897 : Blo 790340 950897 := bbase (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) (by norm_num)
theorem B2261621 : Blo 790340 2261621 := bbase (se 5 (by rfl) ⟨106013, by rfl⟩ : syracuseStep 2261621 = 212027) (by norm_num)
theorem B1507997 : Blo 790340 1507997 := bbase (se 3 (by rfl) ⟨282749, by rfl⟩ : syracuseStep 1507997 = 565499) (by norm_num)
theorem B1901333 : Blo 790340 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B1737509 : Blo 790340 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B1835909 : Blo 790340 1835909 := bbase (se 4 (by rfl) ⟨172116, by rfl⟩ : syracuseStep 1835909 = 344233) (by norm_num)
theorem B951205 : Blo 790340 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B951301 : Blo 790340 951301 := bbase (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) (by norm_num)
theorem B3376181 : Blo 790340 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B1803541 : Blo 790340 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B4818197 : Blo 790340 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B951589 : Blo 790340 951589 := bbase (se 4 (by rfl) ⟨89211, by rfl⟩ : syracuseStep 951589 = 178423) (by norm_num)
theorem B1803653 : Blo 790340 1803653 := bbase (se 4 (by rfl) ⟨169092, by rfl⟩ : syracuseStep 1803653 = 338185) (by norm_num)
theorem B6030773 : Blo 790340 6030773 := bbase (se 5 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 6030773 = 565385) (by norm_num)
theorem B951781 : Blo 790340 951781 := bbase (se 4 (by rfl) ⟨89229, by rfl⟩ : syracuseStep 951781 = 178459) (by norm_num)
theorem B1607357 : Blo 790340 1607357 := bbase (se 3 (by rfl) ⟨301379, by rfl⟩ : syracuseStep 1607357 = 602759) (by norm_num)
theorem B3606245 : Blo 790340 3606245 := bbase (se 4 (by rfl) ⟨338085, by rfl⟩ : syracuseStep 3606245 = 676171) (by norm_num)
theorem B1902485 : Blo 790340 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B5146517 : Blo 790340 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B2000821 : Blo 790340 2000821 := bbase (se 5 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 2000821 = 187577) (by norm_num)
theorem B2754485 : Blo 790340 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B3803125 : Blo 790340 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B3377173 : Blo 790340 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B2000933 : Blo 790340 2000933 := bbase (se 4 (by rfl) ⟨187587, by rfl⟩ : syracuseStep 2000933 = 375175) (by norm_num)
theorem B2852981 : Blo 790340 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B7604405 : Blo 790340 7604405 := bbase (se 5 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 7604405 = 712913) (by norm_num)
theorem B2001125 : Blo 790340 2001125 := bbase (se 4 (by rfl) ⟨187605, by rfl⟩ : syracuseStep 2001125 = 375211) (by norm_num)
theorem B952661 : Blo 790340 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B2034013 : Blo 790340 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B2853413 : Blo 790340 2853413 := bbase (se 4 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 2853413 = 535015) (by norm_num)
theorem B2034229 : Blo 790340 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B2001469 : Blo 790340 2001469 := bbase (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) (by norm_num)
theorem B2001581 : Blo 790340 2001581 := bbase (se 3 (by rfl) ⟨375296, by rfl⟩ : syracuseStep 2001581 = 750593) (by norm_num)
theorem B953165 : Blo 790340 953165 := bbase (se 3 (by rfl) ⟨178718, by rfl⟩ : syracuseStep 953165 = 357437) (by norm_num)
theorem B2001773 : Blo 790340 2001773 := bbase (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) (by norm_num)
theorem B953213 : Blo 790340 953213 := bbase (se 3 (by rfl) ⟨178727, by rfl⟩ : syracuseStep 953213 = 357455) (by norm_num)
theorem B1805365 : Blo 790340 1805365 := bbase (se 5 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 1805365 = 169253) (by norm_num)
theorem B953473 : Blo 790340 953473 := bbase (se 2 (by rfl) ⟨357552, by rfl⟩ : syracuseStep 953473 = 715105) (by norm_num)
theorem B2002117 : Blo 790340 2002117 := bbase (se 4 (by rfl) ⟨187698, by rfl⟩ : syracuseStep 2002117 = 375397) (by norm_num)
theorem B2002229 : Blo 790340 2002229 := bbase (se 5 (by rfl) ⟨93854, by rfl⟩ : syracuseStep 2002229 = 187709) (by norm_num)
theorem B953737 : Blo 790340 953737 := bbase (se 2 (by rfl) ⟨357651, by rfl⟩ : syracuseStep 953737 = 715303) (by norm_num)
theorem B4001237 : Blo 790340 4001237 := bbase (se 7 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 4001237 = 93779) (by norm_num)
theorem B6852053 : Blo 790340 6852053 := bbase (se 7 (by rfl) ⟨80297, by rfl⟩ : syracuseStep 6852053 = 160595) (by norm_num)
theorem B2002421 : Blo 790340 2002421 := bbase (se 5 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 2002421 = 187727) (by norm_num)
theorem B1609205 : Blo 790340 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B953857 : Blo 790340 953857 := bbase (se 2 (by rfl) ⟨357696, by rfl⟩ : syracuseStep 953857 = 715393) (by norm_num)
theorem B3051173 : Blo 790340 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B2002765 : Blo 790340 2002765 := bbase (se 3 (by rfl) ⟨375518, by rfl⟩ : syracuseStep 2002765 = 751037) (by norm_num)
theorem B1904485 : Blo 790340 1904485 := bbase (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) (by norm_num)
theorem B2002877 : Blo 790340 2002877 := bbase (se 3 (by rfl) ⟨375539, by rfl⟩ : syracuseStep 2002877 = 751079) (by norm_num)
theorem B1904581 : Blo 790340 1904581 := bbase (se 4 (by rfl) ⟨178554, by rfl⟩ : syracuseStep 1904581 = 357109) (by norm_num)
theorem B2003069 : Blo 790340 2003069 := bbase (se 3 (by rfl) ⟨375575, by rfl⟩ : syracuseStep 2003069 = 751151) (by norm_num)
theorem B6754549 : Blo 790340 6754549 := bbase (se 5 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 6754549 = 633239) (by norm_num)
theorem B889141 : Blo 790340 889141 := bbase (se 5 (by rfl) ⟨41678, by rfl⟩ : syracuseStep 889141 = 83357) (by norm_num)
theorem B889177 : Blo 790340 889177 := bbase (se 2 (by rfl) ⟨333441, by rfl⟩ : syracuseStep 889177 = 666883) (by norm_num)
theorem B889213 : Blo 790340 889213 := bbase (se 3 (by rfl) ⟨166727, by rfl⟩ : syracuseStep 889213 = 333455) (by norm_num)
theorem B889249 : Blo 790340 889249 := bbase (se 2 (by rfl) ⟨333468, by rfl⟩ : syracuseStep 889249 = 666937) (by norm_num)
theorem B889285 : Blo 790340 889285 := bbase (se 4 (by rfl) ⟨83370, by rfl⟩ : syracuseStep 889285 = 166741) (by norm_num)
theorem B2003413 : Blo 790340 2003413 := bbase (se 7 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 2003413 = 46955) (by norm_num)
theorem B889321 : Blo 790340 889321 := bbase (se 2 (by rfl) ⟨333495, by rfl⟩ : syracuseStep 889321 = 666991) (by norm_num)
theorem B889357 : Blo 790340 889357 := bbase (se 3 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 889357 = 333509) (by norm_num)
theorem B889393 : Blo 790340 889393 := bbase (se 2 (by rfl) ⟨333522, by rfl⟩ : syracuseStep 889393 = 667045) (by norm_num)
theorem B2003525 : Blo 790340 2003525 := bbase (se 4 (by rfl) ⟨187830, by rfl⟩ : syracuseStep 2003525 = 375661) (by norm_num)
theorem B889429 : Blo 790340 889429 := bbase (se 8 (by rfl) ⟨5211, by rfl⟩ : syracuseStep 889429 = 10423) (by norm_num)
theorem B889465 : Blo 790340 889465 := bbase (se 2 (by rfl) ⟨333549, by rfl⟩ : syracuseStep 889465 = 667099) (by norm_num)
theorem B889501 : Blo 790340 889501 := bbase (se 3 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 889501 = 333563) (by norm_num)
theorem B889537 : Blo 790340 889537 := bbase (se 2 (by rfl) ⟨333576, by rfl⟩ : syracuseStep 889537 = 667153) (by norm_num)
theorem B6427349 : Blo 790340 6427349 := bbase (se 7 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 6427349 = 150641) (by norm_num)
theorem B4002533 : Blo 790340 4002533 := bbase (se 4 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 4002533 = 750475) (by norm_num)
theorem B889573 : Blo 790340 889573 := bbase (se 4 (by rfl) ⟨83397, by rfl⟩ : syracuseStep 889573 = 166795) (by norm_num)
theorem B2036477 : Blo 790340 2036477 := bbase (se 3 (by rfl) ⟨381839, by rfl⟩ : syracuseStep 2036477 = 763679) (by norm_num)
theorem B2003717 : Blo 790340 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B889609 : Blo 790340 889609 := bbase (se 2 (by rfl) ⟨333603, by rfl⟩ : syracuseStep 889609 = 667207) (by norm_num)
theorem B3805973 : Blo 790340 3805973 := bbase (se 6 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 3805973 = 178405) (by norm_num)
theorem B889645 : Blo 790340 889645 := bbase (se 3 (by rfl) ⟨166808, by rfl⟩ : syracuseStep 889645 = 333617) (by norm_num)
theorem B889681 : Blo 790340 889681 := bbase (se 2 (by rfl) ⟨333630, by rfl⟩ : syracuseStep 889681 = 667261) (by norm_num)
theorem B889717 : Blo 790340 889717 := bbase (se 5 (by rfl) ⟨41705, by rfl⟩ : syracuseStep 889717 = 83411) (by norm_num)
theorem B889753 : Blo 790340 889753 := bbase (se 2 (by rfl) ⟨333657, by rfl⟩ : syracuseStep 889753 = 667315) (by norm_num)
theorem B889789 : Blo 790340 889789 := bbase (se 3 (by rfl) ⟨166835, by rfl⟩ : syracuseStep 889789 = 333671) (by norm_num)
theorem B2036701 : Blo 790340 2036701 := bbase (se 3 (by rfl) ⟨381881, by rfl⟩ : syracuseStep 2036701 = 763763) (by norm_num)
theorem B889825 : Blo 790340 889825 := bbase (se 2 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 889825 = 667369) (by norm_num)
theorem B889861 : Blo 790340 889861 := bbase (se 4 (by rfl) ⟨83424, by rfl⟩ : syracuseStep 889861 = 166849) (by norm_num)
theorem B1905677 : Blo 790340 1905677 := bbase (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) (by norm_num)
theorem B889897 : Blo 790340 889897 := bbase (se 2 (by rfl) ⟨333711, by rfl⟩ : syracuseStep 889897 = 667423) (by norm_num)
theorem B889933 : Blo 790340 889933 := bbase (se 3 (by rfl) ⟨166862, by rfl⟩ : syracuseStep 889933 = 333725) (by norm_num)
theorem B2004061 : Blo 790340 2004061 := bbase (se 3 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 2004061 = 751523) (by norm_num)
theorem B889969 : Blo 790340 889969 := bbase (se 2 (by rfl) ⟨333738, by rfl⟩ : syracuseStep 889969 = 667477) (by norm_num)
theorem B890005 : Blo 790340 890005 := bbase (se 6 (by rfl) ⟨20859, by rfl⟩ : syracuseStep 890005 = 41719) (by norm_num)
theorem B890041 : Blo 790340 890041 := bbase (se 2 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 890041 = 667531) (by norm_num)
theorem B2004173 : Blo 790340 2004173 := bbase (se 3 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 2004173 = 751565) (by norm_num)
theorem B890077 : Blo 790340 890077 := bbase (se 3 (by rfl) ⟨166889, by rfl⟩ : syracuseStep 890077 = 333779) (by norm_num)
theorem B2856181 : Blo 790340 2856181 := bbase (se 5 (by rfl) ⟨133883, by rfl⟩ : syracuseStep 2856181 = 267767) (by norm_num)
theorem B890113 : Blo 790340 890113 := bbase (se 2 (by rfl) ⟨333792, by rfl⟩ : syracuseStep 890113 = 667585) (by norm_num)
theorem B890149 : Blo 790340 890149 := bbase (se 4 (by rfl) ⟨83451, by rfl⟩ : syracuseStep 890149 = 166903) (by norm_num)
theorem B890185 : Blo 790340 890185 := bbase (se 2 (by rfl) ⟨333819, by rfl⟩ : syracuseStep 890185 = 667639) (by norm_num)
theorem B890221 : Blo 790340 890221 := bbase (se 3 (by rfl) ⟨166916, by rfl⟩ : syracuseStep 890221 = 333833) (by norm_num)
theorem B2004365 : Blo 790340 2004365 := bbase (se 3 (by rfl) ⟨375818, by rfl⟩ : syracuseStep 2004365 = 751637) (by norm_num)
theorem B890257 : Blo 790340 890257 := bbase (se 2 (by rfl) ⟨333846, by rfl⟩ : syracuseStep 890257 = 667693) (by norm_num)
theorem B890293 : Blo 790340 890293 := bbase (se 5 (by rfl) ⟨41732, by rfl⟩ : syracuseStep 890293 = 83465) (by norm_num)
theorem B890329 : Blo 790340 890329 := bbase (se 2 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 890329 = 667747) (by norm_num)
theorem B890365 : Blo 790340 890365 := bbase (se 3 (by rfl) ⟨166943, by rfl⟩ : syracuseStep 890365 = 333887) (by norm_num)
theorem B890401 : Blo 790340 890401 := bbase (se 2 (by rfl) ⟨333900, by rfl⟩ : syracuseStep 890401 = 667801) (by norm_num)
theorem B2856485 : Blo 790340 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B890437 : Blo 790340 890437 := bbase (se 4 (by rfl) ⟨83478, by rfl⟩ : syracuseStep 890437 = 166957) (by norm_num)
theorem B890473 : Blo 790340 890473 := bbase (se 2 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 890473 = 667855) (by norm_num)
theorem B890509 : Blo 790340 890509 := bbase (se 3 (by rfl) ⟨166970, by rfl⟩ : syracuseStep 890509 = 333941) (by norm_num)
theorem B890545 : Blo 790340 890545 := bbase (se 2 (by rfl) ⟨333954, by rfl⟩ : syracuseStep 890545 = 667909) (by norm_num)
theorem B890581 : Blo 790340 890581 := bbase (se 7 (by rfl) ⟨10436, by rfl⟩ : syracuseStep 890581 = 20873) (by norm_num)
theorem B2004709 : Blo 790340 2004709 := bbase (se 4 (by rfl) ⟨187941, by rfl⟩ : syracuseStep 2004709 = 375883) (by norm_num)
theorem B890617 : Blo 790340 890617 := bbase (se 2 (by rfl) ⟨333981, by rfl⟩ : syracuseStep 890617 = 667963) (by norm_num)
theorem B1185533 : Blo 790340 1185533 := bbase (se 3 (by rfl) ⟨222287, by rfl⟩ : syracuseStep 1185533 = 444575) (by norm_num)
theorem B1185557 : Blo 790340 1185557 := bbase (se 6 (by rfl) ⟨27786, by rfl⟩ : syracuseStep 1185557 = 55573) (by norm_num)
theorem B890653 : Blo 790340 890653 := bbase (se 3 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 890653 = 333995) (by norm_num)
theorem B1185581 : Blo 790340 1185581 := bbase (se 3 (by rfl) ⟨222296, by rfl⟩ : syracuseStep 1185581 = 444593) (by norm_num)
theorem B5084981 : Blo 790340 5084981 := bbase (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) (by norm_num)
theorem B890689 : Blo 790340 890689 := bbase (se 2 (by rfl) ⟨334008, by rfl⟩ : syracuseStep 890689 = 668017) (by norm_num)
theorem B1185605 : Blo 790340 1185605 := bbase (se 4 (by rfl) ⟨111150, by rfl⟩ : syracuseStep 1185605 = 222301) (by norm_num)
theorem B2004821 : Blo 790340 2004821 := bbase (se 9 (by rfl) ⟨5873, by rfl⟩ : syracuseStep 2004821 = 11747) (by norm_num)
theorem B1185629 : Blo 790340 1185629 := bbase (se 3 (by rfl) ⟨222305, by rfl⟩ : syracuseStep 1185629 = 444611) (by norm_num)
theorem B890725 : Blo 790340 890725 := bbase (se 4 (by rfl) ⟨83505, by rfl⟩ : syracuseStep 890725 = 167011) (by norm_num)
theorem B1185653 : Blo 790340 1185653 := bbase (se 5 (by rfl) ⟨55577, by rfl⟩ : syracuseStep 1185653 = 111155) (by norm_num)
theorem B890761 : Blo 790340 890761 := bbase (se 2 (by rfl) ⟨334035, by rfl⟩ : syracuseStep 890761 = 668071) (by norm_num)
theorem B1185677 : Blo 790340 1185677 := bbase (se 3 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 1185677 = 444629) (by norm_num)
theorem B1185701 : Blo 790340 1185701 := bbase (se 4 (by rfl) ⟨111159, by rfl⟩ : syracuseStep 1185701 = 222319) (by norm_num)
theorem B890797 : Blo 790340 890797 := bbase (se 3 (by rfl) ⟨167024, by rfl⟩ : syracuseStep 890797 = 334049) (by norm_num)
theorem B1185725 : Blo 790340 1185725 := bbase (se 3 (by rfl) ⟨222323, by rfl⟩ : syracuseStep 1185725 = 444647) (by norm_num)
theorem B1906637 : Blo 790340 1906637 := bbase (se 3 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 1906637 = 714989) (by norm_num)
theorem B890833 : Blo 790340 890833 := bbase (se 2 (by rfl) ⟨334062, by rfl⟩ : syracuseStep 890833 = 668125) (by norm_num)
theorem B1185749 : Blo 790340 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B1185773 : Blo 790340 1185773 := bbase (se 3 (by rfl) ⟨222332, by rfl⟩ : syracuseStep 1185773 = 444665) (by norm_num)
theorem B4003829 : Blo 790340 4003829 := bbase (se 5 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 4003829 = 375359) (by norm_num)
theorem B890869 : Blo 790340 890869 := bbase (se 5 (by rfl) ⟨41759, by rfl⟩ : syracuseStep 890869 = 83519) (by norm_num)
theorem B1185797 : Blo 790340 1185797 := bbase (se 4 (by rfl) ⟨111168, by rfl⟩ : syracuseStep 1185797 = 222337) (by norm_num)
theorem B2005013 : Blo 790340 2005013 := bbase (se 6 (by rfl) ⟨46992, by rfl⟩ : syracuseStep 2005013 = 93985) (by norm_num)
theorem B890905 : Blo 790340 890905 := bbase (se 2 (by rfl) ⟨334089, by rfl⟩ : syracuseStep 890905 = 668179) (by norm_num)
theorem B1185821 : Blo 790340 1185821 := bbase (se 3 (by rfl) ⟨222341, by rfl⟩ : syracuseStep 1185821 = 444683) (by norm_num)
theorem B1185845 : Blo 790340 1185845 := bbase (se 5 (by rfl) ⟨55586, by rfl⟩ : syracuseStep 1185845 = 111173) (by norm_num)
theorem B890941 : Blo 790340 890941 := bbase (se 3 (by rfl) ⟨167051, by rfl⟩ : syracuseStep 890941 = 334103) (by norm_num)
theorem B1185869 : Blo 790340 1185869 := bbase (se 3 (by rfl) ⟨222350, by rfl⟩ : syracuseStep 1185869 = 444701) (by norm_num)
theorem B3807317 : Blo 790340 3807317 := bbase (se 8 (by rfl) ⟨22308, by rfl⟩ : syracuseStep 3807317 = 44617) (by norm_num)
theorem B890977 : Blo 790340 890977 := bbase (se 2 (by rfl) ⟨334116, by rfl⟩ : syracuseStep 890977 = 668233) (by norm_num)
theorem B1185893 : Blo 790340 1185893 := bbase (se 4 (by rfl) ⟨111177, by rfl⟩ : syracuseStep 1185893 = 222355) (by norm_num)
theorem B1185917 : Blo 790340 1185917 := bbase (se 3 (by rfl) ⟨222359, by rfl⟩ : syracuseStep 1185917 = 444719) (by norm_num)
theorem B891013 : Blo 790340 891013 := bbase (se 4 (by rfl) ⟨83532, by rfl⟩ : syracuseStep 891013 = 167065) (by norm_num)
theorem B1185941 : Blo 790340 1185941 := bbase (se 6 (by rfl) ⟨27795, by rfl⟩ : syracuseStep 1185941 = 55591) (by norm_num)
theorem B891049 : Blo 790340 891049 := bbase (se 2 (by rfl) ⟨334143, by rfl⟩ : syracuseStep 891049 = 668287) (by norm_num)
theorem B1185965 : Blo 790340 1185965 := bbase (se 3 (by rfl) ⟨222368, by rfl⟩ : syracuseStep 1185965 = 444737) (by norm_num)
theorem B6756533 : Blo 790340 6756533 := bbase (se 5 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 6756533 = 633425) (by norm_num)
theorem B1185989 : Blo 790340 1185989 := bbase (se 4 (by rfl) ⟨111186, by rfl⟩ : syracuseStep 1185989 = 222373) (by norm_num)
theorem B891085 : Blo 790340 891085 := bbase (se 3 (by rfl) ⟨167078, by rfl⟩ : syracuseStep 891085 = 334157) (by norm_num)
theorem B1186013 : Blo 790340 1186013 := bbase (se 3 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 1186013 = 444755) (by norm_num)
theorem B891121 : Blo 790340 891121 := bbase (se 2 (by rfl) ⟨334170, by rfl⟩ : syracuseStep 891121 = 668341) (by norm_num)
theorem B1186037 : Blo 790340 1186037 := bbase (se 5 (by rfl) ⟨55595, by rfl⟩ : syracuseStep 1186037 = 111191) (by norm_num)
theorem B1186061 : Blo 790340 1186061 := bbase (se 3 (by rfl) ⟨222386, by rfl⟩ : syracuseStep 1186061 = 444773) (by norm_num)
theorem B891157 : Blo 790340 891157 := bbase (se 6 (by rfl) ⟨20886, by rfl⟩ : syracuseStep 891157 = 41773) (by norm_num)
theorem B1186085 : Blo 790340 1186085 := bbase (se 4 (by rfl) ⟨111195, by rfl⟩ : syracuseStep 1186085 = 222391) (by norm_num)
theorem B891193 : Blo 790340 891193 := bbase (se 2 (by rfl) ⟨334197, by rfl⟩ : syracuseStep 891193 = 668395) (by norm_num)
theorem B1186109 : Blo 790340 1186109 := bbase (se 3 (by rfl) ⟨222395, by rfl⟩ : syracuseStep 1186109 = 444791) (by norm_num)
theorem B10819925 : Blo 790340 10819925 := bbase (se 10 (by rfl) ⟨15849, by rfl⟩ : syracuseStep 10819925 = 31699) (by norm_num)
theorem B1186133 : Blo 790340 1186133 := bbase (se 10 (by rfl) ⟨1737, by rfl⟩ : syracuseStep 1186133 = 3475) (by norm_num)
theorem B8690005 : Blo 790340 8690005 := bbase (se 10 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 8690005 = 25459) (by norm_num)
theorem B891229 : Blo 790340 891229 := bbase (se 3 (by rfl) ⟨167105, by rfl⟩ : syracuseStep 891229 = 334211) (by norm_num)
theorem B1186157 : Blo 790340 1186157 := bbase (se 3 (by rfl) ⟨222404, by rfl⟩ : syracuseStep 1186157 = 444809) (by norm_num)
theorem B2005357 : Blo 790340 2005357 := bbase (se 3 (by rfl) ⟨376004, by rfl⟩ : syracuseStep 2005357 = 752009) (by norm_num)
theorem B891265 : Blo 790340 891265 := bbase (se 2 (by rfl) ⟨334224, by rfl⟩ : syracuseStep 891265 = 668449) (by norm_num)
theorem B1186181 : Blo 790340 1186181 := bbase (se 4 (by rfl) ⟨111204, by rfl⟩ : syracuseStep 1186181 = 222409) (by norm_num)
theorem B10164629 : Blo 790340 10164629 := bbase (se 6 (by rfl) ⟨238233, by rfl⟩ : syracuseStep 10164629 = 476467) (by norm_num)
theorem B1186205 : Blo 790340 1186205 := bbase (se 3 (by rfl) ⟨222413, by rfl⟩ : syracuseStep 1186205 = 444827) (by norm_num)
theorem B891301 : Blo 790340 891301 := bbase (se 4 (by rfl) ⟨83559, by rfl⟩ : syracuseStep 891301 = 167119) (by norm_num)
theorem B1186229 : Blo 790340 1186229 := bbase (se 5 (by rfl) ⟨55604, by rfl⟩ : syracuseStep 1186229 = 111209) (by norm_num)
theorem B891337 : Blo 790340 891337 := bbase (se 2 (by rfl) ⟨334251, by rfl⟩ : syracuseStep 891337 = 668503) (by norm_num)
theorem B1186253 : Blo 790340 1186253 := bbase (se 3 (by rfl) ⟨222422, by rfl⟩ : syracuseStep 1186253 = 444845) (by norm_num)
theorem B2005469 : Blo 790340 2005469 := bbase (se 3 (by rfl) ⟨376025, by rfl⟩ : syracuseStep 2005469 = 752051) (by norm_num)
theorem B1186277 : Blo 790340 1186277 := bbase (se 4 (by rfl) ⟨111213, by rfl⟩ : syracuseStep 1186277 = 222427) (by norm_num)
theorem B891373 : Blo 790340 891373 := bbase (se 3 (by rfl) ⟨167132, by rfl⟩ : syracuseStep 891373 = 334265) (by norm_num)
theorem B1186301 : Blo 790340 1186301 := bbase (se 3 (by rfl) ⟨222431, by rfl⟩ : syracuseStep 1186301 = 444863) (by norm_num)
theorem B891409 : Blo 790340 891409 := bbase (se 2 (by rfl) ⟨334278, by rfl⟩ : syracuseStep 891409 = 668557) (by norm_num)
theorem B1186325 : Blo 790340 1186325 := bbase (se 6 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 1186325 = 55609) (by norm_num)
theorem B1186349 : Blo 790340 1186349 := bbase (se 3 (by rfl) ⟨222440, by rfl⟩ : syracuseStep 1186349 = 444881) (by norm_num)
theorem B891445 : Blo 790340 891445 := bbase (se 5 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 891445 = 83573) (by norm_num)
theorem B1186373 : Blo 790340 1186373 := bbase (se 4 (by rfl) ⟨111222, by rfl⟩ : syracuseStep 1186373 = 222445) (by norm_num)
theorem B891481 : Blo 790340 891481 := bbase (se 2 (by rfl) ⟨334305, by rfl⟩ : syracuseStep 891481 = 668611) (by norm_num)
theorem B1186397 : Blo 790340 1186397 := bbase (se 3 (by rfl) ⟨222449, by rfl⟩ : syracuseStep 1186397 = 444899) (by norm_num)
theorem B1186421 : Blo 790340 1186421 := bbase (se 5 (by rfl) ⟨55613, by rfl⟩ : syracuseStep 1186421 = 111227) (by norm_num)
theorem B891517 : Blo 790340 891517 := bbase (se 3 (by rfl) ⟨167159, by rfl⟩ : syracuseStep 891517 = 334319) (by norm_num)
theorem B1186445 : Blo 790340 1186445 := bbase (se 3 (by rfl) ⟨222458, by rfl⟩ : syracuseStep 1186445 = 444917) (by norm_num)
theorem B2005661 : Blo 790340 2005661 := bbase (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) (by norm_num)
theorem B891553 : Blo 790340 891553 := bbase (se 2 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 891553 = 668665) (by norm_num)
theorem B1186469 : Blo 790340 1186469 := bbase (se 4 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 1186469 = 222463) (by norm_num)
theorem B989869 : Blo 790340 989869 := bbase (se 3 (by rfl) ⟨185600, by rfl⟩ : syracuseStep 989869 = 371201) (by norm_num)
theorem B1186493 : Blo 790340 1186493 := bbase (se 3 (by rfl) ⟨222467, by rfl⟩ : syracuseStep 1186493 = 444935) (by norm_num)
theorem B891589 : Blo 790340 891589 := bbase (se 4 (by rfl) ⟨83586, by rfl⟩ : syracuseStep 891589 = 167173) (by norm_num)
theorem B1186517 : Blo 790340 1186517 := bbase (se 7 (by rfl) ⟨13904, by rfl⟩ : syracuseStep 1186517 = 27809) (by norm_num)
theorem B891625 : Blo 790340 891625 := bbase (se 2 (by rfl) ⟨334359, by rfl⟩ : syracuseStep 891625 = 668719) (by norm_num)
theorem B1186541 : Blo 790340 1186541 := bbase (se 3 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 1186541 = 444953) (by norm_num)
theorem B1186565 : Blo 790340 1186565 := bbase (se 4 (by rfl) ⟨111240, by rfl⟩ : syracuseStep 1186565 = 222481) (by norm_num)
theorem B891661 : Blo 790340 891661 := bbase (se 3 (by rfl) ⟨167186, by rfl⟩ : syracuseStep 891661 = 334373) (by norm_num)
theorem B1186589 : Blo 790340 1186589 := bbase (se 3 (by rfl) ⟨222485, by rfl⟩ : syracuseStep 1186589 = 444971) (by norm_num)
theorem B891697 : Blo 790340 891697 := bbase (se 2 (by rfl) ⟨334386, by rfl⟩ : syracuseStep 891697 = 668773) (by norm_num)
theorem B1186613 : Blo 790340 1186613 := bbase (se 5 (by rfl) ⟨55622, by rfl⟩ : syracuseStep 1186613 = 111245) (by norm_num)
theorem B1186637 : Blo 790340 1186637 := bbase (se 3 (by rfl) ⟨222494, by rfl⟩ : syracuseStep 1186637 = 444989) (by norm_num)
theorem B891733 : Blo 790340 891733 := bbase (se 9 (by rfl) ⟨2612, by rfl⟩ : syracuseStep 891733 = 5225) (by norm_num)
theorem B1186661 : Blo 790340 1186661 := bbase (se 4 (by rfl) ⟨111249, by rfl⟩ : syracuseStep 1186661 = 222499) (by norm_num)
theorem B891769 : Blo 790340 891769 := bbase (se 2 (by rfl) ⟨334413, by rfl⟩ : syracuseStep 891769 = 668827) (by norm_num)
theorem B1186685 : Blo 790340 1186685 := bbase (se 3 (by rfl) ⟨222503, by rfl⟩ : syracuseStep 1186685 = 445007) (by norm_num)
theorem B859025 : Blo 790340 859025 := bbase (se 2 (by rfl) ⟨322134, by rfl⟩ : syracuseStep 859025 = 644269) (by norm_num)
theorem B1186709 : Blo 790340 1186709 := bbase (se 6 (by rfl) ⟨27813, by rfl⟩ : syracuseStep 1186709 = 55627) (by norm_num)
theorem B891805 : Blo 790340 891805 := bbase (se 3 (by rfl) ⟨167213, by rfl⟩ : syracuseStep 891805 = 334427) (by norm_num)
theorem B3382181 : Blo 790340 3382181 := bbase (se 4 (by rfl) ⟨317079, by rfl⟩ : syracuseStep 3382181 = 634159) (by norm_num)
theorem B1186733 : Blo 790340 1186733 := bbase (se 3 (by rfl) ⟨222512, by rfl⟩ : syracuseStep 1186733 = 445025) (by norm_num)
theorem B891841 : Blo 790340 891841 := bbase (se 2 (by rfl) ⟨334440, by rfl⟩ : syracuseStep 891841 = 668881) (by norm_num)
theorem B1186757 : Blo 790340 1186757 := bbase (se 4 (by rfl) ⟨111258, by rfl⟩ : syracuseStep 1186757 = 222517) (by norm_num)
theorem B1186781 : Blo 790340 1186781 := bbase (se 3 (by rfl) ⟨222521, by rfl⟩ : syracuseStep 1186781 = 445043) (by norm_num)
theorem B891877 : Blo 790340 891877 := bbase (se 4 (by rfl) ⟨83613, by rfl⟩ : syracuseStep 891877 = 167227) (by norm_num)
theorem B1186805 : Blo 790340 1186805 := bbase (se 5 (by rfl) ⟨55631, by rfl⟩ : syracuseStep 1186805 = 111263) (by norm_num)
theorem B2006005 : Blo 790340 2006005 := bbase (se 5 (by rfl) ⟨94031, by rfl⟩ : syracuseStep 2006005 = 188063) (by norm_num)
theorem B891913 : Blo 790340 891913 := bbase (se 2 (by rfl) ⟨334467, by rfl⟩ : syracuseStep 891913 = 668935) (by norm_num)
theorem B1186829 : Blo 790340 1186829 := bbase (se 3 (by rfl) ⟨222530, by rfl⟩ : syracuseStep 1186829 = 445061) (by norm_num)
theorem B1186853 : Blo 790340 1186853 := bbase (se 4 (by rfl) ⟨111267, by rfl⟩ : syracuseStep 1186853 = 222535) (by norm_num)
theorem B891949 : Blo 790340 891949 := bbase (se 3 (by rfl) ⟨167240, by rfl⟩ : syracuseStep 891949 = 334481) (by norm_num)
theorem B1186877 : Blo 790340 1186877 := bbase (se 3 (by rfl) ⟨222539, by rfl⟩ : syracuseStep 1186877 = 445079) (by norm_num)
theorem B891985 : Blo 790340 891985 := bbase (se 2 (by rfl) ⟨334494, by rfl⟩ : syracuseStep 891985 = 668989) (by norm_num)
theorem B1186901 : Blo 790340 1186901 := bbase (se 8 (by rfl) ⟨6954, by rfl⟩ : syracuseStep 1186901 = 13909) (by norm_num)
theorem B2006117 : Blo 790340 2006117 := bbase (se 4 (by rfl) ⟨188073, by rfl⟩ : syracuseStep 2006117 = 376147) (by norm_num)
theorem B1186925 : Blo 790340 1186925 := bbase (se 3 (by rfl) ⟨222548, by rfl⟩ : syracuseStep 1186925 = 445097) (by norm_num)
theorem B892021 : Blo 790340 892021 := bbase (se 5 (by rfl) ⟨41813, by rfl⟩ : syracuseStep 892021 = 83627) (by norm_num)
theorem B1186949 : Blo 790340 1186949 := bbase (se 4 (by rfl) ⟨111276, by rfl⟩ : syracuseStep 1186949 = 222553) (by norm_num)
theorem B892057 : Blo 790340 892057 := bbase (se 2 (by rfl) ⟨334521, by rfl⟩ : syracuseStep 892057 = 669043) (by norm_num)
theorem B1186973 : Blo 790340 1186973 := bbase (se 3 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 1186973 = 445115) (by norm_num)
theorem B1186997 : Blo 790340 1186997 := bbase (se 5 (by rfl) ⟨55640, by rfl⟩ : syracuseStep 1186997 = 111281) (by norm_num)
theorem B892093 : Blo 790340 892093 := bbase (se 3 (by rfl) ⟨167267, by rfl⟩ : syracuseStep 892093 = 334535) (by norm_num)
theorem B3382469 : Blo 790340 3382469 := bbase (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) (by norm_num)
theorem B1187021 : Blo 790340 1187021 := bbase (se 3 (by rfl) ⟨222566, by rfl⟩ : syracuseStep 1187021 = 445133) (by norm_num)
theorem B892129 : Blo 790340 892129 := bbase (se 2 (by rfl) ⟨334548, by rfl⟩ : syracuseStep 892129 = 669097) (by norm_num)
theorem B1187045 : Blo 790340 1187045 := bbase (se 4 (by rfl) ⟨111285, by rfl⟩ : syracuseStep 1187045 = 222571) (by norm_num)
theorem B1449197 : Blo 790340 1449197 := bbase (se 3 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 1449197 = 543449) (by norm_num)
theorem B1187069 : Blo 790340 1187069 := bbase (se 3 (by rfl) ⟨222575, by rfl⟩ : syracuseStep 1187069 = 445151) (by norm_num)
theorem B4005125 : Blo 790340 4005125 := bbase (se 4 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 4005125 = 750961) (by norm_num)
theorem B892165 : Blo 790340 892165 := bbase (se 4 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 892165 = 167281) (by norm_num)
theorem B1187093 : Blo 790340 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B2006309 : Blo 790340 2006309 := bbase (se 4 (by rfl) ⟨188091, by rfl⟩ : syracuseStep 2006309 = 376183) (by norm_num)
theorem B892201 : Blo 790340 892201 := bbase (se 2 (by rfl) ⟨334575, by rfl⟩ : syracuseStep 892201 = 669151) (by norm_num)
theorem B1187117 : Blo 790340 1187117 := bbase (se 3 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 1187117 = 445169) (by norm_num)
theorem B1187141 : Blo 790340 1187141 := bbase (se 4 (by rfl) ⟨111294, by rfl⟩ : syracuseStep 1187141 = 222589) (by norm_num)
theorem B892237 : Blo 790340 892237 := bbase (se 3 (by rfl) ⟨167294, by rfl⟩ : syracuseStep 892237 = 334589) (by norm_num)
theorem B1187165 : Blo 790340 1187165 := bbase (se 3 (by rfl) ⟨222593, by rfl⟩ : syracuseStep 1187165 = 445187) (by norm_num)
theorem B892273 : Blo 790340 892273 := bbase (se 2 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 892273 = 669205) (by norm_num)
theorem B1187189 : Blo 790340 1187189 := bbase (se 5 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 1187189 = 111299) (by norm_num)
theorem B1187213 : Blo 790340 1187213 := bbase (se 3 (by rfl) ⟨222602, by rfl⟩ : syracuseStep 1187213 = 445205) (by norm_num)
theorem B892309 : Blo 790340 892309 := bbase (se 6 (by rfl) ⟨20913, by rfl⟩ : syracuseStep 892309 = 41827) (by norm_num)
theorem B1187237 : Blo 790340 1187237 := bbase (se 4 (by rfl) ⟨111303, by rfl⟩ : syracuseStep 1187237 = 222607) (by norm_num)
theorem B892345 : Blo 790340 892345 := bbase (se 2 (by rfl) ⟨334629, by rfl⟩ : syracuseStep 892345 = 669259) (by norm_num)
theorem B1187261 : Blo 790340 1187261 := bbase (se 3 (by rfl) ⟨222611, by rfl⟩ : syracuseStep 1187261 = 445223) (by norm_num)
theorem B1187285 : Blo 790340 1187285 := bbase (se 7 (by rfl) ⟨13913, by rfl⟩ : syracuseStep 1187285 = 27827) (by norm_num)
theorem B892381 : Blo 790340 892381 := bbase (se 3 (by rfl) ⟨167321, by rfl⟩ : syracuseStep 892381 = 334643) (by norm_num)
theorem B1187309 : Blo 790340 1187309 := bbase (se 3 (by rfl) ⟨222620, by rfl⟩ : syracuseStep 1187309 = 445241) (by norm_num)
theorem B892417 : Blo 790340 892417 := bbase (se 2 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 892417 = 669313) (by norm_num)
theorem B1187333 : Blo 790340 1187333 := bbase (se 4 (by rfl) ⟨111312, by rfl⟩ : syracuseStep 1187333 = 222625) (by norm_num)
theorem B1187357 : Blo 790340 1187357 := bbase (se 3 (by rfl) ⟨222629, by rfl⟩ : syracuseStep 1187357 = 445259) (by norm_num)
theorem B892453 : Blo 790340 892453 := bbase (se 4 (by rfl) ⟨83667, by rfl⟩ : syracuseStep 892453 = 167335) (by norm_num)
theorem B1187381 : Blo 790340 1187381 := bbase (se 5 (by rfl) ⟨55658, by rfl⟩ : syracuseStep 1187381 = 111317) (by norm_num)
theorem B892489 : Blo 790340 892489 := bbase (se 2 (by rfl) ⟨334683, by rfl⟩ : syracuseStep 892489 = 669367) (by norm_num)
theorem B1187405 : Blo 790340 1187405 := bbase (se 3 (by rfl) ⟨222638, by rfl⟩ : syracuseStep 1187405 = 445277) (by norm_num)
theorem B1187429 : Blo 790340 1187429 := bbase (se 4 (by rfl) ⟨111321, by rfl⟩ : syracuseStep 1187429 = 222643) (by norm_num)
theorem B859753 : Blo 790340 859753 := bbase (se 2 (by rfl) ⟨322407, by rfl⟩ : syracuseStep 859753 = 644815) (by norm_num)
theorem B892525 : Blo 790340 892525 := bbase (se 3 (by rfl) ⟨167348, by rfl⟩ : syracuseStep 892525 = 334697) (by norm_num)
theorem B1187453 : Blo 790340 1187453 := bbase (se 3 (by rfl) ⟨222647, by rfl⟩ : syracuseStep 1187453 = 445295) (by norm_num)
theorem B2006653 : Blo 790340 2006653 := bbase (se 3 (by rfl) ⟨376247, by rfl⟩ : syracuseStep 2006653 = 752495) (by norm_num)
theorem B892561 : Blo 790340 892561 := bbase (se 2 (by rfl) ⟨334710, by rfl⟩ : syracuseStep 892561 = 669421) (by norm_num)
theorem B1187477 : Blo 790340 1187477 := bbase (se 6 (by rfl) ⟨27831, by rfl⟩ : syracuseStep 1187477 = 55663) (by norm_num)
theorem B1187501 : Blo 790340 1187501 := bbase (se 3 (by rfl) ⟨222656, by rfl⟩ : syracuseStep 1187501 = 445313) (by norm_num)
theorem B1908397 : Blo 790340 1908397 := bbase (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) (by norm_num)
theorem B892597 : Blo 790340 892597 := bbase (se 5 (by rfl) ⟨41840, by rfl⟩ : syracuseStep 892597 = 83681) (by norm_num)
theorem B1187525 : Blo 790340 1187525 := bbase (se 4 (by rfl) ⟨111330, by rfl⟩ : syracuseStep 1187525 = 222661) (by norm_num)
theorem B892633 : Blo 790340 892633 := bbase (se 2 (by rfl) ⟨334737, by rfl⟩ : syracuseStep 892633 = 669475) (by norm_num)
theorem B1187549 : Blo 790340 1187549 := bbase (se 3 (by rfl) ⟨222665, by rfl⟩ : syracuseStep 1187549 = 445331) (by norm_num)
theorem B2006765 : Blo 790340 2006765 := bbase (se 3 (by rfl) ⟨376268, by rfl⟩ : syracuseStep 2006765 = 752537) (by norm_num)
theorem B1187573 : Blo 790340 1187573 := bbase (se 5 (by rfl) ⟨55667, by rfl⟩ : syracuseStep 1187573 = 111335) (by norm_num)
theorem B892669 : Blo 790340 892669 := bbase (se 3 (by rfl) ⟨167375, by rfl⟩ : syracuseStep 892669 = 334751) (by norm_num)
theorem B1187597 : Blo 790340 1187597 := bbase (se 3 (by rfl) ⟨222674, by rfl⟩ : syracuseStep 1187597 = 445349) (by norm_num)
theorem B892705 : Blo 790340 892705 := bbase (se 2 (by rfl) ⟨334764, by rfl⟩ : syracuseStep 892705 = 669529) (by norm_num)
theorem B1187621 : Blo 790340 1187621 := bbase (se 4 (by rfl) ⟨111339, by rfl⟩ : syracuseStep 1187621 = 222679) (by norm_num)
theorem B1187645 : Blo 790340 1187645 := bbase (se 3 (by rfl) ⟨222683, by rfl⟩ : syracuseStep 1187645 = 445367) (by norm_num)
theorem B892741 : Blo 790340 892741 := bbase (se 4 (by rfl) ⟨83694, by rfl⟩ : syracuseStep 892741 = 167389) (by norm_num)
theorem B1187669 : Blo 790340 1187669 := bbase (se 9 (by rfl) ⟨3479, by rfl⟩ : syracuseStep 1187669 = 6959) (by norm_num)
theorem B892777 : Blo 790340 892777 := bbase (se 2 (by rfl) ⟨334791, by rfl⟩ : syracuseStep 892777 = 669583) (by norm_num)
theorem B1187693 : Blo 790340 1187693 := bbase (se 3 (by rfl) ⟨222692, by rfl⟩ : syracuseStep 1187693 = 445385) (by norm_num)
theorem B1187717 : Blo 790340 1187717 := bbase (se 4 (by rfl) ⟨111348, by rfl⟩ : syracuseStep 1187717 = 222697) (by norm_num)
theorem B892813 : Blo 790340 892813 := bbase (se 3 (by rfl) ⟨167402, by rfl⟩ : syracuseStep 892813 = 334805) (by norm_num)
theorem B1187741 : Blo 790340 1187741 := bbase (se 3 (by rfl) ⟨222701, by rfl⟩ : syracuseStep 1187741 = 445403) (by norm_num)
theorem B2006957 : Blo 790340 2006957 := bbase (se 3 (by rfl) ⟨376304, by rfl⟩ : syracuseStep 2006957 = 752609) (by norm_num)
theorem B892849 : Blo 790340 892849 := bbase (se 2 (by rfl) ⟨334818, by rfl⟩ : syracuseStep 892849 = 669637) (by norm_num)
theorem B1187765 : Blo 790340 1187765 := bbase (se 5 (by rfl) ⟨55676, by rfl⟩ : syracuseStep 1187765 = 111353) (by norm_num)
theorem B3383221 : Blo 790340 3383221 := bbase (se 5 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 3383221 = 317177) (by norm_num)
theorem B1187789 : Blo 790340 1187789 := bbase (se 3 (by rfl) ⟨222710, by rfl⟩ : syracuseStep 1187789 = 445421) (by norm_num)
theorem B892885 : Blo 790340 892885 := bbase (se 7 (by rfl) ⟨10463, by rfl⟩ : syracuseStep 892885 = 20927) (by norm_num)
theorem B1187813 : Blo 790340 1187813 := bbase (se 4 (by rfl) ⟨111357, by rfl⟩ : syracuseStep 1187813 = 222715) (by norm_num)
theorem B892921 : Blo 790340 892921 := bbase (se 2 (by rfl) ⟨334845, by rfl⟩ : syracuseStep 892921 = 669691) (by norm_num)
theorem B1187837 : Blo 790340 1187837 := bbase (se 3 (by rfl) ⟨222719, by rfl⟩ : syracuseStep 1187837 = 445439) (by norm_num)
theorem B1187861 : Blo 790340 1187861 := bbase (se 6 (by rfl) ⟨27840, by rfl⟩ : syracuseStep 1187861 = 55681) (by norm_num)
theorem B892957 : Blo 790340 892957 := bbase (se 3 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 892957 = 334859) (by norm_num)
theorem B1187885 : Blo 790340 1187885 := bbase (se 3 (by rfl) ⟨222728, by rfl⟩ : syracuseStep 1187885 = 445457) (by norm_num)
theorem B892993 : Blo 790340 892993 := bbase (se 2 (by rfl) ⟨334872, by rfl⟩ : syracuseStep 892993 = 669745) (by norm_num)
theorem B1187909 : Blo 790340 1187909 := bbase (se 4 (by rfl) ⟨111366, by rfl⟩ : syracuseStep 1187909 = 222733) (by norm_num)
theorem B1187933 : Blo 790340 1187933 := bbase (se 3 (by rfl) ⟨222737, by rfl⟩ : syracuseStep 1187933 = 445475) (by norm_num)
theorem B893029 : Blo 790340 893029 := bbase (se 4 (by rfl) ⟨83721, by rfl⟩ : syracuseStep 893029 = 167443) (by norm_num)
theorem B1187957 : Blo 790340 1187957 := bbase (se 5 (by rfl) ⟨55685, by rfl⟩ : syracuseStep 1187957 = 111371) (by norm_num)
theorem B893065 : Blo 790340 893065 := bbase (se 2 (by rfl) ⟨334899, by rfl⟩ : syracuseStep 893065 = 669799) (by norm_num)
theorem B1187981 : Blo 790340 1187981 := bbase (se 3 (by rfl) ⟨222746, by rfl⟩ : syracuseStep 1187981 = 445493) (by norm_num)
theorem B1188005 : Blo 790340 1188005 := bbase (se 4 (by rfl) ⟨111375, by rfl⟩ : syracuseStep 1188005 = 222751) (by norm_num)
theorem B893101 : Blo 790340 893101 := bbase (se 3 (by rfl) ⟨167456, by rfl⟩ : syracuseStep 893101 = 334913) (by norm_num)
theorem B1188029 : Blo 790340 1188029 := bbase (se 3 (by rfl) ⟨222755, by rfl⟩ : syracuseStep 1188029 = 445511) (by norm_num)
theorem B2138309 : Blo 790340 2138309 := bbase (se 4 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 2138309 = 400933) (by norm_num)
theorem B893137 : Blo 790340 893137 := bbase (se 2 (by rfl) ⟨334926, by rfl⟩ : syracuseStep 893137 = 669853) (by norm_num)
theorem B1188053 : Blo 790340 1188053 := bbase (se 7 (by rfl) ⟨13922, by rfl⟩ : syracuseStep 1188053 = 27845) (by norm_num)
theorem B1188077 : Blo 790340 1188077 := bbase (se 3 (by rfl) ⟨222764, by rfl⟩ : syracuseStep 1188077 = 445529) (by norm_num)
theorem B893173 : Blo 790340 893173 := bbase (se 5 (by rfl) ⟨41867, by rfl⟩ : syracuseStep 893173 = 83735) (by norm_num)
theorem B1188101 : Blo 790340 1188101 := bbase (se 4 (by rfl) ⟨111384, by rfl⟩ : syracuseStep 1188101 = 222769) (by norm_num)
theorem B2007301 : Blo 790340 2007301 := bbase (se 4 (by rfl) ⟨188184, by rfl⟩ : syracuseStep 2007301 = 376369) (by norm_num)
theorem B893209 : Blo 790340 893209 := bbase (se 2 (by rfl) ⟨334953, by rfl⟩ : syracuseStep 893209 = 669907) (by norm_num)
theorem B1188125 : Blo 790340 1188125 := bbase (se 3 (by rfl) ⟨222773, by rfl⟩ : syracuseStep 1188125 = 445547) (by norm_num)
theorem B1351973 : Blo 790340 1351973 := bbase (se 4 (by rfl) ⟨126747, by rfl⟩ : syracuseStep 1351973 = 253495) (by norm_num)
theorem B1188149 : Blo 790340 1188149 := bbase (se 5 (by rfl) ⟨55694, by rfl⟩ : syracuseStep 1188149 = 111389) (by norm_num)
theorem B893245 : Blo 790340 893245 := bbase (se 3 (by rfl) ⟨167483, by rfl⟩ : syracuseStep 893245 = 334967) (by norm_num)
theorem B1188173 : Blo 790340 1188173 := bbase (se 3 (by rfl) ⟨222782, by rfl⟩ : syracuseStep 1188173 = 445565) (by norm_num)
theorem B893281 : Blo 790340 893281 := bbase (se 2 (by rfl) ⟨334980, by rfl⟩ : syracuseStep 893281 = 669961) (by norm_num)
theorem B1188197 : Blo 790340 1188197 := bbase (se 4 (by rfl) ⟨111393, by rfl⟩ : syracuseStep 1188197 = 222787) (by norm_num)
theorem B2007413 : Blo 790340 2007413 := bbase (se 5 (by rfl) ⟨94097, by rfl⟩ : syracuseStep 2007413 = 188195) (by norm_num)
theorem B1188221 : Blo 790340 1188221 := bbase (se 3 (by rfl) ⟨222791, by rfl⟩ : syracuseStep 1188221 = 445583) (by norm_num)
theorem B893317 : Blo 790340 893317 := bbase (se 4 (by rfl) ⟨83748, by rfl⟩ : syracuseStep 893317 = 167497) (by norm_num)
theorem B1188245 : Blo 790340 1188245 := bbase (se 6 (by rfl) ⟨27849, by rfl⟩ : syracuseStep 1188245 = 55699) (by norm_num)
theorem B893353 : Blo 790340 893353 := bbase (se 2 (by rfl) ⟨335007, by rfl⟩ : syracuseStep 893353 = 670015) (by norm_num)
theorem B1188269 : Blo 790340 1188269 := bbase (se 3 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 1188269 = 445601) (by norm_num)
theorem B1188293 : Blo 790340 1188293 := bbase (se 4 (by rfl) ⟨111402, by rfl⟩ : syracuseStep 1188293 = 222805) (by norm_num)
theorem B893389 : Blo 790340 893389 := bbase (se 3 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 893389 = 335021) (by norm_num)
theorem B1188317 : Blo 790340 1188317 := bbase (se 3 (by rfl) ⟨222809, by rfl⟩ : syracuseStep 1188317 = 445619) (by norm_num)
theorem B893425 : Blo 790340 893425 := bbase (se 2 (by rfl) ⟨335034, by rfl⟩ : syracuseStep 893425 = 670069) (by norm_num)
theorem B1188341 : Blo 790340 1188341 := bbase (se 5 (by rfl) ⟨55703, by rfl⟩ : syracuseStep 1188341 = 111407) (by norm_num)
theorem B1188365 : Blo 790340 1188365 := bbase (se 3 (by rfl) ⟨222818, by rfl⟩ : syracuseStep 1188365 = 445637) (by norm_num)
theorem B4006421 : Blo 790340 4006421 := bbase (se 6 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 4006421 = 187801) (by norm_num)
theorem B893461 : Blo 790340 893461 := bbase (se 6 (by rfl) ⟨20940, by rfl⟩ : syracuseStep 893461 = 41881) (by norm_num)
theorem B1188389 : Blo 790340 1188389 := bbase (se 4 (by rfl) ⟨111411, by rfl⟩ : syracuseStep 1188389 = 222823) (by norm_num)
theorem B2007605 : Blo 790340 2007605 := bbase (se 5 (by rfl) ⟨94106, by rfl⟩ : syracuseStep 2007605 = 188213) (by norm_num)
theorem B893497 : Blo 790340 893497 := bbase (se 2 (by rfl) ⟨335061, by rfl⟩ : syracuseStep 893497 = 670123) (by norm_num)
theorem B1188413 : Blo 790340 1188413 := bbase (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) (by norm_num)
theorem B1188437 : Blo 790340 1188437 := bbase (se 8 (by rfl) ⟨6963, by rfl⟩ : syracuseStep 1188437 = 13927) (by norm_num)
theorem B893533 : Blo 790340 893533 := bbase (se 3 (by rfl) ⟨167537, by rfl⟩ : syracuseStep 893533 = 335075) (by norm_num)
theorem B1188461 : Blo 790340 1188461 := bbase (se 3 (by rfl) ⟨222836, by rfl⟩ : syracuseStep 1188461 = 445673) (by norm_num)
theorem B893569 : Blo 790340 893569 := bbase (se 2 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 893569 = 670177) (by norm_num)
theorem B1778309 : Blo 790340 1778309 := bbase (se 4 (by rfl) ⟨166716, by rfl⟩ : syracuseStep 1778309 = 333433) (by norm_num)
theorem B1188485 : Blo 790340 1188485 := bbase (se 4 (by rfl) ⟨111420, by rfl⟩ : syracuseStep 1188485 = 222841) (by norm_num)
theorem B3383957 : Blo 790340 3383957 := bbase (se 6 (by rfl) ⟨79311, by rfl⟩ : syracuseStep 3383957 = 158623) (by norm_num)
theorem B1188509 : Blo 790340 1188509 := bbase (se 3 (by rfl) ⟨222845, by rfl⟩ : syracuseStep 1188509 = 445691) (by norm_num)
theorem B893605 : Blo 790340 893605 := bbase (se 4 (by rfl) ⟨83775, by rfl⟩ : syracuseStep 893605 = 167551) (by norm_num)
theorem B1188533 : Blo 790340 1188533 := bbase (se 5 (by rfl) ⟨55712, by rfl⟩ : syracuseStep 1188533 = 111425) (by norm_num)
theorem B1778381 : Blo 790340 1778381 := bbase (se 3 (by rfl) ⟨333446, by rfl⟩ : syracuseStep 1778381 = 666893) (by norm_num)
theorem B1188557 : Blo 790340 1188557 := bbase (se 3 (by rfl) ⟨222854, by rfl⟩ : syracuseStep 1188557 = 445709) (by norm_num)
theorem B1188581 : Blo 790340 1188581 := bbase (se 4 (by rfl) ⟨111429, by rfl⟩ : syracuseStep 1188581 = 222859) (by norm_num)
theorem B2138869 : Blo 790340 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B1188605 : Blo 790340 1188605 := bbase (se 3 (by rfl) ⟨222863, by rfl⟩ : syracuseStep 1188605 = 445727) (by norm_num)
theorem B1778453 : Blo 790340 1778453 := bbase (se 6 (by rfl) ⟨41682, by rfl⟩ : syracuseStep 1778453 = 83365) (by norm_num)
theorem B1188629 : Blo 790340 1188629 := bbase (se 6 (by rfl) ⟨27858, by rfl⟩ : syracuseStep 1188629 = 55717) (by norm_num)
theorem B1188653 : Blo 790340 1188653 := bbase (se 3 (by rfl) ⟨222872, by rfl⟩ : syracuseStep 1188653 = 445745) (by norm_num)
theorem B1188677 : Blo 790340 1188677 := bbase (se 4 (by rfl) ⟨111438, by rfl⟩ : syracuseStep 1188677 = 222877) (by norm_num)
theorem B1778525 : Blo 790340 1778525 := bbase (se 3 (by rfl) ⟨333473, by rfl⟩ : syracuseStep 1778525 = 666947) (by norm_num)
theorem B1188701 : Blo 790340 1188701 := bbase (se 3 (by rfl) ⟨222881, by rfl⟩ : syracuseStep 1188701 = 445763) (by norm_num)
theorem B1188725 : Blo 790340 1188725 := bbase (se 5 (by rfl) ⟨55721, by rfl⟩ : syracuseStep 1188725 = 111443) (by norm_num)
theorem B1188749 : Blo 790340 1188749 := bbase (se 3 (by rfl) ⟨222890, by rfl⟩ : syracuseStep 1188749 = 445781) (by norm_num)
theorem B2007949 : Blo 790340 2007949 := bbase (se 3 (by rfl) ⟨376490, by rfl⟩ : syracuseStep 2007949 = 752981) (by norm_num)
theorem B1778597 : Blo 790340 1778597 := bbase (se 4 (by rfl) ⟨166743, by rfl⟩ : syracuseStep 1778597 = 333487) (by norm_num)
theorem B1188773 : Blo 790340 1188773 := bbase (se 4 (by rfl) ⟨111447, by rfl⟩ : syracuseStep 1188773 = 222895) (by norm_num)
theorem B1188797 : Blo 790340 1188797 := bbase (se 3 (by rfl) ⟨222899, by rfl⟩ : syracuseStep 1188797 = 445799) (by norm_num)
theorem B1188821 : Blo 790340 1188821 := bbase (se 7 (by rfl) ⟨13931, by rfl⟩ : syracuseStep 1188821 = 27863) (by norm_num)
theorem B1778669 : Blo 790340 1778669 := bbase (se 3 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 1778669 = 667001) (by norm_num)
theorem B1188845 : Blo 790340 1188845 := bbase (se 3 (by rfl) ⟨222908, by rfl⟩ : syracuseStep 1188845 = 445817) (by norm_num)
theorem B2532341 : Blo 790340 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B2008061 : Blo 790340 2008061 := bbase (se 3 (by rfl) ⟨376511, by rfl⟩ : syracuseStep 2008061 = 753023) (by norm_num)
theorem B1188869 : Blo 790340 1188869 := bbase (se 4 (by rfl) ⟨111456, by rfl⟩ : syracuseStep 1188869 = 222913) (by norm_num)
theorem B1188893 : Blo 790340 1188893 := bbase (se 3 (by rfl) ⟨222917, by rfl⟩ : syracuseStep 1188893 = 445835) (by norm_num)
theorem B1778741 : Blo 790340 1778741 := bbase (se 5 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 1778741 = 166757) (by norm_num)
theorem B1188917 : Blo 790340 1188917 := bbase (se 5 (by rfl) ⟨55730, by rfl⟩ : syracuseStep 1188917 = 111461) (by norm_num)
theorem B1713221 : Blo 790340 1713221 := bbase (se 4 (by rfl) ⟨160614, by rfl⟩ : syracuseStep 1713221 = 321229) (by norm_num)
theorem B1188941 : Blo 790340 1188941 := bbase (se 3 (by rfl) ⟨222926, by rfl⟩ : syracuseStep 1188941 = 445853) (by norm_num)
theorem B1221725 : Blo 790340 1221725 := bbase (se 3 (by rfl) ⟨229073, by rfl⟩ : syracuseStep 1221725 = 458147) (by norm_num)
theorem B1188965 : Blo 790340 1188965 := bbase (se 4 (by rfl) ⟨111465, by rfl⟩ : syracuseStep 1188965 = 222931) (by norm_num)
theorem B1778813 : Blo 790340 1778813 := bbase (se 3 (by rfl) ⟨333527, by rfl⟩ : syracuseStep 1778813 = 667055) (by norm_num)
theorem B1188989 : Blo 790340 1188989 := bbase (se 3 (by rfl) ⟨222935, by rfl⟩ : syracuseStep 1188989 = 445871) (by norm_num)
theorem B1189013 : Blo 790340 1189013 := bbase (se 6 (by rfl) ⟨27867, by rfl⟩ : syracuseStep 1189013 = 55735) (by norm_num)
theorem B1189037 : Blo 790340 1189037 := bbase (se 3 (by rfl) ⟨222944, by rfl⟩ : syracuseStep 1189037 = 445889) (by norm_num)
theorem B1156277 : Blo 790340 1156277 := bbase (se 5 (by rfl) ⟨54200, by rfl⟩ : syracuseStep 1156277 = 108401) (by norm_num)
theorem B2008253 : Blo 790340 2008253 := bbase (se 3 (by rfl) ⟨376547, by rfl⟩ : syracuseStep 2008253 = 753095) (by norm_num)
theorem B1778885 : Blo 790340 1778885 := bbase (se 4 (by rfl) ⟨166770, by rfl⟩ : syracuseStep 1778885 = 333541) (by norm_num)
theorem B1189061 : Blo 790340 1189061 := bbase (se 4 (by rfl) ⟨111474, by rfl⟩ : syracuseStep 1189061 = 222949) (by norm_num)
theorem B1189085 : Blo 790340 1189085 := bbase (se 3 (by rfl) ⟨222953, by rfl⟩ : syracuseStep 1189085 = 445907) (by norm_num)
theorem B1189109 : Blo 790340 1189109 := bbase (se 5 (by rfl) ⟨55739, by rfl⟩ : syracuseStep 1189109 = 111479) (by norm_num)
theorem B1778957 : Blo 790340 1778957 := bbase (se 3 (by rfl) ⟨333554, by rfl⟩ : syracuseStep 1778957 = 667109) (by norm_num)
theorem B1189133 : Blo 790340 1189133 := bbase (se 3 (by rfl) ⟨222962, by rfl⟩ : syracuseStep 1189133 = 445925) (by norm_num)
theorem B1189157 : Blo 790340 1189157 := bbase (se 4 (by rfl) ⟨111483, by rfl⟩ : syracuseStep 1189157 = 222967) (by norm_num)
theorem B1189181 : Blo 790340 1189181 := bbase (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) (by norm_num)
theorem B1779029 : Blo 790340 1779029 := bbase (se 12 (by rfl) ⟨651, by rfl⟩ : syracuseStep 1779029 = 1303) (by norm_num)
theorem B1189205 : Blo 790340 1189205 := bbase (se 12 (by rfl) ⟨435, by rfl⟩ : syracuseStep 1189205 = 871) (by norm_num)
theorem B1353053 : Blo 790340 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B1189229 : Blo 790340 1189229 := bbase (se 3 (by rfl) ⟨222980, by rfl⟩ : syracuseStep 1189229 = 445961) (by norm_num)
theorem B1189253 : Blo 790340 1189253 := bbase (se 4 (by rfl) ⟨111492, by rfl⟩ : syracuseStep 1189253 = 222985) (by norm_num)
theorem B1779101 : Blo 790340 1779101 := bbase (se 3 (by rfl) ⟨333581, by rfl⟩ : syracuseStep 1779101 = 667163) (by norm_num)
theorem B1189277 : Blo 790340 1189277 := bbase (se 3 (by rfl) ⟨222989, by rfl⟩ : syracuseStep 1189277 = 445979) (by norm_num)
theorem B1189301 : Blo 790340 1189301 := bbase (se 5 (by rfl) ⟨55748, by rfl⟩ : syracuseStep 1189301 = 111497) (by norm_num)
theorem B1189325 : Blo 790340 1189325 := bbase (se 3 (by rfl) ⟨222998, by rfl⟩ : syracuseStep 1189325 = 445997) (by norm_num)
theorem B1779173 : Blo 790340 1779173 := bbase (se 4 (by rfl) ⟨166797, by rfl⟩ : syracuseStep 1779173 = 333595) (by norm_num)
theorem B1189349 : Blo 790340 1189349 := bbase (se 4 (by rfl) ⟨111501, by rfl⟩ : syracuseStep 1189349 = 223003) (by norm_num)
theorem B1189373 : Blo 790340 1189373 := bbase (se 3 (by rfl) ⟨223007, by rfl⟩ : syracuseStep 1189373 = 446015) (by norm_num)
theorem B1189397 : Blo 790340 1189397 := bbase (se 6 (by rfl) ⟨27876, by rfl⟩ : syracuseStep 1189397 = 55753) (by norm_num)
theorem B2008597 : Blo 790340 2008597 := bbase (se 6 (by rfl) ⟨47076, by rfl⟩ : syracuseStep 2008597 = 94153) (by norm_num)
theorem B1779245 : Blo 790340 1779245 := bbase (se 3 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 1779245 = 667217) (by norm_num)
theorem B1189421 : Blo 790340 1189421 := bbase (se 3 (by rfl) ⟨223016, by rfl⟩ : syracuseStep 1189421 = 446033) (by norm_num)
theorem B1189445 : Blo 790340 1189445 := bbase (se 4 (by rfl) ⟨111510, by rfl⟩ : syracuseStep 1189445 = 223021) (by norm_num)
theorem B1189469 : Blo 790340 1189469 := bbase (se 3 (by rfl) ⟨223025, by rfl⟩ : syracuseStep 1189469 = 446051) (by norm_num)
theorem B1779317 : Blo 790340 1779317 := bbase (se 5 (by rfl) ⟨83405, by rfl⟩ : syracuseStep 1779317 = 166811) (by norm_num)
theorem B1189493 : Blo 790340 1189493 := bbase (se 5 (by rfl) ⟨55757, by rfl⟩ : syracuseStep 1189493 = 111515) (by norm_num)
theorem B2008709 : Blo 790340 2008709 := bbase (se 4 (by rfl) ⟨188316, by rfl⟩ : syracuseStep 2008709 = 376633) (by norm_num)
theorem B1189517 : Blo 790340 1189517 := bbase (se 3 (by rfl) ⟨223034, by rfl⟩ : syracuseStep 1189517 = 446069) (by norm_num)
theorem B1189541 : Blo 790340 1189541 := bbase (se 4 (by rfl) ⟨111519, by rfl⟩ : syracuseStep 1189541 = 223039) (by norm_num)
theorem B1779389 : Blo 790340 1779389 := bbase (se 3 (by rfl) ⟨333635, by rfl⟩ : syracuseStep 1779389 = 667271) (by norm_num)
theorem B1189565 : Blo 790340 1189565 := bbase (se 3 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 1189565 = 446087) (by norm_num)
theorem B1189589 : Blo 790340 1189589 := bbase (se 7 (by rfl) ⟨13940, by rfl⟩ : syracuseStep 1189589 = 27881) (by norm_num)
theorem B3811045 : Blo 790340 3811045 := bbase (se 4 (by rfl) ⟨357285, by rfl⟩ : syracuseStep 3811045 = 714571) (by norm_num)
theorem B1189613 : Blo 790340 1189613 := bbase (se 3 (by rfl) ⟨223052, by rfl⟩ : syracuseStep 1189613 = 446105) (by norm_num)
theorem B1779461 : Blo 790340 1779461 := bbase (se 4 (by rfl) ⟨166824, by rfl⟩ : syracuseStep 1779461 = 333649) (by norm_num)
theorem B1189637 : Blo 790340 1189637 := bbase (se 4 (by rfl) ⟨111528, by rfl⟩ : syracuseStep 1189637 = 223057) (by norm_num)
theorem B4073237 : Blo 790340 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B1189661 : Blo 790340 1189661 := bbase (se 3 (by rfl) ⟨223061, by rfl⟩ : syracuseStep 1189661 = 446123) (by norm_num)
theorem B4007717 : Blo 790340 4007717 := bbase (se 4 (by rfl) ⟨375723, by rfl⟩ : syracuseStep 4007717 = 751447) (by norm_num)
theorem B1189685 : Blo 790340 1189685 := bbase (se 5 (by rfl) ⟨55766, by rfl⟩ : syracuseStep 1189685 = 111533) (by norm_num)
theorem B2008901 : Blo 790340 2008901 := bbase (se 4 (by rfl) ⟨188334, by rfl⟩ : syracuseStep 2008901 = 376669) (by norm_num)
theorem B1779533 : Blo 790340 1779533 := bbase (se 3 (by rfl) ⟨333662, by rfl⟩ : syracuseStep 1779533 = 667325) (by norm_num)
theorem B1189709 : Blo 790340 1189709 := bbase (se 3 (by rfl) ⟨223070, by rfl⟩ : syracuseStep 1189709 = 446141) (by norm_num)
theorem B1189733 : Blo 790340 1189733 := bbase (se 4 (by rfl) ⟨111537, by rfl⟩ : syracuseStep 1189733 = 223075) (by norm_num)
theorem B1288045 : Blo 790340 1288045 := bbase (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) (by norm_num)
theorem B1189757 : Blo 790340 1189757 := bbase (se 3 (by rfl) ⟨223079, by rfl⟩ : syracuseStep 1189757 = 446159) (by norm_num)
theorem B2140037 : Blo 790340 2140037 := bbase (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) (by norm_num)
theorem B1779605 : Blo 790340 1779605 := bbase (se 6 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 1779605 = 83419) (by norm_num)
theorem B1189781 : Blo 790340 1189781 := bbase (se 6 (by rfl) ⟨27885, by rfl⟩ : syracuseStep 1189781 = 55771) (by norm_num)
theorem B1189805 : Blo 790340 1189805 := bbase (se 3 (by rfl) ⟨223088, by rfl⟩ : syracuseStep 1189805 = 446177) (by norm_num)
theorem B1189829 : Blo 790340 1189829 := bbase (se 4 (by rfl) ⟨111546, by rfl⟩ : syracuseStep 1189829 = 223093) (by norm_num)
theorem B1779677 : Blo 790340 1779677 := bbase (se 3 (by rfl) ⟨333689, by rfl⟩ : syracuseStep 1779677 = 667379) (by norm_num)
theorem B1189853 : Blo 790340 1189853 := bbase (se 3 (by rfl) ⟨223097, by rfl⟩ : syracuseStep 1189853 = 446195) (by norm_num)
theorem B1189877 : Blo 790340 1189877 := bbase (se 5 (by rfl) ⟨55775, by rfl⟩ : syracuseStep 1189877 = 111551) (by norm_num)
theorem B1189901 : Blo 790340 1189901 := bbase (se 3 (by rfl) ⟨223106, by rfl⟩ : syracuseStep 1189901 = 446213) (by norm_num)
theorem B1779749 : Blo 790340 1779749 := bbase (se 4 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 1779749 = 333703) (by norm_num)
theorem B1189925 : Blo 790340 1189925 := bbase (se 4 (by rfl) ⟨111555, by rfl⟩ : syracuseStep 1189925 = 223111) (by norm_num)
theorem B1189949 : Blo 790340 1189949 := bbase (se 3 (by rfl) ⟨223115, by rfl⟩ : syracuseStep 1189949 = 446231) (by norm_num)
theorem B5711957 : Blo 790340 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B1189973 : Blo 790340 1189973 := bbase (se 8 (by rfl) ⟨6972, by rfl⟩ : syracuseStep 1189973 = 13945) (by norm_num)
theorem B1779821 : Blo 790340 1779821 := bbase (se 3 (by rfl) ⟨333716, by rfl⟩ : syracuseStep 1779821 = 667433) (by norm_num)
theorem B1189997 : Blo 790340 1189997 := bbase (se 3 (by rfl) ⟨223124, by rfl⟩ : syracuseStep 1189997 = 446249) (by norm_num)
theorem B1190021 : Blo 790340 1190021 := bbase (se 4 (by rfl) ⟨111564, by rfl⟩ : syracuseStep 1190021 = 223129) (by norm_num)
theorem B1190045 : Blo 790340 1190045 := bbase (se 3 (by rfl) ⟨223133, by rfl⟩ : syracuseStep 1190045 = 446267) (by norm_num)
theorem B2009245 : Blo 790340 2009245 := bbase (se 3 (by rfl) ⟨376733, by rfl⟩ : syracuseStep 2009245 = 753467) (by norm_num)
theorem B1779893 : Blo 790340 1779893 := bbase (se 5 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 1779893 = 166865) (by norm_num)
theorem B1190069 : Blo 790340 1190069 := bbase (se 5 (by rfl) ⟨55784, by rfl⟩ : syracuseStep 1190069 = 111569) (by norm_num)
theorem B1190093 : Blo 790340 1190093 := bbase (se 3 (by rfl) ⟨223142, by rfl⟩ : syracuseStep 1190093 = 446285) (by norm_num)
theorem B2140373 : Blo 790340 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B1190117 : Blo 790340 1190117 := bbase (se 4 (by rfl) ⟨111573, by rfl⟩ : syracuseStep 1190117 = 223147) (by norm_num)
theorem B2894069 : Blo 790340 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B1779965 : Blo 790340 1779965 := bbase (se 3 (by rfl) ⟨333743, by rfl⟩ : syracuseStep 1779965 = 667487) (by norm_num)
theorem B1190141 : Blo 790340 1190141 := bbase (se 3 (by rfl) ⟨223151, by rfl⟩ : syracuseStep 1190141 = 446303) (by norm_num)
theorem B2009357 : Blo 790340 2009357 := bbase (se 3 (by rfl) ⟨376754, by rfl⟩ : syracuseStep 2009357 = 753509) (by norm_num)
theorem B1190165 : Blo 790340 1190165 := bbase (se 6 (by rfl) ⟨27894, by rfl⟩ : syracuseStep 1190165 = 55789) (by norm_num)
theorem B1190189 : Blo 790340 1190189 := bbase (se 3 (by rfl) ⟨223160, by rfl⟩ : syracuseStep 1190189 = 446321) (by norm_num)
theorem B1780037 : Blo 790340 1780037 := bbase (se 4 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 1780037 = 333757) (by norm_num)
theorem B1190213 : Blo 790340 1190213 := bbase (se 4 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 1190213 = 223165) (by norm_num)
theorem B1190237 : Blo 790340 1190237 := bbase (se 3 (by rfl) ⟨223169, by rfl⟩ : syracuseStep 1190237 = 446339) (by norm_num)
theorem B1190261 : Blo 790340 1190261 := bbase (se 5 (by rfl) ⟨55793, by rfl⟩ : syracuseStep 1190261 = 111587) (by norm_num)
theorem B1780109 : Blo 790340 1780109 := bbase (se 3 (by rfl) ⟨333770, by rfl⟩ : syracuseStep 1780109 = 667541) (by norm_num)
theorem B1190285 : Blo 790340 1190285 := bbase (se 3 (by rfl) ⟨223178, by rfl⟩ : syracuseStep 1190285 = 446357) (by norm_num)
theorem B1190309 : Blo 790340 1190309 := bbase (se 4 (by rfl) ⟨111591, by rfl⟩ : syracuseStep 1190309 = 223183) (by norm_num)
theorem B1190333 : Blo 790340 1190333 := bbase (se 3 (by rfl) ⟨223187, by rfl⟩ : syracuseStep 1190333 = 446375) (by norm_num)
theorem B2009549 : Blo 790340 2009549 := bbase (se 3 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 2009549 = 753581) (by norm_num)
theorem B1780181 : Blo 790340 1780181 := bbase (se 7 (by rfl) ⟨20861, by rfl⟩ : syracuseStep 1780181 = 41723) (by norm_num)
theorem B1190357 : Blo 790340 1190357 := bbase (se 7 (by rfl) ⟨13949, by rfl⟩ : syracuseStep 1190357 = 27899) (by norm_num)
theorem B1190381 : Blo 790340 1190381 := bbase (se 3 (by rfl) ⟨223196, by rfl⟩ : syracuseStep 1190381 = 446393) (by norm_num)
theorem B1190405 : Blo 790340 1190405 := bbase (se 4 (by rfl) ⟨111600, by rfl⟩ : syracuseStep 1190405 = 223201) (by norm_num)
theorem B1780253 : Blo 790340 1780253 := bbase (se 3 (by rfl) ⟨333797, by rfl⟩ : syracuseStep 1780253 = 667595) (by norm_num)
theorem B1190429 : Blo 790340 1190429 := bbase (se 3 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 1190429 = 446411) (by norm_num)
theorem B1190453 : Blo 790340 1190453 := bbase (se 5 (by rfl) ⟨55802, by rfl⟩ : syracuseStep 1190453 = 111605) (by norm_num)
theorem B1190477 : Blo 790340 1190477 := bbase (se 3 (by rfl) ⟨223214, by rfl⟩ : syracuseStep 1190477 = 446429) (by norm_num)
theorem B1780325 : Blo 790340 1780325 := bbase (se 4 (by rfl) ⟨166905, by rfl⟩ : syracuseStep 1780325 = 333811) (by norm_num)
theorem B1190501 : Blo 790340 1190501 := bbase (se 4 (by rfl) ⟨111609, by rfl⟩ : syracuseStep 1190501 = 223219) (by norm_num)
theorem B1190525 : Blo 790340 1190525 := bbase (se 3 (by rfl) ⟨223223, by rfl⟩ : syracuseStep 1190525 = 446447) (by norm_num)
theorem B6007445 : Blo 790340 6007445 := bbase (se 6 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 6007445 = 281599) (by norm_num)
theorem B1190549 : Blo 790340 1190549 := bbase (se 6 (by rfl) ⟨27903, by rfl⟩ : syracuseStep 1190549 = 55807) (by norm_num)
theorem B1780397 : Blo 790340 1780397 := bbase (se 3 (by rfl) ⟨333824, by rfl⟩ : syracuseStep 1780397 = 667649) (by norm_num)
theorem B1190573 : Blo 790340 1190573 := bbase (se 3 (by rfl) ⟨223232, by rfl⟩ : syracuseStep 1190573 = 446465) (by norm_num)
theorem B1190597 : Blo 790340 1190597 := bbase (se 4 (by rfl) ⟨111618, by rfl⟩ : syracuseStep 1190597 = 223237) (by norm_num)
theorem B25701077 : Blo 790340 25701077 := bbase (se 7 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 25701077 = 602369) (by norm_num)
theorem B1190621 : Blo 790340 1190621 := bbase (se 3 (by rfl) ⟨223241, by rfl⟩ : syracuseStep 1190621 = 446483) (by norm_num)
theorem B1780469 : Blo 790340 1780469 := bbase (se 5 (by rfl) ⟨83459, by rfl⟩ : syracuseStep 1780469 = 166919) (by norm_num)
theorem B1190645 : Blo 790340 1190645 := bbase (se 5 (by rfl) ⟨55811, by rfl⟩ : syracuseStep 1190645 = 111623) (by norm_num)
theorem B1190669 : Blo 790340 1190669 := bbase (se 3 (by rfl) ⟨223250, by rfl⟩ : syracuseStep 1190669 = 446501) (by norm_num)
theorem B11578133 : Blo 790340 11578133 := bbase (se 6 (by rfl) ⟨271362, by rfl⟩ : syracuseStep 11578133 = 542725) (by norm_num)
theorem B1190693 : Blo 790340 1190693 := bbase (se 4 (by rfl) ⟨111627, by rfl⟩ : syracuseStep 1190693 = 223255) (by norm_num)
theorem B2009893 : Blo 790340 2009893 := bbase (se 4 (by rfl) ⟨188427, by rfl⟩ : syracuseStep 2009893 = 376855) (by norm_num)
theorem B1780541 : Blo 790340 1780541 := bbase (se 3 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 1780541 = 667703) (by norm_num)
theorem B1190717 : Blo 790340 1190717 := bbase (se 3 (by rfl) ⟨223259, by rfl⟩ : syracuseStep 1190717 = 446519) (by norm_num)
theorem B1190741 : Blo 790340 1190741 := bbase (se 9 (by rfl) ⟨3488, by rfl⟩ : syracuseStep 1190741 = 6977) (by norm_num)
theorem B1190765 : Blo 790340 1190765 := bbase (se 3 (by rfl) ⟨223268, by rfl⟩ : syracuseStep 1190765 = 446537) (by norm_num)
theorem B1780613 : Blo 790340 1780613 := bbase (se 4 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 1780613 = 333865) (by norm_num)
theorem B1190789 : Blo 790340 1190789 := bbase (se 4 (by rfl) ⟨111636, by rfl⟩ : syracuseStep 1190789 = 223273) (by norm_num)
theorem B2010005 : Blo 790340 2010005 := bbase (se 6 (by rfl) ⟨47109, by rfl⟩ : syracuseStep 2010005 = 94219) (by norm_num)
theorem B1190813 : Blo 790340 1190813 := bbase (se 3 (by rfl) ⟨223277, by rfl⟩ : syracuseStep 1190813 = 446555) (by norm_num)
theorem B1190837 : Blo 790340 1190837 := bbase (se 5 (by rfl) ⟨55820, by rfl⟩ : syracuseStep 1190837 = 111641) (by norm_num)
theorem B2534341 : Blo 790340 2534341 := bbase (se 4 (by rfl) ⟨237594, by rfl⟩ : syracuseStep 2534341 = 475189) (by norm_num)
theorem B1780685 : Blo 790340 1780685 := bbase (se 3 (by rfl) ⟨333878, by rfl⟩ : syracuseStep 1780685 = 667757) (by norm_num)
theorem B1190861 : Blo 790340 1190861 := bbase (se 3 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 1190861 = 446573) (by norm_num)
theorem B1190885 : Blo 790340 1190885 := bbase (se 4 (by rfl) ⟨111645, by rfl⟩ : syracuseStep 1190885 = 223291) (by norm_num)
theorem B1190909 : Blo 790340 1190909 := bbase (se 3 (by rfl) ⟨223295, by rfl⟩ : syracuseStep 1190909 = 446591) (by norm_num)
theorem B1780757 : Blo 790340 1780757 := bbase (se 6 (by rfl) ⟨41736, by rfl⟩ : syracuseStep 1780757 = 83473) (by norm_num)
theorem B1190933 : Blo 790340 1190933 := bbase (se 6 (by rfl) ⟨27912, by rfl⟩ : syracuseStep 1190933 = 55825) (by norm_num)
theorem B1190957 : Blo 790340 1190957 := bbase (se 3 (by rfl) ⟨223304, by rfl⟩ : syracuseStep 1190957 = 446609) (by norm_num)
theorem B4009013 : Blo 790340 4009013 := bbase (se 5 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 4009013 = 375845) (by norm_num)
theorem B1190981 : Blo 790340 1190981 := bbase (se 4 (by rfl) ⟨111654, by rfl⟩ : syracuseStep 1190981 = 223309) (by norm_num)
theorem B2010197 : Blo 790340 2010197 := bbase (se 8 (by rfl) ⟨11778, by rfl⟩ : syracuseStep 2010197 = 23557) (by norm_num)
theorem B1780829 : Blo 790340 1780829 := bbase (se 3 (by rfl) ⟨333905, by rfl⟩ : syracuseStep 1780829 = 667811) (by norm_num)
theorem B1191005 : Blo 790340 1191005 := bbase (se 3 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 1191005 = 446627) (by norm_num)
theorem B2403445 : Blo 790340 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B1191029 : Blo 790340 1191029 := bbase (se 5 (by rfl) ⟨55829, by rfl⟩ : syracuseStep 1191029 = 111659) (by norm_num)
theorem B1191053 : Blo 790340 1191053 := bbase (se 3 (by rfl) ⟨223322, by rfl⟩ : syracuseStep 1191053 = 446645) (by norm_num)
theorem B1780901 : Blo 790340 1780901 := bbase (se 4 (by rfl) ⟨166959, by rfl⟩ : syracuseStep 1780901 = 333919) (by norm_num)
theorem B1191077 : Blo 790340 1191077 := bbase (se 4 (by rfl) ⟨111663, by rfl⟩ : syracuseStep 1191077 = 223327) (by norm_num)
theorem B1191101 : Blo 790340 1191101 := bbase (se 3 (by rfl) ⟨223331, by rfl⟩ : syracuseStep 1191101 = 446663) (by norm_num)
theorem B1191125 : Blo 790340 1191125 := bbase (se 7 (by rfl) ⟨13958, by rfl⟩ : syracuseStep 1191125 = 27917) (by norm_num)
theorem B1780973 : Blo 790340 1780973 := bbase (se 3 (by rfl) ⟨333932, by rfl⟩ : syracuseStep 1780973 = 667865) (by norm_num)
theorem B1191149 : Blo 790340 1191149 := bbase (se 3 (by rfl) ⟨223340, by rfl⟩ : syracuseStep 1191149 = 446681) (by norm_num)
theorem B1191173 : Blo 790340 1191173 := bbase (se 4 (by rfl) ⟨111672, by rfl⟩ : syracuseStep 1191173 = 223345) (by norm_num)
theorem B1191197 : Blo 790340 1191197 := bbase (se 3 (by rfl) ⟨223349, by rfl⟩ : syracuseStep 1191197 = 446699) (by norm_num)
theorem B1781045 : Blo 790340 1781045 := bbase (se 5 (by rfl) ⟨83486, by rfl⟩ : syracuseStep 1781045 = 166973) (by norm_num)
theorem B1191221 : Blo 790340 1191221 := bbase (se 5 (by rfl) ⟨55838, by rfl⟩ : syracuseStep 1191221 = 111677) (by norm_num)
theorem B1191245 : Blo 790340 1191245 := bbase (se 3 (by rfl) ⟨223358, by rfl⟩ : syracuseStep 1191245 = 446717) (by norm_num)
theorem B1191269 : Blo 790340 1191269 := bbase (se 4 (by rfl) ⟨111681, by rfl⟩ : syracuseStep 1191269 = 223363) (by norm_num)
theorem B1781117 : Blo 790340 1781117 := bbase (se 3 (by rfl) ⟨333959, by rfl⟩ : syracuseStep 1781117 = 667919) (by norm_num)
theorem B1191293 : Blo 790340 1191293 := bbase (se 3 (by rfl) ⟨223367, by rfl⟩ : syracuseStep 1191293 = 446735) (by norm_num)
theorem B1191317 : Blo 790340 1191317 := bbase (se 6 (by rfl) ⟨27921, by rfl⟩ : syracuseStep 1191317 = 55843) (by norm_num)
theorem B1191341 : Blo 790340 1191341 := bbase (se 3 (by rfl) ⟨223376, by rfl⟩ : syracuseStep 1191341 = 446753) (by norm_num)
theorem B2010541 : Blo 790340 2010541 := bbase (se 3 (by rfl) ⟨376976, by rfl⟩ : syracuseStep 2010541 = 753953) (by norm_num)
theorem B1781189 : Blo 790340 1781189 := bbase (se 4 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 1781189 = 333973) (by norm_num)
theorem B1191365 : Blo 790340 1191365 := bbase (se 4 (by rfl) ⟨111690, by rfl⟩ : syracuseStep 1191365 = 223381) (by norm_num)
theorem B1191389 : Blo 790340 1191389 := bbase (se 3 (by rfl) ⟨223385, by rfl⟩ : syracuseStep 1191389 = 446771) (by norm_num)
theorem B1191413 : Blo 790340 1191413 := bbase (se 5 (by rfl) ⟨55847, by rfl⟩ : syracuseStep 1191413 = 111695) (by norm_num)
theorem B1781261 : Blo 790340 1781261 := bbase (se 3 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 1781261 = 667973) (by norm_num)
theorem B1191437 : Blo 790340 1191437 := bbase (se 3 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 1191437 = 446789) (by norm_num)
theorem B2010653 : Blo 790340 2010653 := bbase (se 3 (by rfl) ⟨376997, by rfl⟩ : syracuseStep 2010653 = 753995) (by norm_num)
theorem B1191461 : Blo 790340 1191461 := bbase (se 4 (by rfl) ⟨111699, by rfl⟩ : syracuseStep 1191461 = 223399) (by norm_num)
theorem B1191485 : Blo 790340 1191485 := bbase (se 3 (by rfl) ⟨223403, by rfl⟩ : syracuseStep 1191485 = 446807) (by norm_num)
theorem B1781333 : Blo 790340 1781333 := bbase (se 8 (by rfl) ⟨10437, by rfl⟩ : syracuseStep 1781333 = 20875) (by norm_num)
theorem B1191509 : Blo 790340 1191509 := bbase (se 8 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 1191509 = 13963) (by norm_num)
theorem B1781405 : Blo 790340 1781405 := bbase (se 3 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 1781405 = 668027) (by norm_num)
theorem B1781477 : Blo 790340 1781477 := bbase (se 4 (by rfl) ⟨167013, by rfl⟩ : syracuseStep 1781477 = 334027) (by norm_num)
theorem B1781549 : Blo 790340 1781549 := bbase (se 3 (by rfl) ⟨334040, by rfl⟩ : syracuseStep 1781549 = 668081) (by norm_num)
theorem B1126237 : Blo 790340 1126237 := bbase (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) (by norm_num)
theorem B1781621 : Blo 790340 1781621 := bbase (se 5 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 1781621 = 167027) (by norm_num)
theorem B3387253 : Blo 790340 3387253 := bbase (se 5 (by rfl) ⟨158777, by rfl⟩ : syracuseStep 3387253 = 317555) (by norm_num)
theorem B3092357 : Blo 790340 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B1781693 : Blo 790340 1781693 := bbase (se 3 (by rfl) ⟨334067, by rfl⟩ : syracuseStep 1781693 = 668135) (by norm_num)
theorem B1781765 : Blo 790340 1781765 := bbase (se 4 (by rfl) ⟨167040, by rfl⟩ : syracuseStep 1781765 = 334081) (by norm_num)
theorem B1781837 : Blo 790340 1781837 := bbase (se 3 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 1781837 = 668189) (by norm_num)
theorem B2404453 : Blo 790340 2404453 := bbase (se 4 (by rfl) ⟨225417, by rfl⟩ : syracuseStep 2404453 = 450835) (by norm_num)
theorem B1781909 : Blo 790340 1781909 := bbase (se 6 (by rfl) ⟨41763, by rfl⟩ : syracuseStep 1781909 = 83527) (by norm_num)
theorem B1781981 : Blo 790340 1781981 := bbase (se 3 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 1781981 = 668243) (by norm_num)
theorem B1782053 : Blo 790340 1782053 := bbase (se 4 (by rfl) ⟨167067, by rfl⟩ : syracuseStep 1782053 = 334135) (by norm_num)
theorem B4010309 : Blo 790340 4010309 := bbase (se 4 (by rfl) ⟨375966, by rfl⟩ : syracuseStep 4010309 = 751933) (by norm_num)
theorem B1782125 : Blo 790340 1782125 := bbase (se 3 (by rfl) ⟨334148, by rfl⟩ : syracuseStep 1782125 = 668297) (by norm_num)
theorem B1126829 : Blo 790340 1126829 := bbase (se 3 (by rfl) ⟨211280, by rfl⟩ : syracuseStep 1126829 = 422561) (by norm_num)
theorem B1782197 : Blo 790340 1782197 := bbase (se 5 (by rfl) ⟨83540, by rfl⟩ : syracuseStep 1782197 = 167081) (by norm_num)
theorem B1126909 : Blo 790340 1126909 := bbase (se 3 (by rfl) ⟨211295, by rfl⟩ : syracuseStep 1126909 = 422591) (by norm_num)
theorem B1782269 : Blo 790340 1782269 := bbase (se 3 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 1782269 = 668351) (by norm_num)
theorem B1782341 : Blo 790340 1782341 := bbase (se 4 (by rfl) ⟨167094, by rfl⟩ : syracuseStep 1782341 = 334189) (by norm_num)
theorem B1127029 : Blo 790340 1127029 := bbase (se 5 (by rfl) ⟨52829, by rfl⟩ : syracuseStep 1127029 = 105659) (by norm_num)
theorem B1782413 : Blo 790340 1782413 := bbase (se 3 (by rfl) ⟨334202, by rfl⟩ : syracuseStep 1782413 = 668405) (by norm_num)
theorem B1127125 : Blo 790340 1127125 := bbase (se 7 (by rfl) ⟨13208, by rfl⟩ : syracuseStep 1127125 = 26417) (by norm_num)
theorem B1782485 : Blo 790340 1782485 := bbase (se 7 (by rfl) ⟨20888, by rfl⟩ : syracuseStep 1782485 = 41777) (by norm_num)
theorem B1782557 : Blo 790340 1782557 := bbase (se 3 (by rfl) ⟨334229, by rfl⟩ : syracuseStep 1782557 = 668459) (by norm_num)
theorem B963425 : Blo 790340 963425 := bbase (se 2 (by rfl) ⟨361284, by rfl⟩ : syracuseStep 963425 = 722569) (by norm_num)
theorem B1782629 : Blo 790340 1782629 := bbase (se 4 (by rfl) ⟨167121, by rfl⟩ : syracuseStep 1782629 = 334243) (by norm_num)
theorem B5714837 : Blo 790340 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B1782701 : Blo 790340 1782701 := bbase (se 3 (by rfl) ⟨334256, by rfl⟩ : syracuseStep 1782701 = 668513) (by norm_num)
theorem B1782773 : Blo 790340 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B1782845 : Blo 790340 1782845 := bbase (se 3 (by rfl) ⟨334283, by rfl⟩ : syracuseStep 1782845 = 668567) (by norm_num)
theorem B2667653 : Blo 790340 2667653 := bbase (se 4 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 2667653 = 500185) (by norm_num)
theorem B1782917 : Blo 790340 1782917 := bbase (se 4 (by rfl) ⟨167148, by rfl⟩ : syracuseStep 1782917 = 334297) (by norm_num)
theorem B1127621 : Blo 790340 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B1782989 : Blo 790340 1782989 := bbase (se 3 (by rfl) ⟨334310, by rfl⟩ : syracuseStep 1782989 = 668621) (by norm_num)
theorem B3257605 : Blo 790340 3257605 := bbase (se 4 (by rfl) ⟨305400, by rfl⟩ : syracuseStep 3257605 = 610801) (by norm_num)
theorem B1783061 : Blo 790340 1783061 := bbase (se 6 (by rfl) ⟨41790, by rfl⟩ : syracuseStep 1783061 = 83581) (by norm_num)
theorem B1783133 : Blo 790340 1783133 := bbase (se 3 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 1783133 = 668675) (by norm_num)
theorem B1783205 : Blo 790340 1783205 := bbase (se 4 (by rfl) ⟨167175, by rfl⟩ : syracuseStep 1783205 = 334351) (by norm_num)
theorem B1783277 : Blo 790340 1783277 := bbase (se 3 (by rfl) ⟨334364, by rfl⟩ : syracuseStep 1783277 = 668729) (by norm_num)
theorem B2668085 : Blo 790340 2668085 := bbase (se 5 (by rfl) ⟨125066, by rfl⟩ : syracuseStep 2668085 = 250133) (by norm_num)
theorem B1783349 : Blo 790340 1783349 := bbase (se 5 (by rfl) ⟨83594, by rfl⟩ : syracuseStep 1783349 = 167189) (by norm_num)
theorem B4011605 : Blo 790340 4011605 := bbase (se 8 (by rfl) ⟨23505, by rfl⟩ : syracuseStep 4011605 = 47011) (by norm_num)
theorem B1783421 : Blo 790340 1783421 := bbase (se 3 (by rfl) ⟨334391, by rfl⟩ : syracuseStep 1783421 = 668783) (by norm_num)
theorem B3815045 : Blo 790340 3815045 := bbase (se 4 (by rfl) ⟨357660, by rfl⟩ : syracuseStep 3815045 = 715321) (by norm_num)
theorem B1783493 : Blo 790340 1783493 := bbase (se 4 (by rfl) ⟨167202, by rfl⟩ : syracuseStep 1783493 = 334405) (by norm_num)
theorem B1128173 : Blo 790340 1128173 := bbase (se 3 (by rfl) ⟨211532, by rfl⟩ : syracuseStep 1128173 = 423065) (by norm_num)
theorem B1783565 : Blo 790340 1783565 := bbase (se 3 (by rfl) ⟨334418, by rfl⟩ : syracuseStep 1783565 = 668837) (by norm_num)
theorem B1783637 : Blo 790340 1783637 := bbase (se 9 (by rfl) ⟨5225, by rfl⟩ : syracuseStep 1783637 = 10451) (by norm_num)
theorem B2537365 : Blo 790340 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B1783709 : Blo 790340 1783709 := bbase (se 3 (by rfl) ⟨334445, by rfl⟩ : syracuseStep 1783709 = 668891) (by norm_num)
theorem B2668517 : Blo 790340 2668517 := bbase (se 4 (by rfl) ⟨250173, by rfl⟩ : syracuseStep 2668517 = 500347) (by norm_num)
theorem B1783781 : Blo 790340 1783781 := bbase (se 4 (by rfl) ⟨167229, by rfl⟩ : syracuseStep 1783781 = 334459) (by norm_num)
theorem B1783853 : Blo 790340 1783853 := bbase (se 3 (by rfl) ⟨334472, by rfl⟩ : syracuseStep 1783853 = 668945) (by norm_num)
theorem B1783925 : Blo 790340 1783925 := bbase (se 5 (by rfl) ⟨83621, by rfl⟩ : syracuseStep 1783925 = 167243) (by norm_num)
theorem B2144405 : Blo 790340 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B1783997 : Blo 790340 1783997 := bbase (se 3 (by rfl) ⟨334499, by rfl⟩ : syracuseStep 1783997 = 668999) (by norm_num)
theorem B1521877 : Blo 790340 1521877 := bbase (se 7 (by rfl) ⟨17834, by rfl⟩ : syracuseStep 1521877 = 35669) (by norm_num)
theorem B1784069 : Blo 790340 1784069 := bbase (se 4 (by rfl) ⟨167256, by rfl⟩ : syracuseStep 1784069 = 334513) (by norm_num)
theorem B1784141 : Blo 790340 1784141 := bbase (se 3 (by rfl) ⟨334526, by rfl⟩ : syracuseStep 1784141 = 669053) (by norm_num)
theorem B2668949 : Blo 790340 2668949 := bbase (se 6 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 2668949 = 125107) (by norm_num)
theorem B1784213 : Blo 790340 1784213 := bbase (se 6 (by rfl) ⟨41817, by rfl⟩ : syracuseStep 1784213 = 83635) (by norm_num)
theorem B1128925 : Blo 790340 1128925 := bbase (se 3 (by rfl) ⟨211673, by rfl⟩ : syracuseStep 1128925 = 423347) (by norm_num)
theorem B1784285 : Blo 790340 1784285 := bbase (se 3 (by rfl) ⟨334553, by rfl⟩ : syracuseStep 1784285 = 669107) (by norm_num)
theorem B1784357 : Blo 790340 1784357 := bbase (se 4 (by rfl) ⟨167283, by rfl⟩ : syracuseStep 1784357 = 334567) (by norm_num)
theorem B1522229 : Blo 790340 1522229 := bbase (se 5 (by rfl) ⟨71354, by rfl⟩ : syracuseStep 1522229 = 142709) (by norm_num)
theorem B1784429 : Blo 790340 1784429 := bbase (se 3 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 1784429 = 669161) (by norm_num)
theorem B1784501 : Blo 790340 1784501 := bbase (se 5 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 1784501 = 167297) (by norm_num)
theorem B2407141 : Blo 790340 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B1784573 : Blo 790340 1784573 := bbase (se 3 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 1784573 = 669215) (by norm_num)
theorem B3816197 : Blo 790340 3816197 := bbase (se 4 (by rfl) ⟨357768, by rfl⟩ : syracuseStep 3816197 = 715537) (by norm_num)
theorem B3390245 : Blo 790340 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B2669381 : Blo 790340 2669381 := bbase (se 4 (by rfl) ⟨250254, by rfl⟩ : syracuseStep 2669381 = 500509) (by norm_num)
theorem B1784645 : Blo 790340 1784645 := bbase (se 4 (by rfl) ⟨167310, by rfl⟩ : syracuseStep 1784645 = 334621) (by norm_num)
theorem B4012901 : Blo 790340 4012901 := bbase (se 4 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 4012901 = 752419) (by norm_num)
theorem B1784717 : Blo 790340 1784717 := bbase (se 3 (by rfl) ⟨334634, by rfl⟩ : syracuseStep 1784717 = 669269) (by norm_num)
theorem B1784789 : Blo 790340 1784789 := bbase (se 7 (by rfl) ⟨20915, by rfl⟩ : syracuseStep 1784789 = 41831) (by norm_num)
theorem B2407445 : Blo 790340 2407445 := bbase (se 6 (by rfl) ⟨56424, by rfl⟩ : syracuseStep 2407445 = 112849) (by norm_num)
theorem B1784861 : Blo 790340 1784861 := bbase (se 3 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 1784861 = 669323) (by norm_num)
theorem B1784933 : Blo 790340 1784933 := bbase (se 4 (by rfl) ⟨167337, by rfl⟩ : syracuseStep 1784933 = 334675) (by norm_num)
theorem B1785005 : Blo 790340 1785005 := bbase (se 3 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 1785005 = 669377) (by norm_num)
theorem B2669813 : Blo 790340 2669813 := bbase (se 5 (by rfl) ⟨125147, by rfl⟩ : syracuseStep 2669813 = 250295) (by norm_num)
theorem B1785077 : Blo 790340 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B1129717 : Blo 790340 1129717 := bbase (se 5 (by rfl) ⟨52955, by rfl⟩ : syracuseStep 1129717 = 105911) (by norm_num)
theorem B1424645 : Blo 790340 1424645 := bbase (se 4 (by rfl) ⟨133560, by rfl⟩ : syracuseStep 1424645 = 267121) (by norm_num)
theorem B1785149 : Blo 790340 1785149 := bbase (se 3 (by rfl) ⟨334715, by rfl⟩ : syracuseStep 1785149 = 669431) (by norm_num)
theorem B802121 : Blo 790340 802121 := bbase (se 2 (by rfl) ⟨300795, by rfl⟩ : syracuseStep 802121 = 601591) (by norm_num)
theorem B1785221 : Blo 790340 1785221 := bbase (se 4 (by rfl) ⟨167364, by rfl⟩ : syracuseStep 1785221 = 334729) (by norm_num)
theorem B1785293 : Blo 790340 1785293 := bbase (se 3 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 1785293 = 669485) (by norm_num)
theorem B3816965 : Blo 790340 3816965 := bbase (se 4 (by rfl) ⟨357840, by rfl⟩ : syracuseStep 3816965 = 715681) (by norm_num)
theorem B1785365 : Blo 790340 1785365 := bbase (se 6 (by rfl) ⟨41844, by rfl⟩ : syracuseStep 1785365 = 83689) (by norm_num)
theorem B1130053 : Blo 790340 1130053 := bbase (se 4 (by rfl) ⟨105942, by rfl⟩ : syracuseStep 1130053 = 211885) (by norm_num)
theorem B1785437 : Blo 790340 1785437 := bbase (se 3 (by rfl) ⟨334769, by rfl⟩ : syracuseStep 1785437 = 669539) (by norm_num)
theorem B2670245 : Blo 790340 2670245 := bbase (se 4 (by rfl) ⟨250335, by rfl⟩ : syracuseStep 2670245 = 500671) (by norm_num)
theorem B1785509 : Blo 790340 1785509 := bbase (se 4 (by rfl) ⟨167391, by rfl⟩ : syracuseStep 1785509 = 334783) (by norm_num)
theorem B1785581 : Blo 790340 1785581 := bbase (se 3 (by rfl) ⟨334796, by rfl⟩ : syracuseStep 1785581 = 669593) (by norm_num)
theorem B3391253 : Blo 790340 3391253 := bbase (se 6 (by rfl) ⟨79482, by rfl⟩ : syracuseStep 3391253 = 158965) (by norm_num)
theorem B1130269 : Blo 790340 1130269 := bbase (se 3 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 1130269 = 423851) (by norm_num)
theorem B1785653 : Blo 790340 1785653 := bbase (se 5 (by rfl) ⟨83702, by rfl⟩ : syracuseStep 1785653 = 167405) (by norm_num)
theorem B3620693 : Blo 790340 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B1785725 : Blo 790340 1785725 := bbase (se 3 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 1785725 = 669647) (by norm_num)
theorem B1785797 : Blo 790340 1785797 := bbase (se 4 (by rfl) ⟨167418, by rfl⟩ : syracuseStep 1785797 = 334837) (by norm_num)
theorem B1425365 : Blo 790340 1425365 := bbase (se 7 (by rfl) ⟨16703, by rfl⟩ : syracuseStep 1425365 = 33407) (by norm_num)
theorem B20299733 : Blo 790340 20299733 := bbase (se 7 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 20299733 = 475775) (by norm_num)
theorem B1523677 : Blo 790340 1523677 := bbase (se 3 (by rfl) ⟨285689, by rfl⟩ : syracuseStep 1523677 = 571379) (by norm_num)
theorem B1785869 : Blo 790340 1785869 := bbase (se 3 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 1785869 = 669701) (by norm_num)
theorem B2670677 : Blo 790340 2670677 := bbase (se 8 (by rfl) ⟨15648, by rfl⟩ : syracuseStep 2670677 = 31297) (by norm_num)
theorem B1785941 : Blo 790340 1785941 := bbase (se 8 (by rfl) ⟨10464, by rfl⟩ : syracuseStep 1785941 = 20929) (by norm_num)
theorem B4014197 : Blo 790340 4014197 := bbase (se 5 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 4014197 = 376331) (by norm_num)
theorem B1130645 : Blo 790340 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B1786013 : Blo 790340 1786013 := bbase (se 3 (by rfl) ⟨334877, by rfl⟩ : syracuseStep 1786013 = 669755) (by norm_num)
theorem B4505813 : Blo 790340 4505813 := bbase (se 7 (by rfl) ⟨52802, by rfl⟩ : syracuseStep 4505813 = 105605) (by norm_num)
theorem B1786085 : Blo 790340 1786085 := bbase (se 4 (by rfl) ⟨167445, by rfl⟩ : syracuseStep 1786085 = 334891) (by norm_num)
theorem B901369 : Blo 790340 901369 := bbase (se 2 (by rfl) ⟨338013, by rfl⟩ : syracuseStep 901369 = 676027) (by norm_num)
theorem B868601 : Blo 790340 868601 := bbase (se 2 (by rfl) ⟨325725, by rfl⟩ : syracuseStep 868601 = 651451) (by norm_num)
theorem B1786157 : Blo 790340 1786157 := bbase (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) (by norm_num)
theorem B1524077 : Blo 790340 1524077 := bbase (se 3 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 1524077 = 571529) (by norm_num)
theorem B1786229 : Blo 790340 1786229 := bbase (se 5 (by rfl) ⟨83729, by rfl⟩ : syracuseStep 1786229 = 167459) (by norm_num)
theorem B1786301 : Blo 790340 1786301 := bbase (se 3 (by rfl) ⟨334931, by rfl⟩ : syracuseStep 1786301 = 669863) (by norm_num)
theorem B2671109 : Blo 790340 2671109 := bbase (se 4 (by rfl) ⟨250416, by rfl⟩ : syracuseStep 2671109 = 500833) (by norm_num)
theorem B1786373 : Blo 790340 1786373 := bbase (se 4 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 1786373 = 334945) (by norm_num)
theorem B6439445 : Blo 790340 6439445 := bbase (se 6 (by rfl) ⟨150924, by rfl⟩ : syracuseStep 6439445 = 301849) (by norm_num)
theorem B1786445 : Blo 790340 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B1786517 : Blo 790340 1786517 := bbase (se 6 (by rfl) ⟨41871, by rfl⟩ : syracuseStep 1786517 = 83743) (by norm_num)
theorem B3424949 : Blo 790340 3424949 := bbase (se 5 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 3424949 = 321089) (by norm_num)
theorem B1786589 : Blo 790340 1786589 := bbase (se 3 (by rfl) ⟨334985, by rfl⟩ : syracuseStep 1786589 = 669971) (by norm_num)
theorem B2540261 : Blo 790340 2540261 := bbase (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) (by norm_num)
theorem B1688357 : Blo 790340 1688357 := bbase (se 4 (by rfl) ⟨158283, by rfl⟩ : syracuseStep 1688357 = 316567) (by norm_num)
theorem B1786661 : Blo 790340 1786661 := bbase (se 4 (by rfl) ⟨167499, by rfl⟩ : syracuseStep 1786661 = 334999) (by norm_num)
theorem B803633 : Blo 790340 803633 := bbase (se 2 (by rfl) ⟨301362, by rfl⟩ : syracuseStep 803633 = 602725) (by norm_num)
theorem B1000289 : Blo 790340 1000289 := bbase (se 2 (by rfl) ⟨375108, by rfl⟩ : syracuseStep 1000289 = 750217) (by norm_num)
theorem B1786733 : Blo 790340 1786733 := bbase (se 3 (by rfl) ⟨335012, by rfl⟩ : syracuseStep 1786733 = 670025) (by norm_num)
theorem B1000345 : Blo 790340 1000345 := bbase (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) (by norm_num)
theorem B1688501 : Blo 790340 1688501 := bbase (se 5 (by rfl) ⟨79148, by rfl⟩ : syracuseStep 1688501 = 158297) (by norm_num)
theorem B2671541 : Blo 790340 2671541 := bbase (se 5 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 2671541 = 250457) (by norm_num)
theorem B1786805 : Blo 790340 1786805 := bbase (se 5 (by rfl) ⟨83756, by rfl⟩ : syracuseStep 1786805 = 167513) (by norm_num)
theorem B1000441 : Blo 790340 1000441 := bbase (se 2 (by rfl) ⟨375165, by rfl⟩ : syracuseStep 1000441 = 750331) (by norm_num)
theorem B1786877 : Blo 790340 1786877 := bbase (se 3 (by rfl) ⟨335039, by rfl⟩ : syracuseStep 1786877 = 670079) (by norm_num)
theorem B1786949 : Blo 790340 1786949 := bbase (se 4 (by rfl) ⟨167526, by rfl⟩ : syracuseStep 1786949 = 335053) (by norm_num)
theorem B902245 : Blo 790340 902245 := bbase (se 4 (by rfl) ⟨84585, by rfl⟩ : syracuseStep 902245 = 169171) (by norm_num)
theorem B1787021 : Blo 790340 1787021 := bbase (se 3 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 1787021 = 670133) (by norm_num)
theorem B1000613 : Blo 790340 1000613 := bbase (se 4 (by rfl) ⟨93807, by rfl⟩ : syracuseStep 1000613 = 187615) (by norm_num)
theorem B1787093 : Blo 790340 1787093 := bbase (se 7 (by rfl) ⟨20942, by rfl⟩ : syracuseStep 1787093 = 41885) (by norm_num)
theorem B1000669 : Blo 790340 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B3622117 : Blo 790340 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B836893 : Blo 790340 836893 := bbase (se 3 (by rfl) ⟨156917, by rfl⟩ : syracuseStep 836893 = 313835) (by norm_num)
theorem B1787165 : Blo 790340 1787165 := bbase (se 3 (by rfl) ⟨335093, by rfl⟩ : syracuseStep 1787165 = 670187) (by norm_num)
theorem B1000765 : Blo 790340 1000765 := bbase (se 3 (by rfl) ⟨187643, by rfl⟩ : syracuseStep 1000765 = 375287) (by norm_num)
theorem B2671973 : Blo 790340 2671973 := bbase (se 4 (by rfl) ⟨250497, by rfl⟩ : syracuseStep 2671973 = 500995) (by norm_num)
theorem B1787237 : Blo 790340 1787237 := bbase (se 4 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 1787237 = 335107) (by norm_num)
theorem B4015493 : Blo 790340 4015493 := bbase (se 4 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 4015493 = 752905) (by norm_num)
theorem B1000937 : Blo 790340 1000937 := bbase (se 2 (by rfl) ⟨375351, by rfl⟩ : syracuseStep 1000937 = 750703) (by norm_num)
theorem B1000993 : Blo 790340 1000993 := bbase (se 2 (by rfl) ⟨375372, by rfl⟩ : syracuseStep 1000993 = 750745) (by norm_num)
theorem B902765 : Blo 790340 902765 := bbase (se 3 (by rfl) ⟨169268, by rfl⟩ : syracuseStep 902765 = 338537) (by norm_num)
theorem B1001089 : Blo 790340 1001089 := bbase (se 2 (by rfl) ⟨375408, by rfl⟩ : syracuseStep 1001089 = 750817) (by norm_num)
theorem B1689245 : Blo 790340 1689245 := bbase (se 3 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 1689245 = 633467) (by norm_num)
theorem B2672405 : Blo 790340 2672405 := bbase (se 6 (by rfl) ⟨62634, by rfl⟩ : syracuseStep 2672405 = 125269) (by norm_num)
theorem B1001261 : Blo 790340 1001261 := bbase (se 3 (by rfl) ⟨187736, by rfl⟩ : syracuseStep 1001261 = 375473) (by norm_num)
theorem B1001317 : Blo 790340 1001317 := bbase (se 4 (by rfl) ⟨93873, by rfl⟩ : syracuseStep 1001317 = 187747) (by norm_num)
theorem B1001413 : Blo 790340 1001413 := bbase (se 4 (by rfl) ⟨93882, by rfl⟩ : syracuseStep 1001413 = 187765) (by norm_num)
theorem B6768629 : Blo 790340 6768629 := bbase (se 5 (by rfl) ⟨317279, by rfl⟩ : syracuseStep 6768629 = 634559) (by norm_num)
theorem B2541557 : Blo 790340 2541557 := bbase (se 5 (by rfl) ⟨119135, by rfl⟩ : syracuseStep 2541557 = 238271) (by norm_num)
theorem B1001585 : Blo 790340 1001585 := bbase (se 2 (by rfl) ⟨375594, by rfl⟩ : syracuseStep 1001585 = 751189) (by norm_num)
theorem B1001641 : Blo 790340 1001641 := bbase (se 2 (by rfl) ⟨375615, by rfl⟩ : syracuseStep 1001641 = 751231) (by norm_num)
theorem B903349 : Blo 790340 903349 := bbase (se 5 (by rfl) ⟨42344, by rfl⟩ : syracuseStep 903349 = 84689) (by norm_num)
theorem B2672837 : Blo 790340 2672837 := bbase (se 4 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 2672837 = 501157) (by norm_num)
theorem B6015221 : Blo 790340 6015221 := bbase (se 5 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 6015221 = 563927) (by norm_num)
theorem B1427701 : Blo 790340 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B1001737 : Blo 790340 1001737 := bbase (se 2 (by rfl) ⟨375651, by rfl⟩ : syracuseStep 1001737 = 751303) (by norm_num)
theorem B1689997 : Blo 790340 1689997 := bbase (se 3 (by rfl) ⟨316874, by rfl⟩ : syracuseStep 1689997 = 633749) (by norm_num)
theorem B1001909 : Blo 790340 1001909 := bbase (se 5 (by rfl) ⟨46964, by rfl⟩ : syracuseStep 1001909 = 93929) (by norm_num)
theorem B21121493 : Blo 790340 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B870869 : Blo 790340 870869 := bbase (se 7 (by rfl) ⟨10205, by rfl⟩ : syracuseStep 870869 = 20411) (by norm_num)
theorem B1001965 : Blo 790340 1001965 := bbase (se 3 (by rfl) ⟨187868, by rfl⟩ : syracuseStep 1001965 = 375737) (by norm_num)
theorem B1690141 : Blo 790340 1690141 := bbase (se 3 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 1690141 = 633803) (by norm_num)
theorem B1002061 : Blo 790340 1002061 := bbase (se 3 (by rfl) ⟨187886, by rfl⟩ : syracuseStep 1002061 = 375773) (by norm_num)
theorem B2673269 : Blo 790340 2673269 := bbase (se 5 (by rfl) ⟨125309, by rfl⟩ : syracuseStep 2673269 = 250619) (by norm_num)
theorem B4016789 : Blo 790340 4016789 := bbase (se 6 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 4016789 = 188287) (by norm_num)
theorem B1428133 : Blo 790340 1428133 := bbase (se 4 (by rfl) ⟨133887, by rfl⟩ : syracuseStep 1428133 = 267775) (by norm_num)
theorem B1002233 : Blo 790340 1002233 := bbase (se 2 (by rfl) ⟨375837, by rfl⟩ : syracuseStep 1002233 = 751675) (by norm_num)
theorem B1002289 : Blo 790340 1002289 := bbase (se 2 (by rfl) ⟨375858, by rfl⟩ : syracuseStep 1002289 = 751717) (by norm_num)
theorem B3001157 : Blo 790340 3001157 := bbase (se 4 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 3001157 = 562717) (by norm_num)
theorem B1002385 : Blo 790340 1002385 := bbase (se 2 (by rfl) ⟨375894, by rfl⟩ : syracuseStep 1002385 = 751789) (by norm_num)
theorem B1690517 : Blo 790340 1690517 := bbase (se 6 (by rfl) ⟨39621, by rfl⟩ : syracuseStep 1690517 = 79243) (by norm_num)
theorem B5065685 : Blo 790340 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B2673701 : Blo 790340 2673701 := bbase (se 4 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 2673701 = 501319) (by norm_num)
theorem B1002557 : Blo 790340 1002557 := bbase (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) (by norm_num)
theorem B3001445 : Blo 790340 3001445 := bbase (se 4 (by rfl) ⟨281385, by rfl⟩ : syracuseStep 3001445 = 562771) (by norm_num)
theorem B1002613 : Blo 790340 1002613 := bbase (se 5 (by rfl) ⟨46997, by rfl⟩ : syracuseStep 1002613 = 93995) (by norm_num)
theorem B1428653 : Blo 790340 1428653 := bbase (se 3 (by rfl) ⟨267872, by rfl⟩ : syracuseStep 1428653 = 535745) (by norm_num)
theorem B904397 : Blo 790340 904397 := bbase (se 3 (by rfl) ⟨169574, by rfl⟩ : syracuseStep 904397 = 339149) (by norm_num)
theorem B1002709 : Blo 790340 1002709 := bbase (se 7 (by rfl) ⟨11750, by rfl⟩ : syracuseStep 1002709 = 23501) (by norm_num)
theorem B1690885 : Blo 790340 1690885 := bbase (se 4 (by rfl) ⟨158520, by rfl⟩ : syracuseStep 1690885 = 317041) (by norm_num)
theorem B1002881 : Blo 790340 1002881 := bbase (se 2 (by rfl) ⟨376080, by rfl⟩ : syracuseStep 1002881 = 752161) (by norm_num)
theorem B1002937 : Blo 790340 1002937 := bbase (se 2 (by rfl) ⟨376101, by rfl⟩ : syracuseStep 1002937 = 752203) (by norm_num)
theorem B1428941 : Blo 790340 1428941 := bbase (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) (by norm_num)
theorem B2674133 : Blo 790340 2674133 := bbase (se 7 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 2674133 = 62675) (by norm_num)
theorem B1003033 : Blo 790340 1003033 := bbase (se 2 (by rfl) ⟨376137, by rfl⟩ : syracuseStep 1003033 = 752275) (by norm_num)
theorem B1003205 : Blo 790340 1003205 := bbase (se 4 (by rfl) ⟨94050, by rfl⟩ : syracuseStep 1003205 = 188101) (by norm_num)
theorem B1003261 : Blo 790340 1003261 := bbase (se 3 (by rfl) ⟨188111, by rfl⟩ : syracuseStep 1003261 = 376223) (by norm_num)
theorem B2543413 : Blo 790340 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B1003357 : Blo 790340 1003357 := bbase (se 3 (by rfl) ⟨188129, by rfl⟩ : syracuseStep 1003357 = 376259) (by norm_num)
theorem B1429373 : Blo 790340 1429373 := bbase (se 3 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 1429373 = 536015) (by norm_num)
theorem B2674565 : Blo 790340 2674565 := bbase (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) (by norm_num)
theorem B4018085 : Blo 790340 4018085 := bbase (se 4 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 4018085 = 753391) (by norm_num)
theorem B1003529 : Blo 790340 1003529 := bbase (se 2 (by rfl) ⟨376323, by rfl⟩ : syracuseStep 1003529 = 752647) (by norm_num)
theorem B1429517 : Blo 790340 1429517 := bbase (se 3 (by rfl) ⟨268034, by rfl⟩ : syracuseStep 1429517 = 536069) (by norm_num)
theorem B8572949 : Blo 790340 8572949 := bbase (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) (by norm_num)
theorem B1003585 : Blo 790340 1003585 := bbase (se 2 (by rfl) ⟨376344, by rfl⟩ : syracuseStep 1003585 = 752689) (by norm_num)
theorem B1003681 : Blo 790340 1003681 := bbase (se 2 (by rfl) ⟨376380, by rfl⟩ : syracuseStep 1003681 = 752761) (by norm_num)
theorem B3002629 : Blo 790340 3002629 := bbase (se 4 (by rfl) ⟨281496, by rfl⟩ : syracuseStep 3002629 = 562993) (by norm_num)
theorem B2674997 : Blo 790340 2674997 := bbase (se 5 (by rfl) ⟨125390, by rfl⟩ : syracuseStep 2674997 = 250781) (by norm_num)
theorem B1003853 : Blo 790340 1003853 := bbase (se 3 (by rfl) ⟨188222, by rfl⟩ : syracuseStep 1003853 = 376445) (by norm_num)
theorem B1528141 : Blo 790340 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B1003909 : Blo 790340 1003909 := bbase (se 4 (by rfl) ⟨94116, by rfl⟩ : syracuseStep 1003909 = 188233) (by norm_num)
theorem B1266133 : Blo 790340 1266133 := bbase (se 7 (by rfl) ⟨14837, by rfl⟩ : syracuseStep 1266133 = 29675) (by norm_num)
theorem B1004005 : Blo 790340 1004005 := bbase (se 4 (by rfl) ⟨94125, by rfl⟩ : syracuseStep 1004005 = 188251) (by norm_num)
theorem B1069597 : Blo 790340 1069597 := bbase (se 3 (by rfl) ⟨200549, by rfl⟩ : syracuseStep 1069597 = 401099) (by norm_num)
theorem B3002933 : Blo 790340 3002933 := bbase (se 5 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 3002933 = 281525) (by norm_num)
theorem B1004177 : Blo 790340 1004177 := bbase (se 2 (by rfl) ⟨376566, by rfl⟩ : syracuseStep 1004177 = 753133) (by norm_num)
theorem B1004233 : Blo 790340 1004233 := bbase (se 2 (by rfl) ⟨376587, by rfl⟩ : syracuseStep 1004233 = 753175) (by norm_num)
theorem B1692389 : Blo 790340 1692389 := bbase (se 4 (by rfl) ⟨158661, by rfl⟩ : syracuseStep 1692389 = 317323) (by norm_num)
theorem B2675429 : Blo 790340 2675429 := bbase (se 4 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 2675429 = 501643) (by norm_num)
theorem B1004329 : Blo 790340 1004329 := bbase (se 2 (by rfl) ⟨376623, by rfl⟩ : syracuseStep 1004329 = 753247) (by norm_num)
theorem B1692533 : Blo 790340 1692533 := bbase (se 5 (by rfl) ⟨79337, by rfl⟩ : syracuseStep 1692533 = 158675) (by norm_num)
theorem B1266581 : Blo 790340 1266581 := bbase (se 6 (by rfl) ⟨29685, by rfl⟩ : syracuseStep 1266581 = 59371) (by norm_num)
theorem B1004501 : Blo 790340 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B1004557 : Blo 790340 1004557 := bbase (se 3 (by rfl) ⟨188354, by rfl⟩ : syracuseStep 1004557 = 376709) (by norm_num)
theorem B1430549 : Blo 790340 1430549 := bbase (se 6 (by rfl) ⟨33528, by rfl⟩ : syracuseStep 1430549 = 67057) (by norm_num)
theorem B2282597 : Blo 790340 2282597 := bbase (se 4 (by rfl) ⟨213993, by rfl⟩ : syracuseStep 2282597 = 427987) (by norm_num)
theorem B1004653 : Blo 790340 1004653 := bbase (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) (by norm_num)
theorem B2675861 : Blo 790340 2675861 := bbase (se 6 (by rfl) ⟨62715, by rfl⟩ : syracuseStep 2675861 = 125431) (by norm_num)
theorem B4019381 : Blo 790340 4019381 := bbase (se 5 (by rfl) ⟨188408, by rfl⟩ : syracuseStep 4019381 = 376817) (by norm_num)
theorem B1692893 : Blo 790340 1692893 := bbase (se 3 (by rfl) ⟨317417, by rfl⟩ : syracuseStep 1692893 = 634835) (by norm_num)
theorem B3855637 : Blo 790340 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B1004825 : Blo 790340 1004825 := bbase (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) (by norm_num)
theorem B1004881 : Blo 790340 1004881 := bbase (se 2 (by rfl) ⟨376830, by rfl⟩ : syracuseStep 1004881 = 753661) (by norm_num)
theorem B1004977 : Blo 790340 1004977 := bbase (se 2 (by rfl) ⟨376866, by rfl⟩ : syracuseStep 1004977 = 753733) (by norm_num)
theorem B1070533 : Blo 790340 1070533 := bbase (se 4 (by rfl) ⟨100362, by rfl⟩ : syracuseStep 1070533 = 200725) (by norm_num)
theorem B2676293 : Blo 790340 2676293 := bbase (se 4 (by rfl) ⟨250902, by rfl⟩ : syracuseStep 2676293 = 501805) (by norm_num)
theorem B1005149 : Blo 790340 1005149 := bbase (se 3 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 1005149 = 376931) (by norm_num)
theorem B1005205 : Blo 790340 1005205 := bbase (se 6 (by rfl) ⟨23559, by rfl⟩ : syracuseStep 1005205 = 47119) (by norm_num)
theorem B1005301 : Blo 790340 1005301 := bbase (se 5 (by rfl) ⟨47123, by rfl⟩ : syracuseStep 1005301 = 94247) (by norm_num)
theorem B2250629 : Blo 790340 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B2414549 : Blo 790340 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B2676725 : Blo 790340 2676725 := bbase (se 5 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 2676725 = 250943) (by norm_num)
theorem B2414645 : Blo 790340 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B1693781 : Blo 790340 1693781 := bbase (se 8 (by rfl) ⟨9924, by rfl⟩ : syracuseStep 1693781 = 19849) (by norm_num)
theorem B2251061 : Blo 790340 2251061 := bbase (se 5 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 2251061 = 211037) (by norm_num)
theorem B1694029 : Blo 790340 1694029 := bbase (se 3 (by rfl) ⟨317630, by rfl⟩ : syracuseStep 1694029 = 635261) (by norm_num)
theorem B1268093 : Blo 790340 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B2677157 : Blo 790340 2677157 := bbase (se 4 (by rfl) ⟨250983, by rfl⟩ : syracuseStep 2677157 = 501967) (by norm_num)
theorem B4020677 : Blo 790340 4020677 := bbase (se 4 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 4020677 = 753877) (by norm_num)
theorem B1268221 : Blo 790340 1268221 := bbase (se 3 (by rfl) ⟨237791, by rfl⟩ : syracuseStep 1268221 = 475583) (by norm_num)
theorem B1333813 : Blo 790340 1333813 := bbase (se 5 (by rfl) ⟨62522, by rfl⟩ : syracuseStep 1333813 = 125045) (by norm_num)
theorem B2447941 : Blo 790340 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B6085205 : Blo 790340 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B3005045 : Blo 790340 3005045 := bbase (se 5 (by rfl) ⟨140861, by rfl⟩ : syracuseStep 3005045 = 281723) (by norm_num)
theorem B1333901 : Blo 790340 1333901 := bbase (se 3 (by rfl) ⟨250106, by rfl⟩ : syracuseStep 1333901 = 500213) (by norm_num)
theorem B1334029 : Blo 790340 1334029 := bbase (se 3 (by rfl) ⟨250130, by rfl⟩ : syracuseStep 1334029 = 500261) (by norm_num)
theorem B1694533 : Blo 790340 1694533 := bbase (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) (by norm_num)
theorem B2677589 : Blo 790340 2677589 := bbase (se 9 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 2677589 = 15689) (by norm_num)
theorem B1334117 : Blo 790340 1334117 := bbase (se 4 (by rfl) ⟨125073, by rfl⟩ : syracuseStep 1334117 = 250147) (by norm_num)
theorem B3005333 : Blo 790340 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B1334245 : Blo 790340 1334245 := bbase (se 4 (by rfl) ⟨125085, by rfl⟩ : syracuseStep 1334245 = 250171) (by norm_num)
theorem B5790709 : Blo 790340 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B2251813 : Blo 790340 2251813 := bbase (se 4 (by rfl) ⟨211107, by rfl⟩ : syracuseStep 2251813 = 422215) (by norm_num)
theorem B1334333 : Blo 790340 1334333 := bbase (se 3 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 1334333 = 500375) (by norm_num)
theorem B1334461 : Blo 790340 1334461 := bbase (se 3 (by rfl) ⟨250211, by rfl⟩ : syracuseStep 1334461 = 500423) (by norm_num)
theorem B2678021 : Blo 790340 2678021 := bbase (se 4 (by rfl) ⟨251064, by rfl⟩ : syracuseStep 2678021 = 502129) (by norm_num)
theorem B1072397 : Blo 790340 1072397 := bbase (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) (by norm_num)
theorem B1334549 : Blo 790340 1334549 := bbase (se 6 (by rfl) ⟨31278, by rfl⟩ : syracuseStep 1334549 = 62557) (by norm_num)
theorem B1334677 : Blo 790340 1334677 := bbase (se 6 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 1334677 = 62563) (by norm_num)
theorem B1072549 : Blo 790340 1072549 := bbase (se 4 (by rfl) ⟨100551, by rfl⟩ : syracuseStep 1072549 = 201103) (by norm_num)
theorem B1334765 : Blo 790340 1334765 := bbase (se 3 (by rfl) ⟨250268, by rfl⟩ : syracuseStep 1334765 = 500537) (by norm_num)
theorem B1334893 : Blo 790340 1334893 := bbase (se 3 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 1334893 = 500585) (by norm_num)
theorem B4284053 : Blo 790340 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B2678453 : Blo 790340 2678453 := bbase (se 5 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 2678453 = 251105) (by norm_num)
theorem B1695421 : Blo 790340 1695421 := bbase (se 3 (by rfl) ⟨317891, by rfl⟩ : syracuseStep 1695421 = 635783) (by norm_num)
theorem B1334981 : Blo 790340 1334981 := bbase (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) (by norm_num)
theorem B1335109 : Blo 790340 1335109 := bbase (se 4 (by rfl) ⟨125166, by rfl⟩ : syracuseStep 1335109 = 250333) (by norm_num)
theorem B1269605 : Blo 790340 1269605 := bbase (se 4 (by rfl) ⟨119025, by rfl⟩ : syracuseStep 1269605 = 238051) (by norm_num)
theorem B1335197 : Blo 790340 1335197 := bbase (se 3 (by rfl) ⟨250349, by rfl⟩ : syracuseStep 1335197 = 500699) (by norm_num)
theorem B1335325 : Blo 790340 1335325 := bbase (se 3 (by rfl) ⟨250373, by rfl⟩ : syracuseStep 1335325 = 500747) (by norm_num)
theorem B3006517 : Blo 790340 3006517 := bbase (se 5 (by rfl) ⟨140930, by rfl⟩ : syracuseStep 3006517 = 281861) (by norm_num)
theorem B4513877 : Blo 790340 4513877 := bbase (se 8 (by rfl) ⟨26448, by rfl⟩ : syracuseStep 4513877 = 52897) (by norm_num)
theorem B2678885 : Blo 790340 2678885 := bbase (se 4 (by rfl) ⟨251145, by rfl⟩ : syracuseStep 2678885 = 502291) (by norm_num)
theorem B1335413 : Blo 790340 1335413 := bbase (se 5 (by rfl) ⟨62597, by rfl⟩ : syracuseStep 1335413 = 125195) (by norm_num)
theorem B1695917 : Blo 790340 1695917 := bbase (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) (by norm_num)
theorem B1335541 : Blo 790340 1335541 := bbase (se 5 (by rfl) ⟨62603, by rfl⟩ : syracuseStep 1335541 = 125207) (by norm_num)
theorem B1335629 : Blo 790340 1335629 := bbase (se 3 (by rfl) ⟨250430, by rfl⟩ : syracuseStep 1335629 = 500861) (by norm_num)
theorem B5431637 : Blo 790340 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B3006821 : Blo 790340 3006821 := bbase (se 4 (by rfl) ⟨281889, by rfl⟩ : syracuseStep 3006821 = 563779) (by norm_num)
theorem B844165 : Blo 790340 844165 := bbase (se 4 (by rfl) ⟨79140, by rfl⟩ : syracuseStep 844165 = 158281) (by norm_num)
theorem B1335757 : Blo 790340 1335757 := bbase (se 3 (by rfl) ⟨250454, by rfl⟩ : syracuseStep 1335757 = 500909) (by norm_num)
theorem B2679317 : Blo 790340 2679317 := bbase (se 6 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 2679317 = 125593) (by norm_num)
theorem B1335845 : Blo 790340 1335845 := bbase (se 4 (by rfl) ⟨125235, by rfl⟩ : syracuseStep 1335845 = 250471) (by norm_num)
theorem B844349 : Blo 790340 844349 := bbase (se 3 (by rfl) ⟨158315, by rfl⟩ : syracuseStep 844349 = 316631) (by norm_num)
theorem B1335973 : Blo 790340 1335973 := bbase (se 4 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 1335973 = 250495) (by norm_num)
theorem B1336061 : Blo 790340 1336061 := bbase (se 3 (by rfl) ⟨250511, by rfl⟩ : syracuseStep 1336061 = 501023) (by norm_num)
theorem B1270541 : Blo 790340 1270541 := bbase (se 3 (by rfl) ⟨238226, by rfl⟩ : syracuseStep 1270541 = 476453) (by norm_num)
theorem B1631069 : Blo 790340 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B7725941 : Blo 790340 7725941 := bbase (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) (by norm_num)
theorem B1336189 : Blo 790340 1336189 := bbase (se 3 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 1336189 = 501071) (by norm_num)
theorem B2679749 : Blo 790340 2679749 := bbase (se 4 (by rfl) ⟨251226, by rfl⟩ : syracuseStep 2679749 = 502453) (by norm_num)
theorem B1336277 : Blo 790340 1336277 := bbase (se 7 (by rfl) ⟨15659, by rfl⟩ : syracuseStep 1336277 = 31319) (by norm_num)
theorem B1336405 : Blo 790340 1336405 := bbase (se 8 (by rfl) ⟨7830, by rfl⟩ : syracuseStep 1336405 = 15661) (by norm_num)
theorem B1336493 : Blo 790340 1336493 := bbase (se 3 (by rfl) ⟨250592, by rfl⟩ : syracuseStep 1336493 = 501185) (by norm_num)
theorem B4515061 : Blo 790340 4515061 := bbase (se 5 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 4515061 = 423287) (by norm_num)
theorem B845101 : Blo 790340 845101 := bbase (se 3 (by rfl) ⟨158456, by rfl⟩ : syracuseStep 845101 = 316913) (by norm_num)
theorem B1336621 : Blo 790340 1336621 := bbase (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) (by norm_num)
theorem B38495573 : Blo 790340 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B845173 : Blo 790340 845173 := bbase (se 5 (by rfl) ⟨39617, by rfl⟩ : syracuseStep 845173 = 79235) (by norm_num)
theorem B2680181 : Blo 790340 2680181 := bbase (se 5 (by rfl) ⟨125633, by rfl⟩ : syracuseStep 2680181 = 251267) (by norm_num)
theorem B1336709 : Blo 790340 1336709 := bbase (se 4 (by rfl) ⟨125316, by rfl⟩ : syracuseStep 1336709 = 250633) (by norm_num)
theorem B1271189 : Blo 790340 1271189 := bbase (se 6 (by rfl) ⟨29793, by rfl⟩ : syracuseStep 1271189 = 59587) (by norm_num)
theorem B1500677 : Blo 790340 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B1336837 : Blo 790340 1336837 := bbase (se 4 (by rfl) ⟨125328, by rfl⟩ : syracuseStep 1336837 = 250657) (by norm_num)
theorem B845353 : Blo 790340 845353 := bbase (se 2 (by rfl) ⟨317007, by rfl⟩ : syracuseStep 845353 = 634015) (by norm_num)
theorem B1336925 : Blo 790340 1336925 := bbase (se 3 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 1336925 = 501347) (by norm_num)
theorem B1337053 : Blo 790340 1337053 := bbase (se 3 (by rfl) ⟨250697, by rfl⟩ : syracuseStep 1337053 = 501395) (by norm_num)
theorem B2680613 : Blo 790340 2680613 := bbase (se 4 (by rfl) ⟨251307, by rfl⟩ : syracuseStep 2680613 = 502615) (by norm_num)
theorem B1337141 : Blo 790340 1337141 := bbase (se 5 (by rfl) ⟨62678, by rfl⟩ : syracuseStep 1337141 = 125357) (by norm_num)
theorem B1828669 : Blo 790340 1828669 := bbase (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) (by norm_num)
theorem B2254661 : Blo 790340 2254661 := bbase (se 4 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 2254661 = 422749) (by norm_num)
theorem B6022997 : Blo 790340 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B1206101 : Blo 790340 1206101 := bbase (se 9 (by rfl) ⟨3533, by rfl⟩ : syracuseStep 1206101 = 7067) (by norm_num)
theorem B6776693 : Blo 790340 6776693 := bbase (se 5 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 6776693 = 635315) (by norm_num)
theorem B1337269 : Blo 790340 1337269 := bbase (se 5 (by rfl) ⟨62684, by rfl⟩ : syracuseStep 1337269 = 125369) (by norm_num)
theorem B845797 : Blo 790340 845797 := bbase (se 4 (by rfl) ⟨79293, by rfl⟩ : syracuseStep 845797 = 158587) (by norm_num)
theorem B1337357 : Blo 790340 1337357 := bbase (se 3 (by rfl) ⟨250754, by rfl⟩ : syracuseStep 1337357 = 501509) (by norm_num)
theorem B845921 : Blo 790340 845921 := bbase (se 2 (by rfl) ⟨317220, by rfl⟩ : syracuseStep 845921 = 634441) (by norm_num)
theorem B6514805 : Blo 790340 6514805 := bbase (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) (by norm_num)
theorem B1337485 : Blo 790340 1337485 := bbase (se 3 (by rfl) ⟨250778, by rfl⟩ : syracuseStep 1337485 = 501557) (by norm_num)
theorem B1337573 : Blo 790340 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B1501429 : Blo 790340 1501429 := bbase (se 5 (by rfl) ⟨70379, by rfl⟩ : syracuseStep 1501429 = 140759) (by norm_num)
theorem B846173 : Blo 790340 846173 := bbase (se 3 (by rfl) ⟨158657, by rfl⟩ : syracuseStep 846173 = 317315) (by norm_num)
theorem B1337701 : Blo 790340 1337701 := bbase (se 4 (by rfl) ⟨125409, by rfl⟩ : syracuseStep 1337701 = 250819) (by norm_num)
theorem B1272181 : Blo 790340 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B1501573 : Blo 790340 1501573 := bbase (se 4 (by rfl) ⟨140772, by rfl⟩ : syracuseStep 1501573 = 281545) (by norm_num)
theorem B1206685 : Blo 790340 1206685 := bbase (se 3 (by rfl) ⟨226253, by rfl⟩ : syracuseStep 1206685 = 452507) (by norm_num)
theorem B3008933 : Blo 790340 3008933 := bbase (se 4 (by rfl) ⟨282087, by rfl⟩ : syracuseStep 3008933 = 564175) (by norm_num)
theorem B1337789 : Blo 790340 1337789 := bbase (se 3 (by rfl) ⟨250835, by rfl⟩ : syracuseStep 1337789 = 501671) (by norm_num)
theorem B1501733 : Blo 790340 1501733 := bbase (se 4 (by rfl) ⟨140787, by rfl⟩ : syracuseStep 1501733 = 281575) (by norm_num)
theorem B2714165 : Blo 790340 2714165 := bbase (se 5 (by rfl) ⟨127226, by rfl⟩ : syracuseStep 2714165 = 254453) (by norm_num)
theorem B1337917 : Blo 790340 1337917 := bbase (se 3 (by rfl) ⟨250859, by rfl⟩ : syracuseStep 1337917 = 501719) (by norm_num)
theorem B1338005 : Blo 790340 1338005 := bbase (se 6 (by rfl) ⟨31359, by rfl⟩ : syracuseStep 1338005 = 62719) (by norm_num)
theorem B1501877 : Blo 790340 1501877 := bbase (se 5 (by rfl) ⟨70400, by rfl⟩ : syracuseStep 1501877 = 140801) (by norm_num)
theorem B3009221 : Blo 790340 3009221 := bbase (se 4 (by rfl) ⟨282114, by rfl⟩ : syracuseStep 3009221 = 564229) (by norm_num)
theorem B1338133 : Blo 790340 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B846617 : Blo 790340 846617 := bbase (se 2 (by rfl) ⟨317481, by rfl⟩ : syracuseStep 846617 = 634963) (by norm_num)
theorem B1338221 : Blo 790340 1338221 := bbase (se 3 (by rfl) ⟨250916, by rfl⟩ : syracuseStep 1338221 = 501833) (by norm_num)
theorem B1207189 : Blo 790340 1207189 := bbase (se 6 (by rfl) ⟨28293, by rfl⟩ : syracuseStep 1207189 = 56587) (by norm_num)
theorem B3206101 : Blo 790340 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B1502165 : Blo 790340 1502165 := bbase (se 7 (by rfl) ⟨17603, by rfl⟩ : syracuseStep 1502165 = 35207) (by norm_num)
theorem B2255845 : Blo 790340 2255845 := bbase (se 4 (by rfl) ⟨211485, by rfl⟩ : syracuseStep 2255845 = 422971) (by norm_num)
theorem B1338349 : Blo 790340 1338349 := bbase (se 3 (by rfl) ⟨250940, by rfl⟩ : syracuseStep 1338349 = 501881) (by norm_num)
theorem B846865 : Blo 790340 846865 := bbase (se 2 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 846865 = 635149) (by norm_num)
theorem B1338437 : Blo 790340 1338437 := bbase (se 4 (by rfl) ⟨125478, by rfl⟩ : syracuseStep 1338437 = 250957) (by norm_num)
theorem B1502317 : Blo 790340 1502317 := bbase (se 3 (by rfl) ⟨281684, by rfl⟩ : syracuseStep 1502317 = 563369) (by norm_num)
theorem B2256005 : Blo 790340 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B4517045 : Blo 790340 4517045 := bbase (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) (by norm_num)
theorem B1338565 : Blo 790340 1338565 := bbase (se 4 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 1338565 = 250981) (by norm_num)
theorem B1338653 : Blo 790340 1338653 := bbase (se 3 (by rfl) ⟨250997, by rfl⟩ : syracuseStep 1338653 = 501995) (by norm_num)
theorem B3042613 : Blo 790340 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B2256245 : Blo 790340 2256245 := bbase (se 5 (by rfl) ⟨105761, by rfl⟩ : syracuseStep 2256245 = 211523) (by norm_num)
theorem B1502621 : Blo 790340 1502621 := bbase (se 3 (by rfl) ⟨281741, by rfl⟩ : syracuseStep 1502621 = 563483) (by norm_num)
theorem B1338781 : Blo 790340 1338781 := bbase (se 3 (by rfl) ⟨251021, by rfl⟩ : syracuseStep 1338781 = 502043) (by norm_num)
theorem B847309 : Blo 790340 847309 := bbase (se 3 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 847309 = 317741) (by norm_num)
theorem B1338869 : Blo 790340 1338869 := bbase (se 5 (by rfl) ⟨62759, by rfl⟩ : syracuseStep 1338869 = 125519) (by norm_num)
theorem B847369 : Blo 790340 847369 := bbase (se 2 (by rfl) ⟨317763, by rfl⟩ : syracuseStep 847369 = 635527) (by norm_num)
theorem B2256437 : Blo 790340 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B1338997 : Blo 790340 1338997 := bbase (se 5 (by rfl) ⟨62765, by rfl⟩ : syracuseStep 1338997 = 125531) (by norm_num)
theorem B1339085 : Blo 790340 1339085 := bbase (se 3 (by rfl) ⟨251078, by rfl⟩ : syracuseStep 1339085 = 502157) (by norm_num)
theorem B847685 : Blo 790340 847685 := bbase (se 4 (by rfl) ⟨79470, by rfl⟩ : syracuseStep 847685 = 158941) (by norm_num)
theorem B1339213 : Blo 790340 1339213 := bbase (se 3 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 1339213 = 502205) (by norm_num)
theorem B3010405 : Blo 790340 3010405 := bbase (se 4 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 3010405 = 564451) (by norm_num)
theorem B1339301 : Blo 790340 1339301 := bbase (se 4 (by rfl) ⟨125559, by rfl⟩ : syracuseStep 1339301 = 251119) (by norm_num)
theorem B1339429 : Blo 790340 1339429 := bbase (se 4 (by rfl) ⟨125571, by rfl⟩ : syracuseStep 1339429 = 251143) (by norm_num)
theorem B1339517 : Blo 790340 1339517 := bbase (se 3 (by rfl) ⟨251159, by rfl⟩ : syracuseStep 1339517 = 502319) (by norm_num)
theorem B1503373 : Blo 790340 1503373 := bbase (se 3 (by rfl) ⟨281882, by rfl⟩ : syracuseStep 1503373 = 563765) (by norm_num)
theorem B3010709 : Blo 790340 3010709 := bbase (se 6 (by rfl) ⟨70563, by rfl⟩ : syracuseStep 3010709 = 141127) (by norm_num)
theorem B13693141 : Blo 790340 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B1339645 : Blo 790340 1339645 := bbase (se 3 (by rfl) ⟨251183, by rfl⟩ : syracuseStep 1339645 = 502367) (by norm_num)
theorem B848129 : Blo 790340 848129 := bbase (se 2 (by rfl) ⟨318048, by rfl⟩ : syracuseStep 848129 = 636097) (by norm_num)
theorem B1503517 : Blo 790340 1503517 := bbase (se 3 (by rfl) ⟨281909, by rfl⟩ : syracuseStep 1503517 = 563819) (by norm_num)
theorem B848189 : Blo 790340 848189 := bbase (se 3 (by rfl) ⟨159035, by rfl⟩ : syracuseStep 848189 = 318071) (by norm_num)
theorem B1339733 : Blo 790340 1339733 := bbase (se 10 (by rfl) ⟨1962, by rfl⟩ : syracuseStep 1339733 = 3925) (by norm_num)
theorem B1503677 : Blo 790340 1503677 := bbase (se 3 (by rfl) ⟨281939, by rfl⟩ : syracuseStep 1503677 = 563879) (by norm_num)
theorem B1339861 : Blo 790340 1339861 := bbase (se 7 (by rfl) ⟨15701, by rfl⟩ : syracuseStep 1339861 = 31403) (by norm_num)
theorem B2257429 : Blo 790340 2257429 := bbase (se 6 (by rfl) ⟨52908, by rfl⟩ : syracuseStep 2257429 = 105817) (by norm_num)
theorem B1339949 : Blo 790340 1339949 := bbase (se 3 (by rfl) ⟨251240, by rfl⟩ : syracuseStep 1339949 = 502481) (by norm_num)
theorem B1503821 : Blo 790340 1503821 := bbase (se 3 (by rfl) ⟨281966, by rfl⟩ : syracuseStep 1503821 = 563933) (by norm_num)
theorem B1340077 : Blo 790340 1340077 := bbase (se 3 (by rfl) ⟨251264, by rfl⟩ : syracuseStep 1340077 = 502529) (by norm_num)
theorem B2716357 : Blo 790340 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B1176325 : Blo 790340 1176325 := bbase (se 4 (by rfl) ⟨110280, by rfl⟩ : syracuseStep 1176325 = 220561) (by norm_num)
theorem B1340165 : Blo 790340 1340165 := bbase (se 4 (by rfl) ⟨125640, by rfl⟩ : syracuseStep 1340165 = 251281) (by norm_num)
theorem B2028325 : Blo 790340 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B1504109 : Blo 790340 1504109 := bbase (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) (by norm_num)
theorem B1340293 : Blo 790340 1340293 := bbase (se 4 (by rfl) ⟨125652, by rfl⟩ : syracuseStep 1340293 = 251305) (by norm_num)
theorem B979885 : Blo 790340 979885 := bbase (se 3 (by rfl) ⟨183728, by rfl⟩ : syracuseStep 979885 = 367457) (by norm_num)
theorem B1340381 : Blo 790340 1340381 := bbase (se 3 (by rfl) ⟨251321, by rfl⟩ : syracuseStep 1340381 = 502643) (by norm_num)
theorem B1504261 : Blo 790340 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B1504565 : Blo 790340 1504565 := bbase (se 5 (by rfl) ⟨70526, by rfl⟩ : syracuseStep 1504565 = 141053) (by norm_num)
theorem B4519253 : Blo 790340 4519253 := bbase (se 13 (by rfl) ⟨827, by rfl⟩ : syracuseStep 4519253 = 1655) (by norm_num)
theorem B1471981 : Blo 790340 1471981 := bbase (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) (by norm_num)
theorem B2258533 : Blo 790340 2258533 := bbase (se 4 (by rfl) ⟨211737, by rfl⟩ : syracuseStep 2258533 = 423475) (by norm_num)
theorem B9008981 : Blo 790340 9008981 := bbase (se 9 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 9008981 = 52787) (by norm_num)
theorem B1505317 : Blo 790340 1505317 := bbase (se 4 (by rfl) ⟨141123, by rfl⟩ : syracuseStep 1505317 = 282247) (by norm_num)
theorem B2062493 : Blo 790340 2062493 := bbase (se 3 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 2062493 = 773435) (by norm_num)
theorem B1505461 : Blo 790340 1505461 := bbase (se 5 (by rfl) ⟨70568, by rfl⟩ : syracuseStep 1505461 = 141137) (by norm_num)
theorem B3012821 : Blo 790340 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B1505621 : Blo 790340 1505621 := bbase (se 10 (by rfl) ⟨2205, by rfl⟩ : syracuseStep 1505621 = 4411) (by norm_num)
theorem B1603925 : Blo 790340 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B8550805 : Blo 790340 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B1505765 : Blo 790340 1505765 := bbase (se 4 (by rfl) ⟨141165, by rfl⟩ : syracuseStep 1505765 = 282331) (by norm_num)
theorem B3013109 : Blo 790340 3013109 := bbase (se 5 (by rfl) ⟨141239, by rfl⟩ : syracuseStep 3013109 = 282479) (by norm_num)
theorem B1506053 : Blo 790340 1506053 := bbase (se 4 (by rfl) ⟨141192, by rfl⟩ : syracuseStep 1506053 = 282385) (by norm_num)
theorem B2292581 : Blo 790340 2292581 := bbase (se 4 (by rfl) ⟨214929, by rfl⟩ : syracuseStep 2292581 = 429859) (by norm_num)
theorem B2063261 : Blo 790340 2063261 := bbase (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) (by norm_num)
theorem B1506205 : Blo 790340 1506205 := bbase (se 3 (by rfl) ⟨282413, by rfl⟩ : syracuseStep 1506205 = 564827) (by norm_num)
theorem B3799973 : Blo 790340 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B1014697 : Blo 790340 1014697 := bbase (se 2 (by rfl) ⟨380511, by rfl⟩ : syracuseStep 1014697 = 761023) (by norm_num)
theorem B2260037 : Blo 790340 2260037 := bbase (se 4 (by rfl) ⟨211878, by rfl⟩ : syracuseStep 2260037 = 423757) (by norm_num)
theorem B2030789 : Blo 790340 2030789 := bbase (se 4 (by rfl) ⟨190386, by rfl⟩ : syracuseStep 2030789 = 380773) (by norm_num)
theorem B1506509 : Blo 790340 1506509 := bbase (se 3 (by rfl) ⟨282470, by rfl⟩ : syracuseStep 1506509 = 564941) (by norm_num)
theorem B2751877 : Blo 790340 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B1899949 : Blo 790340 1899949 := bbase (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) (by norm_num)
theorem B1900093 : Blo 790340 1900093 := bbase (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) (by norm_num)
theorem B3014293 : Blo 790340 3014293 := bbase (se 6 (by rfl) ⟨70647, by rfl⟩ : syracuseStep 3014293 = 141295) (by norm_num)
theorem B3210965 : Blo 790340 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B3211093 : Blo 790340 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B5078933 : Blo 790340 5078933 := bbase (se 6 (by rfl) ⟨119037, by rfl⟩ : syracuseStep 5078933 = 238075) (by norm_num)
theorem B1507261 : Blo 790340 1507261 := bbase (se 3 (by rfl) ⟨282611, by rfl⟩ : syracuseStep 1507261 = 565223) (by norm_num)
theorem B3014597 : Blo 790340 3014597 := bbase (se 4 (by rfl) ⟨282618, by rfl⟩ : syracuseStep 3014597 = 565237) (by norm_num)
theorem B5505059 : Blo 790340 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B1016051 : Blo 790340 1016051 := bstep (se 1 (by rfl) ⟨762038, by rfl⟩ : syracuseStep 1016051 = 1524077) B1524077
theorem B4292963 : Blo 790340 4292963 := bstep (se 1 (by rfl) ⟨3219722, by rfl⟩ : syracuseStep 4292963 = 6439445) B6439445
theorem B3015053 : Blo 790340 3015053 := bstep (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) B1130645
theorem B1507747 : Blo 790340 1507747 := bstep (se 1 (by rfl) ⟨1130810, by rfl⟩ : syracuseStep 1507747 = 2261621) B2261621
theorem B2261677 : Blo 790340 2261677 := bstep (se 3 (by rfl) ⟨424064, by rfl⟩ : syracuseStep 2261677 = 848129) B848129
theorem B2261837 : Blo 790340 2261837 := bstep (se 3 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 2261837 = 848189) B848189
theorem B3212131 : Blo 790340 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B14484365 : Blo 790340 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B1836323 : Blo 790340 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B1901987 : Blo 790340 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B1902275 : Blo 790340 1902275 := bstep (se 1 (by rfl) ⟨1426706, by rfl⟩ : syracuseStep 1902275 = 2853413) B2853413
theorem B1115857 : Blo 790340 1115857 := bstep (se 2 (by rfl) ⟨418446, by rfl⟩ : syracuseStep 1115857 = 836893) B836893
theorem B2000771 : Blo 790340 2000771 := bstep (se 1 (by rfl) ⟨1500578, by rfl⟩ : syracuseStep 2000771 = 3001157) B3001157
theorem B3377123 : Blo 790340 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B2000963 : Blo 790340 2000963 := bstep (se 1 (by rfl) ⟨1500722, by rfl⟩ : syracuseStep 2000963 = 3001445) B3001445
theorem B952435 : Blo 790340 952435 := bstep (se 1 (by rfl) ⟨714326, by rfl⟩ : syracuseStep 952435 = 1428653) B1428653
theorem B5081393 : Blo 790340 5081393 := bstep (se 2 (by rfl) ⟨1905522, by rfl⟩ : syracuseStep 5081393 = 3811045) B3811045
theorem B952627 : Blo 790340 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B2034115 : Blo 790340 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B6752909 : Blo 790340 6752909 := bstep (se 3 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 6752909 = 2532341) B2532341
theorem B953011 : Blo 790340 953011 := bstep (se 1 (by rfl) ⟨714758, by rfl⟩ : syracuseStep 953011 = 1429517) B1429517
theorem B2001905 : Blo 790340 2001905 := bstep (se 2 (by rfl) ⟨750714, by rfl⟩ : syracuseStep 2001905 = 1501429) B1501429
theorem B1903601 : Blo 790340 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B2001955 : Blo 790340 2001955 := bstep (se 1 (by rfl) ⟨1501466, by rfl⟩ : syracuseStep 2001955 = 3002933) B3002933
theorem B3083405 : Blo 790340 3083405 := bstep (se 3 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 3083405 = 1156277) B1156277
theorem B2002097 : Blo 790340 2002097 := bstep (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) B1501573
theorem B1608913 : Blo 790340 1608913 := bstep (se 2 (by rfl) ⟨603342, by rfl⟩ : syracuseStep 1608913 = 1206685) B1206685
theorem B953699 : Blo 790340 953699 := bstep (se 1 (by rfl) ⟨715274, by rfl⟩ : syracuseStep 953699 = 1430549) B1430549
theorem B1904177 : Blo 790340 1904177 := bstep (se 2 (by rfl) ⟨714066, by rfl⟩ : syracuseStep 1904177 = 1428133) B1428133
theorem B1904323 : Blo 790340 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B790355 : Blo 790340 790355 := bstep (se 1 (by rfl) ⟨592766, by rfl⟩ : syracuseStep 790355 = 1185533) B1185533
theorem B790371 : Blo 790340 790371 := bstep (se 1 (by rfl) ⟨592778, by rfl⟩ : syracuseStep 790371 = 1185557) B1185557
theorem B790387 : Blo 790340 790387 := bstep (se 1 (by rfl) ⟨592790, by rfl⟩ : syracuseStep 790387 = 1185581) B1185581
theorem B790403 : Blo 790340 790403 := bstep (se 1 (by rfl) ⟨592802, by rfl⟩ : syracuseStep 790403 = 1185605) B1185605
theorem B790419 : Blo 790340 790419 := bstep (se 1 (by rfl) ⟨592814, by rfl⟩ : syracuseStep 790419 = 1185629) B1185629
theorem B790435 : Blo 790340 790435 := bstep (se 1 (by rfl) ⟨592826, by rfl⟩ : syracuseStep 790435 = 1185653) B1185653
theorem B3379121 : Blo 790340 3379121 := bstep (se 2 (by rfl) ⟨1267170, by rfl⟩ : syracuseStep 3379121 = 2534341) B2534341
theorem B790451 : Blo 790340 790451 := bstep (se 1 (by rfl) ⟨592838, by rfl⟩ : syracuseStep 790451 = 1185677) B1185677
theorem B790467 : Blo 790340 790467 := bstep (se 1 (by rfl) ⟨592850, by rfl⟩ : syracuseStep 790467 = 1185701) B1185701
theorem B11407301 : Blo 790340 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B790483 : Blo 790340 790483 := bstep (se 1 (by rfl) ⟨592862, by rfl⟩ : syracuseStep 790483 = 1185725) B1185725
theorem B790499 : Blo 790340 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B1609699 : Blo 790340 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B790515 : Blo 790340 790515 := bstep (se 1 (by rfl) ⟨592886, by rfl⟩ : syracuseStep 790515 = 1185773) B1185773
theorem B790531 : Blo 790340 790531 := bstep (se 1 (by rfl) ⟨592898, by rfl⟩ : syracuseStep 790531 = 1185797) B1185797
theorem B790547 : Blo 790340 790547 := bstep (se 1 (by rfl) ⟨592910, by rfl⟩ : syracuseStep 790547 = 1185821) B1185821
theorem B790563 : Blo 790340 790563 := bstep (se 1 (by rfl) ⟨592922, by rfl⟩ : syracuseStep 790563 = 1185845) B1185845
theorem B1609763 : Blo 790340 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B790579 : Blo 790340 790579 := bstep (se 1 (by rfl) ⟨592934, by rfl⟩ : syracuseStep 790579 = 1185869) B1185869
theorem B790595 : Blo 790340 790595 := bstep (se 1 (by rfl) ⟨592946, by rfl⟩ : syracuseStep 790595 = 1185893) B1185893
theorem B790611 : Blo 790340 790611 := bstep (se 1 (by rfl) ⟨592958, by rfl⟩ : syracuseStep 790611 = 1185917) B1185917
theorem B790627 : Blo 790340 790627 := bstep (se 1 (by rfl) ⟨592970, by rfl⟩ : syracuseStep 790627 = 1185941) B1185941
theorem B790643 : Blo 790340 790643 := bstep (se 1 (by rfl) ⟨592982, by rfl⟩ : syracuseStep 790643 = 1185965) B1185965
theorem B790659 : Blo 790340 790659 := bstep (se 1 (by rfl) ⟨592994, by rfl⟩ : syracuseStep 790659 = 1185989) B1185989
theorem B2003089 : Blo 790340 2003089 := bstep (se 2 (by rfl) ⟨751158, by rfl⟩ : syracuseStep 2003089 = 1502317) B1502317
theorem B790675 : Blo 790340 790675 := bstep (se 1 (by rfl) ⟨593006, by rfl⟩ : syracuseStep 790675 = 1186013) B1186013
theorem B790691 : Blo 790340 790691 := bstep (se 1 (by rfl) ⟨593018, by rfl⟩ : syracuseStep 790691 = 1186037) B1186037
theorem B790707 : Blo 790340 790707 := bstep (se 1 (by rfl) ⟨593030, by rfl⟩ : syracuseStep 790707 = 1186061) B1186061
theorem B790723 : Blo 790340 790723 := bstep (se 1 (by rfl) ⟨593042, by rfl⟩ : syracuseStep 790723 = 1186085) B1186085
theorem B790739 : Blo 790340 790739 := bstep (se 1 (by rfl) ⟨593054, by rfl⟩ : syracuseStep 790739 = 1186109) B1186109
theorem B7213283 : Blo 790340 7213283 := bstep (se 1 (by rfl) ⟨5409962, by rfl⟩ : syracuseStep 7213283 = 10819925) B10819925
theorem B790755 : Blo 790340 790755 := bstep (se 1 (by rfl) ⟨593066, by rfl⟩ : syracuseStep 790755 = 1186133) B1186133
theorem B790771 : Blo 790340 790771 := bstep (se 1 (by rfl) ⟨593078, by rfl⟩ : syracuseStep 790771 = 1186157) B1186157
theorem B790787 : Blo 790340 790787 := bstep (se 1 (by rfl) ⟨593090, by rfl⟩ : syracuseStep 790787 = 1186181) B1186181
theorem B790803 : Blo 790340 790803 := bstep (se 1 (by rfl) ⟨593102, by rfl⟩ : syracuseStep 790803 = 1186205) B1186205
theorem B790819 : Blo 790340 790819 := bstep (se 1 (by rfl) ⟨593114, by rfl⟩ : syracuseStep 790819 = 1186229) B1186229
theorem B790835 : Blo 790340 790835 := bstep (se 1 (by rfl) ⟨593126, by rfl⟩ : syracuseStep 790835 = 1186253) B1186253
theorem B790851 : Blo 790340 790851 := bstep (se 1 (by rfl) ⟨593138, by rfl⟩ : syracuseStep 790851 = 1186277) B1186277
theorem B790867 : Blo 790340 790867 := bstep (se 1 (by rfl) ⟨593150, by rfl⟩ : syracuseStep 790867 = 1186301) B1186301
theorem B790883 : Blo 790340 790883 := bstep (se 1 (by rfl) ⟨593162, by rfl⟩ : syracuseStep 790883 = 1186325) B1186325
theorem B790899 : Blo 790340 790899 := bstep (se 1 (by rfl) ⟨593174, by rfl⟩ : syracuseStep 790899 = 1186349) B1186349
theorem B790915 : Blo 790340 790915 := bstep (se 1 (by rfl) ⟨593186, by rfl⟩ : syracuseStep 790915 = 1186373) B1186373
theorem B790931 : Blo 790340 790931 := bstep (se 1 (by rfl) ⟨593198, by rfl⟩ : syracuseStep 790931 = 1186397) B1186397
theorem B790947 : Blo 790340 790947 := bstep (se 1 (by rfl) ⟨593210, by rfl⟩ : syracuseStep 790947 = 1186421) B1186421
theorem B2003363 : Blo 790340 2003363 := bstep (se 1 (by rfl) ⟨1502522, by rfl⟩ : syracuseStep 2003363 = 3005045) B3005045
theorem B889267 : Blo 790340 889267 := bstep (se 1 (by rfl) ⟨666950, by rfl⟩ : syracuseStep 889267 = 1333901) B1333901
theorem B790963 : Blo 790340 790963 := bstep (se 1 (by rfl) ⟨593222, by rfl⟩ : syracuseStep 790963 = 1186445) B1186445
theorem B790979 : Blo 790340 790979 := bstep (se 1 (by rfl) ⟨593234, by rfl⟩ : syracuseStep 790979 = 1186469) B1186469
theorem B790995 : Blo 790340 790995 := bstep (se 1 (by rfl) ⟨593246, by rfl⟩ : syracuseStep 790995 = 1186493) B1186493
theorem B791011 : Blo 790340 791011 := bstep (se 1 (by rfl) ⟨593258, by rfl⟩ : syracuseStep 791011 = 1186517) B1186517
theorem B791027 : Blo 790340 791027 := bstep (se 1 (by rfl) ⟨593270, by rfl⟩ : syracuseStep 791027 = 1186541) B1186541
theorem B791043 : Blo 790340 791043 := bstep (se 1 (by rfl) ⟨593282, by rfl⟩ : syracuseStep 791043 = 1186565) B1186565
theorem B791059 : Blo 790340 791059 := bstep (se 1 (by rfl) ⟨593294, by rfl⟩ : syracuseStep 791059 = 1186589) B1186589
theorem B791075 : Blo 790340 791075 := bstep (se 1 (by rfl) ⟨593306, by rfl⟩ : syracuseStep 791075 = 1186613) B1186613
theorem B791091 : Blo 790340 791091 := bstep (se 1 (by rfl) ⟨593318, by rfl⟩ : syracuseStep 791091 = 1186637) B1186637
theorem B889411 : Blo 790340 889411 := bstep (se 1 (by rfl) ⟨667058, by rfl⟩ : syracuseStep 889411 = 1334117) B1334117
theorem B791107 : Blo 790340 791107 := bstep (se 1 (by rfl) ⟨593330, by rfl⟩ : syracuseStep 791107 = 1186661) B1186661
theorem B791123 : Blo 790340 791123 := bstep (se 1 (by rfl) ⟨593342, by rfl⟩ : syracuseStep 791123 = 1186685) B1186685
theorem B791139 : Blo 790340 791139 := bstep (se 1 (by rfl) ⟨593354, by rfl⟩ : syracuseStep 791139 = 1186709) B1186709
theorem B2003555 : Blo 790340 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B791155 : Blo 790340 791155 := bstep (se 1 (by rfl) ⟨593366, by rfl⟩ : syracuseStep 791155 = 1186733) B1186733
theorem B791171 : Blo 790340 791171 := bstep (se 1 (by rfl) ⟨593378, by rfl⟩ : syracuseStep 791171 = 1186757) B1186757
theorem B791187 : Blo 790340 791187 := bstep (se 1 (by rfl) ⟨593390, by rfl⟩ : syracuseStep 791187 = 1186781) B1186781
theorem B791203 : Blo 790340 791203 := bstep (se 1 (by rfl) ⟨593402, by rfl⟩ : syracuseStep 791203 = 1186805) B1186805
theorem B791219 : Blo 790340 791219 := bstep (se 1 (by rfl) ⟨593414, by rfl⟩ : syracuseStep 791219 = 1186829) B1186829
theorem B791235 : Blo 790340 791235 := bstep (se 1 (by rfl) ⟨593426, by rfl⟩ : syracuseStep 791235 = 1186853) B1186853
theorem B889555 : Blo 790340 889555 := bstep (se 1 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 889555 = 1334333) B1334333
theorem B791251 : Blo 790340 791251 := bstep (se 1 (by rfl) ⟨593438, by rfl⟩ : syracuseStep 791251 = 1186877) B1186877
theorem B791267 : Blo 790340 791267 := bstep (se 1 (by rfl) ⟨593450, by rfl⟩ : syracuseStep 791267 = 1186901) B1186901
theorem B791283 : Blo 790340 791283 := bstep (se 1 (by rfl) ⟨593462, by rfl⟩ : syracuseStep 791283 = 1186925) B1186925
theorem B791299 : Blo 790340 791299 := bstep (se 1 (by rfl) ⟨593474, by rfl⟩ : syracuseStep 791299 = 1186949) B1186949
theorem B791315 : Blo 790340 791315 := bstep (se 1 (by rfl) ⟨593486, by rfl⟩ : syracuseStep 791315 = 1186973) B1186973
theorem B791331 : Blo 790340 791331 := bstep (se 1 (by rfl) ⟨593498, by rfl⟩ : syracuseStep 791331 = 1186997) B1186997
theorem B791347 : Blo 790340 791347 := bstep (se 1 (by rfl) ⟨593510, by rfl⟩ : syracuseStep 791347 = 1187021) B1187021
theorem B791363 : Blo 790340 791363 := bstep (se 1 (by rfl) ⟨593522, by rfl⟩ : syracuseStep 791363 = 1187045) B1187045
theorem B791379 : Blo 790340 791379 := bstep (se 1 (by rfl) ⟨593534, by rfl⟩ : syracuseStep 791379 = 1187069) B1187069
theorem B889699 : Blo 790340 889699 := bstep (se 1 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 889699 = 1334549) B1334549
theorem B791395 : Blo 790340 791395 := bstep (se 1 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 791395 = 1187093) B1187093
theorem B791411 : Blo 790340 791411 := bstep (se 1 (by rfl) ⟨593558, by rfl⟩ : syracuseStep 791411 = 1187117) B1187117
theorem B791427 : Blo 790340 791427 := bstep (se 1 (by rfl) ⟨593570, by rfl⟩ : syracuseStep 791427 = 1187141) B1187141
theorem B5411717 : Blo 790340 5411717 := bstep (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) B1014697
theorem B3216269 : Blo 790340 3216269 := bstep (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) B1206101
theorem B791443 : Blo 790340 791443 := bstep (se 1 (by rfl) ⟨593582, by rfl⟩ : syracuseStep 791443 = 1187165) B1187165
theorem B791459 : Blo 790340 791459 := bstep (se 1 (by rfl) ⟨593594, by rfl⟩ : syracuseStep 791459 = 1187189) B1187189
theorem B791475 : Blo 790340 791475 := bstep (se 1 (by rfl) ⟨593606, by rfl⟩ : syracuseStep 791475 = 1187213) B1187213
theorem B791491 : Blo 790340 791491 := bstep (se 1 (by rfl) ⟨593618, by rfl⟩ : syracuseStep 791491 = 1187237) B1187237
theorem B791507 : Blo 790340 791507 := bstep (se 1 (by rfl) ⟨593630, by rfl⟩ : syracuseStep 791507 = 1187261) B1187261
theorem B791523 : Blo 790340 791523 := bstep (se 1 (by rfl) ⟨593642, by rfl⟩ : syracuseStep 791523 = 1187285) B1187285
theorem B889843 : Blo 790340 889843 := bstep (se 1 (by rfl) ⟨667382, by rfl⟩ : syracuseStep 889843 = 1334765) B1334765
theorem B791539 : Blo 790340 791539 := bstep (se 1 (by rfl) ⟨593654, by rfl⟩ : syracuseStep 791539 = 1187309) B1187309
theorem B791555 : Blo 790340 791555 := bstep (se 1 (by rfl) ⟨593666, by rfl⟩ : syracuseStep 791555 = 1187333) B1187333
theorem B791571 : Blo 790340 791571 := bstep (se 1 (by rfl) ⟨593678, by rfl⟩ : syracuseStep 791571 = 1187357) B1187357
theorem B791587 : Blo 790340 791587 := bstep (se 1 (by rfl) ⟨593690, by rfl⟩ : syracuseStep 791587 = 1187381) B1187381
theorem B791603 : Blo 790340 791603 := bstep (se 1 (by rfl) ⟨593702, by rfl⟩ : syracuseStep 791603 = 1187405) B1187405
theorem B791619 : Blo 790340 791619 := bstep (se 1 (by rfl) ⟨593714, by rfl⟩ : syracuseStep 791619 = 1187429) B1187429
theorem B791635 : Blo 790340 791635 := bstep (se 1 (by rfl) ⟨593726, by rfl⟩ : syracuseStep 791635 = 1187453) B1187453
theorem B791651 : Blo 790340 791651 := bstep (se 1 (by rfl) ⟨593738, by rfl⟩ : syracuseStep 791651 = 1187477) B1187477
theorem B2856035 : Blo 790340 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B791667 : Blo 790340 791667 := bstep (se 1 (by rfl) ⟨593750, by rfl⟩ : syracuseStep 791667 = 1187501) B1187501
theorem B889987 : Blo 790340 889987 := bstep (se 1 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 889987 = 1334981) B1334981
theorem B791683 : Blo 790340 791683 := bstep (se 1 (by rfl) ⟨593762, by rfl⟩ : syracuseStep 791683 = 1187525) B1187525
theorem B791699 : Blo 790340 791699 := bstep (se 1 (by rfl) ⟨593774, by rfl⟩ : syracuseStep 791699 = 1187549) B1187549
theorem B791715 : Blo 790340 791715 := bstep (se 1 (by rfl) ⟨593786, by rfl⟩ : syracuseStep 791715 = 1187573) B1187573
theorem B791731 : Blo 790340 791731 := bstep (se 1 (by rfl) ⟨593798, by rfl⟩ : syracuseStep 791731 = 1187597) B1187597
theorem B791747 : Blo 790340 791747 := bstep (se 1 (by rfl) ⟨593810, by rfl⟩ : syracuseStep 791747 = 1187621) B1187621
theorem B5084365 : Blo 790340 5084365 := bstep (se 3 (by rfl) ⟨953318, by rfl⟩ : syracuseStep 5084365 = 1906637) B1906637
theorem B791763 : Blo 790340 791763 := bstep (se 1 (by rfl) ⟨593822, by rfl⟩ : syracuseStep 791763 = 1187645) B1187645
theorem B791779 : Blo 790340 791779 := bstep (se 1 (by rfl) ⟨593834, by rfl⟩ : syracuseStep 791779 = 1187669) B1187669
theorem B791795 : Blo 790340 791795 := bstep (se 1 (by rfl) ⟨593846, by rfl⟩ : syracuseStep 791795 = 1187693) B1187693
theorem B791811 : Blo 790340 791811 := bstep (se 1 (by rfl) ⟨593858, by rfl⟩ : syracuseStep 791811 = 1187717) B1187717
theorem B890131 : Blo 790340 890131 := bstep (se 1 (by rfl) ⟨667598, by rfl⟩ : syracuseStep 890131 = 1335197) B1335197
theorem B791827 : Blo 790340 791827 := bstep (se 1 (by rfl) ⟨593870, by rfl⟩ : syracuseStep 791827 = 1187741) B1187741
theorem B791843 : Blo 790340 791843 := bstep (se 1 (by rfl) ⟨593882, by rfl⟩ : syracuseStep 791843 = 1187765) B1187765
theorem B791859 : Blo 790340 791859 := bstep (se 1 (by rfl) ⟨593894, by rfl⟩ : syracuseStep 791859 = 1187789) B1187789
theorem B791875 : Blo 790340 791875 := bstep (se 1 (by rfl) ⟨593906, by rfl⟩ : syracuseStep 791875 = 1187813) B1187813
theorem B791891 : Blo 790340 791891 := bstep (se 1 (by rfl) ⟨593918, by rfl⟩ : syracuseStep 791891 = 1187837) B1187837
theorem B791907 : Blo 790340 791907 := bstep (se 1 (by rfl) ⟨593930, by rfl⟩ : syracuseStep 791907 = 1187861) B1187861
theorem B791923 : Blo 790340 791923 := bstep (se 1 (by rfl) ⟨593942, by rfl⟩ : syracuseStep 791923 = 1187885) B1187885
theorem B791939 : Blo 790340 791939 := bstep (se 1 (by rfl) ⟨593954, by rfl⟩ : syracuseStep 791939 = 1187909) B1187909
theorem B791955 : Blo 790340 791955 := bstep (se 1 (by rfl) ⟨593966, by rfl⟩ : syracuseStep 791955 = 1187933) B1187933
theorem B890275 : Blo 790340 890275 := bstep (se 1 (by rfl) ⟨667706, by rfl⟩ : syracuseStep 890275 = 1335413) B1335413
theorem B791971 : Blo 790340 791971 := bstep (se 1 (by rfl) ⟨593978, by rfl⟩ : syracuseStep 791971 = 1187957) B1187957
theorem B791987 : Blo 790340 791987 := bstep (se 1 (by rfl) ⟨593990, by rfl⟩ : syracuseStep 791987 = 1187981) B1187981
theorem B792003 : Blo 790340 792003 := bstep (se 1 (by rfl) ⟨594002, by rfl⟩ : syracuseStep 792003 = 1188005) B1188005
theorem B792019 : Blo 790340 792019 := bstep (se 1 (by rfl) ⟨594014, by rfl⟩ : syracuseStep 792019 = 1188029) B1188029
theorem B792035 : Blo 790340 792035 := bstep (se 1 (by rfl) ⟨594026, by rfl⟩ : syracuseStep 792035 = 1188053) B1188053
theorem B792051 : Blo 790340 792051 := bstep (se 1 (by rfl) ⟨594038, by rfl⟩ : syracuseStep 792051 = 1188077) B1188077
theorem B792067 : Blo 790340 792067 := bstep (se 1 (by rfl) ⟨594050, by rfl⟩ : syracuseStep 792067 = 1188101) B1188101
theorem B2004497 : Blo 790340 2004497 := bstep (se 2 (by rfl) ⟨751686, by rfl⟩ : syracuseStep 2004497 = 1503373) B1503373
theorem B792083 : Blo 790340 792083 := bstep (se 1 (by rfl) ⟨594062, by rfl⟩ : syracuseStep 792083 = 1188125) B1188125
theorem B792099 : Blo 790340 792099 := bstep (se 1 (by rfl) ⟨594074, by rfl⟩ : syracuseStep 792099 = 1188149) B1188149
theorem B890419 : Blo 790340 890419 := bstep (se 1 (by rfl) ⟨667814, by rfl⟩ : syracuseStep 890419 = 1335629) B1335629
theorem B792115 : Blo 790340 792115 := bstep (se 1 (by rfl) ⟨594086, by rfl⟩ : syracuseStep 792115 = 1188173) B1188173
theorem B2004547 : Blo 790340 2004547 := bstep (se 1 (by rfl) ⟨1503410, by rfl⟩ : syracuseStep 2004547 = 3006821) B3006821
theorem B792131 : Blo 790340 792131 := bstep (se 1 (by rfl) ⟨594098, by rfl⟩ : syracuseStep 792131 = 1188197) B1188197
theorem B792147 : Blo 790340 792147 := bstep (se 1 (by rfl) ⟨594110, by rfl⟩ : syracuseStep 792147 = 1188221) B1188221
theorem B792163 : Blo 790340 792163 := bstep (se 1 (by rfl) ⟨594122, by rfl⟩ : syracuseStep 792163 = 1188245) B1188245
theorem B18257521 : Blo 790340 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B792179 : Blo 790340 792179 := bstep (se 1 (by rfl) ⟨594134, by rfl⟩ : syracuseStep 792179 = 1188269) B1188269
theorem B792195 : Blo 790340 792195 := bstep (se 1 (by rfl) ⟨594146, by rfl⟩ : syracuseStep 792195 = 1188293) B1188293
theorem B792211 : Blo 790340 792211 := bstep (se 1 (by rfl) ⟨594158, by rfl⟩ : syracuseStep 792211 = 1188317) B1188317
theorem B792227 : Blo 790340 792227 := bstep (se 1 (by rfl) ⟨594170, by rfl⟩ : syracuseStep 792227 = 1188341) B1188341
theorem B4003505 : Blo 790340 4003505 := bstep (se 2 (by rfl) ⟨1501314, by rfl⟩ : syracuseStep 4003505 = 3002629) B3002629
theorem B792243 : Blo 790340 792243 := bstep (se 1 (by rfl) ⟨594182, by rfl⟩ : syracuseStep 792243 = 1188365) B1188365
theorem B890563 : Blo 790340 890563 := bstep (se 1 (by rfl) ⟨667922, by rfl⟩ : syracuseStep 890563 = 1335845) B1335845
theorem B792259 : Blo 790340 792259 := bstep (se 1 (by rfl) ⟨594194, by rfl⟩ : syracuseStep 792259 = 1188389) B1188389
theorem B2004689 : Blo 790340 2004689 := bstep (se 2 (by rfl) ⟨751758, by rfl⟩ : syracuseStep 2004689 = 1503517) B1503517
theorem B792275 : Blo 790340 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B792291 : Blo 790340 792291 := bstep (se 1 (by rfl) ⟨594218, by rfl⟩ : syracuseStep 792291 = 1188437) B1188437
theorem B1185521 : Blo 790340 1185521 := bstep (se 2 (by rfl) ⟨444570, by rfl⟩ : syracuseStep 1185521 = 889141) B889141
theorem B792307 : Blo 790340 792307 := bstep (se 1 (by rfl) ⟨594230, by rfl⟩ : syracuseStep 792307 = 1188461) B1188461
theorem B1185539 : Blo 790340 1185539 := bstep (se 1 (by rfl) ⟨889154, by rfl⟩ : syracuseStep 1185539 = 1778309) B1778309
theorem B792323 : Blo 790340 792323 := bstep (se 1 (by rfl) ⟨594242, by rfl⟩ : syracuseStep 792323 = 1188485) B1188485
theorem B2037521 : Blo 790340 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B792339 : Blo 790340 792339 := bstep (se 1 (by rfl) ⟨594254, by rfl⟩ : syracuseStep 792339 = 1188509) B1188509
theorem B1185569 : Blo 790340 1185569 := bstep (se 2 (by rfl) ⟨444588, by rfl⟩ : syracuseStep 1185569 = 889177) B889177
theorem B792355 : Blo 790340 792355 := bstep (se 1 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 792355 = 1188533) B1188533
theorem B1185587 : Blo 790340 1185587 := bstep (se 1 (by rfl) ⟨889190, by rfl⟩ : syracuseStep 1185587 = 1778381) B1778381
theorem B792371 : Blo 790340 792371 := bstep (se 1 (by rfl) ⟨594278, by rfl⟩ : syracuseStep 792371 = 1188557) B1188557
theorem B792387 : Blo 790340 792387 := bstep (se 1 (by rfl) ⟨594290, by rfl⟩ : syracuseStep 792387 = 1188581) B1188581
theorem B1185617 : Blo 790340 1185617 := bstep (se 2 (by rfl) ⟨444606, by rfl⟩ : syracuseStep 1185617 = 889213) B889213
theorem B890707 : Blo 790340 890707 := bstep (se 1 (by rfl) ⟨668030, by rfl⟩ : syracuseStep 890707 = 1336061) B1336061
theorem B792403 : Blo 790340 792403 := bstep (se 1 (by rfl) ⟨594302, by rfl⟩ : syracuseStep 792403 = 1188605) B1188605
theorem B1185635 : Blo 790340 1185635 := bstep (se 1 (by rfl) ⟨889226, by rfl⟩ : syracuseStep 1185635 = 1778453) B1778453
theorem B792419 : Blo 790340 792419 := bstep (se 1 (by rfl) ⟨594314, by rfl⟩ : syracuseStep 792419 = 1188629) B1188629
theorem B792435 : Blo 790340 792435 := bstep (se 1 (by rfl) ⟨594326, by rfl⟩ : syracuseStep 792435 = 1188653) B1188653
theorem B1185665 : Blo 790340 1185665 := bstep (se 2 (by rfl) ⟨444624, by rfl⟩ : syracuseStep 1185665 = 889249) B889249
theorem B792451 : Blo 790340 792451 := bstep (se 1 (by rfl) ⟨594338, by rfl⟩ : syracuseStep 792451 = 1188677) B1188677
theorem B1185683 : Blo 790340 1185683 := bstep (se 1 (by rfl) ⟨889262, by rfl⟩ : syracuseStep 1185683 = 1778525) B1778525
theorem B792467 : Blo 790340 792467 := bstep (se 1 (by rfl) ⟨594350, by rfl⟩ : syracuseStep 792467 = 1188701) B1188701
theorem B1087379 : Blo 790340 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B792483 : Blo 790340 792483 := bstep (se 1 (by rfl) ⟨594362, by rfl⟩ : syracuseStep 792483 = 1188725) B1188725
theorem B5150627 : Blo 790340 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B1185713 : Blo 790340 1185713 := bstep (se 2 (by rfl) ⟨444642, by rfl⟩ : syracuseStep 1185713 = 889285) B889285
theorem B792499 : Blo 790340 792499 := bstep (se 1 (by rfl) ⟨594374, by rfl⟩ : syracuseStep 792499 = 1188749) B1188749
theorem B1185731 : Blo 790340 1185731 := bstep (se 1 (by rfl) ⟨889298, by rfl⟩ : syracuseStep 1185731 = 1778597) B1778597
theorem B792515 : Blo 790340 792515 := bstep (se 1 (by rfl) ⟨594386, by rfl⟩ : syracuseStep 792515 = 1188773) B1188773
theorem B792531 : Blo 790340 792531 := bstep (se 1 (by rfl) ⟨594398, by rfl⟩ : syracuseStep 792531 = 1188797) B1188797
theorem B1185761 : Blo 790340 1185761 := bstep (se 2 (by rfl) ⟨444660, by rfl⟩ : syracuseStep 1185761 = 889321) B889321
theorem B890851 : Blo 790340 890851 := bstep (se 1 (by rfl) ⟨668138, by rfl⟩ : syracuseStep 890851 = 1336277) B1336277
theorem B792547 : Blo 790340 792547 := bstep (se 1 (by rfl) ⟨594410, by rfl⟩ : syracuseStep 792547 = 1188821) B1188821
theorem B1185779 : Blo 790340 1185779 := bstep (se 1 (by rfl) ⟨889334, by rfl⟩ : syracuseStep 1185779 = 1778669) B1778669
theorem B792563 : Blo 790340 792563 := bstep (se 1 (by rfl) ⟨594422, by rfl⟩ : syracuseStep 792563 = 1188845) B1188845
theorem B792579 : Blo 790340 792579 := bstep (se 1 (by rfl) ⟨594434, by rfl⟩ : syracuseStep 792579 = 1188869) B1188869
theorem B1185809 : Blo 790340 1185809 := bstep (se 2 (by rfl) ⟨444678, by rfl⟩ : syracuseStep 1185809 = 889357) B889357
theorem B792595 : Blo 790340 792595 := bstep (se 1 (by rfl) ⟨594446, by rfl⟩ : syracuseStep 792595 = 1188893) B1188893
theorem B1185827 : Blo 790340 1185827 := bstep (se 1 (by rfl) ⟨889370, by rfl⟩ : syracuseStep 1185827 = 1778741) B1778741
theorem B792611 : Blo 790340 792611 := bstep (se 1 (by rfl) ⟨594458, by rfl⟩ : syracuseStep 792611 = 1188917) B1188917
theorem B792627 : Blo 790340 792627 := bstep (se 1 (by rfl) ⟨594470, by rfl⟩ : syracuseStep 792627 = 1188941) B1188941
theorem B1185857 : Blo 790340 1185857 := bstep (se 2 (by rfl) ⟨444696, by rfl⟩ : syracuseStep 1185857 = 889393) B889393
theorem B792643 : Blo 790340 792643 := bstep (se 1 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 792643 = 1188965) B1188965
theorem B1185875 : Blo 790340 1185875 := bstep (se 1 (by rfl) ⟨889406, by rfl⟩ : syracuseStep 1185875 = 1778813) B1778813
theorem B792659 : Blo 790340 792659 := bstep (se 1 (by rfl) ⟨594494, by rfl⟩ : syracuseStep 792659 = 1188989) B1188989
theorem B792675 : Blo 790340 792675 := bstep (se 1 (by rfl) ⟨594506, by rfl⟩ : syracuseStep 792675 = 1189013) B1189013
theorem B1185905 : Blo 790340 1185905 := bstep (se 2 (by rfl) ⟨444714, by rfl⟩ : syracuseStep 1185905 = 889429) B889429
theorem B890995 : Blo 790340 890995 := bstep (se 1 (by rfl) ⟨668246, by rfl⟩ : syracuseStep 890995 = 1336493) B1336493
theorem B792691 : Blo 790340 792691 := bstep (se 1 (by rfl) ⟨594518, by rfl⟩ : syracuseStep 792691 = 1189037) B1189037
theorem B1185923 : Blo 790340 1185923 := bstep (se 1 (by rfl) ⟨889442, by rfl⟩ : syracuseStep 1185923 = 1778885) B1778885
theorem B792707 : Blo 790340 792707 := bstep (se 1 (by rfl) ⟨594530, by rfl⟩ : syracuseStep 792707 = 1189061) B1189061
theorem B792723 : Blo 790340 792723 := bstep (se 1 (by rfl) ⟨594542, by rfl⟩ : syracuseStep 792723 = 1189085) B1189085
theorem B1185953 : Blo 790340 1185953 := bstep (se 2 (by rfl) ⟨444732, by rfl⟩ : syracuseStep 1185953 = 889465) B889465
theorem B792739 : Blo 790340 792739 := bstep (se 1 (by rfl) ⟨594554, by rfl⟩ : syracuseStep 792739 = 1189109) B1189109
theorem B1185971 : Blo 790340 1185971 := bstep (se 1 (by rfl) ⟨889478, by rfl⟩ : syracuseStep 1185971 = 1778957) B1778957
theorem B792755 : Blo 790340 792755 := bstep (se 1 (by rfl) ⟨594566, by rfl⟩ : syracuseStep 792755 = 1189133) B1189133
theorem B792771 : Blo 790340 792771 := bstep (se 1 (by rfl) ⟨594578, by rfl⟩ : syracuseStep 792771 = 1189157) B1189157
theorem B1186001 : Blo 790340 1186001 := bstep (se 2 (by rfl) ⟨444750, by rfl⟩ : syracuseStep 1186001 = 889501) B889501
theorem B792787 : Blo 790340 792787 := bstep (se 1 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 792787 = 1189181) B1189181
theorem B1186019 : Blo 790340 1186019 := bstep (se 1 (by rfl) ⟨889514, by rfl⟩ : syracuseStep 1186019 = 1779029) B1779029
theorem B25663715 : Blo 790340 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B792803 : Blo 790340 792803 := bstep (se 1 (by rfl) ⟨594602, by rfl⟩ : syracuseStep 792803 = 1189205) B1189205
theorem B792819 : Blo 790340 792819 := bstep (se 1 (by rfl) ⟨594614, by rfl⟩ : syracuseStep 792819 = 1189229) B1189229
theorem B1186049 : Blo 790340 1186049 := bstep (se 2 (by rfl) ⟨444768, by rfl⟩ : syracuseStep 1186049 = 889537) B889537
theorem B891139 : Blo 790340 891139 := bstep (se 1 (by rfl) ⟨668354, by rfl⟩ : syracuseStep 891139 = 1336709) B1336709
theorem B792835 : Blo 790340 792835 := bstep (se 1 (by rfl) ⟨594626, by rfl⟩ : syracuseStep 792835 = 1189253) B1189253
theorem B1186067 : Blo 790340 1186067 := bstep (se 1 (by rfl) ⟨889550, by rfl⟩ : syracuseStep 1186067 = 1779101) B1779101
theorem B792851 : Blo 790340 792851 := bstep (se 1 (by rfl) ⟨594638, by rfl⟩ : syracuseStep 792851 = 1189277) B1189277
theorem B792867 : Blo 790340 792867 := bstep (se 1 (by rfl) ⟨594650, by rfl⟩ : syracuseStep 792867 = 1189301) B1189301
theorem B1186097 : Blo 790340 1186097 := bstep (se 2 (by rfl) ⟨444786, by rfl⟩ : syracuseStep 1186097 = 889573) B889573
theorem B792883 : Blo 790340 792883 := bstep (se 1 (by rfl) ⟨594662, by rfl⟩ : syracuseStep 792883 = 1189325) B1189325
theorem B1186115 : Blo 790340 1186115 := bstep (se 1 (by rfl) ⟨889586, by rfl⟩ : syracuseStep 1186115 = 1779173) B1779173
theorem B792899 : Blo 790340 792899 := bstep (se 1 (by rfl) ⟨594674, by rfl⟩ : syracuseStep 792899 = 1189349) B1189349
theorem B3381581 : Blo 790340 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B792915 : Blo 790340 792915 := bstep (se 1 (by rfl) ⟨594686, by rfl⟩ : syracuseStep 792915 = 1189373) B1189373
theorem B1186145 : Blo 790340 1186145 := bstep (se 2 (by rfl) ⟨444804, by rfl⟩ : syracuseStep 1186145 = 889609) B889609
theorem B792931 : Blo 790340 792931 := bstep (se 1 (by rfl) ⟨594698, by rfl⟩ : syracuseStep 792931 = 1189397) B1189397
theorem B1186163 : Blo 790340 1186163 := bstep (se 1 (by rfl) ⟨889622, by rfl⟩ : syracuseStep 1186163 = 1779245) B1779245
theorem B792947 : Blo 790340 792947 := bstep (se 1 (by rfl) ⟨594710, by rfl⟩ : syracuseStep 792947 = 1189421) B1189421
theorem B792963 : Blo 790340 792963 := bstep (se 1 (by rfl) ⟨594722, by rfl⟩ : syracuseStep 792963 = 1189445) B1189445
theorem B1186193 : Blo 790340 1186193 := bstep (se 2 (by rfl) ⟨444822, by rfl⟩ : syracuseStep 1186193 = 889645) B889645
theorem B891283 : Blo 790340 891283 := bstep (se 1 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 891283 = 1336925) B1336925
theorem B792979 : Blo 790340 792979 := bstep (se 1 (by rfl) ⟨594734, by rfl⟩ : syracuseStep 792979 = 1189469) B1189469
theorem B1186211 : Blo 790340 1186211 := bstep (se 1 (by rfl) ⟨889658, by rfl⟩ : syracuseStep 1186211 = 1779317) B1779317
theorem B792995 : Blo 790340 792995 := bstep (se 1 (by rfl) ⟨594746, by rfl⟩ : syracuseStep 792995 = 1189493) B1189493
theorem B793011 : Blo 790340 793011 := bstep (se 1 (by rfl) ⟨594758, by rfl⟩ : syracuseStep 793011 = 1189517) B1189517
theorem B1186241 : Blo 790340 1186241 := bstep (se 2 (by rfl) ⟨444840, by rfl⟩ : syracuseStep 1186241 = 889681) B889681
theorem B793027 : Blo 790340 793027 := bstep (se 1 (by rfl) ⟨594770, by rfl⟩ : syracuseStep 793027 = 1189541) B1189541
theorem B1186259 : Blo 790340 1186259 := bstep (se 1 (by rfl) ⟨889694, by rfl⟩ : syracuseStep 1186259 = 1779389) B1779389
theorem B793043 : Blo 790340 793043 := bstep (se 1 (by rfl) ⟨594782, by rfl⟩ : syracuseStep 793043 = 1189565) B1189565
theorem B793059 : Blo 790340 793059 := bstep (se 1 (by rfl) ⟨594794, by rfl⟩ : syracuseStep 793059 = 1189589) B1189589
theorem B1186289 : Blo 790340 1186289 := bstep (se 2 (by rfl) ⟨444858, by rfl⟩ : syracuseStep 1186289 = 889717) B889717
theorem B793075 : Blo 790340 793075 := bstep (se 1 (by rfl) ⟨594806, by rfl⟩ : syracuseStep 793075 = 1189613) B1189613
theorem B1186307 : Blo 790340 1186307 := bstep (se 1 (by rfl) ⟨889730, by rfl⟩ : syracuseStep 1186307 = 1779461) B1779461
theorem B793091 : Blo 790340 793091 := bstep (se 1 (by rfl) ⟨594818, by rfl⟩ : syracuseStep 793091 = 1189637) B1189637
theorem B793107 : Blo 790340 793107 := bstep (se 1 (by rfl) ⟨594830, by rfl⟩ : syracuseStep 793107 = 1189661) B1189661
theorem B1186337 : Blo 790340 1186337 := bstep (se 2 (by rfl) ⟨444876, by rfl⟩ : syracuseStep 1186337 = 889753) B889753
theorem B891427 : Blo 790340 891427 := bstep (se 1 (by rfl) ⟨668570, by rfl⟩ : syracuseStep 891427 = 1337141) B1337141
theorem B793123 : Blo 790340 793123 := bstep (se 1 (by rfl) ⟨594842, by rfl⟩ : syracuseStep 793123 = 1189685) B1189685
theorem B1186355 : Blo 790340 1186355 := bstep (se 1 (by rfl) ⟨889766, by rfl⟩ : syracuseStep 1186355 = 1779533) B1779533
theorem B793139 : Blo 790340 793139 := bstep (se 1 (by rfl) ⟨594854, by rfl⟩ : syracuseStep 793139 = 1189709) B1189709
theorem B793155 : Blo 790340 793155 := bstep (se 1 (by rfl) ⟨594866, by rfl⟩ : syracuseStep 793155 = 1189733) B1189733
theorem B1186385 : Blo 790340 1186385 := bstep (se 2 (by rfl) ⟨444894, by rfl⟩ : syracuseStep 1186385 = 889789) B889789
theorem B793171 : Blo 790340 793171 := bstep (se 1 (by rfl) ⟨594878, by rfl⟩ : syracuseStep 793171 = 1189757) B1189757
theorem B1186403 : Blo 790340 1186403 := bstep (se 1 (by rfl) ⟨889802, by rfl⟩ : syracuseStep 1186403 = 1779605) B1779605
theorem B793187 : Blo 790340 793187 := bstep (se 1 (by rfl) ⟨594890, by rfl⟩ : syracuseStep 793187 = 1189781) B1189781
theorem B793203 : Blo 790340 793203 := bstep (se 1 (by rfl) ⟨594902, by rfl⟩ : syracuseStep 793203 = 1189805) B1189805
theorem B1186433 : Blo 790340 1186433 := bstep (se 2 (by rfl) ⟨444912, by rfl⟩ : syracuseStep 1186433 = 889825) B889825
theorem B793219 : Blo 790340 793219 := bstep (se 1 (by rfl) ⟨594914, by rfl⟩ : syracuseStep 793219 = 1189829) B1189829
theorem B1186451 : Blo 790340 1186451 := bstep (se 1 (by rfl) ⟨889838, by rfl⟩ : syracuseStep 1186451 = 1779677) B1779677
theorem B793235 : Blo 790340 793235 := bstep (se 1 (by rfl) ⟨594926, by rfl⟩ : syracuseStep 793235 = 1189853) B1189853
theorem B793251 : Blo 790340 793251 := bstep (se 1 (by rfl) ⟨594938, by rfl⟩ : syracuseStep 793251 = 1189877) B1189877
theorem B1186481 : Blo 790340 1186481 := bstep (se 2 (by rfl) ⟨444930, by rfl⟩ : syracuseStep 1186481 = 889861) B889861
theorem B2005681 : Blo 790340 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B891571 : Blo 790340 891571 := bstep (se 1 (by rfl) ⟨668678, by rfl⟩ : syracuseStep 891571 = 1337357) B1337357
theorem B793267 : Blo 790340 793267 := bstep (se 1 (by rfl) ⟨594950, by rfl⟩ : syracuseStep 793267 = 1189901) B1189901
theorem B1186499 : Blo 790340 1186499 := bstep (se 1 (by rfl) ⟨889874, by rfl⟩ : syracuseStep 1186499 = 1779749) B1779749
theorem B793283 : Blo 790340 793283 := bstep (se 1 (by rfl) ⟨594962, by rfl⟩ : syracuseStep 793283 = 1189925) B1189925
theorem B793299 : Blo 790340 793299 := bstep (se 1 (by rfl) ⟨594974, by rfl⟩ : syracuseStep 793299 = 1189949) B1189949
theorem B1186529 : Blo 790340 1186529 := bstep (se 2 (by rfl) ⟨444948, by rfl⟩ : syracuseStep 1186529 = 889897) B889897
theorem B793315 : Blo 790340 793315 := bstep (se 1 (by rfl) ⟨594986, by rfl⟩ : syracuseStep 793315 = 1189973) B1189973
theorem B3807971 : Blo 790340 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B1186547 : Blo 790340 1186547 := bstep (se 1 (by rfl) ⟨889910, by rfl⟩ : syracuseStep 1186547 = 1779821) B1779821
theorem B793331 : Blo 790340 793331 := bstep (se 1 (by rfl) ⟨594998, by rfl⟩ : syracuseStep 793331 = 1189997) B1189997
theorem B793347 : Blo 790340 793347 := bstep (se 1 (by rfl) ⟨595010, by rfl⟩ : syracuseStep 793347 = 1190021) B1190021
theorem B1186577 : Blo 790340 1186577 := bstep (se 2 (by rfl) ⟨444966, by rfl⟩ : syracuseStep 1186577 = 889933) B889933
theorem B793363 : Blo 790340 793363 := bstep (se 1 (by rfl) ⟨595022, by rfl⟩ : syracuseStep 793363 = 1190045) B1190045
theorem B1186595 : Blo 790340 1186595 := bstep (se 1 (by rfl) ⟨889946, by rfl⟩ : syracuseStep 1186595 = 1779893) B1779893
theorem B793379 : Blo 790340 793379 := bstep (se 1 (by rfl) ⟨595034, by rfl⟩ : syracuseStep 793379 = 1190069) B1190069
theorem B793395 : Blo 790340 793395 := bstep (se 1 (by rfl) ⟨595046, by rfl⟩ : syracuseStep 793395 = 1190093) B1190093
theorem B1186625 : Blo 790340 1186625 := bstep (se 2 (by rfl) ⟨444984, by rfl⟩ : syracuseStep 1186625 = 889969) B889969
theorem B891715 : Blo 790340 891715 := bstep (se 1 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 891715 = 1337573) B1337573
theorem B793411 : Blo 790340 793411 := bstep (se 1 (by rfl) ⟨595058, by rfl⟩ : syracuseStep 793411 = 1190117) B1190117
theorem B1186643 : Blo 790340 1186643 := bstep (se 1 (by rfl) ⟨889982, by rfl⟩ : syracuseStep 1186643 = 1779965) B1779965
theorem B793427 : Blo 790340 793427 := bstep (se 1 (by rfl) ⟨595070, by rfl⟩ : syracuseStep 793427 = 1190141) B1190141
theorem B793443 : Blo 790340 793443 := bstep (se 1 (by rfl) ⟨595082, by rfl⟩ : syracuseStep 793443 = 1190165) B1190165
theorem B1186673 : Blo 790340 1186673 := bstep (se 2 (by rfl) ⟨445002, by rfl⟩ : syracuseStep 1186673 = 890005) B890005
theorem B793459 : Blo 790340 793459 := bstep (se 1 (by rfl) ⟨595094, by rfl⟩ : syracuseStep 793459 = 1190189) B1190189
theorem B1186691 : Blo 790340 1186691 := bstep (se 1 (by rfl) ⟨890018, by rfl⟩ : syracuseStep 1186691 = 1780037) B1780037
theorem B793475 : Blo 790340 793475 := bstep (se 1 (by rfl) ⟨595106, by rfl⟩ : syracuseStep 793475 = 1190213) B1190213
theorem B793491 : Blo 790340 793491 := bstep (se 1 (by rfl) ⟨595118, by rfl⟩ : syracuseStep 793491 = 1190237) B1190237
theorem B1186721 : Blo 790340 1186721 := bstep (se 2 (by rfl) ⟨445020, by rfl⟩ : syracuseStep 1186721 = 890041) B890041
theorem B793507 : Blo 790340 793507 := bstep (se 1 (by rfl) ⟨595130, by rfl⟩ : syracuseStep 793507 = 1190261) B1190261
theorem B1186739 : Blo 790340 1186739 := bstep (se 1 (by rfl) ⟨890054, by rfl⟩ : syracuseStep 1186739 = 1780109) B1780109
theorem B793523 : Blo 790340 793523 := bstep (se 1 (by rfl) ⟨595142, by rfl⟩ : syracuseStep 793523 = 1190285) B1190285
theorem B2005955 : Blo 790340 2005955 := bstep (se 1 (by rfl) ⟨1504466, by rfl⟩ : syracuseStep 2005955 = 3008933) B3008933
theorem B793539 : Blo 790340 793539 := bstep (se 1 (by rfl) ⟨595154, by rfl⟩ : syracuseStep 793539 = 1190309) B1190309
theorem B1186769 : Blo 790340 1186769 := bstep (se 2 (by rfl) ⟨445038, by rfl⟩ : syracuseStep 1186769 = 890077) B890077
theorem B891859 : Blo 790340 891859 := bstep (se 1 (by rfl) ⟨668894, by rfl⟩ : syracuseStep 891859 = 1337789) B1337789
theorem B793555 : Blo 790340 793555 := bstep (se 1 (by rfl) ⟨595166, by rfl⟩ : syracuseStep 793555 = 1190333) B1190333
theorem B1186787 : Blo 790340 1186787 := bstep (se 1 (by rfl) ⟨890090, by rfl⟩ : syracuseStep 1186787 = 1780181) B1780181
theorem B793571 : Blo 790340 793571 := bstep (se 1 (by rfl) ⟨595178, by rfl⟩ : syracuseStep 793571 = 1190357) B1190357
theorem B3808241 : Blo 790340 3808241 := bstep (se 2 (by rfl) ⟨1428090, by rfl⟩ : syracuseStep 3808241 = 2856181) B2856181
theorem B793587 : Blo 790340 793587 := bstep (se 1 (by rfl) ⟨595190, by rfl⟩ : syracuseStep 793587 = 1190381) B1190381
theorem B1186817 : Blo 790340 1186817 := bstep (se 2 (by rfl) ⟨445056, by rfl⟩ : syracuseStep 1186817 = 890113) B890113
theorem B793603 : Blo 790340 793603 := bstep (se 1 (by rfl) ⟨595202, by rfl⟩ : syracuseStep 793603 = 1190405) B1190405
theorem B1186835 : Blo 790340 1186835 := bstep (se 1 (by rfl) ⟨890126, by rfl⟩ : syracuseStep 1186835 = 1780253) B1780253
theorem B793619 : Blo 790340 793619 := bstep (se 1 (by rfl) ⟨595214, by rfl⟩ : syracuseStep 793619 = 1190429) B1190429
theorem B1809443 : Blo 790340 1809443 := bstep (se 1 (by rfl) ⟨1357082, by rfl⟩ : syracuseStep 1809443 = 2714165) B2714165
theorem B793635 : Blo 790340 793635 := bstep (se 1 (by rfl) ⟨595226, by rfl⟩ : syracuseStep 793635 = 1190453) B1190453
theorem B1186865 : Blo 790340 1186865 := bstep (se 2 (by rfl) ⟨445074, by rfl⟩ : syracuseStep 1186865 = 890149) B890149
theorem B793651 : Blo 790340 793651 := bstep (se 1 (by rfl) ⟨595238, by rfl⟩ : syracuseStep 793651 = 1190477) B1190477
theorem B1186883 : Blo 790340 1186883 := bstep (se 1 (by rfl) ⟨890162, by rfl⟩ : syracuseStep 1186883 = 1780325) B1780325
theorem B793667 : Blo 790340 793667 := bstep (se 1 (by rfl) ⟨595250, by rfl⟩ : syracuseStep 793667 = 1190501) B1190501
theorem B793683 : Blo 790340 793683 := bstep (se 1 (by rfl) ⟨595262, by rfl⟩ : syracuseStep 793683 = 1190525) B1190525
theorem B1186913 : Blo 790340 1186913 := bstep (se 2 (by rfl) ⟨445092, by rfl⟩ : syracuseStep 1186913 = 890185) B890185
theorem B4004963 : Blo 790340 4004963 := bstep (se 1 (by rfl) ⟨3003722, by rfl⟩ : syracuseStep 4004963 = 6007445) B6007445
theorem B892003 : Blo 790340 892003 := bstep (se 1 (by rfl) ⟨669002, by rfl⟩ : syracuseStep 892003 = 1338005) B1338005
theorem B793699 : Blo 790340 793699 := bstep (se 1 (by rfl) ⟨595274, by rfl⟩ : syracuseStep 793699 = 1190549) B1190549
theorem B1186931 : Blo 790340 1186931 := bstep (se 1 (by rfl) ⟨890198, by rfl⟩ : syracuseStep 1186931 = 1780397) B1780397
theorem B793715 : Blo 790340 793715 := bstep (se 1 (by rfl) ⟨595286, by rfl⟩ : syracuseStep 793715 = 1190573) B1190573
theorem B2006147 : Blo 790340 2006147 := bstep (se 1 (by rfl) ⟨1504610, by rfl⟩ : syracuseStep 2006147 = 3009221) B3009221
theorem B793731 : Blo 790340 793731 := bstep (se 1 (by rfl) ⟨595298, by rfl⟩ : syracuseStep 793731 = 1190597) B1190597
theorem B1186961 : Blo 790340 1186961 := bstep (se 2 (by rfl) ⟨445110, by rfl⟩ : syracuseStep 1186961 = 890221) B890221
theorem B793747 : Blo 790340 793747 := bstep (se 1 (by rfl) ⟨595310, by rfl⟩ : syracuseStep 793747 = 1190621) B1190621
theorem B1186979 : Blo 790340 1186979 := bstep (se 1 (by rfl) ⟨890234, by rfl⟩ : syracuseStep 1186979 = 1780469) B1780469
theorem B793763 : Blo 790340 793763 := bstep (se 1 (by rfl) ⟨595322, by rfl⟩ : syracuseStep 793763 = 1190645) B1190645
theorem B793779 : Blo 790340 793779 := bstep (se 1 (by rfl) ⟨595334, by rfl⟩ : syracuseStep 793779 = 1190669) B1190669
theorem B1187009 : Blo 790340 1187009 := bstep (se 2 (by rfl) ⟨445128, by rfl⟩ : syracuseStep 1187009 = 890257) B890257
theorem B793795 : Blo 790340 793795 := bstep (se 1 (by rfl) ⟨595346, by rfl⟩ : syracuseStep 793795 = 1190693) B1190693
theorem B1187027 : Blo 790340 1187027 := bstep (se 1 (by rfl) ⟨890270, by rfl⟩ : syracuseStep 1187027 = 1780541) B1780541
theorem B793811 : Blo 790340 793811 := bstep (se 1 (by rfl) ⟨595358, by rfl⟩ : syracuseStep 793811 = 1190717) B1190717
theorem B793827 : Blo 790340 793827 := bstep (se 1 (by rfl) ⟨595370, by rfl⟩ : syracuseStep 793827 = 1190741) B1190741
theorem B1187057 : Blo 790340 1187057 := bstep (se 2 (by rfl) ⟨445146, by rfl⟩ : syracuseStep 1187057 = 890293) B890293
theorem B892147 : Blo 790340 892147 := bstep (se 1 (by rfl) ⟨669110, by rfl⟩ : syracuseStep 892147 = 1338221) B1338221
theorem B793843 : Blo 790340 793843 := bstep (se 1 (by rfl) ⟨595382, by rfl⟩ : syracuseStep 793843 = 1190765) B1190765
theorem B1187075 : Blo 790340 1187075 := bstep (se 1 (by rfl) ⟨890306, by rfl⟩ : syracuseStep 1187075 = 1780613) B1780613
theorem B793859 : Blo 790340 793859 := bstep (se 1 (by rfl) ⟨595394, by rfl⟩ : syracuseStep 793859 = 1190789) B1190789
theorem B793875 : Blo 790340 793875 := bstep (se 1 (by rfl) ⟨595406, by rfl⟩ : syracuseStep 793875 = 1190813) B1190813
theorem B1187105 : Blo 790340 1187105 := bstep (se 2 (by rfl) ⟨445164, by rfl⟩ : syracuseStep 1187105 = 890329) B890329
theorem B793891 : Blo 790340 793891 := bstep (se 1 (by rfl) ⟨595418, by rfl⟩ : syracuseStep 793891 = 1190837) B1190837
theorem B1187123 : Blo 790340 1187123 := bstep (se 1 (by rfl) ⟨890342, by rfl⟩ : syracuseStep 1187123 = 1780685) B1780685
theorem B793907 : Blo 790340 793907 := bstep (se 1 (by rfl) ⟨595430, by rfl⟩ : syracuseStep 793907 = 1190861) B1190861
theorem B793923 : Blo 790340 793923 := bstep (se 1 (by rfl) ⟨595442, by rfl⟩ : syracuseStep 793923 = 1190885) B1190885
theorem B1187153 : Blo 790340 1187153 := bstep (se 2 (by rfl) ⟨445182, by rfl⟩ : syracuseStep 1187153 = 890365) B890365
theorem B793939 : Blo 790340 793939 := bstep (se 1 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 793939 = 1190909) B1190909
theorem B1187171 : Blo 790340 1187171 := bstep (se 1 (by rfl) ⟨890378, by rfl⟩ : syracuseStep 1187171 = 1780757) B1780757
theorem B793955 : Blo 790340 793955 := bstep (se 1 (by rfl) ⟨595466, by rfl⟩ : syracuseStep 793955 = 1190933) B1190933
theorem B793971 : Blo 790340 793971 := bstep (se 1 (by rfl) ⟨595478, by rfl⟩ : syracuseStep 793971 = 1190957) B1190957
theorem B1187201 : Blo 790340 1187201 := bstep (se 2 (by rfl) ⟨445200, by rfl⟩ : syracuseStep 1187201 = 890401) B890401
theorem B892291 : Blo 790340 892291 := bstep (se 1 (by rfl) ⟨669218, by rfl⟩ : syracuseStep 892291 = 1338437) B1338437
theorem B793987 : Blo 790340 793987 := bstep (se 1 (by rfl) ⟨595490, by rfl⟩ : syracuseStep 793987 = 1190981) B1190981
theorem B5086597 : Blo 790340 5086597 := bstep (se 4 (by rfl) ⟨476868, by rfl⟩ : syracuseStep 5086597 = 953737) B953737
theorem B1187219 : Blo 790340 1187219 := bstep (se 1 (by rfl) ⟨890414, by rfl⟩ : syracuseStep 1187219 = 1780829) B1780829
theorem B794003 : Blo 790340 794003 := bstep (se 1 (by rfl) ⟨595502, by rfl⟩ : syracuseStep 794003 = 1191005) B1191005
theorem B794019 : Blo 790340 794019 := bstep (se 1 (by rfl) ⟨595514, by rfl⟩ : syracuseStep 794019 = 1191029) B1191029
theorem B1187249 : Blo 790340 1187249 := bstep (se 2 (by rfl) ⟨445218, by rfl⟩ : syracuseStep 1187249 = 890437) B890437
theorem B794035 : Blo 790340 794035 := bstep (se 1 (by rfl) ⟨595526, by rfl⟩ : syracuseStep 794035 = 1191053) B1191053
theorem B1187267 : Blo 790340 1187267 := bstep (se 1 (by rfl) ⟨890450, by rfl⟩ : syracuseStep 1187267 = 1780901) B1780901
theorem B794051 : Blo 790340 794051 := bstep (se 1 (by rfl) ⟨595538, by rfl⟩ : syracuseStep 794051 = 1191077) B1191077
theorem B794067 : Blo 790340 794067 := bstep (se 1 (by rfl) ⟨595550, by rfl⟩ : syracuseStep 794067 = 1191101) B1191101
theorem B1187297 : Blo 790340 1187297 := bstep (se 2 (by rfl) ⟨445236, by rfl⟩ : syracuseStep 1187297 = 890473) B890473
theorem B794083 : Blo 790340 794083 := bstep (se 1 (by rfl) ⟨595562, by rfl⟩ : syracuseStep 794083 = 1191125) B1191125
theorem B1187315 : Blo 790340 1187315 := bstep (se 1 (by rfl) ⟨890486, by rfl⟩ : syracuseStep 1187315 = 1780973) B1780973
theorem B794099 : Blo 790340 794099 := bstep (se 1 (by rfl) ⟨595574, by rfl⟩ : syracuseStep 794099 = 1191149) B1191149
theorem B794115 : Blo 790340 794115 := bstep (se 1 (by rfl) ⟨595586, by rfl⟩ : syracuseStep 794115 = 1191173) B1191173
theorem B1187345 : Blo 790340 1187345 := bstep (se 2 (by rfl) ⟨445254, by rfl⟩ : syracuseStep 1187345 = 890509) B890509
theorem B892435 : Blo 790340 892435 := bstep (se 1 (by rfl) ⟨669326, by rfl⟩ : syracuseStep 892435 = 1338653) B1338653
theorem B794131 : Blo 790340 794131 := bstep (se 1 (by rfl) ⟨595598, by rfl⟩ : syracuseStep 794131 = 1191197) B1191197
theorem B1187363 : Blo 790340 1187363 := bstep (se 1 (by rfl) ⟨890522, by rfl⟩ : syracuseStep 1187363 = 1781045) B1781045
theorem B794147 : Blo 790340 794147 := bstep (se 1 (by rfl) ⟨595610, by rfl⟩ : syracuseStep 794147 = 1191221) B1191221
theorem B794163 : Blo 790340 794163 := bstep (se 1 (by rfl) ⟨595622, by rfl⟩ : syracuseStep 794163 = 1191245) B1191245
theorem B1187393 : Blo 790340 1187393 := bstep (se 2 (by rfl) ⟨445272, by rfl⟩ : syracuseStep 1187393 = 890545) B890545
theorem B794179 : Blo 790340 794179 := bstep (se 1 (by rfl) ⟨595634, by rfl⟩ : syracuseStep 794179 = 1191269) B1191269
theorem B1187411 : Blo 790340 1187411 := bstep (se 1 (by rfl) ⟨890558, by rfl⟩ : syracuseStep 1187411 = 1781117) B1781117
theorem B794195 : Blo 790340 794195 := bstep (se 1 (by rfl) ⟨595646, by rfl⟩ : syracuseStep 794195 = 1191293) B1191293
theorem B794211 : Blo 790340 794211 := bstep (se 1 (by rfl) ⟨595658, by rfl⟩ : syracuseStep 794211 = 1191317) B1191317
theorem B1187441 : Blo 790340 1187441 := bstep (se 2 (by rfl) ⟨445290, by rfl⟩ : syracuseStep 1187441 = 890581) B890581
theorem B794227 : Blo 790340 794227 := bstep (se 1 (by rfl) ⟨595670, by rfl⟩ : syracuseStep 794227 = 1191341) B1191341
theorem B1187459 : Blo 790340 1187459 := bstep (se 1 (by rfl) ⟨890594, by rfl⟩ : syracuseStep 1187459 = 1781189) B1781189
theorem B794243 : Blo 790340 794243 := bstep (se 1 (by rfl) ⟨595682, by rfl⟩ : syracuseStep 794243 = 1191365) B1191365
theorem B794259 : Blo 790340 794259 := bstep (se 1 (by rfl) ⟨595694, by rfl⟩ : syracuseStep 794259 = 1191389) B1191389
theorem B1187489 : Blo 790340 1187489 := bstep (se 2 (by rfl) ⟨445308, by rfl⟩ : syracuseStep 1187489 = 890617) B890617
theorem B892579 : Blo 790340 892579 := bstep (se 1 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 892579 = 1338869) B1338869
theorem B794275 : Blo 790340 794275 := bstep (se 1 (by rfl) ⟨595706, by rfl⟩ : syracuseStep 794275 = 1191413) B1191413
theorem B1187507 : Blo 790340 1187507 := bstep (se 1 (by rfl) ⟨890630, by rfl⟩ : syracuseStep 1187507 = 1781261) B1781261
theorem B794291 : Blo 790340 794291 := bstep (se 1 (by rfl) ⟨595718, by rfl⟩ : syracuseStep 794291 = 1191437) B1191437
theorem B794307 : Blo 790340 794307 := bstep (se 1 (by rfl) ⟨595730, by rfl⟩ : syracuseStep 794307 = 1191461) B1191461
theorem B1187537 : Blo 790340 1187537 := bstep (se 2 (by rfl) ⟨445326, by rfl⟩ : syracuseStep 1187537 = 890653) B890653
theorem B794323 : Blo 790340 794323 := bstep (se 1 (by rfl) ⟨595742, by rfl⟩ : syracuseStep 794323 = 1191485) B1191485
theorem B1187555 : Blo 790340 1187555 := bstep (se 1 (by rfl) ⟨890666, by rfl⟩ : syracuseStep 1187555 = 1781333) B1781333
theorem B794339 : Blo 790340 794339 := bstep (se 1 (by rfl) ⟨595754, by rfl⟩ : syracuseStep 794339 = 1191509) B1191509
theorem B1187585 : Blo 790340 1187585 := bstep (se 2 (by rfl) ⟨445344, by rfl⟩ : syracuseStep 1187585 = 890689) B890689
theorem B10133261 : Blo 790340 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B1187603 : Blo 790340 1187603 := bstep (se 1 (by rfl) ⟨890702, by rfl⟩ : syracuseStep 1187603 = 1781405) B1781405
theorem B1187633 : Blo 790340 1187633 := bstep (se 2 (by rfl) ⟨445362, by rfl⟩ : syracuseStep 1187633 = 890725) B890725
theorem B892723 : Blo 790340 892723 := bstep (se 1 (by rfl) ⟨669542, by rfl⟩ : syracuseStep 892723 = 1339085) B1339085
theorem B1187651 : Blo 790340 1187651 := bstep (se 1 (by rfl) ⟨890738, by rfl⟩ : syracuseStep 1187651 = 1781477) B1781477
theorem B1187681 : Blo 790340 1187681 := bstep (se 2 (by rfl) ⟨445380, by rfl⟩ : syracuseStep 1187681 = 890761) B890761
theorem B3383153 : Blo 790340 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B1187699 : Blo 790340 1187699 := bstep (se 1 (by rfl) ⟨890774, by rfl⟩ : syracuseStep 1187699 = 1781549) B1781549
theorem B4005773 : Blo 790340 4005773 := bstep (se 3 (by rfl) ⟨751082, by rfl⟩ : syracuseStep 4005773 = 1502165) B1502165
theorem B1187729 : Blo 790340 1187729 := bstep (se 2 (by rfl) ⟨445398, by rfl⟩ : syracuseStep 1187729 = 890797) B890797
theorem B1187747 : Blo 790340 1187747 := bstep (se 1 (by rfl) ⟨890810, by rfl⟩ : syracuseStep 1187747 = 1781621) B1781621
theorem B1187777 : Blo 790340 1187777 := bstep (se 2 (by rfl) ⟨445416, by rfl⟩ : syracuseStep 1187777 = 890833) B890833
theorem B892867 : Blo 790340 892867 := bstep (se 1 (by rfl) ⟨669650, by rfl⟩ : syracuseStep 892867 = 1339301) B1339301
theorem B1187795 : Blo 790340 1187795 := bstep (se 1 (by rfl) ⟨890846, by rfl⟩ : syracuseStep 1187795 = 1781693) B1781693
theorem B1187825 : Blo 790340 1187825 := bstep (se 2 (by rfl) ⟨445434, by rfl⟩ : syracuseStep 1187825 = 890869) B890869
theorem B1187843 : Blo 790340 1187843 := bstep (se 1 (by rfl) ⟨890882, by rfl⟩ : syracuseStep 1187843 = 1781765) B1781765
theorem B1187873 : Blo 790340 1187873 := bstep (se 2 (by rfl) ⟨445452, by rfl⟩ : syracuseStep 1187873 = 890905) B890905
theorem B2007089 : Blo 790340 2007089 := bstep (se 2 (by rfl) ⟨752658, by rfl⟩ : syracuseStep 2007089 = 1505317) B1505317
theorem B1187891 : Blo 790340 1187891 := bstep (se 1 (by rfl) ⟨890918, by rfl⟩ : syracuseStep 1187891 = 1781837) B1781837
theorem B1187921 : Blo 790340 1187921 := bstep (se 2 (by rfl) ⟨445470, by rfl⟩ : syracuseStep 1187921 = 890941) B890941
theorem B893011 : Blo 790340 893011 := bstep (se 1 (by rfl) ⟨669758, by rfl⟩ : syracuseStep 893011 = 1339517) B1339517
theorem B1187939 : Blo 790340 1187939 := bstep (se 1 (by rfl) ⟨890954, by rfl⟩ : syracuseStep 1187939 = 1781909) B1781909
theorem B2007139 : Blo 790340 2007139 := bstep (se 1 (by rfl) ⟨1505354, by rfl⟩ : syracuseStep 2007139 = 3010709) B3010709
theorem B1187969 : Blo 790340 1187969 := bstep (se 2 (by rfl) ⟨445488, by rfl⟩ : syracuseStep 1187969 = 890977) B890977
theorem B1187987 : Blo 790340 1187987 := bstep (se 1 (by rfl) ⟨890990, by rfl⟩ : syracuseStep 1187987 = 1781981) B1781981
theorem B1188017 : Blo 790340 1188017 := bstep (se 2 (by rfl) ⟨445506, by rfl⟩ : syracuseStep 1188017 = 891013) B891013
theorem B1188035 : Blo 790340 1188035 := bstep (se 1 (by rfl) ⟨891026, by rfl⟩ : syracuseStep 1188035 = 1782053) B1782053
theorem B1188065 : Blo 790340 1188065 := bstep (se 2 (by rfl) ⟨445524, by rfl⟩ : syracuseStep 1188065 = 891049) B891049
theorem B893155 : Blo 790340 893155 := bstep (se 1 (by rfl) ⟨669866, by rfl⟩ : syracuseStep 893155 = 1339733) B1339733
theorem B2007281 : Blo 790340 2007281 := bstep (se 2 (by rfl) ⟨752730, by rfl⟩ : syracuseStep 2007281 = 1505461) B1505461
theorem B1188083 : Blo 790340 1188083 := bstep (se 1 (by rfl) ⟨891062, by rfl⟩ : syracuseStep 1188083 = 1782125) B1782125
theorem B1188113 : Blo 790340 1188113 := bstep (se 2 (by rfl) ⟨445542, by rfl⟩ : syracuseStep 1188113 = 891085) B891085
theorem B1188131 : Blo 790340 1188131 := bstep (se 1 (by rfl) ⟨891098, by rfl⟩ : syracuseStep 1188131 = 1782197) B1782197
theorem B1188161 : Blo 790340 1188161 := bstep (se 2 (by rfl) ⟨445560, by rfl⟩ : syracuseStep 1188161 = 891121) B891121
theorem B1188179 : Blo 790340 1188179 := bstep (se 1 (by rfl) ⟨891134, by rfl⟩ : syracuseStep 1188179 = 1782269) B1782269
theorem B1188209 : Blo 790340 1188209 := bstep (se 2 (by rfl) ⟨445578, by rfl⟩ : syracuseStep 1188209 = 891157) B891157
theorem B893299 : Blo 790340 893299 := bstep (se 1 (by rfl) ⟨669974, by rfl⟩ : syracuseStep 893299 = 1339949) B1339949
theorem B1188227 : Blo 790340 1188227 := bstep (se 1 (by rfl) ⟨891170, by rfl⟩ : syracuseStep 1188227 = 1782341) B1782341
theorem B1188257 : Blo 790340 1188257 := bstep (se 2 (by rfl) ⟨445596, by rfl⟩ : syracuseStep 1188257 = 891193) B891193
theorem B1188275 : Blo 790340 1188275 := bstep (se 1 (by rfl) ⟨891206, by rfl⟩ : syracuseStep 1188275 = 1782413) B1782413
theorem B1188305 : Blo 790340 1188305 := bstep (se 2 (by rfl) ⟨445614, by rfl⟩ : syracuseStep 1188305 = 891229) B891229
theorem B1188323 : Blo 790340 1188323 := bstep (se 1 (by rfl) ⟨891242, by rfl⟩ : syracuseStep 1188323 = 1782485) B1782485
theorem B1188353 : Blo 790340 1188353 := bstep (se 2 (by rfl) ⟨445632, by rfl⟩ : syracuseStep 1188353 = 891265) B891265
theorem B893443 : Blo 790340 893443 := bstep (se 1 (by rfl) ⟨670082, by rfl⟩ : syracuseStep 893443 = 1340165) B1340165
theorem B5415437 : Blo 790340 5415437 := bstep (se 3 (by rfl) ⟨1015394, by rfl⟩ : syracuseStep 5415437 = 2030789) B2030789
theorem B1188371 : Blo 790340 1188371 := bstep (se 1 (by rfl) ⟨891278, by rfl⟩ : syracuseStep 1188371 = 1782557) B1782557
theorem B1188401 : Blo 790340 1188401 := bstep (se 2 (by rfl) ⟨445650, by rfl⟩ : syracuseStep 1188401 = 891301) B891301
theorem B1188419 : Blo 790340 1188419 := bstep (se 1 (by rfl) ⟨891314, by rfl⟩ : syracuseStep 1188419 = 1782629) B1782629
theorem B1188449 : Blo 790340 1188449 := bstep (se 2 (by rfl) ⟨445668, by rfl⟩ : syracuseStep 1188449 = 891337) B891337
theorem B3809891 : Blo 790340 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B1188467 : Blo 790340 1188467 := bstep (se 1 (by rfl) ⟨891350, by rfl⟩ : syracuseStep 1188467 = 1782701) B1782701
theorem B1188497 : Blo 790340 1188497 := bstep (se 2 (by rfl) ⟨445686, by rfl⟩ : syracuseStep 1188497 = 891373) B891373
theorem B893587 : Blo 790340 893587 := bstep (se 1 (by rfl) ⟨670190, by rfl⟩ : syracuseStep 893587 = 1340381) B1340381
theorem B1188515 : Blo 790340 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B1188545 : Blo 790340 1188545 := bstep (se 2 (by rfl) ⟨445704, by rfl⟩ : syracuseStep 1188545 = 891409) B891409
theorem B2859725 : Blo 790340 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B1188563 : Blo 790340 1188563 := bstep (se 1 (by rfl) ⟨891422, by rfl⟩ : syracuseStep 1188563 = 1782845) B1782845
theorem B1778417 : Blo 790340 1778417 := bstep (se 2 (by rfl) ⟨666906, by rfl⟩ : syracuseStep 1778417 = 1333813) B1333813
theorem B1188593 : Blo 790340 1188593 := bstep (se 2 (by rfl) ⟨445722, by rfl⟩ : syracuseStep 1188593 = 891445) B891445
theorem B1778435 : Blo 790340 1778435 := bstep (se 1 (by rfl) ⟨1333826, by rfl⟩ : syracuseStep 1778435 = 2667653) B2667653
theorem B1188611 : Blo 790340 1188611 := bstep (se 1 (by rfl) ⟨891458, by rfl⟩ : syracuseStep 1188611 = 1782917) B1782917
theorem B1188641 : Blo 790340 1188641 := bstep (se 2 (by rfl) ⟨445740, by rfl⟩ : syracuseStep 1188641 = 891481) B891481
theorem B1188659 : Blo 790340 1188659 := bstep (se 1 (by rfl) ⟨891494, by rfl⟩ : syracuseStep 1188659 = 1782989) B1782989
theorem B1188689 : Blo 790340 1188689 := bstep (se 2 (by rfl) ⟨445758, by rfl⟩ : syracuseStep 1188689 = 891517) B891517
theorem B1188707 : Blo 790340 1188707 := bstep (se 1 (by rfl) ⟨891530, by rfl⟩ : syracuseStep 1188707 = 1783061) B1783061
theorem B2138989 : Blo 790340 2138989 := bstep (se 3 (by rfl) ⟨401060, by rfl⟩ : syracuseStep 2138989 = 802121) B802121
theorem B1188737 : Blo 790340 1188737 := bstep (se 2 (by rfl) ⟨445776, by rfl⟩ : syracuseStep 1188737 = 891553) B891553
theorem B1319825 : Blo 790340 1319825 := bstep (se 2 (by rfl) ⟨494934, by rfl⟩ : syracuseStep 1319825 = 989869) B989869
theorem B1188755 : Blo 790340 1188755 := bstep (se 1 (by rfl) ⟨891566, by rfl⟩ : syracuseStep 1188755 = 1783133) B1783133
theorem B1188785 : Blo 790340 1188785 := bstep (se 2 (by rfl) ⟨445794, by rfl⟩ : syracuseStep 1188785 = 891589) B891589
theorem B1188803 : Blo 790340 1188803 := bstep (se 1 (by rfl) ⟨891602, by rfl⟩ : syracuseStep 1188803 = 1783205) B1783205
theorem B1188833 : Blo 790340 1188833 := bstep (se 2 (by rfl) ⟨445812, by rfl⟩ : syracuseStep 1188833 = 891625) B891625
theorem B1188851 : Blo 790340 1188851 := bstep (se 1 (by rfl) ⟨891638, by rfl⟩ : syracuseStep 1188851 = 1783277) B1783277
theorem B1778705 : Blo 790340 1778705 := bstep (se 2 (by rfl) ⟨667014, by rfl⟩ : syracuseStep 1778705 = 1334029) B1334029
theorem B1188881 : Blo 790340 1188881 := bstep (se 2 (by rfl) ⟨445830, by rfl⟩ : syracuseStep 1188881 = 891661) B891661
theorem B1778723 : Blo 790340 1778723 := bstep (se 1 (by rfl) ⟨1334042, by rfl⟩ : syracuseStep 1778723 = 2668085) B2668085
theorem B1188899 : Blo 790340 1188899 := bstep (se 1 (by rfl) ⟨891674, by rfl⟩ : syracuseStep 1188899 = 1783349) B1783349
theorem B1188929 : Blo 790340 1188929 := bstep (se 2 (by rfl) ⟨445848, by rfl⟩ : syracuseStep 1188929 = 891697) B891697
theorem B1188947 : Blo 790340 1188947 := bstep (se 1 (by rfl) ⟨891710, by rfl⟩ : syracuseStep 1188947 = 1783421) B1783421
theorem B1188977 : Blo 790340 1188977 := bstep (se 2 (by rfl) ⟨445866, by rfl⟩ : syracuseStep 1188977 = 891733) B891733
theorem B1188995 : Blo 790340 1188995 := bstep (se 1 (by rfl) ⟨891746, by rfl⟩ : syracuseStep 1188995 = 1783493) B1783493
theorem B1189025 : Blo 790340 1189025 := bstep (se 2 (by rfl) ⟨445884, by rfl⟩ : syracuseStep 1189025 = 891769) B891769
theorem B1189043 : Blo 790340 1189043 := bstep (se 1 (by rfl) ⟨891782, by rfl⟩ : syracuseStep 1189043 = 1783565) B1783565
theorem B1189073 : Blo 790340 1189073 := bstep (se 2 (by rfl) ⟨445902, by rfl⟩ : syracuseStep 1189073 = 891805) B891805
theorem B2008273 : Blo 790340 2008273 := bstep (se 2 (by rfl) ⟨753102, by rfl⟩ : syracuseStep 2008273 = 1506205) B1506205
theorem B6005987 : Blo 790340 6005987 := bstep (se 1 (by rfl) ⟨4504490, by rfl⟩ : syracuseStep 6005987 = 9008981) B9008981
theorem B1189091 : Blo 790340 1189091 := bstep (se 1 (by rfl) ⟨891818, by rfl⟩ : syracuseStep 1189091 = 1783637) B1783637
theorem B1189121 : Blo 790340 1189121 := bstep (se 2 (by rfl) ⟨445920, by rfl⟩ : syracuseStep 1189121 = 891841) B891841
theorem B1189139 : Blo 790340 1189139 := bstep (se 1 (by rfl) ⟨891854, by rfl⟩ : syracuseStep 1189139 = 1783709) B1783709
theorem B1778993 : Blo 790340 1778993 := bstep (se 2 (by rfl) ⟨667122, by rfl⟩ : syracuseStep 1778993 = 1334245) B1334245
theorem B1189169 : Blo 790340 1189169 := bstep (se 2 (by rfl) ⟨445938, by rfl⟩ : syracuseStep 1189169 = 891877) B891877
theorem B10167605 : Blo 790340 10167605 := bstep (se 5 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 10167605 = 953213) B953213
theorem B1779011 : Blo 790340 1779011 := bstep (se 1 (by rfl) ⟨1334258, by rfl⟩ : syracuseStep 1779011 = 2668517) B2668517
theorem B1189187 : Blo 790340 1189187 := bstep (se 1 (by rfl) ⟨891890, by rfl⟩ : syracuseStep 1189187 = 1783781) B1783781
theorem B1189217 : Blo 790340 1189217 := bstep (se 2 (by rfl) ⟨445956, by rfl⟩ : syracuseStep 1189217 = 891913) B891913
theorem B1189235 : Blo 790340 1189235 := bstep (se 1 (by rfl) ⟨891926, by rfl⟩ : syracuseStep 1189235 = 1783853) B1783853
theorem B1189265 : Blo 790340 1189265 := bstep (se 2 (by rfl) ⟨445974, by rfl⟩ : syracuseStep 1189265 = 891949) B891949
theorem B1189283 : Blo 790340 1189283 := bstep (se 1 (by rfl) ⟨891962, by rfl⟩ : syracuseStep 1189283 = 1783925) B1783925
theorem B1189313 : Blo 790340 1189313 := bstep (se 2 (by rfl) ⟨445992, by rfl⟩ : syracuseStep 1189313 = 891985) B891985
theorem B1189331 : Blo 790340 1189331 := bstep (se 1 (by rfl) ⟨891998, by rfl⟩ : syracuseStep 1189331 = 1783997) B1783997
theorem B2008547 : Blo 790340 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B1189361 : Blo 790340 1189361 := bstep (se 2 (by rfl) ⟨446010, by rfl⟩ : syracuseStep 1189361 = 892021) B892021
theorem B1189379 : Blo 790340 1189379 := bstep (se 1 (by rfl) ⟨892034, by rfl⟩ : syracuseStep 1189379 = 1784069) B1784069
theorem B1189409 : Blo 790340 1189409 := bstep (se 2 (by rfl) ⟨446028, by rfl⟩ : syracuseStep 1189409 = 892057) B892057
theorem B1189427 : Blo 790340 1189427 := bstep (se 1 (by rfl) ⟨892070, by rfl⟩ : syracuseStep 1189427 = 1784141) B1784141
theorem B1779281 : Blo 790340 1779281 := bstep (se 2 (by rfl) ⟨667230, by rfl⟩ : syracuseStep 1779281 = 1334461) B1334461
theorem B1189457 : Blo 790340 1189457 := bstep (se 2 (by rfl) ⟨446046, by rfl⟩ : syracuseStep 1189457 = 892093) B892093
theorem B1779299 : Blo 790340 1779299 := bstep (se 1 (by rfl) ⟨1334474, by rfl⟩ : syracuseStep 1779299 = 2668949) B2668949
theorem B1189475 : Blo 790340 1189475 := bstep (se 1 (by rfl) ⟨892106, by rfl⟩ : syracuseStep 1189475 = 1784213) B1784213
theorem B1189505 : Blo 790340 1189505 := bstep (se 2 (by rfl) ⟨446064, by rfl⟩ : syracuseStep 1189505 = 892129) B892129
theorem B1189523 : Blo 790340 1189523 := bstep (se 1 (by rfl) ⟨892142, by rfl⟩ : syracuseStep 1189523 = 1784285) B1784285
theorem B2008739 : Blo 790340 2008739 := bstep (se 1 (by rfl) ⟨1506554, by rfl⟩ : syracuseStep 2008739 = 3013109) B3013109
theorem B1189553 : Blo 790340 1189553 := bstep (se 2 (by rfl) ⟨446082, by rfl⟩ : syracuseStep 1189553 = 892165) B892165
theorem B1189571 : Blo 790340 1189571 := bstep (se 1 (by rfl) ⟨892178, by rfl⟩ : syracuseStep 1189571 = 1784357) B1784357
theorem B1189601 : Blo 790340 1189601 := bstep (se 2 (by rfl) ⟨446100, by rfl⟩ : syracuseStep 1189601 = 892201) B892201
theorem B1189619 : Blo 790340 1189619 := bstep (se 1 (by rfl) ⟨892214, by rfl⟩ : syracuseStep 1189619 = 1784429) B1784429
theorem B1189649 : Blo 790340 1189649 := bstep (se 2 (by rfl) ⟨446118, by rfl⟩ : syracuseStep 1189649 = 892237) B892237
theorem B1189667 : Blo 790340 1189667 := bstep (se 1 (by rfl) ⟨892250, by rfl⟩ : syracuseStep 1189667 = 1784501) B1784501
theorem B1189697 : Blo 790340 1189697 := bstep (se 2 (by rfl) ⟨446136, by rfl⟩ : syracuseStep 1189697 = 892273) B892273
theorem B1189715 : Blo 790340 1189715 := bstep (se 1 (by rfl) ⟨892286, by rfl⟩ : syracuseStep 1189715 = 1784573) B1784573
theorem B1779569 : Blo 790340 1779569 := bstep (se 2 (by rfl) ⟨667338, by rfl⟩ : syracuseStep 1779569 = 1334677) B1334677
theorem B1189745 : Blo 790340 1189745 := bstep (se 2 (by rfl) ⟨446154, by rfl⟩ : syracuseStep 1189745 = 892309) B892309
theorem B1779587 : Blo 790340 1779587 := bstep (se 1 (by rfl) ⟨1334690, by rfl⟩ : syracuseStep 1779587 = 2669381) B2669381
theorem B1189763 : Blo 790340 1189763 := bstep (se 1 (by rfl) ⟨892322, by rfl⟩ : syracuseStep 1189763 = 1784645) B1784645
theorem B2533265 : Blo 790340 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B1189793 : Blo 790340 1189793 := bstep (se 2 (by rfl) ⟨446172, by rfl⟩ : syracuseStep 1189793 = 892345) B892345
theorem B1189811 : Blo 790340 1189811 := bstep (se 1 (by rfl) ⟨892358, by rfl⟩ : syracuseStep 1189811 = 1784717) B1784717
theorem B1189841 : Blo 790340 1189841 := bstep (se 2 (by rfl) ⟨446190, by rfl⟩ : syracuseStep 1189841 = 892381) B892381
theorem B1189859 : Blo 790340 1189859 := bstep (se 1 (by rfl) ⟨892394, by rfl⟩ : syracuseStep 1189859 = 1784789) B1784789
theorem B1189889 : Blo 790340 1189889 := bstep (se 2 (by rfl) ⟨446208, by rfl⟩ : syracuseStep 1189889 = 892417) B892417
theorem B1189907 : Blo 790340 1189907 := bstep (se 1 (by rfl) ⟨892430, by rfl⟩ : syracuseStep 1189907 = 1784861) B1784861
theorem B1189937 : Blo 790340 1189937 := bstep (se 2 (by rfl) ⟨446226, by rfl⟩ : syracuseStep 1189937 = 892453) B892453
theorem B1189955 : Blo 790340 1189955 := bstep (se 1 (by rfl) ⟨892466, by rfl⟩ : syracuseStep 1189955 = 1784933) B1784933
theorem B2533457 : Blo 790340 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B1189985 : Blo 790340 1189985 := bstep (se 2 (by rfl) ⟨446244, by rfl⟩ : syracuseStep 1189985 = 892489) B892489
theorem B1190003 : Blo 790340 1190003 := bstep (se 1 (by rfl) ⟨892502, by rfl⟩ : syracuseStep 1190003 = 1785005) B1785005
theorem B1779857 : Blo 790340 1779857 := bstep (se 2 (by rfl) ⟨667446, by rfl⟩ : syracuseStep 1779857 = 1334893) B1334893
theorem B1190033 : Blo 790340 1190033 := bstep (se 2 (by rfl) ⟨446262, by rfl⟩ : syracuseStep 1190033 = 892525) B892525
theorem B1779875 : Blo 790340 1779875 := bstep (se 1 (by rfl) ⟨1334906, by rfl⟩ : syracuseStep 1779875 = 2669813) B2669813
theorem B1190051 : Blo 790340 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B1190081 : Blo 790340 1190081 := bstep (se 2 (by rfl) ⟨446280, by rfl⟩ : syracuseStep 1190081 = 892561) B892561
theorem B1190099 : Blo 790340 1190099 := bstep (se 1 (by rfl) ⟨892574, by rfl⟩ : syracuseStep 1190099 = 1785149) B1785149
theorem B1190129 : Blo 790340 1190129 := bstep (se 2 (by rfl) ⟨446298, by rfl⟩ : syracuseStep 1190129 = 892597) B892597
theorem B1190147 : Blo 790340 1190147 := bstep (se 1 (by rfl) ⟨892610, by rfl⟩ : syracuseStep 1190147 = 1785221) B1785221
theorem B3385613 : Blo 790340 3385613 := bstep (se 3 (by rfl) ⟨634802, by rfl⟩ : syracuseStep 3385613 = 1269605) B1269605
theorem B1190177 : Blo 790340 1190177 := bstep (se 2 (by rfl) ⟨446316, by rfl⟩ : syracuseStep 1190177 = 892633) B892633
theorem B1190195 : Blo 790340 1190195 := bstep (se 1 (by rfl) ⟨892646, by rfl⟩ : syracuseStep 1190195 = 1785293) B1785293
theorem B3811661 : Blo 790340 3811661 := bstep (se 3 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 3811661 = 1429373) B1429373
theorem B1190225 : Blo 790340 1190225 := bstep (se 2 (by rfl) ⟨446334, by rfl⟩ : syracuseStep 1190225 = 892669) B892669
theorem B1190243 : Blo 790340 1190243 := bstep (se 1 (by rfl) ⟨892682, by rfl⟩ : syracuseStep 1190243 = 1785365) B1785365
theorem B1190273 : Blo 790340 1190273 := bstep (se 2 (by rfl) ⟨446352, by rfl⟩ : syracuseStep 1190273 = 892705) B892705
theorem B1190291 : Blo 790340 1190291 := bstep (se 1 (by rfl) ⟨892718, by rfl⟩ : syracuseStep 1190291 = 1785437) B1785437
theorem B1780145 : Blo 790340 1780145 := bstep (se 2 (by rfl) ⟨667554, by rfl⟩ : syracuseStep 1780145 = 1335109) B1335109
theorem B1190321 : Blo 790340 1190321 := bstep (se 2 (by rfl) ⟨446370, by rfl⟩ : syracuseStep 1190321 = 892741) B892741
theorem B1780163 : Blo 790340 1780163 := bstep (se 1 (by rfl) ⟨1335122, by rfl⟩ : syracuseStep 1780163 = 2670245) B2670245
theorem B1190339 : Blo 790340 1190339 := bstep (se 1 (by rfl) ⟨892754, by rfl⟩ : syracuseStep 1190339 = 1785509) B1785509
theorem B1190369 : Blo 790340 1190369 := bstep (se 2 (by rfl) ⟨446388, by rfl⟩ : syracuseStep 1190369 = 892777) B892777
theorem B2140643 : Blo 790340 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B1190387 : Blo 790340 1190387 := bstep (se 1 (by rfl) ⟨892790, by rfl⟩ : syracuseStep 1190387 = 1785581) B1785581
theorem B1190417 : Blo 790340 1190417 := bstep (se 2 (by rfl) ⟨446406, by rfl⟩ : syracuseStep 1190417 = 892813) B892813
theorem B1190435 : Blo 790340 1190435 := bstep (se 1 (by rfl) ⟨892826, by rfl⟩ : syracuseStep 1190435 = 1785653) B1785653
theorem B1190465 : Blo 790340 1190465 := bstep (se 2 (by rfl) ⟨446424, by rfl⟩ : syracuseStep 1190465 = 892849) B892849
theorem B2009681 : Blo 790340 2009681 := bstep (se 2 (by rfl) ⟨753630, by rfl⟩ : syracuseStep 2009681 = 1507261) B1507261
theorem B1190483 : Blo 790340 1190483 := bstep (se 1 (by rfl) ⟨892862, by rfl⟩ : syracuseStep 1190483 = 1785725) B1785725
theorem B3385955 : Blo 790340 3385955 := bstep (se 1 (by rfl) ⟨2539466, by rfl⟩ : syracuseStep 3385955 = 5078933) B5078933
theorem B1190513 : Blo 790340 1190513 := bstep (se 2 (by rfl) ⟨446442, by rfl⟩ : syracuseStep 1190513 = 892885) B892885
theorem B1190531 : Blo 790340 1190531 := bstep (se 1 (by rfl) ⟨892898, by rfl⟩ : syracuseStep 1190531 = 1785797) B1785797
theorem B2009731 : Blo 790340 2009731 := bstep (se 1 (by rfl) ⟨1507298, by rfl⟩ : syracuseStep 2009731 = 3014597) B3014597
theorem B1190561 : Blo 790340 1190561 := bstep (se 2 (by rfl) ⟨446460, by rfl⟩ : syracuseStep 1190561 = 892921) B892921
theorem B1190579 : Blo 790340 1190579 := bstep (se 1 (by rfl) ⟨892934, by rfl⟩ : syracuseStep 1190579 = 1785869) B1785869
theorem B1780433 : Blo 790340 1780433 := bstep (se 2 (by rfl) ⟨667662, by rfl⟩ : syracuseStep 1780433 = 1335325) B1335325
theorem B1190609 : Blo 790340 1190609 := bstep (se 2 (by rfl) ⟨446478, by rfl⟩ : syracuseStep 1190609 = 892957) B892957
theorem B1780451 : Blo 790340 1780451 := bstep (se 1 (by rfl) ⟨1335338, by rfl⟩ : syracuseStep 1780451 = 2670677) B2670677
theorem B1190627 : Blo 790340 1190627 := bstep (se 1 (by rfl) ⟨892970, by rfl⟩ : syracuseStep 1190627 = 1785941) B1785941
theorem B4008689 : Blo 790340 4008689 := bstep (se 2 (by rfl) ⟨1503258, by rfl⟩ : syracuseStep 4008689 = 3006517) B3006517
theorem B1190657 : Blo 790340 1190657 := bstep (se 2 (by rfl) ⟨446496, by rfl⟩ : syracuseStep 1190657 = 892993) B892993
theorem B2009873 : Blo 790340 2009873 := bstep (se 2 (by rfl) ⟨753702, by rfl⟩ : syracuseStep 2009873 = 1507405) B1507405
theorem B1190675 : Blo 790340 1190675 := bstep (se 1 (by rfl) ⟨893006, by rfl⟩ : syracuseStep 1190675 = 1786013) B1786013
theorem B1354531 : Blo 790340 1354531 := bstep (se 1 (by rfl) ⟨1015898, by rfl⟩ : syracuseStep 1354531 = 2031797) B2031797
theorem B1190705 : Blo 790340 1190705 := bstep (se 2 (by rfl) ⟨446514, by rfl⟩ : syracuseStep 1190705 = 893029) B893029
theorem B1190723 : Blo 790340 1190723 := bstep (se 1 (by rfl) ⟨893042, by rfl⟩ : syracuseStep 1190723 = 1786085) B1786085
theorem B1190753 : Blo 790340 1190753 := bstep (se 2 (by rfl) ⟨446532, by rfl⟩ : syracuseStep 1190753 = 893065) B893065
theorem B1190771 : Blo 790340 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B1190801 : Blo 790340 1190801 := bstep (se 2 (by rfl) ⟨446550, by rfl⟩ : syracuseStep 1190801 = 893101) B893101
theorem B1190819 : Blo 790340 1190819 := bstep (se 1 (by rfl) ⟨893114, by rfl⟩ : syracuseStep 1190819 = 1786229) B1786229
theorem B1190849 : Blo 790340 1190849 := bstep (se 2 (by rfl) ⟨446568, by rfl⟩ : syracuseStep 1190849 = 893137) B893137
theorem B1190867 : Blo 790340 1190867 := bstep (se 1 (by rfl) ⟨893150, by rfl⟩ : syracuseStep 1190867 = 1786301) B1786301
theorem B1780721 : Blo 790340 1780721 := bstep (se 2 (by rfl) ⟨667770, by rfl⟩ : syracuseStep 1780721 = 1335541) B1335541
theorem B1190897 : Blo 790340 1190897 := bstep (se 2 (by rfl) ⟨446586, by rfl⟩ : syracuseStep 1190897 = 893173) B893173
theorem B1780739 : Blo 790340 1780739 := bstep (se 1 (by rfl) ⟨1335554, by rfl⟩ : syracuseStep 1780739 = 2671109) B2671109
theorem B1190915 : Blo 790340 1190915 := bstep (se 1 (by rfl) ⟨893186, by rfl⟩ : syracuseStep 1190915 = 1786373) B1786373
theorem B1190945 : Blo 790340 1190945 := bstep (se 2 (by rfl) ⟨446604, by rfl⟩ : syracuseStep 1190945 = 893209) B893209
theorem B1190963 : Blo 790340 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B1190993 : Blo 790340 1190993 := bstep (se 2 (by rfl) ⟨446622, by rfl⟩ : syracuseStep 1190993 = 893245) B893245
theorem B1191011 : Blo 790340 1191011 := bstep (se 1 (by rfl) ⟨893258, by rfl⟩ : syracuseStep 1191011 = 1786517) B1786517
theorem B1191041 : Blo 790340 1191041 := bstep (se 2 (by rfl) ⟨446640, by rfl⟩ : syracuseStep 1191041 = 893281) B893281
theorem B1191059 : Blo 790340 1191059 := bstep (se 1 (by rfl) ⟨893294, by rfl⟩ : syracuseStep 1191059 = 1786589) B1786589
theorem B1191089 : Blo 790340 1191089 := bstep (se 2 (by rfl) ⟨446658, by rfl⟩ : syracuseStep 1191089 = 893317) B893317
theorem B1125571 : Blo 790340 1125571 := bstep (se 1 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 1125571 = 1688357) B1688357
theorem B1191107 : Blo 790340 1191107 := bstep (se 1 (by rfl) ⟨893330, by rfl⟩ : syracuseStep 1191107 = 1786661) B1786661
theorem B1191137 : Blo 790340 1191137 := bstep (se 2 (by rfl) ⟨446676, by rfl⟩ : syracuseStep 1191137 = 893353) B893353
theorem B1191155 : Blo 790340 1191155 := bstep (se 1 (by rfl) ⟨893366, by rfl⟩ : syracuseStep 1191155 = 1786733) B1786733
theorem B1223939 : Blo 790340 1223939 := bstep (se 1 (by rfl) ⟨917954, by rfl⟩ : syracuseStep 1223939 = 1835909) B1835909
theorem B1781009 : Blo 790340 1781009 := bstep (se 2 (by rfl) ⟨667878, by rfl⟩ : syracuseStep 1781009 = 1335757) B1335757
theorem B1191185 : Blo 790340 1191185 := bstep (se 2 (by rfl) ⟨446694, by rfl⟩ : syracuseStep 1191185 = 893389) B893389
theorem B1125667 : Blo 790340 1125667 := bstep (se 1 (by rfl) ⟨844250, by rfl⟩ : syracuseStep 1125667 = 1688501) B1688501
theorem B1781027 : Blo 790340 1781027 := bstep (se 1 (by rfl) ⟨1335770, by rfl⟩ : syracuseStep 1781027 = 2671541) B2671541
theorem B1191203 : Blo 790340 1191203 := bstep (se 1 (by rfl) ⟨893402, by rfl⟩ : syracuseStep 1191203 = 1786805) B1786805
theorem B1191233 : Blo 790340 1191233 := bstep (se 2 (by rfl) ⟨446712, by rfl⟩ : syracuseStep 1191233 = 893425) B893425
theorem B1191251 : Blo 790340 1191251 := bstep (se 1 (by rfl) ⟨893438, by rfl⟩ : syracuseStep 1191251 = 1786877) B1786877
theorem B1191281 : Blo 790340 1191281 := bstep (se 2 (by rfl) ⟨446730, by rfl⟩ : syracuseStep 1191281 = 893461) B893461
theorem B1191299 : Blo 790340 1191299 := bstep (se 1 (by rfl) ⟨893474, by rfl⟩ : syracuseStep 1191299 = 1786949) B1786949
theorem B1191329 : Blo 790340 1191329 := bstep (se 2 (by rfl) ⟨446748, by rfl⟩ : syracuseStep 1191329 = 893497) B893497
theorem B1191347 : Blo 790340 1191347 := bstep (se 1 (by rfl) ⟨893510, by rfl⟩ : syracuseStep 1191347 = 1787021) B1787021
theorem B1191377 : Blo 790340 1191377 := bstep (se 2 (by rfl) ⟨446766, by rfl⟩ : syracuseStep 1191377 = 893533) B893533
theorem B1191395 : Blo 790340 1191395 := bstep (se 1 (by rfl) ⟨893546, by rfl⟩ : syracuseStep 1191395 = 1787093) B1787093
theorem B1191425 : Blo 790340 1191425 := bstep (se 2 (by rfl) ⟨446784, by rfl⟩ : syracuseStep 1191425 = 893569) B893569
theorem B1191443 : Blo 790340 1191443 := bstep (se 1 (by rfl) ⟨893582, by rfl⟩ : syracuseStep 1191443 = 1787165) B1787165
theorem B1781297 : Blo 790340 1781297 := bstep (se 2 (by rfl) ⟨667986, by rfl⟩ : syracuseStep 1781297 = 1335973) B1335973
theorem B1191473 : Blo 790340 1191473 := bstep (se 2 (by rfl) ⟨446802, by rfl⟩ : syracuseStep 1191473 = 893605) B893605
theorem B1781315 : Blo 790340 1781315 := bstep (se 1 (by rfl) ⟨1335986, by rfl⟩ : syracuseStep 1781315 = 2671973) B2671973
theorem B1191491 : Blo 790340 1191491 := bstep (se 1 (by rfl) ⟨893618, by rfl⟩ : syracuseStep 1191491 = 1787237) B1787237
theorem B1126163 : Blo 790340 1126163 := bstep (se 1 (by rfl) ⟨844622, by rfl⟩ : syracuseStep 1126163 = 1689245) B1689245
theorem B2404163 : Blo 790340 2404163 := bstep (se 1 (by rfl) ⟨1803122, by rfl⟩ : syracuseStep 2404163 = 3606245) B3606245
theorem B1781585 : Blo 790340 1781585 := bstep (se 2 (by rfl) ⟨668094, by rfl⟩ : syracuseStep 1781585 = 1336189) B1336189
theorem B1781603 : Blo 790340 1781603 := bstep (se 1 (by rfl) ⟨1336202, by rfl⟩ : syracuseStep 1781603 = 2672405) B2672405
theorem B1781873 : Blo 790340 1781873 := bstep (se 2 (by rfl) ⟨668202, by rfl⟩ : syracuseStep 1781873 = 1336405) B1336405
theorem B1781891 : Blo 790340 1781891 := bstep (se 1 (by rfl) ⟨1336418, by rfl⟩ : syracuseStep 1781891 = 2672837) B2672837
theorem B4010147 : Blo 790340 4010147 := bstep (se 1 (by rfl) ⟨3007610, by rfl⟩ : syracuseStep 4010147 = 6015221) B6015221
theorem B2535725 : Blo 790340 2535725 := bstep (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) B950897
theorem B4829489 : Blo 790340 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B2404721 : Blo 790340 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B1126801 : Blo 790340 1126801 := bstep (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) B845101
theorem B1782161 : Blo 790340 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B1782179 : Blo 790340 1782179 := bstep (se 1 (by rfl) ⟨1336634, by rfl⟩ : syracuseStep 1782179 = 2673269) B2673269
theorem B1782449 : Blo 790340 1782449 := bstep (se 2 (by rfl) ⟨668418, by rfl⟩ : syracuseStep 1782449 = 1336837) B1336837
theorem B1782467 : Blo 790340 1782467 := bstep (se 1 (by rfl) ⟨1336850, by rfl⟩ : syracuseStep 1782467 = 2673701) B2673701
theorem B4502213 : Blo 790340 4502213 := bstep (se 4 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 4502213 = 844165) B844165
theorem B1127137 : Blo 790340 1127137 := bstep (se 2 (by rfl) ⟨422676, by rfl⟩ : syracuseStep 1127137 = 845353) B845353
theorem B4633357 : Blo 790340 4633357 := bstep (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) B1737509
theorem B2143021 : Blo 790340 2143021 := bstep (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) B803633
theorem B9646901 : Blo 790340 9646901 := bstep (se 5 (by rfl) ⟨452198, by rfl⟩ : syracuseStep 9646901 = 904397) B904397
theorem B2667437 : Blo 790340 2667437 := bstep (se 3 (by rfl) ⟨500144, by rfl⟩ : syracuseStep 2667437 = 1000289) B1000289
theorem B2569133 : Blo 790340 2569133 := bstep (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) B963425
theorem B4010957 : Blo 790340 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B1782737 : Blo 790340 1782737 := bstep (se 2 (by rfl) ⟨668526, by rfl⟩ : syracuseStep 1782737 = 1337053) B1337053
theorem B2667491 : Blo 790340 2667491 := bstep (se 1 (by rfl) ⟨2000618, by rfl⟩ : syracuseStep 2667491 = 4001237) B4001237
theorem B4568035 : Blo 790340 4568035 := bstep (se 1 (by rfl) ⟨3426026, by rfl⟩ : syracuseStep 4568035 = 6852053) B6852053
theorem B1782755 : Blo 790340 1782755 := bstep (se 1 (by rfl) ⟨1337066, by rfl⟩ : syracuseStep 1782755 = 2674133) B2674133
theorem B2438225 : Blo 790340 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B1717393 : Blo 790340 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B2667761 : Blo 790340 2667761 := bstep (se 2 (by rfl) ⟨1000410, by rfl⟩ : syracuseStep 2667761 = 2000821) B2000821
theorem B1783025 : Blo 790340 1783025 := bstep (se 2 (by rfl) ⟨668634, by rfl⟩ : syracuseStep 1783025 = 1337269) B1337269
theorem B1783043 : Blo 790340 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B1127729 : Blo 790340 1127729 := bstep (se 2 (by rfl) ⟨422898, by rfl⟩ : syracuseStep 1127729 = 845797) B845797
theorem B5715299 : Blo 790340 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B4502897 : Blo 790340 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B1783313 : Blo 790340 1783313 := bstep (se 2 (by rfl) ⟨668742, by rfl⟩ : syracuseStep 1783313 = 1337485) B1337485
theorem B1783331 : Blo 790340 1783331 := bstep (se 1 (by rfl) ⟨1337498, by rfl⟩ : syracuseStep 1783331 = 2674997) B2674997
theorem B2668301 : Blo 790340 2668301 := bstep (se 3 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 2668301 = 1000613) B1000613
theorem B1783601 : Blo 790340 1783601 := bstep (se 2 (by rfl) ⟨668850, by rfl⟩ : syracuseStep 1783601 = 1337701) B1337701
theorem B2668355 : Blo 790340 2668355 := bstep (se 1 (by rfl) ⟨2001266, by rfl⟩ : syracuseStep 2668355 = 4002533) B4002533
theorem B1128259 : Blo 790340 1128259 := bstep (se 1 (by rfl) ⟨846194, by rfl⟩ : syracuseStep 1128259 = 1692389) B1692389
theorem B1783619 : Blo 790340 1783619 := bstep (se 1 (by rfl) ⟨1337714, by rfl⟩ : syracuseStep 1783619 = 2675429) B2675429
theorem B1357651 : Blo 790340 1357651 := bstep (se 1 (by rfl) ⟨1018238, by rfl⟩ : syracuseStep 1357651 = 2036477) B2036477
theorem B2537315 : Blo 790340 2537315 := bstep (se 1 (by rfl) ⟨1902986, by rfl⟩ : syracuseStep 2537315 = 3805973) B3805973
theorem B1521731 : Blo 790340 1521731 := bstep (se 1 (by rfl) ⟨1141298, by rfl⟩ : syracuseStep 1521731 = 2282597) B2282597
theorem B2668625 : Blo 790340 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B1783889 : Blo 790340 1783889 := bstep (se 2 (by rfl) ⟨668958, by rfl⟩ : syracuseStep 1783889 = 1337917) B1337917
theorem B1783907 : Blo 790340 1783907 := bstep (se 1 (by rfl) ⟨1337930, by rfl⟩ : syracuseStep 1783907 = 2675861) B2675861
theorem B1128595 : Blo 790340 1128595 := bstep (se 1 (by rfl) ⟨846446, by rfl⟩ : syracuseStep 1128595 = 1692893) B1692893
theorem B1784177 : Blo 790340 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B1784195 : Blo 790340 1784195 := bstep (se 1 (by rfl) ⟨1338146, by rfl⟩ : syracuseStep 1784195 = 2676293) B2676293
theorem B6011333 : Blo 790340 6011333 := bstep (se 4 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 6011333 = 1127125) B1127125
theorem B3389987 : Blo 790340 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B2669165 : Blo 790340 2669165 := bstep (se 3 (by rfl) ⟨500468, by rfl⟩ : syracuseStep 2669165 = 1000937) B1000937
theorem B4274801 : Blo 790340 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B1784465 : Blo 790340 1784465 := bstep (se 2 (by rfl) ⟨669174, by rfl⟩ : syracuseStep 1784465 = 1338349) B1338349
theorem B2669219 : Blo 790340 2669219 := bstep (se 1 (by rfl) ⟨2001914, by rfl⟩ : syracuseStep 2669219 = 4003829) B4003829
theorem B1784483 : Blo 790340 1784483 := bstep (se 1 (by rfl) ⟨1338362, by rfl⟩ : syracuseStep 1784483 = 2676725) B2676725
theorem B1129153 : Blo 790340 1129153 := bstep (se 2 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 1129153 = 846865) B846865
theorem B6273733 : Blo 790340 6273733 := bstep (se 4 (by rfl) ⟨588162, by rfl⟩ : syracuseStep 6273733 = 1176325) B1176325
theorem B1129187 : Blo 790340 1129187 := bstep (se 1 (by rfl) ⟨846890, by rfl⟩ : syracuseStep 1129187 = 1693781) B1693781
theorem B2538211 : Blo 790340 2538211 := bstep (se 1 (by rfl) ⟨1903658, by rfl⟩ : syracuseStep 2538211 = 3807317) B3807317
theorem B2407153 : Blo 790340 2407153 := bstep (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) B1805365
theorem B4504355 : Blo 790340 4504355 := bstep (se 1 (by rfl) ⟨3378266, by rfl⟩ : syracuseStep 4504355 = 6756533) B6756533
theorem B2669489 : Blo 790340 2669489 := bstep (se 2 (by rfl) ⟨1001058, by rfl⟩ : syracuseStep 2669489 = 2002117) B2002117
theorem B1784753 : Blo 790340 1784753 := bstep (se 2 (by rfl) ⟨669282, by rfl⟩ : syracuseStep 1784753 = 1338565) B1338565
theorem B1784771 : Blo 790340 1784771 := bstep (se 1 (by rfl) ⟨1338578, by rfl⟩ : syracuseStep 1784771 = 2677157) B2677157
theorem B2407373 : Blo 790340 2407373 := bstep (se 3 (by rfl) ⟨451382, by rfl⟩ : syracuseStep 2407373 = 902765) B902765
theorem B1785041 : Blo 790340 1785041 := bstep (se 2 (by rfl) ⟨669390, by rfl⟩ : syracuseStep 1785041 = 1338781) B1338781
theorem B1785059 : Blo 790340 1785059 := bstep (se 1 (by rfl) ⟨1338794, by rfl⟩ : syracuseStep 1785059 = 2677589) B2677589
theorem B1129745 : Blo 790340 1129745 := bstep (se 2 (by rfl) ⟨423654, by rfl⟩ : syracuseStep 1129745 = 847309) B847309
theorem B1129825 : Blo 790340 1129825 := bstep (se 2 (by rfl) ⟨423684, by rfl⟩ : syracuseStep 1129825 = 847369) B847369
theorem B6438341 : Blo 790340 6438341 := bstep (se 4 (by rfl) ⟨603594, by rfl⟩ : syracuseStep 6438341 = 1207189) B1207189
theorem B2670029 : Blo 790340 2670029 := bstep (se 3 (by rfl) ⟨500630, by rfl⟩ : syracuseStep 2670029 = 1001261) B1001261
theorem B1785329 : Blo 790340 1785329 := bstep (se 2 (by rfl) ⟨669498, by rfl⟩ : syracuseStep 1785329 = 1338997) B1338997
theorem B966131 : Blo 790340 966131 := bstep (se 1 (by rfl) ⟨724598, by rfl⟩ : syracuseStep 966131 = 1449197) B1449197
theorem B2670083 : Blo 790340 2670083 := bstep (se 1 (by rfl) ⟨2002562, by rfl⟩ : syracuseStep 2670083 = 4005125) B4005125
theorem B1785347 : Blo 790340 1785347 := bstep (se 1 (by rfl) ⟨1339010, by rfl⟩ : syracuseStep 1785347 = 2678021) B2678021
theorem B5226053 : Blo 790340 5226053 := bstep (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) B979885
theorem B3391217 : Blo 790340 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B2670353 : Blo 790340 2670353 := bstep (se 2 (by rfl) ⟨1001382, by rfl⟩ : syracuseStep 2670353 = 2002765) B2002765
theorem B1785617 : Blo 790340 1785617 := bstep (se 2 (by rfl) ⟨669606, by rfl⟩ : syracuseStep 1785617 = 1339213) B1339213
theorem B1785635 : Blo 790340 1785635 := bstep (se 1 (by rfl) ⟨1339226, by rfl⟩ : syracuseStep 1785635 = 2678453) B2678453
theorem B2539313 : Blo 790340 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B4013873 : Blo 790340 4013873 := bstep (se 2 (by rfl) ⟨1505202, by rfl⟩ : syracuseStep 4013873 = 3010405) B3010405
theorem B2539441 : Blo 790340 2539441 := bstep (se 2 (by rfl) ⟨952290, by rfl⟩ : syracuseStep 2539441 = 1904581) B1904581
theorem B30883781 : Blo 790340 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B1785905 : Blo 790340 1785905 := bstep (se 2 (by rfl) ⟨669714, by rfl⟩ : syracuseStep 1785905 = 1339429) B1339429
theorem B1785923 : Blo 790340 1785923 := bstep (se 1 (by rfl) ⟨1339442, by rfl⟩ : syracuseStep 1785923 = 2678885) B2678885
theorem B1130611 : Blo 790340 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B1425539 : Blo 790340 1425539 := bstep (se 1 (by rfl) ⟨1069154, by rfl⟩ : syracuseStep 1425539 = 2138309) B2138309
theorem B901315 : Blo 790340 901315 := bstep (se 1 (by rfl) ⟨675986, by rfl⟩ : syracuseStep 901315 = 1351973) B1351973
theorem B2670893 : Blo 790340 2670893 := bstep (se 3 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 2670893 = 1001585) B1001585
theorem B1786193 : Blo 790340 1786193 := bstep (se 2 (by rfl) ⟨669822, by rfl⟩ : syracuseStep 1786193 = 1339645) B1339645
theorem B2670947 : Blo 790340 2670947 := bstep (se 1 (by rfl) ⟨2003210, by rfl⟩ : syracuseStep 2670947 = 4006421) B4006421
theorem B1786211 : Blo 790340 1786211 := bstep (se 1 (by rfl) ⟨1339658, by rfl⟩ : syracuseStep 1786211 = 2679317) B2679317
theorem B5718413 : Blo 790340 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B1688177 : Blo 790340 1688177 := bstep (se 2 (by rfl) ⟨633066, by rfl⟩ : syracuseStep 1688177 = 1266133) B1266133
theorem B2671217 : Blo 790340 2671217 := bstep (se 2 (by rfl) ⟨1001706, by rfl⟩ : syracuseStep 2671217 = 2003413) B2003413
theorem B1786481 : Blo 790340 1786481 := bstep (se 2 (by rfl) ⟨669930, by rfl⟩ : syracuseStep 1786481 = 1339861) B1339861
theorem B1786499 : Blo 790340 1786499 := bstep (se 1 (by rfl) ⟨1339874, by rfl⟩ : syracuseStep 1786499 = 2679749) B2679749
theorem B1426129 : Blo 790340 1426129 := bstep (se 2 (by rfl) ⟨534798, by rfl⟩ : syracuseStep 1426129 = 1069597) B1069597
theorem B2540429 : Blo 790340 2540429 := bstep (se 3 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 2540429 = 952661) B952661
theorem B1786769 : Blo 790340 1786769 := bstep (se 2 (by rfl) ⟨670038, by rfl⟩ : syracuseStep 1786769 = 1340077) B1340077
theorem B902035 : Blo 790340 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B1786787 : Blo 790340 1786787 := bstep (se 1 (by rfl) ⟨1340090, by rfl⟩ : syracuseStep 1786787 = 2680181) B2680181
theorem B3621809 : Blo 790340 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B1000451 : Blo 790340 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B2704433 : Blo 790340 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B2671757 : Blo 790340 2671757 := bstep (se 3 (by rfl) ⟨500954, by rfl⟩ : syracuseStep 2671757 = 1001909) B1001909
theorem B1787057 : Blo 790340 1787057 := bstep (se 2 (by rfl) ⟨670146, by rfl⟩ : syracuseStep 1787057 = 1340293) B1340293
theorem B2671811 : Blo 790340 2671811 := bstep (se 1 (by rfl) ⟨2003858, by rfl⟩ : syracuseStep 2671811 = 4007717) B4007717
theorem B1787075 : Blo 790340 1787075 := bstep (se 1 (by rfl) ⟨1340306, by rfl⟩ : syracuseStep 1787075 = 2680613) B2680613
theorem B4015331 : Blo 790340 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B1426691 : Blo 790340 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B4343203 : Blo 790340 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B2672081 : Blo 790340 2672081 := bstep (se 2 (by rfl) ⟨1002030, by rfl⟩ : syracuseStep 2672081 = 2004061) B2004061
theorem B1426915 : Blo 790340 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B4343473 : Blo 790340 4343473 := bstep (se 2 (by rfl) ⟨1628802, by rfl⟩ : syracuseStep 4343473 = 3257605) B3257605
theorem B1001155 : Blo 790340 1001155 := bstep (se 1 (by rfl) ⟨750866, by rfl⟩ : syracuseStep 1001155 = 1501733) B1501733
theorem B1001251 : Blo 790340 1001251 := bstep (se 1 (by rfl) ⟨750938, by rfl⟩ : syracuseStep 1001251 = 1501877) B1501877
theorem B7718755 : Blo 790340 7718755 := bstep (se 1 (by rfl) ⟨5789066, by rfl⟩ : syracuseStep 7718755 = 11578133) B11578133
theorem B1427377 : Blo 790340 1427377 := bstep (se 2 (by rfl) ⟨535266, by rfl⟩ : syracuseStep 1427377 = 1070533) B1070533
theorem B4507589 : Blo 790340 4507589 := bstep (se 4 (by rfl) ⟨422586, by rfl⟩ : syracuseStep 4507589 = 845173) B845173
theorem B2672621 : Blo 790340 2672621 := bstep (se 3 (by rfl) ⟨501116, by rfl⟩ : syracuseStep 2672621 = 1002233) B1002233
theorem B4016141 : Blo 790340 4016141 := bstep (se 3 (by rfl) ⟨753026, by rfl⟩ : syracuseStep 4016141 = 1506053) B1506053
theorem B2672675 : Blo 790340 2672675 := bstep (se 1 (by rfl) ⟨2004506, by rfl⟩ : syracuseStep 2672675 = 4009013) B4009013
theorem B2541773 : Blo 790340 2541773 := bstep (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) B953165
theorem B6113549 : Blo 790340 6113549 := bstep (se 3 (by rfl) ⟨1146290, by rfl⟩ : syracuseStep 6113549 = 2292581) B2292581
theorem B1001747 : Blo 790340 1001747 := bstep (se 1 (by rfl) ⟨751310, by rfl⟩ : syracuseStep 1001747 = 1502621) B1502621
theorem B2672945 : Blo 790340 2672945 := bstep (se 2 (by rfl) ⟨1002354, by rfl⟩ : syracuseStep 2672945 = 2004709) B2004709
theorem B4508045 : Blo 790340 4508045 := bstep (se 3 (by rfl) ⟨845258, by rfl⟩ : syracuseStep 4508045 = 1690517) B1690517
theorem B2673485 : Blo 790340 2673485 := bstep (se 3 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 2673485 = 1002557) B1002557
theorem B2673539 : Blo 790340 2673539 := bstep (se 1 (by rfl) ⟨2005154, by rfl⟩ : syracuseStep 2673539 = 4010309) B4010309
theorem B1002451 : Blo 790340 1002451 := bstep (se 1 (by rfl) ⟨751838, by rfl⟩ : syracuseStep 1002451 = 1503677) B1503677
theorem B1002547 : Blo 790340 1002547 := bstep (se 1 (by rfl) ⟨751910, by rfl⟩ : syracuseStep 1002547 = 1503821) B1503821
theorem B11586673 : Blo 790340 11586673 := bstep (se 2 (by rfl) ⟨4345002, by rfl⟩ : syracuseStep 11586673 = 8690005) B8690005
theorem B2673809 : Blo 790340 2673809 := bstep (se 2 (by rfl) ⟨1002678, by rfl⟩ : syracuseStep 2673809 = 2005357) B2005357
theorem B1690961 : Blo 790340 1690961 := bstep (se 2 (by rfl) ⟨634110, by rfl⟩ : syracuseStep 1690961 = 1268221) B1268221
theorem B3263921 : Blo 790340 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B1003043 : Blo 790340 1003043 := bstep (se 1 (by rfl) ⟨752282, by rfl⟩ : syracuseStep 1003043 = 1504565) B1504565
theorem B2674349 : Blo 790340 2674349 := bstep (se 3 (by rfl) ⟨501440, by rfl⟩ : syracuseStep 2674349 = 1002881) B1002881
theorem B2674403 : Blo 790340 2674403 := bstep (se 1 (by rfl) ⟨2005802, by rfl⟩ : syracuseStep 2674403 = 4011605) B4011605
theorem B2543363 : Blo 790340 2543363 := bstep (se 1 (by rfl) ⟨1907522, by rfl⟩ : syracuseStep 2543363 = 3815045) B3815045
theorem B2674673 : Blo 790340 2674673 := bstep (se 2 (by rfl) ⟨1003002, by rfl⟩ : syracuseStep 2674673 = 2006005) B2006005
theorem B3002417 : Blo 790340 3002417 := bstep (se 2 (by rfl) ⟨1125906, by rfl⟩ : syracuseStep 3002417 = 2251813) B2251813
theorem B6017165 : Blo 790340 6017165 := bstep (se 3 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 6017165 = 2256437) B2256437
theorem B1069283 : Blo 790340 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B1003747 : Blo 790340 1003747 := bstep (se 1 (by rfl) ⟨752810, by rfl⟩ : syracuseStep 1003747 = 1505621) B1505621
theorem B1003843 : Blo 790340 1003843 := bstep (se 1 (by rfl) ⟨752882, by rfl⟩ : syracuseStep 1003843 = 1505765) B1505765
theorem B17125829 : Blo 790340 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B2544131 : Blo 790340 2544131 := bstep (se 1 (by rfl) ⟨1908098, by rfl⟩ : syracuseStep 2544131 = 3816197) B3816197
theorem B2675213 : Blo 790340 2675213 := bstep (se 3 (by rfl) ⟨501602, by rfl⟩ : syracuseStep 2675213 = 1003205) B1003205
theorem B1430065 : Blo 790340 1430065 := bstep (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) B1072549
theorem B2675267 : Blo 790340 2675267 := bstep (se 1 (by rfl) ⟨2006450, by rfl⟩ : syracuseStep 2675267 = 4012901) B4012901
theorem B1004339 : Blo 790340 1004339 := bstep (se 1 (by rfl) ⟨753254, by rfl⟩ : syracuseStep 1004339 = 1506509) B1506509
theorem B2675537 : Blo 790340 2675537 := bstep (se 2 (by rfl) ⟨1003326, by rfl⟩ : syracuseStep 2675537 = 2006653) B2006653
theorem B4019057 : Blo 790340 4019057 := bstep (se 2 (by rfl) ⟨1507146, by rfl⟩ : syracuseStep 4019057 = 3014293) B3014293
theorem B2544529 : Blo 790340 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B2544643 : Blo 790340 2544643 := bstep (se 1 (by rfl) ⟨1908482, by rfl⟩ : syracuseStep 2544643 = 3816965) B3816965
theorem B2413795 : Blo 790340 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B4510961 : Blo 790340 4510961 := bstep (se 2 (by rfl) ⟨1691610, by rfl⟩ : syracuseStep 4510961 = 3383221) B3383221
theorem B2676077 : Blo 790340 2676077 := bstep (se 3 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 2676077 = 1003529) B1003529
theorem B2676131 : Blo 790340 2676131 := bstep (se 1 (by rfl) ⟨2007098, by rfl⟩ : syracuseStep 2676131 = 4014197) B4014197
theorem B1267139 : Blo 790340 1267139 := bstep (se 1 (by rfl) ⟨950354, by rfl⟩ : syracuseStep 1267139 = 1900709) B1900709
theorem B3003875 : Blo 790340 3003875 := bstep (se 1 (by rfl) ⟨2252906, by rfl⟩ : syracuseStep 3003875 = 4505813) B4505813
theorem B1005043 : Blo 790340 1005043 := bstep (se 1 (by rfl) ⟨753782, by rfl⟩ : syracuseStep 1005043 = 1507565) B1507565
theorem B1005139 : Blo 790340 1005139 := bstep (se 1 (by rfl) ⟨753854, by rfl⟩ : syracuseStep 1005139 = 1507709) B1507709
theorem B1201825 : Blo 790340 1201825 := bstep (se 2 (by rfl) ⟨450684, by rfl⟩ : syracuseStep 1201825 = 901369) B901369
theorem B1267363 : Blo 790340 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B2709169 : Blo 790340 2709169 := bstep (se 2 (by rfl) ⟨1015938, by rfl⟩ : syracuseStep 2709169 = 2031877) B2031877
theorem B2676401 : Blo 790340 2676401 := bstep (se 2 (by rfl) ⟨1003650, by rfl⟩ : syracuseStep 2676401 = 2007301) B2007301
theorem B1267427 : Blo 790340 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B2283299 : Blo 790340 2283299 := bstep (se 1 (by rfl) ⟨1712474, by rfl⟩ : syracuseStep 2283299 = 3424949) B3424949
theorem B1267555 : Blo 790340 1267555 := bstep (se 1 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 1267555 = 1901333) B1901333
theorem B2316269 : Blo 790340 2316269 := bstep (se 3 (by rfl) ⟨434300, by rfl⟩ : syracuseStep 2316269 = 868601) B868601
theorem B2676941 : Blo 790340 2676941 := bstep (se 3 (by rfl) ⟨501926, by rfl⟩ : syracuseStep 2676941 = 1003853) B1003853
theorem B1202435 : Blo 790340 1202435 := bstep (se 1 (by rfl) ⟨901826, by rfl⟩ : syracuseStep 1202435 = 1803653) B1803653
theorem B2676995 : Blo 790340 2676995 := bstep (se 1 (by rfl) ⟨2007746, by rfl⟩ : syracuseStep 2676995 = 4015493) B4015493
theorem B4020515 : Blo 790340 4020515 := bstep (se 1 (by rfl) ⟨3015386, by rfl⟩ : syracuseStep 4020515 = 6030773) B6030773
theorem B3004877 : Blo 790340 3004877 := bstep (se 3 (by rfl) ⟨563414, by rfl⟩ : syracuseStep 3004877 = 1126829) B1126829
theorem B1071571 : Blo 790340 1071571 := bstep (se 1 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 1071571 = 1607357) B1607357
theorem B2677265 : Blo 790340 2677265 := bstep (se 2 (by rfl) ⟨1003974, by rfl⟩ : syracuseStep 2677265 = 2007949) B2007949
theorem B1333793 : Blo 790340 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B1268273 : Blo 790340 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B3431011 : Blo 790340 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B1333921 : Blo 790340 1333921 := bstep (se 2 (by rfl) ⟨500220, by rfl⟩ : syracuseStep 1333921 = 1000441) B1000441
theorem B4512419 : Blo 790340 4512419 := bstep (se 1 (by rfl) ⟨3384314, by rfl⟩ : syracuseStep 4512419 = 6768629) B6768629
theorem B1694371 : Blo 790340 1694371 := bstep (se 1 (by rfl) ⟨1270778, by rfl⟩ : syracuseStep 1694371 = 2541557) B2541557
theorem B1268401 : Blo 790340 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B1333955 : Blo 790340 1333955 := bstep (se 1 (by rfl) ⟨1000466, by rfl⟩ : syracuseStep 1333955 = 2000933) B2000933
theorem B5069603 : Blo 790340 5069603 := bstep (se 1 (by rfl) ⟨3802202, by rfl⟩ : syracuseStep 5069603 = 7604405) B7604405
theorem B1202993 : Blo 790340 1202993 := bstep (se 2 (by rfl) ⟨451122, by rfl⟩ : syracuseStep 1202993 = 902245) B902245
theorem B1334083 : Blo 790340 1334083 := bstep (se 1 (by rfl) ⟨1000562, by rfl⟩ : syracuseStep 1334083 = 2001125) B2001125
theorem B2251597 : Blo 790340 2251597 := bstep (se 3 (by rfl) ⟨422174, by rfl⟩ : syracuseStep 2251597 = 844349) B844349
theorem B1334225 : Blo 790340 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B6020081 : Blo 790340 6020081 := bstep (se 2 (by rfl) ⟨2257530, by rfl⟩ : syracuseStep 6020081 = 4515061) B4515061
theorem B2677805 : Blo 790340 2677805 := bstep (se 3 (by rfl) ⟨502088, by rfl⟩ : syracuseStep 2677805 = 1004177) B1004177
theorem B1268785 : Blo 790340 1268785 := bstep (se 2 (by rfl) ⟨475794, by rfl⟩ : syracuseStep 1268785 = 951589) B951589
theorem B4021325 : Blo 790340 4021325 := bstep (se 3 (by rfl) ⟨753998, by rfl⟩ : syracuseStep 4021325 = 1507997) B1507997
theorem B1334353 : Blo 790340 1334353 := bstep (se 2 (by rfl) ⟨500382, by rfl⟩ : syracuseStep 1334353 = 1000765) B1000765
theorem B2677859 : Blo 790340 2677859 := bstep (se 1 (by rfl) ⟨2008394, by rfl⟩ : syracuseStep 2677859 = 4016789) B4016789
theorem B1334387 : Blo 790340 1334387 := bstep (se 1 (by rfl) ⟨1000790, by rfl⟩ : syracuseStep 1334387 = 2001581) B2001581
theorem B1334515 : Blo 790340 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B6774029 : Blo 790340 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B1269041 : Blo 790340 1269041 := bstep (se 2 (by rfl) ⟨475890, by rfl⟩ : syracuseStep 1269041 = 951781) B951781
theorem B2678129 : Blo 790340 2678129 := bstep (se 2 (by rfl) ⟨1004298, by rfl⟩ : syracuseStep 2678129 = 2008597) B2008597
theorem B1334657 : Blo 790340 1334657 := bstep (se 2 (by rfl) ⟨500496, by rfl⟩ : syracuseStep 1334657 = 1000993) B1000993
theorem B1334785 : Blo 790340 1334785 := bstep (se 2 (by rfl) ⟨500544, by rfl⟩ : syracuseStep 1334785 = 1001089) B1001089
theorem B1334819 : Blo 790340 1334819 := bstep (se 1 (by rfl) ⟨1001114, by rfl⟩ : syracuseStep 1334819 = 2002229) B2002229
theorem B4513421 : Blo 790340 4513421 := bstep (se 3 (by rfl) ⟨846266, by rfl⟩ : syracuseStep 4513421 = 1692533) B1692533
theorem B1334947 : Blo 790340 1334947 := bstep (se 1 (by rfl) ⟨1001210, by rfl⟩ : syracuseStep 1334947 = 2002421) B2002421
theorem B1335089 : Blo 790340 1335089 := bstep (se 2 (by rfl) ⟨500658, by rfl⟩ : syracuseStep 1335089 = 1001317) B1001317
theorem B2678669 : Blo 790340 2678669 := bstep (se 3 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 2678669 = 1004501) B1004501
theorem B1335217 : Blo 790340 1335217 := bstep (se 2 (by rfl) ⟨500706, by rfl⟩ : syracuseStep 1335217 = 1001413) B1001413
theorem B2678723 : Blo 790340 2678723 := bstep (se 1 (by rfl) ⟨2009042, by rfl⟩ : syracuseStep 2678723 = 4018085) B4018085
theorem B1335251 : Blo 790340 1335251 := bstep (se 1 (by rfl) ⟨1001438, by rfl⟩ : syracuseStep 1335251 = 2002877) B2002877
theorem B5070833 : Blo 790340 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B1335379 : Blo 790340 1335379 := bstep (se 1 (by rfl) ⟨1001534, by rfl⟩ : syracuseStep 1335379 = 2003069) B2003069
theorem B9003149 : Blo 790340 9003149 := bstep (se 3 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 9003149 = 3376181) B3376181
theorem B2678993 : Blo 790340 2678993 := bstep (se 2 (by rfl) ⟨1004622, by rfl⟩ : syracuseStep 2678993 = 2009245) B2009245
theorem B1335521 : Blo 790340 1335521 := bstep (se 2 (by rfl) ⟨500820, by rfl⟩ : syracuseStep 1335521 = 1001641) B1001641
theorem B1204465 : Blo 790340 1204465 := bstep (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) B903349
theorem B1335649 : Blo 790340 1335649 := bstep (se 2 (by rfl) ⟨500868, by rfl⟩ : syracuseStep 1335649 = 1001737) B1001737
theorem B1335683 : Blo 790340 1335683 := bstep (se 1 (by rfl) ⟨1001762, by rfl⟩ : syracuseStep 1335683 = 2003525) B2003525
theorem B2712017 : Blo 790340 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B4284899 : Blo 790340 4284899 := bstep (se 1 (by rfl) ⟨3213674, by rfl⟩ : syracuseStep 4284899 = 6427349) B6427349
theorem B1696241 : Blo 790340 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B1335811 : Blo 790340 1335811 := bstep (se 1 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 1335811 = 2003717) B2003717
theorem B3006989 : Blo 790340 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B2253329 : Blo 790340 2253329 := bstep (se 2 (by rfl) ⟨844998, by rfl⟩ : syracuseStep 2253329 = 1689997) B1689997
theorem B844387 : Blo 790340 844387 := bstep (se 1 (by rfl) ⟨633290, by rfl⟩ : syracuseStep 844387 = 1266581) B1266581
theorem B1335953 : Blo 790340 1335953 := bstep (se 2 (by rfl) ⟨500982, by rfl⟩ : syracuseStep 1335953 = 1001965) B1001965
theorem B1270451 : Blo 790340 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B2253521 : Blo 790340 2253521 := bstep (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) B1690141
theorem B2679533 : Blo 790340 2679533 := bstep (se 3 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 2679533 = 1004825) B1004825
theorem B2712305 : Blo 790340 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B1336081 : Blo 790340 1336081 := bstep (se 2 (by rfl) ⟨501030, by rfl⟩ : syracuseStep 1336081 = 1002061) B1002061
theorem B2679587 : Blo 790340 2679587 := bstep (se 1 (by rfl) ⟨2009690, by rfl⟩ : syracuseStep 2679587 = 4019381) B4019381
theorem B1336115 : Blo 790340 1336115 := bstep (se 1 (by rfl) ⟨1002086, by rfl⟩ : syracuseStep 1336115 = 2004173) B2004173
theorem B1336243 : Blo 790340 1336243 := bstep (se 1 (by rfl) ⟨1002182, by rfl⟩ : syracuseStep 1336243 = 2004365) B2004365
theorem B2679857 : Blo 790340 2679857 := bstep (se 2 (by rfl) ⟨1004946, by rfl⟩ : syracuseStep 2679857 = 2009893) B2009893
theorem B1336385 : Blo 790340 1336385 := bstep (se 2 (by rfl) ⟨501144, by rfl⟩ : syracuseStep 1336385 = 1002289) B1002289
theorem B1336513 : Blo 790340 1336513 := bstep (se 2 (by rfl) ⟨501192, by rfl⟩ : syracuseStep 1336513 = 1002385) B1002385
theorem B12838085 : Blo 790340 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B1336547 : Blo 790340 1336547 := bstep (se 1 (by rfl) ⟨1002410, by rfl⟩ : syracuseStep 1336547 = 2004821) B2004821
theorem B1500419 : Blo 790340 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B3007793 : Blo 790340 3007793 := bstep (se 2 (by rfl) ⟨1127922, by rfl⟩ : syracuseStep 3007793 = 2255845) B2255845
theorem B1336675 : Blo 790340 1336675 := bstep (se 1 (by rfl) ⟨1002506, by rfl⟩ : syracuseStep 1336675 = 2005013) B2005013
theorem B3204593 : Blo 790340 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B1336817 : Blo 790340 1336817 := bstep (se 2 (by rfl) ⟨501306, by rfl⟩ : syracuseStep 1336817 = 1002613) B1002613
theorem B1271297 : Blo 790340 1271297 := bstep (se 2 (by rfl) ⟨476736, by rfl⟩ : syracuseStep 1271297 = 953473) B953473
theorem B1500707 : Blo 790340 1500707 := bstep (se 1 (by rfl) ⟨1125530, by rfl⟩ : syracuseStep 1500707 = 2251061) B2251061
theorem B2680397 : Blo 790340 2680397 := bstep (se 3 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 2680397 = 1005149) B1005149
theorem B6776419 : Blo 790340 6776419 := bstep (se 1 (by rfl) ⟨5082314, by rfl⟩ : syracuseStep 6776419 = 10164629) B10164629
theorem B1336945 : Blo 790340 1336945 := bstep (se 2 (by rfl) ⟨501354, by rfl⟩ : syracuseStep 1336945 = 1002709) B1002709
theorem B2680451 : Blo 790340 2680451 := bstep (se 1 (by rfl) ⟨2010338, by rfl⟩ : syracuseStep 2680451 = 4020677) B4020677
theorem B1336979 : Blo 790340 1336979 := bstep (se 1 (by rfl) ⟨1002734, by rfl⟩ : syracuseStep 1336979 = 2005469) B2005469
theorem B2254513 : Blo 790340 2254513 := bstep (se 2 (by rfl) ⟨845442, by rfl⟩ : syracuseStep 2254513 = 1690885) B1690885
theorem B4056803 : Blo 790340 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B4056817 : Blo 790340 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1337107 : Blo 790340 1337107 := bstep (se 1 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 1337107 = 2005661) B2005661
theorem B2680721 : Blo 790340 2680721 := bstep (se 2 (by rfl) ⟨1005270, by rfl⟩ : syracuseStep 2680721 = 2010541) B2010541
theorem B1337249 : Blo 790340 1337249 := bstep (se 2 (by rfl) ⟨501468, by rfl⟩ : syracuseStep 1337249 = 1002937) B1002937
theorem B2254787 : Blo 790340 2254787 := bstep (se 1 (by rfl) ⟨1691090, by rfl⟩ : syracuseStep 2254787 = 3382181) B3382181
theorem B3008461 : Blo 790340 3008461 := bstep (se 3 (by rfl) ⟨564086, by rfl⟩ : syracuseStep 3008461 = 1128173) B1128173
theorem B1271809 : Blo 790340 1271809 := bstep (se 2 (by rfl) ⟨476928, by rfl⟩ : syracuseStep 1271809 = 953857) B953857
theorem B1337377 : Blo 790340 1337377 := bstep (se 2 (by rfl) ⟨501516, by rfl⟩ : syracuseStep 1337377 = 1003033) B1003033
theorem B1337411 : Blo 790340 1337411 := bstep (se 1 (by rfl) ⟨1003058, by rfl⟩ : syracuseStep 1337411 = 2006117) B2006117
theorem B2254979 : Blo 790340 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B1337539 : Blo 790340 1337539 := bstep (se 1 (by rfl) ⟨1003154, by rfl⟩ : syracuseStep 1337539 = 2006309) B2006309
theorem B1337681 : Blo 790340 1337681 := bstep (se 2 (by rfl) ⟨501630, by rfl⟩ : syracuseStep 1337681 = 1003261) B1003261
theorem B5073293 : Blo 790340 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B1501649 : Blo 790340 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B1337809 : Blo 790340 1337809 := bstep (se 2 (by rfl) ⟨501678, by rfl⟩ : syracuseStep 1337809 = 1003357) B1003357
theorem B4516337 : Blo 790340 4516337 := bstep (se 2 (by rfl) ⟨1693626, by rfl⟩ : syracuseStep 4516337 = 3387253) B3387253
theorem B1337843 : Blo 790340 1337843 := bstep (se 1 (by rfl) ⟨1003382, by rfl⟩ : syracuseStep 1337843 = 2006765) B2006765
theorem B1337971 : Blo 790340 1337971 := bstep (se 1 (by rfl) ⟨1003478, by rfl⟩ : syracuseStep 1337971 = 2006957) B2006957
theorem B3009251 : Blo 790340 3009251 := bstep (se 1 (by rfl) ⟨2256938, by rfl⟩ : syracuseStep 3009251 = 4513877) B4513877
theorem B1338113 : Blo 790340 1338113 := bstep (se 2 (by rfl) ⟨501792, by rfl⟩ : syracuseStep 1338113 = 1003585) B1003585
theorem B3205937 : Blo 790340 3205937 := bstep (se 2 (by rfl) ⟨1202226, by rfl⟩ : syracuseStep 3205937 = 2404453) B2404453
theorem B1338241 : Blo 790340 1338241 := bstep (se 2 (by rfl) ⟨501840, by rfl⟩ : syracuseStep 1338241 = 1003681) B1003681
theorem B1338275 : Blo 790340 1338275 := bstep (se 1 (by rfl) ⟨1003706, by rfl⟩ : syracuseStep 1338275 = 2007413) B2007413
theorem B2255789 : Blo 790340 2255789 := bstep (se 3 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 2255789 = 845921) B845921
theorem B9006065 : Blo 790340 9006065 := bstep (se 2 (by rfl) ⟨3377274, by rfl⟩ : syracuseStep 9006065 = 6754549) B6754549
theorem B1338403 : Blo 790340 1338403 := bstep (se 1 (by rfl) ⟨1003802, by rfl⟩ : syracuseStep 1338403 = 2007605) B2007605
theorem B2255971 : Blo 790340 2255971 := bstep (se 1 (by rfl) ⟨1691978, by rfl⟩ : syracuseStep 2255971 = 3383957) B3383957
theorem B1338545 : Blo 790340 1338545 := bstep (se 2 (by rfl) ⟨501954, by rfl⟩ : syracuseStep 1338545 = 1003909) B1003909
theorem B847027 : Blo 790340 847027 := bstep (se 1 (by rfl) ⟨635270, by rfl⟩ : syracuseStep 847027 = 1270541) B1270541
theorem B1338673 : Blo 790340 1338673 := bstep (se 2 (by rfl) ⟨502002, by rfl⟩ : syracuseStep 1338673 = 1004005) B1004005
theorem B1502545 : Blo 790340 1502545 := bstep (se 2 (by rfl) ⟨563454, by rfl⟩ : syracuseStep 1502545 = 1126909) B1126909
theorem B1338707 : Blo 790340 1338707 := bstep (se 1 (by rfl) ⟨1004030, by rfl⟩ : syracuseStep 1338707 = 2008061) B2008061
theorem B3009905 : Blo 790340 3009905 := bstep (se 2 (by rfl) ⟨1128714, by rfl⟩ : syracuseStep 3009905 = 2257429) B2257429
theorem B1142147 : Blo 790340 1142147 := bstep (se 1 (by rfl) ⟨856610, by rfl⟩ : syracuseStep 1142147 = 1713221) B1713221
theorem B814483 : Blo 790340 814483 := bstep (se 1 (by rfl) ⟨610862, by rfl⟩ : syracuseStep 814483 = 1221725) B1221725
theorem B1338835 : Blo 790340 1338835 := bstep (se 1 (by rfl) ⟨1004126, by rfl⟩ : syracuseStep 1338835 = 2008253) B2008253
theorem B1502705 : Blo 790340 1502705 := bstep (se 2 (by rfl) ⟨563514, by rfl⟩ : syracuseStep 1502705 = 1127029) B1127029
theorem B2256461 : Blo 790340 2256461 := bstep (se 3 (by rfl) ⟨423086, by rfl⟩ : syracuseStep 2256461 = 846173) B846173
theorem B1338977 : Blo 790340 1338977 := bstep (se 2 (by rfl) ⟨502116, by rfl⟩ : syracuseStep 1338977 = 1004233) B1004233
theorem B847459 : Blo 790340 847459 := bstep (se 1 (by rfl) ⟨635594, by rfl⟩ : syracuseStep 847459 = 1271189) B1271189
theorem B1339105 : Blo 790340 1339105 := bstep (se 2 (by rfl) ⟨502164, by rfl⟩ : syracuseStep 1339105 = 1004329) B1004329
theorem B1339139 : Blo 790340 1339139 := bstep (se 1 (by rfl) ⟨1004354, by rfl⟩ : syracuseStep 1339139 = 2008709) B2008709
theorem B2715491 : Blo 790340 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B1503107 : Blo 790340 1503107 := bstep (se 1 (by rfl) ⟨1127330, by rfl⟩ : syracuseStep 1503107 = 2254661) B2254661
theorem B1339267 : Blo 790340 1339267 := bstep (se 1 (by rfl) ⟨1004450, by rfl⟩ : syracuseStep 1339267 = 2008901) B2008901
theorem B56323981 : Blo 790340 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B2322317 : Blo 790340 2322317 := bstep (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) B870869
theorem B4517795 : Blo 790340 4517795 := bstep (se 1 (by rfl) ⟨3388346, by rfl⟩ : syracuseStep 4517795 = 6776693) B6776693
theorem B2715601 : Blo 790340 2715601 := bstep (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) B2036701
theorem B1339409 : Blo 790340 1339409 := bstep (se 2 (by rfl) ⟨502278, by rfl⟩ : syracuseStep 1339409 = 1004557) B1004557
theorem B4059277 : Blo 790340 4059277 := bstep (se 3 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 4059277 = 1522229) B1522229
theorem B1339537 : Blo 790340 1339537 := bstep (se 2 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 1339537 = 1004653) B1004653
theorem B1929379 : Blo 790340 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B1339571 : Blo 790340 1339571 := bstep (se 1 (by rfl) ⟨1004678, by rfl⟩ : syracuseStep 1339571 = 2009357) B2009357
theorem B1339699 : Blo 790340 1339699 := bstep (se 1 (by rfl) ⟨1004774, by rfl⟩ : syracuseStep 1339699 = 2009549) B2009549
theorem B5140849 : Blo 790340 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B1339841 : Blo 790340 1339841 := bstep (se 2 (by rfl) ⟨502440, by rfl⟩ : syracuseStep 1339841 = 1004881) B1004881
theorem B17134051 : Blo 790340 17134051 := bstep (se 1 (by rfl) ⟨12850538, by rfl⟩ : syracuseStep 17134051 = 25701077) B25701077
theorem B1339969 : Blo 790340 1339969 := bstep (se 2 (by rfl) ⟨502488, by rfl⟩ : syracuseStep 1339969 = 1004977) B1004977
theorem B1340003 : Blo 790340 1340003 := bstep (se 1 (by rfl) ⟨1005002, by rfl⟩ : syracuseStep 1340003 = 2010005) B2010005
theorem B1962641 : Blo 790340 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B14676677 : Blo 790340 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B1340131 : Blo 790340 1340131 := bstep (se 1 (by rfl) ⟨1005098, by rfl⟩ : syracuseStep 1340131 = 2010197) B2010197
theorem B2257645 : Blo 790340 2257645 := bstep (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) B846617
theorem B1504003 : Blo 790340 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B3011363 : Blo 790340 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B3011377 : Blo 790340 3011377 := bstep (se 2 (by rfl) ⟨1129266, by rfl⟩ : syracuseStep 3011377 = 2258533) B2258533
theorem B1340273 : Blo 790340 1340273 := bstep (se 2 (by rfl) ⟨502602, by rfl⟩ : syracuseStep 1340273 = 1005205) B1005205
theorem B1504163 : Blo 790340 1504163 := bstep (se 1 (by rfl) ⟨1128122, by rfl⟩ : syracuseStep 1504163 = 2256245) B2256245
theorem B1340401 : Blo 790340 1340401 := bstep (se 2 (by rfl) ⟨502650, by rfl⟩ : syracuseStep 1340401 = 1005301) B1005301
theorem B1340435 : Blo 790340 1340435 := bstep (se 1 (by rfl) ⟨1005326, by rfl⟩ : syracuseStep 1340435 = 2010653) B2010653
theorem B2290733 : Blo 790340 2290733 := bstep (se 3 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 2290733 = 859025) B859025
theorem B2061571 : Blo 790340 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B2029169 : Blo 790340 2029169 := bstep (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) B1521877
theorem B2258705 : Blo 790340 2258705 := bstep (se 2 (by rfl) ⟨847014, by rfl⟩ : syracuseStep 2258705 = 1694029) B1694029
theorem B11401073 : Blo 790340 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B4585349 : Blo 790340 4585349 := bstep (se 4 (by rfl) ⟨429876, by rfl⟩ : syracuseStep 4585349 = 859753) B859753
theorem B1505233 : Blo 790340 1505233 := bstep (se 2 (by rfl) ⟨564462, by rfl⟩ : syracuseStep 1505233 = 1128925) B1128925
theorem B3012835 : Blo 790340 3012835 := bstep (se 1 (by rfl) ⟨2259626, by rfl⟩ : syracuseStep 3012835 = 4519253) B4519253
theorem B2259377 : Blo 790340 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B4291213 : Blo 790340 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B1374995 : Blo 790340 1374995 := bstep (se 1 (by rfl) ⟨1031246, by rfl⟩ : syracuseStep 1374995 = 2062493) B2062493
theorem B1506289 : Blo 790340 1506289 := bstep (se 2 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 1506289 = 1129717) B1129717
theorem B2260163 : Blo 790340 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1375507 : Blo 790340 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B1604963 : Blo 790340 1604963 := bstep (se 1 (by rfl) ⟨1203722, by rfl⟩ : syracuseStep 1604963 = 2407445) B2407445
theorem B1506691 : Blo 790340 1506691 := bstep (se 1 (by rfl) ⟨1130018, by rfl⟩ : syracuseStep 1506691 = 2260037) B2260037
theorem B1506737 : Blo 790340 1506737 := bstep (se 2 (by rfl) ⟨565026, by rfl⟩ : syracuseStep 1506737 = 1130053) B1130053
theorem B949763 : Blo 790340 949763 := bstep (se 1 (by rfl) ⟨712322, by rfl⟩ : syracuseStep 949763 = 1424645) B1424645
theorem B2260493 : Blo 790340 2260493 := bstep (se 3 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 2260493 = 847685) B847685
theorem B2260561 : Blo 790340 2260561 := bstep (se 2 (by rfl) ⟨847710, by rfl⟩ : syracuseStep 2260561 = 1695421) B1695421
theorem B1507025 : Blo 790340 1507025 := bstep (se 2 (by rfl) ⟨565134, by rfl⟩ : syracuseStep 1507025 = 1130269) B1130269
theorem B2260835 : Blo 790340 2260835 := bstep (se 1 (by rfl) ⟨1695626, by rfl⟩ : syracuseStep 2260835 = 3391253) B3391253
theorem B2031569 : Blo 790340 2031569 := bstep (se 2 (by rfl) ⟨761838, by rfl⟩ : syracuseStep 2031569 = 1523677) B1523677
theorem B950243 : Blo 790340 950243 := bstep (se 1 (by rfl) ⟨712682, by rfl⟩ : syracuseStep 950243 = 1425365) B1425365
theorem B13533155 : Blo 790340 13533155 := bstep (se 1 (by rfl) ⟨10149866, by rfl⟩ : syracuseStep 13533155 = 20299733) B20299733
theorem B3670039 : Blo 790340 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B950359 : Blo 790340 950359 := bstep (se 1 (by rfl) ⟨712769, by rfl⟩ : syracuseStep 950359 = 1425539) B1425539
theorem B1507481 : Blo 790340 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B1605953 : Blo 790340 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B17170805 : Blo 790340 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B1507891 : Blo 790340 1507891 := bstep (se 1 (by rfl) ⟨1130918, by rfl⟩ : syracuseStep 1507891 = 2261837) B2261837
theorem B2851421 : Blo 790340 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B3015569 : Blo 790340 3015569 := bstep (se 2 (by rfl) ⟨1130838, by rfl⟩ : syracuseStep 3015569 = 2261677) B2261677
theorem B2851985 : Blo 790340 2851985 := bstep (se 2 (by rfl) ⟨1069494, by rfl⟩ : syracuseStep 2851985 = 2138989) B2138989
theorem B4523309 : Blo 790340 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B5409089 : Blo 790340 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B10291673 : Blo 790340 10291673 := bstep (se 2 (by rfl) ⟨3859377, by rfl⟩ : syracuseStep 10291673 = 7718755) B7718755
theorem B1903169 : Blo 790340 1903169 := bstep (se 2 (by rfl) ⟨713688, by rfl⟩ : syracuseStep 1903169 = 1427377) B1427377
theorem B7604867 : Blo 790340 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B2001611 : Blo 790340 2001611 := bstep (se 1 (by rfl) ⟨1501208, by rfl⟩ : syracuseStep 2001611 = 3002417) B3002417
theorem B7211821 : Blo 790340 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B36637717 : Blo 790340 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B3607811 : Blo 790340 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B3804509 : Blo 790340 3804509 := bstep (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) B1426691
theorem B1904023 : Blo 790340 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B5082725 : Blo 790340 5082725 := bstep (se 4 (by rfl) ⟨476505, by rfl⟩ : syracuseStep 5082725 = 953011) B953011
theorem B2002583 : Blo 790340 2002583 := bstep (se 1 (by rfl) ⟨1501937, by rfl⟩ : syracuseStep 2002583 = 3003875) B3003875
theorem B1806041 : Blo 790340 1806041 := bstep (se 2 (by rfl) ⟨677265, by rfl⟩ : syracuseStep 1806041 = 1354531) B1354531
theorem B7606021 : Blo 790340 7606021 := bstep (se 4 (by rfl) ⟨713064, by rfl⟩ : syracuseStep 7606021 = 1426129) B1426129
theorem B790347 : Blo 790340 790347 := bstep (se 1 (by rfl) ⟨592760, by rfl⟩ : syracuseStep 790347 = 1185521) B1185521
theorem B790359 : Blo 790340 790359 := bstep (se 1 (by rfl) ⟨592769, by rfl⟩ : syracuseStep 790359 = 1185539) B1185539
theorem B790379 : Blo 790340 790379 := bstep (se 1 (by rfl) ⟨592784, by rfl⟩ : syracuseStep 790379 = 1185569) B1185569
theorem B790391 : Blo 790340 790391 := bstep (se 1 (by rfl) ⟨592793, by rfl⟩ : syracuseStep 790391 = 1185587) B1185587
theorem B790411 : Blo 790340 790411 := bstep (se 1 (by rfl) ⟨592808, by rfl⟩ : syracuseStep 790411 = 1185617) B1185617
theorem B790423 : Blo 790340 790423 := bstep (se 1 (by rfl) ⟨592817, by rfl⟩ : syracuseStep 790423 = 1185635) B1185635
theorem B790443 : Blo 790340 790443 := bstep (se 1 (by rfl) ⟨592832, by rfl⟩ : syracuseStep 790443 = 1185665) B1185665
theorem B790455 : Blo 790340 790455 := bstep (se 1 (by rfl) ⟨592841, by rfl⟩ : syracuseStep 790455 = 1185683) B1185683
theorem B790475 : Blo 790340 790475 := bstep (se 1 (by rfl) ⟨592856, by rfl⟩ : syracuseStep 790475 = 1185713) B1185713
theorem B790487 : Blo 790340 790487 := bstep (se 1 (by rfl) ⟨592865, by rfl⟩ : syracuseStep 790487 = 1185731) B1185731
theorem B790507 : Blo 790340 790507 := bstep (se 1 (by rfl) ⟨592880, by rfl⟩ : syracuseStep 790507 = 1185761) B1185761
theorem B1544179 : Blo 790340 1544179 := bstep (se 1 (by rfl) ⟨1158134, by rfl⟩ : syracuseStep 1544179 = 2316269) B2316269
theorem B790519 : Blo 790340 790519 := bstep (se 1 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 790519 = 1185779) B1185779
theorem B790539 : Blo 790340 790539 := bstep (se 1 (by rfl) ⟨592904, by rfl⟩ : syracuseStep 790539 = 1185809) B1185809
theorem B790551 : Blo 790340 790551 := bstep (se 1 (by rfl) ⟨592913, by rfl⟩ : syracuseStep 790551 = 1185827) B1185827
theorem B790571 : Blo 790340 790571 := bstep (se 1 (by rfl) ⟨592928, by rfl⟩ : syracuseStep 790571 = 1185857) B1185857
theorem B790583 : Blo 790340 790583 := bstep (se 1 (by rfl) ⟨592937, by rfl⟩ : syracuseStep 790583 = 1185875) B1185875
theorem B790603 : Blo 790340 790603 := bstep (se 1 (by rfl) ⟨592952, by rfl⟩ : syracuseStep 790603 = 1185905) B1185905
theorem B790615 : Blo 790340 790615 := bstep (se 1 (by rfl) ⟨592961, by rfl⟩ : syracuseStep 790615 = 1185923) B1185923
theorem B4001885 : Blo 790340 4001885 := bstep (se 3 (by rfl) ⟨750353, by rfl⟩ : syracuseStep 4001885 = 1500707) B1500707
theorem B790635 : Blo 790340 790635 := bstep (se 1 (by rfl) ⟨592976, by rfl⟩ : syracuseStep 790635 = 1185953) B1185953
theorem B790647 : Blo 790340 790647 := bstep (se 1 (by rfl) ⟨592985, by rfl⟩ : syracuseStep 790647 = 1185971) B1185971
theorem B790667 : Blo 790340 790667 := bstep (se 1 (by rfl) ⟨593000, by rfl⟩ : syracuseStep 790667 = 1186001) B1186001
theorem B790679 : Blo 790340 790679 := bstep (se 1 (by rfl) ⟨593009, by rfl⟩ : syracuseStep 790679 = 1186019) B1186019
theorem B17109143 : Blo 790340 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B790699 : Blo 790340 790699 := bstep (se 1 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 790699 = 1186049) B1186049
theorem B790711 : Blo 790340 790711 := bstep (se 1 (by rfl) ⟨593033, by rfl⟩ : syracuseStep 790711 = 1186067) B1186067
theorem B790731 : Blo 790340 790731 := bstep (se 1 (by rfl) ⟨593048, by rfl⟩ : syracuseStep 790731 = 1186097) B1186097
theorem B790743 : Blo 790340 790743 := bstep (se 1 (by rfl) ⟨593057, by rfl⟩ : syracuseStep 790743 = 1186115) B1186115
theorem B790763 : Blo 790340 790763 := bstep (se 1 (by rfl) ⟨593072, by rfl⟩ : syracuseStep 790763 = 1186145) B1186145
theorem B790775 : Blo 790340 790775 := bstep (se 1 (by rfl) ⟨593081, by rfl⟩ : syracuseStep 790775 = 1186163) B1186163
theorem B790795 : Blo 790340 790795 := bstep (se 1 (by rfl) ⟨593096, by rfl⟩ : syracuseStep 790795 = 1186193) B1186193
theorem B790807 : Blo 790340 790807 := bstep (se 1 (by rfl) ⟨593105, by rfl⟩ : syracuseStep 790807 = 1186211) B1186211
theorem B790827 : Blo 790340 790827 := bstep (se 1 (by rfl) ⟨593120, by rfl⟩ : syracuseStep 790827 = 1186241) B1186241
theorem B5411117 : Blo 790340 5411117 := bstep (se 3 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 5411117 = 2029169) B2029169
theorem B2003251 : Blo 790340 2003251 := bstep (se 1 (by rfl) ⟨1502438, by rfl⟩ : syracuseStep 2003251 = 3004877) B3004877
theorem B790839 : Blo 790340 790839 := bstep (se 1 (by rfl) ⟨593129, by rfl⟩ : syracuseStep 790839 = 1186259) B1186259
theorem B790859 : Blo 790340 790859 := bstep (se 1 (by rfl) ⟨593144, by rfl⟩ : syracuseStep 790859 = 1186289) B1186289
theorem B790871 : Blo 790340 790871 := bstep (se 1 (by rfl) ⟨593153, by rfl⟩ : syracuseStep 790871 = 1186307) B1186307
theorem B889195 : Blo 790340 889195 := bstep (se 1 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 889195 = 1333793) B1333793
theorem B790891 : Blo 790340 790891 := bstep (se 1 (by rfl) ⟨593168, by rfl⟩ : syracuseStep 790891 = 1186337) B1186337
theorem B790903 : Blo 790340 790903 := bstep (se 1 (by rfl) ⟨593177, by rfl⟩ : syracuseStep 790903 = 1186355) B1186355
theorem B790923 : Blo 790340 790923 := bstep (se 1 (by rfl) ⟨593192, by rfl⟩ : syracuseStep 790923 = 1186385) B1186385
theorem B790935 : Blo 790340 790935 := bstep (se 1 (by rfl) ⟨593201, by rfl⟩ : syracuseStep 790935 = 1186403) B1186403
theorem B790955 : Blo 790340 790955 := bstep (se 1 (by rfl) ⟨593216, by rfl⟩ : syracuseStep 790955 = 1186433) B1186433
theorem B790967 : Blo 790340 790967 := bstep (se 1 (by rfl) ⟨593225, by rfl⟩ : syracuseStep 790967 = 1186451) B1186451
theorem B2003393 : Blo 790340 2003393 := bstep (se 2 (by rfl) ⟨751272, by rfl⟩ : syracuseStep 2003393 = 1502545) B1502545
theorem B790987 : Blo 790340 790987 := bstep (se 1 (by rfl) ⟨593240, by rfl⟩ : syracuseStep 790987 = 1186481) B1186481
theorem B889303 : Blo 790340 889303 := bstep (se 1 (by rfl) ⟨666977, by rfl⟩ : syracuseStep 889303 = 1333955) B1333955
theorem B790999 : Blo 790340 790999 := bstep (se 1 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 790999 = 1186499) B1186499
theorem B791019 : Blo 790340 791019 := bstep (se 1 (by rfl) ⟨593264, by rfl⟩ : syracuseStep 791019 = 1186529) B1186529
theorem B791031 : Blo 790340 791031 := bstep (se 1 (by rfl) ⟨593273, by rfl⟩ : syracuseStep 791031 = 1186547) B1186547
theorem B791051 : Blo 790340 791051 := bstep (se 1 (by rfl) ⟨593288, by rfl⟩ : syracuseStep 791051 = 1186577) B1186577
theorem B791063 : Blo 790340 791063 := bstep (se 1 (by rfl) ⟨593297, by rfl⟩ : syracuseStep 791063 = 1186595) B1186595
theorem B3379735 : Blo 790340 3379735 := bstep (se 1 (by rfl) ⟨2534801, by rfl⟩ : syracuseStep 3379735 = 5069603) B5069603
theorem B1085977 : Blo 790340 1085977 := bstep (se 2 (by rfl) ⟨407241, by rfl⟩ : syracuseStep 1085977 = 814483) B814483
theorem B791083 : Blo 790340 791083 := bstep (se 1 (by rfl) ⟨593312, by rfl⟩ : syracuseStep 791083 = 1186625) B1186625
theorem B791095 : Blo 790340 791095 := bstep (se 1 (by rfl) ⟨593321, by rfl⟩ : syracuseStep 791095 = 1186643) B1186643
theorem B791115 : Blo 790340 791115 := bstep (se 1 (by rfl) ⟨593336, by rfl⟩ : syracuseStep 791115 = 1186673) B1186673
theorem B791127 : Blo 790340 791127 := bstep (se 1 (by rfl) ⟨593345, by rfl⟩ : syracuseStep 791127 = 1186691) B1186691
theorem B3379805 : Blo 790340 3379805 := bstep (se 3 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 3379805 = 1267427) B1267427
theorem B791147 : Blo 790340 791147 := bstep (se 1 (by rfl) ⟨593360, by rfl⟩ : syracuseStep 791147 = 1186721) B1186721
theorem B791159 : Blo 790340 791159 := bstep (se 1 (by rfl) ⟨593369, by rfl⟩ : syracuseStep 791159 = 1186739) B1186739
theorem B889483 : Blo 790340 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B791179 : Blo 790340 791179 := bstep (se 1 (by rfl) ⟨593384, by rfl⟩ : syracuseStep 791179 = 1186769) B1186769
theorem B791191 : Blo 790340 791191 := bstep (se 1 (by rfl) ⟨593393, by rfl⟩ : syracuseStep 791191 = 1186787) B1186787
theorem B791211 : Blo 790340 791211 := bstep (se 1 (by rfl) ⟨593408, by rfl⟩ : syracuseStep 791211 = 1186817) B1186817
theorem B791223 : Blo 790340 791223 := bstep (se 1 (by rfl) ⟨593417, by rfl⟩ : syracuseStep 791223 = 1186835) B1186835
theorem B791243 : Blo 790340 791243 := bstep (se 1 (by rfl) ⟨593432, by rfl⟩ : syracuseStep 791243 = 1186865) B1186865
theorem B791255 : Blo 790340 791255 := bstep (se 1 (by rfl) ⟨593441, by rfl⟩ : syracuseStep 791255 = 1186883) B1186883
theorem B791275 : Blo 790340 791275 := bstep (se 1 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 791275 = 1186913) B1186913
theorem B889591 : Blo 790340 889591 := bstep (se 1 (by rfl) ⟨667193, by rfl⟩ : syracuseStep 889591 = 1334387) B1334387
theorem B791287 : Blo 790340 791287 := bstep (se 1 (by rfl) ⟨593465, by rfl⟩ : syracuseStep 791287 = 1186931) B1186931
theorem B791307 : Blo 790340 791307 := bstep (se 1 (by rfl) ⟨593480, by rfl⟩ : syracuseStep 791307 = 1186961) B1186961
theorem B791319 : Blo 790340 791319 := bstep (se 1 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 791319 = 1186979) B1186979
theorem B791339 : Blo 790340 791339 := bstep (se 1 (by rfl) ⟨593504, by rfl⟩ : syracuseStep 791339 = 1187009) B1187009
theorem B791351 : Blo 790340 791351 := bstep (se 1 (by rfl) ⟨593513, by rfl⟩ : syracuseStep 791351 = 1187027) B1187027
theorem B791371 : Blo 790340 791371 := bstep (se 1 (by rfl) ⟨593528, by rfl⟩ : syracuseStep 791371 = 1187057) B1187057
theorem B791383 : Blo 790340 791383 := bstep (se 1 (by rfl) ⟨593537, by rfl⟩ : syracuseStep 791383 = 1187075) B1187075
theorem B791403 : Blo 790340 791403 := bstep (se 1 (by rfl) ⟨593552, by rfl⟩ : syracuseStep 791403 = 1187105) B1187105
theorem B791415 : Blo 790340 791415 := bstep (se 1 (by rfl) ⟨593561, by rfl⟩ : syracuseStep 791415 = 1187123) B1187123
theorem B791435 : Blo 790340 791435 := bstep (se 1 (by rfl) ⟨593576, by rfl⟩ : syracuseStep 791435 = 1187153) B1187153
theorem B791447 : Blo 790340 791447 := bstep (se 1 (by rfl) ⟨593585, by rfl⟩ : syracuseStep 791447 = 1187171) B1187171
theorem B889771 : Blo 790340 889771 := bstep (se 1 (by rfl) ⟨667328, by rfl⟩ : syracuseStep 889771 = 1334657) B1334657
theorem B791467 : Blo 790340 791467 := bstep (se 1 (by rfl) ⟨593600, by rfl⟩ : syracuseStep 791467 = 1187201) B1187201
theorem B791479 : Blo 790340 791479 := bstep (se 1 (by rfl) ⟨593609, by rfl⟩ : syracuseStep 791479 = 1187219) B1187219
theorem B791499 : Blo 790340 791499 := bstep (se 1 (by rfl) ⟨593624, by rfl⟩ : syracuseStep 791499 = 1187249) B1187249
theorem B791511 : Blo 790340 791511 := bstep (se 1 (by rfl) ⟨593633, by rfl⟩ : syracuseStep 791511 = 1187267) B1187267
theorem B791531 : Blo 790340 791531 := bstep (se 1 (by rfl) ⟨593648, by rfl⟩ : syracuseStep 791531 = 1187297) B1187297
theorem B791543 : Blo 790340 791543 := bstep (se 1 (by rfl) ⟨593657, by rfl⟩ : syracuseStep 791543 = 1187315) B1187315
theorem B791563 : Blo 790340 791563 := bstep (se 1 (by rfl) ⟨593672, by rfl⟩ : syracuseStep 791563 = 1187345) B1187345
theorem B889879 : Blo 790340 889879 := bstep (se 1 (by rfl) ⟨667409, by rfl⟩ : syracuseStep 889879 = 1334819) B1334819
theorem B791575 : Blo 790340 791575 := bstep (se 1 (by rfl) ⟨593681, by rfl⟩ : syracuseStep 791575 = 1187363) B1187363
theorem B791595 : Blo 790340 791595 := bstep (se 1 (by rfl) ⟨593696, by rfl⟩ : syracuseStep 791595 = 1187393) B1187393
theorem B791607 : Blo 790340 791607 := bstep (se 1 (by rfl) ⟨593705, by rfl⟩ : syracuseStep 791607 = 1187411) B1187411
theorem B791627 : Blo 790340 791627 := bstep (se 1 (by rfl) ⟨593720, by rfl⟩ : syracuseStep 791627 = 1187441) B1187441
theorem B791639 : Blo 790340 791639 := bstep (se 1 (by rfl) ⟨593729, by rfl⟩ : syracuseStep 791639 = 1187459) B1187459
theorem B791659 : Blo 790340 791659 := bstep (se 1 (by rfl) ⟨593744, by rfl⟩ : syracuseStep 791659 = 1187489) B1187489
theorem B791671 : Blo 790340 791671 := bstep (se 1 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 791671 = 1187507) B1187507
theorem B791691 : Blo 790340 791691 := bstep (se 1 (by rfl) ⟨593768, by rfl⟩ : syracuseStep 791691 = 1187537) B1187537
theorem B791703 : Blo 790340 791703 := bstep (se 1 (by rfl) ⟨593777, by rfl⟩ : syracuseStep 791703 = 1187555) B1187555
theorem B791723 : Blo 790340 791723 := bstep (se 1 (by rfl) ⟨593792, by rfl⟩ : syracuseStep 791723 = 1187585) B1187585
theorem B6755507 : Blo 790340 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B791735 : Blo 790340 791735 := bstep (se 1 (by rfl) ⟨593801, by rfl⟩ : syracuseStep 791735 = 1187603) B1187603
theorem B890059 : Blo 790340 890059 := bstep (se 1 (by rfl) ⟨667544, by rfl⟩ : syracuseStep 890059 = 1335089) B1335089
theorem B791755 : Blo 790340 791755 := bstep (se 1 (by rfl) ⟨593816, by rfl⟩ : syracuseStep 791755 = 1187633) B1187633
theorem B791767 : Blo 790340 791767 := bstep (se 1 (by rfl) ⟨593825, by rfl⟩ : syracuseStep 791767 = 1187651) B1187651
theorem B791787 : Blo 790340 791787 := bstep (se 1 (by rfl) ⟨593840, by rfl⟩ : syracuseStep 791787 = 1187681) B1187681
theorem B791799 : Blo 790340 791799 := bstep (se 1 (by rfl) ⟨593849, by rfl⟩ : syracuseStep 791799 = 1187699) B1187699
theorem B791819 : Blo 790340 791819 := bstep (se 1 (by rfl) ⟨593864, by rfl⟩ : syracuseStep 791819 = 1187729) B1187729
theorem B791831 : Blo 790340 791831 := bstep (se 1 (by rfl) ⟨593873, by rfl⟩ : syracuseStep 791831 = 1187747) B1187747
theorem B791851 : Blo 790340 791851 := bstep (se 1 (by rfl) ⟨593888, by rfl⟩ : syracuseStep 791851 = 1187777) B1187777
theorem B890167 : Blo 790340 890167 := bstep (se 1 (by rfl) ⟨667625, by rfl⟩ : syracuseStep 890167 = 1335251) B1335251
theorem B791863 : Blo 790340 791863 := bstep (se 1 (by rfl) ⟨593897, by rfl⟩ : syracuseStep 791863 = 1187795) B1187795
theorem B3380555 : Blo 790340 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B791883 : Blo 790340 791883 := bstep (se 1 (by rfl) ⟨593912, by rfl⟩ : syracuseStep 791883 = 1187825) B1187825
theorem B791895 : Blo 790340 791895 := bstep (se 1 (by rfl) ⟨593921, by rfl⟩ : syracuseStep 791895 = 1187843) B1187843
theorem B791915 : Blo 790340 791915 := bstep (se 1 (by rfl) ⟨593936, by rfl⟩ : syracuseStep 791915 = 1187873) B1187873
theorem B791927 : Blo 790340 791927 := bstep (se 1 (by rfl) ⟨593945, by rfl⟩ : syracuseStep 791927 = 1187891) B1187891
theorem B791947 : Blo 790340 791947 := bstep (se 1 (by rfl) ⟨593960, by rfl⟩ : syracuseStep 791947 = 1187921) B1187921
theorem B791959 : Blo 790340 791959 := bstep (se 1 (by rfl) ⟨593969, by rfl⟩ : syracuseStep 791959 = 1187939) B1187939
theorem B791979 : Blo 790340 791979 := bstep (se 1 (by rfl) ⟨593984, by rfl⟩ : syracuseStep 791979 = 1187969) B1187969
theorem B6002099 : Blo 790340 6002099 := bstep (se 1 (by rfl) ⟨4501574, by rfl⟩ : syracuseStep 6002099 = 9003149) B9003149
theorem B791991 : Blo 790340 791991 := bstep (se 1 (by rfl) ⟨593993, by rfl⟩ : syracuseStep 791991 = 1187987) B1187987
theorem B792011 : Blo 790340 792011 := bstep (se 1 (by rfl) ⟨594008, by rfl⟩ : syracuseStep 792011 = 1188017) B1188017
theorem B792023 : Blo 790340 792023 := bstep (se 1 (by rfl) ⟨594017, by rfl⟩ : syracuseStep 792023 = 1188035) B1188035
theorem B890347 : Blo 790340 890347 := bstep (se 1 (by rfl) ⟨667760, by rfl⟩ : syracuseStep 890347 = 1335521) B1335521
theorem B792043 : Blo 790340 792043 := bstep (se 1 (by rfl) ⟨594032, by rfl⟩ : syracuseStep 792043 = 1188065) B1188065
theorem B792055 : Blo 790340 792055 := bstep (se 1 (by rfl) ⟨594041, by rfl⟩ : syracuseStep 792055 = 1188083) B1188083
theorem B792075 : Blo 790340 792075 := bstep (se 1 (by rfl) ⟨594056, by rfl⟩ : syracuseStep 792075 = 1188113) B1188113
theorem B792087 : Blo 790340 792087 := bstep (se 1 (by rfl) ⟨594065, by rfl⟩ : syracuseStep 792087 = 1188131) B1188131
theorem B792107 : Blo 790340 792107 := bstep (se 1 (by rfl) ⟨594080, by rfl⟩ : syracuseStep 792107 = 1188161) B1188161
theorem B6755885 : Blo 790340 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B792119 : Blo 790340 792119 := bstep (se 1 (by rfl) ⟨594089, by rfl⟩ : syracuseStep 792119 = 1188179) B1188179
theorem B792139 : Blo 790340 792139 := bstep (se 1 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 792139 = 1188209) B1188209
theorem B890455 : Blo 790340 890455 := bstep (se 1 (by rfl) ⟨667841, by rfl⟩ : syracuseStep 890455 = 1335683) B1335683
theorem B792151 : Blo 790340 792151 := bstep (se 1 (by rfl) ⟨594113, by rfl⟩ : syracuseStep 792151 = 1188227) B1188227
theorem B792171 : Blo 790340 792171 := bstep (se 1 (by rfl) ⟨594128, by rfl⟩ : syracuseStep 792171 = 1188257) B1188257
theorem B792183 : Blo 790340 792183 := bstep (se 1 (by rfl) ⟨594137, by rfl⟩ : syracuseStep 792183 = 1188275) B1188275
theorem B792203 : Blo 790340 792203 := bstep (se 1 (by rfl) ⟨594152, by rfl⟩ : syracuseStep 792203 = 1188305) B1188305
theorem B1808011 : Blo 790340 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B792215 : Blo 790340 792215 := bstep (se 1 (by rfl) ⟨594161, by rfl⟩ : syracuseStep 792215 = 1188323) B1188323
theorem B2856599 : Blo 790340 2856599 := bstep (se 1 (by rfl) ⟨2142449, by rfl⟩ : syracuseStep 2856599 = 4284899) B4284899
theorem B792235 : Blo 790340 792235 := bstep (se 1 (by rfl) ⟨594176, by rfl⟩ : syracuseStep 792235 = 1188353) B1188353
theorem B3610291 : Blo 790340 3610291 := bstep (se 1 (by rfl) ⟨2707718, by rfl⟩ : syracuseStep 3610291 = 5415437) B5415437
theorem B2004659 : Blo 790340 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B792247 : Blo 790340 792247 := bstep (se 1 (by rfl) ⟨594185, by rfl⟩ : syracuseStep 792247 = 1188371) B1188371
theorem B792267 : Blo 790340 792267 := bstep (se 1 (by rfl) ⟨594200, by rfl⟩ : syracuseStep 792267 = 1188401) B1188401
theorem B792279 : Blo 790340 792279 := bstep (se 1 (by rfl) ⟨594209, by rfl⟩ : syracuseStep 792279 = 1188419) B1188419
theorem B792299 : Blo 790340 792299 := bstep (se 1 (by rfl) ⟨594224, by rfl⟩ : syracuseStep 792299 = 1188449) B1188449
theorem B792311 : Blo 790340 792311 := bstep (se 1 (by rfl) ⟨594233, by rfl⟩ : syracuseStep 792311 = 1188467) B1188467
theorem B890635 : Blo 790340 890635 := bstep (se 1 (by rfl) ⟨667976, by rfl⟩ : syracuseStep 890635 = 1335953) B1335953
theorem B792331 : Blo 790340 792331 := bstep (se 1 (by rfl) ⟨594248, by rfl⟩ : syracuseStep 792331 = 1188497) B1188497
theorem B792343 : Blo 790340 792343 := bstep (se 1 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 792343 = 1188515) B1188515
theorem B792363 : Blo 790340 792363 := bstep (se 1 (by rfl) ⟨594272, by rfl⟩ : syracuseStep 792363 = 1188545) B1188545
theorem B792375 : Blo 790340 792375 := bstep (se 1 (by rfl) ⟨594281, by rfl⟩ : syracuseStep 792375 = 1188563) B1188563
theorem B6854465 : Blo 790340 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B1185611 : Blo 790340 1185611 := bstep (se 1 (by rfl) ⟨889208, by rfl⟩ : syracuseStep 1185611 = 1778417) B1778417
theorem B792395 : Blo 790340 792395 := bstep (se 1 (by rfl) ⟨594296, by rfl⟩ : syracuseStep 792395 = 1188593) B1188593
theorem B1185623 : Blo 790340 1185623 := bstep (se 1 (by rfl) ⟨889217, by rfl⟩ : syracuseStep 1185623 = 1778435) B1778435
theorem B792407 : Blo 790340 792407 := bstep (se 1 (by rfl) ⟨594305, by rfl⟩ : syracuseStep 792407 = 1188611) B1188611
theorem B792427 : Blo 790340 792427 := bstep (se 1 (by rfl) ⟨594320, by rfl⟩ : syracuseStep 792427 = 1188641) B1188641
theorem B890743 : Blo 790340 890743 := bstep (se 1 (by rfl) ⟨668057, by rfl⟩ : syracuseStep 890743 = 1336115) B1336115
theorem B792439 : Blo 790340 792439 := bstep (se 1 (by rfl) ⟨594329, by rfl⟩ : syracuseStep 792439 = 1188659) B1188659
theorem B792459 : Blo 790340 792459 := bstep (se 1 (by rfl) ⟨594344, by rfl⟩ : syracuseStep 792459 = 1188689) B1188689
theorem B792471 : Blo 790340 792471 := bstep (se 1 (by rfl) ⟨594353, by rfl⟩ : syracuseStep 792471 = 1188707) B1188707
theorem B1185689 : Blo 790340 1185689 := bstep (se 2 (by rfl) ⟨444633, by rfl⟩ : syracuseStep 1185689 = 889267) B889267
theorem B792491 : Blo 790340 792491 := bstep (se 1 (by rfl) ⟨594368, by rfl⟩ : syracuseStep 792491 = 1188737) B1188737
theorem B792503 : Blo 790340 792503 := bstep (se 1 (by rfl) ⟨594377, by rfl⟩ : syracuseStep 792503 = 1188755) B1188755
theorem B792523 : Blo 790340 792523 := bstep (se 1 (by rfl) ⟨594392, by rfl⟩ : syracuseStep 792523 = 1188785) B1188785
theorem B792535 : Blo 790340 792535 := bstep (se 1 (by rfl) ⟨594401, by rfl⟩ : syracuseStep 792535 = 1188803) B1188803
theorem B22845401 : Blo 790340 22845401 := bstep (se 2 (by rfl) ⟨8567025, by rfl⟩ : syracuseStep 22845401 = 17134051) B17134051
theorem B792555 : Blo 790340 792555 := bstep (se 1 (by rfl) ⟨594416, by rfl⟩ : syracuseStep 792555 = 1188833) B1188833
theorem B792567 : Blo 790340 792567 := bstep (se 1 (by rfl) ⟨594425, by rfl⟩ : syracuseStep 792567 = 1188851) B1188851
theorem B1185803 : Blo 790340 1185803 := bstep (se 1 (by rfl) ⟨889352, by rfl⟩ : syracuseStep 1185803 = 1778705) B1778705
theorem B792587 : Blo 790340 792587 := bstep (se 1 (by rfl) ⟨594440, by rfl⟩ : syracuseStep 792587 = 1188881) B1188881
theorem B1185815 : Blo 790340 1185815 := bstep (se 1 (by rfl) ⟨889361, by rfl⟩ : syracuseStep 1185815 = 1778723) B1778723
theorem B792599 : Blo 790340 792599 := bstep (se 1 (by rfl) ⟨594449, by rfl⟩ : syracuseStep 792599 = 1188899) B1188899
theorem B890923 : Blo 790340 890923 := bstep (se 1 (by rfl) ⟨668192, by rfl⟩ : syracuseStep 890923 = 1336385) B1336385
theorem B792619 : Blo 790340 792619 := bstep (se 1 (by rfl) ⟨594464, by rfl⟩ : syracuseStep 792619 = 1188929) B1188929
theorem B792631 : Blo 790340 792631 := bstep (se 1 (by rfl) ⟨594473, by rfl⟩ : syracuseStep 792631 = 1188947) B1188947
theorem B1906753 : Blo 790340 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B792651 : Blo 790340 792651 := bstep (se 1 (by rfl) ⟨594488, by rfl⟩ : syracuseStep 792651 = 1188977) B1188977
theorem B792663 : Blo 790340 792663 := bstep (se 1 (by rfl) ⟨594497, by rfl⟩ : syracuseStep 792663 = 1188995) B1188995
theorem B1185881 : Blo 790340 1185881 := bstep (se 2 (by rfl) ⟨444705, by rfl⟩ : syracuseStep 1185881 = 889411) B889411
theorem B792683 : Blo 790340 792683 := bstep (se 1 (by rfl) ⟨594512, by rfl⟩ : syracuseStep 792683 = 1189025) B1189025
theorem B792695 : Blo 790340 792695 := bstep (se 1 (by rfl) ⟨594521, by rfl⟩ : syracuseStep 792695 = 1189043) B1189043
theorem B8558723 : Blo 790340 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B792715 : Blo 790340 792715 := bstep (se 1 (by rfl) ⟨594536, by rfl⟩ : syracuseStep 792715 = 1189073) B1189073
theorem B4003991 : Blo 790340 4003991 := bstep (se 1 (by rfl) ⟨3002993, by rfl⟩ : syracuseStep 4003991 = 6005987) B6005987
theorem B891031 : Blo 790340 891031 := bstep (se 1 (by rfl) ⟨668273, by rfl⟩ : syracuseStep 891031 = 1336547) B1336547
theorem B792727 : Blo 790340 792727 := bstep (se 1 (by rfl) ⟨594545, by rfl⟩ : syracuseStep 792727 = 1189091) B1189091
theorem B792747 : Blo 790340 792747 := bstep (se 1 (by rfl) ⟨594560, by rfl⟩ : syracuseStep 792747 = 1189121) B1189121
theorem B792759 : Blo 790340 792759 := bstep (se 1 (by rfl) ⟨594569, by rfl⟩ : syracuseStep 792759 = 1189139) B1189139
theorem B1185995 : Blo 790340 1185995 := bstep (se 1 (by rfl) ⟨889496, by rfl⟩ : syracuseStep 1185995 = 1778993) B1778993
theorem B2005195 : Blo 790340 2005195 := bstep (se 1 (by rfl) ⟨1503896, by rfl⟩ : syracuseStep 2005195 = 3007793) B3007793
theorem B792779 : Blo 790340 792779 := bstep (se 1 (by rfl) ⟨594584, by rfl⟩ : syracuseStep 792779 = 1189169) B1189169
theorem B1186007 : Blo 790340 1186007 := bstep (se 1 (by rfl) ⟨889505, by rfl⟩ : syracuseStep 1186007 = 1779011) B1779011
theorem B792791 : Blo 790340 792791 := bstep (se 1 (by rfl) ⟨594593, by rfl⟩ : syracuseStep 792791 = 1189187) B1189187
theorem B792811 : Blo 790340 792811 := bstep (se 1 (by rfl) ⟨594608, by rfl⟩ : syracuseStep 792811 = 1189217) B1189217
theorem B792823 : Blo 790340 792823 := bstep (se 1 (by rfl) ⟨594617, by rfl⟩ : syracuseStep 792823 = 1189235) B1189235
theorem B792843 : Blo 790340 792843 := bstep (se 1 (by rfl) ⟨594632, by rfl⟩ : syracuseStep 792843 = 1189265) B1189265
theorem B792855 : Blo 790340 792855 := bstep (se 1 (by rfl) ⟨594641, by rfl⟩ : syracuseStep 792855 = 1189283) B1189283
theorem B1186073 : Blo 790340 1186073 := bstep (se 2 (by rfl) ⟨444777, by rfl⟩ : syracuseStep 1186073 = 889555) B889555
theorem B792875 : Blo 790340 792875 := bstep (se 1 (by rfl) ⟨594656, by rfl⟩ : syracuseStep 792875 = 1189313) B1189313
theorem B792887 : Blo 790340 792887 := bstep (se 1 (by rfl) ⟨594665, by rfl⟩ : syracuseStep 792887 = 1189331) B1189331
theorem B2136395 : Blo 790340 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B891211 : Blo 790340 891211 := bstep (se 1 (by rfl) ⟨668408, by rfl⟩ : syracuseStep 891211 = 1336817) B1336817
theorem B792907 : Blo 790340 792907 := bstep (se 1 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 792907 = 1189361) B1189361
theorem B792919 : Blo 790340 792919 := bstep (se 1 (by rfl) ⟨594689, by rfl⟩ : syracuseStep 792919 = 1189379) B1189379
theorem B2005337 : Blo 790340 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B792939 : Blo 790340 792939 := bstep (se 1 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 792939 = 1189409) B1189409
theorem B792951 : Blo 790340 792951 := bstep (se 1 (by rfl) ⟨594713, by rfl⟩ : syracuseStep 792951 = 1189427) B1189427
theorem B1186187 : Blo 790340 1186187 := bstep (se 1 (by rfl) ⟨889640, by rfl⟩ : syracuseStep 1186187 = 1779281) B1779281
theorem B792971 : Blo 790340 792971 := bstep (se 1 (by rfl) ⟨594728, by rfl⟩ : syracuseStep 792971 = 1189457) B1189457
theorem B2857361 : Blo 790340 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B1186199 : Blo 790340 1186199 := bstep (se 1 (by rfl) ⟨889649, by rfl⟩ : syracuseStep 1186199 = 1779299) B1779299
theorem B792983 : Blo 790340 792983 := bstep (se 1 (by rfl) ⟨594737, by rfl⟩ : syracuseStep 792983 = 1189475) B1189475
theorem B793003 : Blo 790340 793003 := bstep (se 1 (by rfl) ⟨594752, by rfl⟩ : syracuseStep 793003 = 1189505) B1189505
theorem B891319 : Blo 790340 891319 := bstep (se 1 (by rfl) ⟨668489, by rfl⟩ : syracuseStep 891319 = 1336979) B1336979
theorem B793015 : Blo 790340 793015 := bstep (se 1 (by rfl) ⟨594761, by rfl⟩ : syracuseStep 793015 = 1189523) B1189523
theorem B793035 : Blo 790340 793035 := bstep (se 1 (by rfl) ⟨594776, by rfl⟩ : syracuseStep 793035 = 1189553) B1189553
theorem B793047 : Blo 790340 793047 := bstep (se 1 (by rfl) ⟨594785, by rfl⟩ : syracuseStep 793047 = 1189571) B1189571
theorem B1186265 : Blo 790340 1186265 := bstep (se 2 (by rfl) ⟨444849, by rfl⟩ : syracuseStep 1186265 = 889699) B889699
theorem B793067 : Blo 790340 793067 := bstep (se 1 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 793067 = 1189601) B1189601
theorem B793079 : Blo 790340 793079 := bstep (se 1 (by rfl) ⟨594809, by rfl⟩ : syracuseStep 793079 = 1189619) B1189619
theorem B793099 : Blo 790340 793099 := bstep (se 1 (by rfl) ⟨594824, by rfl⟩ : syracuseStep 793099 = 1189649) B1189649
theorem B793111 : Blo 790340 793111 := bstep (se 1 (by rfl) ⟨594833, by rfl⟩ : syracuseStep 793111 = 1189667) B1189667
theorem B793131 : Blo 790340 793131 := bstep (se 1 (by rfl) ⟨594848, by rfl⟩ : syracuseStep 793131 = 1189697) B1189697
theorem B793143 : Blo 790340 793143 := bstep (se 1 (by rfl) ⟨594857, by rfl⟩ : syracuseStep 793143 = 1189715) B1189715
theorem B1186379 : Blo 790340 1186379 := bstep (se 1 (by rfl) ⟨889784, by rfl⟩ : syracuseStep 1186379 = 1779569) B1779569
theorem B793163 : Blo 790340 793163 := bstep (se 1 (by rfl) ⟨594872, by rfl⟩ : syracuseStep 793163 = 1189745) B1189745
theorem B1186391 : Blo 790340 1186391 := bstep (se 1 (by rfl) ⟨889793, by rfl⟩ : syracuseStep 1186391 = 1779587) B1779587
theorem B793175 : Blo 790340 793175 := bstep (se 1 (by rfl) ⟨594881, by rfl⟩ : syracuseStep 793175 = 1189763) B1189763
theorem B891499 : Blo 790340 891499 := bstep (se 1 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 891499 = 1337249) B1337249
theorem B793195 : Blo 790340 793195 := bstep (se 1 (by rfl) ⟨594896, by rfl⟩ : syracuseStep 793195 = 1189793) B1189793
theorem B793207 : Blo 790340 793207 := bstep (se 1 (by rfl) ⟨594905, by rfl⟩ : syracuseStep 793207 = 1189811) B1189811
theorem B793227 : Blo 790340 793227 := bstep (se 1 (by rfl) ⟨594920, by rfl⟩ : syracuseStep 793227 = 1189841) B1189841
theorem B793239 : Blo 790340 793239 := bstep (se 1 (by rfl) ⟨594929, by rfl⟩ : syracuseStep 793239 = 1189859) B1189859
theorem B1186457 : Blo 790340 1186457 := bstep (se 2 (by rfl) ⟨444921, by rfl⟩ : syracuseStep 1186457 = 889843) B889843
theorem B793259 : Blo 790340 793259 := bstep (se 1 (by rfl) ⟨594944, by rfl⟩ : syracuseStep 793259 = 1189889) B1189889
theorem B793271 : Blo 790340 793271 := bstep (se 1 (by rfl) ⟨594953, by rfl⟩ : syracuseStep 793271 = 1189907) B1189907
theorem B793291 : Blo 790340 793291 := bstep (se 1 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 793291 = 1189937) B1189937
theorem B891607 : Blo 790340 891607 := bstep (se 1 (by rfl) ⟨668705, by rfl⟩ : syracuseStep 891607 = 1337411) B1337411
theorem B793303 : Blo 790340 793303 := bstep (se 1 (by rfl) ⟨594977, by rfl⟩ : syracuseStep 793303 = 1189955) B1189955
theorem B793323 : Blo 790340 793323 := bstep (se 1 (by rfl) ⟨594992, by rfl⟩ : syracuseStep 793323 = 1189985) B1189985
theorem B793335 : Blo 790340 793335 := bstep (se 1 (by rfl) ⟨595001, by rfl⟩ : syracuseStep 793335 = 1190003) B1190003
theorem B1186571 : Blo 790340 1186571 := bstep (se 1 (by rfl) ⟨889928, by rfl⟩ : syracuseStep 1186571 = 1779857) B1779857
theorem B793355 : Blo 790340 793355 := bstep (se 1 (by rfl) ⟨595016, by rfl⟩ : syracuseStep 793355 = 1190033) B1190033
theorem B1186583 : Blo 790340 1186583 := bstep (se 1 (by rfl) ⟨889937, by rfl⟩ : syracuseStep 1186583 = 1779875) B1779875
theorem B793367 : Blo 790340 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B793387 : Blo 790340 793387 := bstep (se 1 (by rfl) ⟨595040, by rfl⟩ : syracuseStep 793387 = 1190081) B1190081
theorem B793399 : Blo 790340 793399 := bstep (se 1 (by rfl) ⟨595049, by rfl⟩ : syracuseStep 793399 = 1190099) B1190099
theorem B793419 : Blo 790340 793419 := bstep (se 1 (by rfl) ⟨595064, by rfl⟩ : syracuseStep 793419 = 1190129) B1190129
theorem B793431 : Blo 790340 793431 := bstep (se 1 (by rfl) ⟨595073, by rfl⟩ : syracuseStep 793431 = 1190147) B1190147
theorem B1186649 : Blo 790340 1186649 := bstep (se 2 (by rfl) ⟨444993, by rfl⟩ : syracuseStep 1186649 = 889987) B889987
theorem B6003557 : Blo 790340 6003557 := bstep (se 4 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 6003557 = 1125667) B1125667
theorem B793451 : Blo 790340 793451 := bstep (se 1 (by rfl) ⟨595088, by rfl⟩ : syracuseStep 793451 = 1190177) B1190177
theorem B793463 : Blo 790340 793463 := bstep (se 1 (by rfl) ⟨595097, by rfl⟩ : syracuseStep 793463 = 1190195) B1190195
theorem B891787 : Blo 790340 891787 := bstep (se 1 (by rfl) ⟨668840, by rfl⟩ : syracuseStep 891787 = 1337681) B1337681
theorem B793483 : Blo 790340 793483 := bstep (se 1 (by rfl) ⟨595112, by rfl⟩ : syracuseStep 793483 = 1190225) B1190225
theorem B793495 : Blo 790340 793495 := bstep (se 1 (by rfl) ⟨595121, by rfl⟩ : syracuseStep 793495 = 1190243) B1190243
theorem B793515 : Blo 790340 793515 := bstep (se 1 (by rfl) ⟨595136, by rfl⟩ : syracuseStep 793515 = 1190273) B1190273
theorem B793527 : Blo 790340 793527 := bstep (se 1 (by rfl) ⟨595145, by rfl⟩ : syracuseStep 793527 = 1190291) B1190291
theorem B1186763 : Blo 790340 1186763 := bstep (se 1 (by rfl) ⟨890072, by rfl⟩ : syracuseStep 1186763 = 1780145) B1780145
theorem B793547 : Blo 790340 793547 := bstep (se 1 (by rfl) ⟨595160, by rfl⟩ : syracuseStep 793547 = 1190321) B1190321
theorem B1186775 : Blo 790340 1186775 := bstep (se 1 (by rfl) ⟨890081, by rfl⟩ : syracuseStep 1186775 = 1780163) B1780163
theorem B793559 : Blo 790340 793559 := bstep (se 1 (by rfl) ⟨595169, by rfl⟩ : syracuseStep 793559 = 1190339) B1190339
theorem B3218393 : Blo 790340 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B793579 : Blo 790340 793579 := bstep (se 1 (by rfl) ⟨595184, by rfl⟩ : syracuseStep 793579 = 1190369) B1190369
theorem B891895 : Blo 790340 891895 := bstep (se 1 (by rfl) ⟨668921, by rfl⟩ : syracuseStep 891895 = 1337843) B1337843
theorem B793591 : Blo 790340 793591 := bstep (se 1 (by rfl) ⟨595193, by rfl⟩ : syracuseStep 793591 = 1190387) B1190387
theorem B793611 : Blo 790340 793611 := bstep (se 1 (by rfl) ⟨595208, by rfl⟩ : syracuseStep 793611 = 1190417) B1190417
theorem B793623 : Blo 790340 793623 := bstep (se 1 (by rfl) ⟨595217, by rfl⟩ : syracuseStep 793623 = 1190435) B1190435
theorem B1186841 : Blo 790340 1186841 := bstep (se 2 (by rfl) ⟨445065, by rfl⟩ : syracuseStep 1186841 = 890131) B890131
theorem B793643 : Blo 790340 793643 := bstep (se 1 (by rfl) ⟨595232, by rfl⟩ : syracuseStep 793643 = 1190465) B1190465
theorem B793655 : Blo 790340 793655 := bstep (se 1 (by rfl) ⟨595241, by rfl⟩ : syracuseStep 793655 = 1190483) B1190483
theorem B793675 : Blo 790340 793675 := bstep (se 1 (by rfl) ⟨595256, by rfl⟩ : syracuseStep 793675 = 1190513) B1190513
theorem B793687 : Blo 790340 793687 := bstep (se 1 (by rfl) ⟨595265, by rfl⟩ : syracuseStep 793687 = 1190531) B1190531
theorem B793707 : Blo 790340 793707 := bstep (se 1 (by rfl) ⟨595280, by rfl⟩ : syracuseStep 793707 = 1190561) B1190561
theorem B793719 : Blo 790340 793719 := bstep (se 1 (by rfl) ⟨595289, by rfl⟩ : syracuseStep 793719 = 1190579) B1190579
theorem B1186955 : Blo 790340 1186955 := bstep (se 1 (by rfl) ⟨890216, by rfl⟩ : syracuseStep 1186955 = 1780433) B1780433
theorem B793739 : Blo 790340 793739 := bstep (se 1 (by rfl) ⟨595304, by rfl⟩ : syracuseStep 793739 = 1190609) B1190609
theorem B1186967 : Blo 790340 1186967 := bstep (se 1 (by rfl) ⟨890225, by rfl⟩ : syracuseStep 1186967 = 1780451) B1780451
theorem B2006167 : Blo 790340 2006167 := bstep (se 1 (by rfl) ⟨1504625, by rfl⟩ : syracuseStep 2006167 = 3009251) B3009251
theorem B793751 : Blo 790340 793751 := bstep (se 1 (by rfl) ⟨595313, by rfl⟩ : syracuseStep 793751 = 1190627) B1190627
theorem B892075 : Blo 790340 892075 := bstep (se 1 (by rfl) ⟨669056, by rfl⟩ : syracuseStep 892075 = 1338113) B1338113
theorem B793771 : Blo 790340 793771 := bstep (se 1 (by rfl) ⟨595328, by rfl⟩ : syracuseStep 793771 = 1190657) B1190657
theorem B793783 : Blo 790340 793783 := bstep (se 1 (by rfl) ⟨595337, by rfl⟩ : syracuseStep 793783 = 1190675) B1190675
theorem B793803 : Blo 790340 793803 := bstep (se 1 (by rfl) ⟨595352, by rfl⟩ : syracuseStep 793803 = 1190705) B1190705
theorem B793815 : Blo 790340 793815 := bstep (se 1 (by rfl) ⟨595361, by rfl⟩ : syracuseStep 793815 = 1190723) B1190723
theorem B1187033 : Blo 790340 1187033 := bstep (se 2 (by rfl) ⟨445137, by rfl⟩ : syracuseStep 1187033 = 890275) B890275
theorem B793835 : Blo 790340 793835 := bstep (se 1 (by rfl) ⟨595376, by rfl⟩ : syracuseStep 793835 = 1190753) B1190753
theorem B793847 : Blo 790340 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B793867 : Blo 790340 793867 := bstep (se 1 (by rfl) ⟨595400, by rfl⟩ : syracuseStep 793867 = 1190801) B1190801
theorem B892183 : Blo 790340 892183 := bstep (se 1 (by rfl) ⟨669137, by rfl⟩ : syracuseStep 892183 = 1338275) B1338275
theorem B793879 : Blo 790340 793879 := bstep (se 1 (by rfl) ⟨595409, by rfl⟩ : syracuseStep 793879 = 1190819) B1190819
theorem B793899 : Blo 790340 793899 := bstep (se 1 (by rfl) ⟨595424, by rfl⟩ : syracuseStep 793899 = 1190849) B1190849
theorem B793911 : Blo 790340 793911 := bstep (se 1 (by rfl) ⟨595433, by rfl⟩ : syracuseStep 793911 = 1190867) B1190867
theorem B6004043 : Blo 790340 6004043 := bstep (se 1 (by rfl) ⟨4503032, by rfl⟩ : syracuseStep 6004043 = 9006065) B9006065
theorem B1187147 : Blo 790340 1187147 := bstep (se 1 (by rfl) ⟨890360, by rfl⟩ : syracuseStep 1187147 = 1780721) B1780721
theorem B793931 : Blo 790340 793931 := bstep (se 1 (by rfl) ⟨595448, by rfl⟩ : syracuseStep 793931 = 1190897) B1190897
theorem B1187159 : Blo 790340 1187159 := bstep (se 1 (by rfl) ⟨890369, by rfl⟩ : syracuseStep 1187159 = 1780739) B1780739
theorem B793943 : Blo 790340 793943 := bstep (se 1 (by rfl) ⟨595457, by rfl⟩ : syracuseStep 793943 = 1190915) B1190915
theorem B793963 : Blo 790340 793963 := bstep (se 1 (by rfl) ⟨595472, by rfl⟩ : syracuseStep 793963 = 1190945) B1190945
theorem B793975 : Blo 790340 793975 := bstep (se 1 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 793975 = 1190963) B1190963
theorem B793995 : Blo 790340 793995 := bstep (se 1 (by rfl) ⟨595496, by rfl⟩ : syracuseStep 793995 = 1190993) B1190993
theorem B794007 : Blo 790340 794007 := bstep (se 1 (by rfl) ⟨595505, by rfl⟩ : syracuseStep 794007 = 1191011) B1191011
theorem B1187225 : Blo 790340 1187225 := bstep (se 2 (by rfl) ⟨445209, by rfl⟩ : syracuseStep 1187225 = 890419) B890419
theorem B794027 : Blo 790340 794027 := bstep (se 1 (by rfl) ⟨595520, by rfl⟩ : syracuseStep 794027 = 1191041) B1191041
theorem B794039 : Blo 790340 794039 := bstep (se 1 (by rfl) ⟨595529, by rfl⟩ : syracuseStep 794039 = 1191059) B1191059
theorem B892363 : Blo 790340 892363 := bstep (se 1 (by rfl) ⟨669272, by rfl⟩ : syracuseStep 892363 = 1338545) B1338545
theorem B794059 : Blo 790340 794059 := bstep (se 1 (by rfl) ⟨595544, by rfl⟩ : syracuseStep 794059 = 1191089) B1191089
theorem B794071 : Blo 790340 794071 := bstep (se 1 (by rfl) ⟨595553, by rfl⟩ : syracuseStep 794071 = 1191107) B1191107
theorem B794091 : Blo 790340 794091 := bstep (se 1 (by rfl) ⟨595568, by rfl⟩ : syracuseStep 794091 = 1191137) B1191137
theorem B794103 : Blo 790340 794103 := bstep (se 1 (by rfl) ⟨595577, by rfl⟩ : syracuseStep 794103 = 1191155) B1191155
theorem B1187339 : Blo 790340 1187339 := bstep (se 1 (by rfl) ⟨890504, by rfl⟩ : syracuseStep 1187339 = 1781009) B1781009
theorem B794123 : Blo 790340 794123 := bstep (se 1 (by rfl) ⟨595592, by rfl⟩ : syracuseStep 794123 = 1191185) B1191185
theorem B1187351 : Blo 790340 1187351 := bstep (se 1 (by rfl) ⟨890513, by rfl⟩ : syracuseStep 1187351 = 1781027) B1781027
theorem B794135 : Blo 790340 794135 := bstep (se 1 (by rfl) ⟨595601, by rfl⟩ : syracuseStep 794135 = 1191203) B1191203
theorem B794155 : Blo 790340 794155 := bstep (se 1 (by rfl) ⟨595616, by rfl⟩ : syracuseStep 794155 = 1191233) B1191233
theorem B892471 : Blo 790340 892471 := bstep (se 1 (by rfl) ⟨669353, by rfl⟩ : syracuseStep 892471 = 1338707) B1338707
theorem B794167 : Blo 790340 794167 := bstep (se 1 (by rfl) ⟨595625, by rfl⟩ : syracuseStep 794167 = 1191251) B1191251
theorem B2006603 : Blo 790340 2006603 := bstep (se 1 (by rfl) ⟨1504952, by rfl⟩ : syracuseStep 2006603 = 3009905) B3009905
theorem B794187 : Blo 790340 794187 := bstep (se 1 (by rfl) ⟨595640, by rfl⟩ : syracuseStep 794187 = 1191281) B1191281
theorem B794199 : Blo 790340 794199 := bstep (se 1 (by rfl) ⟨595649, by rfl⟩ : syracuseStep 794199 = 1191299) B1191299
theorem B1187417 : Blo 790340 1187417 := bstep (se 2 (by rfl) ⟨445281, by rfl⟩ : syracuseStep 1187417 = 890563) B890563
theorem B794219 : Blo 790340 794219 := bstep (se 1 (by rfl) ⟨595664, by rfl⟩ : syracuseStep 794219 = 1191329) B1191329
theorem B794231 : Blo 790340 794231 := bstep (se 1 (by rfl) ⟨595673, by rfl⟩ : syracuseStep 794231 = 1191347) B1191347
theorem B794251 : Blo 790340 794251 := bstep (se 1 (by rfl) ⟨595688, by rfl⟩ : syracuseStep 794251 = 1191377) B1191377
theorem B794263 : Blo 790340 794263 := bstep (se 1 (by rfl) ⟨595697, by rfl⟩ : syracuseStep 794263 = 1191395) B1191395
theorem B794283 : Blo 790340 794283 := bstep (se 1 (by rfl) ⟨595712, by rfl⟩ : syracuseStep 794283 = 1191425) B1191425
theorem B794295 : Blo 790340 794295 := bstep (se 1 (by rfl) ⟨595721, by rfl⟩ : syracuseStep 794295 = 1191443) B1191443
theorem B1187531 : Blo 790340 1187531 := bstep (se 1 (by rfl) ⟨890648, by rfl⟩ : syracuseStep 1187531 = 1781297) B1781297
theorem B794315 : Blo 790340 794315 := bstep (se 1 (by rfl) ⟨595736, by rfl⟩ : syracuseStep 794315 = 1191473) B1191473
theorem B1187543 : Blo 790340 1187543 := bstep (se 1 (by rfl) ⟨890657, by rfl⟩ : syracuseStep 1187543 = 1781315) B1781315
theorem B794327 : Blo 790340 794327 := bstep (se 1 (by rfl) ⟨595745, by rfl⟩ : syracuseStep 794327 = 1191491) B1191491
theorem B892651 : Blo 790340 892651 := bstep (se 1 (by rfl) ⟨669488, by rfl⟩ : syracuseStep 892651 = 1338977) B1338977
theorem B1187609 : Blo 790340 1187609 := bstep (se 2 (by rfl) ⟨445353, by rfl⟩ : syracuseStep 1187609 = 890707) B890707
theorem B1810201 : Blo 790340 1810201 := bstep (se 2 (by rfl) ⟨678825, by rfl⟩ : syracuseStep 1810201 = 1357651) B1357651
theorem B892759 : Blo 790340 892759 := bstep (se 1 (by rfl) ⟨669569, by rfl⟩ : syracuseStep 892759 = 1339139) B1339139
theorem B7610213 : Blo 790340 7610213 := bstep (se 4 (by rfl) ⟨713457, by rfl⟩ : syracuseStep 7610213 = 1426915) B1426915
theorem B1187723 : Blo 790340 1187723 := bstep (se 1 (by rfl) ⟨890792, by rfl⟩ : syracuseStep 1187723 = 1781585) B1781585
theorem B1187735 : Blo 790340 1187735 := bstep (se 1 (by rfl) ⟨890801, by rfl⟩ : syracuseStep 1187735 = 1781603) B1781603
theorem B2006977 : Blo 790340 2006977 := bstep (se 2 (by rfl) ⟨752616, by rfl⟩ : syracuseStep 2006977 = 1505233) B1505233
theorem B1187801 : Blo 790340 1187801 := bstep (se 2 (by rfl) ⟨445425, by rfl⟩ : syracuseStep 1187801 = 890851) B890851
theorem B892939 : Blo 790340 892939 := bstep (se 1 (by rfl) ⟨669704, by rfl⟩ : syracuseStep 892939 = 1339409) B1339409
theorem B1187915 : Blo 790340 1187915 := bstep (se 1 (by rfl) ⟨890936, by rfl⟩ : syracuseStep 1187915 = 1781873) B1781873
theorem B1187927 : Blo 790340 1187927 := bstep (se 1 (by rfl) ⟨890945, by rfl⟩ : syracuseStep 1187927 = 1781891) B1781891
theorem B893047 : Blo 790340 893047 := bstep (se 1 (by rfl) ⟨669785, by rfl⟩ : syracuseStep 893047 = 1339571) B1339571
theorem B1187993 : Blo 790340 1187993 := bstep (se 2 (by rfl) ⟨445497, by rfl⟩ : syracuseStep 1187993 = 890995) B890995
theorem B3219659 : Blo 790340 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B1188107 : Blo 790340 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B1188119 : Blo 790340 1188119 := bstep (se 1 (by rfl) ⟨891089, by rfl⟩ : syracuseStep 1188119 = 1782179) B1782179
theorem B893227 : Blo 790340 893227 := bstep (se 1 (by rfl) ⟨669920, by rfl⟩ : syracuseStep 893227 = 1339841) B1339841
theorem B1188185 : Blo 790340 1188185 := bstep (se 2 (by rfl) ⟨445569, by rfl⟩ : syracuseStep 1188185 = 891139) B891139
theorem B893335 : Blo 790340 893335 := bstep (se 1 (by rfl) ⟨670001, by rfl⟩ : syracuseStep 893335 = 1340003) B1340003
theorem B1188299 : Blo 790340 1188299 := bstep (se 1 (by rfl) ⟨891224, by rfl⟩ : syracuseStep 1188299 = 1782449) B1782449
theorem B1188311 : Blo 790340 1188311 := bstep (se 1 (by rfl) ⟨891233, by rfl⟩ : syracuseStep 1188311 = 1782467) B1782467
theorem B2007575 : Blo 790340 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B1188377 : Blo 790340 1188377 := bstep (se 2 (by rfl) ⟨445641, by rfl⟩ : syracuseStep 1188377 = 891283) B891283
theorem B6431267 : Blo 790340 6431267 := bstep (se 1 (by rfl) ⟨4823450, by rfl⟩ : syracuseStep 6431267 = 9646901) B9646901
theorem B893515 : Blo 790340 893515 := bstep (se 1 (by rfl) ⟨670136, by rfl⟩ : syracuseStep 893515 = 1340273) B1340273
theorem B1778291 : Blo 790340 1778291 := bstep (se 1 (by rfl) ⟨1333718, by rfl⟩ : syracuseStep 1778291 = 2667437) B2667437
theorem B1712755 : Blo 790340 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B1188491 : Blo 790340 1188491 := bstep (se 1 (by rfl) ⟨891368, by rfl⟩ : syracuseStep 1188491 = 1782737) B1782737
theorem B1778327 : Blo 790340 1778327 := bstep (se 1 (by rfl) ⟨1333745, by rfl⟩ : syracuseStep 1778327 = 2667491) B2667491
theorem B1188503 : Blo 790340 1188503 := bstep (se 1 (by rfl) ⟨891377, by rfl⟩ : syracuseStep 1188503 = 1782755) B1782755
theorem B893623 : Blo 790340 893623 := bstep (se 1 (by rfl) ⟨670217, by rfl⟩ : syracuseStep 893623 = 1340435) B1340435
theorem B1188569 : Blo 790340 1188569 := bstep (se 2 (by rfl) ⟨445713, by rfl⟩ : syracuseStep 1188569 = 891427) B891427
theorem B3384109 : Blo 790340 3384109 := bstep (se 3 (by rfl) ⟨634520, by rfl⟩ : syracuseStep 3384109 = 1269041) B1269041
theorem B1778507 : Blo 790340 1778507 := bstep (se 1 (by rfl) ⟨1333880, by rfl⟩ : syracuseStep 1778507 = 2667761) B2667761
theorem B1188683 : Blo 790340 1188683 := bstep (se 1 (by rfl) ⟨891512, by rfl⟩ : syracuseStep 1188683 = 1783025) B1783025
theorem B1188695 : Blo 790340 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B1778561 : Blo 790340 1778561 := bstep (se 2 (by rfl) ⟨666960, by rfl⟩ : syracuseStep 1778561 = 1333921) B1333921
theorem B3810199 : Blo 790340 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B1188761 : Blo 790340 1188761 := bstep (se 2 (by rfl) ⟨445785, by rfl⟩ : syracuseStep 1188761 = 891571) B891571
theorem B8364977 : Blo 790340 8364977 := bstep (se 2 (by rfl) ⟨3136866, by rfl⟩ : syracuseStep 8364977 = 6273733) B6273733
theorem B3384281 : Blo 790340 3384281 := bstep (se 2 (by rfl) ⟨1269105, by rfl⟩ : syracuseStep 3384281 = 2538211) B2538211
theorem B1188875 : Blo 790340 1188875 := bstep (se 1 (by rfl) ⟨891656, by rfl⟩ : syracuseStep 1188875 = 1783313) B1783313
theorem B1188887 : Blo 790340 1188887 := bstep (se 1 (by rfl) ⟨891665, by rfl⟩ : syracuseStep 1188887 = 1783331) B1783331
theorem B1778777 : Blo 790340 1778777 := bstep (se 2 (by rfl) ⟨667041, by rfl⟩ : syracuseStep 1778777 = 1334083) B1334083
theorem B1188953 : Blo 790340 1188953 := bstep (se 2 (by rfl) ⟨445857, by rfl⟩ : syracuseStep 1188953 = 891715) B891715
theorem B1778867 : Blo 790340 1778867 := bstep (se 1 (by rfl) ⟨1334150, by rfl⟩ : syracuseStep 1778867 = 2668301) B2668301
theorem B1189067 : Blo 790340 1189067 := bstep (se 1 (by rfl) ⟨891800, by rfl⟩ : syracuseStep 1189067 = 1783601) B1783601
theorem B1778903 : Blo 790340 1778903 := bstep (se 1 (by rfl) ⟨1334177, by rfl⟩ : syracuseStep 1778903 = 2668355) B2668355
theorem B1189079 : Blo 790340 1189079 := bstep (se 1 (by rfl) ⟨891809, by rfl⟩ : syracuseStep 1189079 = 1783619) B1783619
theorem B3056899 : Blo 790340 3056899 := bstep (se 1 (by rfl) ⟨2292674, by rfl⟩ : syracuseStep 3056899 = 4585349) B4585349
theorem B1189145 : Blo 790340 1189145 := bstep (se 2 (by rfl) ⟨445929, by rfl⟩ : syracuseStep 1189145 = 891859) B891859
theorem B2008385 : Blo 790340 2008385 := bstep (se 2 (by rfl) ⟨753144, by rfl⟩ : syracuseStep 2008385 = 1506289) B1506289
theorem B2532701 : Blo 790340 2532701 := bstep (se 3 (by rfl) ⟨474881, by rfl⟩ : syracuseStep 2532701 = 949763) B949763
theorem B1779083 : Blo 790340 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B1189259 : Blo 790340 1189259 := bstep (se 1 (by rfl) ⟨891944, by rfl⟩ : syracuseStep 1189259 = 1783889) B1783889
theorem B43394453 : Blo 790340 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B1189271 : Blo 790340 1189271 := bstep (se 1 (by rfl) ⟨891953, by rfl⟩ : syracuseStep 1189271 = 1783907) B1783907
theorem B1779137 : Blo 790340 1779137 := bstep (se 2 (by rfl) ⟨667176, by rfl⟩ : syracuseStep 1779137 = 1334353) B1334353
theorem B1189337 : Blo 790340 1189337 := bstep (se 2 (by rfl) ⟨446001, by rfl⟩ : syracuseStep 1189337 = 892003) B892003
theorem B13936141 : Blo 790340 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B1189451 : Blo 790340 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B1189463 : Blo 790340 1189463 := bstep (se 1 (by rfl) ⟨892097, by rfl⟩ : syracuseStep 1189463 = 1784195) B1784195
theorem B4007555 : Blo 790340 4007555 := bstep (se 1 (by rfl) ⟨3005666, by rfl⟩ : syracuseStep 4007555 = 6011333) B6011333
theorem B1779353 : Blo 790340 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B1189529 : Blo 790340 1189529 := bstep (se 2 (by rfl) ⟨446073, by rfl⟩ : syracuseStep 1189529 = 892147) B892147
theorem B1779443 : Blo 790340 1779443 := bstep (se 1 (by rfl) ⟨1334582, by rfl⟩ : syracuseStep 1779443 = 2669165) B2669165
theorem B1189643 : Blo 790340 1189643 := bstep (se 1 (by rfl) ⟨892232, by rfl⟩ : syracuseStep 1189643 = 1784465) B1784465
theorem B1779479 : Blo 790340 1779479 := bstep (se 1 (by rfl) ⟨1334609, by rfl⟩ : syracuseStep 1779479 = 2669219) B2669219
theorem B1189655 : Blo 790340 1189655 := bstep (se 1 (by rfl) ⟨892241, by rfl⟩ : syracuseStep 1189655 = 1784483) B1784483
theorem B1189721 : Blo 790340 1189721 := bstep (se 2 (by rfl) ⟨446145, by rfl⟩ : syracuseStep 1189721 = 892291) B892291
theorem B2008921 : Blo 790340 2008921 := bstep (se 2 (by rfl) ⟨753345, by rfl⟩ : syracuseStep 2008921 = 1506691) B1506691
theorem B1779659 : Blo 790340 1779659 := bstep (se 1 (by rfl) ⟨1334744, by rfl⟩ : syracuseStep 1779659 = 2669489) B2669489
theorem B1189835 : Blo 790340 1189835 := bstep (se 1 (by rfl) ⟨892376, by rfl⟩ : syracuseStep 1189835 = 1784753) B1784753
theorem B1189847 : Blo 790340 1189847 := bstep (se 1 (by rfl) ⟨892385, by rfl⟩ : syracuseStep 1189847 = 1784771) B1784771
theorem B1779713 : Blo 790340 1779713 := bstep (se 2 (by rfl) ⟨667392, by rfl⟩ : syracuseStep 1779713 = 1334785) B1334785
theorem B1189913 : Blo 790340 1189913 := bstep (se 2 (by rfl) ⟨446217, by rfl⟩ : syracuseStep 1189913 = 892435) B892435
theorem B300394565 : Blo 790340 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B1190027 : Blo 790340 1190027 := bstep (se 1 (by rfl) ⟨892520, by rfl⟩ : syracuseStep 1190027 = 1785041) B1785041
theorem B1190039 : Blo 790340 1190039 := bstep (se 1 (by rfl) ⟨892529, by rfl⟩ : syracuseStep 1190039 = 1785059) B1785059
theorem B1779929 : Blo 790340 1779929 := bstep (se 2 (by rfl) ⟨667473, by rfl⟩ : syracuseStep 1779929 = 1334947) B1334947
theorem B1190105 : Blo 790340 1190105 := bstep (se 2 (by rfl) ⟨446289, by rfl⟩ : syracuseStep 1190105 = 892579) B892579
theorem B1780019 : Blo 790340 1780019 := bstep (se 1 (by rfl) ⟨1335014, by rfl⟩ : syracuseStep 1780019 = 2670029) B2670029
theorem B1190219 : Blo 790340 1190219 := bstep (se 1 (by rfl) ⟨892664, by rfl⟩ : syracuseStep 1190219 = 1785329) B1785329
theorem B1780055 : Blo 790340 1780055 := bstep (se 1 (by rfl) ⟨1335041, by rfl⟩ : syracuseStep 1780055 = 2670083) B2670083
theorem B1190231 : Blo 790340 1190231 := bstep (se 1 (by rfl) ⟨892673, by rfl⟩ : syracuseStep 1190231 = 1785347) B1785347
theorem B10135925 : Blo 790340 10135925 := bstep (se 5 (by rfl) ⟨475121, by rfl⟩ : syracuseStep 10135925 = 950243) B950243
theorem B1190297 : Blo 790340 1190297 := bstep (se 2 (by rfl) ⟨446361, by rfl⟩ : syracuseStep 1190297 = 892723) B892723
theorem B1780235 : Blo 790340 1780235 := bstep (se 1 (by rfl) ⟨1335176, by rfl⟩ : syracuseStep 1780235 = 2670353) B2670353
theorem B1190411 : Blo 790340 1190411 := bstep (se 1 (by rfl) ⟨892808, by rfl⟩ : syracuseStep 1190411 = 1785617) B1785617
theorem B82356749 : Blo 790340 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B1190423 : Blo 790340 1190423 := bstep (se 1 (by rfl) ⟨892817, by rfl⟩ : syracuseStep 1190423 = 1785635) B1785635
theorem B1780289 : Blo 790340 1780289 := bstep (se 2 (by rfl) ⟨667608, by rfl⟩ : syracuseStep 1780289 = 1335217) B1335217
theorem B3385921 : Blo 790340 3385921 := bstep (se 2 (by rfl) ⟨1269720, by rfl⟩ : syracuseStep 3385921 = 2539441) B2539441
theorem B1190489 : Blo 790340 1190489 := bstep (se 2 (by rfl) ⟨446433, by rfl⟩ : syracuseStep 1190489 = 892867) B892867
theorem B1354379 : Blo 790340 1354379 := bstep (se 1 (by rfl) ⟨1015784, by rfl⟩ : syracuseStep 1354379 = 2031569) B2031569
theorem B9022103 : Blo 790340 9022103 := bstep (se 1 (by rfl) ⟨6766577, by rfl⟩ : syracuseStep 9022103 = 13533155) B13533155
theorem B1190603 : Blo 790340 1190603 := bstep (se 1 (by rfl) ⟨892952, by rfl⟩ : syracuseStep 1190603 = 1785905) B1785905
theorem B1190615 : Blo 790340 1190615 := bstep (se 1 (by rfl) ⟨892961, by rfl⟩ : syracuseStep 1190615 = 1785923) B1785923
theorem B1780505 : Blo 790340 1780505 := bstep (se 2 (by rfl) ⟨667689, by rfl⟩ : syracuseStep 1780505 = 1335379) B1335379
theorem B1190681 : Blo 790340 1190681 := bstep (se 2 (by rfl) ⟨446505, by rfl⟩ : syracuseStep 1190681 = 893011) B893011
theorem B1780595 : Blo 790340 1780595 := bstep (se 1 (by rfl) ⟨1335446, by rfl⟩ : syracuseStep 1780595 = 2670893) B2670893
theorem B1190795 : Blo 790340 1190795 := bstep (se 1 (by rfl) ⟨893096, by rfl⟩ : syracuseStep 1190795 = 1786193) B1786193
theorem B1780631 : Blo 790340 1780631 := bstep (se 1 (by rfl) ⟨1335473, by rfl⟩ : syracuseStep 1780631 = 2670947) B2670947
theorem B1190807 : Blo 790340 1190807 := bstep (se 1 (by rfl) ⟨893105, by rfl⟩ : syracuseStep 1190807 = 1786211) B1786211
theorem B2861975 : Blo 790340 2861975 := bstep (se 1 (by rfl) ⟨2146481, by rfl⟩ : syracuseStep 2861975 = 4292963) B4292963
theorem B3812275 : Blo 790340 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B2010035 : Blo 790340 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B1190873 : Blo 790340 1190873 := bstep (se 2 (by rfl) ⟨446577, by rfl⟩ : syracuseStep 1190873 = 893155) B893155
theorem B1125451 : Blo 790340 1125451 := bstep (se 1 (by rfl) ⟨844088, by rfl⟩ : syracuseStep 1125451 = 1688177) B1688177
theorem B1780811 : Blo 790340 1780811 := bstep (se 1 (by rfl) ⟨1335608, by rfl⟩ : syracuseStep 1780811 = 2671217) B2671217
theorem B1190987 : Blo 790340 1190987 := bstep (se 1 (by rfl) ⟨893240, by rfl⟩ : syracuseStep 1190987 = 1786481) B1786481
theorem B1190999 : Blo 790340 1190999 := bstep (se 1 (by rfl) ⟨893249, by rfl⟩ : syracuseStep 1190999 = 1786499) B1786499
theorem B1780865 : Blo 790340 1780865 := bstep (se 2 (by rfl) ⟨667824, by rfl⟩ : syracuseStep 1780865 = 1335649) B1335649
theorem B1191065 : Blo 790340 1191065 := bstep (se 2 (by rfl) ⟨446649, by rfl⟩ : syracuseStep 1191065 = 893299) B893299
theorem B2010329 : Blo 790340 2010329 := bstep (se 2 (by rfl) ⟨753873, by rfl⟩ : syracuseStep 2010329 = 1507747) B1507747
theorem B1191179 : Blo 790340 1191179 := bstep (se 1 (by rfl) ⟨893384, by rfl⟩ : syracuseStep 1191179 = 1786769) B1786769
theorem B1191191 : Blo 790340 1191191 := bstep (se 1 (by rfl) ⟨893393, by rfl⟩ : syracuseStep 1191191 = 1786787) B1786787
theorem B1781081 : Blo 790340 1781081 := bstep (se 2 (by rfl) ⟨667905, by rfl⟩ : syracuseStep 1781081 = 1335811) B1335811
theorem B1191257 : Blo 790340 1191257 := bstep (se 2 (by rfl) ⟨446721, by rfl⟩ : syracuseStep 1191257 = 893443) B893443
theorem B1781171 : Blo 790340 1781171 := bstep (se 1 (by rfl) ⟨1335878, by rfl⟩ : syracuseStep 1781171 = 2671757) B2671757
theorem B1191371 : Blo 790340 1191371 := bstep (se 1 (by rfl) ⟨893528, by rfl⟩ : syracuseStep 1191371 = 1787057) B1787057
theorem B1781207 : Blo 790340 1781207 := bstep (se 1 (by rfl) ⟨1335905, by rfl⟩ : syracuseStep 1781207 = 2671811) B2671811
theorem B1191383 : Blo 790340 1191383 := bstep (se 1 (by rfl) ⟨893537, by rfl⟩ : syracuseStep 1191383 = 1787075) B1787075
theorem B1224215 : Blo 790340 1224215 := bstep (se 1 (by rfl) ⟨918161, by rfl⟩ : syracuseStep 1224215 = 1836323) B1836323
theorem B1191449 : Blo 790340 1191449 := bstep (se 2 (by rfl) ⟨446793, by rfl⟩ : syracuseStep 1191449 = 893587) B893587
theorem B1781387 : Blo 790340 1781387 := bstep (se 1 (by rfl) ⟨1336040, by rfl⟩ : syracuseStep 1781387 = 2672081) B2672081
theorem B1781441 : Blo 790340 1781441 := bstep (se 2 (by rfl) ⟨668040, by rfl⟩ : syracuseStep 1781441 = 1336081) B1336081
theorem B1781657 : Blo 790340 1781657 := bstep (se 2 (by rfl) ⟨668121, by rfl⟩ : syracuseStep 1781657 = 1336243) B1336243
theorem B1781747 : Blo 790340 1781747 := bstep (se 1 (by rfl) ⟨1336310, by rfl⟩ : syracuseStep 1781747 = 2672621) B2672621
theorem B1781783 : Blo 790340 1781783 := bstep (se 1 (by rfl) ⟨1336337, by rfl⟩ : syracuseStep 1781783 = 2672675) B2672675
theorem B4075699 : Blo 790340 4075699 := bstep (se 1 (by rfl) ⟨3056774, by rfl⟩ : syracuseStep 4075699 = 6113549) B6113549
theorem B1781963 : Blo 790340 1781963 := bstep (se 1 (by rfl) ⟨1336472, by rfl⟩ : syracuseStep 1781963 = 2672945) B2672945
theorem B3387595 : Blo 790340 3387595 := bstep (se 1 (by rfl) ⟨2540696, by rfl⟩ : syracuseStep 3387595 = 5081393) B5081393
theorem B1782017 : Blo 790340 1782017 := bstep (se 2 (by rfl) ⟨668256, by rfl⟩ : syracuseStep 1782017 = 1336513) B1336513
theorem B4501939 : Blo 790340 4501939 := bstep (se 1 (by rfl) ⟨3376454, by rfl⟩ : syracuseStep 4501939 = 6752909) B6752909
theorem B1782233 : Blo 790340 1782233 := bstep (se 2 (by rfl) ⟨668337, by rfl⟩ : syracuseStep 1782233 = 1336675) B1336675
theorem B3387869 : Blo 790340 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B6009389 : Blo 790340 6009389 := bstep (se 3 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 6009389 = 2253521) B2253521
theorem B1782323 : Blo 790340 1782323 := bstep (se 1 (by rfl) ⟨1336742, by rfl⟩ : syracuseStep 1782323 = 2673485) B2673485
theorem B1782359 : Blo 790340 1782359 := bstep (se 1 (by rfl) ⟨1336769, by rfl⟩ : syracuseStep 1782359 = 2673539) B2673539
theorem B1782539 : Blo 790340 1782539 := bstep (se 1 (by rfl) ⟨1336904, by rfl⟩ : syracuseStep 1782539 = 2673809) B2673809
theorem B1782593 : Blo 790340 1782593 := bstep (se 2 (by rfl) ⟨668472, by rfl⟩ : syracuseStep 1782593 = 1336945) B1336945
theorem B1487809 : Blo 790340 1487809 := bstep (se 2 (by rfl) ⟨557928, by rfl⟩ : syracuseStep 1487809 = 1115857) B1115857
theorem B2175947 : Blo 790340 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1782809 : Blo 790340 1782809 := bstep (se 2 (by rfl) ⟨668553, by rfl⟩ : syracuseStep 1782809 = 1337107) B1337107
theorem B3519533 : Blo 790340 3519533 := bstep (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) B1319825
theorem B1782899 : Blo 790340 1782899 := bstep (se 1 (by rfl) ⟨1337174, by rfl⟩ : syracuseStep 1782899 = 2674349) B2674349
theorem B1782935 : Blo 790340 1782935 := bstep (se 1 (by rfl) ⟨1337201, by rfl⟩ : syracuseStep 1782935 = 2674403) B2674403
theorem B4011281 : Blo 790340 4011281 := bstep (se 2 (by rfl) ⟨1504230, by rfl⟩ : syracuseStep 4011281 = 3008461) B3008461
theorem B1783115 : Blo 790340 1783115 := bstep (se 1 (by rfl) ⟨1337336, by rfl⟩ : syracuseStep 1783115 = 2674673) B2674673
theorem B2667869 : Blo 790340 2667869 := bstep (se 3 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 2667869 = 1000451) B1000451
theorem B1783169 : Blo 790340 1783169 := bstep (se 2 (by rfl) ⟨668688, by rfl⟩ : syracuseStep 1783169 = 1337377) B1337377
theorem B4011443 : Blo 790340 4011443 := bstep (se 1 (by rfl) ⟨3008582, by rfl⟩ : syracuseStep 4011443 = 6017165) B6017165
theorem B1783385 : Blo 790340 1783385 := bstep (se 2 (by rfl) ⟨668769, by rfl⟩ : syracuseStep 1783385 = 1337539) B1337539
theorem B11417219 : Blo 790340 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B1783475 : Blo 790340 1783475 := bstep (se 1 (by rfl) ⟨1337606, by rfl⟩ : syracuseStep 1783475 = 2675213) B2675213
theorem B1783511 : Blo 790340 1783511 := bstep (se 1 (by rfl) ⟨1337633, by rfl⟩ : syracuseStep 1783511 = 2675267) B2675267
theorem B4503397 : Blo 790340 4503397 := bstep (se 4 (by rfl) ⟨422193, by rfl⟩ : syracuseStep 4503397 = 844387) B844387
theorem B1783691 : Blo 790340 1783691 := bstep (se 1 (by rfl) ⟨1337768, by rfl⟩ : syracuseStep 1783691 = 2675537) B2675537
theorem B2144179 : Blo 790340 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B1783745 : Blo 790340 1783745 := bstep (se 2 (by rfl) ⟨668904, by rfl⟩ : syracuseStep 1783745 = 1337809) B1337809
theorem B1783961 : Blo 790340 1783961 := bstep (se 2 (by rfl) ⟨668985, by rfl⟩ : syracuseStep 1783961 = 1337971) B1337971
theorem B1784051 : Blo 790340 1784051 := bstep (se 1 (by rfl) ⟨1338038, by rfl⟩ : syracuseStep 1784051 = 2676077) B2676077
theorem B1784087 : Blo 790340 1784087 := bstep (se 1 (by rfl) ⟨1338065, by rfl⟩ : syracuseStep 1784087 = 2676131) B2676131
theorem B2669003 : Blo 790340 2669003 := bstep (se 1 (by rfl) ⟨2001752, by rfl⟩ : syracuseStep 2669003 = 4003505) B4003505
theorem B1784267 : Blo 790340 1784267 := bstep (se 1 (by rfl) ⟨1338200, by rfl⟩ : syracuseStep 1784267 = 2676401) B2676401
theorem B1784321 : Blo 790340 1784321 := bstep (se 2 (by rfl) ⟨669120, by rfl⟩ : syracuseStep 1784321 = 1338241) B1338241
theorem B1522199 : Blo 790340 1522199 := bstep (se 1 (by rfl) ⟨1141649, by rfl⟩ : syracuseStep 1522199 = 2283299) B2283299
theorem B2669273 : Blo 790340 2669273 := bstep (se 2 (by rfl) ⟨1000977, by rfl⟩ : syracuseStep 2669273 = 2001955) B2001955
theorem B1784537 : Blo 790340 1784537 := bstep (se 2 (by rfl) ⟨669201, by rfl⟩ : syracuseStep 1784537 = 1338403) B1338403
theorem B1784627 : Blo 790340 1784627 := bstep (se 1 (by rfl) ⟨1338470, by rfl⟩ : syracuseStep 1784627 = 2676941) B2676941
theorem B15448897 : Blo 790340 15448897 := bstep (se 2 (by rfl) ⟨5793336, by rfl⟩ : syracuseStep 15448897 = 11586673) B11586673
theorem B801623 : Blo 790340 801623 := bstep (se 1 (by rfl) ⟨601217, by rfl⟩ : syracuseStep 801623 = 1202435) B1202435
theorem B1784663 : Blo 790340 1784663 := bstep (se 1 (by rfl) ⟨1338497, by rfl⟩ : syracuseStep 1784663 = 2676995) B2676995
theorem B2145217 : Blo 790340 2145217 := bstep (se 2 (by rfl) ⟨804456, by rfl⟩ : syracuseStep 2145217 = 1608913) B1608913
theorem B1784843 : Blo 790340 1784843 := bstep (se 1 (by rfl) ⟨1338632, by rfl⟩ : syracuseStep 1784843 = 2677265) B2677265
theorem B1784897 : Blo 790340 1784897 := bstep (se 2 (by rfl) ⟨669336, by rfl⟩ : syracuseStep 1784897 = 1338673) B1338673
theorem B2538647 : Blo 790340 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B801995 : Blo 790340 801995 := bstep (se 1 (by rfl) ⟨601496, by rfl⟩ : syracuseStep 801995 = 1202993) B1202993
theorem B1785113 : Blo 790340 1785113 := bstep (se 2 (by rfl) ⟨669417, by rfl⟩ : syracuseStep 1785113 = 1338835) B1338835
theorem B2538827 : Blo 790340 2538827 := bstep (se 1 (by rfl) ⟨1904120, by rfl⟩ : syracuseStep 2538827 = 3808241) B3808241
theorem B4013387 : Blo 790340 4013387 := bstep (se 1 (by rfl) ⟨3010040, by rfl⟩ : syracuseStep 4013387 = 6020081) B6020081
theorem B1785203 : Blo 790340 1785203 := bstep (se 1 (by rfl) ⟨1338902, by rfl⟩ : syracuseStep 1785203 = 2677805) B2677805
theorem B2669975 : Blo 790340 2669975 := bstep (se 1 (by rfl) ⟨2002481, by rfl⟩ : syracuseStep 2669975 = 4004963) B4004963
theorem B1785239 : Blo 790340 1785239 := bstep (se 1 (by rfl) ⟨1338929, by rfl⟩ : syracuseStep 1785239 = 2677859) B2677859
theorem B1129945 : Blo 790340 1129945 := bstep (se 2 (by rfl) ⟨423729, by rfl⟩ : syracuseStep 1129945 = 847459) B847459
theorem B1785419 : Blo 790340 1785419 := bstep (se 1 (by rfl) ⟨1339064, by rfl⟩ : syracuseStep 1785419 = 2678129) B2678129
theorem B2539097 : Blo 790340 2539097 := bstep (se 2 (by rfl) ⟨952161, by rfl⟩ : syracuseStep 2539097 = 1904323) B1904323
theorem B1785473 : Blo 790340 1785473 := bstep (se 2 (by rfl) ⟨669552, by rfl⟩ : syracuseStep 1785473 = 1339105) B1339105
theorem B1785689 : Blo 790340 1785689 := bstep (se 2 (by rfl) ⟨669633, by rfl⟩ : syracuseStep 1785689 = 1339267) B1339267
theorem B10305397 : Blo 790340 10305397 := bstep (se 5 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 10305397 = 966131) B966131
theorem B2670515 : Blo 790340 2670515 := bstep (se 1 (by rfl) ⟨2002886, by rfl⟩ : syracuseStep 2670515 = 4005773) B4005773
theorem B1785779 : Blo 790340 1785779 := bstep (se 1 (by rfl) ⟨1339334, by rfl⟩ : syracuseStep 1785779 = 2678669) B2678669
theorem B3620801 : Blo 790340 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B1785815 : Blo 790340 1785815 := bstep (se 1 (by rfl) ⟨1339361, by rfl⟩ : syracuseStep 1785815 = 2678723) B2678723
theorem B2146265 : Blo 790340 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B1785995 : Blo 790340 1785995 := bstep (se 1 (by rfl) ⟨1339496, by rfl⟩ : syracuseStep 1785995 = 2678993) B2678993
theorem B2670785 : Blo 790340 2670785 := bstep (se 2 (by rfl) ⟨1001544, by rfl⟩ : syracuseStep 2670785 = 2003089) B2003089
theorem B1786049 : Blo 790340 1786049 := bstep (se 2 (by rfl) ⟨669768, by rfl⟩ : syracuseStep 1786049 = 1339537) B1339537
theorem B2572505 : Blo 790340 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B6013277 : Blo 790340 6013277 := bstep (se 3 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 6013277 = 2254979) B2254979
theorem B2539927 : Blo 790340 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B1786265 : Blo 790340 1786265 := bstep (se 2 (by rfl) ⟨669849, by rfl⟩ : syracuseStep 1786265 = 1339699) B1339699
theorem B1786355 : Blo 790340 1786355 := bstep (se 1 (by rfl) ⟨1339766, by rfl⟩ : syracuseStep 1786355 = 2679533) B2679533
theorem B1786391 : Blo 790340 1786391 := bstep (se 1 (by rfl) ⟨1339793, by rfl⟩ : syracuseStep 1786391 = 2679587) B2679587
theorem B1786571 : Blo 790340 1786571 := bstep (se 1 (by rfl) ⟨1339928, by rfl⟩ : syracuseStep 1786571 = 2679857) B2679857
theorem B2671325 : Blo 790340 2671325 := bstep (se 3 (by rfl) ⟨500873, by rfl⟩ : syracuseStep 2671325 = 1001747) B1001747
theorem B1786625 : Blo 790340 1786625 := bstep (se 2 (by rfl) ⟨669984, by rfl⟩ : syracuseStep 1786625 = 1339969) B1339969
theorem B1000279 : Blo 790340 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B1786841 : Blo 790340 1786841 := bstep (se 2 (by rfl) ⟨670065, by rfl⟩ : syracuseStep 1786841 = 1340131) B1340131
theorem B6177809 : Blo 790340 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B1786931 : Blo 790340 1786931 := bstep (se 1 (by rfl) ⟨1340198, by rfl⟩ : syracuseStep 1786931 = 2680397) B2680397
theorem B4015169 : Blo 790340 4015169 := bstep (se 2 (by rfl) ⟨1505688, by rfl⟩ : syracuseStep 4015169 = 3011377) B3011377
theorem B1786967 : Blo 790340 1786967 := bstep (se 1 (by rfl) ⟨1340225, by rfl⟩ : syracuseStep 1786967 = 2680451) B2680451
theorem B2704535 : Blo 790340 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B3392705 : Blo 790340 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B1688843 : Blo 790340 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B1787147 : Blo 790340 1787147 := bstep (se 1 (by rfl) ⟨1340360, by rfl⟩ : syracuseStep 1787147 = 2680721) B2680721
theorem B1787201 : Blo 790340 1787201 := bstep (se 2 (by rfl) ⟨670200, by rfl⟩ : syracuseStep 1787201 = 1340401) B1340401
theorem B3392857 : Blo 790340 3392857 := bstep (se 2 (by rfl) ⟨1272321, by rfl⟩ : syracuseStep 3392857 = 2544643) B2544643
theorem B2541107 : Blo 790340 2541107 := bstep (se 1 (by rfl) ⟨1905830, by rfl⟩ : syracuseStep 2541107 = 3811661) B3811661
theorem B1001099 : Blo 790340 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B1427095 : Blo 790340 1427095 := bstep (se 1 (by rfl) ⟨1070321, by rfl⟩ : syracuseStep 1427095 = 2140643) B2140643
theorem B2672459 : Blo 790340 2672459 := bstep (se 1 (by rfl) ⟨2004344, by rfl⟩ : syracuseStep 2672459 = 4008689) B4008689
theorem B2672729 : Blo 790340 2672729 := bstep (se 2 (by rfl) ⟨1002273, by rfl⟩ : syracuseStep 2672729 = 2004547) B2004547
theorem B1689817 : Blo 790340 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B1001803 : Blo 790340 1001803 := bstep (se 1 (by rfl) ⟨751352, by rfl⟩ : syracuseStep 1001803 = 1502705) B1502705
theorem B1690073 : Blo 790340 1690073 := bstep (se 2 (by rfl) ⟨633777, by rfl⟩ : syracuseStep 1690073 = 1267555) B1267555
theorem B1002071 : Blo 790340 1002071 := bstep (se 1 (by rfl) ⟨751553, by rfl⟩ : syracuseStep 1002071 = 1503107) B1503107
theorem B2673431 : Blo 790340 2673431 := bstep (se 1 (by rfl) ⟨2005073, by rfl⟩ : syracuseStep 2673431 = 4010147) B4010147
theorem B1690483 : Blo 790340 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B4017113 : Blo 790340 4017113 := bstep (se 2 (by rfl) ⟨1506417, by rfl⟩ : syracuseStep 4017113 = 3012835) B3012835
theorem B3001475 : Blo 790340 3001475 := bstep (se 1 (by rfl) ⟨2251106, by rfl⟩ : syracuseStep 3001475 = 4502213) B4502213
theorem B9784451 : Blo 790340 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B1002775 : Blo 790340 1002775 := bstep (se 1 (by rfl) ⟨752081, by rfl⟩ : syracuseStep 1002775 = 1504163) B1504163
theorem B1428761 : Blo 790340 1428761 := bstep (se 2 (by rfl) ⟨535785, by rfl⟩ : syracuseStep 1428761 = 1071571) B1071571
theorem B2673971 : Blo 790340 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B1527155 : Blo 790340 1527155 := bstep (se 1 (by rfl) ⟨1145366, by rfl⟩ : syracuseStep 1527155 = 2290733) B2290733
theorem B1625483 : Blo 790340 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B4574681 : Blo 790340 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B5721617 : Blo 790340 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B4509229 : Blo 790340 4509229 := bstep (se 3 (by rfl) ⟨845480, by rfl⟩ : syracuseStep 4509229 = 1690961) B1690961
theorem B1691201 : Blo 790340 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B2674241 : Blo 790340 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B3001931 : Blo 790340 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B2543197 : Blo 790340 2543197 := bstep (se 3 (by rfl) ⟨476849, by rfl⟩ : syracuseStep 2543197 = 953699) B953699
theorem B3002129 : Blo 790340 3002129 := bstep (se 2 (by rfl) ⟨1125798, by rfl⟩ : syracuseStep 3002129 = 2251597) B2251597
theorem B1691543 : Blo 790340 1691543 := bstep (se 1 (by rfl) ⟨1268657, by rfl⟩ : syracuseStep 1691543 = 2537315) B2537315
theorem B1691713 : Blo 790340 1691713 := bstep (se 2 (by rfl) ⟨634392, by rfl⟩ : syracuseStep 1691713 = 1268785) B1268785
theorem B2674781 : Blo 790340 2674781 := bstep (se 3 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 2674781 = 1003043) B1003043
theorem B3002903 : Blo 790340 3002903 := bstep (se 1 (by rfl) ⟨2252177, by rfl⟩ : syracuseStep 3002903 = 4504355) B4504355
theorem B4018733 : Blo 790340 4018733 := bstep (se 3 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 4018733 = 1507025) B1507025
theorem B3003101 : Blo 790340 3003101 := bstep (se 3 (by rfl) ⟨563081, by rfl⟩ : syracuseStep 3003101 = 1126163) B1126163
theorem B1069975 : Blo 790340 1069975 := bstep (se 1 (by rfl) ⟨802481, by rfl⟩ : syracuseStep 1069975 = 1604963) B1604963
theorem B1004491 : Blo 790340 1004491 := bstep (se 1 (by rfl) ⟨753368, by rfl⟩ : syracuseStep 1004491 = 1506737) B1506737
theorem B2675915 : Blo 790340 2675915 := bstep (se 1 (by rfl) ⟨2006936, by rfl⟩ : syracuseStep 2675915 = 4013873) B4013873
theorem B1692875 : Blo 790340 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B2676185 : Blo 790340 2676185 := bstep (se 2 (by rfl) ⟨1003569, by rfl⟩ : syracuseStep 2676185 = 2007139) B2007139
theorem B1201753 : Blo 790340 1201753 := bstep (se 2 (by rfl) ⟨450657, by rfl⟩ : syracuseStep 1201753 = 901315) B901315
theorem B1693619 : Blo 790340 1693619 := bstep (se 1 (by rfl) ⟨1270214, by rfl⟩ : syracuseStep 1693619 = 2540429) B2540429
theorem B9656243 : Blo 790340 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B2414539 : Blo 790340 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B2709469 : Blo 790340 2709469 := bstep (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) B1016051
theorem B21649477 : Blo 790340 21649477 := bstep (se 4 (by rfl) ⟨2029638, by rfl⟩ : syracuseStep 21649477 = 4059277) B4059277
theorem B2676887 : Blo 790340 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B1267991 : Blo 790340 1267991 := bstep (se 1 (by rfl) ⟨950993, by rfl⟩ : syracuseStep 1267991 = 1901987) B1901987
theorem B1268183 : Blo 790340 1268183 := bstep (se 1 (by rfl) ⟨951137, by rfl⟩ : syracuseStep 1268183 = 1902275) B1902275
theorem B4282841 : Blo 790340 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B1333847 : Blo 790340 1333847 := bstep (se 1 (by rfl) ⟨1000385, by rfl⟩ : syracuseStep 1333847 = 2000771) B2000771
theorem B3005059 : Blo 790340 3005059 := bstep (se 1 (by rfl) ⟨2253794, by rfl⟩ : syracuseStep 3005059 = 4507589) B4507589
theorem B2251415 : Blo 790340 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B2677427 : Blo 790340 2677427 := bstep (se 1 (by rfl) ⟨2008070, by rfl⟩ : syracuseStep 2677427 = 4016141) B4016141
theorem B1333975 : Blo 790340 1333975 := bstep (se 1 (by rfl) ⟨1000481, by rfl⟩ : syracuseStep 1333975 = 2000963) B2000963
theorem B1694515 : Blo 790340 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B32889653 : Blo 790340 32889653 := bstep (se 5 (by rfl) ⟨1541702, by rfl⟩ : syracuseStep 32889653 = 3083405) B3083405
theorem B3005363 : Blo 790340 3005363 := bstep (se 1 (by rfl) ⟨2254022, by rfl⟩ : syracuseStep 3005363 = 4508045) B4508045
theorem B2677697 : Blo 790340 2677697 := bstep (se 2 (by rfl) ⟨1004136, by rfl⟩ : syracuseStep 2677697 = 2008273) B2008273
theorem B5233709 : Blo 790340 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B7625933 : Blo 790340 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B5790937 : Blo 790340 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B7232813 : Blo 790340 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B1334603 : Blo 790340 1334603 := bstep (se 1 (by rfl) ⟨1000952, by rfl⟩ : syracuseStep 1334603 = 2001905) B2001905
theorem B1334731 : Blo 790340 1334731 := bstep (se 1 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 1334731 = 2002097) B2002097
theorem B9035225 : Blo 790340 9035225 := bstep (se 2 (by rfl) ⟨3388209, by rfl⟩ : syracuseStep 9035225 = 6776419) B6776419
theorem B2678237 : Blo 790340 2678237 := bstep (se 3 (by rfl) ⟨502169, by rfl⟩ : syracuseStep 2678237 = 1004339) B1004339
theorem B3006017 : Blo 790340 3006017 := bstep (se 2 (by rfl) ⟨1127256, by rfl⟩ : syracuseStep 3006017 = 2254513) B2254513
theorem B5791297 : Blo 790340 5791297 := bstep (se 2 (by rfl) ⟨2171736, by rfl⟩ : syracuseStep 5791297 = 4343473) B4343473
theorem B1334873 : Blo 790340 1334873 := bstep (se 2 (by rfl) ⟨500577, by rfl⟩ : syracuseStep 1334873 = 1001155) B1001155
theorem B1269451 : Blo 790340 1269451 := bstep (se 1 (by rfl) ⟨952088, by rfl⟩ : syracuseStep 1269451 = 1904177) B1904177
theorem B1335001 : Blo 790340 1335001 := bstep (se 2 (by rfl) ⟨500625, by rfl⟩ : syracuseStep 1335001 = 1001251) B1001251
theorem B1695575 : Blo 790340 1695575 := bstep (se 1 (by rfl) ⟨1271681, by rfl⟩ : syracuseStep 1695575 = 2543363) B2543363
theorem B2252747 : Blo 790340 2252747 := bstep (se 1 (by rfl) ⟨1689560, by rfl⟩ : syracuseStep 2252747 = 3379121) B3379121
theorem B1695745 : Blo 790340 1695745 := bstep (se 2 (by rfl) ⟨635904, by rfl⟩ : syracuseStep 1695745 = 1271809) B1271809
theorem B4808855 : Blo 790340 4808855 := bstep (se 1 (by rfl) ⟨3606641, by rfl⟩ : syracuseStep 4808855 = 7213283) B7213283
theorem B1269913 : Blo 790340 1269913 := bstep (se 2 (by rfl) ⟨476217, by rfl⟩ : syracuseStep 1269913 = 952435) B952435
theorem B1335575 : Blo 790340 1335575 := bstep (se 1 (by rfl) ⟨1001681, by rfl⟩ : syracuseStep 1335575 = 2003363) B2003363
theorem B1696087 : Blo 790340 1696087 := bstep (se 1 (by rfl) ⟨1272065, by rfl⟩ : syracuseStep 1696087 = 2544131) B2544131
theorem B1335703 : Blo 790340 1335703 := bstep (se 1 (by rfl) ⟨1001777, by rfl⟩ : syracuseStep 1335703 = 2003555) B2003555
theorem B1270169 : Blo 790340 1270169 := bstep (se 2 (by rfl) ⟨476313, by rfl⟩ : syracuseStep 1270169 = 952627) B952627
theorem B2679371 : Blo 790340 2679371 := bstep (se 1 (by rfl) ⟨2009528, by rfl⟩ : syracuseStep 2679371 = 4019057) B4019057
theorem B3007277 : Blo 790340 3007277 := bstep (se 3 (by rfl) ⟨563864, by rfl⟩ : syracuseStep 3007277 = 1127729) B1127729
theorem B3007307 : Blo 790340 3007307 := bstep (se 1 (by rfl) ⟨2255480, by rfl⟩ : syracuseStep 3007307 = 4510961) B4510961
theorem B2679641 : Blo 790340 2679641 := bstep (se 2 (by rfl) ⟨1004865, by rfl⟩ : syracuseStep 2679641 = 2009731) B2009731
theorem B844759 : Blo 790340 844759 := bstep (se 1 (by rfl) ⟨633569, by rfl⟩ : syracuseStep 844759 = 1267139) B1267139
theorem B1336331 : Blo 790340 1336331 := bstep (se 1 (by rfl) ⟨1002248, by rfl⟩ : syracuseStep 1336331 = 2004497) B2004497
theorem B1336459 : Blo 790340 1336459 := bstep (se 1 (by rfl) ⟨1002344, by rfl⟩ : syracuseStep 1336459 = 2004689) B2004689
theorem B3433751 : Blo 790340 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B1336601 : Blo 790340 1336601 := bstep (se 2 (by rfl) ⟨501225, by rfl⟩ : syracuseStep 1336601 = 1002451) B1002451
theorem B1336729 : Blo 790340 1336729 := bstep (se 2 (by rfl) ⟨501273, by rfl⟩ : syracuseStep 1336729 = 1002547) B1002547
theorem B3007961 : Blo 790340 3007961 := bstep (se 2 (by rfl) ⟨1127985, by rfl⟩ : syracuseStep 3007961 = 2255971) B2255971
theorem B2680343 : Blo 790340 2680343 := bstep (se 1 (by rfl) ⟨2010257, by rfl⟩ : syracuseStep 2680343 = 4020515) B4020515
theorem B2254387 : Blo 790340 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B1500761 : Blo 790340 1500761 := bstep (se 2 (by rfl) ⟨562785, by rfl⟩ : syracuseStep 1500761 = 1125571) B1125571
theorem B845515 : Blo 790340 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B3008279 : Blo 790340 3008279 := bstep (se 1 (by rfl) ⟨2256209, by rfl⟩ : syracuseStep 3008279 = 4512419) B4512419
theorem B1337303 : Blo 790340 1337303 := bstep (se 1 (by rfl) ⟨1002977, by rfl⟩ : syracuseStep 1337303 = 2005955) B2005955
theorem B1206295 : Blo 790340 1206295 := bstep (se 1 (by rfl) ⟨904721, by rfl⟩ : syracuseStep 1206295 = 1809443) B1809443
theorem B5433389 : Blo 790340 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B2680883 : Blo 790340 2680883 := bstep (se 1 (by rfl) ⟨2010662, by rfl⟩ : syracuseStep 2680883 = 4021325) B4021325
theorem B1337431 : Blo 790340 1337431 := bstep (se 1 (by rfl) ⟨1003073, by rfl⟩ : syracuseStep 1337431 = 2006147) B2006147
theorem B4810853 : Blo 790340 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B4516019 : Blo 790340 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B3008947 : Blo 790340 3008947 := bstep (se 1 (by rfl) ⟨2256710, by rfl⟩ : syracuseStep 3008947 = 4513421) B4513421
theorem B2255435 : Blo 790340 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B1338059 : Blo 790340 1338059 := bstep (se 1 (by rfl) ⟨1003544, by rfl⟩ : syracuseStep 1338059 = 2007089) B2007089
theorem B1338187 : Blo 790340 1338187 := bstep (se 1 (by rfl) ⟨1003640, by rfl⟩ : syracuseStep 1338187 = 2007281) B2007281
theorem B1338329 : Blo 790340 1338329 := bstep (se 2 (by rfl) ⟨501873, by rfl⟩ : syracuseStep 1338329 = 1003747) B1003747
theorem B1502219 : Blo 790340 1502219 := bstep (se 1 (by rfl) ⟨1126664, by rfl⟩ : syracuseStep 1502219 = 2253329) B2253329
theorem B1338457 : Blo 790340 1338457 := bstep (se 2 (by rfl) ⟨501921, by rfl⟩ : syracuseStep 1338457 = 1003843) B1003843
theorem B1502401 : Blo 790340 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B6778403 : Blo 790340 6778403 := bstep (se 1 (by rfl) ⟨5083802, by rfl⟩ : syracuseStep 6778403 = 10167605) B10167605
theorem B4517477 : Blo 790340 4517477 := bstep (se 4 (by rfl) ⟨423513, by rfl⟩ : syracuseStep 4517477 = 847027) B847027
theorem B1502849 : Blo 790340 1502849 := bstep (se 2 (by rfl) ⟨563568, by rfl⟩ : syracuseStep 1502849 = 1127137) B1127137
theorem B3010193 : Blo 790340 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1339031 : Blo 790340 1339031 := bstep (se 1 (by rfl) ⟨1004273, by rfl⟩ : syracuseStep 1339031 = 2008547) B2008547
theorem B847531 : Blo 790340 847531 := bstep (se 1 (by rfl) ⟨635648, by rfl⟩ : syracuseStep 847531 = 1271297) B1271297
theorem B13528781 : Blo 790340 13528781 := bstep (se 3 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 13528781 = 5073293) B5073293
theorem B1339159 : Blo 790340 1339159 := bstep (se 1 (by rfl) ⟨1004369, by rfl⟩ : syracuseStep 1339159 = 2008739) B2008739
theorem B1503191 : Blo 790340 1503191 := bstep (se 1 (by rfl) ⟨1127393, by rfl⟩ : syracuseStep 1503191 = 2254787) B2254787
theorem B6090713 : Blo 790340 6090713 := bstep (se 2 (by rfl) ⟨2284017, by rfl⟩ : syracuseStep 6090713 = 4568035) B4568035
theorem B7336037 : Blo 790340 7336037 := bstep (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) B1375507
theorem B2257075 : Blo 790340 2257075 := bstep (se 1 (by rfl) ⟨1692806, by rfl⟩ : syracuseStep 2257075 = 3385613) B3385613
theorem B6779153 : Blo 790340 6779153 := bstep (se 2 (by rfl) ⟨2542182, by rfl⟩ : syracuseStep 6779153 = 5084365) B5084365
theorem B3010891 : Blo 790340 3010891 := bstep (se 1 (by rfl) ⟨2258168, by rfl⟩ : syracuseStep 3010891 = 4516337) B4516337
theorem B2748761 : Blo 790340 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B1339787 : Blo 790340 1339787 := bstep (se 1 (by rfl) ⟨1004840, by rfl⟩ : syracuseStep 1339787 = 2009681) B2009681
theorem B2257303 : Blo 790340 2257303 := bstep (se 1 (by rfl) ⟨1692977, by rfl⟩ : syracuseStep 2257303 = 3385955) B3385955
theorem B1339915 : Blo 790340 1339915 := bstep (se 1 (by rfl) ⟨1004936, by rfl⟩ : syracuseStep 1339915 = 2009873) B2009873
theorem B3011165 : Blo 790340 3011165 := bstep (se 3 (by rfl) ⟨564593, by rfl⟩ : syracuseStep 3011165 = 1129187) B1129187
theorem B1503859 : Blo 790340 1503859 := bstep (se 1 (by rfl) ⟨1127894, by rfl⟩ : syracuseStep 1503859 = 2255789) B2255789
theorem B1340057 : Blo 790340 1340057 := bstep (se 2 (by rfl) ⟨502521, by rfl⟩ : syracuseStep 1340057 = 1005043) B1005043
theorem B3666653 : Blo 790340 3666653 := bstep (se 3 (by rfl) ⟨687497, by rfl⟩ : syracuseStep 3666653 = 1374995) B1374995
theorem B1340185 : Blo 790340 1340185 := bstep (se 2 (by rfl) ⟨502569, by rfl⟩ : syracuseStep 1340185 = 1005139) B1005139
theorem B8549165 : Blo 790340 8549165 := bstep (se 3 (by rfl) ⟨1602968, by rfl⟩ : syracuseStep 8549165 = 3205937) B3205937
theorem B24343361 : Blo 790340 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B815959 : Blo 790340 815959 := bstep (se 1 (by rfl) ⟨611969, by rfl⟩ : syracuseStep 815959 = 1223939) B1223939
theorem B1602433 : Blo 790340 1602433 := bstep (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) B1201825
theorem B1504307 : Blo 790340 1504307 := bstep (se 1 (by rfl) ⟨1128230, by rfl⟩ : syracuseStep 1504307 = 2256461) B2256461
theorem B1504345 : Blo 790340 1504345 := bstep (se 2 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 1504345 = 1128259) B1128259
theorem B1602775 : Blo 790340 1602775 := bstep (se 1 (by rfl) ⟨1202081, by rfl⟩ : syracuseStep 1602775 = 2404163) B2404163
theorem B3011863 : Blo 790340 3011863 := bstep (se 1 (by rfl) ⟨2258897, by rfl⟩ : syracuseStep 3011863 = 4517795) B4517795
theorem B5076269 : Blo 790340 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B1504793 : Blo 790340 1504793 := bstep (se 2 (by rfl) ⟨564297, by rfl⟩ : syracuseStep 1504793 = 1128595) B1128595
theorem B1603147 : Blo 790340 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B3012653 : Blo 790340 3012653 := bstep (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) B1129745
theorem B2259161 : Blo 790340 2259161 := bstep (se 2 (by rfl) ⟨847185, by rfl⟩ : syracuseStep 2259161 = 1694371) B1694371
theorem B1505537 : Blo 790340 1505537 := bstep (se 2 (by rfl) ⟨564576, by rfl⟩ : syracuseStep 1505537 = 1129153) B1129153
theorem B14448901 : Blo 790340 14448901 := bstep (se 4 (by rfl) ⟨1354584, by rfl⟩ : syracuseStep 14448901 = 2709169) B2709169
theorem B3209537 : Blo 790340 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B3045725 : Blo 790340 3045725 := bstep (se 3 (by rfl) ⟨571073, by rfl⟩ : syracuseStep 3045725 = 1142147) B1142147
theorem B1505803 : Blo 790340 1505803 := bstep (se 1 (by rfl) ⟨1129352, by rfl⟩ : syracuseStep 1505803 = 2258705) B2258705
theorem B7600715 : Blo 790340 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B1014487 : Blo 790340 1014487 := bstep (se 1 (by rfl) ⟨760865, by rfl⟩ : syracuseStep 1014487 = 1521731) B1521731
theorem B11598709 : Blo 790340 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B1506251 : Blo 790340 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B2259991 : Blo 790340 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B2849867 : Blo 790340 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B1506433 : Blo 790340 1506433 := bstep (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) B1129825
theorem B6782129 : Blo 790340 6782129 := bstep (se 2 (by rfl) ⟨2543298, by rfl⟩ : syracuseStep 6782129 = 5086597) B5086597
theorem B1604915 : Blo 790340 1604915 := bstep (se 1 (by rfl) ⟨1203686, by rfl⟩ : syracuseStep 1604915 = 2407373) B2407373
theorem B3014081 : Blo 790340 3014081 := bstep (se 2 (by rfl) ⟨1130280, by rfl⟩ : syracuseStep 3014081 = 2260561) B2260561
theorem B1506775 : Blo 790340 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B7241309 : Blo 790340 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B4292227 : Blo 790340 4292227 := bstep (se 1 (by rfl) ⟨3219170, by rfl⟩ : syracuseStep 4292227 = 6438341) B6438341
theorem B1506995 : Blo 790340 1506995 := bstep (se 1 (by rfl) ⟨1130246, by rfl⟩ : syracuseStep 1506995 = 2260493) B2260493
theorem B6192845 : Blo 790340 6192845 := bstep (se 3 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 6192845 = 2322317) B2322317
theorem B2260811 : Blo 790340 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B1507223 : Blo 790340 1507223 := bstep (se 1 (by rfl) ⟨1130417, by rfl⟩ : syracuseStep 1507223 = 2260835) B2260835
theorem B9043973 : Blo 790340 9043973 := bstep (se 4 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 9043973 = 1695745) B1695745
theorem B2261449 : Blo 790340 2261449 := bstep (se 2 (by rfl) ⟨848043, by rfl⟩ : syracuseStep 2261449 = 1696087) B1696087
theorem B1901323 : Blo 790340 1901323 := bstep (se 1 (by rfl) ⟨1425992, by rfl⟩ : syracuseStep 1901323 = 2851985) B2851985
theorem B1803023 : Blo 790340 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B2261803 : Blo 790340 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B3015539 : Blo 790340 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B5080265 : Blo 790340 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B3606059 : Blo 790340 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B7603789 : Blo 790340 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B4523809 : Blo 790340 4523809 := bstep (se 2 (by rfl) ⟨1696428, by rfl⟩ : syracuseStep 4523809 = 3392857) B3392857
theorem B2000983 : Blo 790340 2000983 := bstep (se 1 (by rfl) ⟨1500737, by rfl⟩ : syracuseStep 2000983 = 3001475) B3001475
theorem B6522967 : Blo 790340 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B952507 : Blo 790340 952507 := bstep (se 1 (by rfl) ⟨714380, by rfl⟩ : syracuseStep 952507 = 1428761) B1428761
theorem B1902793 : Blo 790340 1902793 := bstep (se 2 (by rfl) ⟨713547, by rfl⟩ : syracuseStep 1902793 = 1427095) B1427095
theorem B1083655 : Blo 790340 1083655 := bstep (se 1 (by rfl) ⟨812741, by rfl⟩ : syracuseStep 1083655 = 1625483) B1625483
theorem B3049787 : Blo 790340 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B2001287 : Blo 790340 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B2001419 : Blo 790340 2001419 := bstep (se 1 (by rfl) ⟨1501064, by rfl⟩ : syracuseStep 2001419 = 3002129) B3002129
theorem B11406095 : Blo 790340 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B3607411 : Blo 790340 3607411 := bstep (se 1 (by rfl) ⟨2705558, by rfl⟩ : syracuseStep 3607411 = 5411117) B5411117
theorem B2001935 : Blo 790340 2001935 := bstep (se 1 (by rfl) ⟨1501451, by rfl⟩ : syracuseStep 2001935 = 3002903) B3002903
theorem B2002067 : Blo 790340 2002067 := bstep (se 1 (by rfl) ⟨1501550, by rfl⟩ : syracuseStep 2002067 = 3003101) B3003101
theorem B9014813 : Blo 790340 9014813 := bstep (se 3 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 9014813 = 3380555) B3380555
theorem B4001399 : Blo 790340 4001399 := bstep (se 1 (by rfl) ⟨3001049, by rfl⟩ : syracuseStep 4001399 = 6002099) B6002099
theorem B1904399 : Blo 790340 1904399 := bstep (se 1 (by rfl) ⟨1428299, by rfl⟩ : syracuseStep 1904399 = 2856599) B2856599
theorem B5410597 : Blo 790340 5410597 := bstep (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) B1014487
theorem B790407 : Blo 790340 790407 := bstep (se 1 (by rfl) ⟨592805, by rfl⟩ : syracuseStep 790407 = 1185611) B1185611
theorem B790415 : Blo 790340 790415 := bstep (se 1 (by rfl) ⟨592811, by rfl⟩ : syracuseStep 790415 = 1185623) B1185623
theorem B5083033 : Blo 790340 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B790459 : Blo 790340 790459 := bstep (se 1 (by rfl) ⟨592844, by rfl⟩ : syracuseStep 790459 = 1185689) B1185689
theorem B790535 : Blo 790340 790535 := bstep (se 1 (by rfl) ⟨592901, by rfl⟩ : syracuseStep 790535 = 1185803) B1185803
theorem B790543 : Blo 790340 790543 := bstep (se 1 (by rfl) ⟨592907, by rfl⟩ : syracuseStep 790543 = 1185815) B1185815
theorem B790587 : Blo 790340 790587 := bstep (se 1 (by rfl) ⟨592940, by rfl⟩ : syracuseStep 790587 = 1185881) B1185881
theorem B5705815 : Blo 790340 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B790663 : Blo 790340 790663 := bstep (se 1 (by rfl) ⟨592997, by rfl⟩ : syracuseStep 790663 = 1185995) B1185995
theorem B790671 : Blo 790340 790671 := bstep (se 1 (by rfl) ⟨593003, by rfl⟩ : syracuseStep 790671 = 1186007) B1186007
theorem B790715 : Blo 790340 790715 := bstep (se 1 (by rfl) ⟨593036, by rfl⟩ : syracuseStep 790715 = 1186073) B1186073
theorem B2003201 : Blo 790340 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B790791 : Blo 790340 790791 := bstep (se 1 (by rfl) ⟨593093, by rfl⟩ : syracuseStep 790791 = 1186187) B1186187
theorem B790799 : Blo 790340 790799 := bstep (se 1 (by rfl) ⟨593099, by rfl⟩ : syracuseStep 790799 = 1186199) B1186199
theorem B790843 : Blo 790340 790843 := bstep (se 1 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 790843 = 1186265) B1186265
theorem B790919 : Blo 790340 790919 := bstep (se 1 (by rfl) ⟨593189, by rfl⟩ : syracuseStep 790919 = 1186379) B1186379
theorem B889231 : Blo 790340 889231 := bstep (se 1 (by rfl) ⟨666923, by rfl⟩ : syracuseStep 889231 = 1333847) B1333847
theorem B790927 : Blo 790340 790927 := bstep (se 1 (by rfl) ⟨593195, by rfl⟩ : syracuseStep 790927 = 1186391) B1186391
theorem B790971 : Blo 790340 790971 := bstep (se 1 (by rfl) ⟨593228, by rfl⟩ : syracuseStep 790971 = 1186457) B1186457
theorem B791047 : Blo 790340 791047 := bstep (se 1 (by rfl) ⟨593285, by rfl⟩ : syracuseStep 791047 = 1186571) B1186571
theorem B791055 : Blo 790340 791055 := bstep (se 1 (by rfl) ⟨593291, by rfl⟩ : syracuseStep 791055 = 1186583) B1186583
theorem B21926435 : Blo 790340 21926435 := bstep (se 1 (by rfl) ⟨16444826, by rfl⟩ : syracuseStep 21926435 = 32889653) B32889653
theorem B791099 : Blo 790340 791099 := bstep (se 1 (by rfl) ⟨593324, by rfl⟩ : syracuseStep 791099 = 1186649) B1186649
theorem B4002371 : Blo 790340 4002371 := bstep (se 1 (by rfl) ⟨3001778, by rfl⟩ : syracuseStep 4002371 = 6003557) B6003557
theorem B2003575 : Blo 790340 2003575 := bstep (se 1 (by rfl) ⟨1502681, by rfl⟩ : syracuseStep 2003575 = 3005363) B3005363
theorem B791175 : Blo 790340 791175 := bstep (se 1 (by rfl) ⟨593381, by rfl⟩ : syracuseStep 791175 = 1186763) B1186763
theorem B791183 : Blo 790340 791183 := bstep (se 1 (by rfl) ⟨593387, by rfl⟩ : syracuseStep 791183 = 1186775) B1186775
theorem B791227 : Blo 790340 791227 := bstep (se 1 (by rfl) ⟨593420, by rfl⟩ : syracuseStep 791227 = 1186841) B1186841
theorem B791303 : Blo 790340 791303 := bstep (se 1 (by rfl) ⟨593477, by rfl⟩ : syracuseStep 791303 = 1186955) B1186955
theorem B791311 : Blo 790340 791311 := bstep (se 1 (by rfl) ⟨593483, by rfl⟩ : syracuseStep 791311 = 1186967) B1186967
theorem B5706533 : Blo 790340 5706533 := bstep (se 4 (by rfl) ⟨534987, by rfl⟩ : syracuseStep 5706533 = 1069975) B1069975
theorem B5083955 : Blo 790340 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B791355 : Blo 790340 791355 := bstep (se 1 (by rfl) ⟨593516, by rfl⟩ : syracuseStep 791355 = 1187033) B1187033
theorem B4821875 : Blo 790340 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B4002695 : Blo 790340 4002695 := bstep (se 1 (by rfl) ⟨3002021, by rfl⟩ : syracuseStep 4002695 = 6004043) B6004043
theorem B889735 : Blo 790340 889735 := bstep (se 1 (by rfl) ⟨667301, by rfl⟩ : syracuseStep 889735 = 1334603) B1334603
theorem B791431 : Blo 790340 791431 := bstep (se 1 (by rfl) ⟨593573, by rfl⟩ : syracuseStep 791431 = 1187147) B1187147
theorem B791439 : Blo 790340 791439 := bstep (se 1 (by rfl) ⟨593579, by rfl⟩ : syracuseStep 791439 = 1187159) B1187159
theorem B791483 : Blo 790340 791483 := bstep (se 1 (by rfl) ⟨593612, by rfl⟩ : syracuseStep 791483 = 1187225) B1187225
theorem B791559 : Blo 790340 791559 := bstep (se 1 (by rfl) ⟨593669, by rfl⟩ : syracuseStep 791559 = 1187339) B1187339
theorem B791567 : Blo 790340 791567 := bstep (se 1 (by rfl) ⟨593675, by rfl⟩ : syracuseStep 791567 = 1187351) B1187351
theorem B2004011 : Blo 790340 2004011 := bstep (se 1 (by rfl) ⟨1503008, by rfl⟩ : syracuseStep 2004011 = 3006017) B3006017
theorem B889915 : Blo 790340 889915 := bstep (se 1 (by rfl) ⟨667436, by rfl⟩ : syracuseStep 889915 = 1334873) B1334873
theorem B791611 : Blo 790340 791611 := bstep (se 1 (by rfl) ⟨593708, by rfl⟩ : syracuseStep 791611 = 1187417) B1187417
theorem B791687 : Blo 790340 791687 := bstep (se 1 (by rfl) ⟨593765, by rfl⟩ : syracuseStep 791687 = 1187531) B1187531
theorem B791695 : Blo 790340 791695 := bstep (se 1 (by rfl) ⟨593771, by rfl⟩ : syracuseStep 791695 = 1187543) B1187543
theorem B791739 : Blo 790340 791739 := bstep (se 1 (by rfl) ⟨593804, by rfl⟩ : syracuseStep 791739 = 1187609) B1187609
theorem B791815 : Blo 790340 791815 := bstep (se 1 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 791815 = 1187723) B1187723
theorem B791823 : Blo 790340 791823 := bstep (se 1 (by rfl) ⟨593867, by rfl⟩ : syracuseStep 791823 = 1187735) B1187735
theorem B791867 : Blo 790340 791867 := bstep (se 1 (by rfl) ⟨593900, by rfl⟩ : syracuseStep 791867 = 1187801) B1187801
theorem B791943 : Blo 790340 791943 := bstep (se 1 (by rfl) ⟨593957, by rfl⟩ : syracuseStep 791943 = 1187915) B1187915
theorem B791951 : Blo 790340 791951 := bstep (se 1 (by rfl) ⟨593963, by rfl⟩ : syracuseStep 791951 = 1187927) B1187927
theorem B791995 : Blo 790340 791995 := bstep (se 1 (by rfl) ⟨593996, by rfl⟩ : syracuseStep 791995 = 1187993) B1187993
theorem B792071 : Blo 790340 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B890383 : Blo 790340 890383 := bstep (se 1 (by rfl) ⟨667787, by rfl⟩ : syracuseStep 890383 = 1335575) B1335575
theorem B792079 : Blo 790340 792079 := bstep (se 1 (by rfl) ⟨594059, by rfl⟩ : syracuseStep 792079 = 1188119) B1188119
theorem B792123 : Blo 790340 792123 := bstep (se 1 (by rfl) ⟨594092, by rfl⟩ : syracuseStep 792123 = 1188185) B1188185
theorem B792199 : Blo 790340 792199 := bstep (se 1 (by rfl) ⟨594149, by rfl⟩ : syracuseStep 792199 = 1188299) B1188299
theorem B792207 : Blo 790340 792207 := bstep (se 1 (by rfl) ⟨594155, by rfl⟩ : syracuseStep 792207 = 1188311) B1188311
theorem B792251 : Blo 790340 792251 := bstep (se 1 (by rfl) ⟨594188, by rfl⟩ : syracuseStep 792251 = 1188377) B1188377
theorem B1185527 : Blo 790340 1185527 := bstep (se 1 (by rfl) ⟨889145, by rfl⟩ : syracuseStep 1185527 = 1778291) B1778291
theorem B792327 : Blo 790340 792327 := bstep (se 1 (by rfl) ⟨594245, by rfl⟩ : syracuseStep 792327 = 1188491) B1188491
theorem B1185551 : Blo 790340 1185551 := bstep (se 1 (by rfl) ⟨889163, by rfl⟩ : syracuseStep 1185551 = 1778327) B1778327
theorem B792335 : Blo 790340 792335 := bstep (se 1 (by rfl) ⟨594251, by rfl⟩ : syracuseStep 792335 = 1188503) B1188503
theorem B1185593 : Blo 790340 1185593 := bstep (se 2 (by rfl) ⟨444597, by rfl⟩ : syracuseStep 1185593 = 889195) B889195
theorem B792379 : Blo 790340 792379 := bstep (se 1 (by rfl) ⟨594284, by rfl⟩ : syracuseStep 792379 = 1188569) B1188569
theorem B2004851 : Blo 790340 2004851 := bstep (se 1 (by rfl) ⟨1503638, by rfl⟩ : syracuseStep 2004851 = 3007277) B3007277
theorem B1185671 : Blo 790340 1185671 := bstep (se 1 (by rfl) ⟨889253, by rfl⟩ : syracuseStep 1185671 = 1778507) B1778507
theorem B2004871 : Blo 790340 2004871 := bstep (se 1 (by rfl) ⟨1503653, by rfl⟩ : syracuseStep 2004871 = 3007307) B3007307
theorem B792455 : Blo 790340 792455 := bstep (se 1 (by rfl) ⟨594341, by rfl⟩ : syracuseStep 792455 = 1188683) B1188683
theorem B792463 : Blo 790340 792463 := bstep (se 1 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 792463 = 1188695) B1188695
theorem B6002585 : Blo 790340 6002585 := bstep (se 2 (by rfl) ⟨2250969, by rfl⟩ : syracuseStep 6002585 = 4501939) B4501939
theorem B1185707 : Blo 790340 1185707 := bstep (se 1 (by rfl) ⟨889280, by rfl⟩ : syracuseStep 1185707 = 1778561) B1778561
theorem B792507 : Blo 790340 792507 := bstep (se 1 (by rfl) ⟨594380, by rfl⟩ : syracuseStep 792507 = 1188761) B1188761
theorem B1185737 : Blo 790340 1185737 := bstep (se 2 (by rfl) ⟨444651, by rfl⟩ : syracuseStep 1185737 = 889303) B889303
theorem B5576651 : Blo 790340 5576651 := bstep (se 1 (by rfl) ⟨4182488, by rfl⟩ : syracuseStep 5576651 = 8364977) B8364977
theorem B890887 : Blo 790340 890887 := bstep (se 1 (by rfl) ⟨668165, by rfl⟩ : syracuseStep 890887 = 1336331) B1336331
theorem B792583 : Blo 790340 792583 := bstep (se 1 (by rfl) ⟨594437, by rfl⟩ : syracuseStep 792583 = 1188875) B1188875
theorem B792591 : Blo 790340 792591 := bstep (se 1 (by rfl) ⟨594443, by rfl⟩ : syracuseStep 792591 = 1188887) B1188887
theorem B1185851 : Blo 790340 1185851 := bstep (se 1 (by rfl) ⟨889388, by rfl⟩ : syracuseStep 1185851 = 1778777) B1778777
theorem B792635 : Blo 790340 792635 := bstep (se 1 (by rfl) ⟨594476, by rfl⟩ : syracuseStep 792635 = 1188953) B1188953
theorem B1185911 : Blo 790340 1185911 := bstep (se 1 (by rfl) ⟨889433, by rfl⟩ : syracuseStep 1185911 = 1778867) B1778867
theorem B792711 : Blo 790340 792711 := bstep (se 1 (by rfl) ⟨594533, by rfl⟩ : syracuseStep 792711 = 1189067) B1189067
theorem B1185935 : Blo 790340 1185935 := bstep (se 1 (by rfl) ⟨889451, by rfl⟩ : syracuseStep 1185935 = 1778903) B1778903
theorem B792719 : Blo 790340 792719 := bstep (se 1 (by rfl) ⟨594539, by rfl⟩ : syracuseStep 792719 = 1189079) B1189079
theorem B2005145 : Blo 790340 2005145 := bstep (se 2 (by rfl) ⟨751929, by rfl⟩ : syracuseStep 2005145 = 1503859) B1503859
theorem B1185977 : Blo 790340 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B891067 : Blo 790340 891067 := bstep (se 1 (by rfl) ⟨668300, by rfl⟩ : syracuseStep 891067 = 1336601) B1336601
theorem B792763 : Blo 790340 792763 := bstep (se 1 (by rfl) ⟨594572, by rfl⟩ : syracuseStep 792763 = 1189145) B1189145
theorem B1186055 : Blo 790340 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B792839 : Blo 790340 792839 := bstep (se 1 (by rfl) ⟨594629, by rfl⟩ : syracuseStep 792839 = 1189259) B1189259
theorem B792847 : Blo 790340 792847 := bstep (se 1 (by rfl) ⟨594635, by rfl⟩ : syracuseStep 792847 = 1189271) B1189271
theorem B1186091 : Blo 790340 1186091 := bstep (se 1 (by rfl) ⟨889568, by rfl⟩ : syracuseStep 1186091 = 1779137) B1779137
theorem B2005307 : Blo 790340 2005307 := bstep (se 1 (by rfl) ⟨1503980, by rfl⟩ : syracuseStep 2005307 = 3007961) B3007961
theorem B792891 : Blo 790340 792891 := bstep (se 1 (by rfl) ⟨594668, by rfl⟩ : syracuseStep 792891 = 1189337) B1189337
theorem B1186121 : Blo 790340 1186121 := bstep (se 2 (by rfl) ⟨444795, by rfl⟩ : syracuseStep 1186121 = 889591) B889591
theorem B792967 : Blo 790340 792967 := bstep (se 1 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 792967 = 1189451) B1189451
theorem B792975 : Blo 790340 792975 := bstep (se 1 (by rfl) ⟨594731, by rfl⟩ : syracuseStep 792975 = 1189463) B1189463
theorem B1186235 : Blo 790340 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B793019 : Blo 790340 793019 := bstep (se 1 (by rfl) ⟨594764, by rfl⟩ : syracuseStep 793019 = 1189529) B1189529
theorem B1186295 : Blo 790340 1186295 := bstep (se 1 (by rfl) ⟨889721, by rfl⟩ : syracuseStep 1186295 = 1779443) B1779443
theorem B793095 : Blo 790340 793095 := bstep (se 1 (by rfl) ⟨594821, by rfl⟩ : syracuseStep 793095 = 1189643) B1189643
theorem B1186319 : Blo 790340 1186319 := bstep (se 1 (by rfl) ⟨889739, by rfl⟩ : syracuseStep 1186319 = 1779479) B1779479
theorem B2005519 : Blo 790340 2005519 := bstep (se 1 (by rfl) ⟨1504139, by rfl⟩ : syracuseStep 2005519 = 3008279) B3008279
theorem B793103 : Blo 790340 793103 := bstep (se 1 (by rfl) ⟨594827, by rfl⟩ : syracuseStep 793103 = 1189655) B1189655
theorem B1186361 : Blo 790340 1186361 := bstep (se 2 (by rfl) ⟨444885, by rfl⟩ : syracuseStep 1186361 = 889771) B889771
theorem B793147 : Blo 790340 793147 := bstep (se 1 (by rfl) ⟨594860, by rfl⟩ : syracuseStep 793147 = 1189721) B1189721
theorem B3381821 : Blo 790340 3381821 := bstep (se 3 (by rfl) ⟨634091, by rfl⟩ : syracuseStep 3381821 = 1268183) B1268183
theorem B1186439 : Blo 790340 1186439 := bstep (se 1 (by rfl) ⟨889829, by rfl⟩ : syracuseStep 1186439 = 1779659) B1779659
theorem B793223 : Blo 790340 793223 := bstep (se 1 (by rfl) ⟨594917, by rfl⟩ : syracuseStep 793223 = 1189835) B1189835
theorem B891535 : Blo 790340 891535 := bstep (se 1 (by rfl) ⟨668651, by rfl⟩ : syracuseStep 891535 = 1337303) B1337303
theorem B793231 : Blo 790340 793231 := bstep (se 1 (by rfl) ⟨594923, by rfl⟩ : syracuseStep 793231 = 1189847) B1189847
theorem B1186475 : Blo 790340 1186475 := bstep (se 1 (by rfl) ⟨889856, by rfl⟩ : syracuseStep 1186475 = 1779713) B1779713
theorem B793275 : Blo 790340 793275 := bstep (se 1 (by rfl) ⟨594956, by rfl⟩ : syracuseStep 793275 = 1189913) B1189913
theorem B1186505 : Blo 790340 1186505 := bstep (se 2 (by rfl) ⟨444939, by rfl⟩ : syracuseStep 1186505 = 889879) B889879
theorem B793351 : Blo 790340 793351 := bstep (se 1 (by rfl) ⟨595013, by rfl⟩ : syracuseStep 793351 = 1190027) B1190027
theorem B793359 : Blo 790340 793359 := bstep (se 1 (by rfl) ⟨595019, by rfl⟩ : syracuseStep 793359 = 1190039) B1190039
theorem B2005793 : Blo 790340 2005793 := bstep (se 2 (by rfl) ⟨752172, by rfl⟩ : syracuseStep 2005793 = 1504345) B1504345
theorem B1186619 : Blo 790340 1186619 := bstep (se 1 (by rfl) ⟨889964, by rfl⟩ : syracuseStep 1186619 = 1779929) B1779929
theorem B793403 : Blo 790340 793403 := bstep (se 1 (by rfl) ⟨595052, by rfl⟩ : syracuseStep 793403 = 1190105) B1190105
theorem B1186679 : Blo 790340 1186679 := bstep (se 1 (by rfl) ⟨890009, by rfl⟩ : syracuseStep 1186679 = 1780019) B1780019
theorem B793479 : Blo 790340 793479 := bstep (se 1 (by rfl) ⟨595109, by rfl⟩ : syracuseStep 793479 = 1190219) B1190219
theorem B1186703 : Blo 790340 1186703 := bstep (se 1 (by rfl) ⟨890027, by rfl⟩ : syracuseStep 1186703 = 1780055) B1780055
theorem B793487 : Blo 790340 793487 := bstep (se 1 (by rfl) ⟨595115, by rfl⟩ : syracuseStep 793487 = 1190231) B1190231
theorem B6757283 : Blo 790340 6757283 := bstep (se 1 (by rfl) ⟨5067962, by rfl⟩ : syracuseStep 6757283 = 10135925) B10135925
theorem B1186745 : Blo 790340 1186745 := bstep (se 2 (by rfl) ⟨445029, by rfl⟩ : syracuseStep 1186745 = 890059) B890059
theorem B793531 : Blo 790340 793531 := bstep (se 1 (by rfl) ⟨595148, by rfl⟩ : syracuseStep 793531 = 1190297) B1190297
theorem B2137033 : Blo 790340 2137033 := bstep (se 2 (by rfl) ⟨801387, by rfl⟩ : syracuseStep 2137033 = 1602775) B1602775
theorem B1186823 : Blo 790340 1186823 := bstep (se 1 (by rfl) ⟨890117, by rfl⟩ : syracuseStep 1186823 = 1780235) B1780235
theorem B793607 : Blo 790340 793607 := bstep (se 1 (by rfl) ⟨595205, by rfl⟩ : syracuseStep 793607 = 1190411) B1190411
theorem B793615 : Blo 790340 793615 := bstep (se 1 (by rfl) ⟨595211, by rfl⟩ : syracuseStep 793615 = 1190423) B1190423
theorem B3611677 : Blo 790340 3611677 := bstep (se 3 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 3611677 = 1354379) B1354379
theorem B1186859 : Blo 790340 1186859 := bstep (se 1 (by rfl) ⟨890144, by rfl⟩ : syracuseStep 1186859 = 1780289) B1780289
theorem B793659 : Blo 790340 793659 := bstep (se 1 (by rfl) ⟨595244, by rfl⟩ : syracuseStep 793659 = 1190489) B1190489
theorem B1186889 : Blo 790340 1186889 := bstep (se 2 (by rfl) ⟨445083, by rfl⟩ : syracuseStep 1186889 = 890167) B890167
theorem B892039 : Blo 790340 892039 := bstep (se 1 (by rfl) ⟨669029, by rfl⟩ : syracuseStep 892039 = 1338059) B1338059
theorem B793735 : Blo 790340 793735 := bstep (se 1 (by rfl) ⟨595301, by rfl⟩ : syracuseStep 793735 = 1190603) B1190603
theorem B793743 : Blo 790340 793743 := bstep (se 1 (by rfl) ⟨595307, by rfl⟩ : syracuseStep 793743 = 1190615) B1190615
theorem B1187003 : Blo 790340 1187003 := bstep (se 1 (by rfl) ⟨890252, by rfl⟩ : syracuseStep 1187003 = 1780505) B1780505
theorem B793787 : Blo 790340 793787 := bstep (se 1 (by rfl) ⟨595340, by rfl⟩ : syracuseStep 793787 = 1190681) B1190681
theorem B1187063 : Blo 790340 1187063 := bstep (se 1 (by rfl) ⟨890297, by rfl⟩ : syracuseStep 1187063 = 1780595) B1780595
theorem B793863 : Blo 790340 793863 := bstep (se 1 (by rfl) ⟨595397, by rfl⟩ : syracuseStep 793863 = 1190795) B1190795
theorem B1187087 : Blo 790340 1187087 := bstep (se 1 (by rfl) ⟨890315, by rfl⟩ : syracuseStep 1187087 = 1780631) B1780631
theorem B793871 : Blo 790340 793871 := bstep (se 1 (by rfl) ⟨595403, by rfl⟩ : syracuseStep 793871 = 1190807) B1190807
theorem B1907983 : Blo 790340 1907983 := bstep (se 1 (by rfl) ⟨1430987, by rfl⟩ : syracuseStep 1907983 = 2861975) B2861975
theorem B1187129 : Blo 790340 1187129 := bstep (se 2 (by rfl) ⟨445173, by rfl⟩ : syracuseStep 1187129 = 890347) B890347
theorem B892219 : Blo 790340 892219 := bstep (se 1 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 892219 = 1338329) B1338329
theorem B793915 : Blo 790340 793915 := bstep (se 1 (by rfl) ⟨595436, by rfl⟩ : syracuseStep 793915 = 1190873) B1190873
theorem B1187207 : Blo 790340 1187207 := bstep (se 1 (by rfl) ⟨890405, by rfl⟩ : syracuseStep 1187207 = 1780811) B1780811
theorem B793991 : Blo 790340 793991 := bstep (se 1 (by rfl) ⟨595493, by rfl⟩ : syracuseStep 793991 = 1190987) B1190987
theorem B793999 : Blo 790340 793999 := bstep (se 1 (by rfl) ⟨595499, by rfl⟩ : syracuseStep 793999 = 1190999) B1190999
theorem B1187243 : Blo 790340 1187243 := bstep (se 1 (by rfl) ⟨890432, by rfl⟩ : syracuseStep 1187243 = 1780865) B1780865
theorem B2137529 : Blo 790340 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B794043 : Blo 790340 794043 := bstep (se 1 (by rfl) ⟨595532, by rfl⟩ : syracuseStep 794043 = 1191065) B1191065
theorem B1187273 : Blo 790340 1187273 := bstep (se 2 (by rfl) ⟨445227, by rfl⟩ : syracuseStep 1187273 = 890455) B890455
theorem B794119 : Blo 790340 794119 := bstep (se 1 (by rfl) ⟨595589, by rfl⟩ : syracuseStep 794119 = 1191179) B1191179
theorem B794127 : Blo 790340 794127 := bstep (se 1 (by rfl) ⟨595595, by rfl⟩ : syracuseStep 794127 = 1191191) B1191191
theorem B1187387 : Blo 790340 1187387 := bstep (se 1 (by rfl) ⟨890540, by rfl⟩ : syracuseStep 1187387 = 1781081) B1781081
theorem B794171 : Blo 790340 794171 := bstep (se 1 (by rfl) ⟨595628, by rfl⟩ : syracuseStep 794171 = 1191257) B1191257
theorem B2137661 : Blo 790340 2137661 := bstep (se 3 (by rfl) ⟨400811, by rfl⟩ : syracuseStep 2137661 = 801623) B801623
theorem B1187447 : Blo 790340 1187447 := bstep (se 1 (by rfl) ⟨890585, by rfl⟩ : syracuseStep 1187447 = 1781171) B1781171
theorem B794247 : Blo 790340 794247 := bstep (se 1 (by rfl) ⟨595685, by rfl⟩ : syracuseStep 794247 = 1191371) B1191371
theorem B1187471 : Blo 790340 1187471 := bstep (se 1 (by rfl) ⟨890603, by rfl⟩ : syracuseStep 1187471 = 1781207) B1781207
theorem B794255 : Blo 790340 794255 := bstep (se 1 (by rfl) ⟨595691, by rfl⟩ : syracuseStep 794255 = 1191383) B1191383
theorem B1187513 : Blo 790340 1187513 := bstep (se 2 (by rfl) ⟨445317, by rfl⟩ : syracuseStep 1187513 = 890635) B890635
theorem B794299 : Blo 790340 794299 := bstep (se 1 (by rfl) ⟨595724, by rfl⟩ : syracuseStep 794299 = 1191449) B1191449
theorem B1187591 : Blo 790340 1187591 := bstep (se 1 (by rfl) ⟨890693, by rfl⟩ : syracuseStep 1187591 = 1781387) B1781387
theorem B2006795 : Blo 790340 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B892687 : Blo 790340 892687 := bstep (se 1 (by rfl) ⟨669515, by rfl⟩ : syracuseStep 892687 = 1339031) B1339031
theorem B1187627 : Blo 790340 1187627 := bstep (se 1 (by rfl) ⟨890720, by rfl⟩ : syracuseStep 1187627 = 1781441) B1781441
theorem B6004529 : Blo 790340 6004529 := bstep (se 2 (by rfl) ⟨2251698, by rfl⟩ : syracuseStep 6004529 = 4503397) B4503397
theorem B9019187 : Blo 790340 9019187 := bstep (se 1 (by rfl) ⟨6764390, by rfl⟩ : syracuseStep 9019187 = 13528781) B13528781
theorem B1187657 : Blo 790340 1187657 := bstep (se 2 (by rfl) ⟨445371, by rfl⟩ : syracuseStep 1187657 = 890743) B890743
theorem B2858905 : Blo 790340 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B3219385 : Blo 790340 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B1187771 : Blo 790340 1187771 := bstep (se 1 (by rfl) ⟨890828, by rfl⟩ : syracuseStep 1187771 = 1781657) B1781657
theorem B1187831 : Blo 790340 1187831 := bstep (se 1 (by rfl) ⟨890873, by rfl⟩ : syracuseStep 1187831 = 1781747) B1781747
theorem B1187855 : Blo 790340 1187855 := bstep (se 1 (by rfl) ⟨890891, by rfl⟩ : syracuseStep 1187855 = 1781783) B1781783
theorem B1187897 : Blo 790340 1187897 := bstep (se 2 (by rfl) ⟨445461, by rfl⟩ : syracuseStep 1187897 = 890923) B890923
theorem B4890691 : Blo 790340 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B74326085 : Blo 790340 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B1187975 : Blo 790340 1187975 := bstep (se 1 (by rfl) ⟨890981, by rfl⟩ : syracuseStep 1187975 = 1781963) B1781963
theorem B1188011 : Blo 790340 1188011 := bstep (se 1 (by rfl) ⟨891008, by rfl⟩ : syracuseStep 1188011 = 1782017) B1782017
theorem B1188041 : Blo 790340 1188041 := bstep (se 2 (by rfl) ⟨445515, by rfl⟩ : syracuseStep 1188041 = 891031) B891031
theorem B893191 : Blo 790340 893191 := bstep (se 1 (by rfl) ⟨669893, by rfl⟩ : syracuseStep 893191 = 1339787) B1339787
theorem B1188155 : Blo 790340 1188155 := bstep (se 1 (by rfl) ⟨891116, by rfl⟩ : syracuseStep 1188155 = 1782233) B1782233
theorem B4006259 : Blo 790340 4006259 := bstep (se 1 (by rfl) ⟨3004694, by rfl⟩ : syracuseStep 4006259 = 6009389) B6009389
theorem B1188215 : Blo 790340 1188215 := bstep (se 1 (by rfl) ⟨891161, by rfl⟩ : syracuseStep 1188215 = 1782323) B1782323
theorem B1188239 : Blo 790340 1188239 := bstep (se 1 (by rfl) ⟨891179, by rfl⟩ : syracuseStep 1188239 = 1782359) B1782359
theorem B2007443 : Blo 790340 2007443 := bstep (se 1 (by rfl) ⟨1505582, by rfl⟩ : syracuseStep 2007443 = 3011165) B3011165
theorem B1188281 : Blo 790340 1188281 := bstep (se 2 (by rfl) ⟨445605, by rfl⟩ : syracuseStep 1188281 = 891211) B891211
theorem B893371 : Blo 790340 893371 := bstep (se 1 (by rfl) ⟨670028, by rfl⟩ : syracuseStep 893371 = 1340057) B1340057
theorem B1188359 : Blo 790340 1188359 := bstep (se 1 (by rfl) ⟨891269, by rfl⟩ : syracuseStep 1188359 = 1782539) B1782539
theorem B2138653 : Blo 790340 2138653 := bstep (se 3 (by rfl) ⟨400997, by rfl⟩ : syracuseStep 2138653 = 801995) B801995
theorem B16228907 : Blo 790340 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B1188395 : Blo 790340 1188395 := bstep (se 1 (by rfl) ⟨891296, by rfl⟩ : syracuseStep 1188395 = 1782593) B1782593
theorem B1188425 : Blo 790340 1188425 := bstep (se 2 (by rfl) ⟨445659, by rfl⟩ : syracuseStep 1188425 = 891319) B891319
theorem B1450631 : Blo 790340 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B2007737 : Blo 790340 2007737 := bstep (se 2 (by rfl) ⟨752901, by rfl⟩ : syracuseStep 2007737 = 1505803) B1505803
theorem B1188539 : Blo 790340 1188539 := bstep (se 1 (by rfl) ⟨891404, by rfl⟩ : syracuseStep 1188539 = 1782809) B1782809
theorem B9642725 : Blo 790340 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B1188599 : Blo 790340 1188599 := bstep (se 1 (by rfl) ⟨891449, by rfl⟩ : syracuseStep 1188599 = 1782899) B1782899
theorem B1188623 : Blo 790340 1188623 := bstep (se 1 (by rfl) ⟨891467, by rfl⟩ : syracuseStep 1188623 = 1782935) B1782935
theorem B1188665 : Blo 790340 1188665 := bstep (se 2 (by rfl) ⟨445749, by rfl⟩ : syracuseStep 1188665 = 891499) B891499
theorem B4006745 : Blo 790340 4006745 := bstep (se 2 (by rfl) ⟨1502529, by rfl⟩ : syracuseStep 4006745 = 3005059) B3005059
theorem B3384179 : Blo 790340 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B1188743 : Blo 790340 1188743 := bstep (se 1 (by rfl) ⟨891557, by rfl⟩ : syracuseStep 1188743 = 1783115) B1783115
theorem B1778579 : Blo 790340 1778579 := bstep (se 1 (by rfl) ⟨1333934, by rfl⟩ : syracuseStep 1778579 = 2667869) B2667869
theorem B1188779 : Blo 790340 1188779 := bstep (se 1 (by rfl) ⟨891584, by rfl⟩ : syracuseStep 1188779 = 1783169) B1783169
theorem B1778633 : Blo 790340 1778633 := bstep (se 2 (by rfl) ⟨666987, by rfl⟩ : syracuseStep 1778633 = 1333975) B1333975
theorem B1188809 : Blo 790340 1188809 := bstep (se 2 (by rfl) ⟨445803, by rfl⟩ : syracuseStep 1188809 = 891607) B891607
theorem B1188923 : Blo 790340 1188923 := bstep (se 1 (by rfl) ⟨891692, by rfl⟩ : syracuseStep 1188923 = 1783385) B1783385
theorem B7611479 : Blo 790340 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B1188983 : Blo 790340 1188983 := bstep (se 1 (by rfl) ⟨891737, by rfl⟩ : syracuseStep 1188983 = 1783475) B1783475
theorem B1189007 : Blo 790340 1189007 := bstep (se 1 (by rfl) ⟨891755, by rfl⟩ : syracuseStep 1189007 = 1783511) B1783511
theorem B1189049 : Blo 790340 1189049 := bstep (se 2 (by rfl) ⟨445893, by rfl⟩ : syracuseStep 1189049 = 891787) B891787
theorem B2860289 : Blo 790340 2860289 := bstep (se 2 (by rfl) ⟨1072608, by rfl⟩ : syracuseStep 2860289 = 2145217) B2145217
theorem B1189127 : Blo 790340 1189127 := bstep (se 1 (by rfl) ⟨891845, by rfl⟩ : syracuseStep 1189127 = 1783691) B1783691
theorem B1189163 : Blo 790340 1189163 := bstep (se 1 (by rfl) ⟨891872, by rfl⟩ : syracuseStep 1189163 = 1783745) B1783745
theorem B1189193 : Blo 790340 1189193 := bstep (se 2 (by rfl) ⟨445947, by rfl⟩ : syracuseStep 1189193 = 891895) B891895
theorem B2008435 : Blo 790340 2008435 := bstep (se 1 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 2008435 = 3012653) B3012653
theorem B1189307 : Blo 790340 1189307 := bstep (se 1 (by rfl) ⟨891980, by rfl⟩ : syracuseStep 1189307 = 1783961) B1783961
theorem B1189367 : Blo 790340 1189367 := bstep (se 1 (by rfl) ⟨892025, by rfl⟩ : syracuseStep 1189367 = 1784051) B1784051
theorem B2008577 : Blo 790340 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B1189391 : Blo 790340 1189391 := bstep (se 1 (by rfl) ⟨892043, by rfl⟩ : syracuseStep 1189391 = 1784087) B1784087
theorem B2139691 : Blo 790340 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B1189433 : Blo 790340 1189433 := bstep (se 2 (by rfl) ⟨446037, by rfl⟩ : syracuseStep 1189433 = 892075) B892075
theorem B1779335 : Blo 790340 1779335 := bstep (se 1 (by rfl) ⟨1334501, by rfl⟩ : syracuseStep 1779335 = 2669003) B2669003
theorem B1189511 : Blo 790340 1189511 := bstep (se 1 (by rfl) ⟨892133, by rfl⟩ : syracuseStep 1189511 = 1784267) B1784267
theorem B1189547 : Blo 790340 1189547 := bstep (se 1 (by rfl) ⟨892160, by rfl⟩ : syracuseStep 1189547 = 1784321) B1784321
theorem B1189577 : Blo 790340 1189577 := bstep (se 2 (by rfl) ⟨446091, by rfl⟩ : syracuseStep 1189577 = 892183) B892183
theorem B1779515 : Blo 790340 1779515 := bstep (se 1 (by rfl) ⟨1334636, by rfl⟩ : syracuseStep 1779515 = 2669273) B2669273
theorem B1189691 : Blo 790340 1189691 := bstep (se 1 (by rfl) ⟨892268, by rfl⟩ : syracuseStep 1189691 = 1784537) B1784537
theorem B1189751 : Blo 790340 1189751 := bstep (se 1 (by rfl) ⟨892313, by rfl⟩ : syracuseStep 1189751 = 1784627) B1784627
theorem B1189775 : Blo 790340 1189775 := bstep (se 1 (by rfl) ⟨892331, by rfl⟩ : syracuseStep 1189775 = 1784663) B1784663
theorem B1779641 : Blo 790340 1779641 := bstep (se 2 (by rfl) ⟨667365, by rfl⟩ : syracuseStep 1779641 = 1334731) B1334731
theorem B1189817 : Blo 790340 1189817 := bstep (se 2 (by rfl) ⟨446181, by rfl⟩ : syracuseStep 1189817 = 892363) B892363
theorem B2009033 : Blo 790340 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B1189895 : Blo 790340 1189895 := bstep (se 1 (by rfl) ⟨892421, by rfl⟩ : syracuseStep 1189895 = 1784843) B1784843
theorem B1189931 : Blo 790340 1189931 := bstep (se 1 (by rfl) ⟨892448, by rfl⟩ : syracuseStep 1189931 = 1784897) B1784897
theorem B1189961 : Blo 790340 1189961 := bstep (se 2 (by rfl) ⟨446235, by rfl⟩ : syracuseStep 1189961 = 892471) B892471
theorem B1190075 : Blo 790340 1190075 := bstep (se 1 (by rfl) ⟨892556, by rfl⟩ : syracuseStep 1190075 = 1785113) B1785113
theorem B1190135 : Blo 790340 1190135 := bstep (se 1 (by rfl) ⟨892601, by rfl⟩ : syracuseStep 1190135 = 1785203) B1785203
theorem B1779983 : Blo 790340 1779983 := bstep (se 1 (by rfl) ⟨1334987, by rfl⟩ : syracuseStep 1779983 = 2669975) B2669975
theorem B1190159 : Blo 790340 1190159 := bstep (se 1 (by rfl) ⟨892619, by rfl⟩ : syracuseStep 1190159 = 1785239) B1785239
theorem B1780001 : Blo 790340 1780001 := bstep (se 2 (by rfl) ⟨667500, by rfl⟩ : syracuseStep 1780001 = 1335001) B1335001
theorem B2009387 : Blo 790340 2009387 := bstep (se 1 (by rfl) ⟨1507040, by rfl⟩ : syracuseStep 2009387 = 3014081) B3014081
theorem B1190201 : Blo 790340 1190201 := bstep (se 2 (by rfl) ⟨446325, by rfl⟩ : syracuseStep 1190201 = 892651) B892651
theorem B1190279 : Blo 790340 1190279 := bstep (se 1 (by rfl) ⟨892709, by rfl⟩ : syracuseStep 1190279 = 1785419) B1785419
theorem B4827539 : Blo 790340 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B1190315 : Blo 790340 1190315 := bstep (se 1 (by rfl) ⟨892736, by rfl⟩ : syracuseStep 1190315 = 1785473) B1785473
theorem B1190345 : Blo 790340 1190345 := bstep (se 2 (by rfl) ⟨446379, by rfl⟩ : syracuseStep 1190345 = 892759) B892759
theorem B13740529 : Blo 790340 13740529 := bstep (se 2 (by rfl) ⟨5152698, by rfl⟩ : syracuseStep 13740529 = 10305397) B10305397
theorem B1190459 : Blo 790340 1190459 := bstep (se 1 (by rfl) ⟨892844, by rfl⟩ : syracuseStep 1190459 = 1785689) B1785689
theorem B1780343 : Blo 790340 1780343 := bstep (se 1 (by rfl) ⟨1335257, by rfl⟩ : syracuseStep 1780343 = 2670515) B2670515
theorem B1190519 : Blo 790340 1190519 := bstep (se 1 (by rfl) ⟨892889, by rfl⟩ : syracuseStep 1190519 = 1785779) B1785779
theorem B1190543 : Blo 790340 1190543 := bstep (se 1 (by rfl) ⟨892907, by rfl⟩ : syracuseStep 1190543 = 1785815) B1785815
theorem B1190585 : Blo 790340 1190585 := bstep (se 2 (by rfl) ⟨446469, by rfl⟩ : syracuseStep 1190585 = 892939) B892939
theorem B4893385 : Blo 790340 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B1190663 : Blo 790340 1190663 := bstep (se 1 (by rfl) ⟨892997, by rfl⟩ : syracuseStep 1190663 = 1785995) B1785995
theorem B1780523 : Blo 790340 1780523 := bstep (se 1 (by rfl) ⟨1335392, by rfl⟩ : syracuseStep 1780523 = 2670785) B2670785
theorem B1190699 : Blo 790340 1190699 := bstep (se 1 (by rfl) ⟨893024, by rfl⟩ : syracuseStep 1190699 = 1786049) B1786049
theorem B1715003 : Blo 790340 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B1190729 : Blo 790340 1190729 := bstep (se 2 (by rfl) ⟨446523, by rfl⟩ : syracuseStep 1190729 = 893047) B893047
theorem B4008851 : Blo 790340 4008851 := bstep (se 1 (by rfl) ⟨3006638, by rfl⟩ : syracuseStep 4008851 = 6013277) B6013277
theorem B11447203 : Blo 790340 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B1190843 : Blo 790340 1190843 := bstep (se 1 (by rfl) ⟨893132, by rfl⟩ : syracuseStep 1190843 = 1786265) B1786265
theorem B1190903 : Blo 790340 1190903 := bstep (se 1 (by rfl) ⟨893177, by rfl⟩ : syracuseStep 1190903 = 1786355) B1786355
theorem B1190927 : Blo 790340 1190927 := bstep (se 1 (by rfl) ⟨893195, by rfl⟩ : syracuseStep 1190927 = 1786391) B1786391
theorem B1190969 : Blo 790340 1190969 := bstep (se 2 (by rfl) ⟨446613, by rfl⟩ : syracuseStep 1190969 = 893227) B893227
theorem B1191047 : Blo 790340 1191047 := bstep (se 1 (by rfl) ⟨893285, by rfl⟩ : syracuseStep 1191047 = 1786571) B1786571
theorem B1780883 : Blo 790340 1780883 := bstep (se 1 (by rfl) ⟨1335662, by rfl⟩ : syracuseStep 1780883 = 2671325) B2671325
theorem B25734293 : Blo 790340 25734293 := bstep (se 6 (by rfl) ⟨603147, by rfl⟩ : syracuseStep 25734293 = 1206295) B1206295
theorem B1191083 : Blo 790340 1191083 := bstep (se 1 (by rfl) ⟨893312, by rfl⟩ : syracuseStep 1191083 = 1786625) B1786625
theorem B1780937 : Blo 790340 1780937 := bstep (se 2 (by rfl) ⟨667851, by rfl⟩ : syracuseStep 1780937 = 1335703) B1335703
theorem B1191113 : Blo 790340 1191113 := bstep (se 2 (by rfl) ⟨446667, by rfl⟩ : syracuseStep 1191113 = 893335) B893335
theorem B2010379 : Blo 790340 2010379 := bstep (se 1 (by rfl) ⟨1507784, by rfl⟩ : syracuseStep 2010379 = 3015569) B3015569
theorem B1191227 : Blo 790340 1191227 := bstep (se 1 (by rfl) ⟨893420, by rfl⟩ : syracuseStep 1191227 = 1786841) B1786841
theorem B1191287 : Blo 790340 1191287 := bstep (se 1 (by rfl) ⟨893465, by rfl⟩ : syracuseStep 1191287 = 1786931) B1786931
theorem B1191311 : Blo 790340 1191311 := bstep (se 1 (by rfl) ⟨893483, by rfl⟩ : syracuseStep 1191311 = 1786967) B1786967
theorem B2010521 : Blo 790340 2010521 := bstep (se 2 (by rfl) ⟨753945, by rfl⟩ : syracuseStep 2010521 = 1507891) B1507891
theorem B1191353 : Blo 790340 1191353 := bstep (se 2 (by rfl) ⟨446757, by rfl⟩ : syracuseStep 1191353 = 893515) B893515
theorem B1125895 : Blo 790340 1125895 := bstep (se 1 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 1125895 = 1688843) B1688843
theorem B1191431 : Blo 790340 1191431 := bstep (se 1 (by rfl) ⟨893573, by rfl⟩ : syracuseStep 1191431 = 1787147) B1787147
theorem B1191467 : Blo 790340 1191467 := bstep (se 1 (by rfl) ⟨893600, by rfl⟩ : syracuseStep 1191467 = 1787201) B1787201
theorem B1191497 : Blo 790340 1191497 := bstep (se 2 (by rfl) ⟨446811, by rfl⟩ : syracuseStep 1191497 = 893623) B893623
theorem B1781639 : Blo 790340 1781639 := bstep (se 1 (by rfl) ⟨1336229, by rfl⟩ : syracuseStep 1781639 = 2672459) B2672459
theorem B1781819 : Blo 790340 1781819 := bstep (se 1 (by rfl) ⟨1336364, by rfl⟩ : syracuseStep 1781819 = 2672729) B2672729
theorem B1781945 : Blo 790340 1781945 := bstep (se 2 (by rfl) ⟨668229, by rfl⟩ : syracuseStep 1781945 = 1336459) B1336459
theorem B1126715 : Blo 790340 1126715 := bstep (se 1 (by rfl) ⟨845036, by rfl⟩ : syracuseStep 1126715 = 1690073) B1690073
theorem B6861115 : Blo 790340 6861115 := bstep (se 1 (by rfl) ⟨5145836, by rfl⟩ : syracuseStep 6861115 = 10291673) B10291673
theorem B4075865 : Blo 790340 4075865 := bstep (se 2 (by rfl) ⟨1528449, by rfl⟩ : syracuseStep 4075865 = 3056899) B3056899
theorem B1782287 : Blo 790340 1782287 := bstep (se 1 (by rfl) ⟨1336715, by rfl⟩ : syracuseStep 1782287 = 2673431) B2673431
theorem B1782305 : Blo 790340 1782305 := bstep (se 2 (by rfl) ⟨668364, by rfl⟩ : syracuseStep 1782305 = 1336729) B1336729
theorem B13546277 : Blo 790340 13546277 := bstep (se 4 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 13546277 = 2539927) B2539927
theorem B2405207 : Blo 790340 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B1782647 : Blo 790340 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B1127353 : Blo 790340 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B3814411 : Blo 790340 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B1127467 : Blo 790340 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B1782827 : Blo 790340 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B3388483 : Blo 790340 3388483 := bstep (se 1 (by rfl) ⟨2541362, by rfl⟩ : syracuseStep 3388483 = 5082725) B5082725
theorem B1127695 : Blo 790340 1127695 := bstep (se 1 (by rfl) ⟨845771, by rfl⟩ : syracuseStep 1127695 = 1691543) B1691543
theorem B2667923 : Blo 790340 2667923 := bstep (se 1 (by rfl) ⟨2000942, by rfl⟩ : syracuseStep 2667923 = 4001885) B4001885
theorem B1783187 : Blo 790340 1783187 := bstep (se 1 (by rfl) ⟨1337390, by rfl⟩ : syracuseStep 1783187 = 2674781) B2674781
theorem B1783241 : Blo 790340 1783241 := bstep (se 2 (by rfl) ⟨668715, by rfl⟩ : syracuseStep 1783241 = 1337431) B1337431
theorem B4011929 : Blo 790340 4011929 := bstep (se 2 (by rfl) ⟨1504473, by rfl⟩ : syracuseStep 4011929 = 3008947) B3008947
theorem B4503671 : Blo 790340 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B1128583 : Blo 790340 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B1783943 : Blo 790340 1783943 := bstep (se 1 (by rfl) ⟨1337957, by rfl⟩ : syracuseStep 1783943 = 2675915) B2675915
theorem B1784123 : Blo 790340 1784123 := bstep (se 1 (by rfl) ⟨1338092, by rfl⟩ : syracuseStep 1784123 = 2676185) B2676185
theorem B4503923 : Blo 790340 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B9615761 : Blo 790340 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B1784249 : Blo 790340 1784249 := bstep (se 2 (by rfl) ⟨669093, by rfl⟩ : syracuseStep 1784249 = 1338187) B1338187
theorem B4569643 : Blo 790340 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B1129079 : Blo 790340 1129079 := bstep (se 1 (by rfl) ⟨846809, by rfl⟩ : syracuseStep 1129079 = 1693619) B1693619
theorem B6437495 : Blo 790340 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B2669327 : Blo 790340 2669327 := bstep (se 1 (by rfl) ⟨2001995, by rfl⟩ : syracuseStep 2669327 = 4003991) B4003991
theorem B1784591 : Blo 790340 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B1784609 : Blo 790340 1784609 := bstep (se 2 (by rfl) ⟨669228, by rfl⟩ : syracuseStep 1784609 = 1338457) B1338457
theorem B82394117 : Blo 790340 82394117 := bstep (se 4 (by rfl) ⟨7724448, by rfl⟩ : syracuseStep 82394117 = 15448897) B15448897
theorem B2669597 : Blo 790340 2669597 := bstep (se 3 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 2669597 = 1001099) B1001099
theorem B1784951 : Blo 790340 1784951 := bstep (se 1 (by rfl) ⟨1338713, by rfl⟩ : syracuseStep 1784951 = 2677427) B2677427
theorem B2538697 : Blo 790340 2538697 := bstep (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) B1904023
theorem B1785131 : Blo 790340 1785131 := bstep (se 1 (by rfl) ⟨1338848, by rfl⟩ : syracuseStep 1785131 = 2677697) B2677697
theorem B3489139 : Blo 790340 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B6012305 : Blo 790340 6012305 := bstep (se 2 (by rfl) ⟨2254614, by rfl⟩ : syracuseStep 6012305 = 4509229) B4509229
theorem B3390929 : Blo 790340 3390929 := bstep (se 2 (by rfl) ⟨1271598, by rfl⟩ : syracuseStep 3390929 = 2543197) B2543197
theorem B65158613 : Blo 790340 65158613 := bstep (se 7 (by rfl) ⟨763577, by rfl⟩ : syracuseStep 65158613 = 1527155) B1527155
theorem B1130041 : Blo 790340 1130041 := bstep (se 2 (by rfl) ⟨423765, by rfl⟩ : syracuseStep 1130041 = 847531) B847531
theorem B1785491 : Blo 790340 1785491 := bstep (se 1 (by rfl) ⟨1339118, by rfl⟩ : syracuseStep 1785491 = 2678237) B2678237
theorem B10141361 : Blo 790340 10141361 := bstep (se 2 (by rfl) ⟨3803010, by rfl⟩ : syracuseStep 10141361 = 7606021) B7606021
theorem B1785545 : Blo 790340 1785545 := bstep (se 2 (by rfl) ⟨669579, by rfl⟩ : syracuseStep 1785545 = 1339159) B1339159
theorem B4505381 : Blo 790340 4505381 := bstep (se 4 (by rfl) ⟨422379, by rfl⟩ : syracuseStep 4505381 = 844759) B844759
theorem B1130383 : Blo 790340 1130383 := bstep (se 1 (by rfl) ⟨847787, by rfl⟩ : syracuseStep 1130383 = 1695575) B1695575
theorem B2146439 : Blo 790340 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B12828941 : Blo 790340 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B1786247 : Blo 790340 1786247 := bstep (se 1 (by rfl) ⟨1339685, by rfl⟩ : syracuseStep 1786247 = 2679371) B2679371
theorem B2671001 : Blo 790340 2671001 := bstep (se 2 (by rfl) ⟨1001625, by rfl⟩ : syracuseStep 2671001 = 2003251) B2003251
theorem B4014521 : Blo 790340 4014521 := bstep (se 2 (by rfl) ⟨1505445, by rfl⟩ : syracuseStep 4014521 = 3010891) B3010891
theorem B1786427 : Blo 790340 1786427 := bstep (se 1 (by rfl) ⟨1339820, by rfl⟩ : syracuseStep 1786427 = 2679641) B2679641
theorem B1786553 : Blo 790340 1786553 := bstep (se 2 (by rfl) ⟨669957, by rfl⟩ : syracuseStep 1786553 = 1339915) B1339915
theorem B4506313 : Blo 790340 4506313 := bstep (se 2 (by rfl) ⟨1689867, by rfl⟩ : syracuseStep 4506313 = 3379735) B3379735
theorem B1688467 : Blo 790340 1688467 := bstep (se 1 (by rfl) ⟨1266350, by rfl⟩ : syracuseStep 1688467 = 2532701) B2532701
theorem B1786895 : Blo 790340 1786895 := bstep (se 1 (by rfl) ⟨1340171, by rfl⟩ : syracuseStep 1786895 = 2680343) B2680343
theorem B1786913 : Blo 790340 1786913 := bstep (se 2 (by rfl) ⟨670092, by rfl⟩ : syracuseStep 1786913 = 1340185) B1340185
theorem B7619629 : Blo 790340 7619629 := bstep (se 3 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 7619629 = 2857361) B2857361
theorem B1000507 : Blo 790340 1000507 := bstep (se 1 (by rfl) ⟨750380, by rfl⟩ : syracuseStep 1000507 = 1500761) B1500761
theorem B2671703 : Blo 790340 2671703 := bstep (se 1 (by rfl) ⟨2003777, by rfl⟩ : syracuseStep 2671703 = 4007555) B4007555
theorem B11420909 : Blo 790340 11420909 := bstep (se 3 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 11420909 = 4282841) B4282841
theorem B1983745 : Blo 790340 1983745 := bstep (se 2 (by rfl) ⟨743904, by rfl⟩ : syracuseStep 1983745 = 1487809) B1487809
theorem B3622259 : Blo 790340 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B1787255 : Blo 790340 1787255 := bstep (se 1 (by rfl) ⟨1340441, by rfl⟩ : syracuseStep 1787255 = 2680883) B2680883
theorem B200263043 : Blo 790340 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B2672189 : Blo 790340 2672189 := bstep (se 3 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 2672189 = 1002071) B1002071
theorem B54904499 : Blo 790340 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B4015817 : Blo 790340 4015817 := bstep (se 2 (by rfl) ⟨1505931, by rfl⟩ : syracuseStep 4015817 = 3011863) B3011863
theorem B6014735 : Blo 790340 6014735 := bstep (se 1 (by rfl) ⟨4511051, by rfl⟩ : syracuseStep 6014735 = 9022103) B9022103
theorem B1001479 : Blo 790340 1001479 := bstep (se 1 (by rfl) ⟨751109, by rfl⟩ : syracuseStep 1001479 = 1502219) B1502219
theorem B1001899 : Blo 790340 1001899 := bstep (se 1 (by rfl) ⟨751424, by rfl⟩ : syracuseStep 1001899 = 1502849) B1502849
theorem B1002127 : Blo 790340 1002127 := bstep (se 1 (by rfl) ⟨751595, by rfl⟩ : syracuseStep 1002127 = 1503191) B1503191
theorem B2542337 : Blo 790340 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B2673593 : Blo 790340 2673593 := bstep (se 2 (by rfl) ⟨1002597, by rfl⟩ : syracuseStep 2673593 = 2005195) B2005195
theorem B2444435 : Blo 790340 2444435 := bstep (se 1 (by rfl) ⟨1833326, by rfl⟩ : syracuseStep 2444435 = 3666653) B3666653
theorem B2346355 : Blo 790340 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B1002871 : Blo 790340 1002871 := bstep (se 1 (by rfl) ⟨752153, by rfl⟩ : syracuseStep 1002871 = 1504307) B1504307
theorem B2674187 : Blo 790340 2674187 := bstep (se 1 (by rfl) ⟨2005640, by rfl⟩ : syracuseStep 2674187 = 4011281) B4011281
theorem B10145357 : Blo 790340 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B2674295 : Blo 790340 2674295 := bstep (se 1 (by rfl) ⟨2005721, by rfl⟩ : syracuseStep 2674295 = 4011443) B4011443
theorem B1003195 : Blo 790340 1003195 := bstep (se 1 (by rfl) ⟨752396, by rfl⟩ : syracuseStep 1003195 = 1504793) B1504793
theorem B6770405 : Blo 790340 6770405 := bstep (se 4 (by rfl) ⟨634725, by rfl⟩ : syracuseStep 6770405 = 1269451) B1269451
theorem B1003691 : Blo 790340 1003691 := bstep (se 1 (by rfl) ⟨752768, by rfl⟩ : syracuseStep 1003691 = 1505537) B1505537
theorem B2674889 : Blo 790340 2674889 := bstep (se 2 (by rfl) ⟨1003083, by rfl⟩ : syracuseStep 2674889 = 2006167) B2006167
theorem B7721249 : Blo 790340 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B5067143 : Blo 790340 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B1004167 : Blo 790340 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B7721729 : Blo 790340 7721729 := bstep (se 2 (by rfl) ⟨2895648, by rfl⟩ : syracuseStep 7721729 = 5791297) B5791297
theorem B1692431 : Blo 790340 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B5722969 : Blo 790340 5722969 := bstep (se 2 (by rfl) ⟨2146113, by rfl⟩ : syracuseStep 5722969 = 4292227) B4292227
theorem B1069943 : Blo 790340 1069943 := bstep (se 1 (by rfl) ⟨802457, by rfl⟩ : syracuseStep 1069943 = 1604915) B1604915
theorem B1692551 : Blo 790340 1692551 := bstep (se 1 (by rfl) ⟨1269413, by rfl⟩ : syracuseStep 1692551 = 2538827) B2538827
theorem B2675591 : Blo 790340 2675591 := bstep (se 1 (by rfl) ⟨2006693, by rfl⟩ : syracuseStep 2675591 = 4013387) B4013387
theorem B2413601 : Blo 790340 2413601 := bstep (se 2 (by rfl) ⟨905100, by rfl⟩ : syracuseStep 2413601 = 1810201) B1810201
theorem B1692731 : Blo 790340 1692731 := bstep (se 1 (by rfl) ⟨1269548, by rfl⟩ : syracuseStep 1692731 = 2539097) B2539097
theorem B1004663 : Blo 790340 1004663 := bstep (se 1 (by rfl) ⟨753497, by rfl⟩ : syracuseStep 1004663 = 1506995) B1506995
theorem B9655469 : Blo 790340 9655469 := bstep (se 3 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 9655469 = 3620801) B3620801
theorem B2675969 : Blo 790340 2675969 := bstep (se 2 (by rfl) ⟨1003488, by rfl⟩ : syracuseStep 2675969 = 2006977) B2006977
theorem B1004815 : Blo 790340 1004815 := bstep (se 1 (by rfl) ⟨753611, by rfl⟩ : syracuseStep 1004815 = 1507223) B1507223
theorem B1430843 : Blo 790340 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B1004987 : Blo 790340 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B1267145 : Blo 790340 1267145 := bstep (se 2 (by rfl) ⟨475179, by rfl⟩ : syracuseStep 1267145 = 950359) B950359
theorem B1693217 : Blo 790340 1693217 := bstep (se 2 (by rfl) ⟨634956, by rfl⟩ : syracuseStep 1693217 = 1269913) B1269913
theorem B4118539 : Blo 790340 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B2676779 : Blo 790340 2676779 := bstep (se 1 (by rfl) ⟨2007584, by rfl⟩ : syracuseStep 2676779 = 4015169) B4015169
theorem B2283673 : Blo 790340 2283673 := bstep (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) B1712755
theorem B4282541 : Blo 790340 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B1694071 : Blo 790340 1694071 := bstep (se 1 (by rfl) ⟨1270553, by rfl⟩ : syracuseStep 1694071 = 2541107) B2541107
theorem B4512145 : Blo 790340 4512145 := bstep (se 2 (by rfl) ⟨1692054, by rfl⟩ : syracuseStep 4512145 = 3384109) B3384109
theorem B1333705 : Blo 790340 1333705 := bstep (se 2 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 1333705 = 1000279) B1000279
theorem B1268779 : Blo 790340 1268779 := bstep (se 1 (by rfl) ⟨951584, by rfl⟩ : syracuseStep 1268779 = 1903169) B1903169
theorem B5069911 : Blo 790340 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B1334407 : Blo 790340 1334407 := bstep (se 1 (by rfl) ⟨1000805, by rfl⟩ : syracuseStep 1334407 = 2001611) B2001611
theorem B2678075 : Blo 790340 2678075 := bstep (se 1 (by rfl) ⟨2008556, by rfl⟩ : syracuseStep 2678075 = 4017113) B4017113
theorem B3005849 : Blo 790340 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B1335055 : Blo 790340 1335055 := bstep (se 1 (by rfl) ⟨1001291, by rfl⟩ : syracuseStep 1335055 = 2002583) B2002583
theorem B2678561 : Blo 790340 2678561 := bstep (se 2 (by rfl) ⟨1004460, by rfl⟩ : syracuseStep 2678561 = 2008921) B2008921
theorem B1204027 : Blo 790340 1204027 := bstep (se 1 (by rfl) ⟨903020, by rfl⟩ : syracuseStep 1204027 = 1806041) B1806041
theorem B5791877 : Blo 790340 5791877 := bstep (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) B1085977
theorem B2253089 : Blo 790340 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B1335595 : Blo 790340 1335595 := bstep (se 1 (by rfl) ⟨1001696, by rfl⟩ : syracuseStep 1335595 = 2003393) B2003393
theorem B2679155 : Blo 790340 2679155 := bstep (se 1 (by rfl) ⟨2009366, by rfl⟩ : syracuseStep 2679155 = 4018733) B4018733
theorem B2253203 : Blo 790340 2253203 := bstep (se 1 (by rfl) ⟨1689902, by rfl⟩ : syracuseStep 2253203 = 3379805) B3379805
theorem B1335737 : Blo 790340 1335737 := bstep (se 2 (by rfl) ⟨500901, by rfl⟩ : syracuseStep 1335737 = 1001803) B1001803
theorem B4514561 : Blo 790340 4514561 := bstep (se 2 (by rfl) ⟨1692960, by rfl⟩ : syracuseStep 4514561 = 3385921) B3385921
theorem B1336439 : Blo 790340 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B2253977 : Blo 790340 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B15230267 : Blo 790340 15230267 := bstep (se 1 (by rfl) ⟨11422700, by rfl⟩ : syracuseStep 15230267 = 22845401) B22845401
theorem B48850289 : Blo 790340 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B1500601 : Blo 790340 1500601 := bstep (se 2 (by rfl) ⟨562725, by rfl⟩ : syracuseStep 1500601 = 1125451) B1125451
theorem B845327 : Blo 790340 845327 := bstep (se 1 (by rfl) ⟨633995, by rfl⟩ : syracuseStep 845327 = 1267991) B1267991
theorem B1336891 : Blo 790340 1336891 := bstep (se 1 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 1336891 = 2005337) B2005337
theorem B1337033 : Blo 790340 1337033 := bstep (se 2 (by rfl) ⟨501387, by rfl⟩ : syracuseStep 1337033 = 1002775) B1002775
theorem B1500943 : Blo 790340 1500943 := bstep (se 1 (by rfl) ⟨1125707, by rfl⟩ : syracuseStep 1500943 = 2251415) B2251415
theorem B4351781 : Blo 790340 4351781 := bstep (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) B815959
theorem B8546309 : Blo 790340 8546309 := bstep (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) B1602433
theorem B6023483 : Blo 790340 6023483 := bstep (se 1 (by rfl) ⟨4517612, by rfl⟩ : syracuseStep 6023483 = 9035225) B9035225
theorem B1337735 : Blo 790340 1337735 := bstep (se 1 (by rfl) ⟨1003301, by rfl⟩ : syracuseStep 1337735 = 2006603) B2006603
theorem B5073475 : Blo 790340 5073475 := bstep (se 1 (by rfl) ⟨3805106, by rfl⟩ : syracuseStep 5073475 = 7610213) B7610213
theorem B1501831 : Blo 790340 1501831 := bstep (se 1 (by rfl) ⟨1126373, by rfl⟩ : syracuseStep 1501831 = 2252747) B2252747
theorem B2058905 : Blo 790340 2058905 := bstep (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) B1544179
theorem B2255617 : Blo 790340 2255617 := bstep (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) B1691713
theorem B3205903 : Blo 790340 3205903 := bstep (se 1 (by rfl) ⟨2404427, by rfl⟩ : syracuseStep 3205903 = 4808855) B4808855
theorem B3009433 : Blo 790340 3009433 := bstep (se 2 (by rfl) ⟨1128537, by rfl⟩ : syracuseStep 3009433 = 2257075) B2257075
theorem B5434265 : Blo 790340 5434265 := bstep (se 2 (by rfl) ⟨2037849, by rfl⟩ : syracuseStep 5434265 = 4075699) B4075699
theorem B4516793 : Blo 790340 4516793 := bstep (se 2 (by rfl) ⟨1693797, by rfl⟩ : syracuseStep 4516793 = 3387595) B3387595
theorem B846779 : Blo 790340 846779 := bstep (se 1 (by rfl) ⟨635084, by rfl⟩ : syracuseStep 846779 = 1270169) B1270169
theorem B1338383 : Blo 790340 1338383 := bstep (se 1 (by rfl) ⟨1003787, by rfl⟩ : syracuseStep 1338383 = 2007575) B2007575
theorem B4287511 : Blo 790340 4287511 := bstep (se 1 (by rfl) ⟨3215633, by rfl⟩ : syracuseStep 4287511 = 6431267) B6431267
theorem B3009737 : Blo 790340 3009737 := bstep (se 2 (by rfl) ⟨1128651, by rfl⟩ : syracuseStep 3009737 = 2257303) B2257303
theorem B2256187 : Blo 790340 2256187 := bstep (se 1 (by rfl) ⟨1692140, by rfl⟩ : syracuseStep 2256187 = 3384281) B3384281
theorem B2289167 : Blo 790340 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B5697053 : Blo 790340 5697053 := bstep (se 3 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 5697053 = 2136395) B2136395
theorem B1338923 : Blo 790340 1338923 := bstep (se 1 (by rfl) ⟨1004192, by rfl⟩ : syracuseStep 1338923 = 2008385) B2008385
theorem B28929635 : Blo 790340 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B1339321 : Blo 790340 1339321 := bstep (se 2 (by rfl) ⟨502245, by rfl⟩ : syracuseStep 1339321 = 1004491) B1004491
theorem B3010679 : Blo 790340 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B1503623 : Blo 790340 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1340023 : Blo 790340 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B1602337 : Blo 790340 1602337 := bstep (se 2 (by rfl) ⟨600876, by rfl⟩ : syracuseStep 1602337 = 1201753) B1201753
theorem B1340219 : Blo 790340 1340219 := bstep (se 1 (by rfl) ⟨1005164, by rfl⟩ : syracuseStep 1340219 = 2010329) B2010329
theorem B4813721 : Blo 790340 4813721 := bstep (se 2 (by rfl) ⟨1805145, by rfl⟩ : syracuseStep 4813721 = 3610291) B3610291
theorem B816143 : Blo 790340 816143 := bstep (se 1 (by rfl) ⟨612107, by rfl⟩ : syracuseStep 816143 = 1224215) B1224215
theorem B4518935 : Blo 790340 4518935 := bstep (se 1 (by rfl) ⟨3389201, by rfl⟩ : syracuseStep 4518935 = 6778403) B6778403
theorem B3011651 : Blo 790340 3011651 := bstep (se 1 (by rfl) ⟨2258738, by rfl⟩ : syracuseStep 3011651 = 4517477) B4517477
theorem B8582381 : Blo 790340 8582381 := bstep (se 3 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 8582381 = 3218393) B3218393
theorem B4060475 : Blo 790340 4060475 := bstep (se 1 (by rfl) ⟨3045356, by rfl⟩ : syracuseStep 4060475 = 6090713) B6090713
theorem B28865969 : Blo 790340 28865969 := bstep (se 2 (by rfl) ⟨10824738, by rfl⟩ : syracuseStep 28865969 = 21649477) B21649477
theorem B4519435 : Blo 790340 4519435 := bstep (se 1 (by rfl) ⟨3389576, by rfl⟩ : syracuseStep 4519435 = 6779153) B6779153
theorem B1832507 : Blo 790340 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B2258579 : Blo 790340 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B19265201 : Blo 790340 19265201 := bstep (se 2 (by rfl) ⟨7224450, by rfl⟩ : syracuseStep 19265201 = 14448901) B14448901
theorem B5699443 : Blo 790340 5699443 := bstep (se 1 (by rfl) ⟨4274582, by rfl⟩ : syracuseStep 5699443 = 8549165) B8549165
theorem B2259353 : Blo 790340 2259353 := bstep (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) B1694515
theorem B15464945 : Blo 790340 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B3013321 : Blo 790340 3013321 := bstep (se 2 (by rfl) ⟨1129995, by rfl⟩ : syracuseStep 3013321 = 2259991) B2259991
theorem B1506107 : Blo 790340 1506107 := bstep (se 1 (by rfl) ⟨1129580, by rfl⟩ : syracuseStep 1506107 = 2259161) B2259161
theorem B2030483 : Blo 790340 2030483 := bstep (se 1 (by rfl) ⟨1522862, by rfl⟩ : syracuseStep 2030483 = 3045725) B3045725
theorem B1014799 : Blo 790340 1014799 := bstep (se 1 (by rfl) ⟨761099, by rfl⟩ : syracuseStep 1014799 = 1522199) B1522199
theorem B1506593 : Blo 790340 1506593 := bstep (se 2 (by rfl) ⟨564972, by rfl⟩ : syracuseStep 1506593 = 1129945) B1129945
theorem B1899911 : Blo 790340 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B4521419 : Blo 790340 4521419 := bstep (se 1 (by rfl) ⟨3391064, by rfl⟩ : syracuseStep 4521419 = 6782129) B6782129
theorem B6028829 : Blo 790340 6028829 := bstep (se 3 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 6028829 = 2260811) B2260811
theorem B4128563 : Blo 790340 4128563 := bstep (se 1 (by rfl) ⟨3096422, by rfl⟩ : syracuseStep 4128563 = 6192845) B6192845
theorem B14450501 : Blo 790340 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B6029315 : Blo 790340 6029315 := bstep (se 1 (by rfl) ⟨4521986, by rfl⟩ : syracuseStep 6029315 = 9043973) B9043973
theorem B8552627 : Blo 790340 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B26083685 : Blo 790340 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B3015265 : Blo 790340 3015265 := bstep (se 2 (by rfl) ⟨1130724, by rfl⟩ : syracuseStep 3015265 = 2261449) B2261449
theorem B2851537 : Blo 790340 2851537 := bstep (se 2 (by rfl) ⟨1069326, by rfl⟩ : syracuseStep 2851537 = 2138653) B2138653
theorem B3015737 : Blo 790340 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B36602999 : Blo 790340 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B10159505 : Blo 790340 10159505 := bstep (se 2 (by rfl) ⟨3809814, by rfl⟩ : syracuseStep 10159505 = 7619629) B7619629
theorem B2033191 : Blo 790340 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B7604063 : Blo 790340 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B2000801 : Blo 790340 2000801 := bstep (se 2 (by rfl) ⟨750300, by rfl⟩ : syracuseStep 2000801 = 1500601) B1500601
theorem B2852921 : Blo 790340 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B2853181 : Blo 790340 2853181 := bstep (se 3 (by rfl) ⟨534971, by rfl⟩ : syracuseStep 2853181 = 1069943) B1069943
theorem B2001257 : Blo 790340 2001257 := bstep (se 2 (by rfl) ⟨750471, by rfl⟩ : syracuseStep 2001257 = 1500943) B1500943
theorem B6031745 : Blo 790340 6031745 := bstep (se 2 (by rfl) ⟨2261904, by rfl⟩ : syracuseStep 6031745 = 4523809) B4523809
theorem B3378095 : Blo 790340 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B1444873 : Blo 790340 1444873 := bstep (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) B1083655
theorem B5147819 : Blo 790340 5147819 := bstep (se 1 (by rfl) ⟨3860864, by rfl⟩ : syracuseStep 5147819 = 7721729) B7721729
theorem B3804355 : Blo 790340 3804355 := bstep (se 1 (by rfl) ⟨2853266, by rfl⟩ : syracuseStep 3804355 = 5706533) B5706533
theorem B3214583 : Blo 790340 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B18320705 : Blo 790340 18320705 := bstep (se 2 (by rfl) ⟨6870264, by rfl⟩ : syracuseStep 18320705 = 13740529) B13740529
theorem B1609067 : Blo 790340 1609067 := bstep (se 1 (by rfl) ⟨1206800, by rfl⟩ : syracuseStep 1609067 = 2413601) B2413601
theorem B2002441 : Blo 790340 2002441 := bstep (se 2 (by rfl) ⟨750915, by rfl⟩ : syracuseStep 2002441 = 1501831) B1501831
theorem B6524513 : Blo 790340 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B790351 : Blo 790340 790351 := bstep (se 1 (by rfl) ⟨592763, by rfl⟩ : syracuseStep 790351 = 1185527) B1185527
theorem B790367 : Blo 790340 790367 := bstep (se 1 (by rfl) ⟨592775, by rfl⟩ : syracuseStep 790367 = 1185551) B1185551
theorem B790395 : Blo 790340 790395 := bstep (se 1 (by rfl) ⟨592796, by rfl⟩ : syracuseStep 790395 = 1185593) B1185593
theorem B790447 : Blo 790340 790447 := bstep (se 1 (by rfl) ⟨592835, by rfl⟩ : syracuseStep 790447 = 1185671) B1185671
theorem B4001723 : Blo 790340 4001723 := bstep (se 1 (by rfl) ⟨3001292, by rfl⟩ : syracuseStep 4001723 = 6002585) B6002585
theorem B790471 : Blo 790340 790471 := bstep (se 1 (by rfl) ⟨592853, by rfl⟩ : syracuseStep 790471 = 1185707) B1185707
theorem B790491 : Blo 790340 790491 := bstep (se 1 (by rfl) ⟨592868, by rfl⟩ : syracuseStep 790491 = 1185737) B1185737
theorem B790567 : Blo 790340 790567 := bstep (se 1 (by rfl) ⟨592925, by rfl⟩ : syracuseStep 790567 = 1185851) B1185851
theorem B790607 : Blo 790340 790607 := bstep (se 1 (by rfl) ⟨592955, by rfl⟩ : syracuseStep 790607 = 1185911) B1185911
theorem B790623 : Blo 790340 790623 := bstep (se 1 (by rfl) ⟨592967, by rfl⟩ : syracuseStep 790623 = 1185935) B1185935
theorem B2855027 : Blo 790340 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B790651 : Blo 790340 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B790703 : Blo 790340 790703 := bstep (se 1 (by rfl) ⟨593027, by rfl⟩ : syracuseStep 790703 = 1186055) B1186055
theorem B790727 : Blo 790340 790727 := bstep (se 1 (by rfl) ⟨593045, by rfl⟩ : syracuseStep 790727 = 1186091) B1186091
theorem B790747 : Blo 790340 790747 := bstep (se 1 (by rfl) ⟨593060, by rfl⟩ : syracuseStep 790747 = 1186121) B1186121
theorem B790823 : Blo 790340 790823 := bstep (se 1 (by rfl) ⟨593117, by rfl⟩ : syracuseStep 790823 = 1186235) B1186235
theorem B790863 : Blo 790340 790863 := bstep (se 1 (by rfl) ⟨593147, by rfl⟩ : syracuseStep 790863 = 1186295) B1186295
theorem B790879 : Blo 790340 790879 := bstep (se 1 (by rfl) ⟨593159, by rfl⟩ : syracuseStep 790879 = 1186319) B1186319
theorem B790907 : Blo 790340 790907 := bstep (se 1 (by rfl) ⟨593180, by rfl⟩ : syracuseStep 790907 = 1186361) B1186361
theorem B790959 : Blo 790340 790959 := bstep (se 1 (by rfl) ⟨593219, by rfl⟩ : syracuseStep 790959 = 1186439) B1186439
theorem B790983 : Blo 790340 790983 := bstep (se 1 (by rfl) ⟨593237, by rfl⟩ : syracuseStep 790983 = 1186475) B1186475
theorem B791003 : Blo 790340 791003 := bstep (se 1 (by rfl) ⟨593252, by rfl⟩ : syracuseStep 791003 = 1186505) B1186505
theorem B791079 : Blo 790340 791079 := bstep (se 1 (by rfl) ⟨593309, by rfl⟩ : syracuseStep 791079 = 1186619) B1186619
theorem B791119 : Blo 790340 791119 := bstep (se 1 (by rfl) ⟨593339, by rfl⟩ : syracuseStep 791119 = 1186679) B1186679
theorem B791135 : Blo 790340 791135 := bstep (se 1 (by rfl) ⟨593351, by rfl⟩ : syracuseStep 791135 = 1186703) B1186703
theorem B791163 : Blo 790340 791163 := bstep (se 1 (by rfl) ⟨593372, by rfl⟩ : syracuseStep 791163 = 1186745) B1186745
theorem B791215 : Blo 790340 791215 := bstep (se 1 (by rfl) ⟨593411, by rfl⟩ : syracuseStep 791215 = 1186823) B1186823
theorem B791239 : Blo 790340 791239 := bstep (se 1 (by rfl) ⟨593429, by rfl⟩ : syracuseStep 791239 = 1186859) B1186859
theorem B791259 : Blo 790340 791259 := bstep (se 1 (by rfl) ⟨593444, by rfl⟩ : syracuseStep 791259 = 1186889) B1186889
theorem B791335 : Blo 790340 791335 := bstep (se 1 (by rfl) ⟨593501, by rfl⟩ : syracuseStep 791335 = 1187003) B1187003
theorem B791375 : Blo 790340 791375 := bstep (se 1 (by rfl) ⟨593531, by rfl⟩ : syracuseStep 791375 = 1187063) B1187063
theorem B791391 : Blo 790340 791391 := bstep (se 1 (by rfl) ⟨593543, by rfl⟩ : syracuseStep 791391 = 1187087) B1187087
theorem B791419 : Blo 790340 791419 := bstep (se 1 (by rfl) ⟨593564, by rfl⟩ : syracuseStep 791419 = 1187129) B1187129
theorem B791471 : Blo 790340 791471 := bstep (se 1 (by rfl) ⟨593603, by rfl⟩ : syracuseStep 791471 = 1187207) B1187207
theorem B2003899 : Blo 790340 2003899 := bstep (se 1 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 2003899 = 3005849) B3005849
theorem B791495 : Blo 790340 791495 := bstep (se 1 (by rfl) ⟨593621, by rfl⟩ : syracuseStep 791495 = 1187243) B1187243
theorem B791515 : Blo 790340 791515 := bstep (se 1 (by rfl) ⟨593636, by rfl⟩ : syracuseStep 791515 = 1187273) B1187273
theorem B791591 : Blo 790340 791591 := bstep (se 1 (by rfl) ⟨593693, by rfl⟩ : syracuseStep 791591 = 1187387) B1187387
theorem B7214129 : Blo 790340 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B791631 : Blo 790340 791631 := bstep (se 1 (by rfl) ⟨593723, by rfl⟩ : syracuseStep 791631 = 1187447) B1187447
theorem B791647 : Blo 790340 791647 := bstep (se 1 (by rfl) ⟨593735, by rfl⟩ : syracuseStep 791647 = 1187471) B1187471
theorem B791675 : Blo 790340 791675 := bstep (se 1 (by rfl) ⟨593756, by rfl⟩ : syracuseStep 791675 = 1187513) B1187513
theorem B791727 : Blo 790340 791727 := bstep (se 1 (by rfl) ⟨593795, by rfl⟩ : syracuseStep 791727 = 1187591) B1187591
theorem B791751 : Blo 790340 791751 := bstep (se 1 (by rfl) ⟨593813, by rfl⟩ : syracuseStep 791751 = 1187627) B1187627
theorem B4003019 : Blo 790340 4003019 := bstep (se 1 (by rfl) ⟨3002264, by rfl⟩ : syracuseStep 4003019 = 6004529) B6004529
theorem B791771 : Blo 790340 791771 := bstep (se 1 (by rfl) ⟨593828, by rfl⟩ : syracuseStep 791771 = 1187657) B1187657
theorem B791847 : Blo 790340 791847 := bstep (se 1 (by rfl) ⟨593885, by rfl⟩ : syracuseStep 791847 = 1187771) B1187771
theorem B791887 : Blo 790340 791887 := bstep (se 1 (by rfl) ⟨593915, by rfl⟩ : syracuseStep 791887 = 1187831) B1187831
theorem B791903 : Blo 790340 791903 := bstep (se 1 (by rfl) ⟨593927, by rfl⟩ : syracuseStep 791903 = 1187855) B1187855
theorem B791931 : Blo 790340 791931 := bstep (se 1 (by rfl) ⟨593948, by rfl⟩ : syracuseStep 791931 = 1187897) B1187897
theorem B49550723 : Blo 790340 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B791983 : Blo 790340 791983 := bstep (se 1 (by rfl) ⟨593987, by rfl⟩ : syracuseStep 791983 = 1187975) B1187975
theorem B792007 : Blo 790340 792007 := bstep (se 1 (by rfl) ⟨594005, by rfl⟩ : syracuseStep 792007 = 1188011) B1188011
theorem B7607753 : Blo 790340 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B792027 : Blo 790340 792027 := bstep (se 1 (by rfl) ⟨594020, by rfl⟩ : syracuseStep 792027 = 1188041) B1188041
theorem B792103 : Blo 790340 792103 := bstep (se 1 (by rfl) ⟨594077, by rfl⟩ : syracuseStep 792103 = 1188155) B1188155
theorem B792143 : Blo 790340 792143 := bstep (se 1 (by rfl) ⟨594107, by rfl⟩ : syracuseStep 792143 = 1188215) B1188215
theorem B792159 : Blo 790340 792159 := bstep (se 1 (by rfl) ⟨594119, by rfl⟩ : syracuseStep 792159 = 1188239) B1188239
theorem B890491 : Blo 790340 890491 := bstep (se 1 (by rfl) ⟨667868, by rfl⟩ : syracuseStep 890491 = 1335737) B1335737
theorem B792187 : Blo 790340 792187 := bstep (se 1 (by rfl) ⟨594140, by rfl⟩ : syracuseStep 792187 = 1188281) B1188281
theorem B792239 : Blo 790340 792239 := bstep (se 1 (by rfl) ⟨594179, by rfl⟩ : syracuseStep 792239 = 1188359) B1188359
theorem B10819271 : Blo 790340 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B792263 : Blo 790340 792263 := bstep (se 1 (by rfl) ⟨594197, by rfl⟩ : syracuseStep 792263 = 1188395) B1188395
theorem B792283 : Blo 790340 792283 := bstep (se 1 (by rfl) ⟨594212, by rfl⟩ : syracuseStep 792283 = 1188425) B1188425
theorem B9148153 : Blo 790340 9148153 := bstep (se 2 (by rfl) ⟨3430557, by rfl⟩ : syracuseStep 9148153 = 6861115) B6861115
theorem B792359 : Blo 790340 792359 := bstep (se 1 (by rfl) ⟨594269, by rfl⟩ : syracuseStep 792359 = 1188539) B1188539
theorem B6428483 : Blo 790340 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B792399 : Blo 790340 792399 := bstep (se 1 (by rfl) ⟨594299, by rfl⟩ : syracuseStep 792399 = 1188599) B1188599
theorem B792415 : Blo 790340 792415 := bstep (se 1 (by rfl) ⟨594311, by rfl⟩ : syracuseStep 792415 = 1188623) B1188623
theorem B1185641 : Blo 790340 1185641 := bstep (se 2 (by rfl) ⟨444615, by rfl⟩ : syracuseStep 1185641 = 889231) B889231
theorem B792443 : Blo 790340 792443 := bstep (se 1 (by rfl) ⟨594332, by rfl⟩ : syracuseStep 792443 = 1188665) B1188665
theorem B792495 : Blo 790340 792495 := bstep (se 1 (by rfl) ⟨594371, by rfl⟩ : syracuseStep 792495 = 1188743) B1188743
theorem B1185719 : Blo 790340 1185719 := bstep (se 1 (by rfl) ⟨889289, by rfl⟩ : syracuseStep 1185719 = 1778579) B1778579
theorem B792519 : Blo 790340 792519 := bstep (se 1 (by rfl) ⟨594389, by rfl⟩ : syracuseStep 792519 = 1188779) B1188779
theorem B1185755 : Blo 790340 1185755 := bstep (se 1 (by rfl) ⟨889316, by rfl⟩ : syracuseStep 1185755 = 1778633) B1778633
theorem B792539 : Blo 790340 792539 := bstep (se 1 (by rfl) ⟨594404, by rfl⟩ : syracuseStep 792539 = 1188809) B1188809
theorem B792615 : Blo 790340 792615 := bstep (se 1 (by rfl) ⟨594461, by rfl⟩ : syracuseStep 792615 = 1188923) B1188923
theorem B890959 : Blo 790340 890959 := bstep (se 1 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 890959 = 1336439) B1336439
theorem B792655 : Blo 790340 792655 := bstep (se 1 (by rfl) ⟨594491, by rfl⟩ : syracuseStep 792655 = 1188983) B1188983
theorem B792671 : Blo 790340 792671 := bstep (se 1 (by rfl) ⟨594503, by rfl⟩ : syracuseStep 792671 = 1189007) B1189007
theorem B792699 : Blo 790340 792699 := bstep (se 1 (by rfl) ⟨594524, by rfl⟩ : syracuseStep 792699 = 1189049) B1189049
theorem B1906859 : Blo 790340 1906859 := bstep (se 1 (by rfl) ⟨1430144, by rfl⟩ : syracuseStep 1906859 = 2860289) B2860289
theorem B792751 : Blo 790340 792751 := bstep (se 1 (by rfl) ⟨594563, by rfl⟩ : syracuseStep 792751 = 1189127) B1189127
theorem B792775 : Blo 790340 792775 := bstep (se 1 (by rfl) ⟨594581, by rfl⟩ : syracuseStep 792775 = 1189163) B1189163
theorem B792795 : Blo 790340 792795 := bstep (se 1 (by rfl) ⟨594596, by rfl⟩ : syracuseStep 792795 = 1189193) B1189193
theorem B792871 : Blo 790340 792871 := bstep (se 1 (by rfl) ⟨594653, by rfl⟩ : syracuseStep 792871 = 1189307) B1189307
theorem B792911 : Blo 790340 792911 := bstep (se 1 (by rfl) ⟨594683, by rfl⟩ : syracuseStep 792911 = 1189367) B1189367
theorem B792927 : Blo 790340 792927 := bstep (se 1 (by rfl) ⟨594695, by rfl⟩ : syracuseStep 792927 = 1189391) B1189391
theorem B792955 : Blo 790340 792955 := bstep (se 1 (by rfl) ⟨594716, by rfl⟩ : syracuseStep 792955 = 1189433) B1189433
theorem B2136449 : Blo 790340 2136449 := bstep (se 2 (by rfl) ⟨801168, by rfl⟩ : syracuseStep 2136449 = 1602337) B1602337
theorem B1186223 : Blo 790340 1186223 := bstep (se 1 (by rfl) ⟨889667, by rfl⟩ : syracuseStep 1186223 = 1779335) B1779335
theorem B793007 : Blo 790340 793007 := bstep (se 1 (by rfl) ⟨594755, by rfl⟩ : syracuseStep 793007 = 1189511) B1189511
theorem B793031 : Blo 790340 793031 := bstep (se 1 (by rfl) ⟨594773, by rfl⟩ : syracuseStep 793031 = 1189547) B1189547
theorem B891355 : Blo 790340 891355 := bstep (se 1 (by rfl) ⟨668516, by rfl⟩ : syracuseStep 891355 = 1337033) B1337033
theorem B793051 : Blo 790340 793051 := bstep (se 1 (by rfl) ⟨594788, by rfl⟩ : syracuseStep 793051 = 1189577) B1189577
theorem B1186313 : Blo 790340 1186313 := bstep (se 2 (by rfl) ⟨444867, by rfl⟩ : syracuseStep 1186313 = 889735) B889735
theorem B1186343 : Blo 790340 1186343 := bstep (se 1 (by rfl) ⟨889757, by rfl⟩ : syracuseStep 1186343 = 1779515) B1779515
theorem B793127 : Blo 790340 793127 := bstep (se 1 (by rfl) ⟨594845, by rfl⟩ : syracuseStep 793127 = 1189691) B1189691
theorem B793167 : Blo 790340 793167 := bstep (se 1 (by rfl) ⟨594875, by rfl⟩ : syracuseStep 793167 = 1189751) B1189751
theorem B793183 : Blo 790340 793183 := bstep (se 1 (by rfl) ⟨594887, by rfl⟩ : syracuseStep 793183 = 1189775) B1189775
theorem B1186427 : Blo 790340 1186427 := bstep (se 1 (by rfl) ⟨889820, by rfl⟩ : syracuseStep 1186427 = 1779641) B1779641
theorem B793211 : Blo 790340 793211 := bstep (se 1 (by rfl) ⟨594908, by rfl⟩ : syracuseStep 793211 = 1189817) B1189817
theorem B793263 : Blo 790340 793263 := bstep (se 1 (by rfl) ⟨594947, by rfl⟩ : syracuseStep 793263 = 1189895) B1189895
theorem B5085881 : Blo 790340 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B793287 : Blo 790340 793287 := bstep (se 1 (by rfl) ⟨594965, by rfl⟩ : syracuseStep 793287 = 1189931) B1189931
theorem B793307 : Blo 790340 793307 := bstep (se 1 (by rfl) ⟨594980, by rfl⟩ : syracuseStep 793307 = 1189961) B1189961
theorem B1186553 : Blo 790340 1186553 := bstep (se 2 (by rfl) ⟨444957, by rfl⟩ : syracuseStep 1186553 = 889915) B889915
theorem B793383 : Blo 790340 793383 := bstep (se 1 (by rfl) ⟨595037, by rfl⟩ : syracuseStep 793383 = 1190075) B1190075
theorem B793423 : Blo 790340 793423 := bstep (se 1 (by rfl) ⟨595067, by rfl⟩ : syracuseStep 793423 = 1190135) B1190135
theorem B1186655 : Blo 790340 1186655 := bstep (se 1 (by rfl) ⟨889991, by rfl⟩ : syracuseStep 1186655 = 1779983) B1779983
theorem B793439 : Blo 790340 793439 := bstep (se 1 (by rfl) ⟨595079, by rfl⟩ : syracuseStep 793439 = 1190159) B1190159
theorem B1186667 : Blo 790340 1186667 := bstep (se 1 (by rfl) ⟨890000, by rfl⟩ : syracuseStep 1186667 = 1780001) B1780001
theorem B793467 : Blo 790340 793467 := bstep (se 1 (by rfl) ⟨595100, by rfl⟩ : syracuseStep 793467 = 1190201) B1190201
theorem B891823 : Blo 790340 891823 := bstep (se 1 (by rfl) ⟨668867, by rfl⟩ : syracuseStep 891823 = 1337735) B1337735
theorem B793519 : Blo 790340 793519 := bstep (se 1 (by rfl) ⟨595139, by rfl⟩ : syracuseStep 793519 = 1190279) B1190279
theorem B3218359 : Blo 790340 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B793543 : Blo 790340 793543 := bstep (se 1 (by rfl) ⟨595157, by rfl⟩ : syracuseStep 793543 = 1190315) B1190315
theorem B793563 : Blo 790340 793563 := bstep (se 1 (by rfl) ⟨595172, by rfl⟩ : syracuseStep 793563 = 1190345) B1190345
theorem B793639 : Blo 790340 793639 := bstep (se 1 (by rfl) ⟨595229, by rfl⟩ : syracuseStep 793639 = 1190459) B1190459
theorem B1186895 : Blo 790340 1186895 := bstep (se 1 (by rfl) ⟨890171, by rfl⟩ : syracuseStep 1186895 = 1780343) B1780343
theorem B793679 : Blo 790340 793679 := bstep (se 1 (by rfl) ⟨595259, by rfl⟩ : syracuseStep 793679 = 1190519) B1190519
theorem B793695 : Blo 790340 793695 := bstep (se 1 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 793695 = 1190543) B1190543
theorem B793723 : Blo 790340 793723 := bstep (se 1 (by rfl) ⟨595292, by rfl⟩ : syracuseStep 793723 = 1190585) B1190585
theorem B793775 : Blo 790340 793775 := bstep (se 1 (by rfl) ⟨595331, by rfl⟩ : syracuseStep 793775 = 1190663) B1190663
theorem B1187015 : Blo 790340 1187015 := bstep (se 1 (by rfl) ⟨890261, by rfl⟩ : syracuseStep 1187015 = 1780523) B1780523
theorem B793799 : Blo 790340 793799 := bstep (se 1 (by rfl) ⟨595349, by rfl⟩ : syracuseStep 793799 = 1190699) B1190699
theorem B793819 : Blo 790340 793819 := bstep (se 1 (by rfl) ⟨595364, by rfl⟩ : syracuseStep 793819 = 1190729) B1190729
theorem B793895 : Blo 790340 793895 := bstep (se 1 (by rfl) ⟨595421, by rfl⟩ : syracuseStep 793895 = 1190843) B1190843
theorem B793935 : Blo 790340 793935 := bstep (se 1 (by rfl) ⟨595451, by rfl⟩ : syracuseStep 793935 = 1190903) B1190903
theorem B892255 : Blo 790340 892255 := bstep (se 1 (by rfl) ⟨669191, by rfl⟩ : syracuseStep 892255 = 1338383) B1338383
theorem B793951 : Blo 790340 793951 := bstep (se 1 (by rfl) ⟨595463, by rfl⟩ : syracuseStep 793951 = 1190927) B1190927
theorem B1187177 : Blo 790340 1187177 := bstep (se 2 (by rfl) ⟨445191, by rfl⟩ : syracuseStep 1187177 = 890383) B890383
theorem B793979 : Blo 790340 793979 := bstep (se 1 (by rfl) ⟨595484, by rfl⟩ : syracuseStep 793979 = 1190969) B1190969
theorem B794031 : Blo 790340 794031 := bstep (se 1 (by rfl) ⟨595523, by rfl⟩ : syracuseStep 794031 = 1191047) B1191047
theorem B1187255 : Blo 790340 1187255 := bstep (se 1 (by rfl) ⟨890441, by rfl⟩ : syracuseStep 1187255 = 1780883) B1780883
theorem B794055 : Blo 790340 794055 := bstep (se 1 (by rfl) ⟨595541, by rfl⟩ : syracuseStep 794055 = 1191083) B1191083
theorem B1187291 : Blo 790340 1187291 := bstep (se 1 (by rfl) ⟨890468, by rfl⟩ : syracuseStep 1187291 = 1780937) B1780937
theorem B2006491 : Blo 790340 2006491 := bstep (se 1 (by rfl) ⟨1504868, by rfl⟩ : syracuseStep 2006491 = 3009737) B3009737
theorem B794075 : Blo 790340 794075 := bstep (se 1 (by rfl) ⟨595556, by rfl⟩ : syracuseStep 794075 = 1191113) B1191113
theorem B794151 : Blo 790340 794151 := bstep (se 1 (by rfl) ⟨595613, by rfl⟩ : syracuseStep 794151 = 1191227) B1191227
theorem B794191 : Blo 790340 794191 := bstep (se 1 (by rfl) ⟨595643, by rfl⟩ : syracuseStep 794191 = 1191287) B1191287
theorem B794207 : Blo 790340 794207 := bstep (se 1 (by rfl) ⟨595655, by rfl⟩ : syracuseStep 794207 = 1191311) B1191311
theorem B794235 : Blo 790340 794235 := bstep (se 1 (by rfl) ⟨595676, by rfl⟩ : syracuseStep 794235 = 1191353) B1191353
theorem B794287 : Blo 790340 794287 := bstep (se 1 (by rfl) ⟨595715, by rfl⟩ : syracuseStep 794287 = 1191431) B1191431
theorem B892615 : Blo 790340 892615 := bstep (se 1 (by rfl) ⟨669461, by rfl⟩ : syracuseStep 892615 = 1338923) B1338923
theorem B794311 : Blo 790340 794311 := bstep (se 1 (by rfl) ⟨595733, by rfl⟩ : syracuseStep 794311 = 1191467) B1191467
theorem B794331 : Blo 790340 794331 := bstep (se 1 (by rfl) ⟨595748, by rfl⟩ : syracuseStep 794331 = 1191497) B1191497
theorem B1187759 : Blo 790340 1187759 := bstep (se 1 (by rfl) ⟨890819, by rfl⟩ : syracuseStep 1187759 = 1781639) B1781639
theorem B1187849 : Blo 790340 1187849 := bstep (se 2 (by rfl) ⟨445443, by rfl⟩ : syracuseStep 1187849 = 890887) B890887
theorem B1187879 : Blo 790340 1187879 := bstep (se 1 (by rfl) ⟨890909, by rfl⟩ : syracuseStep 1187879 = 1781819) B1781819
theorem B2007119 : Blo 790340 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B1187963 : Blo 790340 1187963 := bstep (se 1 (by rfl) ⟨890972, by rfl⟩ : syracuseStep 1187963 = 1781945) B1781945
theorem B1188089 : Blo 790340 1188089 := bstep (se 2 (by rfl) ⟨445533, by rfl⟩ : syracuseStep 1188089 = 891067) B891067
theorem B1188191 : Blo 790340 1188191 := bstep (se 1 (by rfl) ⟨891143, by rfl⟩ : syracuseStep 1188191 = 1782287) B1782287
theorem B1188203 : Blo 790340 1188203 := bstep (se 1 (by rfl) ⟨891152, by rfl⟩ : syracuseStep 1188203 = 1782305) B1782305
theorem B893479 : Blo 790340 893479 := bstep (se 1 (by rfl) ⟨670109, by rfl⟩ : syracuseStep 893479 = 1340219) B1340219
theorem B1188431 : Blo 790340 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B1778273 : Blo 790340 1778273 := bstep (se 2 (by rfl) ⟨666852, by rfl⟩ : syracuseStep 1778273 = 1333705) B1333705
theorem B1188551 : Blo 790340 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B2007767 : Blo 790340 2007767 := bstep (se 1 (by rfl) ⟨1505825, by rfl⟩ : syracuseStep 2007767 = 3011651) B3011651
theorem B1188713 : Blo 790340 1188713 := bstep (se 2 (by rfl) ⟨445767, by rfl⟩ : syracuseStep 1188713 = 891535) B891535
theorem B1778615 : Blo 790340 1778615 := bstep (se 1 (by rfl) ⟨1333961, by rfl⟩ : syracuseStep 1778615 = 2667923) B2667923
theorem B1188791 : Blo 790340 1188791 := bstep (se 1 (by rfl) ⟨891593, by rfl⟩ : syracuseStep 1188791 = 1783187) B1783187
theorem B19243979 : Blo 790340 19243979 := bstep (se 1 (by rfl) ⟨14432984, by rfl⟩ : syracuseStep 19243979 = 28865969) B28865969
theorem B1188827 : Blo 790340 1188827 := bstep (se 1 (by rfl) ⟨891620, by rfl⟩ : syracuseStep 1188827 = 1783241) B1783241
theorem B1221671 : Blo 790340 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B1189295 : Blo 790340 1189295 := bstep (se 1 (by rfl) ⟨891971, by rfl⟩ : syracuseStep 1189295 = 1783943) B1783943
theorem B6759881 : Blo 790340 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B1779209 : Blo 790340 1779209 := bstep (se 2 (by rfl) ⟨667203, by rfl⟩ : syracuseStep 1779209 = 1334407) B1334407
theorem B1189385 : Blo 790340 1189385 := bstep (se 2 (by rfl) ⟨446019, by rfl⟩ : syracuseStep 1189385 = 892039) B892039
theorem B1189415 : Blo 790340 1189415 := bstep (se 1 (by rfl) ⟨892061, by rfl⟩ : syracuseStep 1189415 = 1784123) B1784123
theorem B3384929 : Blo 790340 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B1189499 : Blo 790340 1189499 := bstep (se 1 (by rfl) ⟨892124, by rfl⟩ : syracuseStep 1189499 = 1784249) B1784249
theorem B1189625 : Blo 790340 1189625 := bstep (se 2 (by rfl) ⟨446109, by rfl⟩ : syracuseStep 1189625 = 892219) B892219
theorem B1779551 : Blo 790340 1779551 := bstep (se 1 (by rfl) ⟨1334663, by rfl⟩ : syracuseStep 1779551 = 2669327) B2669327
theorem B1189727 : Blo 790340 1189727 := bstep (se 1 (by rfl) ⟨892295, by rfl⟩ : syracuseStep 1189727 = 1784591) B1784591
theorem B1189739 : Blo 790340 1189739 := bstep (se 1 (by rfl) ⟨892304, by rfl⟩ : syracuseStep 1189739 = 1784609) B1784609
theorem B1353655 : Blo 790340 1353655 := bstep (se 1 (by rfl) ⟨1015241, by rfl⟩ : syracuseStep 1353655 = 2030483) B2030483
theorem B54929411 : Blo 790340 54929411 := bstep (se 1 (by rfl) ⟨41197058, by rfl⟩ : syracuseStep 54929411 = 82394117) B82394117
theorem B1779731 : Blo 790340 1779731 := bstep (se 1 (by rfl) ⟨1334798, by rfl⟩ : syracuseStep 1779731 = 2669597) B2669597
theorem B1189967 : Blo 790340 1189967 := bstep (se 1 (by rfl) ⟨892475, by rfl⟩ : syracuseStep 1189967 = 1784951) B1784951
theorem B1190087 : Blo 790340 1190087 := bstep (se 1 (by rfl) ⟨892565, by rfl⟩ : syracuseStep 1190087 = 1785131) B1785131
theorem B4008203 : Blo 790340 4008203 := bstep (se 1 (by rfl) ⟨3006152, by rfl⟩ : syracuseStep 4008203 = 6012305) B6012305
theorem B1780073 : Blo 790340 1780073 := bstep (se 2 (by rfl) ⟨667527, by rfl⟩ : syracuseStep 1780073 = 1335055) B1335055
theorem B1190249 : Blo 790340 1190249 := bstep (se 2 (by rfl) ⟨446343, by rfl⟩ : syracuseStep 1190249 = 892687) B892687
theorem B1190327 : Blo 790340 1190327 := bstep (se 1 (by rfl) ⟨892745, by rfl⟩ : syracuseStep 1190327 = 1785491) B1785491
theorem B6760907 : Blo 790340 6760907 := bstep (se 1 (by rfl) ⟨5070680, by rfl⟩ : syracuseStep 6760907 = 10141361) B10141361
theorem B1190363 : Blo 790340 1190363 := bstep (se 1 (by rfl) ⟨892772, by rfl⟩ : syracuseStep 1190363 = 1785545) B1785545
theorem B3811873 : Blo 790340 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B1190831 : Blo 790340 1190831 := bstep (se 1 (by rfl) ⟨893123, by rfl⟩ : syracuseStep 1190831 = 1786247) B1786247
theorem B1780667 : Blo 790340 1780667 := bstep (se 1 (by rfl) ⟨1335500, by rfl⟩ : syracuseStep 1780667 = 2671001) B2671001
theorem B1190921 : Blo 790340 1190921 := bstep (se 2 (by rfl) ⟨446595, by rfl⟩ : syracuseStep 1190921 = 893191) B893191
theorem B1190951 : Blo 790340 1190951 := bstep (se 1 (by rfl) ⟨893213, by rfl⟩ : syracuseStep 1190951 = 1786427) B1786427
theorem B1780793 : Blo 790340 1780793 := bstep (se 2 (by rfl) ⟨667797, by rfl⟩ : syracuseStep 1780793 = 1335595) B1335595
theorem B1191035 : Blo 790340 1191035 := bstep (se 1 (by rfl) ⟨893276, by rfl⟩ : syracuseStep 1191035 = 1786553) B1786553
theorem B2010359 : Blo 790340 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B1191161 : Blo 790340 1191161 := bstep (se 2 (by rfl) ⟨446685, by rfl⟩ : syracuseStep 1191161 = 893371) B893371
theorem B1191263 : Blo 790340 1191263 := bstep (se 1 (by rfl) ⟨893447, by rfl⟩ : syracuseStep 1191263 = 1786895) B1786895
theorem B1191275 : Blo 790340 1191275 := bstep (se 1 (by rfl) ⟨893456, by rfl⟩ : syracuseStep 1191275 = 1786913) B1786913
theorem B1781135 : Blo 790340 1781135 := bstep (se 1 (by rfl) ⟨1335851, by rfl⟩ : syracuseStep 1781135 = 2671703) B2671703
theorem B20589997 : Blo 790340 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B3386843 : Blo 790340 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B7613939 : Blo 790340 7613939 := bstep (se 1 (by rfl) ⟨5710454, by rfl⟩ : syracuseStep 7613939 = 11420909) B11420909
theorem B1191503 : Blo 790340 1191503 := bstep (se 1 (by rfl) ⟨893627, by rfl⟩ : syracuseStep 1191503 = 1787255) B1787255
theorem B6008417 : Blo 790340 6008417 := bstep (se 2 (by rfl) ⟨2253156, by rfl⟩ : syracuseStep 6008417 = 4506313) B4506313
theorem B4009661 : Blo 790340 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B1781459 : Blo 790340 1781459 := bstep (se 1 (by rfl) ⟨1336094, by rfl⟩ : syracuseStep 1781459 = 2672189) B2672189
theorem B4009823 : Blo 790340 4009823 := bstep (se 1 (by rfl) ⟨3007367, by rfl⟩ : syracuseStep 4009823 = 6014735) B6014735
theorem B58470493 : Blo 790340 58470493 := bstep (se 3 (by rfl) ⟨10963217, by rfl⟩ : syracuseStep 58470493 = 21926435) B21926435
theorem B1782395 : Blo 790340 1782395 := bstep (se 1 (by rfl) ⟨1336796, by rfl⟩ : syracuseStep 1782395 = 2673593) B2673593
theorem B1782521 : Blo 790340 1782521 := bstep (se 2 (by rfl) ⟨668445, by rfl⟩ : syracuseStep 1782521 = 1336891) B1336891
theorem B10138385 : Blo 790340 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B1782791 : Blo 790340 1782791 := bstep (se 1 (by rfl) ⟨1337093, by rfl⟩ : syracuseStep 1782791 = 2674187) B2674187
theorem B6009875 : Blo 790340 6009875 := bstep (se 1 (by rfl) ⟨4507406, by rfl⟩ : syracuseStep 6009875 = 9014813) B9014813
theorem B6763571 : Blo 790340 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B2667599 : Blo 790340 2667599 := bstep (se 1 (by rfl) ⟨2000699, by rfl⟩ : syracuseStep 2667599 = 4001399) B4001399
theorem B1782863 : Blo 790340 1782863 := bstep (se 1 (by rfl) ⟨1337147, by rfl⟩ : syracuseStep 1782863 = 2674295) B2674295
theorem B2176381 : Blo 790340 2176381 := bstep (se 3 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 2176381 = 816143) B816143
theorem B2667977 : Blo 790340 2667977 := bstep (se 2 (by rfl) ⟨1000491, by rfl⟩ : syracuseStep 2667977 = 2000983) B2000983
theorem B8697289 : Blo 790340 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B1783259 : Blo 790340 1783259 := bstep (se 1 (by rfl) ⟨1337444, by rfl⟩ : syracuseStep 1783259 = 2674889) B2674889
theorem B2537057 : Blo 790340 2537057 := bstep (se 2 (by rfl) ⟨951396, by rfl⟩ : syracuseStep 2537057 = 1902793) B1902793
theorem B2668247 : Blo 790340 2668247 := bstep (se 1 (by rfl) ⟨2001185, by rfl⟩ : syracuseStep 2668247 = 4002371) B4002371
theorem B1128287 : Blo 790340 1128287 := bstep (se 1 (by rfl) ⟨846215, by rfl⟩ : syracuseStep 1128287 = 1692431) B1692431
theorem B3389303 : Blo 790340 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B2668463 : Blo 790340 2668463 := bstep (se 1 (by rfl) ⟨2001347, by rfl⟩ : syracuseStep 2668463 = 4002695) B4002695
theorem B1128367 : Blo 790340 1128367 := bstep (se 1 (by rfl) ⟨846275, by rfl⟩ : syracuseStep 1128367 = 1692551) B1692551
theorem B1783727 : Blo 790340 1783727 := bstep (se 1 (by rfl) ⟨1337795, by rfl⟩ : syracuseStep 1783727 = 2675591) B2675591
theorem B1128487 : Blo 790340 1128487 := bstep (se 1 (by rfl) ⟨846365, by rfl⟩ : syracuseStep 1128487 = 1692731) B1692731
theorem B6764633 : Blo 790340 6764633 := bstep (se 2 (by rfl) ⟨2536737, by rfl⟩ : syracuseStep 6764633 = 5073475) B5073475
theorem B6436979 : Blo 790340 6436979 := bstep (se 1 (by rfl) ⟨4827734, by rfl⟩ : syracuseStep 6436979 = 9655469) B9655469
theorem B3815581 : Blo 790340 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B1783979 : Blo 790340 1783979 := bstep (se 1 (by rfl) ⟨1337984, by rfl⟩ : syracuseStep 1783979 = 2675969) B2675969
theorem B534034781 : Blo 790340 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B4274537 : Blo 790340 4274537 := bstep (se 2 (by rfl) ⟨1602951, by rfl⟩ : syracuseStep 4274537 = 3205903) B3205903
theorem B1128811 : Blo 790340 1128811 := bstep (se 1 (by rfl) ⟨846608, by rfl⟩ : syracuseStep 1128811 = 1693217) B1693217
theorem B4012577 : Blo 790340 4012577 := bstep (se 2 (by rfl) ⟨1504716, by rfl⟩ : syracuseStep 4012577 = 3009433) B3009433
theorem B3717767 : Blo 790340 3717767 := bstep (se 1 (by rfl) ⟨2788325, by rfl⟩ : syracuseStep 3717767 = 5576651) B5576651
theorem B1784519 : Blo 790340 1784519 := bstep (se 1 (by rfl) ⟨1338389, by rfl⟩ : syracuseStep 1784519 = 2676779) B2676779
theorem B10140389 : Blo 790340 10140389 := bstep (se 4 (by rfl) ⟨950661, by rfl⟩ : syracuseStep 10140389 = 1901323) B1901323
theorem B9616157 : Blo 790340 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B3128473 : Blo 790340 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B4504855 : Blo 790340 4504855 := bstep (se 1 (by rfl) ⟨3378641, by rfl⟩ : syracuseStep 4504855 = 6757283) B6757283
theorem B1785383 : Blo 790340 1785383 := bstep (se 1 (by rfl) ⟨1339037, by rfl⟩ : syracuseStep 1785383 = 2678075) B2678075
theorem B1425019 : Blo 790340 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B1425107 : Blo 790340 1425107 := bstep (se 1 (by rfl) ⟨1068830, by rfl⟩ : syracuseStep 1425107 = 2137661) B2137661
theorem B1785707 : Blo 790340 1785707 := bstep (se 1 (by rfl) ⟨1339280, by rfl⟩ : syracuseStep 1785707 = 2678561) B2678561
theorem B6012791 : Blo 790340 6012791 := bstep (se 1 (by rfl) ⟨4509593, by rfl⟩ : syracuseStep 6012791 = 9019187) B9019187
theorem B1785761 : Blo 790340 1785761 := bstep (se 2 (by rfl) ⟨669660, by rfl⟩ : syracuseStep 1785761 = 1339321) B1339321
theorem B2670839 : Blo 790340 2670839 := bstep (se 1 (by rfl) ⟨2003129, by rfl⟩ : syracuseStep 2670839 = 4006259) B4006259
theorem B1786103 : Blo 790340 1786103 := bstep (se 1 (by rfl) ⟨1339577, by rfl⟩ : syracuseStep 1786103 = 2679155) B2679155
theorem B967087 : Blo 790340 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B2671163 : Blo 790340 2671163 := bstep (se 1 (by rfl) ⟨2003372, by rfl⟩ : syracuseStep 2671163 = 4006745) B4006745
theorem B2671433 : Blo 790340 2671433 := bstep (se 2 (by rfl) ⟨1001787, by rfl⟩ : syracuseStep 2671433 = 2003575) B2003575
theorem B1786697 : Blo 790340 1786697 := bstep (se 2 (by rfl) ⟨670011, by rfl⟩ : syracuseStep 1786697 = 1340023) B1340023
theorem B2901187 : Blo 790340 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B4015655 : Blo 790340 4015655 := bstep (se 1 (by rfl) ⟨3011741, by rfl⟩ : syracuseStep 4015655 = 6023483) B6023483
theorem B5490413 : Blo 790340 5490413 := bstep (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) B2058905
theorem B2672567 : Blo 790340 2672567 := bstep (se 1 (by rfl) ⟨2004425, by rfl⟩ : syracuseStep 2672567 = 4008851) B4008851
theorem B3622843 : Blo 790340 3622843 := bstep (se 1 (by rfl) ⟨2717132, by rfl⟩ : syracuseStep 3622843 = 5434265) B5434265
theorem B17156195 : Blo 790340 17156195 := bstep (se 1 (by rfl) ⟨12867146, by rfl⟩ : syracuseStep 17156195 = 25734293) B25734293
theorem B1526111 : Blo 790340 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B19286423 : Blo 790340 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B2673161 : Blo 790340 2673161 := bstep (se 2 (by rfl) ⟨1002435, by rfl⟩ : syracuseStep 2673161 = 2004871) B2004871
theorem B5491385 : Blo 790340 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B6016193 : Blo 790340 6016193 := bstep (se 2 (by rfl) ⟨2256072, by rfl⟩ : syracuseStep 6016193 = 4512145) B4512145
theorem B9030851 : Blo 790340 9030851 := bstep (se 1 (by rfl) ⟨6773138, by rfl⟩ : syracuseStep 9030851 = 13546277) B13546277
theorem B2674025 : Blo 790340 2674025 := bstep (se 2 (by rfl) ⟨1002759, by rfl⟩ : syracuseStep 2674025 = 2005519) B2005519
theorem B5721587 : Blo 790340 5721587 := bstep (se 1 (by rfl) ⟨4291190, by rfl⟩ : syracuseStep 5721587 = 8582381) B8582381
theorem B2706983 : Blo 790340 2706983 := bstep (se 1 (by rfl) ⟨2030237, by rfl⟩ : syracuseStep 2706983 = 4060475) B4060475
theorem B4017761 : Blo 790340 4017761 := bstep (se 2 (by rfl) ⟨1506660, by rfl⟩ : syracuseStep 4017761 = 3013321) B3013321
theorem B2674619 : Blo 790340 2674619 := bstep (se 1 (by rfl) ⟨2005964, by rfl⟩ : syracuseStep 2674619 = 4011929) B4011929
theorem B1691705 : Blo 790340 1691705 := bstep (se 2 (by rfl) ⟨634389, by rfl⟩ : syracuseStep 1691705 = 1268779) B1268779
theorem B3002447 : Blo 790340 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B3002615 : Blo 790340 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B6410507 : Blo 790340 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B10309963 : Blo 790340 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B2543977 : Blo 790340 2543977 := bstep (se 2 (by rfl) ⟨953991, by rfl⟩ : syracuseStep 2543977 = 1907983) B1907983
theorem B1004071 : Blo 790340 1004071 := bstep (se 1 (by rfl) ⟨753053, by rfl⟩ : syracuseStep 1004071 = 1506107) B1506107
theorem B9032309 : Blo 790340 9032309 := bstep (se 5 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 9032309 = 846779) B846779
theorem B1004395 : Blo 790340 1004395 := bstep (se 1 (by rfl) ⟨753296, by rfl⟩ : syracuseStep 1004395 = 1506593) B1506593
theorem B1266607 : Blo 790340 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B43439075 : Blo 790340 43439075 := bstep (se 1 (by rfl) ⟨32579306, by rfl⟩ : syracuseStep 43439075 = 65158613) B65158613
theorem B4019219 : Blo 790340 4019219 := bstep (se 1 (by rfl) ⟨3014414, by rfl⟩ : syracuseStep 4019219 = 6028829) B6028829
theorem B3003587 : Blo 790340 3003587 := bstep (se 1 (by rfl) ⟨2252690, by rfl⟩ : syracuseStep 3003587 = 4505381) B4505381
theorem B1430959 : Blo 790340 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B2676347 : Blo 790340 2676347 := bstep (se 1 (by rfl) ⟨2007260, by rfl⟩ : syracuseStep 2676347 = 4014521) B4014521
theorem B21649045 : Blo 790340 21649045 := bstep (se 6 (by rfl) ⟨507399, by rfl⟩ : syracuseStep 21649045 = 1014799) B1014799
theorem B2676509 : Blo 790340 2676509 := bstep (se 3 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 2676509 = 1003691) B1003691
theorem B1202015 : Blo 790340 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B6019109 : Blo 790340 6019109 := bstep (se 4 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 6019109 = 1128583) B1128583
theorem B3004573 : Blo 790340 3004573 := bstep (se 3 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 3004573 = 1126715) B1126715
theorem B2677211 : Blo 790340 2677211 := bstep (se 1 (by rfl) ⟨2007908, by rfl⟩ : syracuseStep 2677211 = 4015817) B4015817
theorem B2251289 : Blo 790340 2251289 := bstep (se 2 (by rfl) ⟨844233, by rfl⟩ : syracuseStep 2251289 = 1688467) B1688467
theorem B1334009 : Blo 790340 1334009 := bstep (se 2 (by rfl) ⟨500253, by rfl⟩ : syracuseStep 1334009 = 1000507) B1000507
theorem B1334191 : Blo 790340 1334191 := bstep (se 1 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 1334191 = 2001287) B2001287
theorem B2644993 : Blo 790340 2644993 := bstep (se 2 (by rfl) ⟨991872, by rfl⟩ : syracuseStep 2644993 = 1983745) B1983745
theorem B1334279 : Blo 790340 1334279 := bstep (se 1 (by rfl) ⟨1000709, by rfl⟩ : syracuseStep 1334279 = 2001419) B2001419
theorem B2677913 : Blo 790340 2677913 := bstep (se 2 (by rfl) ⟨1004217, by rfl⟩ : syracuseStep 2677913 = 2008435) B2008435
theorem B1694891 : Blo 790340 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B1334623 : Blo 790340 1334623 := bstep (se 1 (by rfl) ⟨1000967, by rfl⟩ : syracuseStep 1334623 = 2001935) B2001935
theorem B1334711 : Blo 790340 1334711 := bstep (se 1 (by rfl) ⟨1001033, by rfl⟩ : syracuseStep 1334711 = 2002067) B2002067
theorem B1629623 : Blo 790340 1629623 := bstep (se 1 (by rfl) ⟨1222217, by rfl⟩ : syracuseStep 1629623 = 2444435) B2444435
theorem B4513603 : Blo 790340 4513603 := bstep (se 1 (by rfl) ⟨3385202, by rfl⟩ : syracuseStep 4513603 = 6770405) B6770405
theorem B1269599 : Blo 790340 1269599 := bstep (se 1 (by rfl) ⟨952199, by rfl⟩ : syracuseStep 1269599 = 1904399) B1904399
theorem B1335305 : Blo 790340 1335305 := bstep (se 2 (by rfl) ⟨500739, by rfl⟩ : syracuseStep 1335305 = 1001479) B1001479
theorem B1335467 : Blo 790340 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B1270009 : Blo 790340 1270009 := bstep (se 2 (by rfl) ⟨476253, by rfl⟩ : syracuseStep 1270009 = 952507) B952507
theorem B2679101 : Blo 790340 2679101 := bstep (se 3 (by rfl) ⟨502331, by rfl⟩ : syracuseStep 2679101 = 1004663) B1004663
theorem B1335865 : Blo 790340 1335865 := bstep (se 2 (by rfl) ⟨500949, by rfl⟩ : syracuseStep 1335865 = 1001899) B1001899
theorem B1336007 : Blo 790340 1336007 := bstep (se 1 (by rfl) ⟨1002005, by rfl⟩ : syracuseStep 1336007 = 2004011) B2004011
theorem B1336169 : Blo 790340 1336169 := bstep (se 2 (by rfl) ⟨501063, by rfl⟩ : syracuseStep 1336169 = 1002127) B1002127
theorem B844763 : Blo 790340 844763 := bstep (se 1 (by rfl) ⟨633572, by rfl⟩ : syracuseStep 844763 = 1267145) B1267145
theorem B9659357 : Blo 790340 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B3007489 : Blo 790340 3007489 := bstep (se 2 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 3007489 = 2255617) B2255617
theorem B4809881 : Blo 790340 4809881 := bstep (se 2 (by rfl) ⟨1803705, by rfl⟩ : syracuseStep 4809881 = 3607411) B3607411
theorem B2679965 : Blo 790340 2679965 := bstep (se 3 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 2679965 = 1004987) B1004987
theorem B15262937 : Blo 790340 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B1336567 : Blo 790340 1336567 := bstep (se 1 (by rfl) ⟨1002425, by rfl⟩ : syracuseStep 1336567 = 2004851) B2004851
theorem B2254205 : Blo 790340 2254205 := bstep (se 3 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 2254205 = 845327) B845327
theorem B1336763 : Blo 790340 1336763 := bstep (se 1 (by rfl) ⟨1002572, by rfl⟩ : syracuseStep 1336763 = 2005145) B2005145
theorem B1336871 : Blo 790340 1336871 := bstep (se 1 (by rfl) ⟨1002653, by rfl⟩ : syracuseStep 1336871 = 2005307) B2005307
theorem B2680505 : Blo 790340 2680505 := bstep (se 2 (by rfl) ⟨1005189, by rfl⟩ : syracuseStep 2680505 = 2010379) B2010379
theorem B2254547 : Blo 790340 2254547 := bstep (se 1 (by rfl) ⟨1690910, by rfl⟩ : syracuseStep 2254547 = 3381821) B3381821
theorem B3008249 : Blo 790340 3008249 := bstep (se 2 (by rfl) ⟨1128093, by rfl⟩ : syracuseStep 3008249 = 2256187) B2256187
theorem B1337161 : Blo 790340 1337161 := bstep (se 2 (by rfl) ⟨501435, by rfl⟩ : syracuseStep 1337161 = 1002871) B1002871
theorem B1337195 : Blo 790340 1337195 := bstep (se 1 (by rfl) ⟨1002896, by rfl⟩ : syracuseStep 1337195 = 2005793) B2005793
theorem B1501193 : Blo 790340 1501193 := bstep (se 2 (by rfl) ⟨562947, by rfl⟩ : syracuseStep 1501193 = 1125895) B1125895
theorem B1337593 : Blo 790340 1337593 := bstep (se 2 (by rfl) ⟨501597, by rfl⟩ : syracuseStep 1337593 = 1003195) B1003195
theorem B1337863 : Blo 790340 1337863 := bstep (se 1 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 1337863 = 2006795) B2006795
theorem B6777377 : Blo 790340 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B3861251 : Blo 790340 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B22866725 : Blo 790340 22866725 := bstep (se 4 (by rfl) ⟨2143755, by rfl⟩ : syracuseStep 22866725 = 4287511) B4287511
theorem B1502059 : Blo 790340 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B1502135 : Blo 790340 1502135 := bstep (se 1 (by rfl) ⟨1126601, by rfl⟩ : syracuseStep 1502135 = 2253203) B2253203
theorem B1338295 : Blo 790340 1338295 := bstep (se 1 (by rfl) ⟨1003721, by rfl⟩ : syracuseStep 1338295 = 2007443) B2007443
theorem B1338491 : Blo 790340 1338491 := bstep (se 1 (by rfl) ⟨1003868, by rfl⟩ : syracuseStep 1338491 = 2007737) B2007737
theorem B3009707 : Blo 790340 3009707 := bstep (se 1 (by rfl) ⟨2257280, by rfl⟩ : syracuseStep 3009707 = 4514561) B4514561
theorem B2256119 : Blo 790340 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B5074319 : Blo 790340 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1502651 : Blo 790340 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B1338889 : Blo 790340 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B10153511 : Blo 790340 10153511 := bstep (se 1 (by rfl) ⟨7615133, by rfl⟩ : syracuseStep 10153511 = 15230267) B15230267
theorem B32566859 : Blo 790340 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B1339051 : Blo 790340 1339051 := bstep (se 1 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 1339051 = 2008577) B2008577
theorem B6024941 : Blo 790340 6024941 := bstep (se 3 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 6024941 = 2259353) B2259353
theorem B7630625 : Blo 790340 7630625 := bstep (se 2 (by rfl) ⟨2861484, by rfl⟩ : syracuseStep 7630625 = 5722969) B5722969
theorem B1503137 : Blo 790340 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B1339355 : Blo 790340 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B5697539 : Blo 790340 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B1503289 : Blo 790340 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B4517977 : Blo 790340 4517977 := bstep (se 2 (by rfl) ⟨1694241, by rfl⟩ : syracuseStep 4517977 = 3388483) B3388483
theorem B1339591 : Blo 790340 1339591 := bstep (se 1 (by rfl) ⟨1004693, by rfl⟩ : syracuseStep 1339591 = 2009387) B2009387
theorem B3010877 : Blo 790340 3010877 := bstep (se 3 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 3010877 = 1129079) B1129079
theorem B17166653 : Blo 790340 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B1503593 : Blo 790340 1503593 := bstep (se 2 (by rfl) ⟨563847, by rfl⟩ : syracuseStep 1503593 = 1127695) B1127695
theorem B1339753 : Blo 790340 1339753 := bstep (se 2 (by rfl) ⟨502407, by rfl⟩ : syracuseStep 1339753 = 1004815) B1004815
theorem B1143335 : Blo 790340 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B3011195 : Blo 790340 3011195 := bstep (se 1 (by rfl) ⟨2258396, by rfl⟩ : syracuseStep 3011195 = 4516793) B4516793
theorem B6025913 : Blo 790340 6025913 := bstep (se 2 (by rfl) ⟨2259717, by rfl⟩ : syracuseStep 6025913 = 4519435) B4519435
theorem B1340347 : Blo 790340 1340347 := bstep (se 1 (by rfl) ⟨1005260, by rfl⟩ : syracuseStep 1340347 = 2010521) B2010521
theorem B3798035 : Blo 790340 3798035 := bstep (se 1 (by rfl) ⟨2848526, by rfl⟩ : syracuseStep 3798035 = 5697053) B5697053
theorem B7599257 : Blo 790340 7599257 := bstep (se 2 (by rfl) ⟨2849721, by rfl⟩ : syracuseStep 7599257 = 5699443) B5699443
theorem B3044897 : Blo 790340 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B2717243 : Blo 790340 2717243 := bstep (se 1 (by rfl) ⟨2037932, by rfl⟩ : syracuseStep 2717243 = 4075865) B4075865
theorem B6026885 : Blo 790340 6026885 := bstep (se 4 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 6026885 = 1130041) B1130041
theorem B2258761 : Blo 790340 2258761 := bstep (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) B1694071
theorem B1603471 : Blo 790340 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B3209147 : Blo 790340 3209147 := bstep (se 1 (by rfl) ⟨2406860, by rfl⟩ : syracuseStep 3209147 = 4813721) B4813721
theorem B3012623 : Blo 790340 3012623 := bstep (se 1 (by rfl) ⟨2259467, by rfl⟩ : syracuseStep 3012623 = 4518935) B4518935
theorem B6092857 : Blo 790340 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B1505719 : Blo 790340 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B12843467 : Blo 790340 12843467 := bstep (se 1 (by rfl) ⟨9632600, by rfl⟩ : syracuseStep 12843467 = 19265201) B19265201
theorem B2849377 : Blo 790340 2849377 := bstep (se 2 (by rfl) ⟨1068516, by rfl⟩ : syracuseStep 2849377 = 2137033) B2137033
theorem B4815569 : Blo 790340 4815569 := bstep (se 2 (by rfl) ⟨1805838, by rfl⟩ : syracuseStep 4815569 = 3611677) B3611677
theorem B6421477 : Blo 790340 6421477 := bstep (se 4 (by rfl) ⟨602013, by rfl⟩ : syracuseStep 6421477 = 1204027) B1204027
theorem B4652185 : Blo 790340 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B3014279 : Blo 790340 3014279 := bstep (se 1 (by rfl) ⟨2260709, by rfl⟩ : syracuseStep 3014279 = 4521419) B4521419
theorem B2260619 : Blo 790340 2260619 := bstep (se 1 (by rfl) ⟨1695464, by rfl⟩ : syracuseStep 2260619 = 3390929) B3390929
theorem B1507177 : Blo 790340 1507177 := bstep (se 2 (by rfl) ⟨565191, by rfl⟩ : syracuseStep 1507177 = 1130383) B1130383
theorem B2752375 : Blo 790340 2752375 := bstep (se 1 (by rfl) ⟨2064281, by rfl⟩ : syracuseStep 2752375 = 4128563) B4128563
theorem B9633667 : Blo 790340 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B4292513 : Blo 790340 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B5701751 : Blo 790340 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B3802049 : Blo 790340 3802049 := bstep (se 2 (by rfl) ⟨1425768, by rfl⟩ : syracuseStep 3802049 = 2851537) B2851537
theorem B11437463 : Blo 790340 11437463 := bstep (se 1 (by rfl) ⟨8578097, by rfl⟩ : syracuseStep 11437463 = 17156195) B17156195
theorem B3048893 : Blo 790340 3048893 := bstep (se 3 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 3048893 = 1143335) B1143335
theorem B1017407 : Blo 790340 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B3868249 : Blo 790340 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B1804655 : Blo 790340 1804655 := bstep (se 1 (by rfl) ⟨1353491, by rfl⟩ : syracuseStep 1804655 = 2706983) B2706983
theorem B2001631 : Blo 790340 2001631 := bstep (se 1 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 2001631 = 3002447) B3002447
theorem B1903351 : Blo 790340 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B2001743 : Blo 790340 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B3804241 : Blo 790340 3804241 := bstep (se 2 (by rfl) ⟨1426590, by rfl⟩ : syracuseStep 3804241 = 2853181) B2853181
theorem B5082497 : Blo 790340 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B2002391 : Blo 790340 2002391 := bstep (se 1 (by rfl) ⟨1501793, by rfl⟩ : syracuseStep 2002391 = 3003587) B3003587
theorem B33033815 : Blo 790340 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B7212847 : Blo 790340 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B2002745 : Blo 790340 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B790427 : Blo 790340 790427 := bstep (se 1 (by rfl) ⟨592820, by rfl⟩ : syracuseStep 790427 = 1185641) B1185641
theorem B790479 : Blo 790340 790479 := bstep (se 1 (by rfl) ⟨592859, by rfl⟩ : syracuseStep 790479 = 1185719) B1185719
theorem B790503 : Blo 790340 790503 := bstep (se 1 (by rfl) ⟨592877, by rfl⟩ : syracuseStep 790503 = 1185755) B1185755
theorem B790815 : Blo 790340 790815 := bstep (se 1 (by rfl) ⟨593111, by rfl⟩ : syracuseStep 790815 = 1186223) B1186223
theorem B790875 : Blo 790340 790875 := bstep (se 1 (by rfl) ⟨593156, by rfl⟩ : syracuseStep 790875 = 1186313) B1186313
theorem B790895 : Blo 790340 790895 := bstep (se 1 (by rfl) ⟨593171, by rfl⟩ : syracuseStep 790895 = 1186343) B1186343
theorem B790951 : Blo 790340 790951 := bstep (se 1 (by rfl) ⟨593213, by rfl⟩ : syracuseStep 790951 = 1186427) B1186427
theorem B889339 : Blo 790340 889339 := bstep (se 1 (by rfl) ⟨667004, by rfl⟩ : syracuseStep 889339 = 1334009) B1334009
theorem B791035 : Blo 790340 791035 := bstep (se 1 (by rfl) ⟨593276, by rfl⟩ : syracuseStep 791035 = 1186553) B1186553
theorem B791103 : Blo 790340 791103 := bstep (se 1 (by rfl) ⟨593327, by rfl⟩ : syracuseStep 791103 = 1186655) B1186655
theorem B791111 : Blo 790340 791111 := bstep (se 1 (by rfl) ⟨593333, by rfl⟩ : syracuseStep 791111 = 1186667) B1186667
theorem B889519 : Blo 790340 889519 := bstep (se 1 (by rfl) ⟨667139, by rfl⟩ : syracuseStep 889519 = 1334279) B1334279
theorem B791263 : Blo 790340 791263 := bstep (se 1 (by rfl) ⟨593447, by rfl⟩ : syracuseStep 791263 = 1186895) B1186895
theorem B791343 : Blo 790340 791343 := bstep (se 1 (by rfl) ⟨593507, by rfl⟩ : syracuseStep 791343 = 1187015) B1187015
theorem B791451 : Blo 790340 791451 := bstep (se 1 (by rfl) ⟨593588, by rfl⟩ : syracuseStep 791451 = 1187177) B1187177
theorem B889807 : Blo 790340 889807 := bstep (se 1 (by rfl) ⟨667355, by rfl⟩ : syracuseStep 889807 = 1334711) B1334711
theorem B791503 : Blo 790340 791503 := bstep (se 1 (by rfl) ⟨593627, by rfl⟩ : syracuseStep 791503 = 1187255) B1187255
theorem B1086415 : Blo 790340 1086415 := bstep (se 1 (by rfl) ⟨814811, by rfl⟩ : syracuseStep 1086415 = 1629623) B1629623
theorem B791527 : Blo 790340 791527 := bstep (se 1 (by rfl) ⟨593645, by rfl⟩ : syracuseStep 791527 = 1187291) B1187291
theorem B791839 : Blo 790340 791839 := bstep (se 1 (by rfl) ⟨593879, by rfl⟩ : syracuseStep 791839 = 1187759) B1187759
theorem B890203 : Blo 790340 890203 := bstep (se 1 (by rfl) ⟨667652, by rfl⟩ : syracuseStep 890203 = 1335305) B1335305
theorem B791899 : Blo 790340 791899 := bstep (se 1 (by rfl) ⟨593924, by rfl⟩ : syracuseStep 791899 = 1187849) B1187849
theorem B4003181 : Blo 790340 4003181 := bstep (se 3 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 4003181 = 1501193) B1501193
theorem B791919 : Blo 790340 791919 := bstep (se 1 (by rfl) ⟨593939, by rfl⟩ : syracuseStep 791919 = 1187879) B1187879
theorem B2004385 : Blo 790340 2004385 := bstep (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) B1503289
theorem B791975 : Blo 790340 791975 := bstep (se 1 (by rfl) ⟨593981, by rfl⟩ : syracuseStep 791975 = 1187963) B1187963
theorem B890311 : Blo 790340 890311 := bstep (se 1 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 890311 = 1335467) B1335467
theorem B77960657 : Blo 790340 77960657 := bstep (se 2 (by rfl) ⟨29235246, by rfl⟩ : syracuseStep 77960657 = 58470493) B58470493
theorem B7607789 : Blo 790340 7607789 := bstep (se 3 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 7607789 = 2852921) B2852921
theorem B792059 : Blo 790340 792059 := bstep (se 1 (by rfl) ⟨594044, by rfl⟩ : syracuseStep 792059 = 1188089) B1188089
theorem B792127 : Blo 790340 792127 := bstep (se 1 (by rfl) ⟨594095, by rfl⟩ : syracuseStep 792127 = 1188191) B1188191
theorem B792135 : Blo 790340 792135 := bstep (se 1 (by rfl) ⟨594101, by rfl⟩ : syracuseStep 792135 = 1188203) B1188203
theorem B792287 : Blo 790340 792287 := bstep (se 1 (by rfl) ⟨594215, by rfl⟩ : syracuseStep 792287 = 1188431) B1188431
theorem B1185515 : Blo 790340 1185515 := bstep (se 1 (by rfl) ⟨889136, by rfl⟩ : syracuseStep 1185515 = 1778273) B1778273
theorem B5084957 : Blo 790340 5084957 := bstep (se 3 (by rfl) ⟨953429, by rfl⟩ : syracuseStep 5084957 = 1906859) B1906859
theorem B890671 : Blo 790340 890671 := bstep (se 1 (by rfl) ⟨668003, by rfl⟩ : syracuseStep 890671 = 1336007) B1336007
theorem B792367 : Blo 790340 792367 := bstep (se 1 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 792367 = 1188551) B1188551
theorem B890779 : Blo 790340 890779 := bstep (se 1 (by rfl) ⟨668084, by rfl⟩ : syracuseStep 890779 = 1336169) B1336169
theorem B792475 : Blo 790340 792475 := bstep (se 1 (by rfl) ⟨594356, by rfl⟩ : syracuseStep 792475 = 1188713) B1188713
theorem B1185743 : Blo 790340 1185743 := bstep (se 1 (by rfl) ⟨889307, by rfl⟩ : syracuseStep 1185743 = 1778615) B1778615
theorem B792527 : Blo 790340 792527 := bstep (se 1 (by rfl) ⟨594395, by rfl⟩ : syracuseStep 792527 = 1188791) B1188791
theorem B792551 : Blo 790340 792551 := bstep (se 1 (by rfl) ⟨594413, by rfl⟩ : syracuseStep 792551 = 1188827) B1188827
theorem B16685189 : Blo 790340 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B792863 : Blo 790340 792863 := bstep (se 1 (by rfl) ⟨594647, by rfl⟩ : syracuseStep 792863 = 1189295) B1189295
theorem B891175 : Blo 790340 891175 := bstep (se 1 (by rfl) ⟨668381, by rfl⟩ : syracuseStep 891175 = 1336763) B1336763
theorem B1186139 : Blo 790340 1186139 := bstep (se 1 (by rfl) ⟨889604, by rfl⟩ : syracuseStep 1186139 = 1779209) B1779209
theorem B792923 : Blo 790340 792923 := bstep (se 1 (by rfl) ⟨594692, by rfl⟩ : syracuseStep 792923 = 1189385) B1189385
theorem B891247 : Blo 790340 891247 := bstep (se 1 (by rfl) ⟨668435, by rfl⟩ : syracuseStep 891247 = 1336871) B1336871
theorem B792943 : Blo 790340 792943 := bstep (se 1 (by rfl) ⟨594707, by rfl⟩ : syracuseStep 792943 = 1189415) B1189415
theorem B792999 : Blo 790340 792999 := bstep (se 1 (by rfl) ⟨594749, by rfl⟩ : syracuseStep 792999 = 1189499) B1189499
theorem B2005499 : Blo 790340 2005499 := bstep (se 1 (by rfl) ⟨1504124, by rfl⟩ : syracuseStep 2005499 = 3008249) B3008249
theorem B793083 : Blo 790340 793083 := bstep (se 1 (by rfl) ⟨594812, by rfl⟩ : syracuseStep 793083 = 1189625) B1189625
theorem B1186367 : Blo 790340 1186367 := bstep (se 1 (by rfl) ⟨889775, by rfl⟩ : syracuseStep 1186367 = 1779551) B1779551
theorem B793151 : Blo 790340 793151 := bstep (se 1 (by rfl) ⟨594863, by rfl⟩ : syracuseStep 793151 = 1189727) B1189727
theorem B891463 : Blo 790340 891463 := bstep (se 1 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 891463 = 1337195) B1337195
theorem B793159 : Blo 790340 793159 := bstep (se 1 (by rfl) ⟨594869, by rfl⟩ : syracuseStep 793159 = 1189739) B1189739
theorem B1186487 : Blo 790340 1186487 := bstep (se 1 (by rfl) ⟨889865, by rfl⟩ : syracuseStep 1186487 = 1779731) B1779731
theorem B793311 : Blo 790340 793311 := bstep (se 1 (by rfl) ⟨594983, by rfl⟩ : syracuseStep 793311 = 1189967) B1189967
theorem B793391 : Blo 790340 793391 := bstep (se 1 (by rfl) ⟨595043, by rfl⟩ : syracuseStep 793391 = 1190087) B1190087
theorem B793499 : Blo 790340 793499 := bstep (se 1 (by rfl) ⟨595124, by rfl⟩ : syracuseStep 793499 = 1190249) B1190249
theorem B1186715 : Blo 790340 1186715 := bstep (se 1 (by rfl) ⟨890036, by rfl⟩ : syracuseStep 1186715 = 1780073) B1780073
theorem B793551 : Blo 790340 793551 := bstep (se 1 (by rfl) ⟨595163, by rfl⟩ : syracuseStep 793551 = 1190327) B1190327
theorem B793575 : Blo 790340 793575 := bstep (se 1 (by rfl) ⟨595181, by rfl⟩ : syracuseStep 793575 = 1190363) B1190363
theorem B15244483 : Blo 790340 15244483 := bstep (se 1 (by rfl) ⟨11433362, by rfl⟩ : syracuseStep 15244483 = 22866725) B22866725
theorem B1907945 : Blo 790340 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B793887 : Blo 790340 793887 := bstep (se 1 (by rfl) ⟨595415, by rfl⟩ : syracuseStep 793887 = 1190831) B1190831
theorem B1187111 : Blo 790340 1187111 := bstep (se 1 (by rfl) ⟨890333, by rfl⟩ : syracuseStep 1187111 = 1780667) B1780667
theorem B793947 : Blo 790340 793947 := bstep (se 1 (by rfl) ⟨595460, by rfl⟩ : syracuseStep 793947 = 1190921) B1190921
theorem B793967 : Blo 790340 793967 := bstep (se 1 (by rfl) ⟨595475, by rfl⟩ : syracuseStep 793967 = 1190951) B1190951
theorem B1187195 : Blo 790340 1187195 := bstep (se 1 (by rfl) ⟨890396, by rfl⟩ : syracuseStep 1187195 = 1780793) B1780793
theorem B892327 : Blo 790340 892327 := bstep (se 1 (by rfl) ⟨669245, by rfl⟩ : syracuseStep 892327 = 1338491) B1338491
theorem B794023 : Blo 790340 794023 := bstep (se 1 (by rfl) ⟨595517, by rfl⟩ : syracuseStep 794023 = 1191035) B1191035
theorem B2006471 : Blo 790340 2006471 := bstep (se 1 (by rfl) ⟨1504853, by rfl⟩ : syracuseStep 2006471 = 3009707) B3009707
theorem B1187321 : Blo 790340 1187321 := bstep (se 2 (by rfl) ⟨445245, by rfl⟩ : syracuseStep 1187321 = 890491) B890491
theorem B794107 : Blo 790340 794107 := bstep (se 1 (by rfl) ⟨595580, by rfl⟩ : syracuseStep 794107 = 1191161) B1191161
theorem B794175 : Blo 790340 794175 := bstep (se 1 (by rfl) ⟨595631, by rfl⟩ : syracuseStep 794175 = 1191263) B1191263
theorem B794183 : Blo 790340 794183 := bstep (se 1 (by rfl) ⟨595637, by rfl⟩ : syracuseStep 794183 = 1191275) B1191275
theorem B1187423 : Blo 790340 1187423 := bstep (se 1 (by rfl) ⟨890567, by rfl⟩ : syracuseStep 1187423 = 1781135) B1781135
theorem B3382879 : Blo 790340 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B12197537 : Blo 790340 12197537 := bstep (se 2 (by rfl) ⟨4574076, by rfl⟩ : syracuseStep 12197537 = 9148153) B9148153
theorem B794335 : Blo 790340 794335 := bstep (se 1 (by rfl) ⟨595751, by rfl⟩ : syracuseStep 794335 = 1191503) B1191503
theorem B4005611 : Blo 790340 4005611 := bstep (se 1 (by rfl) ⟨3004208, by rfl⟩ : syracuseStep 4005611 = 6008417) B6008417
theorem B1187639 : Blo 790340 1187639 := bstep (se 1 (by rfl) ⟨890729, by rfl⟩ : syracuseStep 1187639 = 1781459) B1781459
theorem B2137961 : Blo 790340 2137961 := bstep (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) B1603471
theorem B5087083 : Blo 790340 5087083 := bstep (se 1 (by rfl) ⟨3815312, by rfl⟩ : syracuseStep 5087083 = 7630625) B7630625
theorem B892903 : Blo 790340 892903 := bstep (se 1 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 892903 = 1339355) B1339355
theorem B1187945 : Blo 790340 1187945 := bstep (se 2 (by rfl) ⟨445479, by rfl⟩ : syracuseStep 1187945 = 890959) B890959
theorem B4006097 : Blo 790340 4006097 := bstep (se 2 (by rfl) ⟨1502286, by rfl⟩ : syracuseStep 4006097 = 3004573) B3004573
theorem B2007251 : Blo 790340 2007251 := bstep (se 1 (by rfl) ⟨1505438, by rfl⟩ : syracuseStep 2007251 = 3010877) B3010877
theorem B11444435 : Blo 790340 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B5087441 : Blo 790340 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B1188263 : Blo 790340 1188263 := bstep (se 1 (by rfl) ⟨891197, by rfl⟩ : syracuseStep 1188263 = 1782395) B1782395
theorem B2007463 : Blo 790340 2007463 := bstep (se 1 (by rfl) ⟨1505597, by rfl⟩ : syracuseStep 2007463 = 3011195) B3011195
theorem B1188347 : Blo 790340 1188347 := bstep (se 1 (by rfl) ⟨891260, by rfl⟩ : syracuseStep 1188347 = 1782521) B1782521
theorem B6758923 : Blo 790340 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B2007625 : Blo 790340 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B1188473 : Blo 790340 1188473 := bstep (se 2 (by rfl) ⟨445677, by rfl⟩ : syracuseStep 1188473 = 891355) B891355
theorem B1188527 : Blo 790340 1188527 := bstep (se 1 (by rfl) ⟨891395, by rfl⟩ : syracuseStep 1188527 = 1782791) B1782791
theorem B2532023 : Blo 790340 2532023 := bstep (se 1 (by rfl) ⟨1899017, by rfl⟩ : syracuseStep 2532023 = 3798035) B3798035
theorem B4006583 : Blo 790340 4006583 := bstep (se 1 (by rfl) ⟨3004937, by rfl⟩ : syracuseStep 4006583 = 6009875) B6009875
theorem B1778399 : Blo 790340 1778399 := bstep (se 1 (by rfl) ⟨1333799, by rfl⟩ : syracuseStep 1778399 = 2667599) B2667599
theorem B1188575 : Blo 790340 1188575 := bstep (se 1 (by rfl) ⟨891431, by rfl⟩ : syracuseStep 1188575 = 1782863) B1782863
theorem B1778651 : Blo 790340 1778651 := bstep (se 1 (by rfl) ⟨1333988, by rfl⟩ : syracuseStep 1778651 = 2667977) B2667977
theorem B1188839 : Blo 790340 1188839 := bstep (se 1 (by rfl) ⟨891629, by rfl⟩ : syracuseStep 1188839 = 1783259) B1783259
theorem B1811495 : Blo 790340 1811495 := bstep (se 1 (by rfl) ⟨1358621, by rfl⟩ : syracuseStep 1811495 = 2717243) B2717243
theorem B1778831 : Blo 790340 1778831 := bstep (se 1 (by rfl) ⟨1334123, by rfl⟩ : syracuseStep 1778831 = 2668247) B2668247
theorem B4007069 : Blo 790340 4007069 := bstep (se 3 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 4007069 = 1502651) B1502651
theorem B1778921 : Blo 790340 1778921 := bstep (se 2 (by rfl) ⟨667095, by rfl⟩ : syracuseStep 1778921 = 1334191) B1334191
theorem B1189097 : Blo 790340 1189097 := bstep (se 2 (by rfl) ⟨445911, by rfl⟩ : syracuseStep 1189097 = 891823) B891823
theorem B1778975 : Blo 790340 1778975 := bstep (se 1 (by rfl) ⟨1334231, by rfl⟩ : syracuseStep 1778975 = 2668463) B2668463
theorem B1189151 : Blo 790340 1189151 := bstep (se 1 (by rfl) ⟨891863, by rfl⟩ : syracuseStep 1189151 = 1783727) B1783727
theorem B2139431 : Blo 790340 2139431 := bstep (se 1 (by rfl) ⟨1604573, by rfl⟩ : syracuseStep 2139431 = 3209147) B3209147
theorem B8561969 : Blo 790340 8561969 := bstep (se 2 (by rfl) ⟨3210738, by rfl⟩ : syracuseStep 8561969 = 6421477) B6421477
theorem B2008415 : Blo 790340 2008415 := bstep (se 1 (by rfl) ⟨1506311, by rfl⟩ : syracuseStep 2008415 = 3012623) B3012623
theorem B1189319 : Blo 790340 1189319 := bstep (se 1 (by rfl) ⟨891989, by rfl⟩ : syracuseStep 1189319 = 1783979) B1783979
theorem B6202913 : Blo 790340 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B8562311 : Blo 790340 8562311 := bstep (se 1 (by rfl) ⟨6421733, by rfl⟩ : syracuseStep 8562311 = 12843467) B12843467
theorem B6006473 : Blo 790340 6006473 := bstep (se 2 (by rfl) ⟨2252427, by rfl⟩ : syracuseStep 6006473 = 4504855) B4504855
theorem B1779497 : Blo 790340 1779497 := bstep (se 2 (by rfl) ⟨667311, by rfl⟩ : syracuseStep 1779497 = 1334623) B1334623
theorem B1189673 : Blo 790340 1189673 := bstep (se 2 (by rfl) ⟨446127, by rfl⟩ : syracuseStep 1189673 = 892255) B892255
theorem B1189679 : Blo 790340 1189679 := bstep (se 1 (by rfl) ⟨892259, by rfl⟩ : syracuseStep 1189679 = 1784519) B1784519
theorem B6760259 : Blo 790340 6760259 := bstep (se 1 (by rfl) ⟨5070194, by rfl⟩ : syracuseStep 6760259 = 10140389) B10140389
theorem B3385597 : Blo 790340 3385597 := bstep (se 3 (by rfl) ⟨634799, by rfl⟩ : syracuseStep 3385597 = 1269599) B1269599
theorem B1190153 : Blo 790340 1190153 := bstep (se 2 (by rfl) ⟨446307, by rfl⟩ : syracuseStep 1190153 = 892615) B892615
theorem B7219493 : Blo 790340 7219493 := bstep (se 4 (by rfl) ⟨676827, by rfl⟩ : syracuseStep 7219493 = 1353655) B1353655
theorem B1190255 : Blo 790340 1190255 := bstep (se 1 (by rfl) ⟨892691, by rfl⟩ : syracuseStep 1190255 = 1785383) B1785383
theorem B4008365 : Blo 790340 4008365 := bstep (se 3 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 4008365 = 1503137) B1503137
theorem B2009519 : Blo 790340 2009519 := bstep (se 1 (by rfl) ⟨1507139, by rfl⟩ : syracuseStep 2009519 = 3014279) B3014279
theorem B2009569 : Blo 790340 2009569 := bstep (se 2 (by rfl) ⟨753588, by rfl⟩ : syracuseStep 2009569 = 1507177) B1507177
theorem B1190471 : Blo 790340 1190471 := bstep (se 1 (by rfl) ⟨892853, by rfl⟩ : syracuseStep 1190471 = 1785707) B1785707
theorem B4008527 : Blo 790340 4008527 := bstep (se 1 (by rfl) ⟨3006395, by rfl⟩ : syracuseStep 4008527 = 6012791) B6012791
theorem B1190507 : Blo 790340 1190507 := bstep (se 1 (by rfl) ⟨892880, by rfl⟩ : syracuseStep 1190507 = 1785761) B1785761
theorem B2861675 : Blo 790340 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B1780559 : Blo 790340 1780559 := bstep (se 1 (by rfl) ⟨1335419, by rfl⟩ : syracuseStep 1780559 = 2670839) B2670839
theorem B1190735 : Blo 790340 1190735 := bstep (se 1 (by rfl) ⟨893051, by rfl⟩ : syracuseStep 1190735 = 1786103) B1786103
theorem B1780775 : Blo 790340 1780775 := bstep (se 1 (by rfl) ⟨1335581, by rfl⟩ : syracuseStep 1780775 = 2671163) B2671163
theorem B1780955 : Blo 790340 1780955 := bstep (se 1 (by rfl) ⟨1335716, by rfl⟩ : syracuseStep 1780955 = 2671433) B2671433
theorem B1191131 : Blo 790340 1191131 := bstep (se 1 (by rfl) ⟨893348, by rfl⟩ : syracuseStep 1191131 = 1786697) B1786697
theorem B1289449 : Blo 790340 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B2010491 : Blo 790340 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B1191305 : Blo 790340 1191305 := bstep (se 2 (by rfl) ⟨446739, by rfl⟩ : syracuseStep 1191305 = 893479) B893479
theorem B1781153 : Blo 790340 1781153 := bstep (se 2 (by rfl) ⟨667932, by rfl⟩ : syracuseStep 1781153 = 1335865) B1335865
theorem B1781711 : Blo 790340 1781711 := bstep (se 1 (by rfl) ⟨1336283, by rfl⟩ : syracuseStep 1781711 = 2672567) B2672567
theorem B4009985 : Blo 790340 4009985 := bstep (se 2 (by rfl) ⟨1503744, by rfl⟩ : syracuseStep 4009985 = 3007489) B3007489
theorem B12857615 : Blo 790340 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B1782089 : Blo 790340 1782089 := bstep (se 2 (by rfl) ⟨668283, by rfl⟩ : syracuseStep 1782089 = 1336567) B1336567
theorem B1782107 : Blo 790340 1782107 := bstep (se 1 (by rfl) ⟨1336580, by rfl⟩ : syracuseStep 1782107 = 2673161) B2673161
theorem B4010795 : Blo 790340 4010795 := bstep (se 1 (by rfl) ⟨3008096, by rfl⟩ : syracuseStep 4010795 = 6016193) B6016193
theorem B2143055 : Blo 790340 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B1782683 : Blo 790340 1782683 := bstep (se 1 (by rfl) ⟨1337012, by rfl⟩ : syracuseStep 1782683 = 2674025) B2674025
theorem B3814391 : Blo 790340 3814391 := bstep (se 1 (by rfl) ⟨2860793, by rfl⟩ : syracuseStep 3814391 = 5721587) B5721587
theorem B1782881 : Blo 790340 1782881 := bstep (se 2 (by rfl) ⟨668580, by rfl⟩ : syracuseStep 1782881 = 1337161) B1337161
theorem B4830457 : Blo 790340 4830457 := bstep (se 2 (by rfl) ⟨1811421, by rfl⟩ : syracuseStep 4830457 = 3622843) B3622843
theorem B2667815 : Blo 790340 2667815 := bstep (se 1 (by rfl) ⟨2000861, by rfl⟩ : syracuseStep 2667815 = 4001723) B4001723
theorem B1783079 : Blo 790340 1783079 := bstep (se 1 (by rfl) ⟨1337309, by rfl⟩ : syracuseStep 1783079 = 2674619) B2674619
theorem B1783457 : Blo 790340 1783457 := bstep (se 2 (by rfl) ⟨668796, by rfl⟩ : syracuseStep 1783457 = 1337593) B1337593
theorem B1783817 : Blo 790340 1783817 := bstep (se 2 (by rfl) ⟨668931, by rfl⟩ : syracuseStep 1783817 = 1337863) B1337863
theorem B2668679 : Blo 790340 2668679 := bstep (se 1 (by rfl) ⟨2001509, by rfl⟩ : syracuseStep 2668679 = 4003019) B4003019
theorem B1784231 : Blo 790340 1784231 := bstep (se 1 (by rfl) ⟨1338173, by rfl⟩ : syracuseStep 1784231 = 2676347) B2676347
theorem B1784339 : Blo 790340 1784339 := bstep (se 1 (by rfl) ⟨1338254, by rfl⟩ : syracuseStep 1784339 = 2676509) B2676509
theorem B801343 : Blo 790340 801343 := bstep (se 1 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 801343 = 1202015) B1202015
theorem B1784393 : Blo 790340 1784393 := bstep (se 2 (by rfl) ⟨669147, by rfl⟩ : syracuseStep 1784393 = 1338295) B1338295
theorem B4012739 : Blo 790340 4012739 := bstep (se 1 (by rfl) ⟨3009554, by rfl⟩ : syracuseStep 4012739 = 6019109) B6019109
theorem B1424299 : Blo 790340 1424299 := bstep (se 1 (by rfl) ⟨1068224, by rfl⟩ : syracuseStep 1424299 = 2136449) B2136449
theorem B9026477 : Blo 790340 9026477 := bstep (se 3 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 9026477 = 3384929) B3384929
theorem B1784807 : Blo 790340 1784807 := bstep (se 1 (by rfl) ⟨1338605, by rfl⟩ : syracuseStep 1784807 = 2677211) B2677211
theorem B3390587 : Blo 790340 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2669921 : Blo 790340 2669921 := bstep (se 2 (by rfl) ⟨1001220, by rfl⟩ : syracuseStep 2669921 = 2002441) B2002441
theorem B1785185 : Blo 790340 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B1785275 : Blo 790340 1785275 := bstep (se 1 (by rfl) ⟨1338956, by rfl⟩ : syracuseStep 1785275 = 2677913) B2677913
theorem B1785401 : Blo 790340 1785401 := bstep (se 2 (by rfl) ⟨669525, by rfl⟩ : syracuseStep 1785401 = 1339051) B1339051
theorem B14106629 : Blo 790340 14106629 := bstep (se 4 (by rfl) ⟨1322496, by rfl⟩ : syracuseStep 14106629 = 2644993) B2644993
theorem B1786067 : Blo 790340 1786067 := bstep (se 1 (by rfl) ⟨1339550, by rfl⟩ : syracuseStep 1786067 = 2679101) B2679101
theorem B1786121 : Blo 790340 1786121 := bstep (se 2 (by rfl) ⟨669795, by rfl⟩ : syracuseStep 1786121 = 1339591) B1339591
theorem B13746617 : Blo 790340 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B1786337 : Blo 790340 1786337 := bstep (se 2 (by rfl) ⟨669876, by rfl⟩ : syracuseStep 1786337 = 1339753) B1339753
theorem B3391969 : Blo 790340 3391969 := bstep (se 2 (by rfl) ⟨1271988, by rfl⟩ : syracuseStep 3391969 = 2543977) B2543977
theorem B12829319 : Blo 790340 12829319 := bstep (se 1 (by rfl) ⟨9621989, by rfl⟩ : syracuseStep 12829319 = 19243979) B19243979
theorem B6439571 : Blo 790340 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B1786643 : Blo 790340 1786643 := bstep (se 1 (by rfl) ⟨1339982, by rfl⟩ : syracuseStep 1786643 = 2679965) B2679965
theorem B10175291 : Blo 790340 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B4506587 : Blo 790340 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B1787003 : Blo 790340 1787003 := bstep (se 1 (by rfl) ⟨1340252, by rfl⟩ : syracuseStep 1787003 = 2680505) B2680505
theorem B1688809 : Blo 790340 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B2671865 : Blo 790340 2671865 := bstep (se 2 (by rfl) ⟨1001949, by rfl⟩ : syracuseStep 2671865 = 2003899) B2003899
theorem B1787129 : Blo 790340 1787129 := bstep (se 2 (by rfl) ⟨670173, by rfl⟩ : syracuseStep 1787129 = 1340347) B1340347
theorem B36619607 : Blo 790340 36619607 := bstep (se 1 (by rfl) ⟨27464705, by rfl⟩ : syracuseStep 36619607 = 54929411) B54929411
theorem B2672135 : Blo 790340 2672135 := bstep (se 1 (by rfl) ⟨2004101, by rfl⟩ : syracuseStep 2672135 = 4008203) B4008203
theorem B4507271 : Blo 790340 4507271 := bstep (se 1 (by rfl) ⟨3380453, by rfl⟩ : syracuseStep 4507271 = 6760907) B6760907
theorem B2901841 : Blo 790340 2901841 := bstep (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) B2176381
theorem B1001423 : Blo 790340 1001423 := bstep (se 1 (by rfl) ⟨751067, by rfl⟩ : syracuseStep 1001423 = 1502135) B1502135
theorem B6769007 : Blo 790340 6769007 := bstep (se 1 (by rfl) ⟨5076755, by rfl⟩ : syracuseStep 6769007 = 10153511) B10153511
theorem B21711239 : Blo 790340 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B2673107 : Blo 790340 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B4016627 : Blo 790340 4016627 := bstep (se 1 (by rfl) ⟨3012470, by rfl⟩ : syracuseStep 4016627 = 6024941) B6024941
theorem B2673215 : Blo 790340 2673215 := bstep (se 1 (by rfl) ⟨2004911, by rfl⟩ : syracuseStep 2673215 = 4009823) B4009823
theorem B1002395 : Blo 790340 1002395 := bstep (se 1 (by rfl) ⟨751796, by rfl⟩ : syracuseStep 1002395 = 1503593) B1503593
theorem B4017275 : Blo 790340 4017275 := bstep (se 1 (by rfl) ⟨3012956, by rfl⟩ : syracuseStep 4017275 = 6025913) B6025913
theorem B4509047 : Blo 790340 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B5066171 : Blo 790340 5066171 := bstep (se 1 (by rfl) ⟨3799628, by rfl⟩ : syracuseStep 5066171 = 7599257) B7599257
theorem B1691371 : Blo 790340 1691371 := bstep (se 1 (by rfl) ⟨1268528, by rfl⟩ : syracuseStep 1691371 = 2537057) B2537057
theorem B4017923 : Blo 790340 4017923 := bstep (se 1 (by rfl) ⟨3013442, by rfl⟩ : syracuseStep 4017923 = 6026885) B6026885
theorem B4509755 : Blo 790340 4509755 := bstep (se 1 (by rfl) ⟨3382316, by rfl⟩ : syracuseStep 4509755 = 6764633) B6764633
theorem B2675051 : Blo 790340 2675051 := bstep (se 1 (by rfl) ⟨2006288, by rfl⟩ : syracuseStep 2675051 = 4012577) B4012577
theorem B2478511 : Blo 790340 2478511 := bstep (se 1 (by rfl) ⟨1858883, by rfl⟩ : syracuseStep 2478511 = 3717767) B3717767
theorem B6410771 : Blo 790340 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B2675321 : Blo 790340 2675321 := bstep (se 2 (by rfl) ⟨1003245, by rfl⟩ : syracuseStep 2675321 = 2006491) B2006491
theorem B6018137 : Blo 790340 6018137 := bstep (se 2 (by rfl) ⟨2256801, by rfl⟩ : syracuseStep 6018137 = 4513603) B4513603
theorem B4019543 : Blo 790340 4019543 := bstep (se 1 (by rfl) ⟨3014657, by rfl⟩ : syracuseStep 4019543 = 6029315) B6029315
theorem B4511213 : Blo 790340 4511213 := bstep (se 3 (by rfl) ⟨845852, by rfl⟩ : syracuseStep 4511213 = 1691705) B1691705
theorem B24401999 : Blo 790340 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B4020353 : Blo 790340 4020353 := bstep (se 2 (by rfl) ⟨1507632, by rfl⟩ : syracuseStep 4020353 = 3015265) B3015265
theorem B6773003 : Blo 790340 6773003 := bstep (se 1 (by rfl) ⟨5079752, by rfl⟩ : syracuseStep 6773003 = 10159505) B10159505
theorem B69556493 : Blo 790340 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B2677103 : Blo 790340 2677103 := bstep (se 1 (by rfl) ⟨2007827, by rfl⟩ : syracuseStep 2677103 = 4015655) B4015655
theorem B3660275 : Blo 790340 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B5069375 : Blo 790340 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B1333867 : Blo 790340 1333867 := bstep (se 1 (by rfl) ⟨1000400, by rfl⟩ : syracuseStep 1333867 = 2000801) B2000801
theorem B6773381 : Blo 790340 6773381 := bstep (se 4 (by rfl) ⟨635004, by rfl⟩ : syracuseStep 6773381 = 1270009) B1270009
theorem B1334171 : Blo 790340 1334171 := bstep (se 1 (by rfl) ⟨1000628, by rfl⟩ : syracuseStep 1334171 = 2001257) B2001257
theorem B4021163 : Blo 790340 4021163 := bstep (se 1 (by rfl) ⟨3015872, by rfl⟩ : syracuseStep 4021163 = 6031745) B6031745
theorem B3660923 : Blo 790340 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B2252063 : Blo 790340 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B2710921 : Blo 790340 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B3431879 : Blo 790340 3431879 := bstep (se 1 (by rfl) ⟨2573909, by rfl⟩ : syracuseStep 3431879 = 5147819) B5147819
theorem B6020567 : Blo 790340 6020567 := bstep (se 1 (by rfl) ⟨4515425, by rfl⟩ : syracuseStep 6020567 = 9030851) B9030851
theorem B12213803 : Blo 790340 12213803 := bstep (se 1 (by rfl) ⟨9160352, by rfl⟩ : syracuseStep 12213803 = 18320705) B18320705
theorem B1072711 : Blo 790340 1072711 := bstep (se 1 (by rfl) ⟨804533, by rfl⟩ : syracuseStep 1072711 = 1609067) B1609067
theorem B2678507 : Blo 790340 2678507 := bstep (se 1 (by rfl) ⟨2008880, by rfl⟩ : syracuseStep 2678507 = 4017761) B4017761
theorem B4349675 : Blo 790340 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B2252701 : Blo 790340 2252701 := bstep (se 3 (by rfl) ⟨422381, by rfl⟩ : syracuseStep 2252701 = 844763) B844763
theorem B68378741 : Blo 790340 68378741 := bstep (se 5 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 68378741 = 6410507) B6410507
theorem B6021539 : Blo 790340 6021539 := bstep (se 1 (by rfl) ⟨4516154, by rfl⟩ : syracuseStep 6021539 = 9032309) B9032309
theorem B28959383 : Blo 790340 28959383 := bstep (se 1 (by rfl) ⟨21719537, by rfl⟩ : syracuseStep 28959383 = 43439075) B43439075
theorem B2679479 : Blo 790340 2679479 := bstep (se 1 (by rfl) ⟨2009609, by rfl⟩ : syracuseStep 2679479 = 4019219) B4019219
theorem B4809419 : Blo 790340 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B5071835 : Blo 790340 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B4285655 : Blo 790340 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B1926497 : Blo 790340 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B5072473 : Blo 790340 5072473 := bstep (se 2 (by rfl) ⟨1902177, by rfl⟩ : syracuseStep 5072473 = 3804355) B3804355
theorem B1500859 : Blo 790340 1500859 := bstep (se 1 (by rfl) ⟨1125644, by rfl⟩ : syracuseStep 1500859 = 2251289) B2251289
theorem B27453329 : Blo 790340 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B3008765 : Blo 790340 3008765 := bstep (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) B1128287
theorem B9038141 : Blo 790340 9038141 := bstep (se 3 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 9038141 = 3389303) B3389303
theorem B1338079 : Blo 790340 1338079 := bstep (se 1 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 1338079 = 2007119) B2007119
theorem B6023969 : Blo 790340 6023969 := bstep (se 2 (by rfl) ⟨2258988, by rfl⟩ : syracuseStep 6023969 = 4517977) B4517977
theorem B1338511 : Blo 790340 1338511 := bstep (se 1 (by rfl) ⟨1003883, by rfl⟩ : syracuseStep 1338511 = 2007767) B2007767
theorem B814447 : Blo 790340 814447 := bstep (se 1 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 814447 = 1221671) B1221671
theorem B1338761 : Blo 790340 1338761 := bstep (se 2 (by rfl) ⟨502035, by rfl⟩ : syracuseStep 1338761 = 1004071) B1004071
theorem B3206587 : Blo 790340 3206587 := bstep (se 1 (by rfl) ⟨2404940, by rfl⟩ : syracuseStep 3206587 = 4809881) B4809881
theorem B1502803 : Blo 790340 1502803 := bstep (se 1 (by rfl) ⟨1127102, by rfl⟩ : syracuseStep 1502803 = 2254205) B2254205
theorem B11398765 : Blo 790340 11398765 := bstep (se 3 (by rfl) ⟨2137268, by rfl⟩ : syracuseStep 11398765 = 4274537) B4274537
theorem B1503031 : Blo 790340 1503031 := bstep (se 1 (by rfl) ⟨1127273, by rfl⟩ : syracuseStep 1503031 = 2254547) B2254547
theorem B1339193 : Blo 790340 1339193 := bstep (se 2 (by rfl) ⟨502197, by rfl⟩ : syracuseStep 1339193 = 1004395) B1004395
theorem B4518251 : Blo 790340 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B12841517 : Blo 790340 12841517 := bstep (se 3 (by rfl) ⟨2407784, by rfl⟩ : syracuseStep 12841517 = 4815569) B4815569
theorem B11596385 : Blo 790340 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B1504079 : Blo 790340 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B1340239 : Blo 790340 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B28865393 : Blo 790340 28865393 := bstep (se 2 (by rfl) ⟨10824522, by rfl⟩ : syracuseStep 28865393 = 21649045) B21649045
theorem B2257895 : Blo 790340 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B5075959 : Blo 790340 5075959 := bstep (se 1 (by rfl) ⟨3806969, by rfl⟩ : syracuseStep 5075959 = 7613939) B7613939
theorem B3011681 : Blo 790340 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B1504489 : Blo 790340 1504489 := bstep (se 2 (by rfl) ⟨564183, by rfl⟩ : syracuseStep 1504489 = 1128367) B1128367
theorem B3798359 : Blo 790340 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B41186677 : Blo 790340 41186677 := bstep (se 5 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 41186677 = 3861251) B3861251
theorem B1504649 : Blo 790340 1504649 := bstep (se 2 (by rfl) ⟨564243, by rfl⟩ : syracuseStep 1504649 = 1128487) B1128487
theorem B8123809 : Blo 790340 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B4519709 : Blo 790340 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B1505081 : Blo 790340 1505081 := bstep (se 2 (by rfl) ⟨564405, by rfl⟩ : syracuseStep 1505081 = 1128811) B1128811
theorem B3799169 : Blo 790340 3799169 := bstep (se 2 (by rfl) ⟨1424688, by rfl⟩ : syracuseStep 3799169 = 2849377) B2849377
theorem B2029931 : Blo 790340 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B4291145 : Blo 790340 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B4291319 : Blo 790340 4291319 := bstep (se 1 (by rfl) ⟨3218489, by rfl⟩ : syracuseStep 4291319 = 6436979) B6436979
theorem B356023187 : Blo 790340 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B1900025 : Blo 790340 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B1507079 : Blo 790340 1507079 := bstep (se 1 (by rfl) ⟨1130309, by rfl⟩ : syracuseStep 1507079 = 2260619) B2260619
theorem B950071 : Blo 790340 950071 := bstep (se 1 (by rfl) ⟨712553, by rfl⟩ : syracuseStep 950071 = 1425107) B1425107
theorem B3669833 : Blo 790340 3669833 := bstep (se 2 (by rfl) ⟨1376187, by rfl⟩ : syracuseStep 3669833 = 2752375) B2752375
theorem B12844889 : Blo 790340 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B9404419 : Blo 790340 9404419 := bstep (se 1 (by rfl) ⟨7053314, by rfl⟩ : syracuseStep 9404419 = 14106629) B14106629
theorem B3801167 : Blo 790340 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B8552879 : Blo 790340 8552879 := bstep (se 1 (by rfl) ⟨6414659, by rfl⟩ : syracuseStep 8552879 = 12829319) B12829319
theorem B4293047 : Blo 790340 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B6783527 : Blo 790340 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B4522625 : Blo 790340 4522625 := bstep (se 2 (by rfl) ⟨1695984, by rfl⟩ : syracuseStep 4522625 = 3391969) B3391969
theorem B9011897 : Blo 790340 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B24413071 : Blo 790340 24413071 := bstep (se 1 (by rfl) ⟨18309803, by rfl⟩ : syracuseStep 24413071 = 36619607) B36619607
theorem B2032595 : Blo 790340 2032595 := bstep (se 1 (by rfl) ⟨1524446, by rfl⟩ : syracuseStep 2032595 = 3048893) B3048893
theorem B34244045 : Blo 790340 34244045 := bstep (se 3 (by rfl) ⟨6420758, by rfl⟩ : syracuseStep 34244045 = 12841517) B12841517
theorem B2001145 : Blo 790340 2001145 := bstep (se 2 (by rfl) ⟨750429, by rfl⟩ : syracuseStep 2001145 = 1500859) B1500859
theorem B3377447 : Blo 790340 3377447 := bstep (se 1 (by rfl) ⟨2533085, by rfl⟩ : syracuseStep 3377447 = 5066171) B5066171
theorem B22022543 : Blo 790340 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B5705149 : Blo 790340 5705149 := bstep (se 3 (by rfl) ⟨1069715, by rfl⟩ : syracuseStep 5705149 = 2139431) B2139431
theorem B51973771 : Blo 790340 51973771 := bstep (se 1 (by rfl) ⟨38980328, by rfl⟩ : syracuseStep 51973771 = 77960657) B77960657
theorem B790343 : Blo 790340 790343 := bstep (se 1 (by rfl) ⟨592757, by rfl⟩ : syracuseStep 790343 = 1185515) B1185515
theorem B790495 : Blo 790340 790495 := bstep (se 1 (by rfl) ⟨592871, by rfl⟩ : syracuseStep 790495 = 1185743) B1185743
theorem B790759 : Blo 790340 790759 := bstep (se 1 (by rfl) ⟨593069, by rfl⟩ : syracuseStep 790759 = 1186139) B1186139
theorem B790911 : Blo 790340 790911 := bstep (se 1 (by rfl) ⟨593183, by rfl⟩ : syracuseStep 790911 = 1186367) B1186367
theorem B3379583 : Blo 790340 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B790991 : Blo 790340 790991 := bstep (se 1 (by rfl) ⟨593243, by rfl⟩ : syracuseStep 790991 = 1186487) B1186487
theorem B1085929 : Blo 790340 1085929 := bstep (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) B814447
theorem B889447 : Blo 790340 889447 := bstep (se 1 (by rfl) ⟨667085, by rfl⟩ : syracuseStep 889447 = 1334171) B1334171
theorem B791143 : Blo 790340 791143 := bstep (se 1 (by rfl) ⟨593357, by rfl⟩ : syracuseStep 791143 = 1186715) B1186715
theorem B2003737 : Blo 790340 2003737 := bstep (se 2 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 2003737 = 1502803) B1502803
theorem B791407 : Blo 790340 791407 := bstep (se 1 (by rfl) ⟨593555, by rfl⟩ : syracuseStep 791407 = 1187111) B1187111
theorem B791463 : Blo 790340 791463 := bstep (se 1 (by rfl) ⟨593597, by rfl⟩ : syracuseStep 791463 = 1187195) B1187195
theorem B791547 : Blo 790340 791547 := bstep (se 1 (by rfl) ⟨593660, by rfl⟩ : syracuseStep 791547 = 1187321) B1187321
theorem B791615 : Blo 790340 791615 := bstep (se 1 (by rfl) ⟨593711, by rfl⟩ : syracuseStep 791615 = 1187423) B1187423
theorem B2004041 : Blo 790340 2004041 := bstep (se 2 (by rfl) ⟨751515, by rfl⟩ : syracuseStep 2004041 = 1503031) B1503031
theorem B8131691 : Blo 790340 8131691 := bstep (se 1 (by rfl) ⟨6098768, by rfl⟩ : syracuseStep 8131691 = 12197537) B12197537
theorem B791759 : Blo 790340 791759 := bstep (se 1 (by rfl) ⟨593819, by rfl⟩ : syracuseStep 791759 = 1187639) B1187639
theorem B791963 : Blo 790340 791963 := bstep (se 1 (by rfl) ⟨593972, by rfl⟩ : syracuseStep 791963 = 1187945) B1187945
theorem B45585827 : Blo 790340 45585827 := bstep (se 1 (by rfl) ⟨34189370, by rfl⟩ : syracuseStep 45585827 = 68378741) B68378741
theorem B792175 : Blo 790340 792175 := bstep (se 1 (by rfl) ⟨594131, by rfl⟩ : syracuseStep 792175 = 1188263) B1188263
theorem B792231 : Blo 790340 792231 := bstep (se 1 (by rfl) ⟨594173, by rfl⟩ : syracuseStep 792231 = 1188347) B1188347
theorem B792315 : Blo 790340 792315 := bstep (se 1 (by rfl) ⟨594236, by rfl⟩ : syracuseStep 792315 = 1188473) B1188473
theorem B792351 : Blo 790340 792351 := bstep (se 1 (by rfl) ⟨594263, by rfl⟩ : syracuseStep 792351 = 1188527) B1188527
theorem B1185599 : Blo 790340 1185599 := bstep (se 1 (by rfl) ⟨889199, by rfl⟩ : syracuseStep 1185599 = 1778399) B1778399
theorem B792383 : Blo 790340 792383 := bstep (se 1 (by rfl) ⟨594287, by rfl⟩ : syracuseStep 792383 = 1188575) B1188575
theorem B1185767 : Blo 790340 1185767 := bstep (se 1 (by rfl) ⟨889325, by rfl⟩ : syracuseStep 1185767 = 1778651) B1778651
theorem B3381223 : Blo 790340 3381223 := bstep (se 1 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 3381223 = 5071835) B5071835
theorem B792559 : Blo 790340 792559 := bstep (se 1 (by rfl) ⟨594419, by rfl⟩ : syracuseStep 792559 = 1188839) B1188839
theorem B1185785 : Blo 790340 1185785 := bstep (se 2 (by rfl) ⟨444669, by rfl⟩ : syracuseStep 1185785 = 889339) B889339
theorem B1185887 : Blo 790340 1185887 := bstep (se 1 (by rfl) ⟨889415, by rfl⟩ : syracuseStep 1185887 = 1778831) B1778831
theorem B2857103 : Blo 790340 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B1185947 : Blo 790340 1185947 := bstep (se 1 (by rfl) ⟨889460, by rfl⟩ : syracuseStep 1185947 = 1778921) B1778921
theorem B792731 : Blo 790340 792731 := bstep (se 1 (by rfl) ⟨594548, by rfl⟩ : syracuseStep 792731 = 1189097) B1189097
theorem B1185983 : Blo 790340 1185983 := bstep (se 1 (by rfl) ⟨889487, by rfl⟩ : syracuseStep 1185983 = 1778975) B1778975
theorem B792767 : Blo 790340 792767 := bstep (se 1 (by rfl) ⟨594575, by rfl⟩ : syracuseStep 792767 = 1189151) B1189151
theorem B5707979 : Blo 790340 5707979 := bstep (se 1 (by rfl) ⟨4280984, by rfl⟩ : syracuseStep 5707979 = 8561969) B8561969
theorem B1186025 : Blo 790340 1186025 := bstep (se 2 (by rfl) ⟨444759, by rfl⟩ : syracuseStep 1186025 = 889519) B889519
theorem B1284331 : Blo 790340 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B792879 : Blo 790340 792879 := bstep (se 1 (by rfl) ⟨594659, by rfl⟩ : syracuseStep 792879 = 1189319) B1189319
theorem B5708207 : Blo 790340 5708207 := bstep (se 1 (by rfl) ⟨4281155, by rfl⟩ : syracuseStep 5708207 = 8562311) B8562311
theorem B4004315 : Blo 790340 4004315 := bstep (se 1 (by rfl) ⟨3003236, by rfl⟩ : syracuseStep 4004315 = 6006473) B6006473
theorem B1186331 : Blo 790340 1186331 := bstep (se 1 (by rfl) ⟨889748, by rfl⟩ : syracuseStep 1186331 = 1779497) B1779497
theorem B793115 : Blo 790340 793115 := bstep (se 1 (by rfl) ⟨594836, by rfl⟩ : syracuseStep 793115 = 1189673) B1189673
theorem B793119 : Blo 790340 793119 := bstep (se 1 (by rfl) ⟨594839, by rfl⟩ : syracuseStep 793119 = 1189679) B1189679
theorem B1186409 : Blo 790340 1186409 := bstep (se 2 (by rfl) ⟨444903, by rfl⟩ : syracuseStep 1186409 = 889807) B889807
theorem B2005843 : Blo 790340 2005843 := bstep (se 1 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 2005843 = 3008765) B3008765
theorem B793435 : Blo 790340 793435 := bstep (se 1 (by rfl) ⟨595076, by rfl⟩ : syracuseStep 793435 = 1190153) B1190153
theorem B793503 : Blo 790340 793503 := bstep (se 1 (by rfl) ⟨595127, by rfl⟩ : syracuseStep 793503 = 1190255) B1190255
theorem B2005985 : Blo 790340 2005985 := bstep (se 2 (by rfl) ⟨752244, by rfl⟩ : syracuseStep 2005985 = 1504489) B1504489
theorem B61905941 : Blo 790340 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B793647 : Blo 790340 793647 := bstep (se 1 (by rfl) ⟨595235, by rfl⟩ : syracuseStep 793647 = 1190471) B1190471
theorem B793671 : Blo 790340 793671 := bstep (se 1 (by rfl) ⟨595253, by rfl⟩ : syracuseStep 793671 = 1190507) B1190507
theorem B1907783 : Blo 790340 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B1186937 : Blo 790340 1186937 := bstep (se 2 (by rfl) ⟨445101, by rfl⟩ : syracuseStep 1186937 = 890203) B890203
theorem B1187039 : Blo 790340 1187039 := bstep (se 1 (by rfl) ⟨890279, by rfl⟩ : syracuseStep 1187039 = 1780559) B1780559
theorem B793823 : Blo 790340 793823 := bstep (se 1 (by rfl) ⟨595367, by rfl⟩ : syracuseStep 793823 = 1190735) B1190735
theorem B1187081 : Blo 790340 1187081 := bstep (se 2 (by rfl) ⟨445155, by rfl⟩ : syracuseStep 1187081 = 890311) B890311
theorem B1187183 : Blo 790340 1187183 := bstep (se 1 (by rfl) ⟨890387, by rfl⟩ : syracuseStep 1187183 = 1780775) B1780775
theorem B1187303 : Blo 790340 1187303 := bstep (se 1 (by rfl) ⟨890477, by rfl⟩ : syracuseStep 1187303 = 1780955) B1780955
theorem B794087 : Blo 790340 794087 := bstep (se 1 (by rfl) ⟨595565, by rfl⟩ : syracuseStep 794087 = 1191131) B1191131
theorem B892507 : Blo 790340 892507 := bstep (se 1 (by rfl) ⟨669380, by rfl⟩ : syracuseStep 892507 = 1338761) B1338761
theorem B794203 : Blo 790340 794203 := bstep (se 1 (by rfl) ⟨595652, by rfl⟩ : syracuseStep 794203 = 1191305) B1191305
theorem B1187435 : Blo 790340 1187435 := bstep (se 1 (by rfl) ⟨890576, by rfl⟩ : syracuseStep 1187435 = 1781153) B1781153
theorem B1187561 : Blo 790340 1187561 := bstep (se 2 (by rfl) ⟨445335, by rfl⟩ : syracuseStep 1187561 = 890671) B890671
theorem B1187705 : Blo 790340 1187705 := bstep (se 2 (by rfl) ⟨445389, by rfl⟩ : syracuseStep 1187705 = 890779) B890779
theorem B892795 : Blo 790340 892795 := bstep (se 1 (by rfl) ⟨669596, by rfl⟩ : syracuseStep 892795 = 1339193) B1339193
theorem B1187807 : Blo 790340 1187807 := bstep (se 1 (by rfl) ⟨890855, by rfl⟩ : syracuseStep 1187807 = 1781711) B1781711
theorem B1188059 : Blo 790340 1188059 := bstep (se 1 (by rfl) ⟨891044, by rfl⟩ : syracuseStep 1188059 = 1782089) B1782089
theorem B1188071 : Blo 790340 1188071 := bstep (se 1 (by rfl) ⟨891053, by rfl⟩ : syracuseStep 1188071 = 1782107) B1782107
theorem B1188233 : Blo 790340 1188233 := bstep (se 2 (by rfl) ⟨445587, by rfl⟩ : syracuseStep 1188233 = 891175) B891175
theorem B1188329 : Blo 790340 1188329 := bstep (se 2 (by rfl) ⟨445623, by rfl⟩ : syracuseStep 1188329 = 891247) B891247
theorem B19243595 : Blo 790340 19243595 := bstep (se 1 (by rfl) ⟨14432696, by rfl⟩ : syracuseStep 19243595 = 28865393) B28865393
theorem B1188455 : Blo 790340 1188455 := bstep (se 1 (by rfl) ⟨891341, by rfl⟩ : syracuseStep 1188455 = 1782683) B1782683
theorem B1188587 : Blo 790340 1188587 := bstep (se 1 (by rfl) ⟨891440, by rfl⟩ : syracuseStep 1188587 = 1782881) B1782881
theorem B2007787 : Blo 790340 2007787 := bstep (se 1 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 2007787 = 3011681) B3011681
theorem B6005501 : Blo 790340 6005501 := bstep (se 3 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 6005501 = 2252063) B2252063
theorem B1188617 : Blo 790340 1188617 := bstep (se 2 (by rfl) ⟨445731, by rfl⟩ : syracuseStep 1188617 = 891463) B891463
theorem B1778489 : Blo 790340 1778489 := bstep (se 2 (by rfl) ⟨666933, by rfl⟩ : syracuseStep 1778489 = 1333867) B1333867
theorem B1778543 : Blo 790340 1778543 := bstep (se 1 (by rfl) ⟨1333907, by rfl⟩ : syracuseStep 1778543 = 2667815) B2667815
theorem B1188719 : Blo 790340 1188719 := bstep (se 1 (by rfl) ⟨891539, by rfl⟩ : syracuseStep 1188719 = 1783079) B1783079
theorem B2532239 : Blo 790340 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B1188971 : Blo 790340 1188971 := bstep (se 1 (by rfl) ⟨891728, by rfl⟩ : syracuseStep 1188971 = 1783457) B1783457
theorem B9020645 : Blo 790340 9020645 := bstep (se 4 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 9020645 = 1691371) B1691371
theorem B1189211 : Blo 790340 1189211 := bstep (se 1 (by rfl) ⟨891908, by rfl⟩ : syracuseStep 1189211 = 1783817) B1783817
theorem B2532779 : Blo 790340 2532779 := bstep (se 1 (by rfl) ⟨1899584, by rfl⟩ : syracuseStep 2532779 = 3799169) B3799169
theorem B1779119 : Blo 790340 1779119 := bstep (se 1 (by rfl) ⟨1334339, by rfl⟩ : syracuseStep 1779119 = 2668679) B2668679
theorem B1353287 : Blo 790340 1353287 := bstep (se 1 (by rfl) ⟨1014965, by rfl⟩ : syracuseStep 1353287 = 2029931) B2029931
theorem B20325977 : Blo 790340 20325977 := bstep (se 2 (by rfl) ⟨7622241, by rfl⟩ : syracuseStep 20325977 = 15244483) B15244483
theorem B1189487 : Blo 790340 1189487 := bstep (se 1 (by rfl) ⟨892115, by rfl⟩ : syracuseStep 1189487 = 1784231) B1784231
theorem B1189559 : Blo 790340 1189559 := bstep (se 1 (by rfl) ⟨892169, by rfl⟩ : syracuseStep 1189559 = 1784339) B1784339
theorem B1189595 : Blo 790340 1189595 := bstep (se 1 (by rfl) ⟨892196, by rfl⟩ : syracuseStep 1189595 = 1784393) B1784393
theorem B2860763 : Blo 790340 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B2860879 : Blo 790340 2860879 := bstep (se 1 (by rfl) ⟨2145659, by rfl⟩ : syracuseStep 2860879 = 4291319) B4291319
theorem B3614561 : Blo 790340 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B1189769 : Blo 790340 1189769 := bstep (se 2 (by rfl) ⟨446163, by rfl⟩ : syracuseStep 1189769 = 892327) B892327
theorem B237348791 : Blo 790340 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B1189871 : Blo 790340 1189871 := bstep (se 1 (by rfl) ⟨892403, by rfl⟩ : syracuseStep 1189871 = 1784807) B1784807
theorem B1779947 : Blo 790340 1779947 := bstep (se 1 (by rfl) ⟨1334960, by rfl⟩ : syracuseStep 1779947 = 2669921) B2669921
theorem B1190123 : Blo 790340 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B1190183 : Blo 790340 1190183 := bstep (se 1 (by rfl) ⟨892637, by rfl⟩ : syracuseStep 1190183 = 1785275) B1785275
theorem B1190267 : Blo 790340 1190267 := bstep (se 1 (by rfl) ⟨892700, by rfl⟩ : syracuseStep 1190267 = 1785401) B1785401
theorem B8563259 : Blo 790340 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B1190537 : Blo 790340 1190537 := bstep (se 2 (by rfl) ⟨446451, by rfl⟩ : syracuseStep 1190537 = 892903) B892903
theorem B1190711 : Blo 790340 1190711 := bstep (se 1 (by rfl) ⟨893033, by rfl⟩ : syracuseStep 1190711 = 1786067) B1786067
theorem B1190747 : Blo 790340 1190747 := bstep (se 1 (by rfl) ⟨893060, by rfl⟩ : syracuseStep 1190747 = 1786121) B1786121
theorem B1190891 : Blo 790340 1190891 := bstep (se 1 (by rfl) ⟨893168, by rfl⟩ : syracuseStep 1190891 = 1786337) B1786337
theorem B1191095 : Blo 790340 1191095 := bstep (se 1 (by rfl) ⟨893321, by rfl⟩ : syracuseStep 1191095 = 1786643) B1786643
theorem B2534699 : Blo 790340 2534699 := bstep (se 1 (by rfl) ⟨1901024, by rfl⟩ : syracuseStep 2534699 = 3802049) B3802049
theorem B1191335 : Blo 790340 1191335 := bstep (se 1 (by rfl) ⟨893501, by rfl⟩ : syracuseStep 1191335 = 1787003) B1787003
theorem B1781243 : Blo 790340 1781243 := bstep (se 1 (by rfl) ⟨1335932, by rfl⟩ : syracuseStep 1781243 = 2671865) B2671865
theorem B1191419 : Blo 790340 1191419 := bstep (se 1 (by rfl) ⟨893564, by rfl⟩ : syracuseStep 1191419 = 1787129) B1787129
theorem B1781423 : Blo 790340 1781423 := bstep (se 1 (by rfl) ⟨1336067, by rfl⟩ : syracuseStep 1781423 = 2672135) B2672135
theorem B1782071 : Blo 790340 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B1782143 : Blo 790340 1782143 := bstep (se 1 (by rfl) ⟨1336607, by rfl⟩ : syracuseStep 1782143 = 2673215) B2673215
theorem B6763297 : Blo 790340 6763297 := bstep (se 2 (by rfl) ⟨2536236, by rfl⟩ : syracuseStep 6763297 = 5072473) B5072473
theorem B5157665 : Blo 790340 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B5714813 : Blo 790340 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B3388331 : Blo 790340 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B4830653 : Blo 790340 4830653 := bstep (se 3 (by rfl) ⟨905747, by rfl⟩ : syracuseStep 4830653 = 1811495) B1811495
theorem B1783367 : Blo 790340 1783367 := bstep (se 1 (by rfl) ⟨1337525, by rfl⟩ : syracuseStep 1783367 = 2675051) B2675051
theorem B4273847 : Blo 790340 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B1783547 : Blo 790340 1783547 := bstep (se 1 (by rfl) ⟨1337660, by rfl⟩ : syracuseStep 1783547 = 2675321) B2675321
theorem B4012091 : Blo 790340 4012091 := bstep (se 1 (by rfl) ⟨3009068, by rfl⟩ : syracuseStep 4012091 = 6018137) B6018137
theorem B2668787 : Blo 790340 2668787 := bstep (se 1 (by rfl) ⟨2001590, by rfl⟩ : syracuseStep 2668787 = 4003181) B4003181
theorem B2668841 : Blo 790340 2668841 := bstep (se 2 (by rfl) ⟨1000815, by rfl⟩ : syracuseStep 2668841 = 2001631) B2001631
theorem B1784105 : Blo 790340 1784105 := bstep (se 2 (by rfl) ⟨669039, by rfl⟩ : syracuseStep 1784105 = 1338079) B1338079
theorem B2537801 : Blo 790340 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B3389971 : Blo 790340 3389971 := bstep (se 1 (by rfl) ⟨2542478, by rfl⟩ : syracuseStep 3389971 = 5084957) B5084957
theorem B16267999 : Blo 790340 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B11123459 : Blo 790340 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B1784681 : Blo 790340 1784681 := bstep (se 2 (by rfl) ⟨669255, by rfl⟩ : syracuseStep 1784681 = 1338511) B1338511
theorem B1784735 : Blo 790340 1784735 := bstep (se 1 (by rfl) ⟨1338551, by rfl⟩ : syracuseStep 1784735 = 2677103) B2677103
theorem B1719265 : Blo 790340 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B4275449 : Blo 790340 4275449 := bstep (se 2 (by rfl) ⟨1603293, by rfl⟩ : syracuseStep 4275449 = 3206587) B3206587
theorem B4013549 : Blo 790340 4013549 := bstep (se 3 (by rfl) ⟨752540, by rfl⟩ : syracuseStep 4013549 = 1505081) B1505081
theorem B4013711 : Blo 790340 4013711 := bstep (se 1 (by rfl) ⟨3010283, by rfl⟩ : syracuseStep 4013711 = 6020567) B6020567
theorem B8142535 : Blo 790340 8142535 := bstep (se 1 (by rfl) ⟨6106901, by rfl⟩ : syracuseStep 8142535 = 12213803) B12213803
theorem B9617129 : Blo 790340 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B2670407 : Blo 790340 2670407 := bstep (se 1 (by rfl) ⟨2002805, by rfl⟩ : syracuseStep 2670407 = 4005611) B4005611
theorem B1785671 : Blo 790340 1785671 := bstep (se 1 (by rfl) ⟨1339253, by rfl⟩ : syracuseStep 1785671 = 2678507) B2678507
theorem B2899783 : Blo 790340 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B2670461 : Blo 790340 2670461 := bstep (se 3 (by rfl) ⟨500711, by rfl⟩ : syracuseStep 2670461 = 1001423) B1001423
theorem B2670731 : Blo 790340 2670731 := bstep (se 1 (by rfl) ⟨2003048, by rfl⟩ : syracuseStep 2670731 = 4006097) B4006097
theorem B3391627 : Blo 790340 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B4014359 : Blo 790340 4014359 := bstep (se 1 (by rfl) ⟨3010769, by rfl⟩ : syracuseStep 4014359 = 6021539) B6021539
theorem B1688015 : Blo 790340 1688015 := bstep (se 1 (by rfl) ⟨1266011, by rfl⟩ : syracuseStep 1688015 = 2532023) B2532023
theorem B2671055 : Blo 790340 2671055 := bstep (se 1 (by rfl) ⟨2003291, by rfl⟩ : syracuseStep 2671055 = 4006583) B4006583
theorem B1786319 : Blo 790340 1786319 := bstep (se 1 (by rfl) ⟨1339739, by rfl⟩ : syracuseStep 1786319 = 2679479) B2679479
theorem B185483981 : Blo 790340 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B2671379 : Blo 790340 2671379 := bstep (se 1 (by rfl) ⟨2003534, by rfl⟩ : syracuseStep 2671379 = 4007069) B4007069
theorem B1786985 : Blo 790340 1786985 := bstep (se 2 (by rfl) ⟨670119, by rfl⟩ : syracuseStep 1786985 = 1340239) B1340239
theorem B4506839 : Blo 790340 4506839 := bstep (se 1 (by rfl) ⟨3380129, by rfl⟩ : syracuseStep 4506839 = 6760259) B6760259
theorem B18302219 : Blo 790340 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B6767945 : Blo 790340 6767945 := bstep (se 2 (by rfl) ⟨2537979, by rfl⟩ : syracuseStep 6767945 = 5075959) B5075959
theorem B2672243 : Blo 790340 2672243 := bstep (se 1 (by rfl) ⟨2004182, by rfl⟩ : syracuseStep 2672243 = 4008365) B4008365
theorem B6440609 : Blo 790340 6440609 := bstep (se 2 (by rfl) ⟨2415228, by rfl⟩ : syracuseStep 6440609 = 4830457) B4830457
theorem B2672351 : Blo 790340 2672351 := bstep (se 1 (by rfl) ⟨2004263, by rfl⟩ : syracuseStep 2672351 = 4008527) B4008527
theorem B4015979 : Blo 790340 4015979 := bstep (se 1 (by rfl) ⟨3011984, by rfl⟩ : syracuseStep 4015979 = 6023969) B6023969
theorem B10831745 : Blo 790340 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B2672513 : Blo 790340 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B2673053 : Blo 790340 2673053 := bstep (se 3 (by rfl) ⟨501197, by rfl⟩ : syracuseStep 2673053 = 1002395) B1002395
theorem B2673323 : Blo 790340 2673323 := bstep (se 1 (by rfl) ⟨2004992, by rfl⟩ : syracuseStep 2673323 = 4009985) B4009985
theorem B8571743 : Blo 790340 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B2673863 : Blo 790340 2673863 := bstep (se 1 (by rfl) ⟨2005397, by rfl⟩ : syracuseStep 2673863 = 4010795) B4010795
theorem B1002719 : Blo 790340 1002719 := bstep (se 1 (by rfl) ⟨752039, by rfl⟩ : syracuseStep 1002719 = 1504079) B1504079
theorem B2542927 : Blo 790340 2542927 := bstep (se 1 (by rfl) ⟨1907195, by rfl⟩ : syracuseStep 2542927 = 3814391) B3814391
theorem B1068457 : Blo 790340 1068457 := bstep (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) B801343
theorem B1003099 : Blo 790340 1003099 := bstep (se 1 (by rfl) ⟨752324, by rfl⟩ : syracuseStep 1003099 = 1504649) B1504649
theorem B2675159 : Blo 790340 2675159 := bstep (se 1 (by rfl) ⟨2006369, by rfl⟩ : syracuseStep 2675159 = 4012739) B4012739
theorem B6017651 : Blo 790340 6017651 := bstep (se 1 (by rfl) ⟨4513238, by rfl⟩ : syracuseStep 6017651 = 9026477) B9026477
theorem B1430281 : Blo 790340 1430281 := bstep (se 2 (by rfl) ⟨536355, by rfl⟩ : syracuseStep 1430281 = 1072711) B1072711
theorem B4510505 : Blo 790340 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B1266683 : Blo 790340 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B1266761 : Blo 790340 1266761 := bstep (se 2 (by rfl) ⟨475035, by rfl⟩ : syracuseStep 1266761 = 950071) B950071
theorem B1004719 : Blo 790340 1004719 := bstep (se 1 (by rfl) ⟨753539, by rfl⟩ : syracuseStep 1004719 = 1507079) B1507079
theorem B3003601 : Blo 790340 3003601 := bstep (se 2 (by rfl) ⟨1126350, by rfl⟩ : syracuseStep 3003601 = 2252701) B2252701
theorem B2446555 : Blo 790340 2446555 := bstep (se 1 (by rfl) ⟨1834916, by rfl⟩ : syracuseStep 2446555 = 3669833) B3669833
theorem B9164411 : Blo 790340 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B2676617 : Blo 790340 2676617 := bstep (se 2 (by rfl) ⟨1003731, by rfl⟩ : syracuseStep 2676617 = 2007463) B2007463
theorem B3004391 : Blo 790340 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B2676833 : Blo 790340 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B7624975 : Blo 790340 7624975 := bstep (se 1 (by rfl) ⟨5718731, by rfl⟩ : syracuseStep 7624975 = 11437463) B11437463
theorem B3004847 : Blo 790340 3004847 := bstep (se 1 (by rfl) ⟨2253635, by rfl⟩ : syracuseStep 3004847 = 4507271) B4507271
theorem B1203103 : Blo 790340 1203103 := bstep (se 1 (by rfl) ⟨902327, by rfl⟩ : syracuseStep 1203103 = 1804655) B1804655
theorem B4512671 : Blo 790340 4512671 := bstep (se 1 (by rfl) ⟨3384503, by rfl⟩ : syracuseStep 4512671 = 6769007) B6769007
theorem B14474159 : Blo 790340 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B2251745 : Blo 790340 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B2677751 : Blo 790340 2677751 := bstep (se 1 (by rfl) ⟨2008313, by rfl⟩ : syracuseStep 2677751 = 4016627) B4016627
theorem B77225021 : Blo 790340 77225021 := bstep (se 3 (by rfl) ⟨14479691, by rfl⟩ : syracuseStep 77225021 = 28959383) B28959383
theorem B1334495 : Blo 790340 1334495 := bstep (se 1 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 1334495 = 2001743) B2001743
theorem B2678183 : Blo 790340 2678183 := bstep (se 1 (by rfl) ⟨2008637, by rfl⟩ : syracuseStep 2678183 = 4017275) B4017275
theorem B3006031 : Blo 790340 3006031 := bstep (se 1 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 3006031 = 4509047) B4509047
theorem B1334927 : Blo 790340 1334927 := bstep (se 1 (by rfl) ⟨1001195, by rfl⟩ : syracuseStep 1334927 = 2002391) B2002391
theorem B2678615 : Blo 790340 2678615 := bstep (se 1 (by rfl) ⟨2008961, by rfl⟩ : syracuseStep 2678615 = 4017923) B4017923
theorem B1335163 : Blo 790340 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B6021053 : Blo 790340 6021053 := bstep (se 3 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 6021053 = 2257895) B2257895
theorem B3006503 : Blo 790340 3006503 := bstep (se 1 (by rfl) ⟨2254877, by rfl⟩ : syracuseStep 3006503 = 4509755) B4509755
theorem B4514129 : Blo 790340 4514129 := bstep (se 2 (by rfl) ⟨1692798, by rfl⟩ : syracuseStep 4514129 = 3385597) B3385597
theorem B2679425 : Blo 790340 2679425 := bstep (se 2 (by rfl) ⟨1004784, by rfl⟩ : syracuseStep 2679425 = 2009569) B2009569
theorem B2679695 : Blo 790340 2679695 := bstep (se 1 (by rfl) ⟨2009771, by rfl⟩ : syracuseStep 2679695 = 4019543) B4019543
theorem B5071859 : Blo 790340 5071859 := bstep (se 1 (by rfl) ⟨3803894, by rfl⟩ : syracuseStep 5071859 = 7607789) B7607789
theorem B3007475 : Blo 790340 3007475 := bstep (se 1 (by rfl) ⟨2255606, by rfl⟩ : syracuseStep 3007475 = 4511213) B4511213
theorem B2680235 : Blo 790340 2680235 := bstep (se 1 (by rfl) ⟨2010176, by rfl⟩ : syracuseStep 2680235 = 4020353) B4020353
theorem B16541101 : Blo 790340 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B5072321 : Blo 790340 5072321 := bstep (se 2 (by rfl) ⟨1902120, by rfl⟩ : syracuseStep 5072321 = 3804241) B3804241
theorem B2713085 : Blo 790340 2713085 := bstep (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) B1017407
theorem B4515335 : Blo 790340 4515335 := bstep (se 1 (by rfl) ⟨3386501, by rfl⟩ : syracuseStep 4515335 = 6773003) B6773003
theorem B1336999 : Blo 790340 1336999 := bstep (se 1 (by rfl) ⟨1002749, by rfl⟩ : syracuseStep 1336999 = 2005499) B2005499
theorem B4515587 : Blo 790340 4515587 := bstep (se 1 (by rfl) ⟨3386690, by rfl⟩ : syracuseStep 4515587 = 6773381) B6773381
theorem B2680775 : Blo 790340 2680775 := bstep (se 1 (by rfl) ⟨2010581, by rfl⟩ : syracuseStep 2680775 = 4021163) B4021163
theorem B15198353 : Blo 790340 15198353 := bstep (se 2 (by rfl) ⟨5699382, by rfl⟩ : syracuseStep 15198353 = 11398765) B11398765
theorem B1271963 : Blo 790340 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B2287919 : Blo 790340 2287919 := bstep (se 1 (by rfl) ⟨1715939, by rfl⟩ : syracuseStep 2287919 = 3431879) B3431879
theorem B1337647 : Blo 790340 1337647 := bstep (se 1 (by rfl) ⟨1003235, by rfl⟩ : syracuseStep 1337647 = 2006471) B2006471
theorem B5794213 : Blo 790340 5794213 := bstep (se 4 (by rfl) ⟨543207, by rfl⟩ : syracuseStep 5794213 = 1086415) B1086415
theorem B1338167 : Blo 790340 1338167 := bstep (se 1 (by rfl) ⟨1003625, by rfl⟩ : syracuseStep 1338167 = 2007251) B2007251
theorem B7629623 : Blo 790340 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B3206279 : Blo 790340 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B3304681 : Blo 790340 3304681 := bstep (se 2 (by rfl) ⟨1239255, by rfl⟩ : syracuseStep 3304681 = 2478511) B2478511
theorem B1338943 : Blo 790340 1338943 := bstep (se 1 (by rfl) ⟨1004207, by rfl⟩ : syracuseStep 1338943 = 2008415) B2008415
theorem B9760733 : Blo 790340 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B4812995 : Blo 790340 4812995 := bstep (se 1 (by rfl) ⟨3609746, by rfl⟩ : syracuseStep 4812995 = 7219493) B7219493
theorem B6025427 : Blo 790340 6025427 := bstep (se 1 (by rfl) ⟨4519070, by rfl⟩ : syracuseStep 6025427 = 9038141) B9038141
theorem B1339679 : Blo 790340 1339679 := bstep (se 1 (by rfl) ⟨1004759, by rfl⟩ : syracuseStep 1339679 = 2009519) B2009519
theorem B54915569 : Blo 790340 54915569 := bstep (se 2 (by rfl) ⟨20593338, by rfl⟩ : syracuseStep 54915569 = 41186677) B41186677
theorem B1340327 : Blo 790340 1340327 := bstep (se 1 (by rfl) ⟨1005245, by rfl⟩ : syracuseStep 1340327 = 2010491) B2010491
theorem B3012167 : Blo 790340 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B9762461 : Blo 790340 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B7730923 : Blo 790340 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B3013139 : Blo 790340 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B1899065 : Blo 790340 1899065 := bstep (se 2 (by rfl) ⟨712149, by rfl⟩ : syracuseStep 1899065 = 1424299) B1424299
theorem B2260391 : Blo 790340 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B5701229 : Blo 790340 5701229 := bstep (se 3 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 5701229 = 2137961) B2137961
theorem B6782777 : Blo 790340 6782777 := bstep (se 2 (by rfl) ⟨2543541, by rfl⟩ : syracuseStep 6782777 = 5087083) B5087083
theorem B4522169 : Blo 790340 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B5701919 : Blo 790340 5701919 := bstep (se 1 (by rfl) ⟨4276439, by rfl⟩ : syracuseStep 5701919 = 8552879) B8552879
theorem B4522351 : Blo 790340 4522351 := bstep (se 1 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 4522351 = 6783527) B6783527
theorem B3015083 : Blo 790340 3015083 := bstep (se 1 (by rfl) ⟨2261312, by rfl⟩ : syracuseStep 3015083 = 4522625) B4522625
theorem B4293739 : Blo 790340 4293739 := bstep (se 1 (by rfl) ⟨3220304, by rfl⟩ : syracuseStep 4293739 = 6440609) B6440609
theorem B14681695 : Blo 790340 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B790399 : Blo 790340 790399 := bstep (se 1 (by rfl) ⟨592799, by rfl⟩ : syracuseStep 790399 = 1185599) B1185599
theorem B790511 : Blo 790340 790511 := bstep (se 1 (by rfl) ⟨592883, by rfl⟩ : syracuseStep 790511 = 1185767) B1185767
theorem B2002927 : Blo 790340 2002927 := bstep (se 1 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 2002927 = 3004391) B3004391
theorem B790523 : Blo 790340 790523 := bstep (se 1 (by rfl) ⟨592892, by rfl⟩ : syracuseStep 790523 = 1185785) B1185785
theorem B790591 : Blo 790340 790591 := bstep (se 1 (by rfl) ⟨592943, by rfl⟩ : syracuseStep 790591 = 1185887) B1185887
theorem B1904735 : Blo 790340 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B790631 : Blo 790340 790631 := bstep (se 1 (by rfl) ⟨592973, by rfl⟩ : syracuseStep 790631 = 1185947) B1185947
theorem B790655 : Blo 790340 790655 := bstep (se 1 (by rfl) ⟨592991, by rfl⟩ : syracuseStep 790655 = 1185983) B1185983
theorem B3805319 : Blo 790340 3805319 := bstep (se 1 (by rfl) ⟨2853989, by rfl⟩ : syracuseStep 3805319 = 5707979) B5707979
theorem B790683 : Blo 790340 790683 := bstep (se 1 (by rfl) ⟨593012, by rfl⟩ : syracuseStep 790683 = 1186025) B1186025
theorem B2003231 : Blo 790340 2003231 := bstep (se 1 (by rfl) ⟨1502423, by rfl⟩ : syracuseStep 2003231 = 3004847) B3004847
theorem B3805471 : Blo 790340 3805471 := bstep (se 1 (by rfl) ⟨2854103, by rfl⟩ : syracuseStep 3805471 = 5708207) B5708207
theorem B790887 : Blo 790340 790887 := bstep (se 1 (by rfl) ⟨593165, by rfl⟩ : syracuseStep 790887 = 1186331) B1186331
theorem B790939 : Blo 790340 790939 := bstep (se 1 (by rfl) ⟨593204, by rfl⟩ : syracuseStep 790939 = 1186409) B1186409
theorem B7606865 : Blo 790340 7606865 := bstep (se 2 (by rfl) ⟨2852574, by rfl⟩ : syracuseStep 7606865 = 5705149) B5705149
theorem B51483347 : Blo 790340 51483347 := bstep (se 1 (by rfl) ⟨38612510, by rfl⟩ : syracuseStep 51483347 = 77225021) B77225021
theorem B791291 : Blo 790340 791291 := bstep (se 1 (by rfl) ⟨593468, by rfl⟩ : syracuseStep 791291 = 1186937) B1186937
theorem B889663 : Blo 790340 889663 := bstep (se 1 (by rfl) ⟨667247, by rfl⟩ : syracuseStep 889663 = 1334495) B1334495
theorem B791359 : Blo 790340 791359 := bstep (se 1 (by rfl) ⟨593519, by rfl⟩ : syracuseStep 791359 = 1187039) B1187039
theorem B791387 : Blo 790340 791387 := bstep (se 1 (by rfl) ⟨593540, by rfl⟩ : syracuseStep 791387 = 1187081) B1187081
theorem B791455 : Blo 790340 791455 := bstep (se 1 (by rfl) ⟨593591, by rfl⟩ : syracuseStep 791455 = 1187183) B1187183
theorem B791535 : Blo 790340 791535 := bstep (se 1 (by rfl) ⟨593651, by rfl⟩ : syracuseStep 791535 = 1187303) B1187303
theorem B791623 : Blo 790340 791623 := bstep (se 1 (by rfl) ⟨593717, by rfl⟩ : syracuseStep 791623 = 1187435) B1187435
theorem B889951 : Blo 790340 889951 := bstep (se 1 (by rfl) ⟨667463, by rfl⟩ : syracuseStep 889951 = 1334927) B1334927
theorem B791707 : Blo 790340 791707 := bstep (se 1 (by rfl) ⟨593780, by rfl⟩ : syracuseStep 791707 = 1187561) B1187561
theorem B791803 : Blo 790340 791803 := bstep (se 1 (by rfl) ⟨593852, by rfl⟩ : syracuseStep 791803 = 1187705) B1187705
theorem B791871 : Blo 790340 791871 := bstep (se 1 (by rfl) ⟨593903, by rfl⟩ : syracuseStep 791871 = 1187807) B1187807
theorem B2004335 : Blo 790340 2004335 := bstep (se 1 (by rfl) ⟨1503251, by rfl⟩ : syracuseStep 2004335 = 3006503) B3006503
theorem B792039 : Blo 790340 792039 := bstep (se 1 (by rfl) ⟨594029, by rfl⟩ : syracuseStep 792039 = 1188059) B1188059
theorem B792047 : Blo 790340 792047 := bstep (se 1 (by rfl) ⟨594035, by rfl⟩ : syracuseStep 792047 = 1188071) B1188071
theorem B792155 : Blo 790340 792155 := bstep (se 1 (by rfl) ⟨594116, by rfl⟩ : syracuseStep 792155 = 1188233) B1188233
theorem B792219 : Blo 790340 792219 := bstep (se 1 (by rfl) ⟨594164, by rfl⟩ : syracuseStep 792219 = 1188329) B1188329
theorem B792303 : Blo 790340 792303 := bstep (se 1 (by rfl) ⟨594227, by rfl⟩ : syracuseStep 792303 = 1188455) B1188455
theorem B792391 : Blo 790340 792391 := bstep (se 1 (by rfl) ⟨594293, by rfl⟩ : syracuseStep 792391 = 1188587) B1188587
theorem B4003667 : Blo 790340 4003667 := bstep (se 1 (by rfl) ⟨3002750, by rfl⟩ : syracuseStep 4003667 = 6005501) B6005501
theorem B792411 : Blo 790340 792411 := bstep (se 1 (by rfl) ⟨594308, by rfl⟩ : syracuseStep 792411 = 1188617) B1188617
theorem B1185659 : Blo 790340 1185659 := bstep (se 1 (by rfl) ⟨889244, by rfl⟩ : syracuseStep 1185659 = 1778489) B1778489
theorem B1185695 : Blo 790340 1185695 := bstep (se 1 (by rfl) ⟨889271, by rfl⟩ : syracuseStep 1185695 = 1778543) B1778543
theorem B792479 : Blo 790340 792479 := bstep (se 1 (by rfl) ⟨594359, by rfl⟩ : syracuseStep 792479 = 1188719) B1188719
theorem B3381239 : Blo 790340 3381239 := bstep (se 1 (by rfl) ⟨2535929, by rfl⟩ : syracuseStep 3381239 = 5071859) B5071859
theorem B2004983 : Blo 790340 2004983 := bstep (se 1 (by rfl) ⟨1503737, by rfl⟩ : syracuseStep 2004983 = 3007475) B3007475
theorem B792647 : Blo 790340 792647 := bstep (se 1 (by rfl) ⟨594485, by rfl⟩ : syracuseStep 792647 = 1188971) B1188971
theorem B1185929 : Blo 790340 1185929 := bstep (se 2 (by rfl) ⟨444723, by rfl⟩ : syracuseStep 1185929 = 889447) B889447
theorem B792807 : Blo 790340 792807 := bstep (se 1 (by rfl) ⟨594605, by rfl⟩ : syracuseStep 792807 = 1189211) B1189211
theorem B1186079 : Blo 790340 1186079 := bstep (se 1 (by rfl) ⟨889559, by rfl⟩ : syracuseStep 1186079 = 1779119) B1779119
theorem B3381547 : Blo 790340 3381547 := bstep (se 1 (by rfl) ⟨2536160, by rfl⟩ : syracuseStep 3381547 = 5072321) B5072321
theorem B1808723 : Blo 790340 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B9017729 : Blo 790340 9017729 := bstep (se 2 (by rfl) ⟨3381648, by rfl⟩ : syracuseStep 9017729 = 6763297) B6763297
theorem B792991 : Blo 790340 792991 := bstep (se 1 (by rfl) ⟨594743, by rfl⟩ : syracuseStep 792991 = 1189487) B1189487
theorem B793039 : Blo 790340 793039 := bstep (se 1 (by rfl) ⟨594779, by rfl⟩ : syracuseStep 793039 = 1189559) B1189559
theorem B793063 : Blo 790340 793063 := bstep (se 1 (by rfl) ⟨594797, by rfl⟩ : syracuseStep 793063 = 1189595) B1189595
theorem B793179 : Blo 790340 793179 := bstep (se 1 (by rfl) ⟨594884, by rfl⟩ : syracuseStep 793179 = 1189769) B1189769
theorem B793247 : Blo 790340 793247 := bstep (se 1 (by rfl) ⟨594935, by rfl⟩ : syracuseStep 793247 = 1189871) B1189871
theorem B10132235 : Blo 790340 10132235 := bstep (se 1 (by rfl) ⟨7599176, by rfl⟩ : syracuseStep 10132235 = 15198353) B15198353
theorem B1186631 : Blo 790340 1186631 := bstep (se 1 (by rfl) ⟨889973, by rfl⟩ : syracuseStep 1186631 = 1779947) B1779947
theorem B793415 : Blo 790340 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B793455 : Blo 790340 793455 := bstep (se 1 (by rfl) ⟨595091, by rfl⟩ : syracuseStep 793455 = 1190183) B1190183
theorem B793511 : Blo 790340 793511 := bstep (se 1 (by rfl) ⟨595133, by rfl⟩ : syracuseStep 793511 = 1190267) B1190267
theorem B4004801 : Blo 790340 4004801 := bstep (se 2 (by rfl) ⟨1501800, by rfl⟩ : syracuseStep 4004801 = 3003601) B3003601
theorem B793691 : Blo 790340 793691 := bstep (se 1 (by rfl) ⟨595268, by rfl⟩ : syracuseStep 793691 = 1190537) B1190537
theorem B892111 : Blo 790340 892111 := bstep (se 1 (by rfl) ⟨669083, by rfl⟩ : syracuseStep 892111 = 1338167) B1338167
theorem B793807 : Blo 790340 793807 := bstep (se 1 (by rfl) ⟨595355, by rfl⟩ : syracuseStep 793807 = 1190711) B1190711
theorem B5086415 : Blo 790340 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B793831 : Blo 790340 793831 := bstep (se 1 (by rfl) ⟨595373, by rfl⟩ : syracuseStep 793831 = 1190747) B1190747
theorem B793927 : Blo 790340 793927 := bstep (se 1 (by rfl) ⟨595445, by rfl⟩ : syracuseStep 793927 = 1190891) B1190891
theorem B2137519 : Blo 790340 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B794063 : Blo 790340 794063 := bstep (se 1 (by rfl) ⟨595547, by rfl⟩ : syracuseStep 794063 = 1191095) B1191095
theorem B88219205 : Blo 790340 88219205 := bstep (se 4 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 88219205 = 16541101) B16541101
theorem B794223 : Blo 790340 794223 := bstep (se 1 (by rfl) ⟨595667, by rfl⟩ : syracuseStep 794223 = 1191335) B1191335
theorem B1187495 : Blo 790340 1187495 := bstep (se 1 (by rfl) ⟨890621, by rfl⟩ : syracuseStep 1187495 = 1781243) B1781243
theorem B794279 : Blo 790340 794279 := bstep (se 1 (by rfl) ⟨595709, by rfl⟩ : syracuseStep 794279 = 1191419) B1191419
theorem B1187615 : Blo 790340 1187615 := bstep (se 1 (by rfl) ⟨890711, by rfl⟩ : syracuseStep 1187615 = 1781423) B1781423
theorem B893119 : Blo 790340 893119 := bstep (se 1 (by rfl) ⟨669839, by rfl⟩ : syracuseStep 893119 = 1339679) B1339679
theorem B1188047 : Blo 790340 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B1188095 : Blo 790340 1188095 := bstep (se 1 (by rfl) ⟨891071, by rfl⟩ : syracuseStep 1188095 = 1782143) B1782143
theorem B1712441 : Blo 790340 1712441 := bstep (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) B1284331
theorem B36610379 : Blo 790340 36610379 := bstep (se 1 (by rfl) ⟨27457784, by rfl⟩ : syracuseStep 36610379 = 54915569) B54915569
theorem B10166633 : Blo 790340 10166633 := bstep (se 2 (by rfl) ⟨3812487, by rfl⟩ : syracuseStep 10166633 = 7624975) B7624975
theorem B3809875 : Blo 790340 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B893551 : Blo 790340 893551 := bstep (se 1 (by rfl) ⟨670163, by rfl⟩ : syracuseStep 893551 = 1340327) B1340327
theorem B6759197 : Blo 790340 6759197 := bstep (se 3 (by rfl) ⟨1267349, by rfl⟩ : syracuseStep 6759197 = 2534699) B2534699
theorem B3220435 : Blo 790340 3220435 := bstep (se 1 (by rfl) ⟨2415326, by rfl⟩ : syracuseStep 3220435 = 4830653) B4830653
theorem B1188911 : Blo 790340 1188911 := bstep (se 1 (by rfl) ⟨891683, by rfl⟩ : syracuseStep 1188911 = 1783367) B1783367
theorem B2008111 : Blo 790340 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B1189031 : Blo 790340 1189031 := bstep (se 1 (by rfl) ⟨891773, by rfl⟩ : syracuseStep 1189031 = 1783547) B1783547
theorem B1779191 : Blo 790340 1779191 := bstep (se 1 (by rfl) ⟨1334393, by rfl⟩ : syracuseStep 1779191 = 2668787) B2668787
theorem B1779227 : Blo 790340 1779227 := bstep (se 1 (by rfl) ⟨1334420, by rfl⟩ : syracuseStep 1779227 = 2668841) B2668841
theorem B1189403 : Blo 790340 1189403 := bstep (se 1 (by rfl) ⟨892052, by rfl⟩ : syracuseStep 1189403 = 1784105) B1784105
theorem B2008759 : Blo 790340 2008759 := bstep (se 1 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 2008759 = 3013139) B3013139
theorem B7415639 : Blo 790340 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B1189787 : Blo 790340 1189787 := bstep (se 1 (by rfl) ⟨892340, by rfl⟩ : syracuseStep 1189787 = 1784681) B1784681
theorem B1189823 : Blo 790340 1189823 := bstep (se 1 (by rfl) ⟨892367, by rfl⟩ : syracuseStep 1189823 = 1784735) B1784735
theorem B4008041 : Blo 790340 4008041 := bstep (se 2 (by rfl) ⟨1503015, by rfl⟩ : syracuseStep 4008041 = 3006031) B3006031
theorem B1190009 : Blo 790340 1190009 := bstep (se 2 (by rfl) ⟨446253, by rfl⟩ : syracuseStep 1190009 = 892507) B892507
theorem B10856713 : Blo 790340 10856713 := bstep (se 2 (by rfl) ⟨4071267, by rfl⟩ : syracuseStep 10856713 = 8142535) B8142535
theorem B1780217 : Blo 790340 1780217 := bstep (se 2 (by rfl) ⟨667581, by rfl⟩ : syracuseStep 1780217 = 1335163) B1335163
theorem B1190393 : Blo 790340 1190393 := bstep (se 2 (by rfl) ⟨446397, by rfl⟩ : syracuseStep 1190393 = 892795) B892795
theorem B1780271 : Blo 790340 1780271 := bstep (se 1 (by rfl) ⟨1335203, by rfl⟩ : syracuseStep 1780271 = 2670407) B2670407
theorem B1190447 : Blo 790340 1190447 := bstep (se 1 (by rfl) ⟨892835, by rfl⟩ : syracuseStep 1190447 = 1785671) B1785671
theorem B1780307 : Blo 790340 1780307 := bstep (se 1 (by rfl) ⟨1335230, by rfl⟩ : syracuseStep 1780307 = 2670461) B2670461
theorem B13511285 : Blo 790340 13511285 := bstep (se 5 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 13511285 = 1266683) B1266683
theorem B2534111 : Blo 790340 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B1780487 : Blo 790340 1780487 := bstep (se 1 (by rfl) ⟨1335365, by rfl⟩ : syracuseStep 1780487 = 2670731) B2670731
theorem B1125343 : Blo 790340 1125343 := bstep (se 1 (by rfl) ⟨844007, by rfl⟩ : syracuseStep 1125343 = 1688015) B1688015
theorem B1780703 : Blo 790340 1780703 := bstep (se 1 (by rfl) ⟨1335527, by rfl⟩ : syracuseStep 1780703 = 2671055) B2671055
theorem B1190879 : Blo 790340 1190879 := bstep (se 1 (by rfl) ⟨893159, by rfl⟩ : syracuseStep 1190879 = 1786319) B1786319
theorem B6007931 : Blo 790340 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B1780919 : Blo 790340 1780919 := bstep (se 1 (by rfl) ⟨1335689, by rfl⟩ : syracuseStep 1780919 = 2671379) B2671379
theorem B1355063 : Blo 790340 1355063 := bstep (se 1 (by rfl) ⟨1016297, by rfl⟩ : syracuseStep 1355063 = 2032595) B2032595
theorem B1191323 : Blo 790340 1191323 := bstep (se 1 (by rfl) ⟨893492, by rfl⟩ : syracuseStep 1191323 = 1786985) B1786985
theorem B12201479 : Blo 790340 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B1781495 : Blo 790340 1781495 := bstep (se 1 (by rfl) ⟨1336121, by rfl⟩ : syracuseStep 1781495 = 2672243) B2672243
theorem B11448125 : Blo 790340 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B1781567 : Blo 790340 1781567 := bstep (se 1 (by rfl) ⟨1336175, by rfl⟩ : syracuseStep 1781567 = 2672351) B2672351
theorem B32550761 : Blo 790340 32550761 := bstep (se 2 (by rfl) ⟨12206535, by rfl⟩ : syracuseStep 32550761 = 24413071) B24413071
theorem B7221163 : Blo 790340 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B1781675 : Blo 790340 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B1782035 : Blo 790340 1782035 := bstep (se 1 (by rfl) ⟨1336526, by rfl⟩ : syracuseStep 1782035 = 2673053) B2673053
theorem B1782215 : Blo 790340 1782215 := bstep (se 1 (by rfl) ⟨1336661, by rfl⟩ : syracuseStep 1782215 = 2673323) B2673323
theorem B5714495 : Blo 790340 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B1782575 : Blo 790340 1782575 := bstep (se 1 (by rfl) ⟨1336931, by rfl⟩ : syracuseStep 1782575 = 2673863) B2673863
theorem B1782665 : Blo 790340 1782665 := bstep (se 2 (by rfl) ⟨668499, by rfl⟩ : syracuseStep 1782665 = 1336999) B1336999
theorem B3814505 : Blo 790340 3814505 := bstep (se 2 (by rfl) ⟨1430439, by rfl⟩ : syracuseStep 3814505 = 2860879) B2860879
theorem B1783439 : Blo 790340 1783439 := bstep (se 1 (by rfl) ⟨1337579, by rfl⟩ : syracuseStep 1783439 = 2675159) B2675159
theorem B2668193 : Blo 790340 2668193 := bstep (se 2 (by rfl) ⟨1000572, by rfl⟩ : syracuseStep 2668193 = 2001145) B2001145
theorem B1783529 : Blo 790340 1783529 := bstep (se 2 (by rfl) ⟨668823, by rfl⟩ : syracuseStep 1783529 = 1337647) B1337647
theorem B4011767 : Blo 790340 4011767 := bstep (se 1 (by rfl) ⟨3008825, by rfl⟩ : syracuseStep 4011767 = 6017651) B6017651
theorem B30390551 : Blo 790340 30390551 := bstep (se 1 (by rfl) ⟨22792913, by rfl⟩ : syracuseStep 30390551 = 45585827) B45585827
theorem B6109607 : Blo 790340 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1784411 : Blo 790340 1784411 := bstep (se 1 (by rfl) ⟨1338308, by rfl⟩ : syracuseStep 1784411 = 2676617) B2676617
theorem B1784555 : Blo 790340 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B2669543 : Blo 790340 2669543 := bstep (se 1 (by rfl) ⟨2002157, by rfl⟩ : syracuseStep 2669543 = 4004315) B4004315
theorem B3390569 : Blo 790340 3390569 := bstep (se 2 (by rfl) ⟨1271463, by rfl⟩ : syracuseStep 3390569 = 2542927) B2542927
theorem B1424609 : Blo 790340 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B9649439 : Blo 790340 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B1785167 : Blo 790340 1785167 := bstep (se 1 (by rfl) ⟨1338875, by rfl⟩ : syracuseStep 1785167 = 2677751) B2677751
theorem B41270627 : Blo 790340 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B1785257 : Blo 790340 1785257 := bstep (se 2 (by rfl) ⟨669471, by rfl⟩ : syracuseStep 1785257 = 1338943) B1338943
theorem B1785455 : Blo 790340 1785455 := bstep (se 1 (by rfl) ⟨1339091, by rfl⟩ : syracuseStep 1785455 = 2678183) B2678183
theorem B1785743 : Blo 790340 1785743 := bstep (se 1 (by rfl) ⟨1339307, by rfl⟩ : syracuseStep 1785743 = 2678615) B2678615
theorem B4014035 : Blo 790340 4014035 := bstep (se 1 (by rfl) ⟨3010526, by rfl⟩ : syracuseStep 4014035 = 6021053) B6021053
theorem B12829063 : Blo 790340 12829063 := bstep (se 1 (by rfl) ⟨9621797, by rfl⟩ : syracuseStep 12829063 = 19243595) B19243595
theorem B3391901 : Blo 790340 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B1786283 : Blo 790340 1786283 := bstep (se 1 (by rfl) ⟨1339712, by rfl⟩ : syracuseStep 1786283 = 2679425) B2679425
theorem B1688159 : Blo 790340 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B1786463 : Blo 790340 1786463 := bstep (se 1 (by rfl) ⟨1339847, by rfl⟩ : syracuseStep 1786463 = 2679695) B2679695
theorem B6013763 : Blo 790340 6013763 := bstep (se 1 (by rfl) ⟨4510322, by rfl⟩ : syracuseStep 6013763 = 9020645) B9020645
theorem B1688519 : Blo 790340 1688519 := bstep (se 1 (by rfl) ⟨1266389, by rfl⟩ : syracuseStep 1688519 = 2532779) B2532779
theorem B1786823 : Blo 790340 1786823 := bstep (se 1 (by rfl) ⟨1340117, by rfl⟩ : syracuseStep 1786823 = 2680235) B2680235
theorem B2671649 : Blo 790340 2671649 := bstep (se 2 (by rfl) ⟨1001868, by rfl⟩ : syracuseStep 2671649 = 2003737) B2003737
theorem B902191 : Blo 790340 902191 := bstep (se 1 (by rfl) ⟨676643, by rfl⟩ : syracuseStep 902191 = 1353287) B1353287
theorem B13550651 : Blo 790340 13550651 := bstep (se 1 (by rfl) ⟨10162988, by rfl⟩ : syracuseStep 13550651 = 20325977) B20325977
theorem B2409707 : Blo 790340 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B1787183 : Blo 790340 1787183 := bstep (se 1 (by rfl) ⟨1340387, by rfl⟩ : syracuseStep 1787183 = 2680775) B2680775
theorem B1525279 : Blo 790340 1525279 := bstep (se 1 (by rfl) ⟨1143959, by rfl⟩ : syracuseStep 1525279 = 2287919) B2287919
theorem B3262073 : Blo 790340 3262073 := bstep (se 2 (by rfl) ⟨1223277, by rfl⟩ : syracuseStep 3262073 = 2446555) B2446555
theorem B10307897 : Blo 790340 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B4508297 : Blo 790340 4508297 := bstep (se 2 (by rfl) ⟨1690611, by rfl⟩ : syracuseStep 4508297 = 3381223) B3381223
theorem B6507155 : Blo 790340 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B4016951 : Blo 790340 4016951 := bstep (se 1 (by rfl) ⟨3012713, by rfl⟩ : syracuseStep 4016951 = 6025427) B6025427
theorem B2673917 : Blo 790340 2673917 := bstep (se 3 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 2673917 = 1002719) B1002719
theorem B6508307 : Blo 790340 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B2674457 : Blo 790340 2674457 := bstep (se 2 (by rfl) ⟨1002921, by rfl⟩ : syracuseStep 2674457 = 2005843) B2005843
theorem B2674727 : Blo 790340 2674727 := bstep (se 1 (by rfl) ⟨2006045, by rfl⟩ : syracuseStep 2674727 = 4012091) B4012091
theorem B1691867 : Blo 790340 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B1266043 : Blo 790340 1266043 := bstep (se 1 (by rfl) ⟨949532, by rfl⟩ : syracuseStep 1266043 = 1899065) B1899065
theorem B2675699 : Blo 790340 2675699 := bstep (se 1 (by rfl) ⟨2006774, by rfl⟩ : syracuseStep 2675699 = 4013549) B4013549
theorem B2675807 : Blo 790340 2675807 := bstep (se 1 (by rfl) ⟨2006855, by rfl⟩ : syracuseStep 2675807 = 4013711) B4013711
theorem B6411419 : Blo 790340 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B12539225 : Blo 790340 12539225 := bstep (se 2 (by rfl) ⟨4702209, by rfl⟩ : syracuseStep 12539225 = 9404419) B9404419
theorem B2676239 : Blo 790340 2676239 := bstep (se 1 (by rfl) ⟨2007179, by rfl⟩ : syracuseStep 2676239 = 4014359) B4014359
theorem B123655987 : Blo 790340 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B3004559 : Blo 790340 3004559 := bstep (se 1 (by rfl) ⟨2253419, by rfl⟩ : syracuseStep 3004559 = 4506839) B4506839
theorem B4511963 : Blo 790340 4511963 := bstep (se 1 (by rfl) ⟨3383972, by rfl⟩ : syracuseStep 4511963 = 6767945) B6767945
theorem B22829363 : Blo 790340 22829363 := bstep (se 1 (by rfl) ⟨17122022, by rfl⟩ : syracuseStep 22829363 = 34244045) B34244045
theorem B2677049 : Blo 790340 2677049 := bstep (se 2 (by rfl) ⟨1003893, by rfl⟩ : syracuseStep 2677049 = 2007787) B2007787
theorem B2677319 : Blo 790340 2677319 := bstep (se 1 (by rfl) ⟨2007989, by rfl⟩ : syracuseStep 2677319 = 4015979) B4015979
theorem B2251631 : Blo 790340 2251631 := bstep (se 1 (by rfl) ⟨1688723, by rfl⟩ : syracuseStep 2251631 = 3377447) B3377447
theorem B5791621 : Blo 790340 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B2253055 : Blo 790340 2253055 := bstep (se 1 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 2253055 = 3379583) B3379583
theorem B21684509 : Blo 790340 21684509 := bstep (se 3 (by rfl) ⟨4065845, by rfl⟩ : syracuseStep 21684509 = 8131691) B8131691
theorem B3007003 : Blo 790340 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B7725617 : Blo 790340 7725617 := bstep (se 2 (by rfl) ⟨2897106, by rfl⟩ : syracuseStep 7725617 = 5794213) B5794213
theorem B844507 : Blo 790340 844507 := bstep (se 1 (by rfl) ⟨633380, by rfl⟩ : syracuseStep 844507 = 1266761) B1266761
theorem B1336027 : Blo 790340 1336027 := bstep (se 1 (by rfl) ⟨1002020, by rfl⟩ : syracuseStep 1336027 = 2004041) B2004041
theorem B7628165 : Blo 790340 7628165 := bstep (se 4 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 7628165 = 1430281) B1430281
theorem B7628701 : Blo 790340 7628701 := bstep (se 3 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 7628701 = 2860763) B2860763
theorem B3008447 : Blo 790340 3008447 := bstep (se 1 (by rfl) ⟨2256335, by rfl⟩ : syracuseStep 3008447 = 4512671) B4512671
theorem B1501163 : Blo 790340 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B1337323 : Blo 790340 1337323 := bstep (se 1 (by rfl) ⟨1002992, by rfl⟩ : syracuseStep 1337323 = 2005985) B2005985
theorem B1271855 : Blo 790340 1271855 := bstep (se 1 (by rfl) ⟨953891, by rfl⟩ : syracuseStep 1271855 = 1907783) B1907783
theorem B1337465 : Blo 790340 1337465 := bstep (se 2 (by rfl) ⟨501549, by rfl⟩ : syracuseStep 1337465 = 1003099) B1003099
theorem B69298361 : Blo 790340 69298361 := bstep (se 2 (by rfl) ⟨25986885, by rfl⟩ : syracuseStep 69298361 = 51973771) B51973771
theorem B3009419 : Blo 790340 3009419 := bstep (se 1 (by rfl) ⟨2257064, by rfl⟩ : syracuseStep 3009419 = 4514129) B4514129
theorem B3010223 : Blo 790340 3010223 := bstep (se 1 (by rfl) ⟨2257667, by rfl⟩ : syracuseStep 3010223 = 4515335) B4515335
theorem B3010391 : Blo 790340 3010391 := bstep (se 1 (by rfl) ⟨2257793, by rfl⟩ : syracuseStep 3010391 = 4515587) B4515587
theorem B17624965 : Blo 790340 17624965 := bstep (se 4 (by rfl) ⟨1652340, by rfl⟩ : syracuseStep 17624965 = 3304681) B3304681
theorem B158232527 : Blo 790340 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B22835357 : Blo 790340 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B1339625 : Blo 790340 1339625 := bstep (se 2 (by rfl) ⟨502359, by rfl⟩ : syracuseStep 1339625 = 1004719) B1004719
theorem B3208663 : Blo 790340 3208663 := bstep (se 1 (by rfl) ⟨2406497, by rfl⟩ : syracuseStep 3208663 = 4812995) B4812995
theorem B3438443 : Blo 790340 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B2258887 : Blo 790340 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B4519961 : Blo 790340 4519961 := bstep (se 2 (by rfl) ⟨1694985, by rfl⟩ : syracuseStep 4519961 = 3389971) B3389971
theorem B21690665 : Blo 790340 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B6027709 : Blo 790340 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B2849231 : Blo 790340 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B1604137 : Blo 790340 1604137 := bstep (se 2 (by rfl) ⟨601551, by rfl⟩ : syracuseStep 1604137 = 1203103) B1203103
theorem B2292353 : Blo 790340 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B2850299 : Blo 790340 2850299 := bstep (se 1 (by rfl) ⟨2137724, by rfl⟩ : syracuseStep 2850299 = 4275449) B4275449
theorem B3800819 : Blo 790340 3800819 := bstep (se 1 (by rfl) ⟨2850614, by rfl⟩ : syracuseStep 3800819 = 5701229) B5701229
theorem B3866377 : Blo 790340 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B4521851 : Blo 790340 4521851 := bstep (se 1 (by rfl) ⟨3391388, by rfl⟩ : syracuseStep 4521851 = 6782777) B6782777
theorem B3014779 : Blo 790340 3014779 := bstep (se 1 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 3014779 = 4522169) B4522169
theorem B5079293 : Blo 790340 5079293 := bstep (se 3 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 5079293 = 1904735) B1904735
theorem B2261267 : Blo 790340 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B6029801 : Blo 790340 6029801 := bstep (se 2 (by rfl) ⟨2261175, by rfl⟩ : syracuseStep 6029801 = 4522351) B4522351
theorem B17105417 : Blo 790340 17105417 := bstep (se 2 (by rfl) ⟨6414531, by rfl⟩ : syracuseStep 17105417 = 12829063) B12829063
theorem B15205117 : Blo 790340 15205117 := bstep (se 3 (by rfl) ⟨2850959, by rfl⟩ : syracuseStep 15205117 = 5701919) B5701919
theorem B5079833 : Blo 790340 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B4293913 : Blo 790340 4293913 := bstep (se 2 (by rfl) ⟨1610217, by rfl⟩ : syracuseStep 4293913 = 3220435) B3220435
theorem B2033705 : Blo 790340 2033705 := bstep (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) B1525279
theorem B6425885 : Blo 790340 6425885 := bstep (se 3 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 6425885 = 2409707) B2409707
theorem B790439 : Blo 790340 790439 := bstep (se 1 (by rfl) ⟨592829, by rfl⟩ : syracuseStep 790439 = 1185659) B1185659
theorem B790463 : Blo 790340 790463 := bstep (se 1 (by rfl) ⟨592847, by rfl⟩ : syracuseStep 790463 = 1185695) B1185695
theorem B790619 : Blo 790340 790619 := bstep (se 1 (by rfl) ⟨592964, by rfl⟩ : syracuseStep 790619 = 1185929) B1185929
theorem B2003039 : Blo 790340 2003039 := bstep (se 1 (by rfl) ⟨1502279, by rfl⟩ : syracuseStep 2003039 = 3004559) B3004559
theorem B790719 : Blo 790340 790719 := bstep (se 1 (by rfl) ⟨593039, by rfl⟩ : syracuseStep 790719 = 1186079) B1186079
theorem B6754823 : Blo 790340 6754823 := bstep (se 1 (by rfl) ⟨5066117, by rfl⟩ : syracuseStep 6754823 = 10132235) B10132235
theorem B791087 : Blo 790340 791087 := bstep (se 1 (by rfl) ⟨593315, by rfl⟩ : syracuseStep 791087 = 1186631) B1186631
theorem B791663 : Blo 790340 791663 := bstep (se 1 (by rfl) ⟨593747, by rfl⟩ : syracuseStep 791663 = 1187495) B1187495
theorem B23499953 : Blo 790340 23499953 := bstep (se 2 (by rfl) ⟨8812482, by rfl⟩ : syracuseStep 23499953 = 17624965) B17624965
theorem B791743 : Blo 790340 791743 := bstep (se 1 (by rfl) ⟨593807, by rfl⟩ : syracuseStep 791743 = 1187615) B1187615
theorem B792031 : Blo 790340 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B792063 : Blo 790340 792063 := bstep (se 1 (by rfl) ⟨594047, by rfl⟩ : syracuseStep 792063 = 1188095) B1188095
theorem B14456339 : Blo 790340 14456339 := bstep (se 1 (by rfl) ⟨10842254, by rfl⟩ : syracuseStep 14456339 = 21684509) B21684509
theorem B5150411 : Blo 790340 5150411 := bstep (se 1 (by rfl) ⟨3862808, by rfl⟩ : syracuseStep 5150411 = 7725617) B7725617
theorem B792607 : Blo 790340 792607 := bstep (se 1 (by rfl) ⟨594455, by rfl⟩ : syracuseStep 792607 = 1188911) B1188911
theorem B792687 : Blo 790340 792687 := bstep (se 1 (by rfl) ⟨594515, by rfl⟩ : syracuseStep 792687 = 1189031) B1189031
theorem B5085443 : Blo 790340 5085443 := bstep (se 1 (by rfl) ⟨3814082, by rfl⟩ : syracuseStep 5085443 = 7628165) B7628165
theorem B1186127 : Blo 790340 1186127 := bstep (se 1 (by rfl) ⟨889595, by rfl⟩ : syracuseStep 1186127 = 1779191) B1779191
theorem B1186151 : Blo 790340 1186151 := bstep (se 1 (by rfl) ⟨889613, by rfl⟩ : syracuseStep 1186151 = 1779227) B1779227
theorem B792935 : Blo 790340 792935 := bstep (se 1 (by rfl) ⟨594701, by rfl⟩ : syracuseStep 792935 = 1189403) B1189403
theorem B1186217 : Blo 790340 1186217 := bstep (se 2 (by rfl) ⟨444831, by rfl⟩ : syracuseStep 1186217 = 889663) B889663
theorem B16292285 : Blo 790340 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B793191 : Blo 790340 793191 := bstep (se 1 (by rfl) ⟨594893, by rfl⟩ : syracuseStep 793191 = 1189787) B1189787
theorem B2005631 : Blo 790340 2005631 := bstep (se 1 (by rfl) ⟨1504223, by rfl⟩ : syracuseStep 2005631 = 3008447) B3008447
theorem B793215 : Blo 790340 793215 := bstep (se 1 (by rfl) ⟨594911, by rfl⟩ : syracuseStep 793215 = 1189823) B1189823
theorem B891643 : Blo 790340 891643 := bstep (se 1 (by rfl) ⟨668732, by rfl⟩ : syracuseStep 891643 = 1337465) B1337465
theorem B793339 : Blo 790340 793339 := bstep (se 1 (by rfl) ⟨595004, by rfl⟩ : syracuseStep 793339 = 1190009) B1190009
theorem B1186601 : Blo 790340 1186601 := bstep (se 2 (by rfl) ⟨444975, by rfl⟩ : syracuseStep 1186601 = 889951) B889951
theorem B1186811 : Blo 790340 1186811 := bstep (se 1 (by rfl) ⟨890108, by rfl⟩ : syracuseStep 1186811 = 1780217) B1780217
theorem B793595 : Blo 790340 793595 := bstep (se 1 (by rfl) ⟨595196, by rfl⟩ : syracuseStep 793595 = 1190393) B1190393
theorem B1186847 : Blo 790340 1186847 := bstep (se 1 (by rfl) ⟨890135, by rfl⟩ : syracuseStep 1186847 = 1780271) B1780271
theorem B793631 : Blo 790340 793631 := bstep (se 1 (by rfl) ⟨595223, by rfl⟩ : syracuseStep 793631 = 1190447) B1190447
theorem B1186871 : Blo 790340 1186871 := bstep (se 1 (by rfl) ⟨890153, by rfl⟩ : syracuseStep 1186871 = 1780307) B1780307
theorem B1186991 : Blo 790340 1186991 := bstep (se 1 (by rfl) ⟨890243, by rfl⟩ : syracuseStep 1186991 = 1780487) B1780487
theorem B2006279 : Blo 790340 2006279 := bstep (se 1 (by rfl) ⟨1504709, by rfl⟩ : syracuseStep 2006279 = 3009419) B3009419
theorem B1187135 : Blo 790340 1187135 := bstep (se 1 (by rfl) ⟨890351, by rfl⟩ : syracuseStep 1187135 = 1780703) B1780703
theorem B793919 : Blo 790340 793919 := bstep (se 1 (by rfl) ⟨595439, by rfl⟩ : syracuseStep 793919 = 1190879) B1190879
theorem B4005287 : Blo 790340 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B1187279 : Blo 790340 1187279 := bstep (se 1 (by rfl) ⟨890459, by rfl⟩ : syracuseStep 1187279 = 1780919) B1780919
theorem B794215 : Blo 790340 794215 := bstep (se 1 (by rfl) ⟨595661, by rfl⟩ : syracuseStep 794215 = 1191323) B1191323
theorem B8134319 : Blo 790340 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B2006815 : Blo 790340 2006815 := bstep (se 1 (by rfl) ⟨1505111, by rfl⟩ : syracuseStep 2006815 = 3010223) B3010223
theorem B1187663 : Blo 790340 1187663 := bstep (se 1 (by rfl) ⟨890747, by rfl⟩ : syracuseStep 1187663 = 1781495) B1781495
theorem B1187711 : Blo 790340 1187711 := bstep (se 1 (by rfl) ⟨890783, by rfl⟩ : syracuseStep 1187711 = 1781567) B1781567
theorem B2006927 : Blo 790340 2006927 := bstep (se 1 (by rfl) ⟨1505195, by rfl⟩ : syracuseStep 2006927 = 3010391) B3010391
theorem B1187783 : Blo 790340 1187783 := bstep (se 1 (by rfl) ⟨890837, by rfl⟩ : syracuseStep 1187783 = 1781675) B1781675
theorem B105488351 : Blo 790340 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B893083 : Blo 790340 893083 := bstep (se 1 (by rfl) ⟨669812, by rfl⟩ : syracuseStep 893083 = 1339625) B1339625
theorem B1188023 : Blo 790340 1188023 := bstep (se 1 (by rfl) ⟨891017, by rfl⟩ : syracuseStep 1188023 = 1782035) B1782035
theorem B1188143 : Blo 790340 1188143 := bstep (se 1 (by rfl) ⟨891107, by rfl⟩ : syracuseStep 1188143 = 1782215) B1782215
theorem B3809663 : Blo 790340 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B1188383 : Blo 790340 1188383 := bstep (se 1 (by rfl) ⟨891287, by rfl⟩ : syracuseStep 1188383 = 1782575) B1782575
theorem B8036945 : Blo 790340 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B1188443 : Blo 790340 1188443 := bstep (se 1 (by rfl) ⟨891332, by rfl⟩ : syracuseStep 1188443 = 1782665) B1782665
theorem B2138849 : Blo 790340 2138849 := bstep (se 2 (by rfl) ⟨802068, by rfl⟩ : syracuseStep 2138849 = 1604137) B1604137
theorem B3613501 : Blo 790340 3613501 := bstep (se 3 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 3613501 = 1355063) B1355063
theorem B1188959 : Blo 790340 1188959 := bstep (se 1 (by rfl) ⟨891719, by rfl⟩ : syracuseStep 1188959 = 1783439) B1783439
theorem B1778795 : Blo 790340 1778795 := bstep (se 1 (by rfl) ⟨1334096, by rfl⟩ : syracuseStep 1778795 = 2668193) B2668193
theorem B1189019 : Blo 790340 1189019 := bstep (se 1 (by rfl) ⟨891764, by rfl⟩ : syracuseStep 1189019 = 1783529) B1783529
theorem B20260367 : Blo 790340 20260367 := bstep (se 1 (by rfl) ⟨15195275, by rfl⟩ : syracuseStep 20260367 = 30390551) B30390551
theorem B14460443 : Blo 790340 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B1189481 : Blo 790340 1189481 := bstep (se 2 (by rfl) ⟨446055, by rfl⟩ : syracuseStep 1189481 = 892111) B892111
theorem B1189607 : Blo 790340 1189607 := bstep (se 1 (by rfl) ⟨892205, by rfl⟩ : syracuseStep 1189607 = 1784411) B1784411
theorem B1189703 : Blo 790340 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B1779695 : Blo 790340 1779695 := bstep (se 1 (by rfl) ⟨1334771, by rfl⟩ : syracuseStep 1779695 = 2669543) B2669543
theorem B6432959 : Blo 790340 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B1190111 : Blo 790340 1190111 := bstep (se 1 (by rfl) ⟨892583, by rfl⟩ : syracuseStep 1190111 = 1785167) B1785167
theorem B1190171 : Blo 790340 1190171 := bstep (se 1 (by rfl) ⟨892628, by rfl⟩ : syracuseStep 1190171 = 1785257) B1785257
theorem B5155169 : Blo 790340 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B1190303 : Blo 790340 1190303 := bstep (se 1 (by rfl) ⟨892727, by rfl⟩ : syracuseStep 1190303 = 1785455) B1785455
theorem B2533879 : Blo 790340 2533879 := bstep (se 1 (by rfl) ⟨1900409, by rfl⟩ : syracuseStep 2533879 = 3800819) B3800819
theorem B1190495 : Blo 790340 1190495 := bstep (se 1 (by rfl) ⟨892871, by rfl⟩ : syracuseStep 1190495 = 1785743) B1785743
theorem B1190825 : Blo 790340 1190825 := bstep (se 2 (by rfl) ⟨446559, by rfl⟩ : syracuseStep 1190825 = 893119) B893119
theorem B1190855 : Blo 790340 1190855 := bstep (se 1 (by rfl) ⟨893141, by rfl⟩ : syracuseStep 1190855 = 1786283) B1786283
theorem B2010055 : Blo 790340 2010055 := bstep (se 1 (by rfl) ⟨1507541, by rfl⟩ : syracuseStep 2010055 = 3015083) B3015083
theorem B1190975 : Blo 790340 1190975 := bstep (se 1 (by rfl) ⟨893231, by rfl⟩ : syracuseStep 1190975 = 1786463) B1786463
theorem B4009175 : Blo 790340 4009175 := bstep (se 1 (by rfl) ⟨3006881, by rfl⟩ : syracuseStep 4009175 = 6013763) B6013763
theorem B1125679 : Blo 790340 1125679 := bstep (se 1 (by rfl) ⟨844259, by rfl⟩ : syracuseStep 1125679 = 1688519) B1688519
theorem B1191215 : Blo 790340 1191215 := bstep (se 1 (by rfl) ⟨893411, by rfl⟩ : syracuseStep 1191215 = 1786823) B1786823
theorem B1781099 : Blo 790340 1781099 := bstep (se 1 (by rfl) ⟨1335824, by rfl⟩ : syracuseStep 1781099 = 2671649) B2671649
theorem B4009337 : Blo 790340 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B1191401 : Blo 790340 1191401 := bstep (se 2 (by rfl) ⟨446775, by rfl⟩ : syracuseStep 1191401 = 893551) B893551
theorem B1191455 : Blo 790340 1191455 := bstep (se 1 (by rfl) ⟨893591, by rfl⟩ : syracuseStep 1191455 = 1787183) B1787183
theorem B1126009 : Blo 790340 1126009 := bstep (se 2 (by rfl) ⟨422253, by rfl⟩ : syracuseStep 1126009 = 844507) B844507
theorem B1781369 : Blo 790340 1781369 := bstep (se 2 (by rfl) ⟨668013, by rfl⟩ : syracuseStep 1781369 = 1336027) B1336027
theorem B4501757 : Blo 790340 4501757 := bstep (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) B1688159
theorem B4338103 : Blo 790340 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B19575593 : Blo 790340 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B1782611 : Blo 790340 1782611 := bstep (se 1 (by rfl) ⟨1336958, by rfl⟩ : syracuseStep 1782611 = 2673917) B2673917
theorem B1782971 : Blo 790340 1782971 := bstep (se 1 (by rfl) ⟨1337228, by rfl⟩ : syracuseStep 1782971 = 2674457) B2674457
theorem B10171601 : Blo 790340 10171601 := bstep (se 2 (by rfl) ⟨3814350, by rfl⟩ : syracuseStep 10171601 = 7628701) B7628701
theorem B1783097 : Blo 790340 1783097 := bstep (se 2 (by rfl) ⟨668661, by rfl⟩ : syracuseStep 1783097 = 1337323) B1337323
theorem B1783151 : Blo 790340 1783151 := bstep (se 1 (by rfl) ⟨1337363, by rfl⟩ : syracuseStep 1783151 = 2674727) B2674727
theorem B2536879 : Blo 790340 2536879 := bstep (se 1 (by rfl) ⟨1902659, by rfl⟩ : syracuseStep 2536879 = 3805319) B3805319
theorem B34322231 : Blo 790340 34322231 := bstep (se 1 (by rfl) ⟨25741673, by rfl⟩ : syracuseStep 34322231 = 51483347) B51483347
theorem B1783799 : Blo 790340 1783799 := bstep (se 1 (by rfl) ⟨1337849, by rfl⟩ : syracuseStep 1783799 = 2675699) B2675699
theorem B1783871 : Blo 790340 1783871 := bstep (se 1 (by rfl) ⟨1337903, by rfl⟩ : syracuseStep 1783871 = 2675807) B2675807
theorem B4274279 : Blo 790340 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B33437933 : Blo 790340 33437933 := bstep (se 3 (by rfl) ⟨6269612, by rfl⟩ : syracuseStep 33437933 = 12539225) B12539225
theorem B1784159 : Blo 790340 1784159 := bstep (se 1 (by rfl) ⟨1338119, by rfl⟩ : syracuseStep 1784159 = 2676239) B2676239
theorem B2669111 : Blo 790340 2669111 := bstep (se 1 (by rfl) ⟨2001833, by rfl⟩ : syracuseStep 2669111 = 4003667) B4003667
theorem B15219575 : Blo 790340 15219575 := bstep (se 1 (by rfl) ⟨11414681, by rfl⟩ : syracuseStep 15219575 = 22829363) B22829363
theorem B1784699 : Blo 790340 1784699 := bstep (se 1 (by rfl) ⟨1338524, by rfl⟩ : syracuseStep 1784699 = 2677049) B2677049
theorem B6011819 : Blo 790340 6011819 := bstep (se 1 (by rfl) ⟨4508864, by rfl⟩ : syracuseStep 6011819 = 9017729) B9017729
theorem B8698861 : Blo 790340 8698861 := bstep (se 3 (by rfl) ⟨1631036, by rfl⟩ : syracuseStep 8698861 = 3262073) B3262073
theorem B1784879 : Blo 790340 1784879 := bstep (se 1 (by rfl) ⟨1338659, by rfl⟩ : syracuseStep 1784879 = 2677319) B2677319
theorem B2669867 : Blo 790340 2669867 := bstep (se 1 (by rfl) ⟨2002400, by rfl⟩ : syracuseStep 2669867 = 4004801) B4004801
theorem B2670569 : Blo 790340 2670569 := bstep (se 2 (by rfl) ⟨1001463, by rfl⟩ : syracuseStep 2670569 = 2002927) B2002927
theorem B1688057 : Blo 790340 1688057 := bstep (se 2 (by rfl) ⟨633021, by rfl⟩ : syracuseStep 1688057 = 1266043) B1266043
theorem B4506131 : Blo 790340 4506131 := bstep (se 1 (by rfl) ⟨3379598, by rfl⟩ : syracuseStep 4506131 = 6759197) B6759197
theorem B1000775 : Blo 790340 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B2672027 : Blo 790340 2672027 := bstep (se 1 (by rfl) ⟨2004020, by rfl⟩ : syracuseStep 2672027 = 4008041) B4008041
theorem B1689407 : Blo 790340 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B4278217 : Blo 790340 4278217 := bstep (se 2 (by rfl) ⟨1604331, by rfl⟩ : syracuseStep 4278217 = 3208663) B3208663
theorem B164874649 : Blo 790340 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B15223571 : Blo 790340 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B4508729 : Blo 790340 4508729 := bstep (se 2 (by rfl) ⟨1690773, by rfl⟩ : syracuseStep 4508729 = 3381547) B3381547
theorem B2543003 : Blo 790340 2543003 := bstep (se 1 (by rfl) ⟨1907252, by rfl⟩ : syracuseStep 2543003 = 3814505) B3814505
theorem B2674511 : Blo 790340 2674511 := bstep (se 1 (by rfl) ⟨2005883, by rfl⟩ : syracuseStep 2674511 = 4011767) B4011767
theorem B1528235 : Blo 790340 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B17355485 : Blo 790340 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B27513751 : Blo 790340 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B7722161 : Blo 790340 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B2676023 : Blo 790340 2676023 := bstep (se 1 (by rfl) ⟨2007017, by rfl⟩ : syracuseStep 2676023 = 4014035) B4014035
theorem B3004073 : Blo 790340 3004073 := bstep (se 2 (by rfl) ⟨1126527, by rfl⟩ : syracuseStep 3004073 = 2253055) B2253055
theorem B4511645 : Blo 790340 4511645 := bstep (se 3 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 4511645 = 1691867) B1691867
theorem B9033767 : Blo 790340 9033767 := bstep (se 1 (by rfl) ⟨6775325, by rfl⟩ : syracuseStep 9033767 = 13550651) B13550651
theorem B2677481 : Blo 790340 2677481 := bstep (se 2 (by rfl) ⟨1004055, by rfl⟩ : syracuseStep 2677481 = 2008111) B2008111
theorem B1202921 : Blo 790340 1202921 := bstep (se 2 (by rfl) ⟨451095, by rfl⟩ : syracuseStep 1202921 = 902191) B902191
theorem B6871931 : Blo 790340 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B3005531 : Blo 790340 3005531 := bstep (se 1 (by rfl) ⟨2254148, by rfl⟩ : syracuseStep 3005531 = 4508297) B4508297
theorem B2677967 : Blo 790340 2677967 := bstep (se 1 (by rfl) ⟨2008475, by rfl⟩ : syracuseStep 2677967 = 4016951) B4016951
theorem B2678345 : Blo 790340 2678345 := bstep (se 2 (by rfl) ⟨1004379, by rfl⟩ : syracuseStep 2678345 = 2008759) B2008759
theorem B1335487 : Blo 790340 1335487 := bstep (se 1 (by rfl) ⟨1001615, by rfl⟩ : syracuseStep 1335487 = 2003231) B2003231
theorem B14475617 : Blo 790340 14475617 := bstep (se 2 (by rfl) ⟨5428356, by rfl⟩ : syracuseStep 14475617 = 10856713) B10856713
theorem B5071243 : Blo 790340 5071243 := bstep (se 1 (by rfl) ⟨3803432, by rfl⟩ : syracuseStep 5071243 = 7606865) B7606865
theorem B1336223 : Blo 790340 1336223 := bstep (se 1 (by rfl) ⟨1002167, by rfl⟩ : syracuseStep 1336223 = 2004335) B2004335
theorem B1500457 : Blo 790340 1500457 := bstep (se 2 (by rfl) ⟨562671, by rfl⟩ : syracuseStep 1500457 = 1125343) B1125343
theorem B2254159 : Blo 790340 2254159 := bstep (se 1 (by rfl) ⟨1690619, by rfl⟩ : syracuseStep 2254159 = 3381239) B3381239
theorem B1336655 : Blo 790340 1336655 := bstep (se 1 (by rfl) ⟨1002491, by rfl⟩ : syracuseStep 1336655 = 2004983) B2004983
theorem B3007975 : Blo 790340 3007975 := bstep (se 1 (by rfl) ⟨2255981, by rfl⟩ : syracuseStep 3007975 = 4511963) B4511963
theorem B1205815 : Blo 790340 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B1501087 : Blo 790340 1501087 := bstep (se 1 (by rfl) ⟨1125815, by rfl⟩ : syracuseStep 1501087 = 2251631) B2251631
theorem B58812803 : Blo 790340 58812803 := bstep (se 1 (by rfl) ⟨44109602, by rfl⟩ : syracuseStep 58812803 = 88219205) B88219205
theorem B9628217 : Blo 790340 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B1141627 : Blo 790340 1141627 := bstep (se 1 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 1141627 = 1712441) B1712441
theorem B24406919 : Blo 790340 24406919 := bstep (se 1 (by rfl) ⟨18305189, by rfl⟩ : syracuseStep 24406919 = 36610379) B36610379
theorem B6777755 : Blo 790340 6777755 := bstep (se 1 (by rfl) ⟨5083316, by rfl⟩ : syracuseStep 6777755 = 10166633) B10166633
theorem B5073961 : Blo 790340 5073961 := bstep (se 2 (by rfl) ⟨1902735, by rfl⟩ : syracuseStep 5073961 = 3805471) B3805471
theorem B22899941 : Blo 790340 22899941 := bstep (se 4 (by rfl) ⟨2146869, by rfl⟩ : syracuseStep 22899941 = 4293739) B4293739
theorem B4943759 : Blo 790340 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B847903 : Blo 790340 847903 := bstep (se 1 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 847903 = 1271855) B1271855
theorem B46198907 : Blo 790340 46198907 := bstep (se 1 (by rfl) ⟨34649180, by rfl⟩ : syracuseStep 46198907 = 69298361) B69298361
theorem B9007523 : Blo 790340 9007523 := bstep (se 1 (by rfl) ⟨6755642, by rfl⟩ : syracuseStep 9007523 = 13511285) B13511285
theorem B11400101 : Blo 790340 11400101 := bstep (se 4 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 11400101 = 2137519) B2137519
theorem B7632083 : Blo 790340 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B3011849 : Blo 790340 3011849 := bstep (se 2 (by rfl) ⟨1129443, by rfl⟩ : syracuseStep 3011849 = 2258887) B2258887
theorem B13563773 : Blo 790340 13563773 := bstep (se 3 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 13563773 = 5086415) B5086415
theorem B2292295 : Blo 790340 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B3013307 : Blo 790340 3013307 := bstep (se 1 (by rfl) ⟨2259980, by rfl⟩ : syracuseStep 3013307 = 4519961) B4519961
theorem B1899487 : Blo 790340 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B2260379 : Blo 790340 2260379 := bstep (se 1 (by rfl) ⟨1695284, by rfl⟩ : syracuseStep 2260379 = 3390569) B3390569
theorem B949739 : Blo 790340 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B86802029 : Blo 790340 86802029 := bstep (se 3 (by rfl) ⟨16275380, by rfl⟩ : syracuseStep 86802029 = 32550761) B32550761
theorem B1900199 : Blo 790340 1900199 := bstep (se 1 (by rfl) ⟨1425149, by rfl⟩ : syracuseStep 1900199 = 2850299) B2850299
theorem B3014567 : Blo 790340 3014567 := bstep (se 1 (by rfl) ⟨2260925, by rfl⟩ : syracuseStep 3014567 = 4521851) B4521851
theorem B1507511 : Blo 790340 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B11403611 : Blo 790340 11403611 := bstep (se 1 (by rfl) ⟨8552708, by rfl⟩ : syracuseStep 11403611 = 17105417) B17105417
theorem B2000609 : Blo 790340 2000609 := bstep (se 2 (by rfl) ⟨750228, by rfl⟩ : syracuseStep 2000609 = 1500457) B1500457
theorem B1607753 : Blo 790340 1607753 := bstep (se 2 (by rfl) ⟨602907, by rfl⟩ : syracuseStep 1607753 = 1205815) B1205815
theorem B2001449 : Blo 790340 2001449 := bstep (se 2 (by rfl) ⟨750543, by rfl⟩ : syracuseStep 2001449 = 1501087) B1501087
theorem B5704289 : Blo 790340 5704289 := bstep (se 2 (by rfl) ⟨2139108, by rfl⟩ : syracuseStep 5704289 = 4278217) B4278217
theorem B1018823 : Blo 790340 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B11570323 : Blo 790340 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B20352221 : Blo 790340 20352221 := bstep (se 3 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 20352221 = 7632083) B7632083
theorem B3378505 : Blo 790340 3378505 := bstep (se 2 (by rfl) ⟨1266939, by rfl⟩ : syracuseStep 3378505 = 2533879) B2533879
theorem B5148107 : Blo 790340 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B15666635 : Blo 790340 15666635 := bstep (se 1 (by rfl) ⟨11749976, by rfl⟩ : syracuseStep 15666635 = 23499953) B23499953
theorem B9637559 : Blo 790340 9637559 := bstep (se 1 (by rfl) ⟨7228169, by rfl⟩ : syracuseStep 9637559 = 14456339) B14456339
theorem B2002715 : Blo 790340 2002715 := bstep (se 1 (by rfl) ⟨1502036, by rfl⟩ : syracuseStep 2002715 = 3004073) B3004073
theorem B790751 : Blo 790340 790751 := bstep (se 1 (by rfl) ⟨593063, by rfl⟩ : syracuseStep 790751 = 1186127) B1186127
theorem B790767 : Blo 790340 790767 := bstep (se 1 (by rfl) ⟨593075, by rfl⟩ : syracuseStep 790767 = 1186151) B1186151
theorem B790811 : Blo 790340 790811 := bstep (se 1 (by rfl) ⟨593108, by rfl⟩ : syracuseStep 790811 = 1186217) B1186217
theorem B19272005 : Blo 790340 19272005 := bstep (se 4 (by rfl) ⟨1806750, by rfl⟩ : syracuseStep 19272005 = 3613501) B3613501
theorem B791067 : Blo 790340 791067 := bstep (se 1 (by rfl) ⟨593300, by rfl⟩ : syracuseStep 791067 = 1186601) B1186601
theorem B791207 : Blo 790340 791207 := bstep (se 1 (by rfl) ⟨593405, by rfl⟩ : syracuseStep 791207 = 1186811) B1186811
theorem B791231 : Blo 790340 791231 := bstep (se 1 (by rfl) ⟨593423, by rfl⟩ : syracuseStep 791231 = 1186847) B1186847
theorem B791247 : Blo 790340 791247 := bstep (se 1 (by rfl) ⟨593435, by rfl⟩ : syracuseStep 791247 = 1186871) B1186871
theorem B2003687 : Blo 790340 2003687 := bstep (se 1 (by rfl) ⟨1502765, by rfl⟩ : syracuseStep 2003687 = 3005531) B3005531
theorem B791327 : Blo 790340 791327 := bstep (se 1 (by rfl) ⟨593495, by rfl⟩ : syracuseStep 791327 = 1186991) B1186991
theorem B791423 : Blo 790340 791423 := bstep (se 1 (by rfl) ⟨593567, by rfl⟩ : syracuseStep 791423 = 1187135) B1187135
theorem B791519 : Blo 790340 791519 := bstep (se 1 (by rfl) ⟨593639, by rfl⟩ : syracuseStep 791519 = 1187279) B1187279
theorem B791775 : Blo 790340 791775 := bstep (se 1 (by rfl) ⟨593831, by rfl⟩ : syracuseStep 791775 = 1187663) B1187663
theorem B791807 : Blo 790340 791807 := bstep (se 1 (by rfl) ⟨593855, by rfl⟩ : syracuseStep 791807 = 1187711) B1187711
theorem B791855 : Blo 790340 791855 := bstep (se 1 (by rfl) ⟨593891, by rfl⟩ : syracuseStep 791855 = 1187783) B1187783
theorem B70325567 : Blo 790340 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B792015 : Blo 790340 792015 := bstep (se 1 (by rfl) ⟨594011, by rfl⟩ : syracuseStep 792015 = 1188023) B1188023
theorem B792095 : Blo 790340 792095 := bstep (se 1 (by rfl) ⟨594071, by rfl⟩ : syracuseStep 792095 = 1188143) B1188143
theorem B792255 : Blo 790340 792255 := bstep (se 1 (by rfl) ⟨594191, by rfl⟩ : syracuseStep 792255 = 1188383) B1188383
theorem B792295 : Blo 790340 792295 := bstep (se 1 (by rfl) ⟨594221, by rfl⟩ : syracuseStep 792295 = 1188443) B1188443
theorem B890815 : Blo 790340 890815 := bstep (se 1 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 890815 = 1336223) B1336223
theorem B792639 : Blo 790340 792639 := bstep (se 1 (by rfl) ⟨594479, by rfl⟩ : syracuseStep 792639 = 1188959) B1188959
theorem B1185863 : Blo 790340 1185863 := bstep (se 1 (by rfl) ⟨889397, by rfl⟩ : syracuseStep 1185863 = 1778795) B1778795
theorem B792679 : Blo 790340 792679 := bstep (se 1 (by rfl) ⟨594509, by rfl⟩ : syracuseStep 792679 = 1189019) B1189019
theorem B891103 : Blo 790340 891103 := bstep (se 1 (by rfl) ⟨668327, by rfl⟩ : syracuseStep 891103 = 1336655) B1336655
theorem B13506911 : Blo 790340 13506911 := bstep (se 1 (by rfl) ⟨10130183, by rfl⟩ : syracuseStep 13506911 = 20260367) B20260367
theorem B9640295 : Blo 790340 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B792987 : Blo 790340 792987 := bstep (se 1 (by rfl) ⟨594740, by rfl⟩ : syracuseStep 792987 = 1189481) B1189481
theorem B793071 : Blo 790340 793071 := bstep (se 1 (by rfl) ⟨594803, by rfl⟩ : syracuseStep 793071 = 1189607) B1189607
theorem B793135 : Blo 790340 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B1186463 : Blo 790340 1186463 := bstep (se 1 (by rfl) ⟨889847, by rfl⟩ : syracuseStep 1186463 = 1779695) B1779695
theorem B793407 : Blo 790340 793407 := bstep (se 1 (by rfl) ⟨595055, by rfl⟩ : syracuseStep 793407 = 1190111) B1190111
theorem B793447 : Blo 790340 793447 := bstep (se 1 (by rfl) ⟨595085, by rfl⟩ : syracuseStep 793447 = 1190171) B1190171
theorem B793535 : Blo 790340 793535 := bstep (se 1 (by rfl) ⟨595151, by rfl⟩ : syracuseStep 793535 = 1190303) B1190303
theorem B793663 : Blo 790340 793663 := bstep (se 1 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 793663 = 1190495) B1190495
theorem B3382505 : Blo 790340 3382505 := bstep (se 2 (by rfl) ⟨1268439, by rfl⟩ : syracuseStep 3382505 = 2536879) B2536879
theorem B793883 : Blo 790340 793883 := bstep (se 1 (by rfl) ⟨595412, by rfl⟩ : syracuseStep 793883 = 1190825) B1190825
theorem B793903 : Blo 790340 793903 := bstep (se 1 (by rfl) ⟨595427, by rfl⟩ : syracuseStep 793903 = 1190855) B1190855
theorem B793983 : Blo 790340 793983 := bstep (se 1 (by rfl) ⟨595487, by rfl⟩ : syracuseStep 793983 = 1190975) B1190975
theorem B794143 : Blo 790340 794143 := bstep (se 1 (by rfl) ⟨595607, by rfl⟩ : syracuseStep 794143 = 1191215) B1191215
theorem B1187399 : Blo 790340 1187399 := bstep (se 1 (by rfl) ⟨890549, by rfl⟩ : syracuseStep 1187399 = 1781099) B1781099
theorem B794267 : Blo 790340 794267 := bstep (se 1 (by rfl) ⟨595700, by rfl⟩ : syracuseStep 794267 = 1191401) B1191401
theorem B794303 : Blo 790340 794303 := bstep (se 1 (by rfl) ⟨595727, by rfl⟩ : syracuseStep 794303 = 1191455) B1191455
theorem B1187579 : Blo 790340 1187579 := bstep (se 1 (by rfl) ⟨890684, by rfl⟩ : syracuseStep 1187579 = 1781369) B1781369
theorem B6005015 : Blo 790340 6005015 := bstep (se 1 (by rfl) ⟨4503761, by rfl⟩ : syracuseStep 6005015 = 9007523) B9007523
theorem B13050395 : Blo 790340 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B1188407 : Blo 790340 1188407 := bstep (se 1 (by rfl) ⟨891305, by rfl⟩ : syracuseStep 1188407 = 1782611) B1782611
theorem B3056393 : Blo 790340 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B1188647 : Blo 790340 1188647 := bstep (se 1 (by rfl) ⟨891485, by rfl⟩ : syracuseStep 1188647 = 1782971) B1782971
theorem B2007899 : Blo 790340 2007899 := bstep (se 1 (by rfl) ⟨1505924, by rfl⟩ : syracuseStep 2007899 = 3011849) B3011849
theorem B1188731 : Blo 790340 1188731 := bstep (se 1 (by rfl) ⟨891548, by rfl⟩ : syracuseStep 1188731 = 1783097) B1783097
theorem B1188767 : Blo 790340 1188767 := bstep (se 1 (by rfl) ⟨891575, by rfl⟩ : syracuseStep 1188767 = 1783151) B1783151
theorem B1188857 : Blo 790340 1188857 := bstep (se 2 (by rfl) ⟨445821, by rfl⟩ : syracuseStep 1188857 = 891643) B891643
theorem B22881487 : Blo 790340 22881487 := bstep (se 1 (by rfl) ⟨17161115, by rfl⟩ : syracuseStep 22881487 = 34322231) B34322231
theorem B2532637 : Blo 790340 2532637 := bstep (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) B949739
theorem B2532649 : Blo 790340 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1189199 : Blo 790340 1189199 := bstep (se 1 (by rfl) ⟨891899, by rfl⟩ : syracuseStep 1189199 = 1783799) B1783799
theorem B1189247 : Blo 790340 1189247 := bstep (se 1 (by rfl) ⟨891935, by rfl⟩ : syracuseStep 1189247 = 1783871) B1783871
theorem B22291955 : Blo 790340 22291955 := bstep (se 1 (by rfl) ⟨16718966, by rfl⟩ : syracuseStep 22291955 = 33437933) B33437933
theorem B1189439 : Blo 790340 1189439 := bstep (se 1 (by rfl) ⟨892079, by rfl⟩ : syracuseStep 1189439 = 1784159) B1784159
theorem B1779407 : Blo 790340 1779407 := bstep (se 1 (by rfl) ⟨1334555, by rfl⟩ : syracuseStep 1779407 = 2669111) B2669111
theorem B2008871 : Blo 790340 2008871 := bstep (se 1 (by rfl) ⟨1506653, by rfl⟩ : syracuseStep 2008871 = 3013307) B3013307
theorem B1189799 : Blo 790340 1189799 := bstep (se 1 (by rfl) ⟨892349, by rfl⟩ : syracuseStep 1189799 = 1784699) B1784699
theorem B4007879 : Blo 790340 4007879 := bstep (se 1 (by rfl) ⟨3005909, by rfl⟩ : syracuseStep 4007879 = 6011819) B6011819
theorem B1189919 : Blo 790340 1189919 := bstep (se 1 (by rfl) ⟨892439, by rfl⟩ : syracuseStep 1189919 = 1784879) B1784879
theorem B1779911 : Blo 790340 1779911 := bstep (se 1 (by rfl) ⟨1334933, by rfl⟩ : syracuseStep 1779911 = 2669867) B2669867
theorem B13183357 : Blo 790340 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B2009711 : Blo 790340 2009711 := bstep (se 1 (by rfl) ⟨1507283, by rfl⟩ : syracuseStep 2009711 = 3014567) B3014567
theorem B1780379 : Blo 790340 1780379 := bstep (se 1 (by rfl) ⟨1335284, by rfl⟩ : syracuseStep 1780379 = 2670569) B2670569
theorem B3386195 : Blo 790340 3386195 := bstep (se 1 (by rfl) ⟨2539646, by rfl⟩ : syracuseStep 3386195 = 5079293) B5079293
theorem B1190777 : Blo 790340 1190777 := bstep (se 2 (by rfl) ⟨446541, by rfl⟩ : syracuseStep 1190777 = 893083) B893083
theorem B1780649 : Blo 790340 1780649 := bstep (se 2 (by rfl) ⟨667743, by rfl⟩ : syracuseStep 1780649 = 1335487) B1335487
theorem B1125371 : Blo 790340 1125371 := bstep (se 1 (by rfl) ⟨844028, by rfl⟩ : syracuseStep 1125371 = 1688057) B1688057
theorem B6761657 : Blo 790340 6761657 := bstep (se 2 (by rfl) ⟨2535621, by rfl⟩ : syracuseStep 6761657 = 5071243) B5071243
theorem B3386555 : Blo 790340 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B1781351 : Blo 790340 1781351 := bstep (se 1 (by rfl) ⟨1336013, by rfl⟩ : syracuseStep 1781351 = 2672027) B2672027
theorem B1126271 : Blo 790340 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B4010633 : Blo 790340 4010633 := bstep (se 2 (by rfl) ⟨1503987, by rfl⟩ : syracuseStep 4010633 = 3007975) B3007975
theorem B1783007 : Blo 790340 1783007 := bstep (se 1 (by rfl) ⟨1337255, by rfl⟩ : syracuseStep 1783007 = 2674511) B2674511
theorem B4503215 : Blo 790340 4503215 := bstep (se 1 (by rfl) ⟨3377411, by rfl⟩ : syracuseStep 4503215 = 6754823) B6754823
theorem B2668733 : Blo 790340 2668733 := bstep (se 3 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 2668733 = 1000775) B1000775
theorem B1784015 : Blo 790340 1784015 := bstep (se 1 (by rfl) ⟨1338011, by rfl⟩ : syracuseStep 1784015 = 2676023) B2676023
theorem B1522169 : Blo 790340 1522169 := bstep (se 2 (by rfl) ⟨570813, by rfl⟩ : syracuseStep 1522169 = 1141627) B1141627
theorem B6765281 : Blo 790340 6765281 := bstep (se 2 (by rfl) ⟨2536980, by rfl⟩ : syracuseStep 6765281 = 5073961) B5073961
theorem B3390295 : Blo 790340 3390295 := bstep (se 1 (by rfl) ⟨2542721, by rfl⟩ : syracuseStep 3390295 = 5085443) B5085443
theorem B10861523 : Blo 790340 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B801947 : Blo 790340 801947 := bstep (se 1 (by rfl) ⟨601460, by rfl⟩ : syracuseStep 801947 = 1202921) B1202921
theorem B1784987 : Blo 790340 1784987 := bstep (se 1 (by rfl) ⟨1338740, by rfl⟩ : syracuseStep 1784987 = 2677481) B2677481
theorem B1785311 : Blo 790340 1785311 := bstep (se 1 (by rfl) ⟨1338983, by rfl⟩ : syracuseStep 1785311 = 2677967) B2677967
theorem B2670191 : Blo 790340 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B1785563 : Blo 790340 1785563 := bstep (se 1 (by rfl) ⟨1339172, by rfl⟩ : syracuseStep 1785563 = 2678345) B2678345
theorem B5422879 : Blo 790340 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B1130537 : Blo 790340 1130537 := bstep (se 2 (by rfl) ⟨423951, by rfl⟩ : syracuseStep 1130537 = 847903) B847903
theorem B5423213 : Blo 790340 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B9650411 : Blo 790340 9650411 := bstep (se 1 (by rfl) ⟨7237808, by rfl⟩ : syracuseStep 9650411 = 14475617) B14475617
theorem B2539775 : Blo 790340 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B5357963 : Blo 790340 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B1425899 : Blo 790340 1425899 := bstep (se 1 (by rfl) ⟨1069424, by rfl⟩ : syracuseStep 1425899 = 2138849) B2138849
theorem B5784137 : Blo 790340 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B13747117 : Blo 790340 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B36685001 : Blo 790340 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B39208535 : Blo 790340 39208535 := bstep (se 1 (by rfl) ⟨29406401, by rfl⟩ : syracuseStep 39208535 = 58812803) B58812803
theorem B16271279 : Blo 790340 16271279 := bstep (se 1 (by rfl) ⟨12203459, by rfl⟩ : syracuseStep 16271279 = 24406919) B24406919
theorem B2672783 : Blo 790340 2672783 := bstep (se 1 (by rfl) ⟨2004587, by rfl⟩ : syracuseStep 2672783 = 4009175) B4009175
theorem B2672891 : Blo 790340 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B3001171 : Blo 790340 3001171 := bstep (se 1 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 3001171 = 4501757) B4501757
theorem B5067197 : Blo 790340 5067197 := bstep (se 3 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 5067197 = 1900199) B1900199
theorem B10146383 : Blo 790340 10146383 := bstep (se 1 (by rfl) ⟨7609787, by rfl⟩ : syracuseStep 10146383 = 15219575) B15219575
theorem B2675753 : Blo 790340 2675753 := bstep (se 2 (by rfl) ⟨1003407, by rfl⟩ : syracuseStep 2675753 = 2006815) B2006815
theorem B4019705 : Blo 790340 4019705 := bstep (se 2 (by rfl) ⟨1507389, by rfl⟩ : syracuseStep 4019705 = 3014779) B3014779
theorem B4019867 : Blo 790340 4019867 := bstep (se 1 (by rfl) ⟨3014900, by rfl⟩ : syracuseStep 4019867 = 6029801) B6029801
theorem B3004087 : Blo 790340 3004087 := bstep (se 1 (by rfl) ⟨2253065, by rfl⟩ : syracuseStep 3004087 = 4506131) B4506131
theorem B20273489 : Blo 790340 20273489 := bstep (se 2 (by rfl) ⟨7602558, by rfl⟩ : syracuseStep 20273489 = 15205117) B15205117
theorem B5725217 : Blo 790340 5725217 := bstep (se 2 (by rfl) ⟨2146956, by rfl⟩ : syracuseStep 5725217 = 4293913) B4293913
theorem B3005545 : Blo 790340 3005545 := bstep (se 2 (by rfl) ⟨1127079, by rfl⟩ : syracuseStep 3005545 = 2254159) B2254159
theorem B10149047 : Blo 790340 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B3005819 : Blo 790340 3005819 := bstep (se 1 (by rfl) ⟨2254364, by rfl⟩ : syracuseStep 3005819 = 4508729) B4508729
theorem B4283923 : Blo 790340 4283923 := bstep (se 1 (by rfl) ⟨3212942, by rfl⟩ : syracuseStep 4283923 = 6425885) B6425885
theorem B1695335 : Blo 790340 1695335 := bstep (se 1 (by rfl) ⟨1271501, by rfl⟩ : syracuseStep 1695335 = 2543003) B2543003
theorem B1335359 : Blo 790340 1335359 := bstep (se 1 (by rfl) ⟨1001519, by rfl⟩ : syracuseStep 1335359 = 2003039) B2003039
theorem B219832865 : Blo 790340 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B3433607 : Blo 790340 3433607 := bstep (se 1 (by rfl) ⟨2575205, by rfl⟩ : syracuseStep 3433607 = 5150411) B5150411
theorem B2680073 : Blo 790340 2680073 := bstep (se 2 (by rfl) ⟨1005027, by rfl⟩ : syracuseStep 2680073 = 2010055) B2010055
theorem B3007763 : Blo 790340 3007763 := bstep (se 1 (by rfl) ⟨2255822, by rfl⟩ : syracuseStep 3007763 = 4511645) B4511645
theorem B6022511 : Blo 790340 6022511 := bstep (se 1 (by rfl) ⟨4516883, by rfl⟩ : syracuseStep 6022511 = 9033767) B9033767
theorem B1500905 : Blo 790340 1500905 := bstep (se 2 (by rfl) ⟨562839, by rfl⟩ : syracuseStep 1500905 = 1125679) B1125679
theorem B1337087 : Blo 790340 1337087 := bstep (se 1 (by rfl) ⟨1002815, by rfl⟩ : syracuseStep 1337087 = 2005631) B2005631
theorem B4581287 : Blo 790340 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B1501345 : Blo 790340 1501345 := bstep (se 2 (by rfl) ⟨563004, by rfl⟩ : syracuseStep 1501345 = 1126009) B1126009
theorem B1337519 : Blo 790340 1337519 := bstep (se 1 (by rfl) ⟨1003139, by rfl⟩ : syracuseStep 1337519 = 2006279) B2006279
theorem B1337951 : Blo 790340 1337951 := bstep (se 1 (by rfl) ⟨1003463, by rfl⟩ : syracuseStep 1337951 = 2006927) B2006927
theorem B4288639 : Blo 790340 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B6418811 : Blo 790340 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B4518503 : Blo 790340 4518503 := bstep (se 1 (by rfl) ⟨3388877, by rfl⟩ : syracuseStep 4518503 = 6777755) B6777755
theorem B15266627 : Blo 790340 15266627 := bstep (se 1 (by rfl) ⟨11449970, by rfl⟩ : syracuseStep 15266627 = 22899941) B22899941
theorem B30799271 : Blo 790340 30799271 := bstep (se 1 (by rfl) ⟨23099453, by rfl⟩ : syracuseStep 30799271 = 46198907) B46198907
theorem B7600067 : Blo 790340 7600067 := bstep (se 1 (by rfl) ⟨5700050, by rfl⟩ : syracuseStep 7600067 = 11400101) B11400101
theorem B6781067 : Blo 790340 6781067 := bstep (se 1 (by rfl) ⟨5085800, by rfl⟩ : syracuseStep 6781067 = 10171601) B10171601
theorem B9042515 : Blo 790340 9042515 := bstep (se 1 (by rfl) ⟨6781886, by rfl⟩ : syracuseStep 9042515 = 13563773) B13563773
theorem B11598481 : Blo 790340 11598481 := bstep (se 2 (by rfl) ⟨4349430, by rfl⟩ : syracuseStep 11598481 = 8698861) B8698861
theorem B2849519 : Blo 790340 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B1506919 : Blo 790340 1506919 := bstep (se 1 (by rfl) ⟨1130189, by rfl⟩ : syracuseStep 1506919 = 2260379) B2260379
theorem B57868019 : Blo 790340 57868019 := bstep (se 1 (by rfl) ⟨43401014, by rfl⟩ : syracuseStep 57868019 = 86802029) B86802029
theorem B3014765 : Blo 790340 3014765 := bstep (se 3 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 3014765 = 1130537) B1130537
theorem B7602407 : Blo 790340 7602407 := bstep (se 1 (by rfl) ⟨5701805, by rfl⟩ : syracuseStep 7602407 = 11403611) B11403611
theorem B3571975 : Blo 790340 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B950599 : Blo 790340 950599 := bstep (se 1 (by rfl) ⟨712949, by rfl⟩ : syracuseStep 950599 = 1425899) B1425899
theorem B10847519 : Blo 790340 10847519 := bstep (se 1 (by rfl) ⟨8135639, by rfl⟩ : syracuseStep 10847519 = 16271279) B16271279
theorem B30508649 : Blo 790340 30508649 := bstep (se 2 (by rfl) ⟨11440743, by rfl⟩ : syracuseStep 30508649 = 22881487) B22881487
theorem B3376849 : Blo 790340 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B3376865 : Blo 790340 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B3802859 : Blo 790340 3802859 := bstep (se 1 (by rfl) ⟨2852144, by rfl⟩ : syracuseStep 3802859 = 5704289) B5704289
theorem B13568147 : Blo 790340 13568147 := bstep (se 1 (by rfl) ⟨10176110, by rfl⟩ : syracuseStep 13568147 = 20352221) B20352221
theorem B6425039 : Blo 790340 6425039 := bstep (se 1 (by rfl) ⟨4818779, by rfl⟩ : syracuseStep 6425039 = 9637559) B9637559
theorem B2001793 : Blo 790340 2001793 := bstep (se 2 (by rfl) ⟨750672, by rfl⟩ : syracuseStep 2001793 = 1501345) B1501345
theorem B12848003 : Blo 790340 12848003 := bstep (se 1 (by rfl) ⟨9636002, by rfl⟩ : syracuseStep 12848003 = 19272005) B19272005
theorem B3378131 : Blo 790340 3378131 := bstep (se 1 (by rfl) ⟨2533598, by rfl⟩ : syracuseStep 3378131 = 5067197) B5067197
theorem B4001561 : Blo 790340 4001561 := bstep (se 2 (by rfl) ⟨1500585, by rfl⟩ : syracuseStep 4001561 = 3001171) B3001171
theorem B790575 : Blo 790340 790575 := bstep (se 1 (by rfl) ⟨592931, by rfl⟩ : syracuseStep 790575 = 1185863) B1185863
theorem B6426863 : Blo 790340 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B790975 : Blo 790340 790975 := bstep (se 1 (by rfl) ⟨593231, by rfl⟩ : syracuseStep 790975 = 1186463) B1186463
theorem B2003879 : Blo 790340 2003879 := bstep (se 1 (by rfl) ⟨1502909, by rfl⟩ : syracuseStep 2003879 = 3005819) B3005819
theorem B791599 : Blo 790340 791599 := bstep (se 1 (by rfl) ⟨593699, by rfl⟩ : syracuseStep 791599 = 1187399) B1187399
theorem B791719 : Blo 790340 791719 := bstep (se 1 (by rfl) ⟨593789, by rfl⟩ : syracuseStep 791719 = 1187579) B1187579
theorem B890239 : Blo 790340 890239 := bstep (se 1 (by rfl) ⟨667679, by rfl⟩ : syracuseStep 890239 = 1335359) B1335359
theorem B4003343 : Blo 790340 4003343 := bstep (se 1 (by rfl) ⟨3002507, by rfl⟩ : syracuseStep 4003343 = 6005015) B6005015
theorem B792271 : Blo 790340 792271 := bstep (se 1 (by rfl) ⟨594203, by rfl⟩ : syracuseStep 792271 = 1188407) B1188407
theorem B792431 : Blo 790340 792431 := bstep (se 1 (by rfl) ⟨594323, by rfl⟩ : syracuseStep 792431 = 1188647) B1188647
theorem B792487 : Blo 790340 792487 := bstep (se 1 (by rfl) ⟨594365, by rfl⟩ : syracuseStep 792487 = 1188731) B1188731
theorem B792511 : Blo 790340 792511 := bstep (se 1 (by rfl) ⟨594383, by rfl⟩ : syracuseStep 792511 = 1188767) B1188767
theorem B792571 : Blo 790340 792571 := bstep (se 1 (by rfl) ⟨594428, by rfl⟩ : syracuseStep 792571 = 1188857) B1188857
theorem B2005175 : Blo 790340 2005175 := bstep (se 1 (by rfl) ⟨1503881, by rfl⟩ : syracuseStep 2005175 = 3007763) B3007763
theorem B792799 : Blo 790340 792799 := bstep (se 1 (by rfl) ⟨594599, by rfl⟩ : syracuseStep 792799 = 1189199) B1189199
theorem B792831 : Blo 790340 792831 := bstep (se 1 (by rfl) ⟨594623, by rfl⟩ : syracuseStep 792831 = 1189247) B1189247
theorem B792959 : Blo 790340 792959 := bstep (se 1 (by rfl) ⟨594719, by rfl⟩ : syracuseStep 792959 = 1189439) B1189439
theorem B1186271 : Blo 790340 1186271 := bstep (se 1 (by rfl) ⟨889703, by rfl⟩ : syracuseStep 1186271 = 1779407) B1779407
theorem B891391 : Blo 790340 891391 := bstep (se 1 (by rfl) ⟨668543, by rfl⟩ : syracuseStep 891391 = 1337087) B1337087
theorem B793199 : Blo 790340 793199 := bstep (se 1 (by rfl) ⟨594899, by rfl⟩ : syracuseStep 793199 = 1189799) B1189799
theorem B3054191 : Blo 790340 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B793279 : Blo 790340 793279 := bstep (se 1 (by rfl) ⟨594959, by rfl⟩ : syracuseStep 793279 = 1189919) B1189919
theorem B891679 : Blo 790340 891679 := bstep (se 1 (by rfl) ⟨668759, by rfl⟩ : syracuseStep 891679 = 1337519) B1337519
theorem B1186607 : Blo 790340 1186607 := bstep (se 1 (by rfl) ⟨889955, by rfl⟩ : syracuseStep 1186607 = 1779911) B1779911
theorem B891967 : Blo 790340 891967 := bstep (se 1 (by rfl) ⟨668975, by rfl⟩ : syracuseStep 891967 = 1337951) B1337951
theorem B1186919 : Blo 790340 1186919 := bstep (se 1 (by rfl) ⟨890189, by rfl⟩ : syracuseStep 1186919 = 1780379) B1780379
theorem B793851 : Blo 790340 793851 := bstep (se 1 (by rfl) ⟨595388, by rfl⟩ : syracuseStep 793851 = 1190777) B1190777
theorem B1187099 : Blo 790340 1187099 := bstep (se 1 (by rfl) ⟨890324, by rfl⟩ : syracuseStep 1187099 = 1780649) B1780649
theorem B4005449 : Blo 790340 4005449 := bstep (se 2 (by rfl) ⟨1502043, by rfl⟩ : syracuseStep 4005449 = 3004087) B3004087
theorem B1187567 : Blo 790340 1187567 := bstep (se 1 (by rfl) ⟨890675, by rfl⟩ : syracuseStep 1187567 = 1781351) B1781351
theorem B1187753 : Blo 790340 1187753 := bstep (se 2 (by rfl) ⟨445407, by rfl⟩ : syracuseStep 1187753 = 890815) B890815
theorem B1188137 : Blo 790340 1188137 := bstep (se 2 (by rfl) ⟨445551, by rfl⟩ : syracuseStep 1188137 = 891103) B891103
theorem B2138525 : Blo 790340 2138525 := bstep (se 3 (by rfl) ⟨400973, by rfl⟩ : syracuseStep 2138525 = 801947) B801947
theorem B1188671 : Blo 790340 1188671 := bstep (se 1 (by rfl) ⟨891503, by rfl⟩ : syracuseStep 1188671 = 1783007) B1783007
theorem B1779155 : Blo 790340 1779155 := bstep (se 1 (by rfl) ⟨1334366, by rfl⟩ : syracuseStep 1779155 = 2668733) B2668733
theorem B1189343 : Blo 790340 1189343 := bstep (se 1 (by rfl) ⟨892007, by rfl⟩ : syracuseStep 1189343 = 1784015) B1784015
theorem B4007393 : Blo 790340 4007393 := bstep (se 2 (by rfl) ⟨1502772, by rfl⟩ : syracuseStep 4007393 = 3005545) B3005545
theorem B5711897 : Blo 790340 5711897 := bstep (se 2 (by rfl) ⟨2141961, by rfl⟩ : syracuseStep 5711897 = 4283923) B4283923
theorem B1189991 : Blo 790340 1189991 := bstep (se 1 (by rfl) ⟨892493, by rfl⟩ : syracuseStep 1189991 = 1784987) B1784987
theorem B2009225 : Blo 790340 2009225 := bstep (se 2 (by rfl) ⟨753459, by rfl⟩ : syracuseStep 2009225 = 1506919) B1506919
theorem B1190207 : Blo 790340 1190207 := bstep (se 1 (by rfl) ⟨892655, by rfl⟩ : syracuseStep 1190207 = 1785311) B1785311
theorem B1780127 : Blo 790340 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B1190375 : Blo 790340 1190375 := bstep (se 1 (by rfl) ⟨892781, by rfl⟩ : syracuseStep 1190375 = 1785563) B1785563
theorem B38578679 : Blo 790340 38578679 := bstep (se 1 (by rfl) ⟨28934009, by rfl⟩ : syracuseStep 38578679 = 57868019) B57868019
theorem B6433607 : Blo 790340 6433607 := bstep (se 1 (by rfl) ⟨4825205, by rfl⟩ : syracuseStep 6433607 = 9650411) B9650411
theorem B14461901 : Blo 790340 14461901 := bstep (se 3 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 14461901 = 5423213) B5423213
theorem B24456667 : Blo 790340 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B17116829 : Blo 790340 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B18329489 : Blo 790340 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B1781855 : Blo 790340 1781855 := bstep (se 1 (by rfl) ⟨1336391, by rfl⟩ : syracuseStep 1781855 = 2672783) B2672783
theorem B1781927 : Blo 790340 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B6764255 : Blo 790340 6764255 := bstep (se 1 (by rfl) ⟨5073191, by rfl⟩ : syracuseStep 6764255 = 10146383) B10146383
theorem B17577809 : Blo 790340 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B1783835 : Blo 790340 1783835 := bstep (se 1 (by rfl) ⟨1337876, by rfl⟩ : syracuseStep 1783835 = 2675753) B2675753
theorem B13515659 : Blo 790340 13515659 := bstep (se 1 (by rfl) ⟨10136744, by rfl⟩ : syracuseStep 13515659 = 20273489) B20273489
theorem B4504673 : Blo 790340 4504673 := bstep (se 2 (by rfl) ⟨1689252, by rfl⟩ : syracuseStep 4504673 = 3378505) B3378505
theorem B3816811 : Blo 790340 3816811 := bstep (se 1 (by rfl) ⟨2862608, by rfl⟩ : syracuseStep 3816811 = 5725217) B5725217
theorem B6766031 : Blo 790340 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B5718185 : Blo 790340 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B8700263 : Blo 790340 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B146555243 : Blo 790340 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B1786715 : Blo 790340 1786715 := bstep (se 1 (by rfl) ⟨1340036, by rfl⟩ : syracuseStep 1786715 = 2680073) B2680073
theorem B4015007 : Blo 790340 4015007 := bstep (se 1 (by rfl) ⟨3011255, by rfl⟩ : syracuseStep 4015007 = 6022511) B6022511
theorem B14861303 : Blo 790340 14861303 := bstep (se 1 (by rfl) ⟨11145977, by rfl⟩ : syracuseStep 14861303 = 22291955) B22291955
theorem B1000603 : Blo 790340 1000603 := bstep (se 1 (by rfl) ⟨750452, by rfl⟩ : syracuseStep 1000603 = 1500905) B1500905
theorem B2671919 : Blo 790340 2671919 := bstep (se 1 (by rfl) ⟨2003939, by rfl⟩ : syracuseStep 2671919 = 4007879) B4007879
theorem B4507771 : Blo 790340 4507771 := bstep (se 1 (by rfl) ⟨3380828, by rfl⟩ : syracuseStep 4507771 = 6761657) B6761657
theorem B3000989 : Blo 790340 3000989 := bstep (se 3 (by rfl) ⟨562685, by rfl⟩ : syracuseStep 3000989 = 1125371) B1125371
theorem B2673755 : Blo 790340 2673755 := bstep (se 1 (by rfl) ⟨2005316, by rfl⟩ : syracuseStep 2673755 = 4010633) B4010633
theorem B10177751 : Blo 790340 10177751 := bstep (se 1 (by rfl) ⟨7633313, by rfl⟩ : syracuseStep 10177751 = 15266627) B15266627
theorem B20532847 : Blo 790340 20532847 := bstep (se 1 (by rfl) ⟨15399635, by rfl⟩ : syracuseStep 20532847 = 30799271) B30799271
theorem B3002143 : Blo 790340 3002143 := bstep (se 1 (by rfl) ⟨2251607, by rfl⟩ : syracuseStep 3002143 = 4503215) B4503215
theorem B5066711 : Blo 790340 5066711 := bstep (se 1 (by rfl) ⟨3800033, by rfl⟩ : syracuseStep 5066711 = 7600067) B7600067
theorem B4510187 : Blo 790340 4510187 := bstep (se 1 (by rfl) ⟨3382640, by rfl⟩ : syracuseStep 4510187 = 6765281) B6765281
theorem B10867445 : Blo 790340 10867445 := bstep (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) B1018823
theorem B3003389 : Blo 790340 3003389 := bstep (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) B1126271
theorem B7230505 : Blo 790340 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B1693183 : Blo 790340 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B3856091 : Blo 790340 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B4020029 : Blo 790340 4020029 := bstep (se 3 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 4020029 = 1507511) B1507511
theorem B26139023 : Blo 790340 26139023 := bstep (se 1 (by rfl) ⟨19604267, by rfl⟩ : syracuseStep 26139023 = 39208535) B39208535
theorem B1333739 : Blo 790340 1333739 := bstep (se 1 (by rfl) ⟨1000304, by rfl⟩ : syracuseStep 1333739 = 2000609) B2000609
theorem B1071835 : Blo 790340 1071835 := bstep (se 1 (by rfl) ⟨803876, by rfl⟩ : syracuseStep 1071835 = 1607753) B1607753
theorem B1334299 : Blo 790340 1334299 := bstep (se 1 (by rfl) ⟨1000724, by rfl⟩ : syracuseStep 1334299 = 2001449) B2001449
theorem B8150381 : Blo 790340 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B3432071 : Blo 790340 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B1335143 : Blo 790340 1335143 := bstep (se 1 (by rfl) ⟨1001357, by rfl⟩ : syracuseStep 1335143 = 2002715) B2002715
theorem B1335791 : Blo 790340 1335791 := bstep (se 1 (by rfl) ⟨1001843, by rfl⟩ : syracuseStep 1335791 = 2003687) B2003687
theorem B61858565 : Blo 790340 61858565 := bstep (se 4 (by rfl) ⟨5799240, by rfl⟩ : syracuseStep 61858565 = 11598481) B11598481
theorem B46883711 : Blo 790340 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B2679803 : Blo 790340 2679803 := bstep (se 1 (by rfl) ⟨2009852, by rfl⟩ : syracuseStep 2679803 = 4019705) B4019705
theorem B2679911 : Blo 790340 2679911 := bstep (se 1 (by rfl) ⟨2009933, by rfl⟩ : syracuseStep 2679911 = 4019867) B4019867
theorem B15427097 : Blo 790340 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B9004607 : Blo 790340 9004607 := bstep (se 1 (by rfl) ⟨6753455, by rfl⟩ : syracuseStep 9004607 = 13506911) B13506911
theorem B2255003 : Blo 790340 2255003 := bstep (se 1 (by rfl) ⟨1691252, by rfl⟩ : syracuseStep 2255003 = 3382505) B3382505
theorem B1338599 : Blo 790340 1338599 := bstep (se 1 (by rfl) ⟨1003949, by rfl⟩ : syracuseStep 1338599 = 2007899) B2007899
theorem B2289071 : Blo 790340 2289071 := bstep (se 1 (by rfl) ⟨1716803, by rfl⟩ : syracuseStep 2289071 = 3433607) B3433607
theorem B1339247 : Blo 790340 1339247 := bstep (se 1 (by rfl) ⟨1004435, by rfl⟩ : syracuseStep 1339247 = 2008871) B2008871
theorem B1339807 : Blo 790340 1339807 := bstep (se 1 (by rfl) ⟨1004855, by rfl⟩ : syracuseStep 1339807 = 2009711) B2009711
theorem B2257463 : Blo 790340 2257463 := bstep (se 1 (by rfl) ⟨1693097, by rfl⟩ : syracuseStep 2257463 = 3386195) B3386195
theorem B7598717 : Blo 790340 7598717 := bstep (se 3 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 7598717 = 2849519) B2849519
theorem B2257703 : Blo 790340 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B3012335 : Blo 790340 3012335 := bstep (se 1 (by rfl) ⟨2259251, by rfl⟩ : syracuseStep 3012335 = 4518503) B4518503
theorem B4520393 : Blo 790340 4520393 := bstep (se 2 (by rfl) ⟨1695147, by rfl⟩ : syracuseStep 4520393 = 3390295) B3390295
theorem B41777693 : Blo 790340 41777693 := bstep (se 3 (by rfl) ⟨7833317, by rfl⟩ : syracuseStep 41777693 = 15666635) B15666635
theorem B4520711 : Blo 790340 4520711 := bstep (se 1 (by rfl) ⟨3390533, by rfl⟩ : syracuseStep 4520711 = 6781067) B6781067
theorem B4520893 : Blo 790340 4520893 := bstep (se 3 (by rfl) ⟨847667, by rfl⟩ : syracuseStep 4520893 = 1695335) B1695335
theorem B1014779 : Blo 790340 1014779 := bstep (se 1 (by rfl) ⟨761084, by rfl⟩ : syracuseStep 1014779 = 1522169) B1522169
theorem B6028343 : Blo 790340 6028343 := bstep (se 1 (by rfl) ⟨4521257, by rfl⟩ : syracuseStep 6028343 = 9042515) B9042515
theorem B7241015 : Blo 790340 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B5800175 : Blo 790340 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B9045431 : Blo 790340 9045431 := bstep (se 1 (by rfl) ⟨6784073, by rfl⟩ : syracuseStep 9045431 = 13568147) B13568147
theorem B2000659 : Blo 790340 2000659 := bstep (se 1 (by rfl) ⟨1500494, by rfl⟩ : syracuseStep 2000659 = 3000989) B3000989
theorem B6785167 : Blo 790340 6785167 := bstep (se 1 (by rfl) ⟨5088875, by rfl⟩ : syracuseStep 6785167 = 10177751) B10177751
theorem B3377807 : Blo 790340 3377807 := bstep (se 1 (by rfl) ⟨2533355, by rfl⟩ : syracuseStep 3377807 = 5066711) B5066711
theorem B7244963 : Blo 790340 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B2002259 : Blo 790340 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B790847 : Blo 790340 790847 := bstep (se 1 (by rfl) ⟨593135, by rfl⟩ : syracuseStep 790847 = 1186271) B1186271
theorem B889159 : Blo 790340 889159 := bstep (se 1 (by rfl) ⟨666869, by rfl⟩ : syracuseStep 889159 = 1333739) B1333739
theorem B791071 : Blo 790340 791071 := bstep (se 1 (by rfl) ⟨593303, by rfl⟩ : syracuseStep 791071 = 1186607) B1186607
theorem B32608889 : Blo 790340 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B791279 : Blo 790340 791279 := bstep (se 1 (by rfl) ⟨593459, by rfl⟩ : syracuseStep 791279 = 1186919) B1186919
theorem B791399 : Blo 790340 791399 := bstep (se 1 (by rfl) ⟨593549, by rfl⟩ : syracuseStep 791399 = 1187099) B1187099
theorem B4002857 : Blo 790340 4002857 := bstep (se 2 (by rfl) ⟨1501071, by rfl⟩ : syracuseStep 4002857 = 3002143) B3002143
theorem B791711 : Blo 790340 791711 := bstep (se 1 (by rfl) ⟨593783, by rfl⟩ : syracuseStep 791711 = 1187567) B1187567
theorem B890095 : Blo 790340 890095 := bstep (se 1 (by rfl) ⟨667571, by rfl⟩ : syracuseStep 890095 = 1335143) B1335143
theorem B791835 : Blo 790340 791835 := bstep (se 1 (by rfl) ⟨593876, by rfl⟩ : syracuseStep 791835 = 1187753) B1187753
theorem B792091 : Blo 790340 792091 := bstep (se 1 (by rfl) ⟨594068, by rfl⟩ : syracuseStep 792091 = 1188137) B1188137
theorem B890527 : Blo 790340 890527 := bstep (se 1 (by rfl) ⟨667895, by rfl⟩ : syracuseStep 890527 = 1335791) B1335791
theorem B792447 : Blo 790340 792447 := bstep (se 1 (by rfl) ⟨594335, by rfl⟩ : syracuseStep 792447 = 1188671) B1188671
theorem B1186103 : Blo 790340 1186103 := bstep (se 1 (by rfl) ⟨889577, by rfl⟩ : syracuseStep 1186103 = 1779155) B1779155
theorem B792895 : Blo 790340 792895 := bstep (se 1 (by rfl) ⟨594671, by rfl⟩ : syracuseStep 792895 = 1189343) B1189343
theorem B6003071 : Blo 790340 6003071 := bstep (se 1 (by rfl) ⟨4502303, by rfl⟩ : syracuseStep 6003071 = 9004607) B9004607
theorem B9640673 : Blo 790340 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B793327 : Blo 790340 793327 := bstep (se 1 (by rfl) ⟨594995, by rfl⟩ : syracuseStep 793327 = 1189991) B1189991
theorem B793471 : Blo 790340 793471 := bstep (se 1 (by rfl) ⟨595103, by rfl⟩ : syracuseStep 793471 = 1190207) B1190207
theorem B1186751 : Blo 790340 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B793583 : Blo 790340 793583 := bstep (se 1 (by rfl) ⟨595187, by rfl⟩ : syracuseStep 793583 = 1190375) B1190375
theorem B1186985 : Blo 790340 1186985 := bstep (se 2 (by rfl) ⟨445119, by rfl⟩ : syracuseStep 1186985 = 890239) B890239
theorem B9641267 : Blo 790340 9641267 := bstep (se 1 (by rfl) ⟨7230950, by rfl⟩ : syracuseStep 9641267 = 14461901) B14461901
theorem B892399 : Blo 790340 892399 := bstep (se 1 (by rfl) ⟨669299, by rfl⟩ : syracuseStep 892399 = 1338599) B1338599
theorem B11411219 : Blo 790340 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B892831 : Blo 790340 892831 := bstep (se 1 (by rfl) ⟨669623, by rfl⟩ : syracuseStep 892831 = 1339247) B1339247
theorem B1187903 : Blo 790340 1187903 := bstep (se 1 (by rfl) ⟨890927, by rfl⟩ : syracuseStep 1187903 = 1781855) B1781855
theorem B1187951 : Blo 790340 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B1188521 : Blo 790340 1188521 := bstep (se 2 (by rfl) ⟨445695, by rfl⟩ : syracuseStep 1188521 = 891391) B891391
theorem B19309373 : Blo 790340 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B1188905 : Blo 790340 1188905 := bstep (se 2 (by rfl) ⟨445839, by rfl⟩ : syracuseStep 1188905 = 891679) B891679
theorem B2008223 : Blo 790340 2008223 := bstep (se 1 (by rfl) ⟨1506167, by rfl⟩ : syracuseStep 2008223 = 3012335) B3012335
theorem B1189223 : Blo 790340 1189223 := bstep (se 1 (by rfl) ⟨891917, by rfl⟩ : syracuseStep 1189223 = 1783835) B1783835
theorem B1779065 : Blo 790340 1779065 := bstep (se 2 (by rfl) ⟨667149, by rfl⟩ : syracuseStep 1779065 = 1334299) B1334299
theorem B1189289 : Blo 790340 1189289 := bstep (se 2 (by rfl) ⟨445983, by rfl⟩ : syracuseStep 1189289 = 891967) B891967
theorem B5089081 : Blo 790340 5089081 := bstep (se 2 (by rfl) ⟨1908405, by rfl⟩ : syracuseStep 5089081 = 3816811) B3816811
theorem B2009843 : Blo 790340 2009843 := bstep (se 1 (by rfl) ⟨1507382, by rfl⟩ : syracuseStep 2009843 = 3014765) B3014765
theorem B3812123 : Blo 790340 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B4762633 : Blo 790340 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B1191143 : Blo 790340 1191143 := bstep (se 1 (by rfl) ⟨893357, by rfl⟩ : syracuseStep 1191143 = 1786715) B1786715
theorem B9907535 : Blo 790340 9907535 := bstep (se 1 (by rfl) ⟨7430651, by rfl⟩ : syracuseStep 9907535 = 14861303) B14861303
theorem B1781279 : Blo 790340 1781279 := bstep (se 1 (by rfl) ⟨1335959, by rfl⟩ : syracuseStep 1781279 = 2671919) B2671919
theorem B2535239 : Blo 790340 2535239 := bstep (se 1 (by rfl) ⟨1901429, by rfl⟩ : syracuseStep 2535239 = 3802859) B3802859
theorem B8565335 : Blo 790340 8565335 := bstep (se 1 (by rfl) ⟨6424001, by rfl⟩ : syracuseStep 8565335 = 12848003) B12848003
theorem B1782503 : Blo 790340 1782503 := bstep (se 1 (by rfl) ⟨1336877, by rfl⟩ : syracuseStep 1782503 = 2673755) B2673755
theorem B4502465 : Blo 790340 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B2667707 : Blo 790340 2667707 := bstep (se 1 (by rfl) ⟨2000780, by rfl⟩ : syracuseStep 2667707 = 4001561) B4001561
theorem B6010361 : Blo 790340 6010361 := bstep (se 2 (by rfl) ⟨2253885, by rfl⟩ : syracuseStep 6010361 = 4507771) B4507771
theorem B2668895 : Blo 790340 2668895 := bstep (se 1 (by rfl) ⟨2001671, by rfl⟩ : syracuseStep 2668895 = 4003343) B4003343
theorem B5716453 : Blo 790340 5716453 := bstep (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) B1071835
theorem B2669057 : Blo 790340 2669057 := bstep (se 2 (by rfl) ⟨1000896, by rfl⟩ : syracuseStep 2669057 = 2001793) B2001793
theorem B27377129 : Blo 790340 27377129 := bstep (se 2 (by rfl) ⟨10266423, by rfl⟩ : syracuseStep 27377129 = 20532847) B20532847
theorem B2670299 : Blo 790340 2670299 := bstep (se 1 (by rfl) ⟨2002724, by rfl⟩ : syracuseStep 2670299 = 4005449) B4005449
theorem B1425683 : Blo 790340 1425683 := bstep (se 1 (by rfl) ⟨1069262, by rfl⟩ : syracuseStep 1425683 = 2138525) B2138525
theorem B41239043 : Blo 790340 41239043 := bstep (se 1 (by rfl) ⟨30929282, by rfl⟩ : syracuseStep 41239043 = 61858565) B61858565
theorem B1786409 : Blo 790340 1786409 := bstep (se 2 (by rfl) ⟨669903, by rfl⟩ : syracuseStep 1786409 = 1339807) B1339807
theorem B1786535 : Blo 790340 1786535 := bstep (se 1 (by rfl) ⟨1339901, by rfl⟩ : syracuseStep 1786535 = 2679803) B2679803
theorem B1786607 : Blo 790340 1786607 := bstep (se 1 (by rfl) ⟨1339955, by rfl⟩ : syracuseStep 1786607 = 2679911) B2679911
theorem B2671595 : Blo 790340 2671595 := bstep (se 1 (by rfl) ⟨2003696, by rfl⟩ : syracuseStep 2671595 = 4007393) B4007393
theorem B8144509 : Blo 790340 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B1526047 : Blo 790340 1526047 := bstep (se 1 (by rfl) ⟨1144535, by rfl⟩ : syracuseStep 1526047 = 2289071) B2289071
theorem B2706077 : Blo 790340 2706077 := bstep (se 3 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 2706077 = 1014779) B1014779
theorem B5065811 : Blo 790340 5065811 := bstep (se 1 (by rfl) ⟨3799358, by rfl⟩ : syracuseStep 5065811 = 7598717) B7598717
theorem B4509503 : Blo 790340 4509503 := bstep (se 1 (by rfl) ⟨3382127, by rfl⟩ : syracuseStep 4509503 = 6764255) B6764255
theorem B11718539 : Blo 790340 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B4018895 : Blo 790340 4018895 := bstep (se 1 (by rfl) ⟨3014171, by rfl⟩ : syracuseStep 4018895 = 6028343) B6028343
theorem B3003115 : Blo 790340 3003115 := bstep (se 1 (by rfl) ⟨2252336, by rfl⟩ : syracuseStep 3003115 = 4504673) B4504673
theorem B4510687 : Blo 790340 4510687 := bstep (se 1 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 4510687 = 6766031) B6766031
theorem B5068271 : Blo 790340 5068271 := bstep (se 1 (by rfl) ⟨3801203, by rfl⟩ : syracuseStep 5068271 = 7602407) B7602407
theorem B97703495 : Blo 790340 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B2676671 : Blo 790340 2676671 := bstep (se 1 (by rfl) ⟨2007503, by rfl⟩ : syracuseStep 2676671 = 4015007) B4015007
theorem B7231679 : Blo 790340 7231679 := bstep (se 1 (by rfl) ⟨5423759, by rfl⟩ : syracuseStep 7231679 = 10847519) B10847519
theorem B20339099 : Blo 790340 20339099 := bstep (se 1 (by rfl) ⟨15254324, by rfl⟩ : syracuseStep 20339099 = 30508649) B30508649
theorem B2251243 : Blo 790340 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B1334137 : Blo 790340 1334137 := bstep (se 2 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 1334137 = 1000603) B1000603
theorem B5069861 : Blo 790340 5069861 := bstep (se 4 (by rfl) ⟨475299, by rfl⟩ : syracuseStep 5069861 = 950599) B950599
theorem B2252087 : Blo 790340 2252087 := bstep (se 1 (by rfl) ⟨1689065, by rfl⟩ : syracuseStep 2252087 = 3378131) B3378131
theorem B4284575 : Blo 790340 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B3006791 : Blo 790340 3006791 := bstep (se 1 (by rfl) ⟨2255093, by rfl⟩ : syracuseStep 3006791 = 4510187) B4510187
theorem B1335919 : Blo 790340 1335919 := bstep (se 1 (by rfl) ⟨1001939, by rfl⟩ : syracuseStep 1335919 = 2003879) B2003879
theorem B2680019 : Blo 790340 2680019 := bstep (se 1 (by rfl) ⟨2010014, by rfl⟩ : syracuseStep 2680019 = 4020029) B4020029
theorem B1336783 : Blo 790340 1336783 := bstep (se 1 (by rfl) ⟨1002587, by rfl⟩ : syracuseStep 1336783 = 2005175) B2005175
theorem B17426015 : Blo 790340 17426015 := bstep (se 1 (by rfl) ⟨13069511, by rfl⟩ : syracuseStep 17426015 = 26139023) B26139023
theorem B10282909 : Blo 790340 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B5433587 : Blo 790340 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B2288047 : Blo 790340 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B15231725 : Blo 790340 15231725 := bstep (se 3 (by rfl) ⟨2855948, by rfl⟩ : syracuseStep 15231725 = 5711897) B5711897
theorem B31255807 : Blo 790340 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B10284731 : Blo 790340 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B17133437 : Blo 790340 17133437 := bstep (se 3 (by rfl) ⟨3212519, by rfl⟩ : syracuseStep 17133437 = 6425039) B6425039
theorem B1339483 : Blo 790340 1339483 := bstep (se 1 (by rfl) ⟨1004612, by rfl⟩ : syracuseStep 1339483 = 2009225) B2009225
theorem B1503335 : Blo 790340 1503335 := bstep (se 1 (by rfl) ⟨1127501, by rfl⟩ : syracuseStep 1503335 = 2255003) B2255003
theorem B25719119 : Blo 790340 25719119 := bstep (se 1 (by rfl) ⟨19289339, by rfl⟩ : syracuseStep 25719119 = 38578679) B38578679
theorem B4289071 : Blo 790340 4289071 := bstep (se 1 (by rfl) ⟨3216803, by rfl⟩ : syracuseStep 4289071 = 6433607) B6433607
theorem B2257577 : Blo 790340 2257577 := bstep (se 2 (by rfl) ⟨846591, by rfl⟩ : syracuseStep 2257577 = 1693183) B1693183
theorem B12219659 : Blo 790340 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B1504975 : Blo 790340 1504975 := bstep (se 1 (by rfl) ⟨1128731, by rfl⟩ : syracuseStep 1504975 = 2257463) B2257463
theorem B1505135 : Blo 790340 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B6027857 : Blo 790340 6027857 := bstep (se 2 (by rfl) ⟨2260446, by rfl⟩ : syracuseStep 6027857 = 4520893) B4520893
theorem B3013595 : Blo 790340 3013595 := bstep (se 1 (by rfl) ⟨2260196, by rfl⟩ : syracuseStep 3013595 = 4520393) B4520393
theorem B27851795 : Blo 790340 27851795 := bstep (se 1 (by rfl) ⟨20888846, by rfl⟩ : syracuseStep 27851795 = 41777693) B41777693
theorem B3013807 : Blo 790340 3013807 := bstep (se 1 (by rfl) ⟨2260355, by rfl⟩ : syracuseStep 3013807 = 4520711) B4520711
theorem B9010439 : Blo 790340 9010439 := bstep (se 1 (by rfl) ⟨6757829, by rfl⟩ : syracuseStep 9010439 = 13515659) B13515659
theorem B3866783 : Blo 790340 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B950455 : Blo 790340 950455 := bstep (se 1 (by rfl) ⟨712841, by rfl⟩ : syracuseStep 950455 = 1425683) B1425683
theorem B27492695 : Blo 790340 27492695 := bstep (se 1 (by rfl) ⟨20619521, by rfl⟩ : syracuseStep 27492695 = 41239043) B41239043
theorem B6030287 : Blo 790340 6030287 := bstep (se 1 (by rfl) ⟨4522715, by rfl⟩ : syracuseStep 6030287 = 9045431) B9045431
theorem B1804051 : Blo 790340 1804051 := bstep (se 1 (by rfl) ⟨1353038, by rfl⟩ : syracuseStep 1804051 = 2706077) B2706077
theorem B3377207 : Blo 790340 3377207 := bstep (se 1 (by rfl) ⟨2532905, by rfl⟩ : syracuseStep 3377207 = 5065811) B5065811
theorem B6785441 : Blo 790340 6785441 := bstep (se 2 (by rfl) ⟨2544540, by rfl⟩ : syracuseStep 6785441 = 5089081) B5089081
theorem B9046889 : Blo 790340 9046889 := bstep (se 2 (by rfl) ⟨3392583, by rfl⟩ : syracuseStep 9046889 = 6785167) B6785167
theorem B3050729 : Blo 790340 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B3378847 : Blo 790340 3378847 := bstep (se 1 (by rfl) ⟨2534135, by rfl⟩ : syracuseStep 3378847 = 5068271) B5068271
theorem B4821119 : Blo 790340 4821119 := bstep (se 1 (by rfl) ⟨3615839, by rfl⟩ : syracuseStep 4821119 = 7231679) B7231679
theorem B790735 : Blo 790340 790735 := bstep (se 1 (by rfl) ⟨593051, by rfl⟩ : syracuseStep 790735 = 1186103) B1186103
theorem B4002047 : Blo 790340 4002047 := bstep (se 1 (by rfl) ⟨3001535, by rfl⟩ : syracuseStep 4002047 = 6003071) B6003071
theorem B6427115 : Blo 790340 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B791167 : Blo 790340 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B3379907 : Blo 790340 3379907 := bstep (se 1 (by rfl) ⟨2534930, by rfl⟩ : syracuseStep 3379907 = 5069861) B5069861
theorem B791323 : Blo 790340 791323 := bstep (se 1 (by rfl) ⟨593492, by rfl⟩ : syracuseStep 791323 = 1186985) B1186985
theorem B6427511 : Blo 790340 6427511 := bstep (se 1 (by rfl) ⟨4820633, by rfl⟩ : syracuseStep 6427511 = 9641267) B9641267
theorem B791935 : Blo 790340 791935 := bstep (se 1 (by rfl) ⟨593951, by rfl⟩ : syracuseStep 791935 = 1187903) B1187903
theorem B791967 : Blo 790340 791967 := bstep (se 1 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 791967 = 1187951) B1187951
theorem B2856383 : Blo 790340 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B2004527 : Blo 790340 2004527 := bstep (se 1 (by rfl) ⟨1503395, by rfl⟩ : syracuseStep 2004527 = 3006791) B3006791
theorem B1185545 : Blo 790340 1185545 := bstep (se 2 (by rfl) ⟨444579, by rfl⟩ : syracuseStep 1185545 = 889159) B889159
theorem B792347 : Blo 790340 792347 := bstep (se 1 (by rfl) ⟨594260, by rfl⟩ : syracuseStep 792347 = 1188521) B1188521
theorem B792603 : Blo 790340 792603 := bstep (se 1 (by rfl) ⟨594452, by rfl⟩ : syracuseStep 792603 = 1188905) B1188905
theorem B792815 : Blo 790340 792815 := bstep (se 1 (by rfl) ⟨594611, by rfl⟩ : syracuseStep 792815 = 1189223) B1189223
theorem B1186043 : Blo 790340 1186043 := bstep (se 1 (by rfl) ⟨889532, by rfl⟩ : syracuseStep 1186043 = 1779065) B1779065
theorem B792859 : Blo 790340 792859 := bstep (se 1 (by rfl) ⟨594644, by rfl⟩ : syracuseStep 792859 = 1189289) B1189289
theorem B4004153 : Blo 790340 4004153 := bstep (se 2 (by rfl) ⟨1501557, by rfl⟩ : syracuseStep 4004153 = 3003115) B3003115
theorem B1186793 : Blo 790340 1186793 := bstep (se 2 (by rfl) ⟨445047, by rfl⟩ : syracuseStep 1186793 = 890095) B890095
theorem B794095 : Blo 790340 794095 := bstep (se 1 (by rfl) ⟨595571, by rfl⟩ : syracuseStep 794095 = 1191143) B1191143
theorem B1187369 : Blo 790340 1187369 := bstep (se 2 (by rfl) ⟨445263, by rfl⟩ : syracuseStep 1187369 = 890527) B890527
theorem B2006633 : Blo 790340 2006633 := bstep (se 2 (by rfl) ⟨752487, by rfl⟩ : syracuseStep 2006633 = 1504975) B1504975
theorem B1187519 : Blo 790340 1187519 := bstep (se 1 (by rfl) ⟨890639, by rfl⟩ : syracuseStep 1187519 = 1781279) B1781279
theorem B6856487 : Blo 790340 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B17146079 : Blo 790340 17146079 := bstep (se 1 (by rfl) ⟨12859559, by rfl⟩ : syracuseStep 17146079 = 25719119) B25719119
theorem B5710223 : Blo 790340 5710223 := bstep (se 1 (by rfl) ⟨4282667, by rfl⟩ : syracuseStep 5710223 = 8565335) B8565335
theorem B1188335 : Blo 790340 1188335 := bstep (se 1 (by rfl) ⟨891251, by rfl⟩ : syracuseStep 1188335 = 1782503) B1782503
theorem B1778471 : Blo 790340 1778471 := bstep (se 1 (by rfl) ⟨1333853, by rfl⟩ : syracuseStep 1778471 = 2667707) B2667707
theorem B26420093 : Blo 790340 26420093 := bstep (se 3 (by rfl) ⟨4953767, by rfl⟩ : syracuseStep 26420093 = 9907535) B9907535
theorem B4006907 : Blo 790340 4006907 := bstep (se 1 (by rfl) ⟨3005180, by rfl⟩ : syracuseStep 4006907 = 6010361) B6010361
theorem B1778849 : Blo 790340 1778849 := bstep (se 2 (by rfl) ⟨667068, by rfl⟩ : syracuseStep 1778849 = 1334137) B1334137
theorem B1779263 : Blo 790340 1779263 := bstep (se 1 (by rfl) ⟨1334447, by rfl⟩ : syracuseStep 1779263 = 2668895) B2668895
theorem B1779371 : Blo 790340 1779371 := bstep (se 1 (by rfl) ⟨1334528, by rfl⟩ : syracuseStep 1779371 = 2669057) B2669057
theorem B2009063 : Blo 790340 2009063 := bstep (se 1 (by rfl) ⟨1506797, by rfl⟩ : syracuseStep 2009063 = 3013595) B3013595
theorem B1189865 : Blo 790340 1189865 := bstep (se 2 (by rfl) ⟨446199, by rfl⟩ : syracuseStep 1189865 = 892399) B892399
theorem B6006959 : Blo 790340 6006959 := bstep (se 1 (by rfl) ⟨4505219, by rfl⟩ : syracuseStep 6006959 = 9010439) B9010439
theorem B1780199 : Blo 790340 1780199 := bstep (se 1 (by rfl) ⟨1335149, by rfl⟩ : syracuseStep 1780199 = 2670299) B2670299
theorem B1190441 : Blo 790340 1190441 := bstep (se 2 (by rfl) ⟨446415, by rfl⟩ : syracuseStep 1190441 = 892831) B892831
theorem B1190939 : Blo 790340 1190939 := bstep (se 1 (by rfl) ⟨893204, by rfl⟩ : syracuseStep 1190939 = 1786409) B1786409
theorem B1191023 : Blo 790340 1191023 := bstep (se 1 (by rfl) ⟨893267, by rfl⟩ : syracuseStep 1191023 = 1786535) B1786535
theorem B1191071 : Blo 790340 1191071 := bstep (se 1 (by rfl) ⟨893303, by rfl⟩ : syracuseStep 1191071 = 1786607) B1786607
theorem B1781063 : Blo 790340 1781063 := bstep (se 1 (by rfl) ⟨1335797, by rfl⟩ : syracuseStep 1781063 = 2671595) B2671595
theorem B1781225 : Blo 790340 1781225 := bstep (se 2 (by rfl) ⟨667959, by rfl⟩ : syracuseStep 1781225 = 1335919) B1335919
theorem B8138917 : Blo 790340 8138917 := bstep (se 4 (by rfl) ⟨763023, by rfl⟩ : syracuseStep 8138917 = 1526047) B1526047
theorem B1782377 : Blo 790340 1782377 := bstep (se 2 (by rfl) ⟨668391, by rfl⟩ : syracuseStep 1782377 = 1336783) B1336783
theorem B4829975 : Blo 790340 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B10859345 : Blo 790340 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B2667545 : Blo 790340 2667545 := bstep (se 2 (by rfl) ⟨1000329, by rfl⟩ : syracuseStep 2667545 = 2000659) B2000659
theorem B13710545 : Blo 790340 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B7812359 : Blo 790340 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B21739259 : Blo 790340 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B2668571 : Blo 790340 2668571 := bstep (se 1 (by rfl) ⟨2001428, by rfl⟩ : syracuseStep 2668571 = 4002857) B4002857
theorem B1784447 : Blo 790340 1784447 := bstep (se 1 (by rfl) ⟨1338335, by rfl⟩ : syracuseStep 1784447 = 2676671) B2676671
theorem B1785977 : Blo 790340 1785977 := bstep (se 2 (by rfl) ⟨669741, by rfl⟩ : syracuseStep 1785977 = 1339483) B1339483
theorem B5718761 : Blo 790340 5718761 := bstep (se 2 (by rfl) ⟨2144535, by rfl⟩ : syracuseStep 5718761 = 4289071) B4289071
theorem B1786679 : Blo 790340 1786679 := bstep (se 1 (by rfl) ⟨1340009, by rfl⟩ : syracuseStep 1786679 = 2680019) B2680019
theorem B11617343 : Blo 790340 11617343 := bstep (se 1 (by rfl) ⟨8713007, by rfl⟩ : syracuseStep 11617343 = 17426015) B17426015
theorem B6014249 : Blo 790340 6014249 := bstep (se 2 (by rfl) ⟨2255343, by rfl⟩ : syracuseStep 6014249 = 4510687) B4510687
theorem B3622391 : Blo 790340 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B2541415 : Blo 790340 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B1690159 : Blo 790340 1690159 := bstep (se 1 (by rfl) ⟨1267619, by rfl⟩ : syracuseStep 1690159 = 2535239) B2535239
theorem B11422291 : Blo 790340 11422291 := bstep (se 1 (by rfl) ⟨8566718, by rfl⟩ : syracuseStep 11422291 = 17133437) B17133437
theorem B1002223 : Blo 790340 1002223 := bstep (se 1 (by rfl) ⟨751667, by rfl⟩ : syracuseStep 1002223 = 1503335) B1503335
theorem B3001643 : Blo 790340 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B7621937 : Blo 790340 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B3001657 : Blo 790340 3001657 := bstep (se 2 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 3001657 = 2251243) B2251243
theorem B8146439 : Blo 790340 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B1003423 : Blo 790340 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B4018409 : Blo 790340 4018409 := bstep (se 2 (by rfl) ⟨1506903, by rfl⟩ : syracuseStep 4018409 = 3013807) B3013807
theorem B4018571 : Blo 790340 4018571 := bstep (se 1 (by rfl) ⟨3013928, by rfl⟩ : syracuseStep 4018571 = 6027857) B6027857
theorem B18567863 : Blo 790340 18567863 := bstep (se 1 (by rfl) ⟨13925897, by rfl⟩ : syracuseStep 18567863 = 27851795) B27851795
theorem B30429917 : Blo 790340 30429917 := bstep (se 3 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 30429917 = 11411219) B11411219
theorem B2251871 : Blo 790340 2251871 := bstep (se 1 (by rfl) ⟨1688903, by rfl⟩ : syracuseStep 2251871 = 3377807) B3377807
theorem B1334839 : Blo 790340 1334839 := bstep (se 1 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 1334839 = 2002259) B2002259
theorem B3006335 : Blo 790340 3006335 := bstep (se 1 (by rfl) ⟨2254751, by rfl⟩ : syracuseStep 3006335 = 4509503) B4509503
theorem B2679263 : Blo 790340 2679263 := bstep (se 1 (by rfl) ⟨2009447, by rfl⟩ : syracuseStep 2679263 = 4018895) B4018895
theorem B65135663 : Blo 790340 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B6350177 : Blo 790340 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B13559399 : Blo 790340 13559399 := bstep (se 1 (by rfl) ⟨10169549, by rfl⟩ : syracuseStep 13559399 = 20339099) B20339099
theorem B41674409 : Blo 790340 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B1501391 : Blo 790340 1501391 := bstep (se 1 (by rfl) ⟨1126043, by rfl⟩ : syracuseStep 1501391 = 2252087) B2252087
theorem B12872915 : Blo 790340 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B1338815 : Blo 790340 1338815 := bstep (se 1 (by rfl) ⟨1004111, by rfl⟩ : syracuseStep 1338815 = 2008223) B2008223
theorem B10154483 : Blo 790340 10154483 := bstep (se 1 (by rfl) ⟨7615862, by rfl⟩ : syracuseStep 10154483 = 15231725) B15231725
theorem B1339895 : Blo 790340 1339895 := bstep (se 1 (by rfl) ⟨1004921, by rfl⟩ : syracuseStep 1339895 = 2009843) B2009843
theorem B1505051 : Blo 790340 1505051 := bstep (se 1 (by rfl) ⟨1128788, by rfl⟩ : syracuseStep 1505051 = 2257577) B2257577
theorem B18251419 : Blo 790340 18251419 := bstep (se 1 (by rfl) ⟨13688564, by rfl⟩ : syracuseStep 18251419 = 27377129) B27377129
theorem B4523627 : Blo 790340 4523627 := bstep (se 1 (by rfl) ⟨3392720, by rfl⟩ : syracuseStep 4523627 = 6785441) B6785441
theorem B6031259 : Blo 790340 6031259 := bstep (se 1 (by rfl) ⟨4523444, by rfl⟩ : syracuseStep 6031259 = 9046889) B9046889
theorem B2033819 : Blo 790340 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B2001095 : Blo 790340 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B5081291 : Blo 790340 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B3214079 : Blo 790340 3214079 := bstep (se 1 (by rfl) ⟨2410559, by rfl⟩ : syracuseStep 3214079 = 4821119) B4821119
theorem B20286611 : Blo 790340 20286611 := bstep (se 1 (by rfl) ⟨15214958, by rfl⟩ : syracuseStep 20286611 = 30429917) B30429917
theorem B1904255 : Blo 790340 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B790363 : Blo 790340 790363 := bstep (se 1 (by rfl) ⟨592772, by rfl⟩ : syracuseStep 790363 = 1185545) B1185545
theorem B790695 : Blo 790340 790695 := bstep (se 1 (by rfl) ⟨593021, by rfl⟩ : syracuseStep 790695 = 1186043) B1186043
theorem B4002209 : Blo 790340 4002209 := bstep (se 2 (by rfl) ⟨1500828, by rfl⟩ : syracuseStep 4002209 = 3001657) B3001657
theorem B791195 : Blo 790340 791195 := bstep (se 1 (by rfl) ⟨593396, by rfl⟩ : syracuseStep 791195 = 1186793) B1186793
theorem B791579 : Blo 790340 791579 := bstep (se 1 (by rfl) ⟨593684, by rfl⟩ : syracuseStep 791579 = 1187369) B1187369
theorem B791679 : Blo 790340 791679 := bstep (se 1 (by rfl) ⟨593759, by rfl⟩ : syracuseStep 791679 = 1187519) B1187519
theorem B2004223 : Blo 790340 2004223 := bstep (se 1 (by rfl) ⟨1503167, by rfl⟩ : syracuseStep 2004223 = 3006335) B3006335
theorem B10851889 : Blo 790340 10851889 := bstep (se 2 (by rfl) ⟨4069458, by rfl⟩ : syracuseStep 10851889 = 8138917) B8138917
theorem B792223 : Blo 790340 792223 := bstep (se 1 (by rfl) ⟨594167, by rfl⟩ : syracuseStep 792223 = 1188335) B1188335
theorem B1185647 : Blo 790340 1185647 := bstep (se 1 (by rfl) ⟨889235, by rfl⟩ : syracuseStep 1185647 = 1778471) B1778471
theorem B43423775 : Blo 790340 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B1185899 : Blo 790340 1185899 := bstep (se 1 (by rfl) ⟨889424, by rfl⟩ : syracuseStep 1185899 = 1778849) B1778849
theorem B1186175 : Blo 790340 1186175 := bstep (se 1 (by rfl) ⟨889631, by rfl⟩ : syracuseStep 1186175 = 1779263) B1779263
theorem B1186247 : Blo 790340 1186247 := bstep (se 1 (by rfl) ⟨889685, by rfl⟩ : syracuseStep 1186247 = 1779371) B1779371
theorem B793243 : Blo 790340 793243 := bstep (se 1 (by rfl) ⟨594932, by rfl⟩ : syracuseStep 793243 = 1189865) B1189865
theorem B4004639 : Blo 790340 4004639 := bstep (se 1 (by rfl) ⟨3003479, by rfl⟩ : syracuseStep 4004639 = 6006959) B6006959
theorem B1186799 : Blo 790340 1186799 := bstep (se 1 (by rfl) ⟨890099, by rfl⟩ : syracuseStep 1186799 = 1780199) B1780199
theorem B793627 : Blo 790340 793627 := bstep (se 1 (by rfl) ⟨595220, by rfl⟩ : syracuseStep 793627 = 1190441) B1190441
theorem B793959 : Blo 790340 793959 := bstep (se 1 (by rfl) ⟨595469, by rfl⟩ : syracuseStep 793959 = 1190939) B1190939
theorem B794015 : Blo 790340 794015 := bstep (se 1 (by rfl) ⟨595511, by rfl⟩ : syracuseStep 794015 = 1191023) B1191023
theorem B794047 : Blo 790340 794047 := bstep (se 1 (by rfl) ⟨595535, by rfl⟩ : syracuseStep 794047 = 1191071) B1191071
theorem B1187375 : Blo 790340 1187375 := bstep (se 1 (by rfl) ⟨890531, by rfl⟩ : syracuseStep 1187375 = 1781063) B1781063
theorem B892543 : Blo 790340 892543 := bstep (se 1 (by rfl) ⟨669407, by rfl⟩ : syracuseStep 892543 = 1338815) B1338815
theorem B1187483 : Blo 790340 1187483 := bstep (se 1 (by rfl) ⟨890612, by rfl⟩ : syracuseStep 1187483 = 1781225) B1781225
theorem B893263 : Blo 790340 893263 := bstep (se 1 (by rfl) ⟨669947, by rfl⟩ : syracuseStep 893263 = 1339895) B1339895
theorem B1188251 : Blo 790340 1188251 := bstep (se 1 (by rfl) ⟨891188, by rfl⟩ : syracuseStep 1188251 = 1782377) B1782377
theorem B3219983 : Blo 790340 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B1778363 : Blo 790340 1778363 := bstep (se 1 (by rfl) ⟨1333772, by rfl⟩ : syracuseStep 1778363 = 2667545) B2667545
theorem B14492839 : Blo 790340 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B1779047 : Blo 790340 1779047 := bstep (se 1 (by rfl) ⟨1334285, by rfl⟩ : syracuseStep 1779047 = 2668571) B2668571
theorem B1189631 : Blo 790340 1189631 := bstep (se 1 (by rfl) ⟨892223, by rfl⟩ : syracuseStep 1189631 = 1784447) B1784447
theorem B1779785 : Blo 790340 1779785 := bstep (se 2 (by rfl) ⟨667419, by rfl⟩ : syracuseStep 1779785 = 1334839) B1334839
theorem B1190651 : Blo 790340 1190651 := bstep (se 1 (by rfl) ⟨892988, by rfl⟩ : syracuseStep 1190651 = 1785977) B1785977
theorem B18328463 : Blo 790340 18328463 := bstep (se 1 (by rfl) ⟨13746347, by rfl⟩ : syracuseStep 18328463 = 27492695) B27492695
theorem B3812507 : Blo 790340 3812507 := bstep (se 1 (by rfl) ⟨2859380, by rfl⟩ : syracuseStep 3812507 = 5718761) B5718761
theorem B1191119 : Blo 790340 1191119 := bstep (se 1 (by rfl) ⟨893339, by rfl⟩ : syracuseStep 1191119 = 1786679) B1786679
theorem B7744895 : Blo 790340 7744895 := bstep (se 1 (by rfl) ⟨5808671, by rfl⟩ : syracuseStep 7744895 = 11617343) B11617343
theorem B4009499 : Blo 790340 4009499 := bstep (se 1 (by rfl) ⟨3007124, by rfl⟩ : syracuseStep 4009499 = 6014249) B6014249
theorem B3388553 : Blo 790340 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B2668031 : Blo 790340 2668031 := bstep (se 1 (by rfl) ⟨2001023, by rfl⟩ : syracuseStep 2668031 = 4002047) B4002047
theorem B2669435 : Blo 790340 2669435 := bstep (se 1 (by rfl) ⟨2002076, by rfl⟩ : syracuseStep 2669435 = 4004153) B4004153
theorem B4505129 : Blo 790340 4505129 := bstep (se 2 (by rfl) ⟨1689423, by rfl⟩ : syracuseStep 4505129 = 3378847) B3378847
theorem B4570991 : Blo 790340 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B1786175 : Blo 790340 1786175 := bstep (se 1 (by rfl) ⟨1339631, by rfl⟩ : syracuseStep 1786175 = 2679263) B2679263
theorem B17613395 : Blo 790340 17613395 := bstep (se 1 (by rfl) ⟨13210046, by rfl⟩ : syracuseStep 17613395 = 26420093) B26420093
theorem B2671271 : Blo 790340 2671271 := bstep (se 1 (by rfl) ⟨2003453, by rfl⟩ : syracuseStep 2671271 = 4006907) B4006907
theorem B1000927 : Blo 790340 1000927 := bstep (se 1 (by rfl) ⟨750695, by rfl⟩ : syracuseStep 1000927 = 1501391) B1501391
theorem B6769655 : Blo 790340 6769655 := bstep (se 1 (by rfl) ⟨5077241, by rfl⟩ : syracuseStep 6769655 = 10154483) B10154483
theorem B1003367 : Blo 790340 1003367 := bstep (se 1 (by rfl) ⟨752525, by rfl⟩ : syracuseStep 1003367 = 1505051) B1505051
theorem B9621605 : Blo 790340 9621605 := bstep (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) B1804051
theorem B24335225 : Blo 790340 24335225 := bstep (se 2 (by rfl) ⟨9125709, by rfl⟩ : syracuseStep 24335225 = 18251419) B18251419
theorem B1267273 : Blo 790340 1267273 := bstep (se 2 (by rfl) ⟨475227, by rfl⟩ : syracuseStep 1267273 = 950455) B950455
theorem B10311421 : Blo 790340 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B4020191 : Blo 790340 4020191 := bstep (se 1 (by rfl) ⟨3015143, by rfl⟩ : syracuseStep 4020191 = 6030287) B6030287
theorem B2414927 : Blo 790340 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B15227261 : Blo 790340 15227261 := bstep (se 3 (by rfl) ⟨2855111, by rfl⟩ : syracuseStep 15227261 = 5710223) B5710223
theorem B2251471 : Blo 790340 2251471 := bstep (se 1 (by rfl) ⟨1688603, by rfl⟩ : syracuseStep 2251471 = 3377207) B3377207
theorem B5430959 : Blo 790340 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B2678939 : Blo 790340 2678939 := bstep (se 1 (by rfl) ⟨2009204, by rfl⟩ : syracuseStep 2678939 = 4018409) B4018409
theorem B2679047 : Blo 790340 2679047 := bstep (se 1 (by rfl) ⟨2009285, by rfl⟩ : syracuseStep 2679047 = 4018571) B4018571
theorem B4284743 : Blo 790340 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B12378575 : Blo 790340 12378575 := bstep (se 1 (by rfl) ⟨9283931, by rfl⟩ : syracuseStep 12378575 = 18567863) B18567863
theorem B2253271 : Blo 790340 2253271 := bstep (se 1 (by rfl) ⟨1689953, by rfl⟩ : syracuseStep 2253271 = 3379907) B3379907
theorem B4285007 : Blo 790340 4285007 := bstep (se 1 (by rfl) ⟨3213755, by rfl⟩ : syracuseStep 4285007 = 6427511) B6427511
theorem B2253545 : Blo 790340 2253545 := bstep (se 2 (by rfl) ⟨845079, by rfl⟩ : syracuseStep 2253545 = 1690159) B1690159
theorem B15229721 : Blo 790340 15229721 := bstep (se 2 (by rfl) ⟨5711145, by rfl⟩ : syracuseStep 15229721 = 11422291) B11422291
theorem B16933805 : Blo 790340 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B1336297 : Blo 790340 1336297 := bstep (se 2 (by rfl) ⟨501111, by rfl⟩ : syracuseStep 1336297 = 1002223) B1002223
theorem B1336351 : Blo 790340 1336351 := bstep (se 1 (by rfl) ⟨1002263, by rfl⟩ : syracuseStep 1336351 = 2004527) B2004527
theorem B1501247 : Blo 790340 1501247 := bstep (se 1 (by rfl) ⟨1125935, by rfl⟩ : syracuseStep 1501247 = 2251871) B2251871
theorem B1337755 : Blo 790340 1337755 := bstep (se 1 (by rfl) ⟨1003316, by rfl⟩ : syracuseStep 1337755 = 2006633) B2006633
theorem B1337897 : Blo 790340 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B11430719 : Blo 790340 11430719 := bstep (se 1 (by rfl) ⟨8573039, by rfl⟩ : syracuseStep 11430719 = 17146079) B17146079
theorem B9039599 : Blo 790340 9039599 := bstep (se 1 (by rfl) ⟨6779699, by rfl⟩ : syracuseStep 9039599 = 13559399) B13559399
theorem B27782939 : Blo 790340 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B1339375 : Blo 790340 1339375 := bstep (se 1 (by rfl) ⟨1004531, by rfl⟩ : syracuseStep 1339375 = 2009063) B2009063
theorem B8581943 : Blo 790340 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B7239563 : Blo 790340 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B9140363 : Blo 790340 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B5208239 : Blo 790340 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B3015751 : Blo 790340 3015751 := bstep (se 1 (by rfl) ⟨2261813, by rfl⟩ : syracuseStep 3015751 = 4523627) B4523627
theorem B16223483 : Blo 790340 16223483 := bstep (se 1 (by rfl) ⟨12167612, by rfl⟩ : syracuseStep 16223483 = 24335225) B24335225
theorem B790431 : Blo 790340 790431 := bstep (se 1 (by rfl) ⟨592823, by rfl⟩ : syracuseStep 790431 = 1185647) B1185647
theorem B790599 : Blo 790340 790599 := bstep (se 1 (by rfl) ⟨592949, by rfl⟩ : syracuseStep 790599 = 1185899) B1185899
theorem B1609951 : Blo 790340 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B790783 : Blo 790340 790783 := bstep (se 1 (by rfl) ⟨593087, by rfl⟩ : syracuseStep 790783 = 1186175) B1186175
theorem B790831 : Blo 790340 790831 := bstep (se 1 (by rfl) ⟨593123, by rfl⟩ : syracuseStep 790831 = 1186247) B1186247
theorem B791199 : Blo 790340 791199 := bstep (se 1 (by rfl) ⟨593399, by rfl⟩ : syracuseStep 791199 = 1186799) B1186799
theorem B791583 : Blo 790340 791583 := bstep (se 1 (by rfl) ⟨593687, by rfl⟩ : syracuseStep 791583 = 1187375) B1187375
theorem B791655 : Blo 790340 791655 := bstep (se 1 (by rfl) ⟨593741, by rfl⟩ : syracuseStep 791655 = 1187483) B1187483
theorem B792167 : Blo 790340 792167 := bstep (se 1 (by rfl) ⟨594125, by rfl⟩ : syracuseStep 792167 = 1188251) B1188251
theorem B2856671 : Blo 790340 2856671 := bstep (se 1 (by rfl) ⟨2142503, by rfl⟩ : syracuseStep 2856671 = 4285007) B4285007
theorem B1185575 : Blo 790340 1185575 := bstep (se 1 (by rfl) ⟨889181, by rfl⟩ : syracuseStep 1185575 = 1778363) B1778363
theorem B1186031 : Blo 790340 1186031 := bstep (se 1 (by rfl) ⟨889523, by rfl⟩ : syracuseStep 1186031 = 1779047) B1779047
theorem B793087 : Blo 790340 793087 := bstep (se 1 (by rfl) ⟨594815, by rfl⟩ : syracuseStep 793087 = 1189631) B1189631
theorem B1186523 : Blo 790340 1186523 := bstep (se 1 (by rfl) ⟨889892, by rfl⟩ : syracuseStep 1186523 = 1779785) B1779785
theorem B891931 : Blo 790340 891931 := bstep (se 1 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 891931 = 1337897) B1337897
theorem B793767 : Blo 790340 793767 := bstep (se 1 (by rfl) ⟨595325, by rfl⟩ : syracuseStep 793767 = 1190651) B1190651
theorem B794079 : Blo 790340 794079 := bstep (se 1 (by rfl) ⟨595559, by rfl⟩ : syracuseStep 794079 = 1191119) B1191119
theorem B18521959 : Blo 790340 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B1778687 : Blo 790340 1778687 := bstep (se 1 (by rfl) ⟨1334015, by rfl⟩ : syracuseStep 1778687 = 2668031) B2668031
theorem B4826375 : Blo 790340 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B1779623 : Blo 790340 1779623 := bstep (se 1 (by rfl) ⟨1334717, by rfl⟩ : syracuseStep 1779623 = 2669435) B2669435
theorem B1190057 : Blo 790340 1190057 := bstep (se 2 (by rfl) ⟨446271, by rfl⟩ : syracuseStep 1190057 = 892543) B892543
theorem B1190783 : Blo 790340 1190783 := bstep (se 1 (by rfl) ⟨893087, by rfl⟩ : syracuseStep 1190783 = 1786175) B1786175
theorem B11742263 : Blo 790340 11742263 := bstep (se 1 (by rfl) ⟨8806697, by rfl⟩ : syracuseStep 11742263 = 17613395) B17613395
theorem B1191017 : Blo 790340 1191017 := bstep (se 2 (by rfl) ⟨446631, by rfl⟩ : syracuseStep 1191017 = 893263) B893263
theorem B1780847 : Blo 790340 1780847 := bstep (se 1 (by rfl) ⟨1335635, by rfl⟩ : syracuseStep 1780847 = 2671271) B2671271
theorem B1781729 : Blo 790340 1781729 := bstep (se 2 (by rfl) ⟨668148, by rfl⟩ : syracuseStep 1781729 = 1336297) B1336297
theorem B1781801 : Blo 790340 1781801 := bstep (se 2 (by rfl) ⟨668175, by rfl⟩ : syracuseStep 1781801 = 1336351) B1336351
theorem B1355879 : Blo 790340 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B3387527 : Blo 790340 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B2142719 : Blo 790340 2142719 := bstep (se 1 (by rfl) ⟨1607039, by rfl⟩ : syracuseStep 2142719 = 3214079) B3214079
theorem B2668139 : Blo 790340 2668139 := bstep (se 1 (by rfl) ⟨2001104, by rfl⟩ : syracuseStep 2668139 = 4002209) B4002209
theorem B1783673 : Blo 790340 1783673 := bstep (se 2 (by rfl) ⟨668877, by rfl⟩ : syracuseStep 1783673 = 1337755) B1337755
theorem B28949183 : Blo 790340 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B2669759 : Blo 790340 2669759 := bstep (se 1 (by rfl) ⟨2002319, by rfl⟩ : syracuseStep 2669759 = 4004639) B4004639
theorem B3620639 : Blo 790340 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B1785833 : Blo 790340 1785833 := bstep (se 2 (by rfl) ⟨669687, by rfl⟩ : syracuseStep 1785833 = 1339375) B1339375
theorem B1785959 : Blo 790340 1785959 := bstep (se 1 (by rfl) ⟨1339469, by rfl⟩ : syracuseStep 1785959 = 2678939) B2678939
theorem B1786031 : Blo 790340 1786031 := bstep (se 1 (by rfl) ⟨1339523, by rfl⟩ : syracuseStep 1786031 = 2679047) B2679047
theorem B2146655 : Blo 790340 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B11289203 : Blo 790340 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B1000831 : Blo 790340 1000831 := bstep (se 1 (by rfl) ⟨750623, by rfl⟩ : syracuseStep 1000831 = 1501247) B1501247
theorem B2672297 : Blo 790340 2672297 := bstep (se 2 (by rfl) ⟨1002111, by rfl⟩ : syracuseStep 2672297 = 2004223) B2004223
theorem B7620479 : Blo 790340 7620479 := bstep (se 1 (by rfl) ⟨5715359, by rfl⟩ : syracuseStep 7620479 = 11430719) B11430719
theorem B14469185 : Blo 790340 14469185 := bstep (se 2 (by rfl) ⟨5425944, by rfl⟩ : syracuseStep 14469185 = 10851889) B10851889
theorem B1689697 : Blo 790340 1689697 := bstep (se 2 (by rfl) ⟨633636, by rfl⟩ : syracuseStep 1689697 = 1267273) B1267273
theorem B2541671 : Blo 790340 2541671 := bstep (se 1 (by rfl) ⟨1906253, by rfl⟩ : syracuseStep 2541671 = 3812507) B3812507
theorem B5163263 : Blo 790340 5163263 := bstep (se 1 (by rfl) ⟨3872447, by rfl⟩ : syracuseStep 5163263 = 7744895) B7744895
theorem B13748561 : Blo 790340 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B2672999 : Blo 790340 2672999 := bstep (se 1 (by rfl) ⟨2004749, by rfl⟩ : syracuseStep 2672999 = 4009499) B4009499
theorem B5721295 : Blo 790340 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B3001961 : Blo 790340 3001961 := bstep (se 2 (by rfl) ⟨1125735, by rfl⟩ : syracuseStep 3001961 = 2251471) B2251471
theorem B2675645 : Blo 790340 2675645 := bstep (se 3 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 2675645 = 1003367) B1003367
theorem B3003419 : Blo 790340 3003419 := bstep (se 1 (by rfl) ⟨2252564, by rfl⟩ : syracuseStep 3003419 = 4505129) B4505129
theorem B3004361 : Blo 790340 3004361 := bstep (se 2 (by rfl) ⟨1126635, by rfl⟩ : syracuseStep 3004361 = 2253271) B2253271
theorem B4020839 : Blo 790340 4020839 := bstep (se 1 (by rfl) ⟨3015629, by rfl⟩ : syracuseStep 4020839 = 6031259) B6031259
theorem B1334063 : Blo 790340 1334063 := bstep (se 1 (by rfl) ⟨1000547, by rfl⟩ : syracuseStep 1334063 = 2001095) B2001095
theorem B19323785 : Blo 790340 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B1334569 : Blo 790340 1334569 := bstep (se 2 (by rfl) ⟨500463, by rfl⟩ : syracuseStep 1334569 = 1000927) B1000927
theorem B4513103 : Blo 790340 4513103 := bstep (se 1 (by rfl) ⟨3384827, by rfl⟩ : syracuseStep 4513103 = 6769655) B6769655
theorem B13524407 : Blo 790340 13524407 := bstep (se 1 (by rfl) ⟨10143305, by rfl⟩ : syracuseStep 13524407 = 20286611) B20286611
theorem B1269503 : Blo 790340 1269503 := bstep (se 1 (by rfl) ⟨952127, by rfl⟩ : syracuseStep 1269503 = 1904255) B1904255
theorem B6414403 : Blo 790340 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B45703925 : Blo 790340 45703925 := bstep (se 5 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 45703925 = 4284743) B4284743
theorem B2680127 : Blo 790340 2680127 := bstep (se 1 (by rfl) ⟨2010095, by rfl⟩ : syracuseStep 2680127 = 4020191) B4020191
theorem B10151507 : Blo 790340 10151507 := bstep (se 1 (by rfl) ⟨7613630, by rfl⟩ : syracuseStep 10151507 = 15227261) B15227261
theorem B8252383 : Blo 790340 8252383 := bstep (se 1 (by rfl) ⟨6189287, by rfl⟩ : syracuseStep 8252383 = 12378575) B12378575
theorem B1502363 : Blo 790340 1502363 := bstep (se 1 (by rfl) ⟨1126772, by rfl⟩ : syracuseStep 1502363 = 2253545) B2253545
theorem B10153147 : Blo 790340 10153147 := bstep (se 1 (by rfl) ⟨7614860, by rfl⟩ : syracuseStep 10153147 = 15229721) B15229721
theorem B12218975 : Blo 790340 12218975 := bstep (se 1 (by rfl) ⟨9164231, by rfl⟩ : syracuseStep 12218975 = 18328463) B18328463
theorem B6026399 : Blo 790340 6026399 := bstep (se 1 (by rfl) ⟨4519799, by rfl⟩ : syracuseStep 6026399 = 9039599) B9039599
theorem B2259035 : Blo 790340 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B6093575 : Blo 790340 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B3472159 : Blo 790340 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B3047327 : Blo 790340 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B8552537 : Blo 790340 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B5080319 : Blo 790340 5080319 := bstep (se 1 (by rfl) ⟨3810239, by rfl⟩ : syracuseStep 5080319 = 7620479) B7620479
theorem B3442175 : Blo 790340 3442175 := bstep (se 1 (by rfl) ⟨2581631, by rfl⟩ : syracuseStep 3442175 = 5163263) B5163263
theorem B10815655 : Blo 790340 10815655 := bstep (se 1 (by rfl) ⟨8111741, by rfl⟩ : syracuseStep 10815655 = 16223483) B16223483
theorem B2001307 : Blo 790340 2001307 := bstep (se 1 (by rfl) ⟨1500980, by rfl⟩ : syracuseStep 2001307 = 3001961) B3001961
theorem B2002279 : Blo 790340 2002279 := bstep (se 1 (by rfl) ⟨1501709, by rfl⟩ : syracuseStep 2002279 = 3003419) B3003419
theorem B1904447 : Blo 790340 1904447 := bstep (se 1 (by rfl) ⟨1428335, by rfl⟩ : syracuseStep 1904447 = 2856671) B2856671
theorem B790383 : Blo 790340 790383 := bstep (se 1 (by rfl) ⟨592787, by rfl⟩ : syracuseStep 790383 = 1185575) B1185575
theorem B2002907 : Blo 790340 2002907 := bstep (se 1 (by rfl) ⟨1502180, by rfl⟩ : syracuseStep 2002907 = 3004361) B3004361
theorem B790687 : Blo 790340 790687 := bstep (se 1 (by rfl) ⟨593015, by rfl⟩ : syracuseStep 790687 = 1186031) B1186031
theorem B13537529 : Blo 790340 13537529 := bstep (se 2 (by rfl) ⟨5076573, by rfl⟩ : syracuseStep 13537529 = 10153147) B10153147
theorem B791015 : Blo 790340 791015 := bstep (se 1 (by rfl) ⟨593261, by rfl⟩ : syracuseStep 791015 = 1186523) B1186523
theorem B889375 : Blo 790340 889375 := bstep (se 1 (by rfl) ⟨667031, by rfl⟩ : syracuseStep 889375 = 1334063) B1334063
theorem B12882523 : Blo 790340 12882523 := bstep (se 1 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 12882523 = 19323785) B19323785
theorem B9016271 : Blo 790340 9016271 := bstep (se 1 (by rfl) ⟨6762203, by rfl⟩ : syracuseStep 9016271 = 13524407) B13524407
theorem B1185791 : Blo 790340 1185791 := bstep (se 1 (by rfl) ⟨889343, by rfl⟩ : syracuseStep 1185791 = 1778687) B1778687
theorem B3217583 : Blo 790340 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B1186415 : Blo 790340 1186415 := bstep (se 1 (by rfl) ⟨889811, by rfl⟩ : syracuseStep 1186415 = 1779623) B1779623
theorem B793371 : Blo 790340 793371 := bstep (se 1 (by rfl) ⟨595028, by rfl⟩ : syracuseStep 793371 = 1190057) B1190057
theorem B793855 : Blo 790340 793855 := bstep (se 1 (by rfl) ⟨595391, by rfl⟩ : syracuseStep 793855 = 1190783) B1190783
theorem B794011 : Blo 790340 794011 := bstep (se 1 (by rfl) ⟨595508, by rfl⟩ : syracuseStep 794011 = 1191017) B1191017
theorem B1187231 : Blo 790340 1187231 := bstep (se 1 (by rfl) ⟨890423, by rfl⟩ : syracuseStep 1187231 = 1780847) B1780847
theorem B1187819 : Blo 790340 1187819 := bstep (se 1 (by rfl) ⟨890864, by rfl⟩ : syracuseStep 1187819 = 1781729) B1781729
theorem B1187867 : Blo 790340 1187867 := bstep (se 1 (by rfl) ⟨890900, by rfl⟩ : syracuseStep 1187867 = 1781801) B1781801
theorem B4629545 : Blo 790340 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B1778759 : Blo 790340 1778759 := bstep (se 1 (by rfl) ⟨1334069, by rfl⟩ : syracuseStep 1778759 = 2668139) B2668139
theorem B1189115 : Blo 790340 1189115 := bstep (se 1 (by rfl) ⟨891836, by rfl⟩ : syracuseStep 1189115 = 1783673) B1783673
theorem B1189241 : Blo 790340 1189241 := bstep (se 2 (by rfl) ⟨445965, by rfl⟩ : syracuseStep 1189241 = 891931) B891931
theorem B1779425 : Blo 790340 1779425 := bstep (se 2 (by rfl) ⟨667284, by rfl⟩ : syracuseStep 1779425 = 1334569) B1334569
theorem B1779839 : Blo 790340 1779839 := bstep (se 1 (by rfl) ⟨1334879, by rfl⟩ : syracuseStep 1779839 = 2669759) B2669759
theorem B1190555 : Blo 790340 1190555 := bstep (se 1 (by rfl) ⟨892916, by rfl⟩ : syracuseStep 1190555 = 1785833) B1785833
theorem B1190639 : Blo 790340 1190639 := bstep (se 1 (by rfl) ⟨892979, by rfl⟩ : syracuseStep 1190639 = 1785959) B1785959
theorem B1190687 : Blo 790340 1190687 := bstep (se 1 (by rfl) ⟨893015, by rfl⟩ : syracuseStep 1190687 = 1786031) B1786031
theorem B3615677 : Blo 790340 3615677 := bstep (se 3 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 3615677 = 1355879) B1355879
theorem B1781531 : Blo 790340 1781531 := bstep (se 1 (by rfl) ⟨1336148, by rfl⟩ : syracuseStep 1781531 = 2672297) B2672297
theorem B9646123 : Blo 790340 9646123 := bstep (se 1 (by rfl) ⟨7234592, by rfl⟩ : syracuseStep 9646123 = 14469185) B14469185
theorem B1781999 : Blo 790340 1781999 := bstep (se 1 (by rfl) ⟨1336499, by rfl⟩ : syracuseStep 1781999 = 2672999) B2672999
theorem B1783763 : Blo 790340 1783763 := bstep (se 1 (by rfl) ⟨1337822, by rfl⟩ : syracuseStep 1783763 = 2675645) B2675645
theorem B2146601 : Blo 790340 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B1786751 : Blo 790340 1786751 := bstep (se 1 (by rfl) ⟨1340063, by rfl⟩ : syracuseStep 1786751 = 2680127) B2680127
theorem B6767671 : Blo 790340 6767671 := bstep (se 1 (by rfl) ⟨5075753, by rfl⟩ : syracuseStep 6767671 = 10151507) B10151507
theorem B1001575 : Blo 790340 1001575 := bstep (se 1 (by rfl) ⟨751181, by rfl⟩ : syracuseStep 1001575 = 1502363) B1502363
theorem B1428479 : Blo 790340 1428479 := bstep (se 1 (by rfl) ⟨1071359, by rfl⟩ : syracuseStep 1428479 = 2142719) B2142719
theorem B8145983 : Blo 790340 8145983 := bstep (se 1 (by rfl) ⟨6109487, by rfl⟩ : syracuseStep 8145983 = 12218975) B12218975
theorem B4017599 : Blo 790340 4017599 := bstep (se 1 (by rfl) ⟨3013199, by rfl⟩ : syracuseStep 4017599 = 6026399) B6026399
theorem B9655037 : Blo 790340 9655037 := bstep (se 3 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 9655037 = 3620639) B3620639
theorem B24695945 : Blo 790340 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B1431103 : Blo 790340 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B7526135 : Blo 790340 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B1694447 : Blo 790340 1694447 := bstep (se 1 (by rfl) ⟨1270835, by rfl⟩ : syracuseStep 1694447 = 2541671) B2541671
theorem B4021001 : Blo 790340 4021001 := bstep (se 2 (by rfl) ⟨1507875, by rfl⟩ : syracuseStep 4021001 = 3015751) B3015751
theorem B9165707 : Blo 790340 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B1334441 : Blo 790340 1334441 := bstep (se 2 (by rfl) ⟨500415, by rfl⟩ : syracuseStep 1334441 = 1000831) B1000831
theorem B2252929 : Blo 790340 2252929 := bstep (se 2 (by rfl) ⟨844848, by rfl⟩ : syracuseStep 2252929 = 1689697) B1689697
theorem B11003177 : Blo 790340 11003177 := bstep (se 2 (by rfl) ⟨4126191, by rfl⟩ : syracuseStep 11003177 = 8252383) B8252383
theorem B7628393 : Blo 790340 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B2680559 : Blo 790340 2680559 := bstep (se 1 (by rfl) ⟨2010419, by rfl⟩ : syracuseStep 2680559 = 4020839) B4020839
theorem B3008735 : Blo 790340 3008735 := bstep (se 1 (by rfl) ⟨2256551, by rfl⟩ : syracuseStep 3008735 = 4513103) B4513103
theorem B846335 : Blo 790340 846335 := bstep (se 1 (by rfl) ⟨634751, by rfl⟩ : syracuseStep 846335 = 1269503) B1269503
theorem B30469283 : Blo 790340 30469283 := bstep (se 1 (by rfl) ⟨22851962, by rfl⟩ : syracuseStep 30469283 = 45703925) B45703925
theorem B7828175 : Blo 790340 7828175 := bstep (se 1 (by rfl) ⟨5871131, by rfl⟩ : syracuseStep 7828175 = 11742263) B11742263
theorem B2258351 : Blo 790340 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B1506023 : Blo 790340 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B19299455 : Blo 790340 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B4062383 : Blo 790340 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B2031551 : Blo 790340 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B5701691 : Blo 790340 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B2294783 : Blo 790340 2294783 := bstep (se 1 (by rfl) ⟨1721087, by rfl⟩ : syracuseStep 2294783 = 3442175) B3442175
theorem B20875133 : Blo 790340 20875133 := bstep (se 3 (by rfl) ⟨3914087, by rfl⟩ : syracuseStep 20875133 = 7828175) B7828175
theorem B952319 : Blo 790340 952319 := bstep (se 1 (by rfl) ⟨714239, by rfl⟩ : syracuseStep 952319 = 1428479) B1428479
theorem B14420873 : Blo 790340 14420873 := bstep (se 2 (by rfl) ⟨5407827, by rfl⟩ : syracuseStep 14420873 = 10815655) B10815655
theorem B5017423 : Blo 790340 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B790527 : Blo 790340 790527 := bstep (se 1 (by rfl) ⟨592895, by rfl⟩ : syracuseStep 790527 = 1185791) B1185791
theorem B790943 : Blo 790340 790943 := bstep (se 1 (by rfl) ⟨593207, by rfl⟩ : syracuseStep 790943 = 1186415) B1186415
theorem B889627 : Blo 790340 889627 := bstep (se 1 (by rfl) ⟨667220, by rfl⟩ : syracuseStep 889627 = 1334441) B1334441
theorem B791487 : Blo 790340 791487 := bstep (se 1 (by rfl) ⟨593615, by rfl⟩ : syracuseStep 791487 = 1187231) B1187231
theorem B791879 : Blo 790340 791879 := bstep (se 1 (by rfl) ⟨593909, by rfl⟩ : syracuseStep 791879 = 1187819) B1187819
theorem B791911 : Blo 790340 791911 := bstep (se 1 (by rfl) ⟨593933, by rfl⟩ : syracuseStep 791911 = 1187867) B1187867
theorem B3086363 : Blo 790340 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B1185833 : Blo 790340 1185833 := bstep (se 2 (by rfl) ⟨444687, by rfl⟩ : syracuseStep 1185833 = 889375) B889375
theorem B1185839 : Blo 790340 1185839 := bstep (se 1 (by rfl) ⟨889379, by rfl⟩ : syracuseStep 1185839 = 1778759) B1778759
theorem B17176697 : Blo 790340 17176697 := bstep (se 2 (by rfl) ⟨6441261, by rfl⟩ : syracuseStep 17176697 = 12882523) B12882523
theorem B792743 : Blo 790340 792743 := bstep (se 1 (by rfl) ⟨594557, by rfl⟩ : syracuseStep 792743 = 1189115) B1189115
theorem B792827 : Blo 790340 792827 := bstep (se 1 (by rfl) ⟨594620, by rfl⟩ : syracuseStep 792827 = 1189241) B1189241
theorem B5085595 : Blo 790340 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B1186283 : Blo 790340 1186283 := bstep (se 1 (by rfl) ⟨889712, by rfl⟩ : syracuseStep 1186283 = 1779425) B1779425
theorem B1186559 : Blo 790340 1186559 := bstep (se 1 (by rfl) ⟨889919, by rfl⟩ : syracuseStep 1186559 = 1779839) B1779839
theorem B2005823 : Blo 790340 2005823 := bstep (se 1 (by rfl) ⟨1504367, by rfl⟩ : syracuseStep 2005823 = 3008735) B3008735
theorem B793703 : Blo 790340 793703 := bstep (se 1 (by rfl) ⟨595277, by rfl⟩ : syracuseStep 793703 = 1190555) B1190555
theorem B793759 : Blo 790340 793759 := bstep (se 1 (by rfl) ⟨595319, by rfl⟩ : syracuseStep 793759 = 1190639) B1190639
theorem B793791 : Blo 790340 793791 := bstep (se 1 (by rfl) ⟨595343, by rfl⟩ : syracuseStep 793791 = 1190687) B1190687
theorem B1908137 : Blo 790340 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B1187687 : Blo 790340 1187687 := bstep (se 1 (by rfl) ⟨890765, by rfl⟩ : syracuseStep 1187687 = 1781531) B1781531
theorem B1187999 : Blo 790340 1187999 := bstep (se 1 (by rfl) ⟨890999, by rfl⟩ : syracuseStep 1187999 = 1781999) B1781999
theorem B1189175 : Blo 790340 1189175 := bstep (se 1 (by rfl) ⟨891881, by rfl⟩ : syracuseStep 1189175 = 1783763) B1783763
theorem B1354367 : Blo 790340 1354367 := bstep (se 1 (by rfl) ⟨1015775, by rfl⟩ : syracuseStep 1354367 = 2031551) B2031551
theorem B1191167 : Blo 790340 1191167 := bstep (se 1 (by rfl) ⟨893375, by rfl⟩ : syracuseStep 1191167 = 1786751) B1786751
theorem B3386879 : Blo 790340 3386879 := bstep (se 1 (by rfl) ⟨2540159, by rfl⟩ : syracuseStep 3386879 = 5080319) B5080319
theorem B9023561 : Blo 790340 9023561 := bstep (se 2 (by rfl) ⟨3383835, by rfl⟩ : syracuseStep 9023561 = 6767671) B6767671
theorem B9025019 : Blo 790340 9025019 := bstep (se 1 (by rfl) ⟨6768764, by rfl⟩ : syracuseStep 9025019 = 13537529) B13537529
theorem B6436691 : Blo 790340 6436691 := bstep (se 1 (by rfl) ⟨4827518, by rfl⟩ : syracuseStep 6436691 = 9655037) B9655037
theorem B2668409 : Blo 790340 2668409 := bstep (se 2 (by rfl) ⟨1000653, by rfl⟩ : syracuseStep 2668409 = 2001307) B2001307
theorem B6010847 : Blo 790340 6010847 := bstep (se 1 (by rfl) ⟨4508135, by rfl⟩ : syracuseStep 6010847 = 9016271) B9016271
theorem B16463963 : Blo 790340 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B2145055 : Blo 790340 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B2669705 : Blo 790340 2669705 := bstep (se 2 (by rfl) ⟨1001139, by rfl⟩ : syracuseStep 2669705 = 2002279) B2002279
theorem B1129631 : Blo 790340 1129631 := bstep (se 1 (by rfl) ⟨847223, by rfl⟩ : syracuseStep 1129631 = 1694447) B1694447
theorem B6110471 : Blo 790340 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B12861497 : Blo 790340 12861497 := bstep (se 2 (by rfl) ⟨4823061, by rfl⟩ : syracuseStep 12861497 = 9646123) B9646123
theorem B1787039 : Blo 790340 1787039 := bstep (se 1 (by rfl) ⟨1340279, by rfl⟩ : syracuseStep 1787039 = 2680559) B2680559
theorem B2410451 : Blo 790340 2410451 := bstep (se 1 (by rfl) ⟨1807838, by rfl⟩ : syracuseStep 2410451 = 3615677) B3615677
theorem B1004015 : Blo 790340 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B12866303 : Blo 790340 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B2708255 : Blo 790340 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B3003905 : Blo 790340 3003905 := bstep (se 2 (by rfl) ⟨1126464, by rfl⟩ : syracuseStep 3003905 = 2252929) B2252929
theorem B5724269 : Blo 790340 5724269 := bstep (se 3 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 5724269 = 2146601) B2146601
theorem B5430655 : Blo 790340 5430655 := bstep (se 1 (by rfl) ⟨4072991, by rfl⟩ : syracuseStep 5430655 = 8145983) B8145983
theorem B2678399 : Blo 790340 2678399 := bstep (se 1 (by rfl) ⟨2008799, by rfl⟩ : syracuseStep 2678399 = 4017599) B4017599
theorem B1269631 : Blo 790340 1269631 := bstep (se 1 (by rfl) ⟨952223, by rfl⟩ : syracuseStep 1269631 = 1904447) B1904447
theorem B1335271 : Blo 790340 1335271 := bstep (se 1 (by rfl) ⟨1001453, by rfl⟩ : syracuseStep 1335271 = 2002907) B2002907
theorem B1335433 : Blo 790340 1335433 := bstep (se 2 (by rfl) ⟨500787, by rfl⟩ : syracuseStep 1335433 = 1001575) B1001575
theorem B2680667 : Blo 790340 2680667 := bstep (se 1 (by rfl) ⟨2010500, by rfl⟩ : syracuseStep 2680667 = 4021001) B4021001
theorem B7335451 : Blo 790340 7335451 := bstep (se 1 (by rfl) ⟨5501588, by rfl⟩ : syracuseStep 7335451 = 11003177) B11003177
theorem B2256893 : Blo 790340 2256893 := bstep (se 3 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 2256893 = 846335) B846335
theorem B20312855 : Blo 790340 20312855 := bstep (se 1 (by rfl) ⟨15234641, by rfl⟩ : syracuseStep 20312855 = 30469283) B30469283
theorem B1505567 : Blo 790340 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B3801127 : Blo 790340 3801127 := bstep (se 1 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 3801127 = 5701691) B5701691
theorem B1606967 : Blo 790340 1606967 := bstep (se 1 (by rfl) ⟨1205225, by rfl⟩ : syracuseStep 1606967 = 2410451) B2410451
theorem B1805503 : Blo 790340 1805503 := bstep (se 1 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 1805503 = 2708255) B2708255
theorem B2002603 : Blo 790340 2002603 := bstep (se 1 (by rfl) ⟨1501952, by rfl⟩ : syracuseStep 2002603 = 3003905) B3003905
theorem B790555 : Blo 790340 790555 := bstep (se 1 (by rfl) ⟨592916, by rfl⟩ : syracuseStep 790555 = 1185833) B1185833
theorem B790559 : Blo 790340 790559 := bstep (se 1 (by rfl) ⟨592919, by rfl⟩ : syracuseStep 790559 = 1185839) B1185839
theorem B790855 : Blo 790340 790855 := bstep (se 1 (by rfl) ⟨593141, by rfl⟩ : syracuseStep 790855 = 1186283) B1186283
theorem B791039 : Blo 790340 791039 := bstep (se 1 (by rfl) ⟨593279, by rfl⟩ : syracuseStep 791039 = 1186559) B1186559
theorem B6689897 : Blo 790340 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B791791 : Blo 790340 791791 := bstep (se 1 (by rfl) ⟨593843, by rfl⟩ : syracuseStep 791791 = 1187687) B1187687
theorem B791999 : Blo 790340 791999 := bstep (se 1 (by rfl) ⟨593999, by rfl⟩ : syracuseStep 791999 = 1187999) B1187999
theorem B792783 : Blo 790340 792783 := bstep (se 1 (by rfl) ⟨594587, by rfl⟩ : syracuseStep 792783 = 1189175) B1189175
theorem B1186169 : Blo 790340 1186169 := bstep (se 2 (by rfl) ⟨444813, by rfl⟩ : syracuseStep 1186169 = 889627) B889627
theorem B794111 : Blo 790340 794111 := bstep (se 1 (by rfl) ⟨595583, by rfl⟩ : syracuseStep 794111 = 1191167) B1191167
theorem B13541903 : Blo 790340 13541903 := bstep (se 1 (by rfl) ⟨10156427, by rfl⟩ : syracuseStep 13541903 = 20312855) B20312855
theorem B2860073 : Blo 790340 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B5088365 : Blo 790340 5088365 := bstep (se 3 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 5088365 = 1908137) B1908137
theorem B1778939 : Blo 790340 1778939 := bstep (se 1 (by rfl) ⟨1334204, by rfl⟩ : syracuseStep 1778939 = 2668409) B2668409
theorem B4007231 : Blo 790340 4007231 := bstep (se 1 (by rfl) ⟨3005423, by rfl⟩ : syracuseStep 4007231 = 6010847) B6010847
theorem B1779803 : Blo 790340 1779803 := bstep (se 1 (by rfl) ⟨1334852, by rfl⟩ : syracuseStep 1779803 = 2669705) B2669705
theorem B4073647 : Blo 790340 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B1780361 : Blo 790340 1780361 := bstep (se 2 (by rfl) ⟨667635, by rfl⟩ : syracuseStep 1780361 = 1335271) B1335271
theorem B1780577 : Blo 790340 1780577 := bstep (se 2 (by rfl) ⟨667716, by rfl⟩ : syracuseStep 1780577 = 1335433) B1335433
theorem B1191359 : Blo 790340 1191359 := bstep (se 1 (by rfl) ⟨893519, by rfl⟩ : syracuseStep 1191359 = 1787039) B1787039
theorem B3816179 : Blo 790340 3816179 := bstep (se 1 (by rfl) ⟨2862134, by rfl⟩ : syracuseStep 3816179 = 5724269) B5724269
theorem B11451131 : Blo 790340 11451131 := bstep (se 1 (by rfl) ⟨8588348, by rfl⟩ : syracuseStep 11451131 = 17176697) B17176697
theorem B9780601 : Blo 790340 9780601 := bstep (se 2 (by rfl) ⟨3667725, by rfl⟩ : syracuseStep 9780601 = 7335451) B7335451
theorem B1785599 : Blo 790340 1785599 := bstep (se 1 (by rfl) ⟨1339199, by rfl⟩ : syracuseStep 1785599 = 2678399) B2678399
theorem B2539517 : Blo 790340 2539517 := bstep (se 3 (by rfl) ⟨476159, by rfl⟩ : syracuseStep 2539517 = 952319) B952319
theorem B4014845 : Blo 790340 4014845 := bstep (se 3 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 4014845 = 1505567) B1505567
theorem B1787111 : Blo 790340 1787111 := bstep (se 1 (by rfl) ⟨1340333, by rfl⟩ : syracuseStep 1787111 = 2680667) B2680667
theorem B902911 : Blo 790340 902911 := bstep (se 1 (by rfl) ⟨677183, by rfl⟩ : syracuseStep 902911 = 1354367) B1354367
theorem B38455661 : Blo 790340 38455661 := bstep (se 3 (by rfl) ⟨7210436, by rfl⟩ : syracuseStep 38455661 = 14420873) B14420873
theorem B6015707 : Blo 790340 6015707 := bstep (se 1 (by rfl) ⟨4511780, by rfl⟩ : syracuseStep 6015707 = 9023561) B9023561
theorem B6016679 : Blo 790340 6016679 := bstep (se 1 (by rfl) ⟨4512509, by rfl⟩ : syracuseStep 6016679 = 9025019) B9025019
theorem B1692841 : Blo 790340 1692841 := bstep (se 2 (by rfl) ⟨634815, by rfl⟩ : syracuseStep 1692841 = 1269631) B1269631
theorem B8574331 : Blo 790340 8574331 := bstep (se 1 (by rfl) ⟨6430748, by rfl⟩ : syracuseStep 8574331 = 12861497) B12861497
theorem B1529855 : Blo 790340 1529855 := bstep (se 1 (by rfl) ⟨1147391, by rfl⟩ : syracuseStep 1529855 = 2294783) B2294783
theorem B13916755 : Blo 790340 13916755 := bstep (se 1 (by rfl) ⟨10437566, by rfl⟩ : syracuseStep 13916755 = 20875133) B20875133
theorem B2677373 : Blo 790340 2677373 := bstep (se 3 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 2677373 = 1004015) B1004015
theorem B8577535 : Blo 790340 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B2057575 : Blo 790340 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B1337215 : Blo 790340 1337215 := bstep (se 1 (by rfl) ⟨1002911, by rfl⟩ : syracuseStep 1337215 = 2005823) B2005823
theorem B2257919 : Blo 790340 2257919 := bstep (se 1 (by rfl) ⟨1693439, by rfl⟩ : syracuseStep 2257919 = 3386879) B3386879
theorem B1504595 : Blo 790340 1504595 := bstep (se 1 (by rfl) ⟨1128446, by rfl⟩ : syracuseStep 1504595 = 2256893) B2256893
theorem B3012349 : Blo 790340 3012349 := bstep (se 3 (by rfl) ⟨564815, by rfl⟩ : syracuseStep 3012349 = 1129631) B1129631
theorem B6780793 : Blo 790340 6780793 := bstep (se 2 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 6780793 = 5085595) B5085595
theorem B4291127 : Blo 790340 4291127 := bstep (se 1 (by rfl) ⟨3218345, by rfl⟩ : syracuseStep 4291127 = 6436691) B6436691
theorem B10975975 : Blo 790340 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B7240873 : Blo 790340 7240873 := bstep (se 2 (by rfl) ⟨2715327, by rfl⟩ : syracuseStep 7240873 = 5430655) B5430655
theorem B11436713 : Blo 790340 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B4459931 : Blo 790340 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B1019903 : Blo 790340 1019903 := bstep (se 1 (by rfl) ⟨764927, by rfl⟩ : syracuseStep 1019903 = 1529855) B1529855
theorem B790779 : Blo 790340 790779 := bstep (se 1 (by rfl) ⟨593084, by rfl⟩ : syracuseStep 790779 = 1186169) B1186169
theorem B1906715 : Blo 790340 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B1185959 : Blo 790340 1185959 := bstep (se 1 (by rfl) ⟨889469, by rfl⟩ : syracuseStep 1185959 = 1778939) B1778939
theorem B1186535 : Blo 790340 1186535 := bstep (se 1 (by rfl) ⟨889901, by rfl⟩ : syracuseStep 1186535 = 1779803) B1779803
theorem B1186907 : Blo 790340 1186907 := bstep (se 1 (by rfl) ⟨890180, by rfl⟩ : syracuseStep 1186907 = 1780361) B1780361
theorem B1187051 : Blo 790340 1187051 := bstep (se 1 (by rfl) ⟨890288, by rfl⟩ : syracuseStep 1187051 = 1780577) B1780577
theorem B794239 : Blo 790340 794239 := bstep (se 1 (by rfl) ⟨595679, by rfl⟩ : syracuseStep 794239 = 1191359) B1191359
theorem B18555673 : Blo 790340 18555673 := bstep (se 2 (by rfl) ⟨6958377, by rfl⟩ : syracuseStep 18555673 = 13916755) B13916755
theorem B2860751 : Blo 790340 2860751 := bstep (se 1 (by rfl) ⟨2145563, by rfl⟩ : syracuseStep 2860751 = 4291127) B4291127
theorem B1190399 : Blo 790340 1190399 := bstep (se 1 (by rfl) ⟨892799, by rfl⟩ : syracuseStep 1190399 = 1785599) B1785599
theorem B1191407 : Blo 790340 1191407 := bstep (se 1 (by rfl) ⟨893555, by rfl⟩ : syracuseStep 1191407 = 1787111) B1787111
theorem B25637107 : Blo 790340 25637107 := bstep (se 1 (by rfl) ⟨19227830, by rfl⟩ : syracuseStep 25637107 = 38455661) B38455661
theorem B4010471 : Blo 790340 4010471 := bstep (se 1 (by rfl) ⟨3007853, by rfl⟩ : syracuseStep 4010471 = 6015707) B6015707
theorem B4011119 : Blo 790340 4011119 := bstep (se 1 (by rfl) ⟨3008339, by rfl⟩ : syracuseStep 4011119 = 6016679) B6016679
theorem B1782953 : Blo 790340 1782953 := bstep (se 2 (by rfl) ⟨668607, by rfl⟩ : syracuseStep 1782953 = 1337215) B1337215
theorem B4012253 : Blo 790340 4012253 := bstep (se 3 (by rfl) ⟨752297, by rfl⟩ : syracuseStep 4012253 = 1504595) B1504595
theorem B58538533 : Blo 790340 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B2407337 : Blo 790340 2407337 := bstep (se 2 (by rfl) ⟨902751, by rfl⟩ : syracuseStep 2407337 = 1805503) B1805503
theorem B1784915 : Blo 790340 1784915 := bstep (se 1 (by rfl) ⟨1338686, by rfl⟩ : syracuseStep 1784915 = 2677373) B2677373
theorem B2670137 : Blo 790340 2670137 := bstep (se 2 (by rfl) ⟨1001301, by rfl⟩ : syracuseStep 2670137 = 2002603) B2002603
theorem B9027935 : Blo 790340 9027935 := bstep (se 1 (by rfl) ⟨6770951, by rfl⟩ : syracuseStep 9027935 = 13541903) B13541903
theorem B3392243 : Blo 790340 3392243 := bstep (se 1 (by rfl) ⟨2544182, by rfl⟩ : syracuseStep 3392243 = 5088365) B5088365
theorem B2671487 : Blo 790340 2671487 := bstep (se 1 (by rfl) ⟨2003615, by rfl⟩ : syracuseStep 2671487 = 4007231) B4007231
theorem B4016465 : Blo 790340 4016465 := bstep (se 2 (by rfl) ⟨1506174, by rfl⟩ : syracuseStep 4016465 = 3012349) B3012349
theorem B9654497 : Blo 790340 9654497 := bstep (se 2 (by rfl) ⟨3620436, by rfl⟩ : syracuseStep 9654497 = 7240873) B7240873
theorem B2544119 : Blo 790340 2544119 := bstep (se 1 (by rfl) ⟨1908089, by rfl⟩ : syracuseStep 2544119 = 3816179) B3816179
theorem B6772045 : Blo 790340 6772045 := bstep (se 3 (by rfl) ⟨1269758, by rfl⟩ : syracuseStep 6772045 = 2539517) B2539517
theorem B5068169 : Blo 790340 5068169 := bstep (se 2 (by rfl) ⟨1900563, by rfl⟩ : syracuseStep 5068169 = 3801127) B3801127
theorem B2676563 : Blo 790340 2676563 := bstep (se 1 (by rfl) ⟨2007422, by rfl⟩ : syracuseStep 2676563 = 4014845) B4014845
theorem B1071311 : Blo 790340 1071311 := bstep (se 1 (by rfl) ⟨803483, by rfl⟩ : syracuseStep 1071311 = 1606967) B1606967
theorem B2743433 : Blo 790340 2743433 := bstep (se 2 (by rfl) ⟨1028787, by rfl⟩ : syracuseStep 2743433 = 2057575) B2057575
theorem B1203881 : Blo 790340 1203881 := bstep (se 2 (by rfl) ⟨451455, by rfl⟩ : syracuseStep 1203881 = 902911) B902911
theorem B5431529 : Blo 790340 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B2257121 : Blo 790340 2257121 := bstep (se 2 (by rfl) ⟨846420, by rfl⟩ : syracuseStep 2257121 = 1692841) B1692841
theorem B11432441 : Blo 790340 11432441 := bstep (se 2 (by rfl) ⟨4287165, by rfl⟩ : syracuseStep 11432441 = 8574331) B8574331
theorem B9041057 : Blo 790340 9041057 := bstep (se 2 (by rfl) ⟨3390396, by rfl⟩ : syracuseStep 9041057 = 6780793) B6780793
theorem B1505279 : Blo 790340 1505279 := bstep (se 1 (by rfl) ⟨1128959, by rfl⟩ : syracuseStep 1505279 = 2257919) B2257919
theorem B13040801 : Blo 790340 13040801 := bstep (se 2 (by rfl) ⟨4890300, by rfl⟩ : syracuseStep 13040801 = 9780601) B9780601
theorem B7634087 : Blo 790340 7634087 := bstep (se 1 (by rfl) ⟨5725565, by rfl⟩ : syracuseStep 7634087 = 11451131) B11451131
theorem B2261495 : Blo 790340 2261495 := bstep (se 1 (by rfl) ⟨1696121, by rfl⟩ : syracuseStep 2261495 = 3392243) B3392243
theorem B24740897 : Blo 790340 24740897 := bstep (se 2 (by rfl) ⟨9277836, by rfl⟩ : syracuseStep 24740897 = 18555673) B18555673
theorem B3378779 : Blo 790340 3378779 := bstep (se 1 (by rfl) ⟨2534084, by rfl⟩ : syracuseStep 3378779 = 5068169) B5068169
theorem B790639 : Blo 790340 790639 := bstep (se 1 (by rfl) ⟨592979, by rfl⟩ : syracuseStep 790639 = 1185959) B1185959
theorem B791023 : Blo 790340 791023 := bstep (se 1 (by rfl) ⟨593267, by rfl⟩ : syracuseStep 791023 = 1186535) B1186535
theorem B791271 : Blo 790340 791271 := bstep (se 1 (by rfl) ⟨593453, by rfl⟩ : syracuseStep 791271 = 1186907) B1186907
theorem B791367 : Blo 790340 791367 := bstep (se 1 (by rfl) ⟨593525, by rfl⟩ : syracuseStep 791367 = 1187051) B1187051
theorem B34182809 : Blo 790340 34182809 := bstep (se 2 (by rfl) ⟨12818553, by rfl⟩ : syracuseStep 34182809 = 25637107) B25637107
theorem B1907167 : Blo 790340 1907167 := bstep (se 1 (by rfl) ⟨1430375, by rfl⟩ : syracuseStep 1907167 = 2860751) B2860751
theorem B793599 : Blo 790340 793599 := bstep (se 1 (by rfl) ⟨595199, by rfl⟩ : syracuseStep 793599 = 1190399) B1190399
theorem B794271 : Blo 790340 794271 := bstep (se 1 (by rfl) ⟨595703, by rfl⟩ : syracuseStep 794271 = 1191407) B1191407
theorem B1188635 : Blo 790340 1188635 := bstep (se 1 (by rfl) ⟨891476, by rfl⟩ : syracuseStep 1188635 = 1782953) B1782953
theorem B1189943 : Blo 790340 1189943 := bstep (se 1 (by rfl) ⟨892457, by rfl⟩ : syracuseStep 1189943 = 1784915) B1784915
theorem B8693867 : Blo 790340 8693867 := bstep (se 1 (by rfl) ⟨6520400, by rfl⟩ : syracuseStep 8693867 = 13040801) B13040801
theorem B5089391 : Blo 790340 5089391 := bstep (se 1 (by rfl) ⟨3817043, by rfl⟩ : syracuseStep 5089391 = 7634087) B7634087
theorem B1780091 : Blo 790340 1780091 := bstep (se 1 (by rfl) ⟨1335068, by rfl⟩ : syracuseStep 1780091 = 2670137) B2670137
theorem B1780991 : Blo 790340 1780991 := bstep (se 1 (by rfl) ⟨1335743, by rfl⟩ : syracuseStep 1780991 = 2671487) B2671487
theorem B6436331 : Blo 790340 6436331 := bstep (se 1 (by rfl) ⟨4827248, by rfl⟩ : syracuseStep 6436331 = 9654497) B9654497
theorem B1784375 : Blo 790340 1784375 := bstep (se 1 (by rfl) ⟨1338281, by rfl⟩ : syracuseStep 1784375 = 2676563) B2676563
theorem B3621019 : Blo 790340 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B9029393 : Blo 790340 9029393 := bstep (se 2 (by rfl) ⟨3386022, by rfl⟩ : syracuseStep 9029393 = 6772045) B6772045
theorem B2673647 : Blo 790340 2673647 := bstep (se 1 (by rfl) ⟨2005235, by rfl⟩ : syracuseStep 2673647 = 4010471) B4010471
theorem B7621627 : Blo 790340 7621627 := bstep (se 1 (by rfl) ⟨5716220, by rfl⟩ : syracuseStep 7621627 = 11432441) B11432441
theorem B2674079 : Blo 790340 2674079 := bstep (se 1 (by rfl) ⟨2005559, by rfl⟩ : syracuseStep 2674079 = 4011119) B4011119
theorem B1003519 : Blo 790340 1003519 := bstep (se 1 (by rfl) ⟨752639, by rfl⟩ : syracuseStep 1003519 = 1505279) B1505279
theorem B2674835 : Blo 790340 2674835 := bstep (se 1 (by rfl) ⟨2006126, by rfl⟩ : syracuseStep 2674835 = 4012253) B4012253
theorem B6018623 : Blo 790340 6018623 := bstep (se 1 (by rfl) ⟨4513967, by rfl⟩ : syracuseStep 6018623 = 9027935) B9027935
theorem B7624475 : Blo 790340 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B2677643 : Blo 790340 2677643 := bstep (se 1 (by rfl) ⟨2008232, by rfl⟩ : syracuseStep 2677643 = 4016465) B4016465
theorem B11427317 : Blo 790340 11427317 := bstep (se 5 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 11427317 = 1071311) B1071311
theorem B2973287 : Blo 790340 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B1696079 : Blo 790340 1696079 := bstep (se 1 (by rfl) ⟨1272059, by rfl⟩ : syracuseStep 1696079 = 2544119) B2544119
theorem B1271143 : Blo 790340 1271143 := bstep (se 1 (by rfl) ⟨953357, by rfl⟩ : syracuseStep 1271143 = 1906715) B1906715
theorem B1828955 : Blo 790340 1828955 := bstep (se 1 (by rfl) ⟨1371716, by rfl⟩ : syracuseStep 1828955 = 2743433) B2743433
theorem B1504747 : Blo 790340 1504747 := bstep (se 1 (by rfl) ⟨1128560, by rfl⟩ : syracuseStep 1504747 = 2257121) B2257121
theorem B78051377 : Blo 790340 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B6027371 : Blo 790340 6027371 := bstep (se 1 (by rfl) ⟨4520528, by rfl⟩ : syracuseStep 6027371 = 9041057) B9041057
theorem B3210349 : Blo 790340 3210349 := bstep (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) B1203881
theorem B1604891 : Blo 790340 1604891 := bstep (se 1 (by rfl) ⟨1203668, by rfl⟩ : syracuseStep 1604891 = 2407337) B2407337
theorem B10878965 : Blo 790340 10878965 := bstep (se 5 (by rfl) ⟨509951, by rfl⟩ : syracuseStep 10878965 = 1019903) B1019903
theorem B1507663 : Blo 790340 1507663 := bstep (se 1 (by rfl) ⟨1130747, by rfl⟩ : syracuseStep 1507663 = 2261495) B2261495
theorem B4522877 : Blo 790340 4522877 := bstep (se 3 (by rfl) ⟨848039, by rfl⟩ : syracuseStep 4522877 = 1696079) B1696079
theorem B5082983 : Blo 790340 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B10162169 : Blo 790340 10162169 := bstep (se 2 (by rfl) ⟨3810813, by rfl⟩ : syracuseStep 10162169 = 7621627) B7621627
theorem B792423 : Blo 790340 792423 := bstep (se 1 (by rfl) ⟨594317, by rfl⟩ : syracuseStep 792423 = 1188635) B1188635
theorem B793295 : Blo 790340 793295 := bstep (se 1 (by rfl) ⟨594971, by rfl⟩ : syracuseStep 793295 = 1189943) B1189943
theorem B1219303 : Blo 790340 1219303 := bstep (se 1 (by rfl) ⟨914477, by rfl⟩ : syracuseStep 1219303 = 1828955) B1828955
theorem B1186727 : Blo 790340 1186727 := bstep (se 1 (by rfl) ⟨890045, by rfl⟩ : syracuseStep 1186727 = 1780091) B1780091
theorem B2006329 : Blo 790340 2006329 := bstep (se 2 (by rfl) ⟨752373, by rfl⟩ : syracuseStep 2006329 = 1504747) B1504747
theorem B1187327 : Blo 790340 1187327 := bstep (se 1 (by rfl) ⟨890495, by rfl⟩ : syracuseStep 1187327 = 1780991) B1780991
theorem B1189583 : Blo 790340 1189583 := bstep (se 1 (by rfl) ⟨892187, by rfl⟩ : syracuseStep 1189583 = 1784375) B1784375
theorem B7252643 : Blo 790340 7252643 := bstep (se 1 (by rfl) ⟨5439482, by rfl⟩ : syracuseStep 7252643 = 10878965) B10878965
theorem B4828025 : Blo 790340 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B1782431 : Blo 790340 1782431 := bstep (se 1 (by rfl) ⟨1336823, by rfl⟩ : syracuseStep 1782431 = 2673647) B2673647
theorem B1782719 : Blo 790340 1782719 := bstep (se 1 (by rfl) ⟨1337039, by rfl⟩ : syracuseStep 1782719 = 2674079) B2674079
theorem B65975725 : Blo 790340 65975725 := bstep (se 3 (by rfl) ⟨12370448, by rfl⟩ : syracuseStep 65975725 = 24740897) B24740897
theorem B1783223 : Blo 790340 1783223 := bstep (se 1 (by rfl) ⟨1337417, by rfl⟩ : syracuseStep 1783223 = 2674835) B2674835
theorem B4012415 : Blo 790340 4012415 := bstep (se 1 (by rfl) ⟨3009311, by rfl⟩ : syracuseStep 4012415 = 6018623) B6018623
theorem B22788539 : Blo 790340 22788539 := bstep (se 1 (by rfl) ⟨17091404, by rfl⟩ : syracuseStep 22788539 = 34182809) B34182809
theorem B1785095 : Blo 790340 1785095 := bstep (se 1 (by rfl) ⟨1338821, by rfl⟩ : syracuseStep 1785095 = 2677643) B2677643
theorem B7618211 : Blo 790340 7618211 := bstep (se 1 (by rfl) ⟨5713658, by rfl⟩ : syracuseStep 7618211 = 11427317) B11427317
theorem B3392927 : Blo 790340 3392927 := bstep (se 1 (by rfl) ⟨2544695, by rfl⟩ : syracuseStep 3392927 = 5089391) B5089391
theorem B2542889 : Blo 790340 2542889 := bstep (se 2 (by rfl) ⟨953583, by rfl⟩ : syracuseStep 2542889 = 1907167) B1907167
theorem B4279709 : Blo 790340 4279709 := bstep (se 3 (by rfl) ⟨802445, by rfl⟩ : syracuseStep 4279709 = 1604891) B1604891
theorem B4018247 : Blo 790340 4018247 := bstep (se 1 (by rfl) ⟨3013685, by rfl⟩ : syracuseStep 4018247 = 6027371) B6027371
theorem B4280465 : Blo 790340 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B6019595 : Blo 790340 6019595 := bstep (se 1 (by rfl) ⟨4514696, by rfl⟩ : syracuseStep 6019595 = 9029393) B9029393
theorem B1694857 : Blo 790340 1694857 := bstep (se 2 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 1694857 = 1271143) B1271143
theorem B2252519 : Blo 790340 2252519 := bstep (se 1 (by rfl) ⟨1689389, by rfl⟩ : syracuseStep 2252519 = 3378779) B3378779
theorem B1338025 : Blo 790340 1338025 := bstep (se 2 (by rfl) ⟨501759, by rfl⟩ : syracuseStep 1338025 = 1003519) B1003519
theorem B5795911 : Blo 790340 5795911 := bstep (se 1 (by rfl) ⟨4346933, by rfl⟩ : syracuseStep 5795911 = 8693867) B8693867
theorem B4290887 : Blo 790340 4290887 := bstep (se 1 (by rfl) ⟨3218165, by rfl⟩ : syracuseStep 4290887 = 6436331) B6436331
theorem B52034251 : Blo 790340 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B7928765 : Blo 790340 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B3015251 : Blo 790340 3015251 := bstep (se 1 (by rfl) ⟨2261438, by rfl⟩ : syracuseStep 3015251 = 4522877) B4522877
theorem B2261951 : Blo 790340 2261951 := bstep (se 1 (by rfl) ⟨1696463, by rfl⟩ : syracuseStep 2261951 = 3392927) B3392927
theorem B2853139 : Blo 790340 2853139 := bstep (se 1 (by rfl) ⟨2139854, by rfl⟩ : syracuseStep 2853139 = 4279709) B4279709
theorem B2853643 : Blo 790340 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B791151 : Blo 790340 791151 := bstep (se 1 (by rfl) ⟨593363, by rfl⟩ : syracuseStep 791151 = 1186727) B1186727
theorem B791551 : Blo 790340 791551 := bstep (se 1 (by rfl) ⟨593663, by rfl⟩ : syracuseStep 791551 = 1187327) B1187327
theorem B793055 : Blo 790340 793055 := bstep (se 1 (by rfl) ⟨594791, by rfl⟩ : syracuseStep 793055 = 1189583) B1189583
theorem B1188287 : Blo 790340 1188287 := bstep (se 1 (by rfl) ⟨891215, by rfl⟩ : syracuseStep 1188287 = 1782431) B1782431
theorem B1188479 : Blo 790340 1188479 := bstep (se 1 (by rfl) ⟨891359, by rfl⟩ : syracuseStep 1188479 = 1782719) B1782719
theorem B69379001 : Blo 790340 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B1188815 : Blo 790340 1188815 := bstep (se 1 (by rfl) ⟨891611, by rfl⟩ : syracuseStep 1188815 = 1783223) B1783223
theorem B2860591 : Blo 790340 2860591 := bstep (se 1 (by rfl) ⟨2145443, by rfl⟩ : syracuseStep 2860591 = 4290887) B4290887
theorem B5285843 : Blo 790340 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B1190063 : Blo 790340 1190063 := bstep (se 1 (by rfl) ⟨892547, by rfl⟩ : syracuseStep 1190063 = 1785095) B1785095
theorem B2010217 : Blo 790340 2010217 := bstep (se 2 (by rfl) ⟨753831, by rfl⟩ : syracuseStep 2010217 = 1507663) B1507663
theorem B3388655 : Blo 790340 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B1784033 : Blo 790340 1784033 := bstep (se 2 (by rfl) ⟨669012, by rfl⟩ : syracuseStep 1784033 = 1338025) B1338025
theorem B4013063 : Blo 790340 4013063 := bstep (se 1 (by rfl) ⟨3009797, by rfl⟩ : syracuseStep 4013063 = 6019595) B6019595
theorem B4835095 : Blo 790340 4835095 := bstep (se 1 (by rfl) ⟨3626321, by rfl⟩ : syracuseStep 4835095 = 7252643) B7252643
theorem B87967633 : Blo 790340 87967633 := bstep (se 2 (by rfl) ⟨32987862, by rfl⟩ : syracuseStep 87967633 = 65975725) B65975725
theorem B1625737 : Blo 790340 1625737 := bstep (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) B1219303
theorem B2674943 : Blo 790340 2674943 := bstep (se 1 (by rfl) ⟨2006207, by rfl⟩ : syracuseStep 2674943 = 4012415) B4012415
theorem B15192359 : Blo 790340 15192359 := bstep (se 1 (by rfl) ⟨11394269, by rfl⟩ : syracuseStep 15192359 = 22788539) B22788539
theorem B2675105 : Blo 790340 2675105 := bstep (se 2 (by rfl) ⟨1003164, by rfl⟩ : syracuseStep 2675105 = 2006329) B2006329
theorem B1695259 : Blo 790340 1695259 := bstep (se 1 (by rfl) ⟨1271444, by rfl⟩ : syracuseStep 1695259 = 2542889) B2542889
theorem B6774779 : Blo 790340 6774779 := bstep (se 1 (by rfl) ⟨5081084, by rfl⟩ : syracuseStep 6774779 = 10162169) B10162169
theorem B2678831 : Blo 790340 2678831 := bstep (se 1 (by rfl) ⟨2009123, by rfl⟩ : syracuseStep 2678831 = 4018247) B4018247
theorem B1501679 : Blo 790340 1501679 := bstep (se 1 (by rfl) ⟨1126259, by rfl⟩ : syracuseStep 1501679 = 2252519) B2252519
theorem B7727881 : Blo 790340 7727881 := bstep (se 2 (by rfl) ⟨2897955, by rfl⟩ : syracuseStep 7727881 = 5795911) B5795911
theorem B12874733 : Blo 790340 12874733 := bstep (se 3 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 12874733 = 4828025) B4828025
theorem B2259809 : Blo 790340 2259809 := bstep (se 2 (by rfl) ⟨847428, by rfl⟩ : syracuseStep 2259809 = 1694857) B1694857
theorem B5078807 : Blo 790340 5078807 := bstep (se 1 (by rfl) ⟨3809105, by rfl⟩ : syracuseStep 5078807 = 7618211) B7618211
theorem B1507967 : Blo 790340 1507967 := bstep (se 1 (by rfl) ⟨1130975, by rfl⟩ : syracuseStep 1507967 = 2261951) B2261951
theorem B10128239 : Blo 790340 10128239 := bstep (se 1 (by rfl) ⟨7596179, by rfl⟩ : syracuseStep 10128239 = 15192359) B15192359
theorem B3804185 : Blo 790340 3804185 := bstep (se 2 (by rfl) ⟨1426569, by rfl⟩ : syracuseStep 3804185 = 2853139) B2853139
theorem B3804857 : Blo 790340 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B2167649 : Blo 790340 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B792191 : Blo 790340 792191 := bstep (se 1 (by rfl) ⟨594143, by rfl⟩ : syracuseStep 792191 = 1188287) B1188287
theorem B792319 : Blo 790340 792319 := bstep (se 1 (by rfl) ⟨594239, by rfl⟩ : syracuseStep 792319 = 1188479) B1188479
theorem B792543 : Blo 790340 792543 := bstep (se 1 (by rfl) ⟨594407, by rfl⟩ : syracuseStep 792543 = 1188815) B1188815
theorem B4004477 : Blo 790340 4004477 := bstep (se 3 (by rfl) ⟨750839, by rfl⟩ : syracuseStep 4004477 = 1501679) B1501679
theorem B793375 : Blo 790340 793375 := bstep (se 1 (by rfl) ⟨595031, by rfl⟩ : syracuseStep 793375 = 1190063) B1190063
theorem B1189355 : Blo 790340 1189355 := bstep (se 1 (by rfl) ⟨892016, by rfl⟩ : syracuseStep 1189355 = 1784033) B1784033
theorem B3385871 : Blo 790340 3385871 := bstep (se 1 (by rfl) ⟨2539403, by rfl⟩ : syracuseStep 3385871 = 5078807) B5078807
theorem B2010167 : Blo 790340 2010167 := bstep (se 1 (by rfl) ⟨1507625, by rfl⟩ : syracuseStep 2010167 = 3015251) B3015251
theorem B3814121 : Blo 790340 3814121 := bstep (se 2 (by rfl) ⟨1430295, by rfl⟩ : syracuseStep 3814121 = 2860591) B2860591
theorem B117290177 : Blo 790340 117290177 := bstep (se 2 (by rfl) ⟨43983816, by rfl⟩ : syracuseStep 117290177 = 87967633) B87967633
theorem B1783295 : Blo 790340 1783295 := bstep (se 1 (by rfl) ⟨1337471, by rfl⟩ : syracuseStep 1783295 = 2674943) B2674943
theorem B1783403 : Blo 790340 1783403 := bstep (se 1 (by rfl) ⟨1337552, by rfl⟩ : syracuseStep 1783403 = 2675105) B2675105
theorem B10303841 : Blo 790340 10303841 := bstep (se 2 (by rfl) ⟨3863940, by rfl⟩ : syracuseStep 10303841 = 7727881) B7727881
theorem B1785887 : Blo 790340 1785887 := bstep (se 1 (by rfl) ⟨1339415, by rfl⟩ : syracuseStep 1785887 = 2678831) B2678831
theorem B46252667 : Blo 790340 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B3523895 : Blo 790340 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B2675375 : Blo 790340 2675375 := bstep (se 1 (by rfl) ⟨2006531, by rfl⟩ : syracuseStep 2675375 = 4013063) B4013063
theorem B2680289 : Blo 790340 2680289 := bstep (se 2 (by rfl) ⟨1005108, by rfl⟩ : syracuseStep 2680289 = 2010217) B2010217
theorem B4516519 : Blo 790340 4516519 := bstep (se 1 (by rfl) ⟨3387389, by rfl⟩ : syracuseStep 4516519 = 6774779) B6774779
theorem B8583155 : Blo 790340 8583155 := bstep (se 1 (by rfl) ⟨6437366, by rfl⟩ : syracuseStep 8583155 = 12874733) B12874733
theorem B2259103 : Blo 790340 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B25787173 : Blo 790340 25787173 := bstep (se 4 (by rfl) ⟨2417547, by rfl⟩ : syracuseStep 25787173 = 4835095) B4835095
theorem B1506539 : Blo 790340 1506539 := bstep (se 1 (by rfl) ⟨1129904, by rfl⟩ : syracuseStep 1506539 = 2259809) B2259809
theorem B2260345 : Blo 790340 2260345 := bstep (se 2 (by rfl) ⟨847629, by rfl⟩ : syracuseStep 2260345 = 1695259) B1695259
theorem B123340445 : Blo 790340 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B6752159 : Blo 790340 6752159 := bstep (se 1 (by rfl) ⟨5064119, by rfl⟩ : syracuseStep 6752159 = 10128239) B10128239
theorem B1445099 : Blo 790340 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B792903 : Blo 790340 792903 := bstep (se 1 (by rfl) ⟨594677, by rfl⟩ : syracuseStep 792903 = 1189355) B1189355
theorem B78193451 : Blo 790340 78193451 := bstep (se 1 (by rfl) ⟨58645088, by rfl⟩ : syracuseStep 78193451 = 117290177) B117290177
theorem B1188863 : Blo 790340 1188863 := bstep (se 1 (by rfl) ⟨891647, by rfl⟩ : syracuseStep 1188863 = 1783295) B1783295
theorem B34382897 : Blo 790340 34382897 := bstep (se 2 (by rfl) ⟨12893586, by rfl⟩ : syracuseStep 34382897 = 25787173) B25787173
theorem B1188935 : Blo 790340 1188935 := bstep (se 1 (by rfl) ⟨891701, by rfl⟩ : syracuseStep 1188935 = 1783403) B1783403
theorem B1190591 : Blo 790340 1190591 := bstep (se 1 (by rfl) ⟨892943, by rfl⟩ : syracuseStep 1190591 = 1785887) B1785887
theorem B2536123 : Blo 790340 2536123 := bstep (se 1 (by rfl) ⟨1902092, by rfl⟩ : syracuseStep 2536123 = 3804185) B3804185
theorem B2536571 : Blo 790340 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B1783583 : Blo 790340 1783583 := bstep (se 1 (by rfl) ⟨1337687, by rfl⟩ : syracuseStep 1783583 = 2675375) B2675375
theorem B2669651 : Blo 790340 2669651 := bstep (se 1 (by rfl) ⟨2002238, by rfl⟩ : syracuseStep 2669651 = 4004477) B4004477
theorem B1786859 : Blo 790340 1786859 := bstep (se 1 (by rfl) ⟨1340144, by rfl⟩ : syracuseStep 1786859 = 2680289) B2680289
theorem B2542747 : Blo 790340 2542747 := bstep (se 1 (by rfl) ⟨1907060, by rfl⟩ : syracuseStep 2542747 = 3814121) B3814121
theorem B4017437 : Blo 790340 4017437 := bstep (se 3 (by rfl) ⟨753269, by rfl⟩ : syracuseStep 4017437 = 1506539) B1506539
theorem B5722103 : Blo 790340 5722103 := bstep (se 1 (by rfl) ⟨4291577, by rfl⟩ : syracuseStep 5722103 = 8583155) B8583155
theorem B6869227 : Blo 790340 6869227 := bstep (se 1 (by rfl) ⟨5151920, by rfl⟩ : syracuseStep 6869227 = 10303841) B10303841
theorem B1005311 : Blo 790340 1005311 := bstep (se 1 (by rfl) ⟨753983, by rfl⟩ : syracuseStep 1005311 = 1507967) B1507967
theorem B2349263 : Blo 790340 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B6022025 : Blo 790340 6022025 := bstep (se 2 (by rfl) ⟨2258259, by rfl⟩ : syracuseStep 6022025 = 4516519) B4516519
theorem B2257247 : Blo 790340 2257247 := bstep (se 1 (by rfl) ⟨1692935, by rfl⟩ : syracuseStep 2257247 = 3385871) B3385871
theorem B1340111 : Blo 790340 1340111 := bstep (se 1 (by rfl) ⟨1005083, by rfl⟩ : syracuseStep 1340111 = 2010167) B2010167
theorem B3012137 : Blo 790340 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B3013793 : Blo 790340 3013793 := bstep (se 2 (by rfl) ⟨1130172, by rfl⟩ : syracuseStep 3013793 = 2260345) B2260345
theorem B792575 : Blo 790340 792575 := bstep (se 1 (by rfl) ⟨594431, by rfl⟩ : syracuseStep 792575 = 1188863) B1188863
theorem B792623 : Blo 790340 792623 := bstep (se 1 (by rfl) ⟨594467, by rfl⟩ : syracuseStep 792623 = 1188935) B1188935
theorem B3381497 : Blo 790340 3381497 := bstep (se 2 (by rfl) ⟨1268061, by rfl⟩ : syracuseStep 3381497 = 2536123) B2536123
theorem B793727 : Blo 790340 793727 := bstep (se 1 (by rfl) ⟨595295, by rfl⟩ : syracuseStep 793727 = 1190591) B1190591
theorem B893407 : Blo 790340 893407 := bstep (se 1 (by rfl) ⟨670055, by rfl⟩ : syracuseStep 893407 = 1340111) B1340111
theorem B2008091 : Blo 790340 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B1189055 : Blo 790340 1189055 := bstep (se 1 (by rfl) ⟨891791, by rfl⟩ : syracuseStep 1189055 = 1783583) B1783583
theorem B1779767 : Blo 790340 1779767 := bstep (se 1 (by rfl) ⟨1334825, by rfl⟩ : syracuseStep 1779767 = 2669651) B2669651
theorem B2009195 : Blo 790340 2009195 := bstep (se 1 (by rfl) ⟨1506896, by rfl⟩ : syracuseStep 2009195 = 3013793) B3013793
theorem B1191239 : Blo 790340 1191239 := bstep (se 1 (by rfl) ⟨893429, by rfl⟩ : syracuseStep 1191239 = 1786859) B1786859
theorem B82226963 : Blo 790340 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B4501439 : Blo 790340 4501439 := bstep (se 1 (by rfl) ⟨3376079, by rfl⟩ : syracuseStep 4501439 = 6752159) B6752159
theorem B3390329 : Blo 790340 3390329 := bstep (se 2 (by rfl) ⟨1271373, by rfl⟩ : syracuseStep 3390329 = 2542747) B2542747
theorem B9158969 : Blo 790340 9158969 := bstep (se 2 (by rfl) ⟨3434613, by rfl⟩ : syracuseStep 9158969 = 6869227) B6869227
theorem B4014683 : Blo 790340 4014683 := bstep (se 1 (by rfl) ⟨3011012, by rfl⟩ : syracuseStep 4014683 = 6022025) B6022025
theorem B22921931 : Blo 790340 22921931 := bstep (se 1 (by rfl) ⟨17191448, by rfl⟩ : syracuseStep 22921931 = 34382897) B34382897
theorem B3853597 : Blo 790340 3853597 := bstep (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) B1445099
theorem B1691047 : Blo 790340 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B15258941 : Blo 790340 15258941 := bstep (se 3 (by rfl) ⟨2861051, by rfl⟩ : syracuseStep 15258941 = 5722103) B5722103
theorem B2678291 : Blo 790340 2678291 := bstep (se 1 (by rfl) ⟨2008718, by rfl⟩ : syracuseStep 2678291 = 4017437) B4017437
theorem B1566175 : Blo 790340 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B2680829 : Blo 790340 2680829 := bstep (se 3 (by rfl) ⟨502655, by rfl⟩ : syracuseStep 2680829 = 1005311) B1005311
theorem B52128967 : Blo 790340 52128967 := bstep (se 1 (by rfl) ⟨39096725, by rfl⟩ : syracuseStep 52128967 = 78193451) B78193451
theorem B1504831 : Blo 790340 1504831 := bstep (se 1 (by rfl) ⟨1128623, by rfl⟩ : syracuseStep 1504831 = 2257247) B2257247
theorem B69505289 : Blo 790340 69505289 := bstep (se 2 (by rfl) ⟨26064483, by rfl⟩ : syracuseStep 69505289 = 52128967) B52128967
theorem B792703 : Blo 790340 792703 := bstep (se 1 (by rfl) ⟨594527, by rfl⟩ : syracuseStep 792703 = 1189055) B1189055
theorem B1186511 : Blo 790340 1186511 := bstep (se 1 (by rfl) ⟨889883, by rfl⟩ : syracuseStep 1186511 = 1779767) B1779767
theorem B2006441 : Blo 790340 2006441 := bstep (se 2 (by rfl) ⟨752415, by rfl⟩ : syracuseStep 2006441 = 1504831) B1504831
theorem B794159 : Blo 790340 794159 := bstep (se 1 (by rfl) ⟨595619, by rfl⟩ : syracuseStep 794159 = 1191239) B1191239
theorem B6105979 : Blo 790340 6105979 := bstep (se 1 (by rfl) ⟨4579484, by rfl⟩ : syracuseStep 6105979 = 9158969) B9158969
theorem B15281287 : Blo 790340 15281287 := bstep (se 1 (by rfl) ⟨11460965, by rfl⟩ : syracuseStep 15281287 = 22921931) B22921931
theorem B1191209 : Blo 790340 1191209 := bstep (se 2 (by rfl) ⟨446703, by rfl⟩ : syracuseStep 1191209 = 893407) B893407
theorem B10172627 : Blo 790340 10172627 := bstep (se 1 (by rfl) ⟨7629470, by rfl⟩ : syracuseStep 10172627 = 15258941) B15258941
theorem B1785527 : Blo 790340 1785527 := bstep (se 1 (by rfl) ⟨1339145, by rfl⟩ : syracuseStep 1785527 = 2678291) B2678291
theorem B1787219 : Blo 790340 1787219 := bstep (se 1 (by rfl) ⟨1340414, by rfl⟩ : syracuseStep 1787219 = 2680829) B2680829
theorem B3000959 : Blo 790340 3000959 := bstep (se 1 (by rfl) ⟨2250719, by rfl⟩ : syracuseStep 3000959 = 4501439) B4501439
theorem B2676455 : Blo 790340 2676455 := bstep (se 1 (by rfl) ⟨2007341, by rfl⟩ : syracuseStep 2676455 = 4014683) B4014683
theorem B2088233 : Blo 790340 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B2254331 : Blo 790340 2254331 := bstep (se 1 (by rfl) ⟨1690748, by rfl⟩ : syracuseStep 2254331 = 3381497) B3381497
theorem B5138129 : Blo 790340 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B2254729 : Blo 790340 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B1338727 : Blo 790340 1338727 := bstep (se 1 (by rfl) ⟨1004045, by rfl⟩ : syracuseStep 1338727 = 2008091) B2008091
theorem B1339463 : Blo 790340 1339463 := bstep (se 1 (by rfl) ⟨1004597, by rfl⟩ : syracuseStep 1339463 = 2009195) B2009195
theorem B54817975 : Blo 790340 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B2260219 : Blo 790340 2260219 := bstep (se 1 (by rfl) ⟨1695164, by rfl⟩ : syracuseStep 2260219 = 3390329) B3390329
theorem B2000639 : Blo 790340 2000639 := bstep (se 1 (by rfl) ⟨1500479, by rfl⟩ : syracuseStep 2000639 = 3000959) B3000959
theorem B46336859 : Blo 790340 46336859 := bstep (se 1 (by rfl) ⟨34752644, by rfl⟩ : syracuseStep 46336859 = 69505289) B69505289
theorem B791007 : Blo 790340 791007 := bstep (se 1 (by rfl) ⟨593255, by rfl⟩ : syracuseStep 791007 = 1186511) B1186511
theorem B81500197 : Blo 790340 81500197 := bstep (se 4 (by rfl) ⟨7640643, by rfl⟩ : syracuseStep 81500197 = 15281287) B15281287
theorem B794139 : Blo 790340 794139 := bstep (se 1 (by rfl) ⟨595604, by rfl⟩ : syracuseStep 794139 = 1191209) B1191209
theorem B892975 : Blo 790340 892975 := bstep (se 1 (by rfl) ⟨669731, by rfl⟩ : syracuseStep 892975 = 1339463) B1339463
theorem B1190351 : Blo 790340 1190351 := bstep (se 1 (by rfl) ⟨892763, by rfl⟩ : syracuseStep 1190351 = 1785527) B1785527
theorem B1191479 : Blo 790340 1191479 := bstep (se 1 (by rfl) ⟨893609, by rfl⟩ : syracuseStep 1191479 = 1787219) B1787219
theorem B1784303 : Blo 790340 1784303 := bstep (se 1 (by rfl) ⟨1338227, by rfl⟩ : syracuseStep 1784303 = 2676455) B2676455
theorem B8141305 : Blo 790340 8141305 := bstep (se 2 (by rfl) ⟨3052989, by rfl⟩ : syracuseStep 8141305 = 6105979) B6105979
theorem B1784969 : Blo 790340 1784969 := bstep (se 2 (by rfl) ⟨669363, by rfl⟩ : syracuseStep 1784969 = 1338727) B1338727
theorem B1392155 : Blo 790340 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B3425419 : Blo 790340 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B73090633 : Blo 790340 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B3006305 : Blo 790340 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B1337627 : Blo 790340 1337627 := bstep (se 1 (by rfl) ⟨1003220, by rfl⟩ : syracuseStep 1337627 = 2006441) B2006441
theorem B1502887 : Blo 790340 1502887 := bstep (se 1 (by rfl) ⟨1127165, by rfl⟩ : syracuseStep 1502887 = 2254331) B2254331
theorem B6781751 : Blo 790340 6781751 := bstep (se 1 (by rfl) ⟨5086313, by rfl⟩ : syracuseStep 6781751 = 10172627) B10172627
theorem B3013625 : Blo 790340 3013625 := bstep (se 2 (by rfl) ⟨1130109, by rfl⟩ : syracuseStep 3013625 = 2260219) B2260219
theorem B97454177 : Blo 790340 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B2003849 : Blo 790340 2003849 := bstep (se 2 (by rfl) ⟨751443, by rfl⟩ : syracuseStep 2003849 = 1502887) B1502887
theorem B2004203 : Blo 790340 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B891751 : Blo 790340 891751 := bstep (se 1 (by rfl) ⟨668813, by rfl⟩ : syracuseStep 891751 = 1337627) B1337627
theorem B793567 : Blo 790340 793567 := bstep (se 1 (by rfl) ⟨595175, by rfl⟩ : syracuseStep 793567 = 1190351) B1190351
theorem B794319 : Blo 790340 794319 := bstep (se 1 (by rfl) ⟨595739, by rfl⟩ : syracuseStep 794319 = 1191479) B1191479
theorem B108666929 : Blo 790340 108666929 := bstep (se 2 (by rfl) ⟨40750098, by rfl⟩ : syracuseStep 108666929 = 81500197) B81500197
theorem B10855073 : Blo 790340 10855073 := bstep (se 2 (by rfl) ⟨4070652, by rfl⟩ : syracuseStep 10855073 = 8141305) B8141305
theorem B1189535 : Blo 790340 1189535 := bstep (se 1 (by rfl) ⟨892151, by rfl⟩ : syracuseStep 1189535 = 1784303) B1784303
theorem B2009083 : Blo 790340 2009083 := bstep (se 1 (by rfl) ⟨1506812, by rfl⟩ : syracuseStep 2009083 = 3013625) B3013625
theorem B1189979 : Blo 790340 1189979 := bstep (se 1 (by rfl) ⟨892484, by rfl⟩ : syracuseStep 1189979 = 1784969) B1784969
theorem B928103 : Blo 790340 928103 := bstep (se 1 (by rfl) ⟨696077, by rfl⟩ : syracuseStep 928103 = 1392155) B1392155
theorem B1190633 : Blo 790340 1190633 := bstep (se 2 (by rfl) ⟨446487, by rfl⟩ : syracuseStep 1190633 = 892975) B892975
theorem B18268901 : Blo 790340 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B1333759 : Blo 790340 1333759 := bstep (se 1 (by rfl) ⟨1000319, by rfl⟩ : syracuseStep 1333759 = 2000639) B2000639
theorem B30891239 : Blo 790340 30891239 := bstep (se 1 (by rfl) ⟨23168429, by rfl⟩ : syracuseStep 30891239 = 46336859) B46336859
theorem B4521167 : Blo 790340 4521167 := bstep (se 1 (by rfl) ⟨3390875, by rfl⟩ : syracuseStep 4521167 = 6781751) B6781751
theorem B9899765 : Blo 790340 9899765 := bstep (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) B928103
theorem B793023 : Blo 790340 793023 := bstep (se 1 (by rfl) ⟨594767, by rfl⟩ : syracuseStep 793023 = 1189535) B1189535
theorem B793319 : Blo 790340 793319 := bstep (se 1 (by rfl) ⟨594989, by rfl⟩ : syracuseStep 793319 = 1189979) B1189979
theorem B793755 : Blo 790340 793755 := bstep (se 1 (by rfl) ⟨595316, by rfl⟩ : syracuseStep 793755 = 1190633) B1190633
theorem B1778345 : Blo 790340 1778345 := bstep (se 2 (by rfl) ⟨666879, by rfl⟩ : syracuseStep 1778345 = 1333759) B1333759
theorem B1189001 : Blo 790340 1189001 := bstep (se 2 (by rfl) ⟨445875, by rfl⟩ : syracuseStep 1189001 = 891751) B891751
theorem B20594159 : Blo 790340 20594159 := bstep (se 1 (by rfl) ⟨15445619, by rfl⟩ : syracuseStep 20594159 = 30891239) B30891239
theorem B12179267 : Blo 790340 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B64969451 : Blo 790340 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B2678777 : Blo 790340 2678777 := bstep (se 2 (by rfl) ⟨1004541, by rfl⟩ : syracuseStep 2678777 = 2009083) B2009083
theorem B1335899 : Blo 790340 1335899 := bstep (se 1 (by rfl) ⟨1001924, by rfl⟩ : syracuseStep 1335899 = 2003849) B2003849
theorem B1336135 : Blo 790340 1336135 := bstep (se 1 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 1336135 = 2004203) B2004203
theorem B72444619 : Blo 790340 72444619 := bstep (se 1 (by rfl) ⟨54333464, by rfl⟩ : syracuseStep 72444619 = 108666929) B108666929
theorem B7236715 : Blo 790340 7236715 := bstep (se 1 (by rfl) ⟨5427536, by rfl⟩ : syracuseStep 7236715 = 10855073) B10855073
theorem B3014111 : Blo 790340 3014111 := bstep (se 1 (by rfl) ⟨2260583, by rfl⟩ : syracuseStep 3014111 = 4521167) B4521167
theorem B890599 : Blo 790340 890599 := bstep (se 1 (by rfl) ⟨667949, by rfl⟩ : syracuseStep 890599 = 1335899) B1335899
theorem B1185563 : Blo 790340 1185563 := bstep (se 1 (by rfl) ⟨889172, by rfl⟩ : syracuseStep 1185563 = 1778345) B1778345
theorem B792667 : Blo 790340 792667 := bstep (se 1 (by rfl) ⟨594500, by rfl⟩ : syracuseStep 792667 = 1189001) B1189001
theorem B2009407 : Blo 790340 2009407 := bstep (se 1 (by rfl) ⟨1507055, by rfl⟩ : syracuseStep 2009407 = 3014111) B3014111
theorem B1781513 : Blo 790340 1781513 := bstep (se 2 (by rfl) ⟨668067, by rfl⟩ : syracuseStep 1781513 = 1336135) B1336135
theorem B6599843 : Blo 790340 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B9648953 : Blo 790340 9648953 := bstep (se 2 (by rfl) ⟨3618357, by rfl⟩ : syracuseStep 9648953 = 7236715) B7236715
theorem B1785851 : Blo 790340 1785851 := bstep (se 1 (by rfl) ⟨1339388, by rfl⟩ : syracuseStep 1785851 = 2678777) B2678777
theorem B96592825 : Blo 790340 96592825 := bstep (se 2 (by rfl) ⟨36222309, by rfl⟩ : syracuseStep 96592825 = 72444619) B72444619
theorem B8119511 : Blo 790340 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B43312967 : Blo 790340 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B13729439 : Blo 790340 13729439 := bstep (se 1 (by rfl) ⟨10297079, by rfl⟩ : syracuseStep 13729439 = 20594159) B20594159
theorem B790375 : Blo 790340 790375 := bstep (se 1 (by rfl) ⟨592781, by rfl⟩ : syracuseStep 790375 = 1185563) B1185563
theorem B5413007 : Blo 790340 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B28875311 : Blo 790340 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B1187465 : Blo 790340 1187465 := bstep (se 2 (by rfl) ⟨445299, by rfl⟩ : syracuseStep 1187465 = 890599) B890599
theorem B1187675 : Blo 790340 1187675 := bstep (se 1 (by rfl) ⟨890756, by rfl⟩ : syracuseStep 1187675 = 1781513) B1781513
theorem B4399895 : Blo 790340 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B6432635 : Blo 790340 6432635 := bstep (se 1 (by rfl) ⟨4824476, by rfl⟩ : syracuseStep 6432635 = 9648953) B9648953
theorem B9152959 : Blo 790340 9152959 := bstep (se 1 (by rfl) ⟨6864719, by rfl⟩ : syracuseStep 9152959 = 13729439) B13729439
theorem B1190567 : Blo 790340 1190567 := bstep (se 1 (by rfl) ⟨892925, by rfl⟩ : syracuseStep 1190567 = 1785851) B1785851
theorem B128790433 : Blo 790340 128790433 := bstep (se 2 (by rfl) ⟨48296412, by rfl⟩ : syracuseStep 128790433 = 96592825) B96592825
theorem B2679209 : Blo 790340 2679209 := bstep (se 2 (by rfl) ⟨1004703, by rfl⟩ : syracuseStep 2679209 = 2009407) B2009407
theorem B3608671 : Blo 790340 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B791643 : Blo 790340 791643 := bstep (se 1 (by rfl) ⟨593732, by rfl⟩ : syracuseStep 791643 = 1187465) B1187465
theorem B791783 : Blo 790340 791783 := bstep (se 1 (by rfl) ⟨593837, by rfl⟩ : syracuseStep 791783 = 1187675) B1187675
theorem B793711 : Blo 790340 793711 := bstep (se 1 (by rfl) ⟨595283, by rfl⟩ : syracuseStep 793711 = 1190567) B1190567
theorem B12203945 : Blo 790340 12203945 := bstep (se 2 (by rfl) ⟨4576479, by rfl⟩ : syracuseStep 12203945 = 9152959) B9152959
theorem B19250207 : Blo 790340 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B171720577 : Blo 790340 171720577 := bstep (se 2 (by rfl) ⟨64395216, by rfl⟩ : syracuseStep 171720577 = 128790433) B128790433
theorem B1786139 : Blo 790340 1786139 := bstep (se 1 (by rfl) ⟨1339604, by rfl⟩ : syracuseStep 1786139 = 2679209) B2679209
theorem B2933263 : Blo 790340 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B4288423 : Blo 790340 4288423 := bstep (se 1 (by rfl) ⟨3216317, by rfl⟩ : syracuseStep 4288423 = 6432635) B6432635
theorem B8135963 : Blo 790340 8135963 := bstep (se 1 (by rfl) ⟨6101972, by rfl⟩ : syracuseStep 8135963 = 12203945) B12203945
theorem B228960769 : Blo 790340 228960769 := bstep (se 2 (by rfl) ⟨85860288, by rfl⟩ : syracuseStep 228960769 = 171720577) B171720577
theorem B1190759 : Blo 790340 1190759 := bstep (se 1 (by rfl) ⟨893069, by rfl⟩ : syracuseStep 1190759 = 1786139) B1786139
theorem B3911017 : Blo 790340 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B5717897 : Blo 790340 5717897 := bstep (se 2 (by rfl) ⟨2144211, by rfl⟩ : syracuseStep 5717897 = 4288423) B4288423
theorem B12833471 : Blo 790340 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B4811561 : Blo 790340 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B8555647 : Blo 790340 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B5214689 : Blo 790340 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B793839 : Blo 790340 793839 := bstep (se 1 (by rfl) ⟨595379, by rfl⟩ : syracuseStep 793839 = 1190759) B1190759
theorem B3811931 : Blo 790340 3811931 := bstep (se 1 (by rfl) ⟨2858948, by rfl⟩ : syracuseStep 3811931 = 5717897) B5717897
theorem B305281025 : Blo 790340 305281025 := bstep (se 2 (by rfl) ⟨114480384, by rfl⟩ : syracuseStep 305281025 = 228960769) B228960769
theorem B5423975 : Blo 790340 5423975 := bstep (se 1 (by rfl) ⟨4067981, by rfl⟩ : syracuseStep 5423975 = 8135963) B8135963
theorem B3207707 : Blo 790340 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B3476459 : Blo 790340 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B11407529 : Blo 790340 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B2138471 : Blo 790340 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B3615983 : Blo 790340 3615983 := bstep (se 1 (by rfl) ⟨2711987, by rfl⟩ : syracuseStep 3615983 = 5423975) B5423975
theorem B2541287 : Blo 790340 2541287 := bstep (se 1 (by rfl) ⟨1905965, by rfl⟩ : syracuseStep 2541287 = 3811931) B3811931
theorem B203520683 : Blo 790340 203520683 := bstep (se 1 (by rfl) ⟨152640512, by rfl⟩ : syracuseStep 203520683 = 305281025) B305281025
theorem B7605019 : Blo 790340 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B1425647 : Blo 790340 1425647 := bstep (se 1 (by rfl) ⟨1069235, by rfl⟩ : syracuseStep 1425647 = 2138471) B2138471
theorem B2410655 : Blo 790340 2410655 := bstep (se 1 (by rfl) ⟨1807991, by rfl⟩ : syracuseStep 2410655 = 3615983) B3615983
theorem B135680455 : Blo 790340 135680455 := bstep (se 1 (by rfl) ⟨101760341, by rfl⟩ : syracuseStep 135680455 = 203520683) B203520683
theorem B1694191 : Blo 790340 1694191 := bstep (se 1 (by rfl) ⟨1270643, by rfl⟩ : syracuseStep 1694191 = 2541287) B2541287
theorem B9270557 : Blo 790340 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B3801725 : Blo 790340 3801725 := bstep (se 3 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 3801725 = 1425647) B1425647
theorem B6428413 : Blo 790340 6428413 := bstep (se 3 (by rfl) ⟨1205327, by rfl⟩ : syracuseStep 6428413 = 2410655) B2410655
theorem B10140025 : Blo 790340 10140025 := bstep (se 2 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 10140025 = 7605019) B7605019
theorem B6180371 : Blo 790340 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B180907273 : Blo 790340 180907273 := bstep (se 2 (by rfl) ⟨67840227, by rfl⟩ : syracuseStep 180907273 = 135680455) B135680455
theorem B2258921 : Blo 790340 2258921 := bstep (se 2 (by rfl) ⟨847095, by rfl⟩ : syracuseStep 2258921 = 1694191) B1694191
theorem B241209697 : Blo 790340 241209697 := bstep (se 2 (by rfl) ⟨90453636, by rfl⟩ : syracuseStep 241209697 = 180907273) B180907273
theorem B34284869 : Blo 790340 34284869 := bstep (se 4 (by rfl) ⟨3214206, by rfl⟩ : syracuseStep 34284869 = 6428413) B6428413
theorem B2534483 : Blo 790340 2534483 := bstep (se 1 (by rfl) ⟨1900862, by rfl⟩ : syracuseStep 2534483 = 3801725) B3801725
theorem B13520033 : Blo 790340 13520033 := bstep (se 2 (by rfl) ⟨5070012, by rfl⟩ : syracuseStep 13520033 = 10140025) B10140025
theorem B4120247 : Blo 790340 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B1505947 : Blo 790340 1505947 := bstep (se 1 (by rfl) ⟨1129460, by rfl⟩ : syracuseStep 1505947 = 2258921) B2258921
theorem B9013355 : Blo 790340 9013355 := bstep (se 1 (by rfl) ⟨6760016, by rfl⟩ : syracuseStep 9013355 = 13520033) B13520033
theorem B2007929 : Blo 790340 2007929 := bstep (se 2 (by rfl) ⟨752973, by rfl⟩ : syracuseStep 2007929 = 1505947) B1505947
theorem B22856579 : Blo 790340 22856579 := bstep (se 1 (by rfl) ⟨17142434, by rfl⟩ : syracuseStep 22856579 = 34284869) B34284869
theorem B1689655 : Blo 790340 1689655 := bstep (se 1 (by rfl) ⟨1267241, by rfl⟩ : syracuseStep 1689655 = 2534483) B2534483
theorem B2746831 : Blo 790340 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B321612929 : Blo 790340 321612929 := bstep (se 2 (by rfl) ⟨120604848, by rfl⟩ : syracuseStep 321612929 = 241209697) B241209697
theorem B15237719 : Blo 790340 15237719 := bstep (se 1 (by rfl) ⟨11428289, by rfl⟩ : syracuseStep 15237719 = 22856579) B22856579
theorem B214408619 : Blo 790340 214408619 := bstep (se 1 (by rfl) ⟨160806464, by rfl⟩ : syracuseStep 214408619 = 321612929) B321612929
theorem B6008903 : Blo 790340 6008903 := bstep (se 1 (by rfl) ⟨4506677, by rfl⟩ : syracuseStep 6008903 = 9013355) B9013355
theorem B2252873 : Blo 790340 2252873 := bstep (se 2 (by rfl) ⟨844827, by rfl⟩ : syracuseStep 2252873 = 1689655) B1689655
theorem B3662441 : Blo 790340 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B1338619 : Blo 790340 1338619 := bstep (se 1 (by rfl) ⟨1003964, by rfl⟩ : syracuseStep 1338619 = 2007929) B2007929
theorem B10158479 : Blo 790340 10158479 := bstep (se 1 (by rfl) ⟨7618859, by rfl⟩ : syracuseStep 10158479 = 15237719) B15237719
theorem B142939079 : Blo 790340 142939079 := bstep (se 1 (by rfl) ⟨107204309, by rfl⟩ : syracuseStep 142939079 = 214408619) B214408619
theorem B4005935 : Blo 790340 4005935 := bstep (se 1 (by rfl) ⟨3004451, by rfl⟩ : syracuseStep 4005935 = 6008903) B6008903
theorem B1784825 : Blo 790340 1784825 := bstep (se 2 (by rfl) ⟨669309, by rfl⟩ : syracuseStep 1784825 = 1338619) B1338619
theorem B2441627 : Blo 790340 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B1501915 : Blo 790340 1501915 := bstep (se 1 (by rfl) ⟨1126436, by rfl⟩ : syracuseStep 1501915 = 2252873) B2252873
theorem B95292719 : Blo 790340 95292719 := bstep (se 1 (by rfl) ⟨71469539, by rfl⟩ : syracuseStep 95292719 = 142939079) B142939079
theorem B2002553 : Blo 790340 2002553 := bstep (se 2 (by rfl) ⟨750957, by rfl⟩ : syracuseStep 2002553 = 1501915) B1501915
theorem B1189883 : Blo 790340 1189883 := bstep (se 1 (by rfl) ⟨892412, by rfl⟩ : syracuseStep 1189883 = 1784825) B1784825
theorem B2670623 : Blo 790340 2670623 := bstep (se 1 (by rfl) ⟨2002967, by rfl⟩ : syracuseStep 2670623 = 4005935) B4005935
theorem B6772319 : Blo 790340 6772319 := bstep (se 1 (by rfl) ⟨5079239, by rfl⟩ : syracuseStep 6772319 = 10158479) B10158479
theorem B1627751 : Blo 790340 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B1085167 : Blo 790340 1085167 := bstep (se 1 (by rfl) ⟨813875, by rfl⟩ : syracuseStep 1085167 = 1627751) B1627751
theorem B793255 : Blo 790340 793255 := bstep (se 1 (by rfl) ⟨594941, by rfl⟩ : syracuseStep 793255 = 1189883) B1189883
theorem B1780415 : Blo 790340 1780415 := bstep (se 1 (by rfl) ⟨1335311, by rfl⟩ : syracuseStep 1780415 = 2670623) B2670623
theorem B63528479 : Blo 790340 63528479 := bstep (se 1 (by rfl) ⟨47646359, by rfl⟩ : syracuseStep 63528479 = 95292719) B95292719
theorem B1335035 : Blo 790340 1335035 := bstep (se 1 (by rfl) ⟨1001276, by rfl⟩ : syracuseStep 1335035 = 2002553) B2002553
theorem B4514879 : Blo 790340 4514879 := bstep (se 1 (by rfl) ⟨3386159, by rfl⟩ : syracuseStep 4514879 = 6772319) B6772319
theorem B1446889 : Blo 790340 1446889 := bstep (se 2 (by rfl) ⟨542583, by rfl⟩ : syracuseStep 1446889 = 1085167) B1085167
theorem B890023 : Blo 790340 890023 := bstep (se 1 (by rfl) ⟨667517, by rfl⟩ : syracuseStep 890023 = 1335035) B1335035
theorem B1186943 : Blo 790340 1186943 := bstep (se 1 (by rfl) ⟨890207, by rfl⟩ : syracuseStep 1186943 = 1780415) B1780415
theorem B42352319 : Blo 790340 42352319 := bstep (se 1 (by rfl) ⟨31764239, by rfl⟩ : syracuseStep 42352319 = 63528479) B63528479
theorem B3009919 : Blo 790340 3009919 := bstep (se 1 (by rfl) ⟨2257439, by rfl⟩ : syracuseStep 3009919 = 4514879) B4514879
theorem B791295 : Blo 790340 791295 := bstep (se 1 (by rfl) ⟨593471, by rfl⟩ : syracuseStep 791295 = 1186943) B1186943
theorem B1186697 : Blo 790340 1186697 := bstep (se 2 (by rfl) ⟨445011, by rfl⟩ : syracuseStep 1186697 = 890023) B890023
theorem B4013225 : Blo 790340 4013225 := bstep (se 2 (by rfl) ⟨1504959, by rfl⟩ : syracuseStep 4013225 = 3009919) B3009919
theorem B112939517 : Blo 790340 112939517 := bstep (se 3 (by rfl) ⟨21176159, by rfl⟩ : syracuseStep 112939517 = 42352319) B42352319
theorem B1929185 : Blo 790340 1929185 := bstep (se 2 (by rfl) ⟨723444, by rfl⟩ : syracuseStep 1929185 = 1446889) B1446889
theorem B791131 : Blo 790340 791131 := bstep (se 1 (by rfl) ⟨593348, by rfl⟩ : syracuseStep 791131 = 1186697) B1186697
theorem B1286123 : Blo 790340 1286123 := bstep (se 1 (by rfl) ⟨964592, by rfl⟩ : syracuseStep 1286123 = 1929185) B1929185
theorem B2675483 : Blo 790340 2675483 := bstep (se 1 (by rfl) ⟨2006612, by rfl⟩ : syracuseStep 2675483 = 4013225) B4013225
theorem B75293011 : Blo 790340 75293011 := bstep (se 1 (by rfl) ⟨56469758, by rfl⟩ : syracuseStep 75293011 = 112939517) B112939517
theorem B1783655 : Blo 790340 1783655 := bstep (se 1 (by rfl) ⟨1337741, by rfl⟩ : syracuseStep 1783655 = 2675483) B2675483
theorem B3429661 : Blo 790340 3429661 := bstep (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) B1286123
theorem B100390681 : Blo 790340 100390681 := bstep (se 2 (by rfl) ⟨37646505, by rfl⟩ : syracuseStep 100390681 = 75293011) B75293011
theorem B1189103 : Blo 790340 1189103 := bstep (se 1 (by rfl) ⟨891827, by rfl⟩ : syracuseStep 1189103 = 1783655) B1783655
theorem B4572881 : Blo 790340 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B133854241 : Blo 790340 133854241 := bstep (se 2 (by rfl) ⟨50195340, by rfl⟩ : syracuseStep 133854241 = 100390681) B100390681
theorem B3048587 : Blo 790340 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B792735 : Blo 790340 792735 := bstep (se 1 (by rfl) ⟨594551, by rfl⟩ : syracuseStep 792735 = 1189103) B1189103
theorem B178472321 : Blo 790340 178472321 := bstep (se 2 (by rfl) ⟨66927120, by rfl⟩ : syracuseStep 178472321 = 133854241) B133854241
theorem B2032391 : Blo 790340 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B118981547 : Blo 790340 118981547 := bstep (se 1 (by rfl) ⟨89236160, by rfl⟩ : syracuseStep 118981547 = 178472321) B178472321
theorem B5419709 : Blo 790340 5419709 := bstep (se 3 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 5419709 = 2032391) B2032391
theorem B79321031 : Blo 790340 79321031 := bstep (se 1 (by rfl) ⟨59490773, by rfl⟩ : syracuseStep 79321031 = 118981547) B118981547
theorem B3613139 : Blo 790340 3613139 := bstep (se 1 (by rfl) ⟨2709854, by rfl⟩ : syracuseStep 3613139 = 5419709) B5419709
theorem B52880687 : Blo 790340 52880687 := bstep (se 1 (by rfl) ⟨39660515, by rfl⟩ : syracuseStep 52880687 = 79321031) B79321031
theorem B2408759 : Blo 790340 2408759 := bstep (se 1 (by rfl) ⟨1806569, by rfl⟩ : syracuseStep 2408759 = 3613139) B3613139
theorem B35253791 : Blo 790340 35253791 := bstep (se 1 (by rfl) ⟨26440343, by rfl⟩ : syracuseStep 35253791 = 52880687) B52880687
theorem B1605839 : Blo 790340 1605839 := bstep (se 1 (by rfl) ⟨1204379, by rfl⟩ : syracuseStep 1605839 = 2408759) B2408759
theorem B23502527 : Blo 790340 23502527 := bstep (se 1 (by rfl) ⟨17626895, by rfl⟩ : syracuseStep 23502527 = 35253791) B35253791
theorem B15668351 : Blo 790340 15668351 := bstep (se 1 (by rfl) ⟨11751263, by rfl⟩ : syracuseStep 15668351 = 23502527) B23502527
theorem B4282237 : Blo 790340 4282237 := bstep (se 3 (by rfl) ⟨802919, by rfl⟩ : syracuseStep 4282237 = 1605839) B1605839
theorem B5709649 : Blo 790340 5709649 := bstep (se 2 (by rfl) ⟨2141118, by rfl⟩ : syracuseStep 5709649 = 4282237) B4282237
theorem B10445567 : Blo 790340 10445567 := bstep (se 1 (by rfl) ⟨7834175, by rfl⟩ : syracuseStep 10445567 = 15668351) B15668351
theorem B111419381 : Blo 790340 111419381 := bstep (se 5 (by rfl) ⟨5222783, by rfl⟩ : syracuseStep 111419381 = 10445567) B10445567
theorem B7612865 : Blo 790340 7612865 := bstep (se 2 (by rfl) ⟨2854824, by rfl⟩ : syracuseStep 7612865 = 5709649) B5709649
theorem B74279587 : Blo 790340 74279587 := bstep (se 1 (by rfl) ⟨55709690, by rfl⟩ : syracuseStep 74279587 = 111419381) B111419381
theorem B5075243 : Blo 790340 5075243 := bstep (se 1 (by rfl) ⟨3806432, by rfl⟩ : syracuseStep 5075243 = 7612865) B7612865
theorem B3383495 : Blo 790340 3383495 := bstep (se 1 (by rfl) ⟨2537621, by rfl⟩ : syracuseStep 3383495 = 5075243) B5075243
theorem B99039449 : Blo 790340 99039449 := bstep (se 2 (by rfl) ⟨37139793, by rfl⟩ : syracuseStep 99039449 = 74279587) B74279587
theorem B2255663 : Blo 790340 2255663 := bstep (se 1 (by rfl) ⟨1691747, by rfl⟩ : syracuseStep 2255663 = 3383495) B3383495
theorem B264105197 : Blo 790340 264105197 := bstep (se 3 (by rfl) ⟨49519724, by rfl⟩ : syracuseStep 264105197 = 99039449) B99039449
theorem B176070131 : Blo 790340 176070131 := bstep (se 1 (by rfl) ⟨132052598, by rfl⟩ : syracuseStep 176070131 = 264105197) B264105197
theorem B1503775 : Blo 790340 1503775 := bstep (se 1 (by rfl) ⟨1127831, by rfl⟩ : syracuseStep 1503775 = 2255663) B2255663
theorem B117380087 : Blo 790340 117380087 := bstep (se 1 (by rfl) ⟨88035065, by rfl⟩ : syracuseStep 117380087 = 176070131) B176070131
theorem B2005033 : Blo 790340 2005033 := bstep (se 2 (by rfl) ⟨751887, by rfl⟩ : syracuseStep 2005033 = 1503775) B1503775
theorem B78253391 : Blo 790340 78253391 := bstep (se 1 (by rfl) ⟨58690043, by rfl⟩ : syracuseStep 78253391 = 117380087) B117380087
theorem B2673377 : Blo 790340 2673377 := bstep (se 2 (by rfl) ⟨1002516, by rfl⟩ : syracuseStep 2673377 = 2005033) B2005033
theorem B208675709 : Blo 790340 208675709 := bstep (se 3 (by rfl) ⟨39126695, by rfl⟩ : syracuseStep 208675709 = 78253391) B78253391
theorem B1782251 : Blo 790340 1782251 := bstep (se 1 (by rfl) ⟨1336688, by rfl⟩ : syracuseStep 1782251 = 2673377) B2673377
theorem B1188167 : Blo 790340 1188167 := bstep (se 1 (by rfl) ⟨891125, by rfl⟩ : syracuseStep 1188167 = 1782251) B1782251
theorem B139117139 : Blo 790340 139117139 := bstep (se 1 (by rfl) ⟨104337854, by rfl⟩ : syracuseStep 139117139 = 208675709) B208675709
theorem B792111 : Blo 790340 792111 := bstep (se 1 (by rfl) ⟨594083, by rfl⟩ : syracuseStep 792111 = 1188167) B1188167
theorem B92744759 : Blo 790340 92744759 := bstep (se 1 (by rfl) ⟨69558569, by rfl⟩ : syracuseStep 92744759 = 139117139) B139117139
theorem B61829839 : Blo 790340 61829839 := bstep (se 1 (by rfl) ⟨46372379, by rfl⟩ : syracuseStep 61829839 = 92744759) B92744759
theorem B82439785 : Blo 790340 82439785 := bstep (se 2 (by rfl) ⟨30914919, by rfl⟩ : syracuseStep 82439785 = 61829839) B61829839
theorem B109919713 : Blo 790340 109919713 := bstep (se 2 (by rfl) ⟨41219892, by rfl⟩ : syracuseStep 109919713 = 82439785) B82439785
theorem B146559617 : Blo 790340 146559617 := bstep (se 2 (by rfl) ⟨54959856, by rfl⟩ : syracuseStep 146559617 = 109919713) B109919713
theorem B97706411 : Blo 790340 97706411 := bstep (se 1 (by rfl) ⟨73279808, by rfl⟩ : syracuseStep 97706411 = 146559617) B146559617
theorem B65137607 : Blo 790340 65137607 := bstep (se 1 (by rfl) ⟨48853205, by rfl⟩ : syracuseStep 65137607 = 97706411) B97706411
theorem B43425071 : Blo 790340 43425071 := bstep (se 1 (by rfl) ⟨32568803, by rfl⟩ : syracuseStep 43425071 = 65137607) B65137607
theorem B28950047 : Blo 790340 28950047 := bstep (se 1 (by rfl) ⟨21712535, by rfl⟩ : syracuseStep 28950047 = 43425071) B43425071
theorem B19300031 : Blo 790340 19300031 := bstep (se 1 (by rfl) ⟨14475023, by rfl⟩ : syracuseStep 19300031 = 28950047) B28950047
theorem B12866687 : Blo 790340 12866687 := bstep (se 1 (by rfl) ⟨9650015, by rfl⟩ : syracuseStep 12866687 = 19300031) B19300031
theorem B8577791 : Blo 790340 8577791 := bstep (se 1 (by rfl) ⟨6433343, by rfl⟩ : syracuseStep 8577791 = 12866687) B12866687
theorem B5718527 : Blo 790340 5718527 := bstep (se 1 (by rfl) ⟨4288895, by rfl⟩ : syracuseStep 5718527 = 8577791) B8577791
theorem B3812351 : Blo 790340 3812351 := bstep (se 1 (by rfl) ⟨2859263, by rfl⟩ : syracuseStep 3812351 = 5718527) B5718527
theorem B10166269 : Blo 790340 10166269 := bstep (se 3 (by rfl) ⟨1906175, by rfl⟩ : syracuseStep 10166269 = 3812351) B3812351
theorem B13555025 : Blo 790340 13555025 := bstep (se 2 (by rfl) ⟨5083134, by rfl⟩ : syracuseStep 13555025 = 10166269) B10166269
theorem B9036683 : Blo 790340 9036683 := bstep (se 1 (by rfl) ⟨6777512, by rfl⟩ : syracuseStep 9036683 = 13555025) B13555025
theorem B6024455 : Blo 790340 6024455 := bstep (se 1 (by rfl) ⟨4518341, by rfl⟩ : syracuseStep 6024455 = 9036683) B9036683
theorem B4016303 : Blo 790340 4016303 := bstep (se 1 (by rfl) ⟨3012227, by rfl⟩ : syracuseStep 4016303 = 6024455) B6024455
theorem B2677535 : Blo 790340 2677535 := bstep (se 1 (by rfl) ⟨2008151, by rfl⟩ : syracuseStep 2677535 = 4016303) B4016303
theorem B1785023 : Blo 790340 1785023 := bstep (se 1 (by rfl) ⟨1338767, by rfl⟩ : syracuseStep 1785023 = 2677535) B2677535
theorem B1190015 : Blo 790340 1190015 := bstep (se 1 (by rfl) ⟨892511, by rfl⟩ : syracuseStep 1190015 = 1785023) B1785023
theorem B793343 : Blo 790340 793343 := bstep (se 1 (by rfl) ⟨595007, by rfl⟩ : syracuseStep 793343 = 1190015) B1190015

theorem C0 (j : ℕ) (h1 : 197585 ≤ j) (h2 : j ≤ 198284) : Blo 790340 (4 * j + 3) := by
  interval_cases j
  · exact B790343
  · exact B790347
  · exact B790351
  · exact B790355
  · exact B790359
  · exact B790363
  · exact B790367
  · exact B790371
  · exact B790375
  · exact B790379
  · exact B790383
  · exact B790387
  · exact B790391
  · exact B790395
  · exact B790399
  · exact B790403
  · exact B790407
  · exact B790411
  · exact B790415
  · exact B790419
  · exact B790423
  · exact B790427
  · exact B790431
  · exact B790435
  · exact B790439
  · exact B790443
  · exact B790447
  · exact B790451
  · exact B790455
  · exact B790459
  · exact B790463
  · exact B790467
  · exact B790471
  · exact B790475
  · exact B790479
  · exact B790483
  · exact B790487
  · exact B790491
  · exact B790495
  · exact B790499
  · exact B790503
  · exact B790507
  · exact B790511
  · exact B790515
  · exact B790519
  · exact B790523
  · exact B790527
  · exact B790531
  · exact B790535
  · exact B790539
  · exact B790543
  · exact B790547
  · exact B790551
  · exact B790555
  · exact B790559
  · exact B790563
  · exact B790567
  · exact B790571
  · exact B790575
  · exact B790579
  · exact B790583
  · exact B790587
  · exact B790591
  · exact B790595
  · exact B790599
  · exact B790603
  · exact B790607
  · exact B790611
  · exact B790615
  · exact B790619
  · exact B790623
  · exact B790627
  · exact B790631
  · exact B790635
  · exact B790639
  · exact B790643
  · exact B790647
  · exact B790651
  · exact B790655
  · exact B790659
  · exact B790663
  · exact B790667
  · exact B790671
  · exact B790675
  · exact B790679
  · exact B790683
  · exact B790687
  · exact B790691
  · exact B790695
  · exact B790699
  · exact B790703
  · exact B790707
  · exact B790711
  · exact B790715
  · exact B790719
  · exact B790723
  · exact B790727
  · exact B790731
  · exact B790735
  · exact B790739
  · exact B790743
  · exact B790747
  · exact B790751
  · exact B790755
  · exact B790759
  · exact B790763
  · exact B790767
  · exact B790771
  · exact B790775
  · exact B790779
  · exact B790783
  · exact B790787
  · exact B790791
  · exact B790795
  · exact B790799
  · exact B790803
  · exact B790807
  · exact B790811
  · exact B790815
  · exact B790819
  · exact B790823
  · exact B790827
  · exact B790831
  · exact B790835
  · exact B790839
  · exact B790843
  · exact B790847
  · exact B790851
  · exact B790855
  · exact B790859
  · exact B790863
  · exact B790867
  · exact B790871
  · exact B790875
  · exact B790879
  · exact B790883
  · exact B790887
  · exact B790891
  · exact B790895
  · exact B790899
  · exact B790903
  · exact B790907
  · exact B790911
  · exact B790915
  · exact B790919
  · exact B790923
  · exact B790927
  · exact B790931
  · exact B790935
  · exact B790939
  · exact B790943
  · exact B790947
  · exact B790951
  · exact B790955
  · exact B790959
  · exact B790963
  · exact B790967
  · exact B790971
  · exact B790975
  · exact B790979
  · exact B790983
  · exact B790987
  · exact B790991
  · exact B790995
  · exact B790999
  · exact B791003
  · exact B791007
  · exact B791011
  · exact B791015
  · exact B791019
  · exact B791023
  · exact B791027
  · exact B791031
  · exact B791035
  · exact B791039
  · exact B791043
  · exact B791047
  · exact B791051
  · exact B791055
  · exact B791059
  · exact B791063
  · exact B791067
  · exact B791071
  · exact B791075
  · exact B791079
  · exact B791083
  · exact B791087
  · exact B791091
  · exact B791095
  · exact B791099
  · exact B791103
  · exact B791107
  · exact B791111
  · exact B791115
  · exact B791119
  · exact B791123
  · exact B791127
  · exact B791131
  · exact B791135
  · exact B791139
  · exact B791143
  · exact B791147
  · exact B791151
  · exact B791155
  · exact B791159
  · exact B791163
  · exact B791167
  · exact B791171
  · exact B791175
  · exact B791179
  · exact B791183
  · exact B791187
  · exact B791191
  · exact B791195
  · exact B791199
  · exact B791203
  · exact B791207
  · exact B791211
  · exact B791215
  · exact B791219
  · exact B791223
  · exact B791227
  · exact B791231
  · exact B791235
  · exact B791239
  · exact B791243
  · exact B791247
  · exact B791251
  · exact B791255
  · exact B791259
  · exact B791263
  · exact B791267
  · exact B791271
  · exact B791275
  · exact B791279
  · exact B791283
  · exact B791287
  · exact B791291
  · exact B791295
  · exact B791299
  · exact B791303
  · exact B791307
  · exact B791311
  · exact B791315
  · exact B791319
  · exact B791323
  · exact B791327
  · exact B791331
  · exact B791335
  · exact B791339
  · exact B791343
  · exact B791347
  · exact B791351
  · exact B791355
  · exact B791359
  · exact B791363
  · exact B791367
  · exact B791371
  · exact B791375
  · exact B791379
  · exact B791383
  · exact B791387
  · exact B791391
  · exact B791395
  · exact B791399
  · exact B791403
  · exact B791407
  · exact B791411
  · exact B791415
  · exact B791419
  · exact B791423
  · exact B791427
  · exact B791431
  · exact B791435
  · exact B791439
  · exact B791443
  · exact B791447
  · exact B791451
  · exact B791455
  · exact B791459
  · exact B791463
  · exact B791467
  · exact B791471
  · exact B791475
  · exact B791479
  · exact B791483
  · exact B791487
  · exact B791491
  · exact B791495
  · exact B791499
  · exact B791503
  · exact B791507
  · exact B791511
  · exact B791515
  · exact B791519
  · exact B791523
  · exact B791527
  · exact B791531
  · exact B791535
  · exact B791539
  · exact B791543
  · exact B791547
  · exact B791551
  · exact B791555
  · exact B791559
  · exact B791563
  · exact B791567
  · exact B791571
  · exact B791575
  · exact B791579
  · exact B791583
  · exact B791587
  · exact B791591
  · exact B791595
  · exact B791599
  · exact B791603
  · exact B791607
  · exact B791611
  · exact B791615
  · exact B791619
  · exact B791623
  · exact B791627
  · exact B791631
  · exact B791635
  · exact B791639
  · exact B791643
  · exact B791647
  · exact B791651
  · exact B791655
  · exact B791659
  · exact B791663
  · exact B791667
  · exact B791671
  · exact B791675
  · exact B791679
  · exact B791683
  · exact B791687
  · exact B791691
  · exact B791695
  · exact B791699
  · exact B791703
  · exact B791707
  · exact B791711
  · exact B791715
  · exact B791719
  · exact B791723
  · exact B791727
  · exact B791731
  · exact B791735
  · exact B791739
  · exact B791743
  · exact B791747
  · exact B791751
  · exact B791755
  · exact B791759
  · exact B791763
  · exact B791767
  · exact B791771
  · exact B791775
  · exact B791779
  · exact B791783
  · exact B791787
  · exact B791791
  · exact B791795
  · exact B791799
  · exact B791803
  · exact B791807
  · exact B791811
  · exact B791815
  · exact B791819
  · exact B791823
  · exact B791827
  · exact B791831
  · exact B791835
  · exact B791839
  · exact B791843
  · exact B791847
  · exact B791851
  · exact B791855
  · exact B791859
  · exact B791863
  · exact B791867
  · exact B791871
  · exact B791875
  · exact B791879
  · exact B791883
  · exact B791887
  · exact B791891
  · exact B791895
  · exact B791899
  · exact B791903
  · exact B791907
  · exact B791911
  · exact B791915
  · exact B791919
  · exact B791923
  · exact B791927
  · exact B791931
  · exact B791935
  · exact B791939
  · exact B791943
  · exact B791947
  · exact B791951
  · exact B791955
  · exact B791959
  · exact B791963
  · exact B791967
  · exact B791971
  · exact B791975
  · exact B791979
  · exact B791983
  · exact B791987
  · exact B791991
  · exact B791995
  · exact B791999
  · exact B792003
  · exact B792007
  · exact B792011
  · exact B792015
  · exact B792019
  · exact B792023
  · exact B792027
  · exact B792031
  · exact B792035
  · exact B792039
  · exact B792043
  · exact B792047
  · exact B792051
  · exact B792055
  · exact B792059
  · exact B792063
  · exact B792067
  · exact B792071
  · exact B792075
  · exact B792079
  · exact B792083
  · exact B792087
  · exact B792091
  · exact B792095
  · exact B792099
  · exact B792103
  · exact B792107
  · exact B792111
  · exact B792115
  · exact B792119
  · exact B792123
  · exact B792127
  · exact B792131
  · exact B792135
  · exact B792139
  · exact B792143
  · exact B792147
  · exact B792151
  · exact B792155
  · exact B792159
  · exact B792163
  · exact B792167
  · exact B792171
  · exact B792175
  · exact B792179
  · exact B792183
  · exact B792187
  · exact B792191
  · exact B792195
  · exact B792199
  · exact B792203
  · exact B792207
  · exact B792211
  · exact B792215
  · exact B792219
  · exact B792223
  · exact B792227
  · exact B792231
  · exact B792235
  · exact B792239
  · exact B792243
  · exact B792247
  · exact B792251
  · exact B792255
  · exact B792259
  · exact B792263
  · exact B792267
  · exact B792271
  · exact B792275
  · exact B792279
  · exact B792283
  · exact B792287
  · exact B792291
  · exact B792295
  · exact B792299
  · exact B792303
  · exact B792307
  · exact B792311
  · exact B792315
  · exact B792319
  · exact B792323
  · exact B792327
  · exact B792331
  · exact B792335
  · exact B792339
  · exact B792343
  · exact B792347
  · exact B792351
  · exact B792355
  · exact B792359
  · exact B792363
  · exact B792367
  · exact B792371
  · exact B792375
  · exact B792379
  · exact B792383
  · exact B792387
  · exact B792391
  · exact B792395
  · exact B792399
  · exact B792403
  · exact B792407
  · exact B792411
  · exact B792415
  · exact B792419
  · exact B792423
  · exact B792427
  · exact B792431
  · exact B792435
  · exact B792439
  · exact B792443
  · exact B792447
  · exact B792451
  · exact B792455
  · exact B792459
  · exact B792463
  · exact B792467
  · exact B792471
  · exact B792475
  · exact B792479
  · exact B792483
  · exact B792487
  · exact B792491
  · exact B792495
  · exact B792499
  · exact B792503
  · exact B792507
  · exact B792511
  · exact B792515
  · exact B792519
  · exact B792523
  · exact B792527
  · exact B792531
  · exact B792535
  · exact B792539
  · exact B792543
  · exact B792547
  · exact B792551
  · exact B792555
  · exact B792559
  · exact B792563
  · exact B792567
  · exact B792571
  · exact B792575
  · exact B792579
  · exact B792583
  · exact B792587
  · exact B792591
  · exact B792595
  · exact B792599
  · exact B792603
  · exact B792607
  · exact B792611
  · exact B792615
  · exact B792619
  · exact B792623
  · exact B792627
  · exact B792631
  · exact B792635
  · exact B792639
  · exact B792643
  · exact B792647
  · exact B792651
  · exact B792655
  · exact B792659
  · exact B792663
  · exact B792667
  · exact B792671
  · exact B792675
  · exact B792679
  · exact B792683
  · exact B792687
  · exact B792691
  · exact B792695
  · exact B792699
  · exact B792703
  · exact B792707
  · exact B792711
  · exact B792715
  · exact B792719
  · exact B792723
  · exact B792727
  · exact B792731
  · exact B792735
  · exact B792739
  · exact B792743
  · exact B792747
  · exact B792751
  · exact B792755
  · exact B792759
  · exact B792763
  · exact B792767
  · exact B792771
  · exact B792775
  · exact B792779
  · exact B792783
  · exact B792787
  · exact B792791
  · exact B792795
  · exact B792799
  · exact B792803
  · exact B792807
  · exact B792811
  · exact B792815
  · exact B792819
  · exact B792823
  · exact B792827
  · exact B792831
  · exact B792835
  · exact B792839
  · exact B792843
  · exact B792847
  · exact B792851
  · exact B792855
  · exact B792859
  · exact B792863
  · exact B792867
  · exact B792871
  · exact B792875
  · exact B792879
  · exact B792883
  · exact B792887
  · exact B792891
  · exact B792895
  · exact B792899
  · exact B792903
  · exact B792907
  · exact B792911
  · exact B792915
  · exact B792919
  · exact B792923
  · exact B792927
  · exact B792931
  · exact B792935
  · exact B792939
  · exact B792943
  · exact B792947
  · exact B792951
  · exact B792955
  · exact B792959
  · exact B792963
  · exact B792967
  · exact B792971
  · exact B792975
  · exact B792979
  · exact B792983
  · exact B792987
  · exact B792991
  · exact B792995
  · exact B792999
  · exact B793003
  · exact B793007
  · exact B793011
  · exact B793015
  · exact B793019
  · exact B793023
  · exact B793027
  · exact B793031
  · exact B793035
  · exact B793039
  · exact B793043
  · exact B793047
  · exact B793051
  · exact B793055
  · exact B793059
  · exact B793063
  · exact B793067
  · exact B793071
  · exact B793075
  · exact B793079
  · exact B793083
  · exact B793087
  · exact B793091
  · exact B793095
  · exact B793099
  · exact B793103
  · exact B793107
  · exact B793111
  · exact B793115
  · exact B793119
  · exact B793123
  · exact B793127
  · exact B793131
  · exact B793135
  · exact B793139

theorem C1 (j : ℕ) (h1 : 198285 ≤ j) (h2 : j ≤ 198584) : Blo 790340 (4 * j + 3) := by
  interval_cases j
  · exact B793143
  · exact B793147
  · exact B793151
  · exact B793155
  · exact B793159
  · exact B793163
  · exact B793167
  · exact B793171
  · exact B793175
  · exact B793179
  · exact B793183
  · exact B793187
  · exact B793191
  · exact B793195
  · exact B793199
  · exact B793203
  · exact B793207
  · exact B793211
  · exact B793215
  · exact B793219
  · exact B793223
  · exact B793227
  · exact B793231
  · exact B793235
  · exact B793239
  · exact B793243
  · exact B793247
  · exact B793251
  · exact B793255
  · exact B793259
  · exact B793263
  · exact B793267
  · exact B793271
  · exact B793275
  · exact B793279
  · exact B793283
  · exact B793287
  · exact B793291
  · exact B793295
  · exact B793299
  · exact B793303
  · exact B793307
  · exact B793311
  · exact B793315
  · exact B793319
  · exact B793323
  · exact B793327
  · exact B793331
  · exact B793335
  · exact B793339
  · exact B793343
  · exact B793347
  · exact B793351
  · exact B793355
  · exact B793359
  · exact B793363
  · exact B793367
  · exact B793371
  · exact B793375
  · exact B793379
  · exact B793383
  · exact B793387
  · exact B793391
  · exact B793395
  · exact B793399
  · exact B793403
  · exact B793407
  · exact B793411
  · exact B793415
  · exact B793419
  · exact B793423
  · exact B793427
  · exact B793431
  · exact B793435
  · exact B793439
  · exact B793443
  · exact B793447
  · exact B793451
  · exact B793455
  · exact B793459
  · exact B793463
  · exact B793467
  · exact B793471
  · exact B793475
  · exact B793479
  · exact B793483
  · exact B793487
  · exact B793491
  · exact B793495
  · exact B793499
  · exact B793503
  · exact B793507
  · exact B793511
  · exact B793515
  · exact B793519
  · exact B793523
  · exact B793527
  · exact B793531
  · exact B793535
  · exact B793539
  · exact B793543
  · exact B793547
  · exact B793551
  · exact B793555
  · exact B793559
  · exact B793563
  · exact B793567
  · exact B793571
  · exact B793575
  · exact B793579
  · exact B793583
  · exact B793587
  · exact B793591
  · exact B793595
  · exact B793599
  · exact B793603
  · exact B793607
  · exact B793611
  · exact B793615
  · exact B793619
  · exact B793623
  · exact B793627
  · exact B793631
  · exact B793635
  · exact B793639
  · exact B793643
  · exact B793647
  · exact B793651
  · exact B793655
  · exact B793659
  · exact B793663
  · exact B793667
  · exact B793671
  · exact B793675
  · exact B793679
  · exact B793683
  · exact B793687
  · exact B793691
  · exact B793695
  · exact B793699
  · exact B793703
  · exact B793707
  · exact B793711
  · exact B793715
  · exact B793719
  · exact B793723
  · exact B793727
  · exact B793731
  · exact B793735
  · exact B793739
  · exact B793743
  · exact B793747
  · exact B793751
  · exact B793755
  · exact B793759
  · exact B793763
  · exact B793767
  · exact B793771
  · exact B793775
  · exact B793779
  · exact B793783
  · exact B793787
  · exact B793791
  · exact B793795
  · exact B793799
  · exact B793803
  · exact B793807
  · exact B793811
  · exact B793815
  · exact B793819
  · exact B793823
  · exact B793827
  · exact B793831
  · exact B793835
  · exact B793839
  · exact B793843
  · exact B793847
  · exact B793851
  · exact B793855
  · exact B793859
  · exact B793863
  · exact B793867
  · exact B793871
  · exact B793875
  · exact B793879
  · exact B793883
  · exact B793887
  · exact B793891
  · exact B793895
  · exact B793899
  · exact B793903
  · exact B793907
  · exact B793911
  · exact B793915
  · exact B793919
  · exact B793923
  · exact B793927
  · exact B793931
  · exact B793935
  · exact B793939
  · exact B793943
  · exact B793947
  · exact B793951
  · exact B793955
  · exact B793959
  · exact B793963
  · exact B793967
  · exact B793971
  · exact B793975
  · exact B793979
  · exact B793983
  · exact B793987
  · exact B793991
  · exact B793995
  · exact B793999
  · exact B794003
  · exact B794007
  · exact B794011
  · exact B794015
  · exact B794019
  · exact B794023
  · exact B794027
  · exact B794031
  · exact B794035
  · exact B794039
  · exact B794043
  · exact B794047
  · exact B794051
  · exact B794055
  · exact B794059
  · exact B794063
  · exact B794067
  · exact B794071
  · exact B794075
  · exact B794079
  · exact B794083
  · exact B794087
  · exact B794091
  · exact B794095
  · exact B794099
  · exact B794103
  · exact B794107
  · exact B794111
  · exact B794115
  · exact B794119
  · exact B794123
  · exact B794127
  · exact B794131
  · exact B794135
  · exact B794139
  · exact B794143
  · exact B794147
  · exact B794151
  · exact B794155
  · exact B794159
  · exact B794163
  · exact B794167
  · exact B794171
  · exact B794175
  · exact B794179
  · exact B794183
  · exact B794187
  · exact B794191
  · exact B794195
  · exact B794199
  · exact B794203
  · exact B794207
  · exact B794211
  · exact B794215
  · exact B794219
  · exact B794223
  · exact B794227
  · exact B794231
  · exact B794235
  · exact B794239
  · exact B794243
  · exact B794247
  · exact B794251
  · exact B794255
  · exact B794259
  · exact B794263
  · exact B794267
  · exact B794271
  · exact B794275
  · exact B794279
  · exact B794283
  · exact B794287
  · exact B794291
  · exact B794295
  · exact B794299
  · exact B794303
  · exact B794307
  · exact B794311
  · exact B794315
  · exact B794319
  · exact B794323
  · exact B794327
  · exact B794331
  · exact B794335
  · exact B794339

theorem solution (m : ℕ) (hlo : 790340 ≤ m) (hhi : m ≤ 794340) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 197585 ≤ j := by omega
    have hj2 : j ≤ 198584 := by omega
    have hb : Blo 790340 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 198285 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
