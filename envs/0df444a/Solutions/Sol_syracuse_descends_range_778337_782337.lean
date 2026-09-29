-- Prove2me | solution 1 for syracuse_descends_range_778337_782337
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:26.145678+00:00
-- url     : https://prove2.me/submissions/2787a146-4ab2-49ee-beb8-acc36e5201c4

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


theorem B2818309 : Blo 778337 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B1802549 : Blo 778337 1802549 := bbase (se 5 (by rfl) ⟨84494, by rfl⟩ : syracuseStep 1802549 = 168989) (by norm_num)
theorem B1409501 : Blo 778337 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B1016329 : Blo 778337 1016329 := bbase (se 2 (by rfl) ⟨381123, by rfl⟩ : syracuseStep 1016329 = 762247) (by norm_num)
theorem B7111253 : Blo 778337 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B1999613 : Blo 778337 1999613 := bbase (se 3 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 1999613 = 749855) (by norm_num)
theorem B3801941 : Blo 778337 3801941 := bbase (se 9 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 3801941 = 22277) (by norm_num)
theorem B3999013 : Blo 778337 3999013 := bbase (se 4 (by rfl) ⟨374907, by rfl⟩ : syracuseStep 3999013 = 749815) (by norm_num)
theorem B1246757 : Blo 778337 1246757 := bbase (se 4 (by rfl) ⟨116883, by rfl⟩ : syracuseStep 1246757 = 233767) (by norm_num)
theorem B985117 : Blo 778337 985117 := bbase (se 3 (by rfl) ⟨184709, by rfl⟩ : syracuseStep 985117 = 369419) (by norm_num)
theorem B854069 : Blo 778337 854069 := bbase (se 5 (by rfl) ⟨40034, by rfl⟩ : syracuseStep 854069 = 80069) (by norm_num)
theorem B985213 : Blo 778337 985213 := bbase (se 3 (by rfl) ⟨184727, by rfl⟩ : syracuseStep 985213 = 369455) (by norm_num)
theorem B985385 : Blo 778337 985385 := bbase (se 2 (by rfl) ⟨369519, by rfl⟩ : syracuseStep 985385 = 739039) (by norm_num)
theorem B985441 : Blo 778337 985441 := bbase (se 2 (by rfl) ⟨369540, by rfl⟩ : syracuseStep 985441 = 739081) (by norm_num)
theorem B985537 : Blo 778337 985537 := bbase (se 2 (by rfl) ⟨369576, by rfl⟩ : syracuseStep 985537 = 739153) (by norm_num)
theorem B3213877 : Blo 778337 3213877 := bbase (se 5 (by rfl) ⟨150650, by rfl⟩ : syracuseStep 3213877 = 301301) (by norm_num)
theorem B2001469 : Blo 778337 2001469 := bbase (se 3 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 2001469 = 750551) (by norm_num)
theorem B985709 : Blo 778337 985709 := bbase (se 3 (by rfl) ⟨184820, by rfl⟩ : syracuseStep 985709 = 369641) (by norm_num)
theorem B985765 : Blo 778337 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B1313509 : Blo 778337 1313509 := bbase (se 4 (by rfl) ⟨123141, by rfl⟩ : syracuseStep 1313509 = 246283) (by norm_num)
theorem B985861 : Blo 778337 985861 := bbase (se 4 (by rfl) ⟨92424, by rfl⟩ : syracuseStep 985861 = 184849) (by norm_num)
theorem B1313597 : Blo 778337 1313597 := bbase (se 3 (by rfl) ⟨246299, by rfl⟩ : syracuseStep 1313597 = 492599) (by norm_num)
theorem B1248077 : Blo 778337 1248077 := bbase (se 3 (by rfl) ⟨234014, by rfl⟩ : syracuseStep 1248077 = 468029) (by norm_num)
theorem B887645 : Blo 778337 887645 := bbase (se 3 (by rfl) ⟨166433, by rfl⟩ : syracuseStep 887645 = 332867) (by norm_num)
theorem B986033 : Blo 778337 986033 := bbase (se 2 (by rfl) ⟨369762, by rfl⟩ : syracuseStep 986033 = 739525) (by norm_num)
theorem B1313725 : Blo 778337 1313725 := bbase (se 3 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 1313725 = 492647) (by norm_num)
theorem B1248205 : Blo 778337 1248205 := bbase (se 3 (by rfl) ⟨234038, by rfl⟩ : syracuseStep 1248205 = 468077) (by norm_num)
theorem B986089 : Blo 778337 986089 := bbase (se 2 (by rfl) ⟨369783, by rfl⟩ : syracuseStep 986089 = 739567) (by norm_num)
theorem B1313813 : Blo 778337 1313813 := bbase (se 6 (by rfl) ⟨30792, by rfl⟩ : syracuseStep 1313813 = 61585) (by norm_num)
theorem B1870877 : Blo 778337 1870877 := bbase (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) (by norm_num)
theorem B1870885 : Blo 778337 1870885 := bbase (se 4 (by rfl) ⟨175395, by rfl⟩ : syracuseStep 1870885 = 350791) (by norm_num)
theorem B986185 : Blo 778337 986185 := bbase (se 2 (by rfl) ⟨369819, by rfl⟩ : syracuseStep 986185 = 739639) (by norm_num)
theorem B1313941 : Blo 778337 1313941 := bbase (se 6 (by rfl) ⟨30795, by rfl⟩ : syracuseStep 1313941 = 61591) (by norm_num)
theorem B1314029 : Blo 778337 1314029 := bbase (se 3 (by rfl) ⟨246380, by rfl⟩ : syracuseStep 1314029 = 492761) (by norm_num)
theorem B888049 : Blo 778337 888049 := bbase (se 2 (by rfl) ⟨333018, by rfl⟩ : syracuseStep 888049 = 666037) (by norm_num)
theorem B986357 : Blo 778337 986357 := bbase (se 5 (by rfl) ⟨46235, by rfl⟩ : syracuseStep 986357 = 92471) (by norm_num)
theorem B986413 : Blo 778337 986413 := bbase (se 3 (by rfl) ⟨184952, by rfl⟩ : syracuseStep 986413 = 369905) (by norm_num)
theorem B1314157 : Blo 778337 1314157 := bbase (se 3 (by rfl) ⟨246404, by rfl⟩ : syracuseStep 1314157 = 492809) (by norm_num)
theorem B986509 : Blo 778337 986509 := bbase (se 3 (by rfl) ⟨184970, by rfl⟩ : syracuseStep 986509 = 369941) (by norm_num)
theorem B1314245 : Blo 778337 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B1478101 : Blo 778337 1478101 := bbase (se 7 (by rfl) ⟨17321, by rfl⟩ : syracuseStep 1478101 = 34643) (by norm_num)
theorem B888341 : Blo 778337 888341 := bbase (se 6 (by rfl) ⟨20820, by rfl⟩ : syracuseStep 888341 = 41641) (by norm_num)
theorem B986681 : Blo 778337 986681 := bbase (se 2 (by rfl) ⟨370005, by rfl⟩ : syracuseStep 986681 = 740011) (by norm_num)
theorem B1314373 : Blo 778337 1314373 := bbase (se 4 (by rfl) ⟨123222, by rfl⟩ : syracuseStep 1314373 = 246445) (by norm_num)
theorem B1478245 : Blo 778337 1478245 := bbase (se 4 (by rfl) ⟨138585, by rfl⟩ : syracuseStep 1478245 = 277171) (by norm_num)
theorem B986737 : Blo 778337 986737 := bbase (se 2 (by rfl) ⟨370026, by rfl⟩ : syracuseStep 986737 = 740053) (by norm_num)
theorem B1314461 : Blo 778337 1314461 := bbase (se 3 (by rfl) ⟨246461, by rfl⟩ : syracuseStep 1314461 = 492923) (by norm_num)
theorem B2002589 : Blo 778337 2002589 := bbase (se 3 (by rfl) ⟨375485, by rfl⟩ : syracuseStep 2002589 = 750971) (by norm_num)
theorem B986833 : Blo 778337 986833 := bbase (se 2 (by rfl) ⟨370062, by rfl⟩ : syracuseStep 986833 = 740125) (by norm_num)
theorem B1249013 : Blo 778337 1249013 := bbase (se 5 (by rfl) ⟨58547, by rfl⟩ : syracuseStep 1249013 = 117095) (by norm_num)
theorem B1478405 : Blo 778337 1478405 := bbase (se 4 (by rfl) ⟨138600, by rfl⟩ : syracuseStep 1478405 = 277201) (by norm_num)
theorem B1314589 : Blo 778337 1314589 := bbase (se 3 (by rfl) ⟨246485, by rfl⟩ : syracuseStep 1314589 = 492971) (by norm_num)
theorem B1314677 : Blo 778337 1314677 := bbase (se 5 (by rfl) ⟨61625, by rfl⟩ : syracuseStep 1314677 = 123251) (by norm_num)
theorem B987005 : Blo 778337 987005 := bbase (se 3 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 987005 = 370127) (by norm_num)
theorem B1478549 : Blo 778337 1478549 := bbase (se 6 (by rfl) ⟨34653, by rfl⟩ : syracuseStep 1478549 = 69307) (by norm_num)
theorem B855973 : Blo 778337 855973 := bbase (se 4 (by rfl) ⟨80247, by rfl⟩ : syracuseStep 855973 = 160495) (by norm_num)
theorem B987061 : Blo 778337 987061 := bbase (se 5 (by rfl) ⟨46268, by rfl⟩ : syracuseStep 987061 = 92537) (by norm_num)
theorem B1314805 : Blo 778337 1314805 := bbase (se 5 (by rfl) ⟨61631, by rfl⟩ : syracuseStep 1314805 = 123263) (by norm_num)
theorem B1871885 : Blo 778337 1871885 := bbase (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) (by norm_num)
theorem B1249301 : Blo 778337 1249301 := bbase (se 6 (by rfl) ⟨29280, by rfl⟩ : syracuseStep 1249301 = 58561) (by norm_num)
theorem B987157 : Blo 778337 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B1314893 : Blo 778337 1314893 := bbase (se 3 (by rfl) ⟨246542, by rfl⟩ : syracuseStep 1314893 = 493085) (by norm_num)
theorem B1478837 : Blo 778337 1478837 := bbase (se 5 (by rfl) ⟨69320, by rfl⟩ : syracuseStep 1478837 = 138641) (by norm_num)
theorem B1970365 : Blo 778337 1970365 := bbase (se 3 (by rfl) ⟨369443, by rfl⟩ : syracuseStep 1970365 = 738887) (by norm_num)
theorem B987329 : Blo 778337 987329 := bbase (se 2 (by rfl) ⟨370248, by rfl⟩ : syracuseStep 987329 = 740497) (by norm_num)
theorem B1315021 : Blo 778337 1315021 := bbase (se 3 (by rfl) ⟨246566, by rfl⟩ : syracuseStep 1315021 = 493133) (by norm_num)
theorem B790769 : Blo 778337 790769 := bbase (se 2 (by rfl) ⟨296538, by rfl⟩ : syracuseStep 790769 = 593077) (by norm_num)
theorem B987385 : Blo 778337 987385 := bbase (se 2 (by rfl) ⟨370269, by rfl⟩ : syracuseStep 987385 = 740539) (by norm_num)
theorem B1315109 : Blo 778337 1315109 := bbase (se 4 (by rfl) ⟨123291, by rfl⟩ : syracuseStep 1315109 = 246583) (by norm_num)
theorem B1970477 : Blo 778337 1970477 := bbase (se 3 (by rfl) ⟨369464, by rfl⟩ : syracuseStep 1970477 = 738929) (by norm_num)
theorem B1478989 : Blo 778337 1478989 := bbase (se 3 (by rfl) ⟨277310, by rfl⟩ : syracuseStep 1478989 = 554621) (by norm_num)
theorem B987481 : Blo 778337 987481 := bbase (se 2 (by rfl) ⟨370305, by rfl⟩ : syracuseStep 987481 = 740611) (by norm_num)
theorem B1315237 : Blo 778337 1315237 := bbase (se 4 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 1315237 = 246607) (by norm_num)
theorem B1249717 : Blo 778337 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B1970669 : Blo 778337 1970669 := bbase (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) (by norm_num)
theorem B1315325 : Blo 778337 1315325 := bbase (se 3 (by rfl) ⟨246623, by rfl⟩ : syracuseStep 1315325 = 493247) (by norm_num)
theorem B987653 : Blo 778337 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B987709 : Blo 778337 987709 := bbase (se 3 (by rfl) ⟨185195, by rfl⟩ : syracuseStep 987709 = 370391) (by norm_num)
theorem B1479293 : Blo 778337 1479293 := bbase (se 3 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 1479293 = 554735) (by norm_num)
theorem B1315453 : Blo 778337 1315453 := bbase (se 3 (by rfl) ⟨246647, by rfl⟩ : syracuseStep 1315453 = 493295) (by norm_num)
theorem B987805 : Blo 778337 987805 := bbase (se 3 (by rfl) ⟨185213, by rfl⟩ : syracuseStep 987805 = 370427) (by norm_num)
theorem B1315541 : Blo 778337 1315541 := bbase (se 7 (by rfl) ⟨15416, by rfl⟩ : syracuseStep 1315541 = 30833) (by norm_num)
theorem B1872653 : Blo 778337 1872653 := bbase (se 3 (by rfl) ⟨351122, by rfl⟩ : syracuseStep 1872653 = 702245) (by norm_num)
theorem B1971013 : Blo 778337 1971013 := bbase (se 4 (by rfl) ⟨184782, by rfl⟩ : syracuseStep 1971013 = 369565) (by norm_num)
theorem B987977 : Blo 778337 987977 := bbase (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) (by norm_num)
theorem B1315669 : Blo 778337 1315669 := bbase (se 9 (by rfl) ⟨3854, by rfl⟩ : syracuseStep 1315669 = 7709) (by norm_num)
theorem B2495333 : Blo 778337 2495333 := bbase (se 4 (by rfl) ⟨233937, by rfl⟩ : syracuseStep 2495333 = 467875) (by norm_num)
theorem B988033 : Blo 778337 988033 := bbase (se 2 (by rfl) ⟨370512, by rfl⟩ : syracuseStep 988033 = 741025) (by norm_num)
theorem B1315757 : Blo 778337 1315757 := bbase (se 3 (by rfl) ⟨246704, by rfl⟩ : syracuseStep 1315757 = 493409) (by norm_num)
theorem B1971125 : Blo 778337 1971125 := bbase (se 5 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 1971125 = 184793) (by norm_num)
theorem B988129 : Blo 778337 988129 := bbase (se 2 (by rfl) ⟨370548, by rfl⟩ : syracuseStep 988129 = 741097) (by norm_num)
theorem B4756501 : Blo 778337 4756501 := bbase (se 6 (by rfl) ⟨111480, by rfl⟩ : syracuseStep 4756501 = 222961) (by norm_num)
theorem B1315885 : Blo 778337 1315885 := bbase (se 3 (by rfl) ⟨246728, by rfl⟩ : syracuseStep 1315885 = 493457) (by norm_num)
theorem B1053757 : Blo 778337 1053757 := bbase (se 3 (by rfl) ⟨197579, by rfl⟩ : syracuseStep 1053757 = 395159) (by norm_num)
theorem B1971317 : Blo 778337 1971317 := bbase (se 5 (by rfl) ⟨92405, by rfl⟩ : syracuseStep 1971317 = 184811) (by norm_num)
theorem B1315973 : Blo 778337 1315973 := bbase (se 4 (by rfl) ⟨123372, by rfl⟩ : syracuseStep 1315973 = 246745) (by norm_num)
theorem B988301 : Blo 778337 988301 := bbase (se 3 (by rfl) ⟨185306, by rfl⟩ : syracuseStep 988301 = 370613) (by norm_num)
theorem B988357 : Blo 778337 988357 := bbase (se 4 (by rfl) ⟨92658, by rfl⟩ : syracuseStep 988357 = 185317) (by norm_num)
theorem B1316101 : Blo 778337 1316101 := bbase (se 4 (by rfl) ⟨123384, by rfl⟩ : syracuseStep 1316101 = 246769) (by norm_num)
theorem B988453 : Blo 778337 988453 := bbase (se 4 (by rfl) ⟨92667, by rfl⟩ : syracuseStep 988453 = 185335) (by norm_num)
theorem B1578293 : Blo 778337 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B1316189 : Blo 778337 1316189 := bbase (se 3 (by rfl) ⟨246785, by rfl⟩ : syracuseStep 1316189 = 493571) (by norm_num)
theorem B1250653 : Blo 778337 1250653 := bbase (se 3 (by rfl) ⟨234497, by rfl⟩ : syracuseStep 1250653 = 468995) (by norm_num)
theorem B1480045 : Blo 778337 1480045 := bbase (se 3 (by rfl) ⟨277508, by rfl⟩ : syracuseStep 1480045 = 555017) (by norm_num)
theorem B792001 : Blo 778337 792001 := bbase (se 2 (by rfl) ⟨297000, by rfl⟩ : syracuseStep 792001 = 594001) (by norm_num)
theorem B1971661 : Blo 778337 1971661 := bbase (se 3 (by rfl) ⟨369686, by rfl⟩ : syracuseStep 1971661 = 739373) (by norm_num)
theorem B1185229 : Blo 778337 1185229 := bbase (se 3 (by rfl) ⟨222230, by rfl⟩ : syracuseStep 1185229 = 444461) (by norm_num)
theorem B988625 : Blo 778337 988625 := bbase (se 2 (by rfl) ⟨370734, by rfl⟩ : syracuseStep 988625 = 741469) (by norm_num)
theorem B1316317 : Blo 778337 1316317 := bbase (se 3 (by rfl) ⟨246809, by rfl⟩ : syracuseStep 1316317 = 493619) (by norm_num)
theorem B2627045 : Blo 778337 2627045 := bbase (se 4 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 2627045 = 492571) (by norm_num)
theorem B1480189 : Blo 778337 1480189 := bbase (se 3 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 1480189 = 555071) (by norm_num)
theorem B988681 : Blo 778337 988681 := bbase (se 2 (by rfl) ⟨370755, by rfl⟩ : syracuseStep 988681 = 741511) (by norm_num)
theorem B1316405 : Blo 778337 1316405 := bbase (se 5 (by rfl) ⟨61706, by rfl⟩ : syracuseStep 1316405 = 123413) (by norm_num)
theorem B1971773 : Blo 778337 1971773 := bbase (se 3 (by rfl) ⟨369707, by rfl⟩ : syracuseStep 1971773 = 739415) (by norm_num)
theorem B988777 : Blo 778337 988777 := bbase (se 2 (by rfl) ⟨370791, by rfl⟩ : syracuseStep 988777 = 741583) (by norm_num)
theorem B5346965 : Blo 778337 5346965 := bbase (se 6 (by rfl) ⟨125319, by rfl⟩ : syracuseStep 5346965 = 250639) (by norm_num)
theorem B1480349 : Blo 778337 1480349 := bbase (se 3 (by rfl) ⟨277565, by rfl⟩ : syracuseStep 1480349 = 555131) (by norm_num)
theorem B3741349 : Blo 778337 3741349 := bbase (se 4 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 3741349 = 701503) (by norm_num)
theorem B1316533 : Blo 778337 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B792281 : Blo 778337 792281 := bbase (se 2 (by rfl) ⟨297105, by rfl⟩ : syracuseStep 792281 = 594211) (by norm_num)
theorem B1971965 : Blo 778337 1971965 := bbase (se 3 (by rfl) ⟨369743, by rfl⟩ : syracuseStep 1971965 = 739487) (by norm_num)
theorem B1316621 : Blo 778337 1316621 := bbase (se 3 (by rfl) ⟨246866, by rfl⟩ : syracuseStep 1316621 = 493733) (by norm_num)
theorem B988949 : Blo 778337 988949 := bbase (se 6 (by rfl) ⟨23178, by rfl⟩ : syracuseStep 988949 = 46357) (by norm_num)
theorem B1480493 : Blo 778337 1480493 := bbase (se 3 (by rfl) ⟨277592, by rfl⟩ : syracuseStep 1480493 = 555185) (by norm_num)
theorem B890677 : Blo 778337 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B989005 : Blo 778337 989005 := bbase (se 3 (by rfl) ⟨185438, by rfl⟩ : syracuseStep 989005 = 370877) (by norm_num)
theorem B1316749 : Blo 778337 1316749 := bbase (se 3 (by rfl) ⟨246890, by rfl⟩ : syracuseStep 1316749 = 493781) (by norm_num)
theorem B2627477 : Blo 778337 2627477 := bbase (se 6 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 2627477 = 123163) (by norm_num)
theorem B989101 : Blo 778337 989101 := bbase (se 3 (by rfl) ⟨185456, by rfl⟩ : syracuseStep 989101 = 370913) (by norm_num)
theorem B1316837 : Blo 778337 1316837 := bbase (se 4 (by rfl) ⟨123453, by rfl⟩ : syracuseStep 1316837 = 246907) (by norm_num)
theorem B1480781 : Blo 778337 1480781 := bbase (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) (by norm_num)
theorem B1972309 : Blo 778337 1972309 := bbase (se 8 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 1972309 = 23113) (by norm_num)
theorem B989273 : Blo 778337 989273 := bbase (se 2 (by rfl) ⟨370977, by rfl⟩ : syracuseStep 989273 = 741955) (by norm_num)
theorem B1316965 : Blo 778337 1316965 := bbase (se 4 (by rfl) ⟨123465, by rfl⟩ : syracuseStep 1316965 = 246931) (by norm_num)
theorem B2136181 : Blo 778337 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B989329 : Blo 778337 989329 := bbase (se 2 (by rfl) ⟨370998, by rfl⟩ : syracuseStep 989329 = 741997) (by norm_num)
theorem B1317053 : Blo 778337 1317053 := bbase (se 3 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 1317053 = 493895) (by norm_num)
theorem B1972421 : Blo 778337 1972421 := bbase (se 4 (by rfl) ⟨184914, by rfl⟩ : syracuseStep 1972421 = 369829) (by norm_num)
theorem B1480933 : Blo 778337 1480933 := bbase (se 4 (by rfl) ⟨138837, by rfl⟩ : syracuseStep 1480933 = 277675) (by norm_num)
theorem B989425 : Blo 778337 989425 := bbase (se 2 (by rfl) ⟨371034, by rfl⟩ : syracuseStep 989425 = 742069) (by norm_num)
theorem B2496757 : Blo 778337 2496757 := bbase (se 5 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 2496757 = 234071) (by norm_num)
theorem B792865 : Blo 778337 792865 := bbase (se 2 (by rfl) ⟨297324, by rfl⟩ : syracuseStep 792865 = 594649) (by norm_num)
theorem B5937461 : Blo 778337 5937461 := bbase (se 5 (by rfl) ⟨278318, by rfl⟩ : syracuseStep 5937461 = 556637) (by norm_num)
theorem B1317181 : Blo 778337 1317181 := bbase (se 3 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 1317181 = 493943) (by norm_num)
theorem B2627909 : Blo 778337 2627909 := bbase (se 4 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 2627909 = 492733) (by norm_num)
theorem B792913 : Blo 778337 792913 := bbase (se 2 (by rfl) ⟨297342, by rfl⟩ : syracuseStep 792913 = 594685) (by norm_num)
theorem B1972613 : Blo 778337 1972613 := bbase (se 4 (by rfl) ⟨184932, by rfl⟩ : syracuseStep 1972613 = 369865) (by norm_num)
theorem B1317269 : Blo 778337 1317269 := bbase (se 6 (by rfl) ⟨30873, by rfl⟩ : syracuseStep 1317269 = 61747) (by norm_num)
theorem B1579421 : Blo 778337 1579421 := bbase (se 3 (by rfl) ⟨296141, by rfl⟩ : syracuseStep 1579421 = 592283) (by norm_num)
theorem B989597 : Blo 778337 989597 := bbase (se 3 (by rfl) ⟨185549, by rfl⟩ : syracuseStep 989597 = 371099) (by norm_num)
theorem B989653 : Blo 778337 989653 := bbase (se 7 (by rfl) ⟨11597, by rfl⟩ : syracuseStep 989653 = 23195) (by norm_num)
theorem B2005501 : Blo 778337 2005501 := bbase (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) (by norm_num)
theorem B1251845 : Blo 778337 1251845 := bbase (se 4 (by rfl) ⟨117360, by rfl⟩ : syracuseStep 1251845 = 234721) (by norm_num)
theorem B1481237 : Blo 778337 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B1317397 : Blo 778337 1317397 := bbase (se 6 (by rfl) ⟨30876, by rfl⟩ : syracuseStep 1317397 = 61753) (by norm_num)
theorem B1874461 : Blo 778337 1874461 := bbase (se 3 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 1874461 = 702923) (by norm_num)
theorem B989749 : Blo 778337 989749 := bbase (se 5 (by rfl) ⟨46394, by rfl⟩ : syracuseStep 989749 = 92789) (by norm_num)
theorem B1186397 : Blo 778337 1186397 := bbase (se 3 (by rfl) ⟨222449, by rfl⟩ : syracuseStep 1186397 = 444899) (by norm_num)
theorem B1317485 : Blo 778337 1317485 := bbase (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) (by norm_num)
theorem B2497205 : Blo 778337 2497205 := bbase (se 5 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 2497205 = 234113) (by norm_num)
theorem B2955973 : Blo 778337 2955973 := bbase (se 4 (by rfl) ⟨277122, by rfl⟩ : syracuseStep 2955973 = 554245) (by norm_num)
theorem B1252037 : Blo 778337 1252037 := bbase (se 4 (by rfl) ⟨117378, by rfl⟩ : syracuseStep 1252037 = 234757) (by norm_num)
theorem B1972957 : Blo 778337 1972957 := bbase (se 3 (by rfl) ⟨369929, by rfl⟩ : syracuseStep 1972957 = 739859) (by norm_num)
theorem B989921 : Blo 778337 989921 := bbase (se 2 (by rfl) ⟨371220, by rfl⟩ : syracuseStep 989921 = 742441) (by norm_num)
theorem B1317613 : Blo 778337 1317613 := bbase (se 3 (by rfl) ⟨247052, by rfl⟩ : syracuseStep 1317613 = 494105) (by norm_num)
theorem B2628341 : Blo 778337 2628341 := bbase (se 5 (by rfl) ⟨123203, by rfl⟩ : syracuseStep 2628341 = 246407) (by norm_num)
theorem B989977 : Blo 778337 989977 := bbase (se 2 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 989977 = 742483) (by norm_num)
theorem B1317701 : Blo 778337 1317701 := bbase (se 4 (by rfl) ⟨123534, by rfl⟩ : syracuseStep 1317701 = 247069) (by norm_num)
theorem B1973069 : Blo 778337 1973069 := bbase (se 3 (by rfl) ⟨369950, by rfl⟩ : syracuseStep 1973069 = 739901) (by norm_num)
theorem B990073 : Blo 778337 990073 := bbase (se 2 (by rfl) ⟨371277, by rfl⟩ : syracuseStep 990073 = 742555) (by norm_num)
theorem B1317829 : Blo 778337 1317829 := bbase (se 4 (by rfl) ⟨123546, by rfl⟩ : syracuseStep 1317829 = 247093) (by norm_num)
theorem B891877 : Blo 778337 891877 := bbase (se 4 (by rfl) ⟨83613, by rfl⟩ : syracuseStep 891877 = 167227) (by norm_num)
theorem B2956277 : Blo 778337 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B1776629 : Blo 778337 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B1973261 : Blo 778337 1973261 := bbase (se 3 (by rfl) ⟨369986, by rfl⟩ : syracuseStep 1973261 = 739973) (by norm_num)
theorem B1317917 : Blo 778337 1317917 := bbase (se 3 (by rfl) ⟨247109, by rfl⟩ : syracuseStep 1317917 = 494219) (by norm_num)
theorem B1874981 : Blo 778337 1874981 := bbase (se 4 (by rfl) ⟨175779, by rfl⟩ : syracuseStep 1874981 = 351559) (by norm_num)
theorem B1186901 : Blo 778337 1186901 := bbase (se 8 (by rfl) ⟨6954, by rfl⟩ : syracuseStep 1186901 = 13909) (by norm_num)
theorem B1055845 : Blo 778337 1055845 := bbase (se 4 (by rfl) ⟨98985, by rfl⟩ : syracuseStep 1055845 = 197971) (by norm_num)
theorem B1318045 : Blo 778337 1318045 := bbase (se 3 (by rfl) ⟨247133, by rfl⟩ : syracuseStep 1318045 = 494267) (by norm_num)
theorem B2628773 : Blo 778337 2628773 := bbase (se 4 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 2628773 = 492895) (by norm_num)
theorem B2170037 : Blo 778337 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B1318133 : Blo 778337 1318133 := bbase (se 5 (by rfl) ⟨61787, by rfl⟩ : syracuseStep 1318133 = 123575) (by norm_num)
theorem B1481989 : Blo 778337 1481989 := bbase (se 4 (by rfl) ⟨138936, by rfl⟩ : syracuseStep 1481989 = 277873) (by norm_num)
theorem B1973605 : Blo 778337 1973605 := bbase (se 4 (by rfl) ⟨185025, by rfl⟩ : syracuseStep 1973605 = 370051) (by norm_num)
theorem B1318261 : Blo 778337 1318261 := bbase (se 5 (by rfl) ⟨61793, by rfl⟩ : syracuseStep 1318261 = 123587) (by norm_num)
theorem B1482133 : Blo 778337 1482133 := bbase (se 6 (by rfl) ⟨34737, by rfl⟩ : syracuseStep 1482133 = 69475) (by norm_num)
theorem B1875365 : Blo 778337 1875365 := bbase (se 4 (by rfl) ⟨175815, by rfl⟩ : syracuseStep 1875365 = 351631) (by norm_num)
theorem B1318349 : Blo 778337 1318349 := bbase (se 3 (by rfl) ⟨247190, by rfl⟩ : syracuseStep 1318349 = 494381) (by norm_num)
theorem B1973717 : Blo 778337 1973717 := bbase (se 7 (by rfl) ⟨23129, by rfl⟩ : syracuseStep 1973717 = 46259) (by norm_num)
theorem B1875413 : Blo 778337 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B1875421 : Blo 778337 1875421 := bbase (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) (by norm_num)
theorem B1056277 : Blo 778337 1056277 := bbase (se 6 (by rfl) ⟨24756, by rfl⟩ : syracuseStep 1056277 = 49513) (by norm_num)
theorem B1482293 : Blo 778337 1482293 := bbase (se 5 (by rfl) ⟨69482, by rfl⟩ : syracuseStep 1482293 = 138965) (by norm_num)
theorem B1318477 : Blo 778337 1318477 := bbase (se 3 (by rfl) ⟨247214, by rfl⟩ : syracuseStep 1318477 = 494429) (by norm_num)
theorem B2629205 : Blo 778337 2629205 := bbase (se 8 (by rfl) ⟨15405, by rfl⟩ : syracuseStep 2629205 = 30811) (by norm_num)
theorem B1973909 : Blo 778337 1973909 := bbase (se 6 (by rfl) ⟨46263, by rfl⟩ : syracuseStep 1973909 = 92527) (by norm_num)
theorem B1318565 : Blo 778337 1318565 := bbase (se 4 (by rfl) ⟨123615, by rfl⟩ : syracuseStep 1318565 = 247231) (by norm_num)
theorem B1482437 : Blo 778337 1482437 := bbase (se 4 (by rfl) ⟨138978, by rfl⟩ : syracuseStep 1482437 = 277957) (by norm_num)
theorem B1318693 : Blo 778337 1318693 := bbase (se 4 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 1318693 = 247255) (by norm_num)
theorem B1318781 : Blo 778337 1318781 := bbase (se 3 (by rfl) ⟨247271, by rfl⟩ : syracuseStep 1318781 = 494543) (by norm_num)
theorem B5611477 : Blo 778337 5611477 := bbase (se 7 (by rfl) ⟨65759, by rfl⟩ : syracuseStep 5611477 = 131519) (by norm_num)
theorem B1482725 : Blo 778337 1482725 := bbase (se 4 (by rfl) ⟨139005, by rfl⟩ : syracuseStep 1482725 = 278011) (by norm_num)
theorem B1974253 : Blo 778337 1974253 := bbase (se 3 (by rfl) ⟨370172, by rfl⟩ : syracuseStep 1974253 = 740345) (by norm_num)
theorem B1318909 : Blo 778337 1318909 := bbase (se 3 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 1318909 = 494591) (by norm_num)
theorem B2629637 : Blo 778337 2629637 := bbase (se 4 (by rfl) ⟨246528, by rfl⟩ : syracuseStep 2629637 = 493057) (by norm_num)
theorem B1318997 : Blo 778337 1318997 := bbase (se 8 (by rfl) ⟨7728, by rfl⟩ : syracuseStep 1318997 = 15457) (by norm_num)
theorem B1974365 : Blo 778337 1974365 := bbase (se 3 (by rfl) ⟨370193, by rfl⟩ : syracuseStep 1974365 = 740387) (by norm_num)
theorem B1482877 : Blo 778337 1482877 := bbase (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) (by norm_num)
theorem B1056925 : Blo 778337 1056925 := bbase (se 3 (by rfl) ⟨198173, by rfl⟩ : syracuseStep 1056925 = 396347) (by norm_num)
theorem B1319125 : Blo 778337 1319125 := bbase (se 7 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 1319125 = 30917) (by norm_num)
theorem B1057045 : Blo 778337 1057045 := bbase (se 6 (by rfl) ⟨24774, by rfl⟩ : syracuseStep 1057045 = 49549) (by norm_num)
theorem B1974557 : Blo 778337 1974557 := bbase (se 3 (by rfl) ⟨370229, by rfl⟩ : syracuseStep 1974557 = 740459) (by norm_num)
theorem B1581349 : Blo 778337 1581349 := bbase (se 4 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 1581349 = 296503) (by norm_num)
theorem B1319213 : Blo 778337 1319213 := bbase (se 3 (by rfl) ⟨247352, by rfl⟩ : syracuseStep 1319213 = 494705) (by norm_num)
theorem B1777997 : Blo 778337 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B1483181 : Blo 778337 1483181 := bbase (se 3 (by rfl) ⟨278096, by rfl⟩ : syracuseStep 1483181 = 556193) (by norm_num)
theorem B1319341 : Blo 778337 1319341 := bbase (se 3 (by rfl) ⟨247376, by rfl⟩ : syracuseStep 1319341 = 494753) (by norm_num)
theorem B2630069 : Blo 778337 2630069 := bbase (se 5 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 2630069 = 246569) (by norm_num)
theorem B1876421 : Blo 778337 1876421 := bbase (se 4 (by rfl) ⟨175914, by rfl⟩ : syracuseStep 1876421 = 351829) (by norm_num)
theorem B1319429 : Blo 778337 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B1974901 : Blo 778337 1974901 := bbase (se 5 (by rfl) ⟨92573, by rfl⟩ : syracuseStep 1974901 = 185147) (by norm_num)
theorem B1876613 : Blo 778337 1876613 := bbase (se 4 (by rfl) ⟨175932, by rfl⟩ : syracuseStep 1876613 = 351865) (by norm_num)
theorem B1319557 : Blo 778337 1319557 := bbase (se 4 (by rfl) ⟨123708, by rfl⟩ : syracuseStep 1319557 = 247417) (by norm_num)
theorem B1319645 : Blo 778337 1319645 := bbase (se 3 (by rfl) ⟨247433, by rfl⟩ : syracuseStep 1319645 = 494867) (by norm_num)
theorem B1975013 : Blo 778337 1975013 := bbase (se 4 (by rfl) ⟨185157, by rfl⟩ : syracuseStep 1975013 = 370315) (by norm_num)
theorem B1319773 : Blo 778337 1319773 := bbase (se 3 (by rfl) ⟨247457, by rfl⟩ : syracuseStep 1319773 = 494915) (by norm_num)
theorem B2630501 : Blo 778337 2630501 := bbase (se 4 (by rfl) ⟨246609, by rfl⟩ : syracuseStep 2630501 = 493219) (by norm_num)
theorem B2499461 : Blo 778337 2499461 := bbase (se 4 (by rfl) ⟨234324, by rfl⟩ : syracuseStep 2499461 = 468649) (by norm_num)
theorem B1975205 : Blo 778337 1975205 := bbase (se 4 (by rfl) ⟨185175, by rfl⟩ : syracuseStep 1975205 = 370351) (by norm_num)
theorem B1319861 : Blo 778337 1319861 := bbase (se 5 (by rfl) ⟨61868, by rfl⟩ : syracuseStep 1319861 = 123737) (by norm_num)
theorem B2532341 : Blo 778337 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B2106389 : Blo 778337 2106389 := bbase (se 6 (by rfl) ⟨49368, by rfl⟩ : syracuseStep 2106389 = 98737) (by norm_num)
theorem B2958389 : Blo 778337 2958389 := bbase (se 5 (by rfl) ⟨138674, by rfl⟩ : syracuseStep 2958389 = 277349) (by norm_num)
theorem B1319989 : Blo 778337 1319989 := bbase (se 5 (by rfl) ⟨61874, by rfl⟩ : syracuseStep 1319989 = 123749) (by norm_num)
theorem B1320077 : Blo 778337 1320077 := bbase (se 3 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 1320077 = 495029) (by norm_num)
theorem B1483933 : Blo 778337 1483933 := bbase (se 3 (by rfl) ⟨278237, by rfl⟩ : syracuseStep 1483933 = 556475) (by norm_num)
theorem B3941621 : Blo 778337 3941621 := bbase (se 5 (by rfl) ⟨184763, by rfl⟩ : syracuseStep 3941621 = 369527) (by norm_num)
theorem B1975549 : Blo 778337 1975549 := bbase (se 3 (by rfl) ⟨370415, by rfl⟩ : syracuseStep 1975549 = 740831) (by norm_num)
theorem B2630933 : Blo 778337 2630933 := bbase (se 6 (by rfl) ⟨61662, by rfl⟩ : syracuseStep 2630933 = 123325) (by norm_num)
theorem B1484077 : Blo 778337 1484077 := bbase (se 3 (by rfl) ⟨278264, by rfl⟩ : syracuseStep 1484077 = 556529) (by norm_num)
theorem B5612885 : Blo 778337 5612885 := bbase (se 12 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 5612885 = 4111) (by norm_num)
theorem B2958677 : Blo 778337 2958677 := bbase (se 12 (by rfl) ⟨1083, by rfl⟩ : syracuseStep 2958677 = 2167) (by norm_num)
theorem B1975661 : Blo 778337 1975661 := bbase (se 3 (by rfl) ⟨370436, by rfl⟩ : syracuseStep 1975661 = 740873) (by norm_num)
theorem B2368901 : Blo 778337 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B1582517 : Blo 778337 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B1484237 : Blo 778337 1484237 := bbase (se 3 (by rfl) ⟨278294, by rfl⟩ : syracuseStep 1484237 = 556589) (by norm_num)
theorem B2368997 : Blo 778337 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B1975853 : Blo 778337 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B1484381 : Blo 778337 1484381 := bbase (se 3 (by rfl) ⟨278321, by rfl⟩ : syracuseStep 1484381 = 556643) (by norm_num)
theorem B2631365 : Blo 778337 2631365 := bbase (se 4 (by rfl) ⟨246690, by rfl⟩ : syracuseStep 2631365 = 493381) (by norm_num)
theorem B117253973 : Blo 778337 117253973 := bbase (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) (by norm_num)
theorem B1484669 : Blo 778337 1484669 := bbase (se 3 (by rfl) ⟨278375, by rfl⟩ : syracuseStep 1484669 = 556751) (by norm_num)
theorem B1976197 : Blo 778337 1976197 := bbase (se 4 (by rfl) ⟨185268, by rfl⟩ : syracuseStep 1976197 = 370537) (by norm_num)
theorem B1124285 : Blo 778337 1124285 := bbase (se 3 (by rfl) ⟨210803, by rfl⟩ : syracuseStep 1124285 = 421607) (by norm_num)
theorem B1976309 : Blo 778337 1976309 := bbase (se 5 (by rfl) ⟨92639, by rfl⟩ : syracuseStep 1976309 = 185279) (by norm_num)
theorem B1484821 : Blo 778337 1484821 := bbase (se 6 (by rfl) ⟨34800, by rfl⟩ : syracuseStep 1484821 = 69601) (by norm_num)
theorem B1779749 : Blo 778337 1779749 := bbase (se 4 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 1779749 = 333703) (by norm_num)
theorem B6006869 : Blo 778337 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B2631797 : Blo 778337 2631797 := bbase (se 5 (by rfl) ⟨123365, by rfl⟩ : syracuseStep 2631797 = 246731) (by norm_num)
theorem B1976501 : Blo 778337 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B4696309 : Blo 778337 4696309 := bbase (se 5 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 4696309 = 440279) (by norm_num)
theorem B1485125 : Blo 778337 1485125 := bbase (se 4 (by rfl) ⟨139230, by rfl⟩ : syracuseStep 1485125 = 278461) (by norm_num)
theorem B7317845 : Blo 778337 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B2959861 : Blo 778337 2959861 := bbase (se 5 (by rfl) ⟨138743, by rfl⟩ : syracuseStep 2959861 = 277487) (by norm_num)
theorem B3942917 : Blo 778337 3942917 := bbase (se 4 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 3942917 = 739297) (by norm_num)
theorem B1976845 : Blo 778337 1976845 := bbase (se 3 (by rfl) ⟨370658, by rfl⟩ : syracuseStep 1976845 = 741317) (by norm_num)
theorem B2632229 : Blo 778337 2632229 := bbase (se 4 (by rfl) ⟨246771, by rfl⟩ : syracuseStep 2632229 = 493543) (by norm_num)
theorem B1878565 : Blo 778337 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1976957 : Blo 778337 1976957 := bbase (se 3 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 1976957 = 741359) (by norm_num)
theorem B2960165 : Blo 778337 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B1977149 : Blo 778337 1977149 := bbase (se 3 (by rfl) ⟨370715, by rfl⟩ : syracuseStep 1977149 = 741431) (by norm_num)
theorem B2632661 : Blo 778337 2632661 := bbase (se 7 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 2632661 = 61703) (by norm_num)
theorem B1977493 : Blo 778337 1977493 := bbase (se 6 (by rfl) ⟨46347, by rfl⟩ : syracuseStep 1977493 = 92695) (by norm_num)
theorem B3550373 : Blo 778337 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B1977605 : Blo 778337 1977605 := bbase (se 4 (by rfl) ⟨185400, by rfl⟩ : syracuseStep 1977605 = 370801) (by norm_num)
theorem B2633093 : Blo 778337 2633093 := bbase (se 4 (by rfl) ⟨246852, by rfl⟩ : syracuseStep 2633093 = 493705) (by norm_num)
theorem B1977797 : Blo 778337 1977797 := bbase (se 4 (by rfl) ⟨185418, by rfl⟩ : syracuseStep 1977797 = 370837) (by norm_num)
theorem B1879517 : Blo 778337 1879517 := bbase (se 3 (by rfl) ⟨352409, by rfl⟩ : syracuseStep 1879517 = 704819) (by norm_num)
theorem B1879573 : Blo 778337 1879573 := bbase (se 6 (by rfl) ⟨44052, by rfl⟩ : syracuseStep 1879573 = 88105) (by norm_num)
theorem B3944213 : Blo 778337 3944213 := bbase (se 6 (by rfl) ⟨92442, by rfl⟩ : syracuseStep 3944213 = 184885) (by norm_num)
theorem B1978141 : Blo 778337 1978141 := bbase (se 3 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 1978141 = 741803) (by norm_num)
theorem B831265 : Blo 778337 831265 := bbase (se 2 (by rfl) ⟨311724, by rfl⟩ : syracuseStep 831265 = 623449) (by norm_num)
theorem B2633525 : Blo 778337 2633525 := bbase (se 5 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 2633525 = 246893) (by norm_num)
theorem B3747653 : Blo 778337 3747653 := bbase (se 4 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 3747653 = 702685) (by norm_num)
theorem B7515989 : Blo 778337 7515989 := bbase (se 9 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 7515989 = 44039) (by norm_num)
theorem B4435829 : Blo 778337 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B1978253 : Blo 778337 1978253 := bbase (se 3 (by rfl) ⟨370922, by rfl⟩ : syracuseStep 1978253 = 741845) (by norm_num)
theorem B831385 : Blo 778337 831385 := bbase (se 2 (by rfl) ⟨311769, by rfl⟩ : syracuseStep 831385 = 623539) (by norm_num)
theorem B1978445 : Blo 778337 1978445 := bbase (se 3 (by rfl) ⟨370958, by rfl⟩ : syracuseStep 1978445 = 741917) (by norm_num)
theorem B2535509 : Blo 778337 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B831637 : Blo 778337 831637 := bbase (se 6 (by rfl) ⟨19491, by rfl⟩ : syracuseStep 831637 = 38983) (by norm_num)
theorem B831641 : Blo 778337 831641 := bbase (se 2 (by rfl) ⟨311865, by rfl⟩ : syracuseStep 831641 = 623731) (by norm_num)
theorem B1585325 : Blo 778337 1585325 := bbase (se 3 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 1585325 = 594497) (by norm_num)
theorem B2633957 : Blo 778337 2633957 := bbase (se 4 (by rfl) ⟨246933, by rfl⟩ : syracuseStep 2633957 = 493867) (by norm_num)
theorem B1585469 : Blo 778337 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1978789 : Blo 778337 1978789 := bbase (se 4 (by rfl) ⟨185511, by rfl⟩ : syracuseStep 1978789 = 371023) (by norm_num)
theorem B1782229 : Blo 778337 1782229 := bbase (se 7 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 1782229 = 41771) (by norm_num)
theorem B2535925 : Blo 778337 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B1978901 : Blo 778337 1978901 := bbase (se 6 (by rfl) ⟨46380, by rfl⟩ : syracuseStep 1978901 = 92761) (by norm_num)
theorem B4993589 : Blo 778337 4993589 := bbase (se 5 (by rfl) ⟨234074, by rfl⟩ : syracuseStep 4993589 = 468149) (by norm_num)
theorem B2634389 : Blo 778337 2634389 := bbase (se 6 (by rfl) ⟨61743, by rfl⟩ : syracuseStep 2634389 = 123487) (by norm_num)
theorem B832205 : Blo 778337 832205 := bbase (se 3 (by rfl) ⟨156038, by rfl⟩ : syracuseStep 832205 = 312077) (by norm_num)
theorem B2503381 : Blo 778337 2503381 := bbase (se 7 (by rfl) ⟨29336, by rfl⟩ : syracuseStep 2503381 = 58673) (by norm_num)
theorem B1979093 : Blo 778337 1979093 := bbase (se 7 (by rfl) ⟨23192, by rfl⟩ : syracuseStep 1979093 = 46385) (by norm_num)
theorem B2962277 : Blo 778337 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B832393 : Blo 778337 832393 := bbase (se 2 (by rfl) ⟨312147, by rfl⟩ : syracuseStep 832393 = 624295) (by norm_num)
theorem B7484309 : Blo 778337 7484309 := bbase (se 6 (by rfl) ⟨175413, by rfl⟩ : syracuseStep 7484309 = 350827) (by norm_num)
theorem B2503637 : Blo 778337 2503637 := bbase (se 7 (by rfl) ⟨29339, by rfl⟩ : syracuseStep 2503637 = 58679) (by norm_num)
theorem B3945509 : Blo 778337 3945509 := bbase (se 4 (by rfl) ⟨369891, by rfl⟩ : syracuseStep 3945509 = 739783) (by norm_num)
theorem B1979437 : Blo 778337 1979437 := bbase (se 3 (by rfl) ⟨371144, by rfl⟩ : syracuseStep 1979437 = 742289) (by norm_num)
theorem B2634821 : Blo 778337 2634821 := bbase (se 4 (by rfl) ⟨247014, by rfl⟩ : syracuseStep 2634821 = 494029) (by norm_num)
theorem B3847253 : Blo 778337 3847253 := bbase (se 8 (by rfl) ⟨22542, by rfl⟩ : syracuseStep 3847253 = 45085) (by norm_num)
theorem B3748997 : Blo 778337 3748997 := bbase (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) (by norm_num)
theorem B2962565 : Blo 778337 2962565 := bbase (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) (by norm_num)
theorem B1979549 : Blo 778337 1979549 := bbase (se 3 (by rfl) ⟨371165, by rfl⟩ : syracuseStep 1979549 = 742331) (by norm_num)
theorem B6665429 : Blo 778337 6665429 := bbase (se 7 (by rfl) ⟨78110, by rfl⟩ : syracuseStep 6665429 = 156221) (by norm_num)
theorem B1979741 : Blo 778337 1979741 := bbase (se 3 (by rfl) ⟨371201, by rfl⟩ : syracuseStep 1979741 = 742403) (by norm_num)
theorem B2635253 : Blo 778337 2635253 := bbase (se 5 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 2635253 = 247055) (by norm_num)
theorem B2110997 : Blo 778337 2110997 := bbase (se 6 (by rfl) ⟨49476, by rfl⟩ : syracuseStep 2110997 = 98953) (by norm_num)
theorem B1980085 : Blo 778337 1980085 := bbase (se 5 (by rfl) ⟨92816, by rfl⟩ : syracuseStep 1980085 = 185633) (by norm_num)
theorem B833213 : Blo 778337 833213 := bbase (se 3 (by rfl) ⟨156227, by rfl⟩ : syracuseStep 833213 = 312455) (by norm_num)
theorem B2537173 : Blo 778337 2537173 := bbase (se 7 (by rfl) ⟨29732, by rfl⟩ : syracuseStep 2537173 = 59465) (by norm_num)
theorem B1980197 : Blo 778337 1980197 := bbase (se 4 (by rfl) ⟨185643, by rfl⟩ : syracuseStep 1980197 = 371287) (by norm_num)
theorem B2635685 : Blo 778337 2635685 := bbase (se 4 (by rfl) ⟨247095, by rfl⟩ : syracuseStep 2635685 = 494191) (by norm_num)
theorem B833657 : Blo 778337 833657 := bbase (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) (by norm_num)
theorem B1751309 : Blo 778337 1751309 := bbase (se 3 (by rfl) ⟨328370, by rfl⟩ : syracuseStep 1751309 = 656741) (by norm_num)
theorem B2963749 : Blo 778337 2963749 := bbase (se 4 (by rfl) ⟨277851, by rfl⟩ : syracuseStep 2963749 = 555703) (by norm_num)
theorem B3946805 : Blo 778337 3946805 := bbase (se 5 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 3946805 = 370013) (by norm_num)
theorem B1751381 : Blo 778337 1751381 := bbase (se 10 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 1751381 = 5131) (by norm_num)
theorem B2636117 : Blo 778337 2636117 := bbase (se 10 (by rfl) ⟨3861, by rfl⟩ : syracuseStep 2636117 = 7723) (by norm_num)
theorem B833905 : Blo 778337 833905 := bbase (se 2 (by rfl) ⟨312714, by rfl⟩ : syracuseStep 833905 = 625429) (by norm_num)
theorem B1849717 : Blo 778337 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B1751453 : Blo 778337 1751453 := bbase (se 3 (by rfl) ⟨328397, by rfl⟩ : syracuseStep 1751453 = 656795) (by norm_num)
theorem B2374069 : Blo 778337 2374069 := bbase (se 5 (by rfl) ⟨111284, by rfl⟩ : syracuseStep 2374069 = 222569) (by norm_num)
theorem B1751525 : Blo 778337 1751525 := bbase (se 4 (by rfl) ⟨164205, by rfl⟩ : syracuseStep 1751525 = 328411) (by norm_num)
theorem B3750421 : Blo 778337 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B1751597 : Blo 778337 1751597 := bbase (se 3 (by rfl) ⟨328424, by rfl⟩ : syracuseStep 1751597 = 656849) (by norm_num)
theorem B2964053 : Blo 778337 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B1751669 : Blo 778337 1751669 := bbase (se 5 (by rfl) ⟨82109, by rfl⟩ : syracuseStep 1751669 = 164219) (by norm_num)
theorem B1751741 : Blo 778337 1751741 := bbase (se 3 (by rfl) ⟨328451, by rfl⟩ : syracuseStep 1751741 = 656903) (by norm_num)
theorem B1751813 : Blo 778337 1751813 := bbase (se 4 (by rfl) ⟨164232, by rfl⟩ : syracuseStep 1751813 = 328465) (by norm_num)
theorem B2636549 : Blo 778337 2636549 := bbase (se 4 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 2636549 = 494353) (by norm_num)
theorem B834337 : Blo 778337 834337 := bbase (se 2 (by rfl) ⟨312876, by rfl⟩ : syracuseStep 834337 = 625753) (by norm_num)
theorem B1751885 : Blo 778337 1751885 := bbase (se 3 (by rfl) ⟨328478, by rfl⟩ : syracuseStep 1751885 = 656957) (by norm_num)
theorem B834409 : Blo 778337 834409 := bbase (se 2 (by rfl) ⟨312903, by rfl⟩ : syracuseStep 834409 = 625807) (by norm_num)
theorem B1424269 : Blo 778337 1424269 := bbase (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) (by norm_num)
theorem B1751957 : Blo 778337 1751957 := bbase (se 6 (by rfl) ⟨41061, by rfl⟩ : syracuseStep 1751957 = 82123) (by norm_num)
theorem B3161045 : Blo 778337 3161045 := bbase (se 7 (by rfl) ⟨37043, by rfl⟩ : syracuseStep 3161045 = 74087) (by norm_num)
theorem B1752029 : Blo 778337 1752029 := bbase (se 3 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 1752029 = 657011) (by norm_num)
theorem B1752101 : Blo 778337 1752101 := bbase (se 4 (by rfl) ⟨164259, by rfl⟩ : syracuseStep 1752101 = 328519) (by norm_num)
theorem B1752173 : Blo 778337 1752173 := bbase (se 3 (by rfl) ⟨328532, by rfl⟩ : syracuseStep 1752173 = 657065) (by norm_num)
theorem B1752245 : Blo 778337 1752245 := bbase (se 5 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 1752245 = 164273) (by norm_num)
theorem B2636981 : Blo 778337 2636981 := bbase (se 5 (by rfl) ⟨123608, by rfl⟩ : syracuseStep 2636981 = 247217) (by norm_num)
theorem B900313 : Blo 778337 900313 := bbase (se 2 (by rfl) ⟨337617, by rfl⟩ : syracuseStep 900313 = 675235) (by norm_num)
theorem B834781 : Blo 778337 834781 := bbase (se 3 (by rfl) ⟨156521, by rfl⟩ : syracuseStep 834781 = 313043) (by norm_num)
theorem B1752317 : Blo 778337 1752317 := bbase (se 3 (by rfl) ⟨328559, by rfl⟩ : syracuseStep 1752317 = 657119) (by norm_num)
theorem B1752389 : Blo 778337 1752389 := bbase (se 4 (by rfl) ⟨164286, by rfl⟩ : syracuseStep 1752389 = 328573) (by norm_num)
theorem B27344213 : Blo 778337 27344213 := bbase (se 11 (by rfl) ⟨20027, by rfl⟩ : syracuseStep 27344213 = 40055) (by norm_num)
theorem B1752461 : Blo 778337 1752461 := bbase (se 3 (by rfl) ⟨328586, by rfl⟩ : syracuseStep 1752461 = 657173) (by norm_num)
theorem B998861 : Blo 778337 998861 := bbase (se 3 (by rfl) ⟨187286, by rfl⟩ : syracuseStep 998861 = 374573) (by norm_num)
theorem B1752533 : Blo 778337 1752533 := bbase (se 7 (by rfl) ⟨20537, by rfl⟩ : syracuseStep 1752533 = 41075) (by norm_num)
theorem B5914133 : Blo 778337 5914133 := bbase (se 6 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 5914133 = 277225) (by norm_num)
theorem B1752605 : Blo 778337 1752605 := bbase (se 3 (by rfl) ⟨328613, by rfl⟩ : syracuseStep 1752605 = 657227) (by norm_num)
theorem B3948101 : Blo 778337 3948101 := bbase (se 4 (by rfl) ⟨370134, by rfl⟩ : syracuseStep 3948101 = 740269) (by norm_num)
theorem B2375237 : Blo 778337 2375237 := bbase (se 4 (by rfl) ⟨222678, by rfl⟩ : syracuseStep 2375237 = 445357) (by norm_num)
theorem B835157 : Blo 778337 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B1752677 : Blo 778337 1752677 := bbase (se 4 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 1752677 = 328627) (by norm_num)
theorem B2637413 : Blo 778337 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B900721 : Blo 778337 900721 := bbase (se 2 (by rfl) ⟨337770, by rfl⟩ : syracuseStep 900721 = 675541) (by norm_num)
theorem B835229 : Blo 778337 835229 := bbase (se 3 (by rfl) ⟨156605, by rfl⟩ : syracuseStep 835229 = 313211) (by norm_num)
theorem B2375333 : Blo 778337 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B1752749 : Blo 778337 1752749 := bbase (se 3 (by rfl) ⟨328640, by rfl⟩ : syracuseStep 1752749 = 657281) (by norm_num)
theorem B1752821 : Blo 778337 1752821 := bbase (se 5 (by rfl) ⟨82163, by rfl⟩ : syracuseStep 1752821 = 164327) (by norm_num)
theorem B1752893 : Blo 778337 1752893 := bbase (se 3 (by rfl) ⟨328667, by rfl⟩ : syracuseStep 1752893 = 657335) (by norm_num)
theorem B835417 : Blo 778337 835417 := bbase (se 2 (by rfl) ⟨313281, by rfl⟩ : syracuseStep 835417 = 626563) (by norm_num)
theorem B2113397 : Blo 778337 2113397 := bbase (se 5 (by rfl) ⟨99065, by rfl⟩ : syracuseStep 2113397 = 198131) (by norm_num)
theorem B1752965 : Blo 778337 1752965 := bbase (se 4 (by rfl) ⟨164340, by rfl⟩ : syracuseStep 1752965 = 328681) (by norm_num)
theorem B3162037 : Blo 778337 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B1753037 : Blo 778337 1753037 := bbase (se 3 (by rfl) ⟨328694, by rfl⟩ : syracuseStep 1753037 = 657389) (by norm_num)
theorem B1753109 : Blo 778337 1753109 := bbase (se 6 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 1753109 = 82177) (by norm_num)
theorem B2637845 : Blo 778337 2637845 := bbase (se 6 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 2637845 = 123649) (by norm_num)
theorem B1753181 : Blo 778337 1753181 := bbase (se 3 (by rfl) ⟨328721, by rfl⟩ : syracuseStep 1753181 = 657443) (by norm_num)
theorem B6668405 : Blo 778337 6668405 := bbase (se 5 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 6668405 = 625163) (by norm_num)
theorem B1753253 : Blo 778337 1753253 := bbase (se 4 (by rfl) ⟨164367, by rfl⟩ : syracuseStep 1753253 = 328735) (by norm_num)
theorem B1753325 : Blo 778337 1753325 := bbase (se 3 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 1753325 = 657497) (by norm_num)
theorem B2113829 : Blo 778337 2113829 := bbase (se 4 (by rfl) ⟨198171, by rfl⟩ : syracuseStep 2113829 = 396343) (by norm_num)
theorem B1753397 : Blo 778337 1753397 := bbase (se 5 (by rfl) ⟨82190, by rfl⟩ : syracuseStep 1753397 = 164381) (by norm_num)
theorem B999749 : Blo 778337 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B3555701 : Blo 778337 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B1753469 : Blo 778337 1753469 := bbase (se 3 (by rfl) ⟨328775, by rfl⟩ : syracuseStep 1753469 = 657551) (by norm_num)
theorem B1130917 : Blo 778337 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B1753541 : Blo 778337 1753541 := bbase (se 4 (by rfl) ⟨164394, by rfl⟩ : syracuseStep 1753541 = 328789) (by norm_num)
theorem B2638277 : Blo 778337 2638277 := bbase (se 4 (by rfl) ⟨247338, by rfl⟩ : syracuseStep 2638277 = 494677) (by norm_num)
theorem B3555829 : Blo 778337 3555829 := bbase (se 5 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 3555829 = 333359) (by norm_num)
theorem B1753613 : Blo 778337 1753613 := bbase (se 3 (by rfl) ⟨328802, by rfl⟩ : syracuseStep 1753613 = 657605) (by norm_num)
theorem B1753685 : Blo 778337 1753685 := bbase (se 8 (by rfl) ⟨10275, by rfl⟩ : syracuseStep 1753685 = 20551) (by norm_num)
theorem B8438357 : Blo 778337 8438357 := bbase (se 8 (by rfl) ⟨49443, by rfl⟩ : syracuseStep 8438357 = 98887) (by norm_num)
theorem B2966165 : Blo 778337 2966165 := bbase (se 6 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 2966165 = 139039) (by norm_num)
theorem B1753757 : Blo 778337 1753757 := bbase (se 3 (by rfl) ⟨328829, by rfl⟩ : syracuseStep 1753757 = 657659) (by norm_num)
theorem B1753829 : Blo 778337 1753829 := bbase (se 4 (by rfl) ⟨164421, by rfl⟩ : syracuseStep 1753829 = 328843) (by norm_num)
theorem B1753901 : Blo 778337 1753901 := bbase (se 3 (by rfl) ⟨328856, by rfl⟩ : syracuseStep 1753901 = 657713) (by norm_num)
theorem B3949397 : Blo 778337 3949397 := bbase (se 9 (by rfl) ⟨11570, by rfl⟩ : syracuseStep 3949397 = 23141) (by norm_num)
theorem B1753973 : Blo 778337 1753973 := bbase (se 5 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 1753973 = 164435) (by norm_num)
theorem B2638709 : Blo 778337 2638709 := bbase (se 5 (by rfl) ⟨123689, by rfl⟩ : syracuseStep 2638709 = 247379) (by norm_num)
theorem B1000369 : Blo 778337 1000369 := bbase (se 2 (by rfl) ⟨375138, by rfl⟩ : syracuseStep 1000369 = 750277) (by norm_num)
theorem B2966453 : Blo 778337 2966453 := bbase (se 5 (by rfl) ⟨139052, by rfl⟩ : syracuseStep 2966453 = 278105) (by norm_num)
theorem B1754045 : Blo 778337 1754045 := bbase (se 3 (by rfl) ⟨328883, by rfl⟩ : syracuseStep 1754045 = 657767) (by norm_num)
theorem B1754117 : Blo 778337 1754117 := bbase (se 4 (by rfl) ⟨164448, by rfl⟩ : syracuseStep 1754117 = 328897) (by norm_num)
theorem B1754189 : Blo 778337 1754189 := bbase (se 3 (by rfl) ⟨328910, by rfl⟩ : syracuseStep 1754189 = 657821) (by norm_num)
theorem B1754261 : Blo 778337 1754261 := bbase (se 6 (by rfl) ⟨41115, by rfl⟩ : syracuseStep 1754261 = 82231) (by norm_num)
theorem B6341813 : Blo 778337 6341813 := bbase (se 5 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 6341813 = 594545) (by norm_num)
theorem B1098965 : Blo 778337 1098965 := bbase (se 7 (by rfl) ⟨12878, by rfl⟩ : syracuseStep 1098965 = 25757) (by norm_num)
theorem B1754333 : Blo 778337 1754333 := bbase (se 3 (by rfl) ⟨328937, by rfl⟩ : syracuseStep 1754333 = 657875) (by norm_num)
theorem B1000669 : Blo 778337 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B4211957 : Blo 778337 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B1754405 : Blo 778337 1754405 := bbase (se 4 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 1754405 = 328951) (by norm_num)
theorem B2639141 : Blo 778337 2639141 := bbase (se 4 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 2639141 = 494839) (by norm_num)
theorem B3327317 : Blo 778337 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B1754477 : Blo 778337 1754477 := bbase (se 3 (by rfl) ⟨328964, by rfl⟩ : syracuseStep 1754477 = 657929) (by norm_num)
theorem B1754549 : Blo 778337 1754549 := bbase (se 5 (by rfl) ⟨82244, by rfl⟩ : syracuseStep 1754549 = 164489) (by norm_num)
theorem B1754621 : Blo 778337 1754621 := bbase (se 3 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 1754621 = 657983) (by norm_num)
theorem B1754693 : Blo 778337 1754693 := bbase (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) (by norm_num)
theorem B1754765 : Blo 778337 1754765 := bbase (se 3 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 1754765 = 658037) (by norm_num)
theorem B1754837 : Blo 778337 1754837 := bbase (se 7 (by rfl) ⟨20564, by rfl⟩ : syracuseStep 1754837 = 41129) (by norm_num)
theorem B2639573 : Blo 778337 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B935669 : Blo 778337 935669 := bbase (se 5 (by rfl) ⟨43859, by rfl⟩ : syracuseStep 935669 = 87719) (by norm_num)
theorem B1754909 : Blo 778337 1754909 := bbase (se 3 (by rfl) ⟨329045, by rfl⟩ : syracuseStep 1754909 = 658091) (by norm_num)
theorem B902977 : Blo 778337 902977 := bbase (se 2 (by rfl) ⟨338616, by rfl⟩ : syracuseStep 902977 = 677233) (by norm_num)
theorem B1754981 : Blo 778337 1754981 := bbase (se 4 (by rfl) ⟨164529, by rfl⟩ : syracuseStep 1754981 = 329059) (by norm_num)
theorem B1689509 : Blo 778337 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B1755053 : Blo 778337 1755053 := bbase (se 3 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 1755053 = 658145) (by norm_num)
theorem B1755125 : Blo 778337 1755125 := bbase (se 5 (by rfl) ⟨82271, by rfl⟩ : syracuseStep 1755125 = 164543) (by norm_num)
theorem B935977 : Blo 778337 935977 := bbase (se 2 (by rfl) ⟨350991, by rfl⟩ : syracuseStep 935977 = 701983) (by norm_num)
theorem B1755197 : Blo 778337 1755197 := bbase (se 3 (by rfl) ⟨329099, by rfl⟩ : syracuseStep 1755197 = 658199) (by norm_num)
theorem B2967637 : Blo 778337 2967637 := bbase (se 8 (by rfl) ⟨17388, by rfl⟩ : syracuseStep 2967637 = 34777) (by norm_num)
theorem B3950693 : Blo 778337 3950693 := bbase (se 4 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 3950693 = 740755) (by norm_num)
theorem B1755269 : Blo 778337 1755269 := bbase (se 4 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 1755269 = 329113) (by norm_num)
theorem B2640005 : Blo 778337 2640005 := bbase (se 4 (by rfl) ⟨247500, by rfl⟩ : syracuseStep 2640005 = 495001) (by norm_num)
theorem B1755341 : Blo 778337 1755341 := bbase (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) (by norm_num)
theorem B1755413 : Blo 778337 1755413 := bbase (se 6 (by rfl) ⟨41142, by rfl⟩ : syracuseStep 1755413 = 82285) (by norm_num)
theorem B1755485 : Blo 778337 1755485 := bbase (se 3 (by rfl) ⟨329153, by rfl⟩ : syracuseStep 1755485 = 658307) (by norm_num)
theorem B2967941 : Blo 778337 2967941 := bbase (se 4 (by rfl) ⟨278244, by rfl⟩ : syracuseStep 2967941 = 556489) (by norm_num)
theorem B1755557 : Blo 778337 1755557 := bbase (se 4 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 1755557 = 329167) (by norm_num)
theorem B936361 : Blo 778337 936361 := bbase (se 2 (by rfl) ⟨351135, by rfl⟩ : syracuseStep 936361 = 702271) (by norm_num)
theorem B936365 : Blo 778337 936365 := bbase (se 3 (by rfl) ⟨175568, by rfl⟩ : syracuseStep 936365 = 351137) (by norm_num)
theorem B1755629 : Blo 778337 1755629 := bbase (se 3 (by rfl) ⟨329180, by rfl⟩ : syracuseStep 1755629 = 658361) (by norm_num)
theorem B1001981 : Blo 778337 1001981 := bbase (se 3 (by rfl) ⟨187871, by rfl⟩ : syracuseStep 1001981 = 375743) (by norm_num)
theorem B1755701 : Blo 778337 1755701 := bbase (se 5 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 1755701 = 164597) (by norm_num)
theorem B1755773 : Blo 778337 1755773 := bbase (se 3 (by rfl) ⟨329207, by rfl⟩ : syracuseStep 1755773 = 658415) (by norm_num)
theorem B1755845 : Blo 778337 1755845 := bbase (se 4 (by rfl) ⟨164610, by rfl⟩ : syracuseStep 1755845 = 329221) (by norm_num)
theorem B1755917 : Blo 778337 1755917 := bbase (se 3 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 1755917 = 658469) (by norm_num)
theorem B936769 : Blo 778337 936769 := bbase (se 2 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 936769 = 702577) (by norm_num)
theorem B1428301 : Blo 778337 1428301 := bbase (se 3 (by rfl) ⟨267806, by rfl⟩ : syracuseStep 1428301 = 535613) (by norm_num)
theorem B1755989 : Blo 778337 1755989 := bbase (se 9 (by rfl) ⟨5144, by rfl⟩ : syracuseStep 1755989 = 10289) (by norm_num)
theorem B1756061 : Blo 778337 1756061 := bbase (se 3 (by rfl) ⟨329261, by rfl⟩ : syracuseStep 1756061 = 658523) (by norm_num)
theorem B904133 : Blo 778337 904133 := bbase (se 4 (by rfl) ⟨84762, by rfl⟩ : syracuseStep 904133 = 169525) (by norm_num)
theorem B1756133 : Blo 778337 1756133 := bbase (se 4 (by rfl) ⟨164637, by rfl⟩ : syracuseStep 1756133 = 329275) (by norm_num)
theorem B1756205 : Blo 778337 1756205 := bbase (se 3 (by rfl) ⟨329288, by rfl⟩ : syracuseStep 1756205 = 658577) (by norm_num)
theorem B3329093 : Blo 778337 3329093 := bbase (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) (by norm_num)
theorem B1756277 : Blo 778337 1756277 := bbase (se 5 (by rfl) ⟨82325, by rfl⟩ : syracuseStep 1756277 = 164651) (by norm_num)
theorem B1756349 : Blo 778337 1756349 := bbase (se 3 (by rfl) ⟨329315, by rfl⟩ : syracuseStep 1756349 = 658631) (by norm_num)
theorem B1756421 : Blo 778337 1756421 := bbase (se 4 (by rfl) ⟨164664, by rfl⟩ : syracuseStep 1756421 = 329329) (by norm_num)
theorem B3755285 : Blo 778337 3755285 := bbase (se 6 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 3755285 = 176029) (by norm_num)
theorem B3329333 : Blo 778337 3329333 := bbase (se 5 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 3329333 = 312125) (by norm_num)
theorem B1756493 : Blo 778337 1756493 := bbase (se 3 (by rfl) ⟨329342, by rfl⟩ : syracuseStep 1756493 = 658685) (by norm_num)
theorem B3951989 : Blo 778337 3951989 := bbase (se 5 (by rfl) ⟨185249, by rfl⟩ : syracuseStep 3951989 = 370499) (by norm_num)
theorem B1756565 : Blo 778337 1756565 := bbase (se 6 (by rfl) ⟨41169, by rfl⟩ : syracuseStep 1756565 = 82339) (by norm_num)
theorem B10833301 : Blo 778337 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B1068485 : Blo 778337 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B1756637 : Blo 778337 1756637 := bbase (se 3 (by rfl) ⟨329369, by rfl⟩ : syracuseStep 1756637 = 658739) (by norm_num)
theorem B1756709 : Blo 778337 1756709 := bbase (se 4 (by rfl) ⟨164691, by rfl⟩ : syracuseStep 1756709 = 329383) (by norm_num)
theorem B3165749 : Blo 778337 3165749 := bbase (se 5 (by rfl) ⟨148394, by rfl⟩ : syracuseStep 3165749 = 296789) (by norm_num)
theorem B1756781 : Blo 778337 1756781 := bbase (se 3 (by rfl) ⟨329396, by rfl⟩ : syracuseStep 1756781 = 658793) (by norm_num)
theorem B1756853 : Blo 778337 1756853 := bbase (se 5 (by rfl) ⟨82352, by rfl⟩ : syracuseStep 1756853 = 164705) (by norm_num)
theorem B4443893 : Blo 778337 4443893 := bbase (se 5 (by rfl) ⟨208307, by rfl⟩ : syracuseStep 4443893 = 416615) (by norm_num)
theorem B1756925 : Blo 778337 1756925 := bbase (se 3 (by rfl) ⟨329423, by rfl⟩ : syracuseStep 1756925 = 658847) (by norm_num)
theorem B1756997 : Blo 778337 1756997 := bbase (se 4 (by rfl) ⟨164718, by rfl⟩ : syracuseStep 1756997 = 329437) (by norm_num)
theorem B2805637 : Blo 778337 2805637 := bbase (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) (by norm_num)
theorem B1757069 : Blo 778337 1757069 := bbase (se 3 (by rfl) ⟨329450, by rfl⟩ : syracuseStep 1757069 = 658901) (by norm_num)
theorem B1757141 : Blo 778337 1757141 := bbase (se 7 (by rfl) ⟨20591, by rfl⟩ : syracuseStep 1757141 = 41183) (by norm_num)
theorem B6770645 : Blo 778337 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B1757213 : Blo 778337 1757213 := bbase (se 3 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 1757213 = 658955) (by norm_num)
theorem B1757285 : Blo 778337 1757285 := bbase (se 4 (by rfl) ⟨164745, by rfl⟩ : syracuseStep 1757285 = 329491) (by norm_num)
theorem B1167509 : Blo 778337 1167509 := bbase (se 6 (by rfl) ⟨27363, by rfl⟩ : syracuseStep 1167509 = 54727) (by norm_num)
theorem B938153 : Blo 778337 938153 := bbase (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) (by norm_num)
theorem B1167533 : Blo 778337 1167533 := bbase (se 3 (by rfl) ⟨218912, by rfl⟩ : syracuseStep 1167533 = 437825) (by norm_num)
theorem B1757357 : Blo 778337 1757357 := bbase (se 3 (by rfl) ⟨329504, by rfl⟩ : syracuseStep 1757357 = 659009) (by norm_num)
theorem B1167557 : Blo 778337 1167557 := bbase (se 4 (by rfl) ⟨109458, by rfl⟩ : syracuseStep 1167557 = 218917) (by norm_num)
theorem B1167581 : Blo 778337 1167581 := bbase (se 3 (by rfl) ⟨218921, by rfl⟩ : syracuseStep 1167581 = 437843) (by norm_num)
theorem B1167605 : Blo 778337 1167605 := bbase (se 5 (by rfl) ⟨54731, by rfl⟩ : syracuseStep 1167605 = 109463) (by norm_num)
theorem B1757429 : Blo 778337 1757429 := bbase (se 5 (by rfl) ⟨82379, by rfl⟩ : syracuseStep 1757429 = 164759) (by norm_num)
theorem B1167629 : Blo 778337 1167629 := bbase (se 3 (by rfl) ⟨218930, by rfl⟩ : syracuseStep 1167629 = 437861) (by norm_num)
theorem B1167653 : Blo 778337 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B1167677 : Blo 778337 1167677 := bbase (se 3 (by rfl) ⟨218939, by rfl⟩ : syracuseStep 1167677 = 437879) (by norm_num)
theorem B1757501 : Blo 778337 1757501 := bbase (se 3 (by rfl) ⟨329531, by rfl⟩ : syracuseStep 1757501 = 659063) (by norm_num)
theorem B1167701 : Blo 778337 1167701 := bbase (se 10 (by rfl) ⟨1710, by rfl⟩ : syracuseStep 1167701 = 3421) (by norm_num)
theorem B1167725 : Blo 778337 1167725 := bbase (se 3 (by rfl) ⟨218948, by rfl⟩ : syracuseStep 1167725 = 437897) (by norm_num)
theorem B1167749 : Blo 778337 1167749 := bbase (se 4 (by rfl) ⟨109476, by rfl⟩ : syracuseStep 1167749 = 218953) (by norm_num)
theorem B1757573 : Blo 778337 1757573 := bbase (se 4 (by rfl) ⟨164772, by rfl⟩ : syracuseStep 1757573 = 329545) (by norm_num)
theorem B1167773 : Blo 778337 1167773 := bbase (se 3 (by rfl) ⟨218957, by rfl⟩ : syracuseStep 1167773 = 437915) (by norm_num)
theorem B938413 : Blo 778337 938413 := bbase (se 3 (by rfl) ⟨175952, by rfl⟩ : syracuseStep 938413 = 351905) (by norm_num)
theorem B1167797 : Blo 778337 1167797 := bbase (se 5 (by rfl) ⟨54740, by rfl⟩ : syracuseStep 1167797 = 109481) (by norm_num)
theorem B2970053 : Blo 778337 2970053 := bbase (se 4 (by rfl) ⟨278442, by rfl⟩ : syracuseStep 2970053 = 556885) (by norm_num)
theorem B1167821 : Blo 778337 1167821 := bbase (se 3 (by rfl) ⟨218966, by rfl⟩ : syracuseStep 1167821 = 437933) (by norm_num)
theorem B1757645 : Blo 778337 1757645 := bbase (se 3 (by rfl) ⟨329558, by rfl⟩ : syracuseStep 1757645 = 659117) (by norm_num)
theorem B938461 : Blo 778337 938461 := bbase (se 3 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 938461 = 351923) (by norm_num)
theorem B1167845 : Blo 778337 1167845 := bbase (se 4 (by rfl) ⟨109485, by rfl⟩ : syracuseStep 1167845 = 218971) (by norm_num)
theorem B1167869 : Blo 778337 1167869 := bbase (se 3 (by rfl) ⟨218975, by rfl⟩ : syracuseStep 1167869 = 437951) (by norm_num)
theorem B1167893 : Blo 778337 1167893 := bbase (se 6 (by rfl) ⟨27372, by rfl⟩ : syracuseStep 1167893 = 54745) (by norm_num)
theorem B1757717 : Blo 778337 1757717 := bbase (se 6 (by rfl) ⟨41196, by rfl⟩ : syracuseStep 1757717 = 82393) (by norm_num)
theorem B1167917 : Blo 778337 1167917 := bbase (se 3 (by rfl) ⟨218984, by rfl⟩ : syracuseStep 1167917 = 437969) (by norm_num)
theorem B1167941 : Blo 778337 1167941 := bbase (se 4 (by rfl) ⟨109494, by rfl⟩ : syracuseStep 1167941 = 218989) (by norm_num)
theorem B1167965 : Blo 778337 1167965 := bbase (se 3 (by rfl) ⟨218993, by rfl⟩ : syracuseStep 1167965 = 437987) (by norm_num)
theorem B1757789 : Blo 778337 1757789 := bbase (se 3 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 1757789 = 659171) (by norm_num)
theorem B1167989 : Blo 778337 1167989 := bbase (se 5 (by rfl) ⟨54749, by rfl⟩ : syracuseStep 1167989 = 109499) (by norm_num)
theorem B3953285 : Blo 778337 3953285 := bbase (se 4 (by rfl) ⟨370620, by rfl⟩ : syracuseStep 3953285 = 741241) (by norm_num)
theorem B1168013 : Blo 778337 1168013 := bbase (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) (by norm_num)
theorem B1168037 : Blo 778337 1168037 := bbase (se 4 (by rfl) ⟨109503, by rfl⟩ : syracuseStep 1168037 = 219007) (by norm_num)
theorem B1757861 : Blo 778337 1757861 := bbase (se 4 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 1757861 = 329599) (by norm_num)
theorem B1168061 : Blo 778337 1168061 := bbase (se 3 (by rfl) ⟨219011, by rfl⟩ : syracuseStep 1168061 = 438023) (by norm_num)
theorem B1168085 : Blo 778337 1168085 := bbase (se 7 (by rfl) ⟨13688, by rfl⟩ : syracuseStep 1168085 = 27377) (by norm_num)
theorem B2970341 : Blo 778337 2970341 := bbase (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) (by norm_num)
theorem B1168109 : Blo 778337 1168109 := bbase (se 3 (by rfl) ⟨219020, by rfl⟩ : syracuseStep 1168109 = 438041) (by norm_num)
theorem B1757933 : Blo 778337 1757933 := bbase (se 3 (by rfl) ⟨329612, by rfl⟩ : syracuseStep 1757933 = 659225) (by norm_num)
theorem B1168133 : Blo 778337 1168133 := bbase (se 4 (by rfl) ⟨109512, by rfl⟩ : syracuseStep 1168133 = 219025) (by norm_num)
theorem B1168157 : Blo 778337 1168157 := bbase (se 3 (by rfl) ⟨219029, by rfl⟩ : syracuseStep 1168157 = 438059) (by norm_num)
theorem B1168181 : Blo 778337 1168181 := bbase (se 5 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 1168181 = 109517) (by norm_num)
theorem B1758005 : Blo 778337 1758005 := bbase (se 5 (by rfl) ⟨82406, by rfl⟩ : syracuseStep 1758005 = 164813) (by norm_num)
theorem B1168205 : Blo 778337 1168205 := bbase (se 3 (by rfl) ⟨219038, by rfl⟩ : syracuseStep 1168205 = 438077) (by norm_num)
theorem B7131989 : Blo 778337 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B1168229 : Blo 778337 1168229 := bbase (se 4 (by rfl) ⟨109521, by rfl⟩ : syracuseStep 1168229 = 219043) (by norm_num)
theorem B2216821 : Blo 778337 2216821 := bbase (se 5 (by rfl) ⟨103913, by rfl⟩ : syracuseStep 2216821 = 207827) (by norm_num)
theorem B3756917 : Blo 778337 3756917 := bbase (se 5 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 3756917 = 352211) (by norm_num)
theorem B1168253 : Blo 778337 1168253 := bbase (se 3 (by rfl) ⟨219047, by rfl⟩ : syracuseStep 1168253 = 438095) (by norm_num)
theorem B1758077 : Blo 778337 1758077 := bbase (se 3 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 1758077 = 659279) (by norm_num)
theorem B1168277 : Blo 778337 1168277 := bbase (se 6 (by rfl) ⟨27381, by rfl⟩ : syracuseStep 1168277 = 54763) (by norm_num)
theorem B4445077 : Blo 778337 4445077 := bbase (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) (by norm_num)
theorem B1168301 : Blo 778337 1168301 := bbase (se 3 (by rfl) ⟨219056, by rfl⟩ : syracuseStep 1168301 = 438113) (by norm_num)
theorem B1168325 : Blo 778337 1168325 := bbase (se 4 (by rfl) ⟨109530, by rfl⟩ : syracuseStep 1168325 = 219061) (by norm_num)
theorem B1758149 : Blo 778337 1758149 := bbase (se 4 (by rfl) ⟨164826, by rfl⟩ : syracuseStep 1758149 = 329653) (by norm_num)
theorem B1168349 : Blo 778337 1168349 := bbase (se 3 (by rfl) ⟨219065, by rfl⟩ : syracuseStep 1168349 = 438131) (by norm_num)
theorem B1168373 : Blo 778337 1168373 := bbase (se 5 (by rfl) ⟨54767, by rfl⟩ : syracuseStep 1168373 = 109535) (by norm_num)
theorem B1168397 : Blo 778337 1168397 := bbase (se 3 (by rfl) ⟨219074, by rfl⟩ : syracuseStep 1168397 = 438149) (by norm_num)
theorem B1758221 : Blo 778337 1758221 := bbase (se 3 (by rfl) ⟨329666, by rfl⟩ : syracuseStep 1758221 = 659333) (by norm_num)
theorem B1168421 : Blo 778337 1168421 := bbase (se 4 (by rfl) ⟨109539, by rfl⟩ : syracuseStep 1168421 = 219079) (by norm_num)
theorem B1168445 : Blo 778337 1168445 := bbase (se 3 (by rfl) ⟨219083, by rfl⟩ : syracuseStep 1168445 = 438167) (by norm_num)
theorem B1168469 : Blo 778337 1168469 := bbase (se 8 (by rfl) ⟨6846, by rfl⟩ : syracuseStep 1168469 = 13693) (by norm_num)
theorem B1758293 : Blo 778337 1758293 := bbase (se 8 (by rfl) ⟨10302, by rfl⟩ : syracuseStep 1758293 = 20605) (by norm_num)
theorem B1168493 : Blo 778337 1168493 := bbase (se 3 (by rfl) ⟨219092, by rfl⟩ : syracuseStep 1168493 = 438185) (by norm_num)
theorem B939133 : Blo 778337 939133 := bbase (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) (by norm_num)
theorem B1168517 : Blo 778337 1168517 := bbase (se 4 (by rfl) ⟨109548, by rfl⟩ : syracuseStep 1168517 = 219097) (by norm_num)
theorem B8869013 : Blo 778337 8869013 := bbase (se 6 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 8869013 = 415735) (by norm_num)
theorem B1168541 : Blo 778337 1168541 := bbase (se 3 (by rfl) ⟨219101, by rfl⟩ : syracuseStep 1168541 = 438203) (by norm_num)
theorem B1758365 : Blo 778337 1758365 := bbase (se 3 (by rfl) ⟨329693, by rfl⟩ : syracuseStep 1758365 = 659387) (by norm_num)
theorem B1168565 : Blo 778337 1168565 := bbase (se 5 (by rfl) ⟨54776, by rfl⟩ : syracuseStep 1168565 = 109553) (by norm_num)
theorem B1168589 : Blo 778337 1168589 := bbase (se 3 (by rfl) ⟨219110, by rfl⟩ : syracuseStep 1168589 = 438221) (by norm_num)
theorem B1168613 : Blo 778337 1168613 := bbase (se 4 (by rfl) ⟨109557, by rfl⟩ : syracuseStep 1168613 = 219115) (by norm_num)
theorem B1758437 : Blo 778337 1758437 := bbase (se 4 (by rfl) ⟨164853, by rfl⟩ : syracuseStep 1758437 = 329707) (by norm_num)
theorem B1168637 : Blo 778337 1168637 := bbase (se 3 (by rfl) ⟨219119, by rfl⟩ : syracuseStep 1168637 = 438239) (by norm_num)
theorem B1168661 : Blo 778337 1168661 := bbase (se 6 (by rfl) ⟨27390, by rfl⟩ : syracuseStep 1168661 = 54781) (by norm_num)
theorem B1168685 : Blo 778337 1168685 := bbase (se 3 (by rfl) ⟨219128, by rfl⟩ : syracuseStep 1168685 = 438257) (by norm_num)
theorem B1758509 : Blo 778337 1758509 := bbase (se 3 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 1758509 = 659441) (by norm_num)
theorem B1168709 : Blo 778337 1168709 := bbase (se 4 (by rfl) ⟨109566, by rfl⟩ : syracuseStep 1168709 = 219133) (by norm_num)
theorem B1168733 : Blo 778337 1168733 := bbase (se 3 (by rfl) ⟨219137, by rfl⟩ : syracuseStep 1168733 = 438275) (by norm_num)
theorem B1168757 : Blo 778337 1168757 := bbase (se 5 (by rfl) ⟨54785, by rfl⟩ : syracuseStep 1168757 = 109571) (by norm_num)
theorem B1758581 : Blo 778337 1758581 := bbase (se 5 (by rfl) ⟨82433, by rfl⟩ : syracuseStep 1758581 = 164867) (by norm_num)
theorem B1168781 : Blo 778337 1168781 := bbase (se 3 (by rfl) ⟨219146, by rfl⟩ : syracuseStep 1168781 = 438293) (by norm_num)
theorem B1168805 : Blo 778337 1168805 := bbase (se 4 (by rfl) ⟨109575, by rfl⟩ : syracuseStep 1168805 = 219151) (by norm_num)
theorem B1168829 : Blo 778337 1168829 := bbase (se 3 (by rfl) ⟨219155, by rfl⟩ : syracuseStep 1168829 = 438311) (by norm_num)
theorem B1758653 : Blo 778337 1758653 := bbase (se 3 (by rfl) ⟨329747, by rfl⟩ : syracuseStep 1758653 = 659495) (by norm_num)
theorem B2807237 : Blo 778337 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B1168853 : Blo 778337 1168853 := bbase (se 7 (by rfl) ⟨13697, by rfl⟩ : syracuseStep 1168853 = 27395) (by norm_num)
theorem B1168877 : Blo 778337 1168877 := bbase (se 3 (by rfl) ⟨219164, by rfl⟩ : syracuseStep 1168877 = 438329) (by norm_num)
theorem B1168901 : Blo 778337 1168901 := bbase (se 4 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 1168901 = 219169) (by norm_num)
theorem B1758725 : Blo 778337 1758725 := bbase (se 4 (by rfl) ⟨164880, by rfl⟩ : syracuseStep 1758725 = 329761) (by norm_num)
theorem B1168925 : Blo 778337 1168925 := bbase (se 3 (by rfl) ⟨219173, by rfl⟩ : syracuseStep 1168925 = 438347) (by norm_num)
theorem B3331621 : Blo 778337 3331621 := bbase (se 4 (by rfl) ⟨312339, by rfl⟩ : syracuseStep 3331621 = 624679) (by norm_num)
theorem B1168949 : Blo 778337 1168949 := bbase (se 5 (by rfl) ⟨54794, by rfl⟩ : syracuseStep 1168949 = 109589) (by norm_num)
theorem B1168973 : Blo 778337 1168973 := bbase (se 3 (by rfl) ⟨219182, by rfl⟩ : syracuseStep 1168973 = 438365) (by norm_num)
theorem B1758797 : Blo 778337 1758797 := bbase (se 3 (by rfl) ⟨329774, by rfl⟩ : syracuseStep 1758797 = 659549) (by norm_num)
theorem B1168997 : Blo 778337 1168997 := bbase (se 4 (by rfl) ⟨109593, by rfl⟩ : syracuseStep 1168997 = 219187) (by norm_num)
theorem B1169021 : Blo 778337 1169021 := bbase (se 3 (by rfl) ⟨219191, by rfl⟩ : syracuseStep 1169021 = 438383) (by norm_num)
theorem B1169045 : Blo 778337 1169045 := bbase (se 6 (by rfl) ⟨27399, by rfl⟩ : syracuseStep 1169045 = 54799) (by norm_num)
theorem B1758869 : Blo 778337 1758869 := bbase (se 6 (by rfl) ⟨41223, by rfl⟩ : syracuseStep 1758869 = 82447) (by norm_num)
theorem B1169069 : Blo 778337 1169069 := bbase (se 3 (by rfl) ⟨219200, by rfl⟩ : syracuseStep 1169069 = 438401) (by norm_num)
theorem B1169093 : Blo 778337 1169093 := bbase (se 4 (by rfl) ⟨109602, by rfl⟩ : syracuseStep 1169093 = 219205) (by norm_num)
theorem B1169117 : Blo 778337 1169117 := bbase (se 3 (by rfl) ⟨219209, by rfl⟩ : syracuseStep 1169117 = 438419) (by norm_num)
theorem B1758941 : Blo 778337 1758941 := bbase (se 3 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 1758941 = 659603) (by norm_num)
theorem B1169141 : Blo 778337 1169141 := bbase (se 5 (by rfl) ⟨54803, by rfl⟩ : syracuseStep 1169141 = 109607) (by norm_num)
theorem B1169165 : Blo 778337 1169165 := bbase (se 3 (by rfl) ⟨219218, by rfl⟩ : syracuseStep 1169165 = 438437) (by norm_num)
theorem B1169189 : Blo 778337 1169189 := bbase (se 4 (by rfl) ⟨109611, by rfl⟩ : syracuseStep 1169189 = 219223) (by norm_num)
theorem B1759013 : Blo 778337 1759013 := bbase (se 4 (by rfl) ⟨164907, by rfl⟩ : syracuseStep 1759013 = 329815) (by norm_num)
theorem B1169213 : Blo 778337 1169213 := bbase (se 3 (by rfl) ⟨219227, by rfl⟩ : syracuseStep 1169213 = 438455) (by norm_num)
theorem B1169237 : Blo 778337 1169237 := bbase (se 9 (by rfl) ⟨3425, by rfl⟩ : syracuseStep 1169237 = 6851) (by norm_num)
theorem B1169261 : Blo 778337 1169261 := bbase (se 3 (by rfl) ⟨219236, by rfl⟩ : syracuseStep 1169261 = 438473) (by norm_num)
theorem B1759085 : Blo 778337 1759085 := bbase (se 3 (by rfl) ⟨329828, by rfl⟩ : syracuseStep 1759085 = 659657) (by norm_num)
theorem B1169285 : Blo 778337 1169285 := bbase (se 4 (by rfl) ⟨109620, by rfl⟩ : syracuseStep 1169285 = 219241) (by norm_num)
theorem B3954581 : Blo 778337 3954581 := bbase (se 6 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 3954581 = 185371) (by norm_num)
theorem B1169309 : Blo 778337 1169309 := bbase (se 3 (by rfl) ⟨219245, by rfl⟩ : syracuseStep 1169309 = 438491) (by norm_num)
theorem B1169333 : Blo 778337 1169333 := bbase (se 5 (by rfl) ⟨54812, by rfl⟩ : syracuseStep 1169333 = 109625) (by norm_num)
theorem B1759157 : Blo 778337 1759157 := bbase (se 5 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 1759157 = 164921) (by norm_num)
theorem B1169357 : Blo 778337 1169357 := bbase (se 3 (by rfl) ⟨219254, by rfl⟩ : syracuseStep 1169357 = 438509) (by norm_num)
theorem B1169381 : Blo 778337 1169381 := bbase (se 4 (by rfl) ⟨109629, by rfl⟩ : syracuseStep 1169381 = 219259) (by norm_num)
theorem B1169405 : Blo 778337 1169405 := bbase (se 3 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 1169405 = 438527) (by norm_num)
theorem B1759229 : Blo 778337 1759229 := bbase (se 3 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 1759229 = 659711) (by norm_num)
theorem B1169429 : Blo 778337 1169429 := bbase (se 6 (by rfl) ⟨27408, by rfl⟩ : syracuseStep 1169429 = 54817) (by norm_num)
theorem B1169453 : Blo 778337 1169453 := bbase (se 3 (by rfl) ⟨219272, by rfl⟩ : syracuseStep 1169453 = 438545) (by norm_num)
theorem B1169477 : Blo 778337 1169477 := bbase (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) (by norm_num)
theorem B1759301 : Blo 778337 1759301 := bbase (se 4 (by rfl) ⟨164934, by rfl⟩ : syracuseStep 1759301 = 329869) (by norm_num)
theorem B1169501 : Blo 778337 1169501 := bbase (se 3 (by rfl) ⟨219281, by rfl⟩ : syracuseStep 1169501 = 438563) (by norm_num)
theorem B1169525 : Blo 778337 1169525 := bbase (se 5 (by rfl) ⟨54821, by rfl⟩ : syracuseStep 1169525 = 109643) (by norm_num)
theorem B1169549 : Blo 778337 1169549 := bbase (se 3 (by rfl) ⟨219290, by rfl⟩ : syracuseStep 1169549 = 438581) (by norm_num)
theorem B1759373 : Blo 778337 1759373 := bbase (se 3 (by rfl) ⟨329882, by rfl⟩ : syracuseStep 1759373 = 659765) (by norm_num)
theorem B1169573 : Blo 778337 1169573 := bbase (se 4 (by rfl) ⟨109647, by rfl⟩ : syracuseStep 1169573 = 219295) (by norm_num)
theorem B1169597 : Blo 778337 1169597 := bbase (se 3 (by rfl) ⟨219299, by rfl⟩ : syracuseStep 1169597 = 438599) (by norm_num)
theorem B1169621 : Blo 778337 1169621 := bbase (se 7 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 1169621 = 27413) (by norm_num)
theorem B1759445 : Blo 778337 1759445 := bbase (se 7 (by rfl) ⟨20618, by rfl⟩ : syracuseStep 1759445 = 41237) (by norm_num)
theorem B1169645 : Blo 778337 1169645 := bbase (se 3 (by rfl) ⟨219308, by rfl⟩ : syracuseStep 1169645 = 438617) (by norm_num)
theorem B1169669 : Blo 778337 1169669 := bbase (se 4 (by rfl) ⟨109656, by rfl⟩ : syracuseStep 1169669 = 219313) (by norm_num)
theorem B11229461 : Blo 778337 11229461 := bbase (se 6 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 11229461 = 526381) (by norm_num)
theorem B1169693 : Blo 778337 1169693 := bbase (se 3 (by rfl) ⟨219317, by rfl⟩ : syracuseStep 1169693 = 438635) (by norm_num)
theorem B1759517 : Blo 778337 1759517 := bbase (se 3 (by rfl) ⟨329909, by rfl⟩ : syracuseStep 1759517 = 659819) (by norm_num)
theorem B1169717 : Blo 778337 1169717 := bbase (se 5 (by rfl) ⟨54830, by rfl⟩ : syracuseStep 1169717 = 109661) (by norm_num)
theorem B1169741 : Blo 778337 1169741 := bbase (se 3 (by rfl) ⟨219326, by rfl⟩ : syracuseStep 1169741 = 438653) (by norm_num)
theorem B1169765 : Blo 778337 1169765 := bbase (se 4 (by rfl) ⟨109665, by rfl⟩ : syracuseStep 1169765 = 219331) (by norm_num)
theorem B1759589 : Blo 778337 1759589 := bbase (se 4 (by rfl) ⟨164961, by rfl⟩ : syracuseStep 1759589 = 329923) (by norm_num)
theorem B1169789 : Blo 778337 1169789 := bbase (se 3 (by rfl) ⟨219335, by rfl⟩ : syracuseStep 1169789 = 438671) (by norm_num)
theorem B1169813 : Blo 778337 1169813 := bbase (se 6 (by rfl) ⟨27417, by rfl⟩ : syracuseStep 1169813 = 54835) (by norm_num)
theorem B1169837 : Blo 778337 1169837 := bbase (se 3 (by rfl) ⟨219344, by rfl⟩ : syracuseStep 1169837 = 438689) (by norm_num)
theorem B1759661 : Blo 778337 1759661 := bbase (se 3 (by rfl) ⟨329936, by rfl⟩ : syracuseStep 1759661 = 659873) (by norm_num)
theorem B1169861 : Blo 778337 1169861 := bbase (se 4 (by rfl) ⟨109674, by rfl⟩ : syracuseStep 1169861 = 219349) (by norm_num)
theorem B1169885 : Blo 778337 1169885 := bbase (se 3 (by rfl) ⟨219353, by rfl⟩ : syracuseStep 1169885 = 438707) (by norm_num)
theorem B1169909 : Blo 778337 1169909 := bbase (se 5 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 1169909 = 109679) (by norm_num)
theorem B5003765 : Blo 778337 5003765 := bbase (se 5 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 5003765 = 469103) (by norm_num)
theorem B1759733 : Blo 778337 1759733 := bbase (se 5 (by rfl) ⟨82487, by rfl⟩ : syracuseStep 1759733 = 164975) (by norm_num)
theorem B1169933 : Blo 778337 1169933 := bbase (se 3 (by rfl) ⟨219362, by rfl⟩ : syracuseStep 1169933 = 438725) (by norm_num)
theorem B1169957 : Blo 778337 1169957 := bbase (se 4 (by rfl) ⟨109683, by rfl⟩ : syracuseStep 1169957 = 219367) (by norm_num)
theorem B1169981 : Blo 778337 1169981 := bbase (se 3 (by rfl) ⟨219371, by rfl⟩ : syracuseStep 1169981 = 438743) (by norm_num)
theorem B1759805 : Blo 778337 1759805 := bbase (se 3 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 1759805 = 659927) (by norm_num)
theorem B1170005 : Blo 778337 1170005 := bbase (se 8 (by rfl) ⟨6855, by rfl⟩ : syracuseStep 1170005 = 13711) (by norm_num)
theorem B1170029 : Blo 778337 1170029 := bbase (se 3 (by rfl) ⟨219380, by rfl⟩ : syracuseStep 1170029 = 438761) (by norm_num)
theorem B1170053 : Blo 778337 1170053 := bbase (se 4 (by rfl) ⟨109692, by rfl⟩ : syracuseStep 1170053 = 219385) (by norm_num)
theorem B1759877 : Blo 778337 1759877 := bbase (se 4 (by rfl) ⟨164988, by rfl⟩ : syracuseStep 1759877 = 329977) (by norm_num)
theorem B1170077 : Blo 778337 1170077 := bbase (se 3 (by rfl) ⟨219389, by rfl⟩ : syracuseStep 1170077 = 438779) (by norm_num)
theorem B1170101 : Blo 778337 1170101 := bbase (se 5 (by rfl) ⟨54848, by rfl⟩ : syracuseStep 1170101 = 109697) (by norm_num)
theorem B1170125 : Blo 778337 1170125 := bbase (se 3 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 1170125 = 438797) (by norm_num)
theorem B1759949 : Blo 778337 1759949 := bbase (se 3 (by rfl) ⟨329990, by rfl⟩ : syracuseStep 1759949 = 659981) (by norm_num)
theorem B1170149 : Blo 778337 1170149 := bbase (se 4 (by rfl) ⟨109701, by rfl⟩ : syracuseStep 1170149 = 219403) (by norm_num)
theorem B1170173 : Blo 778337 1170173 := bbase (se 3 (by rfl) ⟨219407, by rfl⟩ : syracuseStep 1170173 = 438815) (by norm_num)
theorem B1170197 : Blo 778337 1170197 := bbase (se 6 (by rfl) ⟨27426, by rfl⟩ : syracuseStep 1170197 = 54853) (by norm_num)
theorem B1760021 : Blo 778337 1760021 := bbase (se 6 (by rfl) ⟨41250, by rfl⟩ : syracuseStep 1760021 = 82501) (by norm_num)
theorem B1334045 : Blo 778337 1334045 := bbase (se 3 (by rfl) ⟨250133, by rfl⟩ : syracuseStep 1334045 = 500267) (by norm_num)
theorem B1170221 : Blo 778337 1170221 := bbase (se 3 (by rfl) ⟨219416, by rfl⟩ : syracuseStep 1170221 = 438833) (by norm_num)
theorem B1170245 : Blo 778337 1170245 := bbase (se 4 (by rfl) ⟨109710, by rfl⟩ : syracuseStep 1170245 = 219421) (by norm_num)
theorem B842581 : Blo 778337 842581 := bbase (se 9 (by rfl) ⟨2468, by rfl⟩ : syracuseStep 842581 = 4937) (by norm_num)
theorem B4447061 : Blo 778337 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B1170269 : Blo 778337 1170269 := bbase (se 3 (by rfl) ⟨219425, by rfl⟩ : syracuseStep 1170269 = 438851) (by norm_num)
theorem B1760093 : Blo 778337 1760093 := bbase (se 3 (by rfl) ⟨330017, by rfl⟩ : syracuseStep 1760093 = 660035) (by norm_num)
theorem B1170293 : Blo 778337 1170293 := bbase (se 5 (by rfl) ⟨54857, by rfl⟩ : syracuseStep 1170293 = 109715) (by norm_num)
theorem B1170317 : Blo 778337 1170317 := bbase (se 3 (by rfl) ⟨219434, by rfl⟩ : syracuseStep 1170317 = 438869) (by norm_num)
theorem B1170341 : Blo 778337 1170341 := bbase (se 4 (by rfl) ⟨109719, by rfl⟩ : syracuseStep 1170341 = 219439) (by norm_num)
theorem B1760165 : Blo 778337 1760165 := bbase (se 4 (by rfl) ⟨165015, by rfl⟩ : syracuseStep 1760165 = 330031) (by norm_num)
theorem B1170365 : Blo 778337 1170365 := bbase (se 3 (by rfl) ⟨219443, by rfl⟩ : syracuseStep 1170365 = 438887) (by norm_num)
theorem B1498061 : Blo 778337 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B1170389 : Blo 778337 1170389 := bbase (se 7 (by rfl) ⟨13715, by rfl⟩ : syracuseStep 1170389 = 27431) (by norm_num)
theorem B1334237 : Blo 778337 1334237 := bbase (se 3 (by rfl) ⟨250169, by rfl⟩ : syracuseStep 1334237 = 500339) (by norm_num)
theorem B1170413 : Blo 778337 1170413 := bbase (se 3 (by rfl) ⟨219452, by rfl⟩ : syracuseStep 1170413 = 438905) (by norm_num)
theorem B1760237 : Blo 778337 1760237 := bbase (se 3 (by rfl) ⟨330044, by rfl⟩ : syracuseStep 1760237 = 660089) (by norm_num)
theorem B3333109 : Blo 778337 3333109 := bbase (se 5 (by rfl) ⟨156239, by rfl⟩ : syracuseStep 3333109 = 312479) (by norm_num)
theorem B1170437 : Blo 778337 1170437 := bbase (se 4 (by rfl) ⟨109728, by rfl⟩ : syracuseStep 1170437 = 219457) (by norm_num)
theorem B3333125 : Blo 778337 3333125 := bbase (se 4 (by rfl) ⟨312480, by rfl⟩ : syracuseStep 3333125 = 624961) (by norm_num)
theorem B1170461 : Blo 778337 1170461 := bbase (se 3 (by rfl) ⟨219461, by rfl⟩ : syracuseStep 1170461 = 438923) (by norm_num)
theorem B1170485 : Blo 778337 1170485 := bbase (se 5 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 1170485 = 109733) (by norm_num)
theorem B1170509 : Blo 778337 1170509 := bbase (se 3 (by rfl) ⟨219470, by rfl⟩ : syracuseStep 1170509 = 438941) (by norm_num)
theorem B1170533 : Blo 778337 1170533 := bbase (se 4 (by rfl) ⟨109737, by rfl⟩ : syracuseStep 1170533 = 219475) (by norm_num)
theorem B5921909 : Blo 778337 5921909 := bbase (se 5 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 5921909 = 555179) (by norm_num)
theorem B1334389 : Blo 778337 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B875641 : Blo 778337 875641 := bbase (se 2 (by rfl) ⟨328365, by rfl⟩ : syracuseStep 875641 = 656731) (by norm_num)
theorem B1170557 : Blo 778337 1170557 := bbase (se 3 (by rfl) ⟨219479, by rfl⟩ : syracuseStep 1170557 = 438959) (by norm_num)
theorem B1170581 : Blo 778337 1170581 := bbase (se 6 (by rfl) ⟨27435, by rfl⟩ : syracuseStep 1170581 = 54871) (by norm_num)
theorem B875677 : Blo 778337 875677 := bbase (se 3 (by rfl) ⟨164189, by rfl⟩ : syracuseStep 875677 = 328379) (by norm_num)
theorem B3955877 : Blo 778337 3955877 := bbase (se 4 (by rfl) ⟨370863, by rfl⟩ : syracuseStep 3955877 = 741727) (by norm_num)
theorem B1170605 : Blo 778337 1170605 := bbase (se 3 (by rfl) ⟨219488, by rfl⟩ : syracuseStep 1170605 = 438977) (by norm_num)
theorem B875713 : Blo 778337 875713 := bbase (se 2 (by rfl) ⟨328392, by rfl⟩ : syracuseStep 875713 = 656785) (by norm_num)
theorem B1170629 : Blo 778337 1170629 := bbase (se 4 (by rfl) ⟨109746, by rfl⟩ : syracuseStep 1170629 = 219493) (by norm_num)
theorem B1170653 : Blo 778337 1170653 := bbase (se 3 (by rfl) ⟨219497, by rfl⟩ : syracuseStep 1170653 = 438995) (by norm_num)
theorem B875749 : Blo 778337 875749 := bbase (se 4 (by rfl) ⟨82101, by rfl⟩ : syracuseStep 875749 = 164203) (by norm_num)
theorem B1170677 : Blo 778337 1170677 := bbase (se 5 (by rfl) ⟨54875, by rfl⟩ : syracuseStep 1170677 = 109751) (by norm_num)
theorem B875785 : Blo 778337 875785 := bbase (se 2 (by rfl) ⟨328419, by rfl⟩ : syracuseStep 875785 = 656839) (by norm_num)
theorem B1170701 : Blo 778337 1170701 := bbase (se 3 (by rfl) ⟨219506, by rfl⟩ : syracuseStep 1170701 = 439013) (by norm_num)
theorem B1170725 : Blo 778337 1170725 := bbase (se 4 (by rfl) ⟨109755, by rfl⟩ : syracuseStep 1170725 = 219511) (by norm_num)
theorem B875821 : Blo 778337 875821 := bbase (se 3 (by rfl) ⟨164216, by rfl⟩ : syracuseStep 875821 = 328433) (by norm_num)
theorem B1170749 : Blo 778337 1170749 := bbase (se 3 (by rfl) ⟨219515, by rfl⟩ : syracuseStep 1170749 = 439031) (by norm_num)
theorem B875857 : Blo 778337 875857 := bbase (se 2 (by rfl) ⟨328446, by rfl⟩ : syracuseStep 875857 = 656893) (by norm_num)
theorem B1170773 : Blo 778337 1170773 := bbase (se 11 (by rfl) ⟨857, by rfl⟩ : syracuseStep 1170773 = 1715) (by norm_num)
theorem B1170797 : Blo 778337 1170797 := bbase (se 3 (by rfl) ⟨219524, by rfl⟩ : syracuseStep 1170797 = 439049) (by norm_num)
theorem B875893 : Blo 778337 875893 := bbase (se 5 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 875893 = 82115) (by norm_num)
theorem B1170821 : Blo 778337 1170821 := bbase (se 4 (by rfl) ⟨109764, by rfl⟩ : syracuseStep 1170821 = 219529) (by norm_num)
theorem B875929 : Blo 778337 875929 := bbase (se 2 (by rfl) ⟨328473, by rfl⟩ : syracuseStep 875929 = 656947) (by norm_num)
theorem B1170845 : Blo 778337 1170845 := bbase (se 3 (by rfl) ⟨219533, by rfl⟩ : syracuseStep 1170845 = 439067) (by norm_num)
theorem B1170869 : Blo 778337 1170869 := bbase (se 5 (by rfl) ⟨54884, by rfl⟩ : syracuseStep 1170869 = 109769) (by norm_num)
theorem B875965 : Blo 778337 875965 := bbase (se 3 (by rfl) ⟨164243, by rfl⟩ : syracuseStep 875965 = 328487) (by norm_num)
theorem B1170893 : Blo 778337 1170893 := bbase (se 3 (by rfl) ⟨219542, by rfl⟩ : syracuseStep 1170893 = 439085) (by norm_num)
theorem B876001 : Blo 778337 876001 := bbase (se 2 (by rfl) ⟨328500, by rfl⟩ : syracuseStep 876001 = 657001) (by norm_num)
theorem B1170917 : Blo 778337 1170917 := bbase (se 4 (by rfl) ⟨109773, by rfl⟩ : syracuseStep 1170917 = 219547) (by norm_num)
theorem B1924597 : Blo 778337 1924597 := bbase (se 5 (by rfl) ⟨90215, by rfl⟩ : syracuseStep 1924597 = 180431) (by norm_num)
theorem B1170941 : Blo 778337 1170941 := bbase (se 3 (by rfl) ⟨219551, by rfl⟩ : syracuseStep 1170941 = 439103) (by norm_num)
theorem B876037 : Blo 778337 876037 := bbase (se 4 (by rfl) ⟨82128, by rfl⟩ : syracuseStep 876037 = 164257) (by norm_num)
theorem B1170965 : Blo 778337 1170965 := bbase (se 6 (by rfl) ⟨27444, by rfl⟩ : syracuseStep 1170965 = 54889) (by norm_num)
theorem B876073 : Blo 778337 876073 := bbase (se 2 (by rfl) ⟨328527, by rfl⟩ : syracuseStep 876073 = 657055) (by norm_num)
theorem B1170989 : Blo 778337 1170989 := bbase (se 3 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 1170989 = 439121) (by norm_num)
theorem B1171013 : Blo 778337 1171013 := bbase (se 4 (by rfl) ⟨109782, by rfl⟩ : syracuseStep 1171013 = 219565) (by norm_num)
theorem B876109 : Blo 778337 876109 := bbase (se 3 (by rfl) ⟨164270, by rfl⟩ : syracuseStep 876109 = 328541) (by norm_num)
theorem B1171037 : Blo 778337 1171037 := bbase (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) (by norm_num)
theorem B1662565 : Blo 778337 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B876145 : Blo 778337 876145 := bbase (se 2 (by rfl) ⟨328554, by rfl⟩ : syracuseStep 876145 = 657109) (by norm_num)
theorem B1171061 : Blo 778337 1171061 := bbase (se 5 (by rfl) ⟨54893, by rfl⟩ : syracuseStep 1171061 = 109787) (by norm_num)
theorem B1171085 : Blo 778337 1171085 := bbase (se 3 (by rfl) ⟨219578, by rfl⟩ : syracuseStep 1171085 = 439157) (by norm_num)
theorem B876181 : Blo 778337 876181 := bbase (se 6 (by rfl) ⟨20535, by rfl⟩ : syracuseStep 876181 = 41071) (by norm_num)
theorem B2219669 : Blo 778337 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B13721237 : Blo 778337 13721237 := bbase (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) (by norm_num)
theorem B1171109 : Blo 778337 1171109 := bbase (se 4 (by rfl) ⟨109791, by rfl⟩ : syracuseStep 1171109 = 219583) (by norm_num)
theorem B876217 : Blo 778337 876217 := bbase (se 2 (by rfl) ⟨328581, by rfl⟩ : syracuseStep 876217 = 657163) (by norm_num)
theorem B1171133 : Blo 778337 1171133 := bbase (se 3 (by rfl) ⟨219587, by rfl⟩ : syracuseStep 1171133 = 439175) (by norm_num)
theorem B1171157 : Blo 778337 1171157 := bbase (se 7 (by rfl) ⟨13724, by rfl⟩ : syracuseStep 1171157 = 27449) (by norm_num)
theorem B876253 : Blo 778337 876253 := bbase (se 3 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 876253 = 328595) (by norm_num)
theorem B1171181 : Blo 778337 1171181 := bbase (se 3 (by rfl) ⟨219596, by rfl⟩ : syracuseStep 1171181 = 439193) (by norm_num)
theorem B876289 : Blo 778337 876289 := bbase (se 2 (by rfl) ⟨328608, by rfl⟩ : syracuseStep 876289 = 657217) (by norm_num)
theorem B1171205 : Blo 778337 1171205 := bbase (se 4 (by rfl) ⟨109800, by rfl⟩ : syracuseStep 1171205 = 219601) (by norm_num)
theorem B1171229 : Blo 778337 1171229 := bbase (se 3 (by rfl) ⟨219605, by rfl⟩ : syracuseStep 1171229 = 439211) (by norm_num)
theorem B876325 : Blo 778337 876325 := bbase (se 4 (by rfl) ⟨82155, by rfl⟩ : syracuseStep 876325 = 164311) (by norm_num)
theorem B1171253 : Blo 778337 1171253 := bbase (se 5 (by rfl) ⟨54902, by rfl⟩ : syracuseStep 1171253 = 109805) (by norm_num)
theorem B876361 : Blo 778337 876361 := bbase (se 2 (by rfl) ⟨328635, by rfl⟩ : syracuseStep 876361 = 657271) (by norm_num)
theorem B1171277 : Blo 778337 1171277 := bbase (se 3 (by rfl) ⟨219614, by rfl⟩ : syracuseStep 1171277 = 439229) (by norm_num)
theorem B1171301 : Blo 778337 1171301 := bbase (se 4 (by rfl) ⟨109809, by rfl⟩ : syracuseStep 1171301 = 219619) (by norm_num)
theorem B876397 : Blo 778337 876397 := bbase (se 3 (by rfl) ⟨164324, by rfl⟩ : syracuseStep 876397 = 328649) (by norm_num)
theorem B1171325 : Blo 778337 1171325 := bbase (se 3 (by rfl) ⟨219623, by rfl⟩ : syracuseStep 1171325 = 439247) (by norm_num)
theorem B876433 : Blo 778337 876433 := bbase (se 2 (by rfl) ⟨328662, by rfl⟩ : syracuseStep 876433 = 657325) (by norm_num)
theorem B1171349 : Blo 778337 1171349 := bbase (se 6 (by rfl) ⟨27453, by rfl⟩ : syracuseStep 1171349 = 54907) (by norm_num)
theorem B1171373 : Blo 778337 1171373 := bbase (se 3 (by rfl) ⟨219632, by rfl⟩ : syracuseStep 1171373 = 439265) (by norm_num)
theorem B876469 : Blo 778337 876469 := bbase (se 5 (by rfl) ⟨41084, by rfl⟩ : syracuseStep 876469 = 82169) (by norm_num)
theorem B1171397 : Blo 778337 1171397 := bbase (se 4 (by rfl) ⟨109818, by rfl⟩ : syracuseStep 1171397 = 219637) (by norm_num)
theorem B876505 : Blo 778337 876505 := bbase (se 2 (by rfl) ⟨328689, by rfl⟩ : syracuseStep 876505 = 657379) (by norm_num)
theorem B1171421 : Blo 778337 1171421 := bbase (se 3 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 1171421 = 439283) (by norm_num)
theorem B1171445 : Blo 778337 1171445 := bbase (se 5 (by rfl) ⟨54911, by rfl⟩ : syracuseStep 1171445 = 109823) (by norm_num)
theorem B876541 : Blo 778337 876541 := bbase (se 3 (by rfl) ⟨164351, by rfl⟩ : syracuseStep 876541 = 328703) (by norm_num)
theorem B1171469 : Blo 778337 1171469 := bbase (se 3 (by rfl) ⟨219650, by rfl⟩ : syracuseStep 1171469 = 439301) (by norm_num)
theorem B876577 : Blo 778337 876577 := bbase (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) (by norm_num)
theorem B1171493 : Blo 778337 1171493 := bbase (se 4 (by rfl) ⟨109827, by rfl⟩ : syracuseStep 1171493 = 219655) (by norm_num)
theorem B1171517 : Blo 778337 1171517 := bbase (se 3 (by rfl) ⟨219659, by rfl⟩ : syracuseStep 1171517 = 439319) (by norm_num)
theorem B876613 : Blo 778337 876613 := bbase (se 4 (by rfl) ⟨82182, by rfl⟩ : syracuseStep 876613 = 164365) (by norm_num)
theorem B1171541 : Blo 778337 1171541 := bbase (se 8 (by rfl) ⟨6864, by rfl⟩ : syracuseStep 1171541 = 13729) (by norm_num)
theorem B876649 : Blo 778337 876649 := bbase (se 2 (by rfl) ⟨328743, by rfl⟩ : syracuseStep 876649 = 657487) (by norm_num)
theorem B1171565 : Blo 778337 1171565 := bbase (se 3 (by rfl) ⟨219668, by rfl⟩ : syracuseStep 1171565 = 439337) (by norm_num)
theorem B1171589 : Blo 778337 1171589 := bbase (se 4 (by rfl) ⟨109836, by rfl⟩ : syracuseStep 1171589 = 219673) (by norm_num)
theorem B876685 : Blo 778337 876685 := bbase (se 3 (by rfl) ⟨164378, by rfl⟩ : syracuseStep 876685 = 328757) (by norm_num)
theorem B1171613 : Blo 778337 1171613 := bbase (se 3 (by rfl) ⟨219677, by rfl⟩ : syracuseStep 1171613 = 439355) (by norm_num)
theorem B876721 : Blo 778337 876721 := bbase (se 2 (by rfl) ⟨328770, by rfl⟩ : syracuseStep 876721 = 657541) (by norm_num)
theorem B1171637 : Blo 778337 1171637 := bbase (se 5 (by rfl) ⟨54920, by rfl⟩ : syracuseStep 1171637 = 109841) (by norm_num)
theorem B1171661 : Blo 778337 1171661 := bbase (se 3 (by rfl) ⟨219686, by rfl⟩ : syracuseStep 1171661 = 439373) (by norm_num)
theorem B876757 : Blo 778337 876757 := bbase (se 7 (by rfl) ⟨10274, by rfl⟩ : syracuseStep 876757 = 20549) (by norm_num)
theorem B1171685 : Blo 778337 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B876793 : Blo 778337 876793 := bbase (se 2 (by rfl) ⟨328797, by rfl⟩ : syracuseStep 876793 = 657595) (by norm_num)
theorem B1171709 : Blo 778337 1171709 := bbase (se 3 (by rfl) ⟨219695, by rfl⟩ : syracuseStep 1171709 = 439391) (by norm_num)
theorem B1171733 : Blo 778337 1171733 := bbase (se 6 (by rfl) ⟨27462, by rfl⟩ : syracuseStep 1171733 = 54925) (by norm_num)
theorem B876829 : Blo 778337 876829 := bbase (se 3 (by rfl) ⟨164405, by rfl⟩ : syracuseStep 876829 = 328811) (by norm_num)
theorem B1171757 : Blo 778337 1171757 := bbase (se 3 (by rfl) ⟨219704, by rfl⟩ : syracuseStep 1171757 = 439409) (by norm_num)
theorem B876865 : Blo 778337 876865 := bbase (se 2 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 876865 = 657649) (by norm_num)
theorem B1171781 : Blo 778337 1171781 := bbase (se 4 (by rfl) ⟨109854, by rfl⟩ : syracuseStep 1171781 = 219709) (by norm_num)
theorem B1171805 : Blo 778337 1171805 := bbase (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) (by norm_num)
theorem B876901 : Blo 778337 876901 := bbase (se 4 (by rfl) ⟨82209, by rfl⟩ : syracuseStep 876901 = 164419) (by norm_num)
theorem B1171829 : Blo 778337 1171829 := bbase (se 5 (by rfl) ⟨54929, by rfl⟩ : syracuseStep 1171829 = 109859) (by norm_num)
theorem B876937 : Blo 778337 876937 := bbase (se 2 (by rfl) ⟨328851, by rfl⟩ : syracuseStep 876937 = 657703) (by norm_num)
theorem B1171853 : Blo 778337 1171853 := bbase (se 3 (by rfl) ⟨219722, by rfl⟩ : syracuseStep 1171853 = 439445) (by norm_num)
theorem B1171877 : Blo 778337 1171877 := bbase (se 4 (by rfl) ⟨109863, by rfl⟩ : syracuseStep 1171877 = 219727) (by norm_num)
theorem B876973 : Blo 778337 876973 := bbase (se 3 (by rfl) ⟨164432, by rfl⟩ : syracuseStep 876973 = 328865) (by norm_num)
theorem B3957173 : Blo 778337 3957173 := bbase (se 5 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 3957173 = 370985) (by norm_num)
theorem B1171901 : Blo 778337 1171901 := bbase (se 3 (by rfl) ⟨219731, by rfl⟩ : syracuseStep 1171901 = 439463) (by norm_num)
theorem B877009 : Blo 778337 877009 := bbase (se 2 (by rfl) ⟨328878, by rfl⟩ : syracuseStep 877009 = 657757) (by norm_num)
theorem B1171925 : Blo 778337 1171925 := bbase (se 7 (by rfl) ⟨13733, by rfl⟩ : syracuseStep 1171925 = 27467) (by norm_num)
theorem B8249813 : Blo 778337 8249813 := bbase (se 7 (by rfl) ⟨96677, by rfl⟩ : syracuseStep 8249813 = 193355) (by norm_num)
theorem B1663453 : Blo 778337 1663453 := bbase (se 3 (by rfl) ⟨311897, by rfl⟩ : syracuseStep 1663453 = 623795) (by norm_num)
theorem B1171949 : Blo 778337 1171949 := bbase (se 3 (by rfl) ⟨219740, by rfl⟩ : syracuseStep 1171949 = 439481) (by norm_num)
theorem B877045 : Blo 778337 877045 := bbase (se 5 (by rfl) ⟨41111, by rfl⟩ : syracuseStep 877045 = 82223) (by norm_num)
theorem B1171973 : Blo 778337 1171973 := bbase (se 4 (by rfl) ⟨109872, by rfl⟩ : syracuseStep 1171973 = 219745) (by norm_num)
theorem B877081 : Blo 778337 877081 := bbase (se 2 (by rfl) ⟨328905, by rfl⟩ : syracuseStep 877081 = 657811) (by norm_num)
theorem B1171997 : Blo 778337 1171997 := bbase (se 3 (by rfl) ⟨219749, by rfl⟩ : syracuseStep 1171997 = 439499) (by norm_num)
theorem B2253349 : Blo 778337 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B1172021 : Blo 778337 1172021 := bbase (se 5 (by rfl) ⟨54938, by rfl⟩ : syracuseStep 1172021 = 109877) (by norm_num)
theorem B877117 : Blo 778337 877117 := bbase (se 3 (by rfl) ⟨164459, by rfl⟩ : syracuseStep 877117 = 328919) (by norm_num)
theorem B1172045 : Blo 778337 1172045 := bbase (se 3 (by rfl) ⟨219758, by rfl⟩ : syracuseStep 1172045 = 439517) (by norm_num)
theorem B1663573 : Blo 778337 1663573 := bbase (se 8 (by rfl) ⟨9747, by rfl⟩ : syracuseStep 1663573 = 19495) (by norm_num)
theorem B877153 : Blo 778337 877153 := bbase (se 2 (by rfl) ⟨328932, by rfl⟩ : syracuseStep 877153 = 657865) (by norm_num)
theorem B1172069 : Blo 778337 1172069 := bbase (se 4 (by rfl) ⟨109881, by rfl⟩ : syracuseStep 1172069 = 219763) (by norm_num)
theorem B1172093 : Blo 778337 1172093 := bbase (se 3 (by rfl) ⟨219767, by rfl⟩ : syracuseStep 1172093 = 439535) (by norm_num)
theorem B877189 : Blo 778337 877189 := bbase (se 4 (by rfl) ⟨82236, by rfl⟩ : syracuseStep 877189 = 164473) (by norm_num)
theorem B1172117 : Blo 778337 1172117 := bbase (se 6 (by rfl) ⟨27471, by rfl⟩ : syracuseStep 1172117 = 54943) (by norm_num)
theorem B877225 : Blo 778337 877225 := bbase (se 2 (by rfl) ⟨328959, by rfl⟩ : syracuseStep 877225 = 657919) (by norm_num)
theorem B1172141 : Blo 778337 1172141 := bbase (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) (by norm_num)
theorem B1172165 : Blo 778337 1172165 := bbase (se 4 (by rfl) ⟨109890, by rfl⟩ : syracuseStep 1172165 = 219781) (by norm_num)
theorem B877261 : Blo 778337 877261 := bbase (se 3 (by rfl) ⟨164486, by rfl⟩ : syracuseStep 877261 = 328973) (by norm_num)
theorem B1172189 : Blo 778337 1172189 := bbase (se 3 (by rfl) ⟨219785, by rfl⟩ : syracuseStep 1172189 = 439571) (by norm_num)
theorem B877297 : Blo 778337 877297 := bbase (se 2 (by rfl) ⟨328986, by rfl⟩ : syracuseStep 877297 = 657973) (by norm_num)
theorem B1172213 : Blo 778337 1172213 := bbase (se 5 (by rfl) ⟨54947, by rfl⟩ : syracuseStep 1172213 = 109895) (by norm_num)
theorem B2286341 : Blo 778337 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B1172237 : Blo 778337 1172237 := bbase (se 3 (by rfl) ⟨219794, by rfl⟩ : syracuseStep 1172237 = 439589) (by norm_num)
theorem B877333 : Blo 778337 877333 := bbase (se 6 (by rfl) ⟨20562, by rfl⟩ : syracuseStep 877333 = 41125) (by norm_num)
theorem B1172261 : Blo 778337 1172261 := bbase (se 4 (by rfl) ⟨109899, by rfl⟩ : syracuseStep 1172261 = 219799) (by norm_num)
theorem B2220853 : Blo 778337 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B877369 : Blo 778337 877369 := bbase (se 2 (by rfl) ⟨329013, by rfl⟩ : syracuseStep 877369 = 658027) (by norm_num)
theorem B1172285 : Blo 778337 1172285 := bbase (se 3 (by rfl) ⟨219803, by rfl⟩ : syracuseStep 1172285 = 439607) (by norm_num)
theorem B1663829 : Blo 778337 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B2253653 : Blo 778337 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1172309 : Blo 778337 1172309 := bbase (se 9 (by rfl) ⟨3434, by rfl⟩ : syracuseStep 1172309 = 6869) (by norm_num)
theorem B877405 : Blo 778337 877405 := bbase (se 3 (by rfl) ⟨164513, by rfl⟩ : syracuseStep 877405 = 329027) (by norm_num)
theorem B1172333 : Blo 778337 1172333 := bbase (se 3 (by rfl) ⟨219812, by rfl⟩ : syracuseStep 1172333 = 439625) (by norm_num)
theorem B877441 : Blo 778337 877441 := bbase (se 2 (by rfl) ⟨329040, by rfl⟩ : syracuseStep 877441 = 658081) (by norm_num)
theorem B1172357 : Blo 778337 1172357 := bbase (se 4 (by rfl) ⟨109908, by rfl⟩ : syracuseStep 1172357 = 219817) (by norm_num)
theorem B1172381 : Blo 778337 1172381 := bbase (se 3 (by rfl) ⟨219821, by rfl⟩ : syracuseStep 1172381 = 439643) (by norm_num)
theorem B877477 : Blo 778337 877477 := bbase (se 4 (by rfl) ⟨82263, by rfl⟩ : syracuseStep 877477 = 164527) (by norm_num)
theorem B1172405 : Blo 778337 1172405 := bbase (se 5 (by rfl) ⟨54956, by rfl⟩ : syracuseStep 1172405 = 109913) (by norm_num)
theorem B877513 : Blo 778337 877513 := bbase (se 2 (by rfl) ⟨329067, by rfl⟩ : syracuseStep 877513 = 658135) (by norm_num)
theorem B1172429 : Blo 778337 1172429 := bbase (se 3 (by rfl) ⟨219830, by rfl⟩ : syracuseStep 1172429 = 439661) (by norm_num)
theorem B2221013 : Blo 778337 2221013 := bbase (se 7 (by rfl) ⟨26027, by rfl⟩ : syracuseStep 2221013 = 52055) (by norm_num)
theorem B1172453 : Blo 778337 1172453 := bbase (se 4 (by rfl) ⟨109917, by rfl⟩ : syracuseStep 1172453 = 219835) (by norm_num)
theorem B877549 : Blo 778337 877549 := bbase (se 3 (by rfl) ⟨164540, by rfl⟩ : syracuseStep 877549 = 329081) (by norm_num)
theorem B4449269 : Blo 778337 4449269 := bbase (se 5 (by rfl) ⟨208559, by rfl⟩ : syracuseStep 4449269 = 417119) (by norm_num)
theorem B1172477 : Blo 778337 1172477 := bbase (se 3 (by rfl) ⟨219839, by rfl⟩ : syracuseStep 1172477 = 439679) (by norm_num)
theorem B877585 : Blo 778337 877585 := bbase (se 2 (by rfl) ⟨329094, by rfl⟩ : syracuseStep 877585 = 658189) (by norm_num)
theorem B1172501 : Blo 778337 1172501 := bbase (se 6 (by rfl) ⟨27480, by rfl⟩ : syracuseStep 1172501 = 54961) (by norm_num)
theorem B1172525 : Blo 778337 1172525 := bbase (se 3 (by rfl) ⟨219848, by rfl⟩ : syracuseStep 1172525 = 439697) (by norm_num)
theorem B877621 : Blo 778337 877621 := bbase (se 5 (by rfl) ⟨41138, by rfl⟩ : syracuseStep 877621 = 82277) (by norm_num)
theorem B1172549 : Blo 778337 1172549 := bbase (se 4 (by rfl) ⟨109926, by rfl⟩ : syracuseStep 1172549 = 219853) (by norm_num)
theorem B877657 : Blo 778337 877657 := bbase (se 2 (by rfl) ⟨329121, by rfl⟩ : syracuseStep 877657 = 658243) (by norm_num)
theorem B1172573 : Blo 778337 1172573 := bbase (se 3 (by rfl) ⟨219857, by rfl⟩ : syracuseStep 1172573 = 439715) (by norm_num)
theorem B1172597 : Blo 778337 1172597 := bbase (se 5 (by rfl) ⟨54965, by rfl⟩ : syracuseStep 1172597 = 109931) (by norm_num)
theorem B877693 : Blo 778337 877693 := bbase (se 3 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 877693 = 329135) (by norm_num)
theorem B1172621 : Blo 778337 1172621 := bbase (se 3 (by rfl) ⟨219866, by rfl⟩ : syracuseStep 1172621 = 439733) (by norm_num)
theorem B877729 : Blo 778337 877729 := bbase (se 2 (by rfl) ⟨329148, by rfl⟩ : syracuseStep 877729 = 658297) (by norm_num)
theorem B1172645 : Blo 778337 1172645 := bbase (se 4 (by rfl) ⟨109935, by rfl⟩ : syracuseStep 1172645 = 219871) (by norm_num)
theorem B1926317 : Blo 778337 1926317 := bbase (se 3 (by rfl) ⟨361184, by rfl⟩ : syracuseStep 1926317 = 722369) (by norm_num)
theorem B1172669 : Blo 778337 1172669 := bbase (se 3 (by rfl) ⟨219875, by rfl⟩ : syracuseStep 1172669 = 439751) (by norm_num)
theorem B2221253 : Blo 778337 2221253 := bbase (se 4 (by rfl) ⟨208242, by rfl⟩ : syracuseStep 2221253 = 416485) (by norm_num)
theorem B877765 : Blo 778337 877765 := bbase (se 4 (by rfl) ⟨82290, by rfl⟩ : syracuseStep 877765 = 164581) (by norm_num)
theorem B3335381 : Blo 778337 3335381 := bbase (se 7 (by rfl) ⟨39086, by rfl⟩ : syracuseStep 3335381 = 78173) (by norm_num)
theorem B1172693 : Blo 778337 1172693 := bbase (se 7 (by rfl) ⟨13742, by rfl⟩ : syracuseStep 1172693 = 27485) (by norm_num)
theorem B877801 : Blo 778337 877801 := bbase (se 2 (by rfl) ⟨329175, by rfl⟩ : syracuseStep 877801 = 658351) (by norm_num)
theorem B1172717 : Blo 778337 1172717 := bbase (se 3 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 1172717 = 439769) (by norm_num)
theorem B1172741 : Blo 778337 1172741 := bbase (se 4 (by rfl) ⟨109944, by rfl⟩ : syracuseStep 1172741 = 219889) (by norm_num)
theorem B877837 : Blo 778337 877837 := bbase (se 3 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 877837 = 329189) (by norm_num)
theorem B1172765 : Blo 778337 1172765 := bbase (se 3 (by rfl) ⟨219893, by rfl⟩ : syracuseStep 1172765 = 439787) (by norm_num)
theorem B877873 : Blo 778337 877873 := bbase (se 2 (by rfl) ⟨329202, by rfl⟩ : syracuseStep 877873 = 658405) (by norm_num)
theorem B1172789 : Blo 778337 1172789 := bbase (se 5 (by rfl) ⟨54974, by rfl⟩ : syracuseStep 1172789 = 109949) (by norm_num)
theorem B1500493 : Blo 778337 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B1172813 : Blo 778337 1172813 := bbase (se 3 (by rfl) ⟨219902, by rfl⟩ : syracuseStep 1172813 = 439805) (by norm_num)
theorem B877909 : Blo 778337 877909 := bbase (se 12 (by rfl) ⟨321, by rfl⟩ : syracuseStep 877909 = 643) (by norm_num)
theorem B1172837 : Blo 778337 1172837 := bbase (se 4 (by rfl) ⟨109953, by rfl⟩ : syracuseStep 1172837 = 219907) (by norm_num)
theorem B877945 : Blo 778337 877945 := bbase (se 2 (by rfl) ⟨329229, by rfl⟩ : syracuseStep 877945 = 658459) (by norm_num)
theorem B1172861 : Blo 778337 1172861 := bbase (se 3 (by rfl) ⟨219911, by rfl⟩ : syracuseStep 1172861 = 439823) (by norm_num)
theorem B2221445 : Blo 778337 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B1172885 : Blo 778337 1172885 := bbase (se 6 (by rfl) ⟨27489, by rfl⟩ : syracuseStep 1172885 = 54979) (by norm_num)
theorem B877981 : Blo 778337 877981 := bbase (se 3 (by rfl) ⟨164621, by rfl⟩ : syracuseStep 877981 = 329243) (by norm_num)
theorem B1172909 : Blo 778337 1172909 := bbase (se 3 (by rfl) ⟨219920, by rfl⟩ : syracuseStep 1172909 = 439841) (by norm_num)
theorem B878017 : Blo 778337 878017 := bbase (se 2 (by rfl) ⟨329256, by rfl⟩ : syracuseStep 878017 = 658513) (by norm_num)
theorem B1172933 : Blo 778337 1172933 := bbase (se 4 (by rfl) ⟨109962, by rfl⟩ : syracuseStep 1172933 = 219925) (by norm_num)
theorem B1172957 : Blo 778337 1172957 := bbase (se 3 (by rfl) ⟨219929, by rfl⟩ : syracuseStep 1172957 = 439859) (by norm_num)
theorem B878053 : Blo 778337 878053 := bbase (se 4 (by rfl) ⟨82317, by rfl⟩ : syracuseStep 878053 = 164635) (by norm_num)
theorem B1172981 : Blo 778337 1172981 := bbase (se 5 (by rfl) ⟨54983, by rfl⟩ : syracuseStep 1172981 = 109967) (by norm_num)
theorem B878089 : Blo 778337 878089 := bbase (se 2 (by rfl) ⟨329283, by rfl⟩ : syracuseStep 878089 = 658567) (by norm_num)
theorem B1173005 : Blo 778337 1173005 := bbase (se 3 (by rfl) ⟨219938, by rfl⟩ : syracuseStep 1173005 = 439877) (by norm_num)
theorem B1173029 : Blo 778337 1173029 := bbase (se 4 (by rfl) ⟨109971, by rfl⟩ : syracuseStep 1173029 = 219943) (by norm_num)
theorem B878125 : Blo 778337 878125 := bbase (se 3 (by rfl) ⟨164648, by rfl⟩ : syracuseStep 878125 = 329297) (by norm_num)
theorem B5629493 : Blo 778337 5629493 := bbase (se 5 (by rfl) ⟨263882, by rfl⟩ : syracuseStep 5629493 = 527765) (by norm_num)
theorem B1173053 : Blo 778337 1173053 := bbase (se 3 (by rfl) ⟨219947, by rfl⟩ : syracuseStep 1173053 = 439895) (by norm_num)
theorem B878161 : Blo 778337 878161 := bbase (se 2 (by rfl) ⟨329310, by rfl⟩ : syracuseStep 878161 = 658621) (by norm_num)
theorem B1173077 : Blo 778337 1173077 := bbase (se 8 (by rfl) ⟨6873, by rfl⟩ : syracuseStep 1173077 = 13747) (by norm_num)
theorem B1173101 : Blo 778337 1173101 := bbase (se 3 (by rfl) ⟨219956, by rfl⟩ : syracuseStep 1173101 = 439913) (by norm_num)
theorem B878197 : Blo 778337 878197 := bbase (se 5 (by rfl) ⟨41165, by rfl⟩ : syracuseStep 878197 = 82331) (by norm_num)
theorem B1173125 : Blo 778337 1173125 := bbase (se 4 (by rfl) ⟨109980, by rfl⟩ : syracuseStep 1173125 = 219961) (by norm_num)
theorem B878233 : Blo 778337 878233 := bbase (se 2 (by rfl) ⟨329337, by rfl⟩ : syracuseStep 878233 = 658675) (by norm_num)
theorem B1173149 : Blo 778337 1173149 := bbase (se 3 (by rfl) ⟨219965, by rfl⟩ : syracuseStep 1173149 = 439931) (by norm_num)
theorem B1173173 : Blo 778337 1173173 := bbase (se 5 (by rfl) ⟨54992, by rfl⟩ : syracuseStep 1173173 = 109985) (by norm_num)
theorem B878269 : Blo 778337 878269 := bbase (se 3 (by rfl) ⟨164675, by rfl⟩ : syracuseStep 878269 = 329351) (by norm_num)
theorem B3958469 : Blo 778337 3958469 := bbase (se 4 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 3958469 = 742213) (by norm_num)
theorem B1664717 : Blo 778337 1664717 := bbase (se 3 (by rfl) ⟨312134, by rfl⟩ : syracuseStep 1664717 = 624269) (by norm_num)
theorem B1173197 : Blo 778337 1173197 := bbase (se 3 (by rfl) ⟨219974, by rfl⟩ : syracuseStep 1173197 = 439949) (by norm_num)
theorem B878305 : Blo 778337 878305 := bbase (se 2 (by rfl) ⟨329364, by rfl⟩ : syracuseStep 878305 = 658729) (by norm_num)
theorem B1173221 : Blo 778337 1173221 := bbase (se 4 (by rfl) ⟨109989, by rfl⟩ : syracuseStep 1173221 = 219979) (by norm_num)
theorem B1042157 : Blo 778337 1042157 := bbase (se 3 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 1042157 = 390809) (by norm_num)
theorem B1173245 : Blo 778337 1173245 := bbase (se 3 (by rfl) ⟨219983, by rfl⟩ : syracuseStep 1173245 = 439967) (by norm_num)
theorem B878341 : Blo 778337 878341 := bbase (se 4 (by rfl) ⟨82344, by rfl⟩ : syracuseStep 878341 = 164689) (by norm_num)
theorem B1402645 : Blo 778337 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B1173269 : Blo 778337 1173269 := bbase (se 6 (by rfl) ⟨27498, by rfl⟩ : syracuseStep 1173269 = 54997) (by norm_num)
theorem B878377 : Blo 778337 878377 := bbase (se 2 (by rfl) ⟨329391, by rfl⟩ : syracuseStep 878377 = 658783) (by norm_num)
theorem B1173293 : Blo 778337 1173293 := bbase (se 3 (by rfl) ⟨219992, by rfl⟩ : syracuseStep 1173293 = 439985) (by norm_num)
theorem B1173317 : Blo 778337 1173317 := bbase (se 4 (by rfl) ⟨109998, by rfl⟩ : syracuseStep 1173317 = 219997) (by norm_num)
theorem B878413 : Blo 778337 878413 := bbase (se 3 (by rfl) ⟨164702, by rfl⟩ : syracuseStep 878413 = 329405) (by norm_num)
theorem B1173341 : Blo 778337 1173341 := bbase (se 3 (by rfl) ⟨220001, by rfl⟩ : syracuseStep 1173341 = 440003) (by norm_num)
theorem B878449 : Blo 778337 878449 := bbase (se 2 (by rfl) ⟨329418, by rfl⟩ : syracuseStep 878449 = 658837) (by norm_num)
theorem B1173365 : Blo 778337 1173365 := bbase (se 5 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 1173365 = 110003) (by norm_num)
theorem B1173389 : Blo 778337 1173389 := bbase (se 3 (by rfl) ⟨220010, by rfl⟩ : syracuseStep 1173389 = 440021) (by norm_num)
theorem B878485 : Blo 778337 878485 := bbase (se 6 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 878485 = 41179) (by norm_num)
theorem B3008405 : Blo 778337 3008405 := bbase (se 6 (by rfl) ⟨70509, by rfl⟩ : syracuseStep 3008405 = 141019) (by norm_num)
theorem B1173413 : Blo 778337 1173413 := bbase (se 4 (by rfl) ⟨110007, by rfl⟩ : syracuseStep 1173413 = 220015) (by norm_num)
theorem B878521 : Blo 778337 878521 := bbase (se 2 (by rfl) ⟨329445, by rfl⟩ : syracuseStep 878521 = 658891) (by norm_num)
theorem B1664957 : Blo 778337 1664957 := bbase (se 3 (by rfl) ⟨312179, by rfl⟩ : syracuseStep 1664957 = 624359) (by norm_num)
theorem B1173437 : Blo 778337 1173437 := bbase (se 3 (by rfl) ⟨220019, by rfl⟩ : syracuseStep 1173437 = 440039) (by norm_num)
theorem B1173461 : Blo 778337 1173461 := bbase (se 7 (by rfl) ⟨13751, by rfl⟩ : syracuseStep 1173461 = 27503) (by norm_num)
theorem B878557 : Blo 778337 878557 := bbase (se 3 (by rfl) ⟨164729, by rfl⟩ : syracuseStep 878557 = 329459) (by norm_num)
theorem B1173485 : Blo 778337 1173485 := bbase (se 3 (by rfl) ⟨220028, by rfl⟩ : syracuseStep 1173485 = 440057) (by norm_num)
theorem B878593 : Blo 778337 878593 := bbase (se 2 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 878593 = 658945) (by norm_num)
theorem B878629 : Blo 778337 878629 := bbase (se 4 (by rfl) ⟨82371, by rfl⟩ : syracuseStep 878629 = 164743) (by norm_num)
theorem B878665 : Blo 778337 878665 := bbase (se 2 (by rfl) ⟨329499, by rfl⟩ : syracuseStep 878665 = 658999) (by norm_num)
theorem B878701 : Blo 778337 878701 := bbase (se 3 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 878701 = 329513) (by norm_num)
theorem B878737 : Blo 778337 878737 := bbase (se 2 (by rfl) ⟨329526, by rfl⟩ : syracuseStep 878737 = 659053) (by norm_num)
theorem B878773 : Blo 778337 878773 := bbase (se 5 (by rfl) ⟨41192, by rfl⟩ : syracuseStep 878773 = 82385) (by norm_num)
theorem B878809 : Blo 778337 878809 := bbase (se 2 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 878809 = 659107) (by norm_num)
theorem B878845 : Blo 778337 878845 := bbase (se 3 (by rfl) ⟨164783, by rfl⟩ : syracuseStep 878845 = 329567) (by norm_num)
theorem B878881 : Blo 778337 878881 := bbase (se 2 (by rfl) ⟨329580, by rfl⟩ : syracuseStep 878881 = 659161) (by norm_num)
theorem B878917 : Blo 778337 878917 := bbase (se 4 (by rfl) ⟨82398, by rfl⟩ : syracuseStep 878917 = 164797) (by norm_num)
theorem B2222437 : Blo 778337 2222437 := bbase (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) (by norm_num)
theorem B878953 : Blo 778337 878953 := bbase (se 2 (by rfl) ⟨329607, by rfl⟩ : syracuseStep 878953 = 659215) (by norm_num)
theorem B878989 : Blo 778337 878989 := bbase (se 3 (by rfl) ⟨164810, by rfl⟩ : syracuseStep 878989 = 329621) (by norm_num)
theorem B879025 : Blo 778337 879025 := bbase (se 2 (by rfl) ⟨329634, by rfl⟩ : syracuseStep 879025 = 659269) (by norm_num)
theorem B1665461 : Blo 778337 1665461 := bbase (se 5 (by rfl) ⟨78068, by rfl⟩ : syracuseStep 1665461 = 156137) (by norm_num)
theorem B1665469 : Blo 778337 1665469 := bbase (se 3 (by rfl) ⟨312275, by rfl⟩ : syracuseStep 1665469 = 624551) (by norm_num)
theorem B879061 : Blo 778337 879061 := bbase (se 7 (by rfl) ⟨10301, by rfl⟩ : syracuseStep 879061 = 20603) (by norm_num)
theorem B879097 : Blo 778337 879097 := bbase (se 2 (by rfl) ⟨329661, by rfl⟩ : syracuseStep 879097 = 659323) (by norm_num)
theorem B879133 : Blo 778337 879133 := bbase (se 3 (by rfl) ⟨164837, by rfl⟩ : syracuseStep 879133 = 329675) (by norm_num)
theorem B879169 : Blo 778337 879169 := bbase (se 2 (by rfl) ⟨329688, by rfl⟩ : syracuseStep 879169 = 659377) (by norm_num)
theorem B879205 : Blo 778337 879205 := bbase (se 4 (by rfl) ⟨82425, by rfl⟩ : syracuseStep 879205 = 164851) (by norm_num)
theorem B879241 : Blo 778337 879241 := bbase (se 2 (by rfl) ⟨329715, by rfl⟩ : syracuseStep 879241 = 659431) (by norm_num)
theorem B879277 : Blo 778337 879277 := bbase (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) (by norm_num)
theorem B879313 : Blo 778337 879313 := bbase (se 2 (by rfl) ⟨329742, by rfl⟩ : syracuseStep 879313 = 659485) (by norm_num)
theorem B879349 : Blo 778337 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B1108741 : Blo 778337 1108741 := bbase (se 4 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 1108741 = 207889) (by norm_num)
theorem B879385 : Blo 778337 879385 := bbase (se 2 (by rfl) ⟨329769, by rfl⟩ : syracuseStep 879385 = 659539) (by norm_num)
theorem B879421 : Blo 778337 879421 := bbase (se 3 (by rfl) ⟨164891, by rfl⟩ : syracuseStep 879421 = 329783) (by norm_num)
theorem B879457 : Blo 778337 879457 := bbase (se 2 (by rfl) ⟨329796, by rfl⟩ : syracuseStep 879457 = 659593) (by norm_num)
theorem B879493 : Blo 778337 879493 := bbase (se 4 (by rfl) ⟨82452, by rfl⟩ : syracuseStep 879493 = 164905) (by norm_num)
theorem B879529 : Blo 778337 879529 := bbase (se 2 (by rfl) ⟨329823, by rfl⟩ : syracuseStep 879529 = 659647) (by norm_num)
theorem B879565 : Blo 778337 879565 := bbase (se 3 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 879565 = 329837) (by norm_num)
theorem B3959765 : Blo 778337 3959765 := bbase (se 7 (by rfl) ⟨46403, by rfl⟩ : syracuseStep 3959765 = 92807) (by norm_num)
theorem B879601 : Blo 778337 879601 := bbase (se 2 (by rfl) ⟨329850, by rfl⟩ : syracuseStep 879601 = 659701) (by norm_num)
theorem B879637 : Blo 778337 879637 := bbase (se 6 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 879637 = 41233) (by norm_num)
theorem B879673 : Blo 778337 879673 := bbase (se 2 (by rfl) ⟨329877, by rfl⟩ : syracuseStep 879673 = 659755) (by norm_num)
theorem B879709 : Blo 778337 879709 := bbase (se 3 (by rfl) ⟨164945, by rfl⟩ : syracuseStep 879709 = 329891) (by norm_num)
theorem B1404029 : Blo 778337 1404029 := bbase (se 3 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 1404029 = 526511) (by norm_num)
theorem B879745 : Blo 778337 879745 := bbase (se 2 (by rfl) ⟨329904, by rfl⟩ : syracuseStep 879745 = 659809) (by norm_num)
theorem B2256005 : Blo 778337 2256005 := bbase (se 4 (by rfl) ⟨211500, by rfl⟩ : syracuseStep 2256005 = 423001) (by norm_num)
theorem B879781 : Blo 778337 879781 := bbase (se 4 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 879781 = 164959) (by norm_num)
theorem B879817 : Blo 778337 879817 := bbase (se 2 (by rfl) ⟨329931, by rfl⟩ : syracuseStep 879817 = 659863) (by norm_num)
theorem B879853 : Blo 778337 879853 := bbase (se 3 (by rfl) ⟨164972, by rfl⟩ : syracuseStep 879853 = 329945) (by norm_num)
theorem B879889 : Blo 778337 879889 := bbase (se 2 (by rfl) ⟨329958, by rfl⟩ : syracuseStep 879889 = 659917) (by norm_num)
theorem B879925 : Blo 778337 879925 := bbase (se 5 (by rfl) ⟨41246, by rfl⟩ : syracuseStep 879925 = 82493) (by norm_num)
theorem B1109333 : Blo 778337 1109333 := bbase (se 11 (by rfl) ⟨812, by rfl⟩ : syracuseStep 1109333 = 1625) (by norm_num)
theorem B879961 : Blo 778337 879961 := bbase (se 2 (by rfl) ⟨329985, by rfl⟩ : syracuseStep 879961 = 659971) (by norm_num)
theorem B879997 : Blo 778337 879997 := bbase (se 3 (by rfl) ⟨164999, by rfl⟩ : syracuseStep 879997 = 329999) (by norm_num)
theorem B8449429 : Blo 778337 8449429 := bbase (se 6 (by rfl) ⟨198033, by rfl⟩ : syracuseStep 8449429 = 396067) (by norm_num)
theorem B880033 : Blo 778337 880033 := bbase (se 2 (by rfl) ⟨330012, by rfl⟩ : syracuseStep 880033 = 660025) (by norm_num)
theorem B1109413 : Blo 778337 1109413 := bbase (se 4 (by rfl) ⟨104007, by rfl⟩ : syracuseStep 1109413 = 208015) (by norm_num)
theorem B2223541 : Blo 778337 2223541 := bbase (se 5 (by rfl) ⟨104228, by rfl⟩ : syracuseStep 2223541 = 208457) (by norm_num)
theorem B880069 : Blo 778337 880069 := bbase (se 4 (by rfl) ⟨82506, by rfl⟩ : syracuseStep 880069 = 165013) (by norm_num)
theorem B880105 : Blo 778337 880105 := bbase (se 2 (by rfl) ⟨330039, by rfl⟩ : syracuseStep 880105 = 660079) (by norm_num)
theorem B1109533 : Blo 778337 1109533 := bbase (se 3 (by rfl) ⟨208037, by rfl⟩ : syracuseStep 1109533 = 416075) (by norm_num)
theorem B1666597 : Blo 778337 1666597 := bbase (se 4 (by rfl) ⟨156243, by rfl⟩ : syracuseStep 1666597 = 312487) (by norm_num)
theorem B1109629 : Blo 778337 1109629 := bbase (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) (by norm_num)
theorem B1666973 : Blo 778337 1666973 := bbase (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) (by norm_num)
theorem B4223029 : Blo 778337 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B1110125 : Blo 778337 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B2814389 : Blo 778337 2814389 := bbase (se 5 (by rfl) ⟨131924, by rfl⟩ : syracuseStep 2814389 = 263849) (by norm_num)
theorem B1110677 : Blo 778337 1110677 := bbase (se 6 (by rfl) ⟨26031, by rfl⟩ : syracuseStep 1110677 = 52063) (by norm_num)
theorem B4223765 : Blo 778337 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B2225045 : Blo 778337 2225045 := bbase (se 6 (by rfl) ⟨52149, by rfl⟩ : syracuseStep 2225045 = 104299) (by norm_num)
theorem B3339413 : Blo 778337 3339413 := bbase (se 6 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 3339413 = 156535) (by norm_num)
theorem B1111429 : Blo 778337 1111429 := bbase (se 4 (by rfl) ⟨104196, by rfl⟩ : syracuseStep 1111429 = 208393) (by norm_num)
theorem B1668613 : Blo 778337 1668613 := bbase (se 4 (by rfl) ⟨156432, by rfl⟩ : syracuseStep 1668613 = 312865) (by norm_num)
theorem B13301333 : Blo 778337 13301333 := bbase (se 8 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 13301333 = 155875) (by norm_num)
theorem B5633621 : Blo 778337 5633621 := bbase (se 8 (by rfl) ⟨33009, by rfl⟩ : syracuseStep 5633621 = 66019) (by norm_num)
theorem B3995237 : Blo 778337 3995237 := bbase (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) (by norm_num)
theorem B2815669 : Blo 778337 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B1112221 : Blo 778337 1112221 := bbase (se 3 (by rfl) ⟨208541, by rfl⟩ : syracuseStep 1112221 = 417083) (by norm_num)
theorem B12024085 : Blo 778337 12024085 := bbase (se 6 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 12024085 = 563629) (by norm_num)
theorem B1669501 : Blo 778337 1669501 := bbase (se 3 (by rfl) ⟨313031, by rfl⟩ : syracuseStep 1669501 = 626063) (by norm_num)
theorem B5339573 : Blo 778337 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B2226629 : Blo 778337 2226629 := bbase (se 4 (by rfl) ⟨208746, by rfl⟩ : syracuseStep 2226629 = 417493) (by norm_num)
theorem B1112557 : Blo 778337 1112557 := bbase (se 3 (by rfl) ⟨208604, by rfl⟩ : syracuseStep 1112557 = 417209) (by norm_num)
theorem B1112773 : Blo 778337 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B5929685 : Blo 778337 5929685 := bbase (se 7 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 5929685 = 138977) (by norm_num)
theorem B1604437 : Blo 778337 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B1669997 : Blo 778337 1669997 := bbase (se 3 (by rfl) ⟨313124, by rfl⟩ : syracuseStep 1669997 = 626249) (by norm_num)
theorem B3341189 : Blo 778337 3341189 := bbase (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) (by norm_num)
theorem B1113149 : Blo 778337 1113149 := bbase (se 3 (by rfl) ⟨208715, by rfl⟩ : syracuseStep 1113149 = 417431) (by norm_num)
theorem B2227301 : Blo 778337 2227301 := bbase (se 4 (by rfl) ⟨208809, by rfl⟩ : syracuseStep 2227301 = 417619) (by norm_num)
theorem B1408117 : Blo 778337 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B1998053 : Blo 778337 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B2227733 : Blo 778337 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B1670861 : Blo 778337 1670861 := bbase (se 3 (by rfl) ⟨313286, by rfl⟩ : syracuseStep 1670861 = 626573) (by norm_num)
theorem B1408757 : Blo 778337 1408757 := bbase (se 5 (by rfl) ⟨66035, by rfl⟩ : syracuseStep 1408757 = 132071) (by norm_num)
theorem B1409219 : Blo 778337 1409219 := bstep (se 1 (by rfl) ⟨1056914, by rfl⟩ : syracuseStep 1409219 = 2113829) B2113829
theorem B1409233 : Blo 778337 1409233 := bstep (se 2 (by rfl) ⟨528462, by rfl⟩ : syracuseStep 1409233 = 1056925) B1056925
theorem B1409393 : Blo 778337 1409393 := bstep (se 2 (by rfl) ⟨528522, by rfl⟩ : syracuseStep 1409393 = 1057045) B1057045
theorem B1507889 : Blo 778337 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B4227875 : Blo 778337 4227875 := bstep (se 1 (by rfl) ⟨3170906, by rfl⟩ : syracuseStep 4227875 = 6341813) B6341813
theorem B2000657 : Blo 778337 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B1247251 : Blo 778337 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B6654221 : Blo 778337 6654221 := bstep (se 3 (by rfl) ⟨1247666, by rfl⟩ : syracuseStep 6654221 = 2495333) B2495333
theorem B1870193 : Blo 778337 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B985603 : Blo 778337 985603 := bstep (se 1 (by rfl) ⟨739202, by rfl⟩ : syracuseStep 985603 = 1478405) B1478405
theorem B985699 : Blo 778337 985699 := bstep (se 1 (by rfl) ⟨739274, by rfl⟩ : syracuseStep 985699 = 1478549) B1478549
theorem B1247923 : Blo 778337 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B1313489 : Blo 778337 1313489 := bstep (se 2 (by rfl) ⟨492558, by rfl⟩ : syracuseStep 1313489 = 985117) B985117
theorem B1247969 : Blo 778337 1247969 := bstep (se 2 (by rfl) ⟨467988, by rfl⟩ : syracuseStep 1247969 = 935977) B935977
theorem B1313617 : Blo 778337 1313617 := bstep (se 2 (by rfl) ⟨492606, by rfl⟩ : syracuseStep 1313617 = 985213) B985213
theorem B1313651 : Blo 778337 1313651 := bstep (se 1 (by rfl) ⟨985238, by rfl⟩ : syracuseStep 1313651 = 1970477) B1970477
theorem B10259341 : Blo 778337 10259341 := bstep (se 3 (by rfl) ⟨1923626, by rfl⟩ : syracuseStep 10259341 = 3847253) B3847253
theorem B6261745 : Blo 778337 6261745 := bstep (se 2 (by rfl) ⟨2348154, by rfl⟩ : syracuseStep 6261745 = 4696309) B4696309
theorem B1313779 : Blo 778337 1313779 := bstep (se 1 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 1313779 = 1970669) B1970669
theorem B986195 : Blo 778337 986195 := bstep (se 1 (by rfl) ⟨739646, by rfl⟩ : syracuseStep 986195 = 1479293) B1479293
theorem B1313921 : Blo 778337 1313921 := bstep (se 2 (by rfl) ⟨492720, by rfl⟩ : syracuseStep 1313921 = 985441) B985441
theorem B1248481 : Blo 778337 1248481 := bstep (se 2 (by rfl) ⟨468180, by rfl⟩ : syracuseStep 1248481 = 936361) B936361
theorem B4754659 : Blo 778337 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B1314049 : Blo 778337 1314049 := bstep (se 2 (by rfl) ⟨492768, by rfl⟩ : syracuseStep 1314049 = 985537) B985537
theorem B1314083 : Blo 778337 1314083 := bstep (se 1 (by rfl) ⟨985562, by rfl⟩ : syracuseStep 1314083 = 1971125) B1971125
theorem B1314211 : Blo 778337 1314211 := bstep (se 1 (by rfl) ⟨985658, by rfl⟩ : syracuseStep 1314211 = 1971317) B1971317
theorem B1052195 : Blo 778337 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B1314353 : Blo 778337 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B1478321 : Blo 778337 1478321 := bstep (se 2 (by rfl) ⟨554370, by rfl⟩ : syracuseStep 1478321 = 1108741) B1108741
theorem B1314481 : Blo 778337 1314481 := bstep (se 2 (by rfl) ⟨492930, by rfl⟩ : syracuseStep 1314481 = 985861) B985861
theorem B1314515 : Blo 778337 1314515 := bstep (se 1 (by rfl) ⟨985886, by rfl⟩ : syracuseStep 1314515 = 1971773) B1971773
theorem B1249025 : Blo 778337 1249025 := bstep (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) B936769
theorem B1904401 : Blo 778337 1904401 := bstep (se 2 (by rfl) ⟨714150, by rfl⟩ : syracuseStep 1904401 = 1428301) B1428301
theorem B986899 : Blo 778337 986899 := bstep (se 1 (by rfl) ⟨740174, by rfl⟩ : syracuseStep 986899 = 1480349) B1480349
theorem B1314643 : Blo 778337 1314643 := bstep (se 1 (by rfl) ⟨985982, by rfl⟩ : syracuseStep 1314643 = 1971965) B1971965
theorem B986995 : Blo 778337 986995 := bstep (se 1 (by rfl) ⟨740246, by rfl⟩ : syracuseStep 986995 = 1480493) B1480493
theorem B1314785 : Blo 778337 1314785 := bstep (se 2 (by rfl) ⟨493044, by rfl⟩ : syracuseStep 1314785 = 986089) B986089
theorem B2494513 : Blo 778337 2494513 := bstep (se 2 (by rfl) ⟨935442, by rfl⟩ : syracuseStep 2494513 = 1870885) B1870885
theorem B1314913 : Blo 778337 1314913 := bstep (se 2 (by rfl) ⟨493092, by rfl⟩ : syracuseStep 1314913 = 986185) B986185
theorem B1314947 : Blo 778337 1314947 := bstep (se 1 (by rfl) ⟨986210, by rfl⟩ : syracuseStep 1314947 = 1972421) B1972421
theorem B1315075 : Blo 778337 1315075 := bstep (se 1 (by rfl) ⟨986306, by rfl⟩ : syracuseStep 1315075 = 1972613) B1972613
theorem B1052947 : Blo 778337 1052947 := bstep (se 1 (by rfl) ⟨789710, by rfl⟩ : syracuseStep 1052947 = 1579421) B1579421
theorem B987491 : Blo 778337 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B1315217 : Blo 778337 1315217 := bstep (se 2 (by rfl) ⟨493206, by rfl⟩ : syracuseStep 1315217 = 986413) B986413
theorem B790931 : Blo 778337 790931 := bstep (se 1 (by rfl) ⟨593198, by rfl⟩ : syracuseStep 790931 = 1186397) B1186397
theorem B4493765 : Blo 778337 4493765 := bstep (se 4 (by rfl) ⟨421290, by rfl⟩ : syracuseStep 4493765 = 842581) B842581
theorem B8556997 : Blo 778337 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B1315345 : Blo 778337 1315345 := bstep (se 2 (by rfl) ⟨493254, by rfl⟩ : syracuseStep 1315345 = 986509) B986509
theorem B889363 : Blo 778337 889363 := bstep (se 1 (by rfl) ⟨667022, by rfl⟩ : syracuseStep 889363 = 1334045) B1334045
theorem B1479217 : Blo 778337 1479217 := bstep (se 2 (by rfl) ⟨554706, by rfl⟩ : syracuseStep 1479217 = 1109413) B1109413
theorem B1315379 : Blo 778337 1315379 := bstep (se 1 (by rfl) ⟨986534, by rfl⟩ : syracuseStep 1315379 = 1973069) B1973069
theorem B1970801 : Blo 778337 1970801 := bstep (se 2 (by rfl) ⟨739050, by rfl⟩ : syracuseStep 1970801 = 1478101) B1478101
theorem B2495117 : Blo 778337 2495117 := bstep (se 3 (by rfl) ⟨467834, by rfl⟩ : syracuseStep 2495117 = 935669) B935669
theorem B1970851 : Blo 778337 1970851 := bstep (se 1 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 1970851 = 2956277) B2956277
theorem B1184419 : Blo 778337 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B1315507 : Blo 778337 1315507 := bstep (se 1 (by rfl) ⟨986630, by rfl⟩ : syracuseStep 1315507 = 1973261) B1973261
theorem B1249987 : Blo 778337 1249987 := bstep (se 1 (by rfl) ⟨937490, by rfl⟩ : syracuseStep 1249987 = 1874981) B1874981
theorem B1479377 : Blo 778337 1479377 := bstep (se 2 (by rfl) ⟨554766, by rfl⟩ : syracuseStep 1479377 = 1109533) B1109533
theorem B791267 : Blo 778337 791267 := bstep (se 1 (by rfl) ⟨593450, by rfl⟩ : syracuseStep 791267 = 1186901) B1186901
theorem B1970993 : Blo 778337 1970993 := bstep (se 2 (by rfl) ⟨739122, by rfl⟩ : syracuseStep 1970993 = 1478245) B1478245
theorem B10654517 : Blo 778337 10654517 := bstep (se 5 (by rfl) ⟨499430, by rfl⟩ : syracuseStep 10654517 = 998861) B998861
theorem B1315649 : Blo 778337 1315649 := bstep (se 2 (by rfl) ⟨493368, by rfl⟩ : syracuseStep 1315649 = 986737) B986737
theorem B1315777 : Blo 778337 1315777 := bstep (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) B986833
theorem B1250243 : Blo 778337 1250243 := bstep (se 1 (by rfl) ⟨937682, by rfl⟩ : syracuseStep 1250243 = 1875365) B1875365
theorem B1315811 : Blo 778337 1315811 := bstep (se 1 (by rfl) ⟨986858, by rfl⟩ : syracuseStep 1315811 = 1973717) B1973717
theorem B988195 : Blo 778337 988195 := bstep (se 1 (by rfl) ⟨741146, by rfl⟩ : syracuseStep 988195 = 1482293) B1482293
theorem B1479779 : Blo 778337 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B1315939 : Blo 778337 1315939 := bstep (se 1 (by rfl) ⟨986954, by rfl⟩ : syracuseStep 1315939 = 1973909) B1973909
theorem B9147491 : Blo 778337 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B988291 : Blo 778337 988291 := bstep (se 1 (by rfl) ⟨741218, by rfl⟩ : syracuseStep 988291 = 1482437) B1482437
theorem B3740849 : Blo 778337 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B1316081 : Blo 778337 1316081 := bstep (se 2 (by rfl) ⟨493530, by rfl⟩ : syracuseStep 1316081 = 987061) B987061
theorem B1316209 : Blo 778337 1316209 := bstep (se 2 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 1316209 = 987157) B987157
theorem B1316243 : Blo 778337 1316243 := bstep (se 1 (by rfl) ⟨987182, by rfl⟩ : syracuseStep 1316243 = 1974365) B1974365
theorem B25368005 : Blo 778337 25368005 := bstep (se 4 (by rfl) ⟨2378250, by rfl⟩ : syracuseStep 25368005 = 4756501) B4756501
theorem B1316371 : Blo 778337 1316371 := bstep (se 1 (by rfl) ⟨987278, by rfl⟩ : syracuseStep 1316371 = 1974557) B1974557
theorem B2627153 : Blo 778337 2627153 := bstep (se 2 (by rfl) ⟨985182, by rfl⟩ : syracuseStep 2627153 = 1970365) B1970365
theorem B988787 : Blo 778337 988787 := bstep (se 1 (by rfl) ⟨741590, by rfl⟩ : syracuseStep 988787 = 1483181) B1483181
theorem B1250947 : Blo 778337 1250947 := bstep (se 1 (by rfl) ⟨938210, by rfl⟩ : syracuseStep 1250947 = 1876421) B1876421
theorem B1316513 : Blo 778337 1316513 := bstep (se 2 (by rfl) ⟨493692, by rfl⟩ : syracuseStep 1316513 = 987385) B987385
theorem B1971985 : Blo 778337 1971985 := bstep (se 2 (by rfl) ⟨739494, by rfl⟩ : syracuseStep 1971985 = 1478989) B1478989
theorem B1316641 : Blo 778337 1316641 := bstep (se 2 (by rfl) ⟨493740, by rfl⟩ : syracuseStep 1316641 = 987481) B987481
theorem B1316675 : Blo 778337 1316675 := bstep (se 1 (by rfl) ⟨987506, by rfl⟩ : syracuseStep 1316675 = 1975013) B1975013
theorem B1251217 : Blo 778337 1251217 := bstep (se 2 (by rfl) ⟨469206, by rfl⟩ : syracuseStep 1251217 = 938413) B938413
theorem B1316803 : Blo 778337 1316803 := bstep (se 1 (by rfl) ⟨987602, by rfl⟩ : syracuseStep 1316803 = 1975205) B1975205
theorem B1251281 : Blo 778337 1251281 := bstep (se 2 (by rfl) ⟨469230, by rfl⟩ : syracuseStep 1251281 = 938461) B938461
theorem B1480675 : Blo 778337 1480675 := bstep (se 1 (by rfl) ⟨1110506, by rfl⟩ : syracuseStep 1480675 = 2221013) B2221013
theorem B3381233 : Blo 778337 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B1972259 : Blo 778337 1972259 := bstep (se 1 (by rfl) ⟨1479194, by rfl⟩ : syracuseStep 1972259 = 2958389) B2958389
theorem B1316945 : Blo 778337 1316945 := bstep (se 2 (by rfl) ⟨493854, by rfl⟩ : syracuseStep 1316945 = 987709) B987709
theorem B2627693 : Blo 778337 2627693 := bstep (se 3 (by rfl) ⟨492692, by rfl⟩ : syracuseStep 2627693 = 985385) B985385
theorem B1284211 : Blo 778337 1284211 := bstep (se 1 (by rfl) ⟨963158, by rfl⟩ : syracuseStep 1284211 = 1926317) B1926317
theorem B1480835 : Blo 778337 1480835 := bstep (se 1 (by rfl) ⟨1110626, by rfl⟩ : syracuseStep 1480835 = 2221253) B2221253
theorem B2627747 : Blo 778337 2627747 := bstep (se 1 (by rfl) ⟨1970810, by rfl⟩ : syracuseStep 2627747 = 3941621) B3941621
theorem B1317073 : Blo 778337 1317073 := bstep (se 2 (by rfl) ⟨493902, by rfl⟩ : syracuseStep 1317073 = 987805) B987805
theorem B3741923 : Blo 778337 3741923 := bstep (se 1 (by rfl) ⟨2806442, by rfl⟩ : syracuseStep 3741923 = 5612885) B5612885
theorem B1972451 : Blo 778337 1972451 := bstep (se 1 (by rfl) ⟨1479338, by rfl⟩ : syracuseStep 1972451 = 2958677) B2958677
theorem B1317107 : Blo 778337 1317107 := bstep (se 1 (by rfl) ⟨987830, by rfl⟩ : syracuseStep 1317107 = 1975661) B1975661
theorem B1579267 : Blo 778337 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B989491 : Blo 778337 989491 := bstep (se 1 (by rfl) ⟨742118, by rfl⟩ : syracuseStep 989491 = 1484237) B1484237
theorem B1579331 : Blo 778337 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B1317235 : Blo 778337 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B989587 : Blo 778337 989587 := bstep (se 1 (by rfl) ⟨742190, by rfl⟩ : syracuseStep 989587 = 1484381) B1484381
theorem B2628017 : Blo 778337 2628017 := bstep (se 2 (by rfl) ⟨985506, by rfl⟩ : syracuseStep 2628017 = 1971013) B1971013
theorem B2955761 : Blo 778337 2955761 := bstep (se 2 (by rfl) ⟨1108410, by rfl⟩ : syracuseStep 2955761 = 2216821) B2216821
theorem B1317377 : Blo 778337 1317377 := bstep (se 2 (by rfl) ⟨494016, by rfl⟩ : syracuseStep 1317377 = 988033) B988033
theorem B2005603 : Blo 778337 2005603 := bstep (se 1 (by rfl) ⟨1504202, by rfl⟩ : syracuseStep 2005603 = 3008405) B3008405
theorem B1317505 : Blo 778337 1317505 := bstep (se 2 (by rfl) ⟨494064, by rfl⟩ : syracuseStep 1317505 = 988129) B988129
theorem B1317539 : Blo 778337 1317539 := bstep (se 1 (by rfl) ⟨988154, by rfl⟩ : syracuseStep 1317539 = 1976309) B1976309
theorem B1186499 : Blo 778337 1186499 := bstep (se 1 (by rfl) ⟨889874, by rfl⟩ : syracuseStep 1186499 = 1779749) B1779749
theorem B4004579 : Blo 778337 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B1317667 : Blo 778337 1317667 := bstep (se 1 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 1317667 = 1976501) B1976501
theorem B990083 : Blo 778337 990083 := bstep (se 1 (by rfl) ⟨742562, by rfl⟩ : syracuseStep 990083 = 1485125) B1485125
theorem B1317809 : Blo 778337 1317809 := bstep (se 2 (by rfl) ⟨494178, by rfl⟩ : syracuseStep 1317809 = 988357) B988357
theorem B2628557 : Blo 778337 2628557 := bstep (se 3 (by rfl) ⟨492854, by rfl⟩ : syracuseStep 2628557 = 985709) B985709
theorem B2628611 : Blo 778337 2628611 := bstep (se 1 (by rfl) ⟨1971458, by rfl⟩ : syracuseStep 2628611 = 3942917) B3942917
theorem B1317937 : Blo 778337 1317937 := bstep (se 2 (by rfl) ⟨494226, by rfl⟩ : syracuseStep 1317937 = 988453) B988453
theorem B1317971 : Blo 778337 1317971 := bstep (se 1 (by rfl) ⟨988478, by rfl⟩ : syracuseStep 1317971 = 1976957) B1976957
theorem B1973393 : Blo 778337 1973393 := bstep (se 2 (by rfl) ⟨740022, by rfl⟩ : syracuseStep 1973393 = 1480045) B1480045
theorem B1481905 : Blo 778337 1481905 := bstep (se 2 (by rfl) ⟨555714, by rfl⟩ : syracuseStep 1481905 = 1111429) B1111429
theorem B1973443 : Blo 778337 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B1318099 : Blo 778337 1318099 := bstep (se 1 (by rfl) ⟨988574, by rfl⟩ : syracuseStep 1318099 = 1977149) B1977149
theorem B1056001 : Blo 778337 1056001 := bstep (se 2 (by rfl) ⟨396000, by rfl⟩ : syracuseStep 1056001 = 792001) B792001
theorem B2628881 : Blo 778337 2628881 := bstep (se 2 (by rfl) ⟨985830, by rfl⟩ : syracuseStep 2628881 = 1971661) B1971661
theorem B1580305 : Blo 778337 1580305 := bstep (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) B1185229
theorem B1973585 : Blo 778337 1973585 := bstep (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) B1480189
theorem B1318241 : Blo 778337 1318241 := bstep (se 2 (by rfl) ⟨494340, by rfl⟩ : syracuseStep 1318241 = 988681) B988681
theorem B2366915 : Blo 778337 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B1318369 : Blo 778337 1318369 := bstep (se 2 (by rfl) ⟨494388, by rfl⟩ : syracuseStep 1318369 = 988777) B988777
theorem B1318403 : Blo 778337 1318403 := bstep (se 1 (by rfl) ⟨988802, by rfl⟩ : syracuseStep 1318403 = 1977605) B1977605
theorem B4988465 : Blo 778337 4988465 := bstep (se 2 (by rfl) ⟨1870674, by rfl⟩ : syracuseStep 4988465 = 3741349) B3741349
theorem B2367053 : Blo 778337 2367053 := bstep (se 3 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 2367053 = 887645) B887645
theorem B3382897 : Blo 778337 3382897 := bstep (se 2 (by rfl) ⟨1268586, by rfl⟩ : syracuseStep 3382897 = 2537173) B2537173
theorem B1318531 : Blo 778337 1318531 := bstep (se 1 (by rfl) ⟨988898, by rfl⟩ : syracuseStep 1318531 = 1977797) B1977797
theorem B1253011 : Blo 778337 1253011 := bstep (se 1 (by rfl) ⟨939758, by rfl⟩ : syracuseStep 1253011 = 1879517) B1879517
theorem B1187569 : Blo 778337 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B1318673 : Blo 778337 1318673 := bstep (se 2 (by rfl) ⟨494502, by rfl⟩ : syracuseStep 1318673 = 989005) B989005
theorem B2629421 : Blo 778337 2629421 := bstep (se 3 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 2629421 = 986033) B986033
theorem B2629475 : Blo 778337 2629475 := bstep (se 1 (by rfl) ⟨1972106, by rfl⟩ : syracuseStep 2629475 = 3944213) B3944213
theorem B2498435 : Blo 778337 2498435 := bstep (se 1 (by rfl) ⟨1873826, by rfl⟩ : syracuseStep 2498435 = 3747653) B3747653
theorem B1318801 : Blo 778337 1318801 := bstep (se 2 (by rfl) ⟨494550, by rfl⟩ : syracuseStep 1318801 = 989101) B989101
theorem B2957219 : Blo 778337 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B1318835 : Blo 778337 1318835 := bstep (se 1 (by rfl) ⟨989126, by rfl⟩ : syracuseStep 1318835 = 1978253) B1978253
theorem B1318963 : Blo 778337 1318963 := bstep (se 1 (by rfl) ⟨989222, by rfl⟩ : syracuseStep 1318963 = 1978445) B1978445
theorem B2629745 : Blo 778337 2629745 := bstep (se 2 (by rfl) ⟨986154, by rfl⟩ : syracuseStep 2629745 = 1972309) B1972309
theorem B1056883 : Blo 778337 1056883 := bstep (se 1 (by rfl) ⟨792662, by rfl⟩ : syracuseStep 1056883 = 1585325) B1585325
theorem B1319105 : Blo 778337 1319105 := bstep (se 2 (by rfl) ⟨494664, by rfl⟩ : syracuseStep 1319105 = 989329) B989329
theorem B1482961 : Blo 778337 1482961 := bstep (se 2 (by rfl) ⟨556110, by rfl⟩ : syracuseStep 1482961 = 1112221) B1112221
theorem B1056979 : Blo 778337 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B1876259 : Blo 778337 1876259 := bstep (se 1 (by rfl) ⟨1407194, by rfl⟩ : syracuseStep 1876259 = 2814389) B2814389
theorem B1974577 : Blo 778337 1974577 := bstep (se 2 (by rfl) ⟨740466, by rfl⟩ : syracuseStep 1974577 = 1480933) B1480933
theorem B1319233 : Blo 778337 1319233 := bstep (se 2 (by rfl) ⟨494712, by rfl⟩ : syracuseStep 1319233 = 989425) B989425
theorem B1319267 : Blo 778337 1319267 := bstep (se 1 (by rfl) ⟨989450, by rfl⟩ : syracuseStep 1319267 = 1978901) B1978901
theorem B16032113 : Blo 778337 16032113 := bstep (se 2 (by rfl) ⟨6012042, by rfl⟩ : syracuseStep 16032113 = 12024085) B12024085
theorem B1057153 : Blo 778337 1057153 := bstep (se 2 (by rfl) ⟨396432, by rfl⟩ : syracuseStep 1057153 = 792865) B792865
theorem B1057217 : Blo 778337 1057217 := bstep (se 2 (by rfl) ⟨396456, by rfl⟩ : syracuseStep 1057217 = 792913) B792913
theorem B1319395 : Blo 778337 1319395 := bstep (se 1 (by rfl) ⟨989546, by rfl⟩ : syracuseStep 1319395 = 1979093) B1979093
theorem B2466289 : Blo 778337 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B1974851 : Blo 778337 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B4989539 : Blo 778337 4989539 := bstep (se 1 (by rfl) ⟨3742154, by rfl⟩ : syracuseStep 4989539 = 7484309) B7484309
theorem B1483363 : Blo 778337 1483363 := bstep (se 1 (by rfl) ⟨1112522, by rfl⟩ : syracuseStep 1483363 = 2225045) B2225045
theorem B1319537 : Blo 778337 1319537 := bstep (se 2 (by rfl) ⟨494826, by rfl⟩ : syracuseStep 1319537 = 989653) B989653
theorem B2630285 : Blo 778337 2630285 := bstep (se 3 (by rfl) ⟨493178, by rfl⟩ : syracuseStep 2630285 = 986357) B986357
theorem B1483409 : Blo 778337 1483409 := bstep (se 2 (by rfl) ⟨556278, by rfl⟩ : syracuseStep 1483409 = 1112557) B1112557
theorem B2630339 : Blo 778337 2630339 := bstep (se 1 (by rfl) ⟨1972754, by rfl⟩ : syracuseStep 2630339 = 3945509) B3945509
theorem B2499281 : Blo 778337 2499281 := bstep (se 2 (by rfl) ⟨937230, by rfl⟩ : syracuseStep 2499281 = 1874461) B1874461
theorem B1319665 : Blo 778337 1319665 := bstep (se 2 (by rfl) ⟨494874, by rfl⟩ : syracuseStep 1319665 = 989749) B989749
theorem B2499331 : Blo 778337 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B1975043 : Blo 778337 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B1319699 : Blo 778337 1319699 := bstep (se 1 (by rfl) ⟨989774, by rfl⟩ : syracuseStep 1319699 = 1979549) B1979549
theorem B307635029 : Blo 778337 307635029 := bstep (se 9 (by rfl) ⟨901274, by rfl⟩ : syracuseStep 307635029 = 1802549) B1802549
theorem B2958221 : Blo 778337 2958221 := bstep (se 3 (by rfl) ⟨554666, by rfl⟩ : syracuseStep 2958221 = 1109333) B1109333
theorem B1319827 : Blo 778337 1319827 := bstep (se 1 (by rfl) ⟨989870, by rfl⟩ : syracuseStep 1319827 = 1979741) B1979741
theorem B3941297 : Blo 778337 3941297 := bstep (se 2 (by rfl) ⟨1477986, by rfl⟩ : syracuseStep 3941297 = 2955973) B2955973
theorem B1483697 : Blo 778337 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B2630609 : Blo 778337 2630609 := bstep (se 2 (by rfl) ⟨986478, by rfl⟩ : syracuseStep 2630609 = 1972957) B1972957
theorem B1319969 : Blo 778337 1319969 := bstep (se 2 (by rfl) ⟨494988, by rfl⟩ : syracuseStep 1319969 = 989977) B989977
theorem B2663491 : Blo 778337 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B1320097 : Blo 778337 1320097 := bstep (se 2 (by rfl) ⟨495036, by rfl⟩ : syracuseStep 1320097 = 990073) B990073
theorem B1320131 : Blo 778337 1320131 := bstep (se 1 (by rfl) ⟨990098, by rfl⟩ : syracuseStep 1320131 = 1980197) B1980197
theorem B1189169 : Blo 778337 1189169 := bstep (se 2 (by rfl) ⟨445938, by rfl⟩ : syracuseStep 1189169 = 891877) B891877
theorem B2368909 : Blo 778337 2368909 := bstep (se 3 (by rfl) ⟨444170, by rfl⟩ : syracuseStep 2368909 = 888341) B888341
theorem B2631149 : Blo 778337 2631149 := bstep (se 3 (by rfl) ⟨493340, by rfl⟩ : syracuseStep 2631149 = 986681) B986681
theorem B1779185 : Blo 778337 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1877489 : Blo 778337 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B4433413 : Blo 778337 4433413 := bstep (se 4 (by rfl) ⟨415632, by rfl⟩ : syracuseStep 4433413 = 831265) B831265
theorem B2631203 : Blo 778337 2631203 := bstep (se 1 (by rfl) ⟨1973402, by rfl⟩ : syracuseStep 2631203 = 3946805) B3946805
theorem B1484419 : Blo 778337 1484419 := bstep (se 1 (by rfl) ⟨1113314, by rfl⟩ : syracuseStep 1484419 = 2226629) B2226629
theorem B1975985 : Blo 778337 1975985 := bstep (se 2 (by rfl) ⟨740994, by rfl⟩ : syracuseStep 1975985 = 1481989) B1481989
theorem B1976035 : Blo 778337 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B2631473 : Blo 778337 2631473 := bstep (se 2 (by rfl) ⟨986802, by rfl⟩ : syracuseStep 2631473 = 1973605) B1973605
theorem B1976177 : Blo 778337 1976177 := bstep (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) B1482133
theorem B2500561 : Blo 778337 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B2107363 : Blo 778337 2107363 := bstep (se 1 (by rfl) ⟨1580522, by rfl⟩ : syracuseStep 2107363 = 3161045) B3161045
theorem B2566129 : Blo 778337 2566129 := bstep (se 2 (by rfl) ⟨962298, by rfl⟩ : syracuseStep 2566129 = 1924597) B1924597
theorem B1484867 : Blo 778337 1484867 := bstep (se 1 (by rfl) ⟨1113650, by rfl⟩ : syracuseStep 1484867 = 2227301) B2227301
theorem B18229475 : Blo 778337 18229475 := bstep (se 1 (by rfl) ⟨13672106, by rfl⟩ : syracuseStep 18229475 = 27344213) B27344213
theorem B2632013 : Blo 778337 2632013 := bstep (se 3 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 2632013 = 987005) B987005
theorem B3942755 : Blo 778337 3942755 := bstep (se 1 (by rfl) ⟨2957066, by rfl⟩ : syracuseStep 3942755 = 5914133) B5914133
theorem B1485155 : Blo 778337 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B2632067 : Blo 778337 2632067 := bstep (se 1 (by rfl) ⟨1974050, by rfl⟩ : syracuseStep 2632067 = 3948101) B3948101
theorem B1583491 : Blo 778337 1583491 := bstep (se 1 (by rfl) ⟨1187618, by rfl⟩ : syracuseStep 1583491 = 2375237) B2375237
theorem B1583555 : Blo 778337 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B7481969 : Blo 778337 7481969 := bstep (se 2 (by rfl) ⟨2805738, by rfl⟩ : syracuseStep 7481969 = 5611477) B5611477
theorem B2632337 : Blo 778337 2632337 := bstep (se 2 (by rfl) ⟨987126, by rfl⟩ : syracuseStep 2632337 = 1974253) B1974253
theorem B1977169 : Blo 778337 1977169 := bstep (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) B1482877
theorem B6761357 : Blo 778337 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B2370467 : Blo 778337 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B2960333 : Blo 778337 2960333 := bstep (se 3 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 2960333 = 1110125) B1110125
theorem B2108465 : Blo 778337 2108465 := bstep (se 2 (by rfl) ⟨790674, by rfl⟩ : syracuseStep 2108465 = 1581349) B1581349
theorem B1977443 : Blo 778337 1977443 := bstep (se 1 (by rfl) ⟨1483082, by rfl⟩ : syracuseStep 1977443 = 2966165) B2966165
theorem B2501741 : Blo 778337 2501741 := bstep (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) B938153
theorem B3943565 : Blo 778337 3943565 := bstep (se 3 (by rfl) ⟨739418, by rfl⟩ : syracuseStep 3943565 = 1478837) B1478837
theorem B2632877 : Blo 778337 2632877 := bstep (se 3 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 2632877 = 987329) B987329
theorem B2632931 : Blo 778337 2632931 := bstep (se 1 (by rfl) ⟨1974698, by rfl⟩ : syracuseStep 2632931 = 3949397) B3949397
theorem B2534627 : Blo 778337 2534627 := bstep (se 1 (by rfl) ⟨1900970, by rfl⟩ : syracuseStep 2534627 = 3801941) B3801941
theorem B1977635 : Blo 778337 1977635 := bstep (se 1 (by rfl) ⟨1483226, by rfl⟩ : syracuseStep 1977635 = 2966453) B2966453
theorem B2108717 : Blo 778337 2108717 := bstep (se 3 (by rfl) ⟨395384, by rfl⟩ : syracuseStep 2108717 = 790769) B790769
theorem B1355105 : Blo 778337 1355105 := bstep (se 2 (by rfl) ⟨508164, by rfl⟩ : syracuseStep 1355105 = 1016329) B1016329
theorem B4435397 : Blo 778337 4435397 := bstep (se 4 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 4435397 = 831637) B831637
theorem B2633201 : Blo 778337 2633201 := bstep (se 2 (by rfl) ⟨987450, by rfl⟩ : syracuseStep 2633201 = 1974901) B1974901
theorem B2665997 : Blo 778337 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B2961137 : Blo 778337 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B8892341 : Blo 778337 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B2633741 : Blo 778337 2633741 := bstep (se 3 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 2633741 = 987653) B987653
theorem B2633795 : Blo 778337 2633795 := bstep (se 1 (by rfl) ⟨1975346, by rfl⟩ : syracuseStep 2633795 = 3950693) B3950693
theorem B1978577 : Blo 778337 1978577 := bstep (se 2 (by rfl) ⟨741966, by rfl⟩ : syracuseStep 1978577 = 1483933) B1483933
theorem B1978627 : Blo 778337 1978627 := bstep (se 1 (by rfl) ⟨1483970, by rfl⟩ : syracuseStep 1978627 = 2967941) B2967941
theorem B2634065 : Blo 778337 2634065 := bstep (se 2 (by rfl) ⟨987774, by rfl⟩ : syracuseStep 2634065 = 1975549) B1975549
theorem B2961805 : Blo 778337 2961805 := bstep (se 3 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 2961805 = 1110677) B1110677
theorem B1978769 : Blo 778337 1978769 := bstep (se 2 (by rfl) ⟨742038, by rfl⟩ : syracuseStep 1978769 = 1484077) B1484077
theorem B832051 : Blo 778337 832051 := bstep (se 1 (by rfl) ⟨624038, by rfl⟩ : syracuseStep 832051 = 1248077) B1248077
theorem B4993741 : Blo 778337 4993741 := bstep (se 3 (by rfl) ⟨936326, by rfl⟩ : syracuseStep 4993741 = 1872653) B1872653
theorem B2503523 : Blo 778337 2503523 := bstep (se 1 (by rfl) ⟨1877642, by rfl⟩ : syracuseStep 2503523 = 3755285) B3755285
theorem B2634605 : Blo 778337 2634605 := bstep (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) B987977
theorem B2634659 : Blo 778337 2634659 := bstep (se 1 (by rfl) ⟨1975994, by rfl⟩ : syracuseStep 2634659 = 3951989) B3951989
theorem B2110499 : Blo 778337 2110499 := bstep (se 1 (by rfl) ⟨1582874, by rfl⟩ : syracuseStep 2110499 = 3165749) B3165749
theorem B832675 : Blo 778337 832675 := bstep (se 1 (by rfl) ⟨624506, by rfl⟩ : syracuseStep 832675 = 1249013) B1249013
theorem B2962595 : Blo 778337 2962595 := bstep (se 1 (by rfl) ⟨2221946, by rfl⟩ : syracuseStep 2962595 = 4443893) B4443893
theorem B2634929 : Blo 778337 2634929 := bstep (se 2 (by rfl) ⟨988098, by rfl⟩ : syracuseStep 2634929 = 1976197) B1976197
theorem B1979761 : Blo 778337 1979761 := bstep (se 2 (by rfl) ⟨742410, by rfl⟩ : syracuseStep 1979761 = 1484821) B1484821
theorem B1980035 : Blo 778337 1980035 := bstep (se 1 (by rfl) ⟨1485026, by rfl⟩ : syracuseStep 1980035 = 2970053) B2970053
theorem B2635469 : Blo 778337 2635469 := bstep (se 3 (by rfl) ⟨494150, by rfl⟩ : syracuseStep 2635469 = 988301) B988301
theorem B2635523 : Blo 778337 2635523 := bstep (se 1 (by rfl) ⟨1976642, by rfl⟩ : syracuseStep 2635523 = 3953285) B3953285
theorem B2963249 : Blo 778337 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B1980227 : Blo 778337 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B2930573 : Blo 778337 2930573 := bstep (se 3 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 2930573 = 1098965) B1098965
theorem B2504611 : Blo 778337 2504611 := bstep (se 1 (by rfl) ⟨1878458, by rfl⟩ : syracuseStep 2504611 = 3756917) B3756917
theorem B3946481 : Blo 778337 3946481 := bstep (se 2 (by rfl) ⟨1479930, by rfl⟩ : syracuseStep 3946481 = 2959861) B2959861
theorem B2635793 : Blo 778337 2635793 := bstep (se 2 (by rfl) ⟨988422, by rfl⟩ : syracuseStep 2635793 = 1976845) B1976845
theorem B2504753 : Blo 778337 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B2668625 : Blo 778337 2668625 := bstep (se 2 (by rfl) ⟨1000734, by rfl⟩ : syracuseStep 2668625 = 2001469) B2001469
theorem B5912675 : Blo 778337 5912675 := bstep (se 1 (by rfl) ⟨4434506, by rfl⟩ : syracuseStep 5912675 = 8869013) B8869013
theorem B1751345 : Blo 778337 1751345 := bstep (se 2 (by rfl) ⟨656754, by rfl⟩ : syracuseStep 1751345 = 1313509) B1313509
theorem B1751363 : Blo 778337 1751363 := bstep (se 1 (by rfl) ⟨1313522, by rfl⟩ : syracuseStep 1751363 = 2627045) B2627045
theorem B7485965 : Blo 778337 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B2636333 : Blo 778337 2636333 := bstep (se 3 (by rfl) ⟨494312, by rfl⟩ : syracuseStep 2636333 = 988625) B988625
theorem B1751633 : Blo 778337 1751633 := bstep (se 2 (by rfl) ⟨656862, by rfl⟩ : syracuseStep 1751633 = 1313725) B1313725
theorem B1751651 : Blo 778337 1751651 := bstep (se 1 (by rfl) ⟨1313738, by rfl⟩ : syracuseStep 1751651 = 2627477) B2627477
theorem B2636387 : Blo 778337 2636387 := bstep (se 1 (by rfl) ⟨1977290, by rfl⟩ : syracuseStep 2636387 = 3954581) B3954581
theorem B3324685 : Blo 778337 3324685 := bstep (se 3 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 3324685 = 1246757) B1246757
theorem B7486307 : Blo 778337 7486307 := bstep (se 1 (by rfl) ⟨5614730, by rfl⟩ : syracuseStep 7486307 = 11229461) B11229461
theorem B1751921 : Blo 778337 1751921 := bstep (se 2 (by rfl) ⟨656970, by rfl⟩ : syracuseStep 1751921 = 1313941) B1313941
theorem B2636657 : Blo 778337 2636657 := bstep (se 2 (by rfl) ⟨988746, by rfl⟩ : syracuseStep 2636657 = 1977493) B1977493
theorem B1751939 : Blo 778337 1751939 := bstep (se 1 (by rfl) ⟨1313954, by rfl⟩ : syracuseStep 1751939 = 2627909) B2627909
theorem B834563 : Blo 778337 834563 := bstep (se 1 (by rfl) ⟨625922, by rfl⟩ : syracuseStep 834563 = 1251845) B1251845
theorem B1752209 : Blo 778337 1752209 := bstep (se 2 (by rfl) ⟨657078, by rfl⟩ : syracuseStep 1752209 = 1314157) B1314157
theorem B1752227 : Blo 778337 1752227 := bstep (se 1 (by rfl) ⟨1314170, by rfl⟩ : syracuseStep 1752227 = 2628341) B2628341
theorem B4439245 : Blo 778337 4439245 := bstep (se 3 (by rfl) ⟨832358, by rfl⟩ : syracuseStep 4439245 = 1664717) B1664717
theorem B2964707 : Blo 778337 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B2112749 : Blo 778337 2112749 := bstep (se 3 (by rfl) ⟨396140, by rfl⟩ : syracuseStep 2112749 = 792281) B792281
theorem B2964721 : Blo 778337 2964721 := bstep (se 2 (by rfl) ⟨1111770, by rfl⟩ : syracuseStep 2964721 = 2223541) B2223541
theorem B2506097 : Blo 778337 2506097 := bstep (se 2 (by rfl) ⟨939786, by rfl⟩ : syracuseStep 2506097 = 1879573) B1879573
theorem B2637197 : Blo 778337 2637197 := bstep (se 3 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 2637197 = 988949) B988949
theorem B3947939 : Blo 778337 3947939 := bstep (se 1 (by rfl) ⟨2960954, by rfl⟩ : syracuseStep 3947939 = 5921909) B5921909
theorem B1752497 : Blo 778337 1752497 := bstep (se 2 (by rfl) ⟨657186, by rfl⟩ : syracuseStep 1752497 = 1314373) B1314373
theorem B1752515 : Blo 778337 1752515 := bstep (se 1 (by rfl) ⟨1314386, by rfl⟩ : syracuseStep 1752515 = 2628773) B2628773
theorem B2637251 : Blo 778337 2637251 := bstep (se 1 (by rfl) ⟨1977938, by rfl⟩ : syracuseStep 2637251 = 3955877) B3955877
theorem B1752785 : Blo 778337 1752785 := bstep (se 2 (by rfl) ⟨657294, by rfl⟩ : syracuseStep 1752785 = 1314589) B1314589
theorem B2637521 : Blo 778337 2637521 := bstep (se 2 (by rfl) ⟨989070, by rfl⟩ : syracuseStep 2637521 = 1978141) B1978141
theorem B1752803 : Blo 778337 1752803 := bstep (se 1 (by rfl) ⟨1314602, by rfl⟩ : syracuseStep 1752803 = 2629205) B2629205
theorem B4505357 : Blo 778337 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B2998093 : Blo 778337 2998093 := bstep (se 3 (by rfl) ⟨562142, by rfl⟩ : syracuseStep 2998093 = 1124285) B1124285
theorem B1753073 : Blo 778337 1753073 := bstep (se 2 (by rfl) ⟨657402, by rfl⟩ : syracuseStep 1753073 = 1314805) B1314805
theorem B1753091 : Blo 778337 1753091 := bstep (se 1 (by rfl) ⟨1314818, by rfl⟩ : syracuseStep 1753091 = 2629637) B2629637
theorem B2277517 : Blo 778337 2277517 := bstep (se 3 (by rfl) ⟨427034, by rfl⟩ : syracuseStep 2277517 = 854069) B854069
theorem B3948749 : Blo 778337 3948749 := bstep (se 3 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 3948749 = 1480781) B1480781
theorem B2638061 : Blo 778337 2638061 := bstep (se 3 (by rfl) ⟨494636, by rfl⟩ : syracuseStep 2638061 = 989273) B989273
theorem B1753361 : Blo 778337 1753361 := bstep (se 2 (by rfl) ⟨657510, by rfl⟩ : syracuseStep 1753361 = 1315021) B1315021
theorem B1753379 : Blo 778337 1753379 := bstep (se 1 (by rfl) ⟨1315034, by rfl⟩ : syracuseStep 1753379 = 2630069) B2630069
theorem B2638115 : Blo 778337 2638115 := bstep (se 1 (by rfl) ⟨1978586, by rfl⟩ : syracuseStep 2638115 = 3957173) B3957173
theorem B1524227 : Blo 778337 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B1753649 : Blo 778337 1753649 := bstep (se 2 (by rfl) ⟨657618, by rfl⟩ : syracuseStep 1753649 = 1315237) B1315237
theorem B2638385 : Blo 778337 2638385 := bstep (se 2 (by rfl) ⟨989394, by rfl⟩ : syracuseStep 2638385 = 1978789) B1978789
theorem B1753667 : Blo 778337 1753667 := bstep (se 1 (by rfl) ⟨1315250, by rfl⟩ : syracuseStep 1753667 = 2630501) B2630501
theorem B2376305 : Blo 778337 2376305 := bstep (se 2 (by rfl) ⟨891114, by rfl⟩ : syracuseStep 2376305 = 1782229) B1782229
theorem B1688227 : Blo 778337 1688227 := bstep (se 1 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 1688227 = 2532341) B2532341
theorem B2966179 : Blo 778337 2966179 := bstep (se 1 (by rfl) ⟨2224634, by rfl⟩ : syracuseStep 2966179 = 4449269) B4449269
theorem B1753937 : Blo 778337 1753937 := bstep (se 2 (by rfl) ⟨657726, by rfl⟩ : syracuseStep 1753937 = 1315453) B1315453
theorem B1753955 : Blo 778337 1753955 := bstep (se 1 (by rfl) ⟨1315466, by rfl⟩ : syracuseStep 1753955 = 2630933) B2630933
theorem B3752995 : Blo 778337 3752995 := bstep (se 1 (by rfl) ⟨2814746, by rfl⟩ : syracuseStep 3752995 = 5629493) B5629493
theorem B2638925 : Blo 778337 2638925 := bstep (se 3 (by rfl) ⟨494798, by rfl⟩ : syracuseStep 2638925 = 989597) B989597
theorem B1754225 : Blo 778337 1754225 := bstep (se 2 (by rfl) ⟨657834, by rfl⟩ : syracuseStep 1754225 = 1315669) B1315669
theorem B1754243 : Blo 778337 1754243 := bstep (se 1 (by rfl) ⟨1315682, by rfl⟩ : syracuseStep 1754243 = 2631365) B2631365
theorem B2638979 : Blo 778337 2638979 := bstep (se 1 (by rfl) ⟨1979234, by rfl⟩ : syracuseStep 2638979 = 3958469) B3958469
theorem B4801669 : Blo 778337 4801669 := bstep (se 4 (by rfl) ⟨450156, by rfl⟩ : syracuseStep 4801669 = 900313) B900313
theorem B4441229 : Blo 778337 4441229 := bstep (se 3 (by rfl) ⟨832730, by rfl⟩ : syracuseStep 4441229 = 1665461) B1665461
theorem B78169315 : Blo 778337 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B4736261 : Blo 778337 4736261 := bstep (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) B888049
theorem B2671949 : Blo 778337 2671949 := bstep (se 3 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 2671949 = 1001981) B1001981
theorem B1754513 : Blo 778337 1754513 := bstep (se 2 (by rfl) ⟨657942, by rfl⟩ : syracuseStep 1754513 = 1315885) B1315885
theorem B2639249 : Blo 778337 2639249 := bstep (se 2 (by rfl) ⟨989718, by rfl⟩ : syracuseStep 2639249 = 1979437) B1979437
theorem B1754531 : Blo 778337 1754531 := bstep (se 1 (by rfl) ⟨1315898, by rfl⟩ : syracuseStep 1754531 = 2631797) B2631797
theorem B1754801 : Blo 778337 1754801 := bstep (se 2 (by rfl) ⟨658050, by rfl⟩ : syracuseStep 1754801 = 1316101) B1316101
theorem B1754819 : Blo 778337 1754819 := bstep (se 1 (by rfl) ⟨1316114, by rfl⟩ : syracuseStep 1754819 = 2632229) B2632229
theorem B2639789 : Blo 778337 2639789 := bstep (se 3 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 2639789 = 989921) B989921
theorem B1755089 : Blo 778337 1755089 := bstep (se 2 (by rfl) ⟨658158, by rfl⟩ : syracuseStep 1755089 = 1316317) B1316317
theorem B1755107 : Blo 778337 1755107 := bstep (se 1 (by rfl) ⟨1316330, by rfl⟩ : syracuseStep 1755107 = 2632661) B2632661
theorem B2639843 : Blo 778337 2639843 := bstep (se 1 (by rfl) ⟨1979882, by rfl⟩ : syracuseStep 2639843 = 3959765) B3959765
theorem B4442161 : Blo 778337 4442161 := bstep (se 2 (by rfl) ⟨1665810, by rfl⟩ : syracuseStep 4442161 = 3331621) B3331621
theorem B936019 : Blo 778337 936019 := bstep (se 1 (by rfl) ⟨702014, by rfl⟩ : syracuseStep 936019 = 1404029) B1404029
theorem B1755377 : Blo 778337 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B3754225 : Blo 778337 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B2640113 : Blo 778337 2640113 := bstep (se 2 (by rfl) ⟨990042, by rfl⟩ : syracuseStep 2640113 = 1980085) B1980085
theorem B1755395 : Blo 778337 1755395 := bstep (se 1 (by rfl) ⟨1316546, by rfl⟩ : syracuseStep 1755395 = 2633093) B2633093
theorem B2411021 : Blo 778337 2411021 := bstep (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) B904133
theorem B1755665 : Blo 778337 1755665 := bstep (se 2 (by rfl) ⟨658374, by rfl⟩ : syracuseStep 1755665 = 1316749) B1316749
theorem B1755683 : Blo 778337 1755683 := bstep (se 1 (by rfl) ⟨1316762, by rfl⟩ : syracuseStep 1755683 = 2633525) B2633525
theorem B15026741 : Blo 778337 15026741 := bstep (se 5 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 15026741 = 1408757) B1408757
theorem B3557965 : Blo 778337 3557965 := bstep (se 3 (by rfl) ⟨667118, by rfl⟩ : syracuseStep 3557965 = 1334237) B1334237
theorem B1755953 : Blo 778337 1755953 := bstep (se 2 (by rfl) ⟨658482, by rfl⟩ : syracuseStep 1755953 = 1316965) B1316965
theorem B1755971 : Blo 778337 1755971 := bstep (se 1 (by rfl) ⟨1316978, by rfl⟩ : syracuseStep 1755971 = 2633957) B2633957
theorem B2968397 : Blo 778337 2968397 := bstep (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) B1113149
theorem B3329009 : Blo 778337 3329009 := bstep (se 2 (by rfl) ⟨1248378, by rfl⟩ : syracuseStep 3329009 = 2496757) B2496757
theorem B3329059 : Blo 778337 3329059 := bstep (se 1 (by rfl) ⟨2496794, by rfl⟩ : syracuseStep 3329059 = 4993589) B4993589
theorem B3951665 : Blo 778337 3951665 := bstep (se 2 (by rfl) ⟨1481874, by rfl⟩ : syracuseStep 3951665 = 2963749) B2963749
theorem B1756241 : Blo 778337 1756241 := bstep (se 2 (by rfl) ⟨658590, by rfl⟩ : syracuseStep 1756241 = 1317181) B1317181
theorem B1756259 : Blo 778337 1756259 := bstep (se 1 (by rfl) ⟨1317194, by rfl⟩ : syracuseStep 1756259 = 2634389) B2634389
theorem B5786765 : Blo 778337 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B3165425 : Blo 778337 3165425 := bstep (se 2 (by rfl) ⟨1187034, by rfl⟩ : syracuseStep 3165425 = 2374069) B2374069
theorem B5918021 : Blo 778337 5918021 := bstep (se 4 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 5918021 = 1109629) B1109629
theorem B2674001 : Blo 778337 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B5000561 : Blo 778337 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B1756529 : Blo 778337 1756529 := bstep (se 2 (by rfl) ⟨658698, by rfl⟩ : syracuseStep 1756529 = 1317397) B1317397
theorem B1756547 : Blo 778337 1756547 := bstep (se 1 (by rfl) ⟨1317410, by rfl⟩ : syracuseStep 1756547 = 2634821) B2634821
theorem B4443619 : Blo 778337 4443619 := bstep (se 1 (by rfl) ⟨3332714, by rfl⟩ : syracuseStep 4443619 = 6665429) B6665429
theorem B1756817 : Blo 778337 1756817 := bstep (se 2 (by rfl) ⟨658806, by rfl⟩ : syracuseStep 1756817 = 1317613) B1317613
theorem B1756835 : Blo 778337 1756835 := bstep (se 1 (by rfl) ⟨1317626, by rfl⟩ : syracuseStep 1756835 = 2635253) B2635253
theorem B8867555 : Blo 778337 8867555 := bstep (se 1 (by rfl) ⟨6650666, by rfl⟩ : syracuseStep 8867555 = 13301333) B13301333
theorem B3755747 : Blo 778337 3755747 := bstep (se 1 (by rfl) ⟨2816810, by rfl⟩ : syracuseStep 3755747 = 5633621) B5633621
theorem B5001101 : Blo 778337 5001101 := bstep (se 3 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 5001101 = 1875413) B1875413
theorem B1757105 : Blo 778337 1757105 := bstep (se 2 (by rfl) ⟨658914, by rfl⟩ : syracuseStep 1757105 = 1317829) B1317829
theorem B1757123 : Blo 778337 1757123 := bstep (se 1 (by rfl) ⟨1317842, by rfl⟩ : syracuseStep 1757123 = 2635685) B2635685
theorem B4444145 : Blo 778337 4444145 := bstep (se 2 (by rfl) ⟨1666554, by rfl⟩ : syracuseStep 4444145 = 3333109) B3333109
theorem B1167521 : Blo 778337 1167521 := bstep (se 2 (by rfl) ⟨437820, by rfl⟩ : syracuseStep 1167521 = 875641) B875641
theorem B1167539 : Blo 778337 1167539 := bstep (se 1 (by rfl) ⟨875654, by rfl⟩ : syracuseStep 1167539 = 1751309) B1751309
theorem B1167569 : Blo 778337 1167569 := bstep (se 2 (by rfl) ⟨437838, by rfl⟩ : syracuseStep 1167569 = 875677) B875677
theorem B1757393 : Blo 778337 1757393 := bstep (se 2 (by rfl) ⟨659022, by rfl⟩ : syracuseStep 1757393 = 1318045) B1318045
theorem B1167587 : Blo 778337 1167587 := bstep (se 1 (by rfl) ⟨875690, by rfl⟩ : syracuseStep 1167587 = 1751381) B1751381
theorem B1757411 : Blo 778337 1757411 := bstep (se 1 (by rfl) ⟨1318058, by rfl⟩ : syracuseStep 1757411 = 2636117) B2636117
theorem B1167617 : Blo 778337 1167617 := bstep (se 2 (by rfl) ⟨437856, by rfl⟩ : syracuseStep 1167617 = 875713) B875713
theorem B1167635 : Blo 778337 1167635 := bstep (se 1 (by rfl) ⟨875726, by rfl⟩ : syracuseStep 1167635 = 1751453) B1751453
theorem B3559715 : Blo 778337 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B1167665 : Blo 778337 1167665 := bstep (se 2 (by rfl) ⟨437874, by rfl⟩ : syracuseStep 1167665 = 875749) B875749
theorem B1167683 : Blo 778337 1167683 := bstep (se 1 (by rfl) ⟨875762, by rfl⟩ : syracuseStep 1167683 = 1751525) B1751525
theorem B1167713 : Blo 778337 1167713 := bstep (se 2 (by rfl) ⟨437892, by rfl⟩ : syracuseStep 1167713 = 875785) B875785
theorem B1167731 : Blo 778337 1167731 := bstep (se 1 (by rfl) ⟨875798, by rfl⟩ : syracuseStep 1167731 = 1751597) B1751597
theorem B1167761 : Blo 778337 1167761 := bstep (se 2 (by rfl) ⟨437910, by rfl⟩ : syracuseStep 1167761 = 875821) B875821
theorem B1167779 : Blo 778337 1167779 := bstep (se 1 (by rfl) ⟨875834, by rfl⟩ : syracuseStep 1167779 = 1751669) B1751669
theorem B1167809 : Blo 778337 1167809 := bstep (se 2 (by rfl) ⟨437928, by rfl⟩ : syracuseStep 1167809 = 875857) B875857
theorem B1167827 : Blo 778337 1167827 := bstep (se 1 (by rfl) ⟨875870, by rfl⟩ : syracuseStep 1167827 = 1751741) B1751741
theorem B3953123 : Blo 778337 3953123 := bstep (se 1 (by rfl) ⟨2964842, by rfl⟩ : syracuseStep 3953123 = 5929685) B5929685
theorem B1167857 : Blo 778337 1167857 := bstep (se 2 (by rfl) ⟨437946, by rfl⟩ : syracuseStep 1167857 = 875893) B875893
theorem B1757681 : Blo 778337 1757681 := bstep (se 2 (by rfl) ⟨659130, by rfl⟩ : syracuseStep 1757681 = 1318261) B1318261
theorem B1167875 : Blo 778337 1167875 := bstep (se 1 (by rfl) ⟨875906, by rfl⟩ : syracuseStep 1167875 = 1751813) B1751813
theorem B1757699 : Blo 778337 1757699 := bstep (se 1 (by rfl) ⟨1318274, by rfl⟩ : syracuseStep 1757699 = 2636549) B2636549
theorem B1167905 : Blo 778337 1167905 := bstep (se 2 (by rfl) ⟨437964, by rfl⟩ : syracuseStep 1167905 = 875929) B875929
theorem B1167923 : Blo 778337 1167923 := bstep (se 1 (by rfl) ⟨875942, by rfl⟩ : syracuseStep 1167923 = 1751885) B1751885
theorem B1167953 : Blo 778337 1167953 := bstep (se 2 (by rfl) ⟨437982, by rfl⟩ : syracuseStep 1167953 = 875965) B875965
theorem B1167971 : Blo 778337 1167971 := bstep (se 1 (by rfl) ⟨875978, by rfl⟩ : syracuseStep 1167971 = 1751957) B1751957
theorem B1168001 : Blo 778337 1168001 := bstep (se 2 (by rfl) ⟨438000, by rfl⟩ : syracuseStep 1168001 = 876001) B876001
theorem B1168019 : Blo 778337 1168019 := bstep (se 1 (by rfl) ⟨876014, by rfl⟩ : syracuseStep 1168019 = 1752029) B1752029
theorem B1168049 : Blo 778337 1168049 := bstep (se 2 (by rfl) ⟨438018, by rfl⟩ : syracuseStep 1168049 = 876037) B876037
theorem B1168067 : Blo 778337 1168067 := bstep (se 1 (by rfl) ⟨876050, by rfl⟩ : syracuseStep 1168067 = 1752101) B1752101
theorem B1168097 : Blo 778337 1168097 := bstep (se 2 (by rfl) ⟨438036, by rfl⟩ : syracuseStep 1168097 = 876073) B876073
theorem B1168115 : Blo 778337 1168115 := bstep (se 1 (by rfl) ⟨876086, by rfl⟩ : syracuseStep 1168115 = 1752173) B1752173
theorem B1168145 : Blo 778337 1168145 := bstep (se 2 (by rfl) ⟨438054, by rfl⟩ : syracuseStep 1168145 = 876109) B876109
theorem B1757969 : Blo 778337 1757969 := bstep (se 2 (by rfl) ⟨659238, by rfl⟩ : syracuseStep 1757969 = 1318477) B1318477
theorem B1168163 : Blo 778337 1168163 := bstep (se 1 (by rfl) ⟨876122, by rfl⟩ : syracuseStep 1168163 = 1752245) B1752245
theorem B1757987 : Blo 778337 1757987 := bstep (se 1 (by rfl) ⟨1318490, by rfl⟩ : syracuseStep 1757987 = 2636981) B2636981
theorem B2216753 : Blo 778337 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B1168193 : Blo 778337 1168193 := bstep (se 2 (by rfl) ⟨438072, by rfl⟩ : syracuseStep 1168193 = 876145) B876145
theorem B1200961 : Blo 778337 1200961 := bstep (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) B900721
theorem B1332035 : Blo 778337 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B1168211 : Blo 778337 1168211 := bstep (se 1 (by rfl) ⟨876158, by rfl⟩ : syracuseStep 1168211 = 1752317) B1752317
theorem B1168241 : Blo 778337 1168241 := bstep (se 2 (by rfl) ⟨438090, by rfl⟩ : syracuseStep 1168241 = 876181) B876181
theorem B1168259 : Blo 778337 1168259 := bstep (se 1 (by rfl) ⟨876194, by rfl⟩ : syracuseStep 1168259 = 1752389) B1752389
theorem B1168289 : Blo 778337 1168289 := bstep (se 2 (by rfl) ⟨438108, by rfl⟩ : syracuseStep 1168289 = 876217) B876217
theorem B1168307 : Blo 778337 1168307 := bstep (se 1 (by rfl) ⟨876230, by rfl⟩ : syracuseStep 1168307 = 1752461) B1752461
theorem B1168337 : Blo 778337 1168337 := bstep (se 2 (by rfl) ⟨438126, by rfl⟩ : syracuseStep 1168337 = 876253) B876253
theorem B1168355 : Blo 778337 1168355 := bstep (se 1 (by rfl) ⟨876266, by rfl⟩ : syracuseStep 1168355 = 1752533) B1752533
theorem B1168385 : Blo 778337 1168385 := bstep (se 2 (by rfl) ⟨438144, by rfl⟩ : syracuseStep 1168385 = 876289) B876289
theorem B1168403 : Blo 778337 1168403 := bstep (se 1 (by rfl) ⟨876302, by rfl⟩ : syracuseStep 1168403 = 1752605) B1752605
theorem B1168433 : Blo 778337 1168433 := bstep (se 2 (by rfl) ⟨438162, by rfl⟩ : syracuseStep 1168433 = 876325) B876325
theorem B1758257 : Blo 778337 1758257 := bstep (se 2 (by rfl) ⟨659346, by rfl⟩ : syracuseStep 1758257 = 1318693) B1318693
theorem B1168451 : Blo 778337 1168451 := bstep (se 1 (by rfl) ⟨876338, by rfl⟩ : syracuseStep 1168451 = 1752677) B1752677
theorem B1758275 : Blo 778337 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1168481 : Blo 778337 1168481 := bstep (se 2 (by rfl) ⟨438180, by rfl⟩ : syracuseStep 1168481 = 876361) B876361
theorem B1168499 : Blo 778337 1168499 := bstep (se 1 (by rfl) ⟨876374, by rfl⟩ : syracuseStep 1168499 = 1752749) B1752749
theorem B1168529 : Blo 778337 1168529 := bstep (se 2 (by rfl) ⟨438198, by rfl⟩ : syracuseStep 1168529 = 876397) B876397
theorem B1168547 : Blo 778337 1168547 := bstep (se 1 (by rfl) ⟨876410, by rfl⟩ : syracuseStep 1168547 = 1752821) B1752821
theorem B1168577 : Blo 778337 1168577 := bstep (se 2 (by rfl) ⟨438216, by rfl⟩ : syracuseStep 1168577 = 876433) B876433
theorem B1168595 : Blo 778337 1168595 := bstep (se 1 (by rfl) ⟨876446, by rfl⟩ : syracuseStep 1168595 = 1752893) B1752893
theorem B1168625 : Blo 778337 1168625 := bstep (se 2 (by rfl) ⟨438234, by rfl⟩ : syracuseStep 1168625 = 876469) B876469
theorem B4216049 : Blo 778337 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B1168643 : Blo 778337 1168643 := bstep (se 1 (by rfl) ⟨876482, by rfl⟩ : syracuseStep 1168643 = 1752965) B1752965
theorem B3953933 : Blo 778337 3953933 := bstep (se 3 (by rfl) ⟨741362, by rfl⟩ : syracuseStep 3953933 = 1482725) B1482725
theorem B1168673 : Blo 778337 1168673 := bstep (se 2 (by rfl) ⟨438252, by rfl⟩ : syracuseStep 1168673 = 876505) B876505
theorem B1168691 : Blo 778337 1168691 := bstep (se 1 (by rfl) ⟨876518, by rfl⟩ : syracuseStep 1168691 = 1753037) B1753037
theorem B1168721 : Blo 778337 1168721 := bstep (se 2 (by rfl) ⟨438270, by rfl⟩ : syracuseStep 1168721 = 876541) B876541
theorem B1758545 : Blo 778337 1758545 := bstep (se 2 (by rfl) ⟨659454, by rfl⟩ : syracuseStep 1758545 = 1318909) B1318909
theorem B1168739 : Blo 778337 1168739 := bstep (se 1 (by rfl) ⟨876554, by rfl⟩ : syracuseStep 1168739 = 1753109) B1753109
theorem B1758563 : Blo 778337 1758563 := bstep (se 1 (by rfl) ⟨1318922, by rfl⟩ : syracuseStep 1758563 = 2637845) B2637845
theorem B1168769 : Blo 778337 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B3331469 : Blo 778337 3331469 := bstep (se 3 (by rfl) ⟨624650, by rfl⟩ : syracuseStep 3331469 = 1249301) B1249301
theorem B1168787 : Blo 778337 1168787 := bstep (se 1 (by rfl) ⟨876590, by rfl⟩ : syracuseStep 1168787 = 1753181) B1753181
theorem B4445603 : Blo 778337 4445603 := bstep (se 1 (by rfl) ⟨3334202, by rfl⟩ : syracuseStep 4445603 = 6668405) B6668405
theorem B1168817 : Blo 778337 1168817 := bstep (se 2 (by rfl) ⟨438306, by rfl⟩ : syracuseStep 1168817 = 876613) B876613
theorem B1168835 : Blo 778337 1168835 := bstep (se 1 (by rfl) ⟨876626, by rfl⟩ : syracuseStep 1168835 = 1753253) B1753253
theorem B1168865 : Blo 778337 1168865 := bstep (se 2 (by rfl) ⟨438324, by rfl⟩ : syracuseStep 1168865 = 876649) B876649
theorem B1168883 : Blo 778337 1168883 := bstep (se 1 (by rfl) ⟨876662, by rfl⟩ : syracuseStep 1168883 = 1753325) B1753325
theorem B1168913 : Blo 778337 1168913 := bstep (se 2 (by rfl) ⟨438342, by rfl⟩ : syracuseStep 1168913 = 876685) B876685
theorem B1168931 : Blo 778337 1168931 := bstep (se 1 (by rfl) ⟨876698, by rfl⟩ : syracuseStep 1168931 = 1753397) B1753397
theorem B1168961 : Blo 778337 1168961 := bstep (se 2 (by rfl) ⟨438360, by rfl⟩ : syracuseStep 1168961 = 876721) B876721
theorem B1168979 : Blo 778337 1168979 := bstep (se 1 (by rfl) ⟨876734, by rfl⟩ : syracuseStep 1168979 = 1753469) B1753469
theorem B1169009 : Blo 778337 1169009 := bstep (se 2 (by rfl) ⟨438378, by rfl⟩ : syracuseStep 1169009 = 876757) B876757
theorem B1758833 : Blo 778337 1758833 := bstep (se 2 (by rfl) ⟨659562, by rfl⟩ : syracuseStep 1758833 = 1319125) B1319125
theorem B1169027 : Blo 778337 1169027 := bstep (se 1 (by rfl) ⟨876770, by rfl⟩ : syracuseStep 1169027 = 1753541) B1753541
theorem B1758851 : Blo 778337 1758851 := bstep (se 1 (by rfl) ⟨1319138, by rfl⟩ : syracuseStep 1758851 = 2638277) B2638277
theorem B1169057 : Blo 778337 1169057 := bstep (se 2 (by rfl) ⟨438396, by rfl⟩ : syracuseStep 1169057 = 876793) B876793
theorem B3757745 : Blo 778337 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B1169075 : Blo 778337 1169075 := bstep (se 1 (by rfl) ⟨876806, by rfl⟩ : syracuseStep 1169075 = 1753613) B1753613
theorem B1169105 : Blo 778337 1169105 := bstep (se 2 (by rfl) ⟨438414, by rfl⟩ : syracuseStep 1169105 = 876829) B876829
theorem B1169123 : Blo 778337 1169123 := bstep (se 1 (by rfl) ⟨876842, by rfl⟩ : syracuseStep 1169123 = 1753685) B1753685
theorem B2217709 : Blo 778337 2217709 := bstep (se 3 (by rfl) ⟨415820, by rfl⟩ : syracuseStep 2217709 = 831641) B831641
theorem B1169153 : Blo 778337 1169153 := bstep (se 2 (by rfl) ⟨438432, by rfl⟩ : syracuseStep 1169153 = 876865) B876865
theorem B1169171 : Blo 778337 1169171 := bstep (se 1 (by rfl) ⟨876878, by rfl⟩ : syracuseStep 1169171 = 1753757) B1753757
theorem B1169201 : Blo 778337 1169201 := bstep (se 2 (by rfl) ⟨438450, by rfl⟩ : syracuseStep 1169201 = 876901) B876901
theorem B1169219 : Blo 778337 1169219 := bstep (se 1 (by rfl) ⟨876914, by rfl⟩ : syracuseStep 1169219 = 1753829) B1753829
theorem B1169249 : Blo 778337 1169249 := bstep (se 2 (by rfl) ⟨438468, by rfl⟩ : syracuseStep 1169249 = 876937) B876937
theorem B1169267 : Blo 778337 1169267 := bstep (se 1 (by rfl) ⟨876950, by rfl⟩ : syracuseStep 1169267 = 1753901) B1753901
theorem B1169297 : Blo 778337 1169297 := bstep (se 2 (by rfl) ⟨438486, by rfl⟩ : syracuseStep 1169297 = 876973) B876973
theorem B1759121 : Blo 778337 1759121 := bstep (se 2 (by rfl) ⟨659670, by rfl⟩ : syracuseStep 1759121 = 1319341) B1319341
theorem B1169315 : Blo 778337 1169315 := bstep (se 1 (by rfl) ⟨876986, by rfl⟩ : syracuseStep 1169315 = 1753973) B1753973
theorem B1759139 : Blo 778337 1759139 := bstep (se 1 (by rfl) ⟨1319354, by rfl⟩ : syracuseStep 1759139 = 2638709) B2638709
theorem B1169345 : Blo 778337 1169345 := bstep (se 2 (by rfl) ⟨438504, by rfl⟩ : syracuseStep 1169345 = 877009) B877009
theorem B2217937 : Blo 778337 2217937 := bstep (se 2 (by rfl) ⟨831726, by rfl⟩ : syracuseStep 2217937 = 1663453) B1663453
theorem B1169363 : Blo 778337 1169363 := bstep (se 1 (by rfl) ⟨877022, by rfl⟩ : syracuseStep 1169363 = 1754045) B1754045
theorem B4741105 : Blo 778337 4741105 := bstep (se 2 (by rfl) ⟨1777914, by rfl⟩ : syracuseStep 4741105 = 3555829) B3555829
theorem B1169393 : Blo 778337 1169393 := bstep (se 2 (by rfl) ⟨438522, by rfl⟩ : syracuseStep 1169393 = 877045) B877045
theorem B1169411 : Blo 778337 1169411 := bstep (se 1 (by rfl) ⟨877058, by rfl⟩ : syracuseStep 1169411 = 1754117) B1754117
theorem B1169441 : Blo 778337 1169441 := bstep (se 2 (by rfl) ⟨438540, by rfl⟩ : syracuseStep 1169441 = 877081) B877081
theorem B3004465 : Blo 778337 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1169459 : Blo 778337 1169459 := bstep (se 1 (by rfl) ⟨877094, by rfl⟩ : syracuseStep 1169459 = 1754189) B1754189
theorem B1169489 : Blo 778337 1169489 := bstep (se 2 (by rfl) ⟨438558, by rfl⟩ : syracuseStep 1169489 = 877117) B877117
theorem B1169507 : Blo 778337 1169507 := bstep (se 1 (by rfl) ⟨877130, by rfl⟩ : syracuseStep 1169507 = 1754261) B1754261
theorem B2218097 : Blo 778337 2218097 := bstep (se 2 (by rfl) ⟨831786, by rfl⟩ : syracuseStep 2218097 = 1663573) B1663573
theorem B1169537 : Blo 778337 1169537 := bstep (se 2 (by rfl) ⟨438576, by rfl⟩ : syracuseStep 1169537 = 877153) B877153
theorem B1169555 : Blo 778337 1169555 := bstep (se 1 (by rfl) ⟨877166, by rfl⟩ : syracuseStep 1169555 = 1754333) B1754333
theorem B1169585 : Blo 778337 1169585 := bstep (se 2 (by rfl) ⟨438594, by rfl⟩ : syracuseStep 1169585 = 877189) B877189
theorem B1759409 : Blo 778337 1759409 := bstep (se 2 (by rfl) ⟨659778, by rfl⟩ : syracuseStep 1759409 = 1319557) B1319557
theorem B1169603 : Blo 778337 1169603 := bstep (se 1 (by rfl) ⟨877202, by rfl⟩ : syracuseStep 1169603 = 1754405) B1754405
theorem B1759427 : Blo 778337 1759427 := bstep (se 1 (by rfl) ⟨1319570, by rfl⟩ : syracuseStep 1759427 = 2639141) B2639141
theorem B4741325 : Blo 778337 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B1169633 : Blo 778337 1169633 := bstep (se 2 (by rfl) ⟨438612, by rfl⟩ : syracuseStep 1169633 = 877225) B877225
theorem B2218211 : Blo 778337 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B1169651 : Blo 778337 1169651 := bstep (se 1 (by rfl) ⟨877238, by rfl⟩ : syracuseStep 1169651 = 1754477) B1754477
theorem B1169681 : Blo 778337 1169681 := bstep (se 2 (by rfl) ⟨438630, by rfl⟩ : syracuseStep 1169681 = 877261) B877261
theorem B1169699 : Blo 778337 1169699 := bstep (se 1 (by rfl) ⟨877274, by rfl⟩ : syracuseStep 1169699 = 1754549) B1754549
theorem B1169729 : Blo 778337 1169729 := bstep (se 2 (by rfl) ⟨438648, by rfl⟩ : syracuseStep 1169729 = 877297) B877297
theorem B1169747 : Blo 778337 1169747 := bstep (se 1 (by rfl) ⟨877310, by rfl⟩ : syracuseStep 1169747 = 1754621) B1754621
theorem B1169777 : Blo 778337 1169777 := bstep (se 2 (by rfl) ⟨438666, by rfl⟩ : syracuseStep 1169777 = 877333) B877333
theorem B1169795 : Blo 778337 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B1169825 : Blo 778337 1169825 := bstep (se 2 (by rfl) ⟨438684, by rfl⟩ : syracuseStep 1169825 = 877369) B877369
theorem B1169843 : Blo 778337 1169843 := bstep (se 1 (by rfl) ⟨877382, by rfl⟩ : syracuseStep 1169843 = 1754765) B1754765
theorem B1169873 : Blo 778337 1169873 := bstep (se 2 (by rfl) ⟨438702, by rfl⟩ : syracuseStep 1169873 = 877405) B877405
theorem B1759697 : Blo 778337 1759697 := bstep (se 2 (by rfl) ⟨659886, by rfl⟩ : syracuseStep 1759697 = 1319773) B1319773
theorem B1169891 : Blo 778337 1169891 := bstep (se 1 (by rfl) ⟨877418, by rfl⟩ : syracuseStep 1169891 = 1754837) B1754837
theorem B1759715 : Blo 778337 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B1169921 : Blo 778337 1169921 := bstep (se 2 (by rfl) ⟨438720, by rfl⟩ : syracuseStep 1169921 = 877441) B877441
theorem B1169939 : Blo 778337 1169939 := bstep (se 1 (by rfl) ⟨877454, by rfl⟩ : syracuseStep 1169939 = 1754909) B1754909
theorem B1169969 : Blo 778337 1169969 := bstep (se 2 (by rfl) ⟨438738, by rfl⟩ : syracuseStep 1169969 = 877477) B877477
theorem B1169987 : Blo 778337 1169987 := bstep (se 1 (by rfl) ⟨877490, by rfl⟩ : syracuseStep 1169987 = 1754981) B1754981
theorem B3758669 : Blo 778337 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1170017 : Blo 778337 1170017 := bstep (se 2 (by rfl) ⟨438756, by rfl⟩ : syracuseStep 1170017 = 877513) B877513
theorem B1170035 : Blo 778337 1170035 := bstep (se 1 (by rfl) ⟨877526, by rfl⟩ : syracuseStep 1170035 = 1755053) B1755053
theorem B1170065 : Blo 778337 1170065 := bstep (se 2 (by rfl) ⟨438774, by rfl⟩ : syracuseStep 1170065 = 877549) B877549
theorem B1170083 : Blo 778337 1170083 := bstep (se 1 (by rfl) ⟨877562, by rfl⟩ : syracuseStep 1170083 = 1755125) B1755125
theorem B1170113 : Blo 778337 1170113 := bstep (se 2 (by rfl) ⟨438792, by rfl⟩ : syracuseStep 1170113 = 877585) B877585
theorem B1170131 : Blo 778337 1170131 := bstep (se 1 (by rfl) ⟨877598, by rfl⟩ : syracuseStep 1170131 = 1755197) B1755197
theorem B1170161 : Blo 778337 1170161 := bstep (se 2 (by rfl) ⟨438810, by rfl⟩ : syracuseStep 1170161 = 877621) B877621
theorem B1759985 : Blo 778337 1759985 := bstep (se 2 (by rfl) ⟨659994, by rfl⟩ : syracuseStep 1759985 = 1319989) B1319989
theorem B1170179 : Blo 778337 1170179 := bstep (se 1 (by rfl) ⟨877634, by rfl⟩ : syracuseStep 1170179 = 1755269) B1755269
theorem B1760003 : Blo 778337 1760003 := bstep (se 1 (by rfl) ⟨1320002, by rfl⟩ : syracuseStep 1760003 = 2640005) B2640005
theorem B1170209 : Blo 778337 1170209 := bstep (se 2 (by rfl) ⟨438828, by rfl⟩ : syracuseStep 1170209 = 877657) B877657
theorem B1170227 : Blo 778337 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B1170257 : Blo 778337 1170257 := bstep (se 2 (by rfl) ⟨438846, by rfl⟩ : syracuseStep 1170257 = 877693) B877693
theorem B1170275 : Blo 778337 1170275 := bstep (se 1 (by rfl) ⟨877706, by rfl⟩ : syracuseStep 1170275 = 1755413) B1755413
theorem B1170305 : Blo 778337 1170305 := bstep (se 2 (by rfl) ⟨438864, by rfl⟩ : syracuseStep 1170305 = 877729) B877729
theorem B18963341 : Blo 778337 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B22502285 : Blo 778337 22502285 := bstep (se 3 (by rfl) ⟨4219178, by rfl⟩ : syracuseStep 22502285 = 8438357) B8438357
theorem B1170323 : Blo 778337 1170323 := bstep (se 1 (by rfl) ⟨877742, by rfl⟩ : syracuseStep 1170323 = 1755485) B1755485
theorem B1170353 : Blo 778337 1170353 := bstep (se 2 (by rfl) ⟨438882, by rfl⟩ : syracuseStep 1170353 = 877765) B877765
theorem B1170371 : Blo 778337 1170371 := bstep (se 1 (by rfl) ⟨877778, by rfl⟩ : syracuseStep 1170371 = 1755557) B1755557
theorem B1334225 : Blo 778337 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B1170401 : Blo 778337 1170401 := bstep (se 2 (by rfl) ⟨438900, by rfl⟩ : syracuseStep 1170401 = 877801) B877801
theorem B1170419 : Blo 778337 1170419 := bstep (se 1 (by rfl) ⟨877814, by rfl⟩ : syracuseStep 1170419 = 1755629) B1755629
theorem B5004301 : Blo 778337 5004301 := bstep (se 3 (by rfl) ⟨938306, by rfl⟩ : syracuseStep 5004301 = 1876613) B1876613
theorem B1170449 : Blo 778337 1170449 := bstep (se 2 (by rfl) ⟨438918, by rfl⟩ : syracuseStep 1170449 = 877837) B877837
theorem B1170467 : Blo 778337 1170467 := bstep (se 1 (by rfl) ⟨877850, by rfl⟩ : syracuseStep 1170467 = 1755701) B1755701
theorem B1170497 : Blo 778337 1170497 := bstep (se 2 (by rfl) ⟨438936, by rfl⟩ : syracuseStep 1170497 = 877873) B877873
theorem B1170515 : Blo 778337 1170515 := bstep (se 1 (by rfl) ⟨877886, by rfl⟩ : syracuseStep 1170515 = 1755773) B1755773
theorem B1170545 : Blo 778337 1170545 := bstep (se 2 (by rfl) ⟨438954, by rfl⟩ : syracuseStep 1170545 = 877909) B877909
theorem B1170563 : Blo 778337 1170563 := bstep (se 1 (by rfl) ⟨877922, by rfl⟩ : syracuseStep 1170563 = 1755845) B1755845
theorem B1170593 : Blo 778337 1170593 := bstep (se 2 (by rfl) ⟨438972, by rfl⟩ : syracuseStep 1170593 = 877945) B877945
theorem B1170611 : Blo 778337 1170611 := bstep (se 1 (by rfl) ⟨877958, by rfl⟩ : syracuseStep 1170611 = 1755917) B1755917
theorem B2219213 : Blo 778337 2219213 := bstep (se 3 (by rfl) ⟨416102, by rfl⟩ : syracuseStep 2219213 = 832205) B832205
theorem B1170641 : Blo 778337 1170641 := bstep (se 2 (by rfl) ⟨438990, by rfl⟩ : syracuseStep 1170641 = 877981) B877981
theorem B875731 : Blo 778337 875731 := bstep (se 1 (by rfl) ⟨656798, by rfl⟩ : syracuseStep 875731 = 1313597) B1313597
theorem B1170659 : Blo 778337 1170659 := bstep (se 1 (by rfl) ⟨877994, by rfl⟩ : syracuseStep 1170659 = 1755989) B1755989
theorem B1170689 : Blo 778337 1170689 := bstep (se 2 (by rfl) ⟨439008, by rfl⟩ : syracuseStep 1170689 = 878017) B878017
theorem B4447493 : Blo 778337 4447493 := bstep (se 4 (by rfl) ⟨416952, by rfl⟩ : syracuseStep 4447493 = 833905) B833905
theorem B1170707 : Blo 778337 1170707 := bstep (se 1 (by rfl) ⟨878030, by rfl⟩ : syracuseStep 1170707 = 1756061) B1756061
theorem B1170737 : Blo 778337 1170737 := bstep (se 2 (by rfl) ⟨439026, by rfl⟩ : syracuseStep 1170737 = 878053) B878053
theorem B1170755 : Blo 778337 1170755 := bstep (se 1 (by rfl) ⟨878066, by rfl⟩ : syracuseStep 1170755 = 1756133) B1756133
theorem B8904005 : Blo 778337 8904005 := bstep (se 4 (by rfl) ⟨834750, by rfl⟩ : syracuseStep 8904005 = 1669501) B1669501
theorem B5332301 : Blo 778337 5332301 := bstep (se 3 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 5332301 = 1999613) B1999613
theorem B1170785 : Blo 778337 1170785 := bstep (se 2 (by rfl) ⟨439044, by rfl⟩ : syracuseStep 1170785 = 878089) B878089
theorem B875875 : Blo 778337 875875 := bstep (se 1 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 875875 = 1313813) B1313813
theorem B1170803 : Blo 778337 1170803 := bstep (se 1 (by rfl) ⟨878102, by rfl⟩ : syracuseStep 1170803 = 1756205) B1756205
theorem B2219395 : Blo 778337 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B1170833 : Blo 778337 1170833 := bstep (se 2 (by rfl) ⟨439062, by rfl⟩ : syracuseStep 1170833 = 878125) B878125
theorem B1170851 : Blo 778337 1170851 := bstep (se 1 (by rfl) ⟨878138, by rfl⟩ : syracuseStep 1170851 = 1756277) B1756277
theorem B1170881 : Blo 778337 1170881 := bstep (se 2 (by rfl) ⟨439080, by rfl⟩ : syracuseStep 1170881 = 878161) B878161
theorem B1170899 : Blo 778337 1170899 := bstep (se 1 (by rfl) ⟨878174, by rfl⟩ : syracuseStep 1170899 = 1756349) B1756349
theorem B1170929 : Blo 778337 1170929 := bstep (se 2 (by rfl) ⟨439098, by rfl⟩ : syracuseStep 1170929 = 878197) B878197
theorem B876019 : Blo 778337 876019 := bstep (se 1 (by rfl) ⟨657014, by rfl⟩ : syracuseStep 876019 = 1314029) B1314029
theorem B1170947 : Blo 778337 1170947 := bstep (se 1 (by rfl) ⟨878210, by rfl⟩ : syracuseStep 1170947 = 1756421) B1756421
theorem B1170977 : Blo 778337 1170977 := bstep (se 2 (by rfl) ⟨439116, by rfl⟩ : syracuseStep 1170977 = 878233) B878233
theorem B2219555 : Blo 778337 2219555 := bstep (se 1 (by rfl) ⟨1664666, by rfl⟩ : syracuseStep 2219555 = 3329333) B3329333
theorem B1170995 : Blo 778337 1170995 := bstep (se 1 (by rfl) ⟨878246, by rfl⟩ : syracuseStep 1170995 = 1756493) B1756493
theorem B1171025 : Blo 778337 1171025 := bstep (se 2 (by rfl) ⟨439134, by rfl⟩ : syracuseStep 1171025 = 878269) B878269
theorem B1171043 : Blo 778337 1171043 := bstep (se 1 (by rfl) ⟨878282, by rfl⟩ : syracuseStep 1171043 = 1756565) B1756565
theorem B1171073 : Blo 778337 1171073 := bstep (se 2 (by rfl) ⟨439152, by rfl⟩ : syracuseStep 1171073 = 878305) B878305
theorem B876163 : Blo 778337 876163 := bstep (se 1 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 876163 = 1314245) B1314245
theorem B1171091 : Blo 778337 1171091 := bstep (se 1 (by rfl) ⟨878318, by rfl⟩ : syracuseStep 1171091 = 1756637) B1756637
theorem B1171121 : Blo 778337 1171121 := bstep (se 2 (by rfl) ⟨439170, by rfl⟩ : syracuseStep 1171121 = 878341) B878341
theorem B1171139 : Blo 778337 1171139 := bstep (se 1 (by rfl) ⟨878354, by rfl⟩ : syracuseStep 1171139 = 1756709) B1756709
theorem B1171169 : Blo 778337 1171169 := bstep (se 2 (by rfl) ⟨439188, by rfl⟩ : syracuseStep 1171169 = 878377) B878377
theorem B1171187 : Blo 778337 1171187 := bstep (se 1 (by rfl) ⟨878390, by rfl⟩ : syracuseStep 1171187 = 1756781) B1756781
theorem B1171217 : Blo 778337 1171217 := bstep (se 2 (by rfl) ⟨439206, by rfl⟩ : syracuseStep 1171217 = 878413) B878413
theorem B876307 : Blo 778337 876307 := bstep (se 1 (by rfl) ⟨657230, by rfl⟩ : syracuseStep 876307 = 1314461) B1314461
theorem B1335059 : Blo 778337 1335059 := bstep (se 1 (by rfl) ⟨1001294, by rfl⟩ : syracuseStep 1335059 = 2002589) B2002589
theorem B1171235 : Blo 778337 1171235 := bstep (se 1 (by rfl) ⟨878426, by rfl⟩ : syracuseStep 1171235 = 1756853) B1756853
theorem B1171265 : Blo 778337 1171265 := bstep (se 2 (by rfl) ⟨439224, by rfl⟩ : syracuseStep 1171265 = 878449) B878449
theorem B1171283 : Blo 778337 1171283 := bstep (se 1 (by rfl) ⟨878462, by rfl⟩ : syracuseStep 1171283 = 1756925) B1756925
theorem B1171313 : Blo 778337 1171313 := bstep (se 2 (by rfl) ⟨439242, by rfl⟩ : syracuseStep 1171313 = 878485) B878485
theorem B1171331 : Blo 778337 1171331 := bstep (se 1 (by rfl) ⟨878498, by rfl⟩ : syracuseStep 1171331 = 1756997) B1756997
theorem B1171361 : Blo 778337 1171361 := bstep (se 2 (by rfl) ⟨439260, by rfl⟩ : syracuseStep 1171361 = 878521) B878521
theorem B876451 : Blo 778337 876451 := bstep (se 1 (by rfl) ⟨657338, by rfl⟩ : syracuseStep 876451 = 1314677) B1314677
theorem B1171379 : Blo 778337 1171379 := bstep (se 1 (by rfl) ⟨878534, by rfl⟩ : syracuseStep 1171379 = 1757069) B1757069
theorem B1171409 : Blo 778337 1171409 := bstep (se 2 (by rfl) ⟨439278, by rfl⟩ : syracuseStep 1171409 = 878557) B878557
theorem B1171427 : Blo 778337 1171427 := bstep (se 1 (by rfl) ⟨878570, by rfl⟩ : syracuseStep 1171427 = 1757141) B1757141
theorem B4513763 : Blo 778337 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B1171457 : Blo 778337 1171457 := bstep (se 2 (by rfl) ⟨439296, by rfl⟩ : syracuseStep 1171457 = 878593) B878593
theorem B1171475 : Blo 778337 1171475 := bstep (se 1 (by rfl) ⟨878606, by rfl⟩ : syracuseStep 1171475 = 1757213) B1757213
theorem B1171505 : Blo 778337 1171505 := bstep (se 2 (by rfl) ⟨439314, by rfl⟩ : syracuseStep 1171505 = 878629) B878629
theorem B876595 : Blo 778337 876595 := bstep (se 1 (by rfl) ⟨657446, by rfl⟩ : syracuseStep 876595 = 1314893) B1314893
theorem B1171523 : Blo 778337 1171523 := bstep (se 1 (by rfl) ⟨878642, by rfl⟩ : syracuseStep 1171523 = 1757285) B1757285
theorem B1171553 : Blo 778337 1171553 := bstep (se 2 (by rfl) ⟨439332, by rfl⟩ : syracuseStep 1171553 = 878665) B878665
theorem B778339 : Blo 778337 778339 := bstep (se 1 (by rfl) ⟨583754, by rfl⟩ : syracuseStep 778339 = 1167509) B1167509
theorem B3956849 : Blo 778337 3956849 := bstep (se 2 (by rfl) ⟨1483818, by rfl⟩ : syracuseStep 3956849 = 2967637) B2967637
theorem B778355 : Blo 778337 778355 := bstep (se 1 (by rfl) ⟨583766, by rfl⟩ : syracuseStep 778355 = 1167533) B1167533
theorem B1171571 : Blo 778337 1171571 := bstep (se 1 (by rfl) ⟨878678, by rfl⟩ : syracuseStep 1171571 = 1757357) B1757357
theorem B778371 : Blo 778337 778371 := bstep (se 1 (by rfl) ⟨583778, by rfl⟩ : syracuseStep 778371 = 1167557) B1167557
theorem B1171601 : Blo 778337 1171601 := bstep (se 2 (by rfl) ⟨439350, by rfl⟩ : syracuseStep 1171601 = 878701) B878701
theorem B778387 : Blo 778337 778387 := bstep (se 1 (by rfl) ⟨583790, by rfl⟩ : syracuseStep 778387 = 1167581) B1167581
theorem B778403 : Blo 778337 778403 := bstep (se 1 (by rfl) ⟨583802, by rfl⟩ : syracuseStep 778403 = 1167605) B1167605
theorem B1171619 : Blo 778337 1171619 := bstep (se 1 (by rfl) ⟨878714, by rfl⟩ : syracuseStep 1171619 = 1757429) B1757429
theorem B778419 : Blo 778337 778419 := bstep (se 1 (by rfl) ⟨583814, by rfl⟩ : syracuseStep 778419 = 1167629) B1167629
theorem B1171649 : Blo 778337 1171649 := bstep (se 2 (by rfl) ⟨439368, by rfl⟩ : syracuseStep 1171649 = 878737) B878737
theorem B778435 : Blo 778337 778435 := bstep (se 1 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 778435 = 1167653) B1167653
theorem B876739 : Blo 778337 876739 := bstep (se 1 (by rfl) ⟨657554, by rfl⟩ : syracuseStep 876739 = 1315109) B1315109
theorem B778451 : Blo 778337 778451 := bstep (se 1 (by rfl) ⟨583838, by rfl⟩ : syracuseStep 778451 = 1167677) B1167677
theorem B1171667 : Blo 778337 1171667 := bstep (se 1 (by rfl) ⟨878750, by rfl⟩ : syracuseStep 1171667 = 1757501) B1757501
theorem B778467 : Blo 778337 778467 := bstep (se 1 (by rfl) ⟨583850, by rfl⟩ : syracuseStep 778467 = 1167701) B1167701
theorem B1171697 : Blo 778337 1171697 := bstep (se 2 (by rfl) ⟨439386, by rfl⟩ : syracuseStep 1171697 = 878773) B878773
theorem B778483 : Blo 778337 778483 := bstep (se 1 (by rfl) ⟨583862, by rfl⟩ : syracuseStep 778483 = 1167725) B1167725
theorem B778499 : Blo 778337 778499 := bstep (se 1 (by rfl) ⟨583874, by rfl⟩ : syracuseStep 778499 = 1167749) B1167749
theorem B1171715 : Blo 778337 1171715 := bstep (se 1 (by rfl) ⟨878786, by rfl⟩ : syracuseStep 1171715 = 1757573) B1757573
theorem B778515 : Blo 778337 778515 := bstep (se 1 (by rfl) ⟨583886, by rfl⟩ : syracuseStep 778515 = 1167773) B1167773
theorem B1171745 : Blo 778337 1171745 := bstep (se 2 (by rfl) ⟨439404, by rfl⟩ : syracuseStep 1171745 = 878809) B878809
theorem B778531 : Blo 778337 778531 := bstep (se 1 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 778531 = 1167797) B1167797
theorem B778547 : Blo 778337 778547 := bstep (se 1 (by rfl) ⟨583910, by rfl⟩ : syracuseStep 778547 = 1167821) B1167821
theorem B1171763 : Blo 778337 1171763 := bstep (se 1 (by rfl) ⟨878822, by rfl⟩ : syracuseStep 1171763 = 1757645) B1757645
theorem B778563 : Blo 778337 778563 := bstep (se 1 (by rfl) ⟨583922, by rfl⟩ : syracuseStep 778563 = 1167845) B1167845
theorem B1171793 : Blo 778337 1171793 := bstep (se 2 (by rfl) ⟨439422, by rfl⟩ : syracuseStep 1171793 = 878845) B878845
theorem B778579 : Blo 778337 778579 := bstep (se 1 (by rfl) ⟨583934, by rfl⟩ : syracuseStep 778579 = 1167869) B1167869
theorem B876883 : Blo 778337 876883 := bstep (se 1 (by rfl) ⟨657662, by rfl⟩ : syracuseStep 876883 = 1315325) B1315325
theorem B778595 : Blo 778337 778595 := bstep (se 1 (by rfl) ⟨583946, by rfl⟩ : syracuseStep 778595 = 1167893) B1167893
theorem B1171811 : Blo 778337 1171811 := bstep (se 1 (by rfl) ⟨878858, by rfl⟩ : syracuseStep 1171811 = 1757717) B1757717
theorem B778611 : Blo 778337 778611 := bstep (se 1 (by rfl) ⟨583958, by rfl⟩ : syracuseStep 778611 = 1167917) B1167917
theorem B1171841 : Blo 778337 1171841 := bstep (se 2 (by rfl) ⟨439440, by rfl⟩ : syracuseStep 1171841 = 878881) B878881
theorem B778627 : Blo 778337 778627 := bstep (se 1 (by rfl) ⟨583970, by rfl⟩ : syracuseStep 778627 = 1167941) B1167941
theorem B778643 : Blo 778337 778643 := bstep (se 1 (by rfl) ⟨583982, by rfl⟩ : syracuseStep 778643 = 1167965) B1167965
theorem B1171859 : Blo 778337 1171859 := bstep (se 1 (by rfl) ⟨878894, by rfl⟩ : syracuseStep 1171859 = 1757789) B1757789
theorem B778659 : Blo 778337 778659 := bstep (se 1 (by rfl) ⟨583994, by rfl⟩ : syracuseStep 778659 = 1167989) B1167989
theorem B1171889 : Blo 778337 1171889 := bstep (se 2 (by rfl) ⟨439458, by rfl⟩ : syracuseStep 1171889 = 878917) B878917
theorem B778675 : Blo 778337 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B778691 : Blo 778337 778691 := bstep (se 1 (by rfl) ⟨584018, by rfl⟩ : syracuseStep 778691 = 1168037) B1168037
theorem B1171907 : Blo 778337 1171907 := bstep (se 1 (by rfl) ⟨878930, by rfl⟩ : syracuseStep 1171907 = 1757861) B1757861
theorem B778707 : Blo 778337 778707 := bstep (se 1 (by rfl) ⟨584030, by rfl⟩ : syracuseStep 778707 = 1168061) B1168061
theorem B1171937 : Blo 778337 1171937 := bstep (se 2 (by rfl) ⟨439476, by rfl⟩ : syracuseStep 1171937 = 878953) B878953
theorem B778723 : Blo 778337 778723 := bstep (se 1 (by rfl) ⟨584042, by rfl⟩ : syracuseStep 778723 = 1168085) B1168085
theorem B877027 : Blo 778337 877027 := bstep (se 1 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 877027 = 1315541) B1315541
theorem B778739 : Blo 778337 778739 := bstep (se 1 (by rfl) ⟨584054, by rfl⟩ : syracuseStep 778739 = 1168109) B1168109
theorem B1171955 : Blo 778337 1171955 := bstep (se 1 (by rfl) ⟨878966, by rfl⟩ : syracuseStep 1171955 = 1757933) B1757933
theorem B778755 : Blo 778337 778755 := bstep (se 1 (by rfl) ⟨584066, by rfl⟩ : syracuseStep 778755 = 1168133) B1168133
theorem B1171985 : Blo 778337 1171985 := bstep (se 2 (by rfl) ⟨439494, by rfl⟩ : syracuseStep 1171985 = 878989) B878989
theorem B778771 : Blo 778337 778771 := bstep (se 1 (by rfl) ⟨584078, by rfl⟩ : syracuseStep 778771 = 1168157) B1168157
theorem B778787 : Blo 778337 778787 := bstep (se 1 (by rfl) ⟨584090, by rfl⟩ : syracuseStep 778787 = 1168181) B1168181
theorem B1172003 : Blo 778337 1172003 := bstep (se 1 (by rfl) ⟨879002, by rfl⟩ : syracuseStep 1172003 = 1758005) B1758005
theorem B778803 : Blo 778337 778803 := bstep (se 1 (by rfl) ⟨584102, by rfl⟩ : syracuseStep 778803 = 1168205) B1168205
theorem B1172033 : Blo 778337 1172033 := bstep (se 2 (by rfl) ⟨439512, by rfl⟩ : syracuseStep 1172033 = 879025) B879025
theorem B778819 : Blo 778337 778819 := bstep (se 1 (by rfl) ⟨584114, by rfl⟩ : syracuseStep 778819 = 1168229) B1168229
theorem B2220625 : Blo 778337 2220625 := bstep (se 2 (by rfl) ⟨832734, by rfl⟩ : syracuseStep 2220625 = 1665469) B1665469
theorem B778835 : Blo 778337 778835 := bstep (se 1 (by rfl) ⟨584126, by rfl⟩ : syracuseStep 778835 = 1168253) B1168253
theorem B1172051 : Blo 778337 1172051 := bstep (se 1 (by rfl) ⟨879038, by rfl⟩ : syracuseStep 1172051 = 1758077) B1758077
theorem B778851 : Blo 778337 778851 := bstep (se 1 (by rfl) ⟨584138, by rfl⟩ : syracuseStep 778851 = 1168277) B1168277
theorem B1172081 : Blo 778337 1172081 := bstep (se 2 (by rfl) ⟨439530, by rfl⟩ : syracuseStep 1172081 = 879061) B879061
theorem B778867 : Blo 778337 778867 := bstep (se 1 (by rfl) ⟨584150, by rfl⟩ : syracuseStep 778867 = 1168301) B1168301
theorem B877171 : Blo 778337 877171 := bstep (se 1 (by rfl) ⟨657878, by rfl⟩ : syracuseStep 877171 = 1315757) B1315757
theorem B778883 : Blo 778337 778883 := bstep (se 1 (by rfl) ⟨584162, by rfl⟩ : syracuseStep 778883 = 1168325) B1168325
theorem B1172099 : Blo 778337 1172099 := bstep (se 1 (by rfl) ⟨879074, by rfl⟩ : syracuseStep 1172099 = 1758149) B1758149
theorem B11231885 : Blo 778337 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B778899 : Blo 778337 778899 := bstep (se 1 (by rfl) ⟨584174, by rfl⟩ : syracuseStep 778899 = 1168349) B1168349
theorem B1172129 : Blo 778337 1172129 := bstep (se 2 (by rfl) ⟨439548, by rfl⟩ : syracuseStep 1172129 = 879097) B879097
theorem B778915 : Blo 778337 778915 := bstep (se 1 (by rfl) ⟨584186, by rfl⟩ : syracuseStep 778915 = 1168373) B1168373
theorem B778931 : Blo 778337 778931 := bstep (se 1 (by rfl) ⟨584198, by rfl⟩ : syracuseStep 778931 = 1168397) B1168397
theorem B1172147 : Blo 778337 1172147 := bstep (se 1 (by rfl) ⟨879110, by rfl⟩ : syracuseStep 1172147 = 1758221) B1758221
theorem B778947 : Blo 778337 778947 := bstep (se 1 (by rfl) ⟨584210, by rfl⟩ : syracuseStep 778947 = 1168421) B1168421
theorem B1172177 : Blo 778337 1172177 := bstep (se 2 (by rfl) ⟨439566, by rfl⟩ : syracuseStep 1172177 = 879133) B879133
theorem B778963 : Blo 778337 778963 := bstep (se 1 (by rfl) ⟨584222, by rfl⟩ : syracuseStep 778963 = 1168445) B1168445
theorem B778979 : Blo 778337 778979 := bstep (se 1 (by rfl) ⟨584234, by rfl⟩ : syracuseStep 778979 = 1168469) B1168469
theorem B1172195 : Blo 778337 1172195 := bstep (se 1 (by rfl) ⟨879146, by rfl⟩ : syracuseStep 1172195 = 1758293) B1758293
theorem B4285169 : Blo 778337 4285169 := bstep (se 2 (by rfl) ⟨1606938, by rfl⟩ : syracuseStep 4285169 = 3213877) B3213877
theorem B778995 : Blo 778337 778995 := bstep (se 1 (by rfl) ⟨584246, by rfl⟩ : syracuseStep 778995 = 1168493) B1168493
theorem B1172225 : Blo 778337 1172225 := bstep (se 2 (by rfl) ⟨439584, by rfl⟩ : syracuseStep 1172225 = 879169) B879169
theorem B779011 : Blo 778337 779011 := bstep (se 1 (by rfl) ⟨584258, by rfl⟩ : syracuseStep 779011 = 1168517) B1168517
theorem B877315 : Blo 778337 877315 := bstep (se 1 (by rfl) ⟨657986, by rfl⟩ : syracuseStep 877315 = 1315973) B1315973
theorem B779027 : Blo 778337 779027 := bstep (se 1 (by rfl) ⟨584270, by rfl⟩ : syracuseStep 779027 = 1168541) B1168541
theorem B1172243 : Blo 778337 1172243 := bstep (se 1 (by rfl) ⟨879182, by rfl⟩ : syracuseStep 1172243 = 1758365) B1758365
theorem B779043 : Blo 778337 779043 := bstep (se 1 (by rfl) ⟨584282, by rfl⟩ : syracuseStep 779043 = 1168565) B1168565
theorem B1172273 : Blo 778337 1172273 := bstep (se 2 (by rfl) ⟨439602, by rfl⟩ : syracuseStep 1172273 = 879205) B879205
theorem B779059 : Blo 778337 779059 := bstep (se 1 (by rfl) ⟨584294, by rfl⟩ : syracuseStep 779059 = 1168589) B1168589
theorem B779075 : Blo 778337 779075 := bstep (se 1 (by rfl) ⟨584306, by rfl⟩ : syracuseStep 779075 = 1168613) B1168613
theorem B1172291 : Blo 778337 1172291 := bstep (se 1 (by rfl) ⟨879218, by rfl⟩ : syracuseStep 1172291 = 1758437) B1758437
theorem B779091 : Blo 778337 779091 := bstep (se 1 (by rfl) ⟨584318, by rfl⟩ : syracuseStep 779091 = 1168637) B1168637
theorem B1172321 : Blo 778337 1172321 := bstep (se 2 (by rfl) ⟨439620, by rfl⟩ : syracuseStep 1172321 = 879241) B879241
theorem B779107 : Blo 778337 779107 := bstep (se 1 (by rfl) ⟨584330, by rfl⟩ : syracuseStep 779107 = 1168661) B1168661
theorem B779123 : Blo 778337 779123 := bstep (se 1 (by rfl) ⟨584342, by rfl⟩ : syracuseStep 779123 = 1168685) B1168685
theorem B1172339 : Blo 778337 1172339 := bstep (se 1 (by rfl) ⟨879254, by rfl⟩ : syracuseStep 1172339 = 1758509) B1758509
theorem B779139 : Blo 778337 779139 := bstep (se 1 (by rfl) ⟨584354, by rfl⟩ : syracuseStep 779139 = 1168709) B1168709
theorem B1172369 : Blo 778337 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B779155 : Blo 778337 779155 := bstep (se 1 (by rfl) ⟨584366, by rfl⟩ : syracuseStep 779155 = 1168733) B1168733
theorem B877459 : Blo 778337 877459 := bstep (se 1 (by rfl) ⟨658094, by rfl⟩ : syracuseStep 877459 = 1316189) B1316189
theorem B779171 : Blo 778337 779171 := bstep (se 1 (by rfl) ⟨584378, by rfl⟩ : syracuseStep 779171 = 1168757) B1168757
theorem B1172387 : Blo 778337 1172387 := bstep (se 1 (by rfl) ⟨879290, by rfl⟩ : syracuseStep 1172387 = 1758581) B1758581
theorem B779187 : Blo 778337 779187 := bstep (se 1 (by rfl) ⟨584390, by rfl⟩ : syracuseStep 779187 = 1168781) B1168781
theorem B1172417 : Blo 778337 1172417 := bstep (se 2 (by rfl) ⟨439656, by rfl⟩ : syracuseStep 1172417 = 879313) B879313
theorem B779203 : Blo 778337 779203 := bstep (se 1 (by rfl) ⟨584402, by rfl⟩ : syracuseStep 779203 = 1168805) B1168805
theorem B779219 : Blo 778337 779219 := bstep (se 1 (by rfl) ⟨584414, by rfl⟩ : syracuseStep 779219 = 1168829) B1168829
theorem B1172435 : Blo 778337 1172435 := bstep (se 1 (by rfl) ⟨879326, by rfl⟩ : syracuseStep 1172435 = 1758653) B1758653
theorem B779235 : Blo 778337 779235 := bstep (se 1 (by rfl) ⟨584426, by rfl⟩ : syracuseStep 779235 = 1168853) B1168853
theorem B1172465 : Blo 778337 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B779251 : Blo 778337 779251 := bstep (se 1 (by rfl) ⟨584438, by rfl⟩ : syracuseStep 779251 = 1168877) B1168877
theorem B779267 : Blo 778337 779267 := bstep (se 1 (by rfl) ⟨584450, by rfl⟩ : syracuseStep 779267 = 1168901) B1168901
theorem B1172483 : Blo 778337 1172483 := bstep (se 1 (by rfl) ⟨879362, by rfl⟩ : syracuseStep 1172483 = 1758725) B1758725
theorem B5923853 : Blo 778337 5923853 := bstep (se 3 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 5923853 = 2221445) B2221445
theorem B779283 : Blo 778337 779283 := bstep (se 1 (by rfl) ⟨584462, by rfl⟩ : syracuseStep 779283 = 1168925) B1168925
theorem B1172513 : Blo 778337 1172513 := bstep (se 2 (by rfl) ⟨439692, by rfl⟩ : syracuseStep 1172513 = 879385) B879385
theorem B779299 : Blo 778337 779299 := bstep (se 1 (by rfl) ⟨584474, by rfl⟩ : syracuseStep 779299 = 1168949) B1168949
theorem B877603 : Blo 778337 877603 := bstep (se 1 (by rfl) ⟨658202, by rfl⟩ : syracuseStep 877603 = 1316405) B1316405
theorem B779315 : Blo 778337 779315 := bstep (se 1 (by rfl) ⟨584486, by rfl⟩ : syracuseStep 779315 = 1168973) B1168973
theorem B1172531 : Blo 778337 1172531 := bstep (se 1 (by rfl) ⟨879398, by rfl⟩ : syracuseStep 1172531 = 1758797) B1758797
theorem B779331 : Blo 778337 779331 := bstep (se 1 (by rfl) ⟨584498, by rfl⟩ : syracuseStep 779331 = 1168997) B1168997
theorem B1172561 : Blo 778337 1172561 := bstep (se 2 (by rfl) ⟨439710, by rfl⟩ : syracuseStep 1172561 = 879421) B879421
theorem B779347 : Blo 778337 779347 := bstep (se 1 (by rfl) ⟨584510, by rfl⟩ : syracuseStep 779347 = 1169021) B1169021
theorem B779363 : Blo 778337 779363 := bstep (se 1 (by rfl) ⟨584522, by rfl⟩ : syracuseStep 779363 = 1169045) B1169045
theorem B3564643 : Blo 778337 3564643 := bstep (se 1 (by rfl) ⟨2673482, by rfl⟩ : syracuseStep 3564643 = 5346965) B5346965
theorem B1172579 : Blo 778337 1172579 := bstep (se 1 (by rfl) ⟨879434, by rfl⟩ : syracuseStep 1172579 = 1758869) B1758869
theorem B779379 : Blo 778337 779379 := bstep (se 1 (by rfl) ⟨584534, by rfl⟩ : syracuseStep 779379 = 1169069) B1169069
theorem B1172609 : Blo 778337 1172609 := bstep (se 2 (by rfl) ⟨439728, by rfl⟩ : syracuseStep 1172609 = 879457) B879457
theorem B779395 : Blo 778337 779395 := bstep (se 1 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 779395 = 1169093) B1169093
theorem B4220045 : Blo 778337 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B779411 : Blo 778337 779411 := bstep (se 1 (by rfl) ⟨584558, by rfl⟩ : syracuseStep 779411 = 1169117) B1169117
theorem B1172627 : Blo 778337 1172627 := bstep (se 1 (by rfl) ⟨879470, by rfl⟩ : syracuseStep 1172627 = 1758941) B1758941
theorem B779427 : Blo 778337 779427 := bstep (se 1 (by rfl) ⟨584570, by rfl⟩ : syracuseStep 779427 = 1169141) B1169141
theorem B1172657 : Blo 778337 1172657 := bstep (se 2 (by rfl) ⟨439746, by rfl⟩ : syracuseStep 1172657 = 879493) B879493
theorem B779443 : Blo 778337 779443 := bstep (se 1 (by rfl) ⟨584582, by rfl⟩ : syracuseStep 779443 = 1169165) B1169165
theorem B877747 : Blo 778337 877747 := bstep (se 1 (by rfl) ⟨658310, by rfl⟩ : syracuseStep 877747 = 1316621) B1316621
theorem B779459 : Blo 778337 779459 := bstep (se 1 (by rfl) ⟨584594, by rfl⟩ : syracuseStep 779459 = 1169189) B1169189
theorem B1172675 : Blo 778337 1172675 := bstep (se 1 (by rfl) ⟨879506, by rfl⟩ : syracuseStep 1172675 = 1759013) B1759013
theorem B779475 : Blo 778337 779475 := bstep (se 1 (by rfl) ⟨584606, by rfl⟩ : syracuseStep 779475 = 1169213) B1169213
theorem B1172705 : Blo 778337 1172705 := bstep (se 2 (by rfl) ⟨439764, by rfl⟩ : syracuseStep 1172705 = 879529) B879529
theorem B779491 : Blo 778337 779491 := bstep (se 1 (by rfl) ⟨584618, by rfl⟩ : syracuseStep 779491 = 1169237) B1169237
theorem B779507 : Blo 778337 779507 := bstep (se 1 (by rfl) ⟨584630, by rfl⟩ : syracuseStep 779507 = 1169261) B1169261
theorem B1172723 : Blo 778337 1172723 := bstep (se 1 (by rfl) ⟨879542, by rfl⟩ : syracuseStep 1172723 = 1759085) B1759085
theorem B779523 : Blo 778337 779523 := bstep (se 1 (by rfl) ⟨584642, by rfl⟩ : syracuseStep 779523 = 1169285) B1169285
theorem B1664273 : Blo 778337 1664273 := bstep (se 2 (by rfl) ⟨624102, by rfl⟩ : syracuseStep 1664273 = 1248205) B1248205
theorem B1172753 : Blo 778337 1172753 := bstep (se 2 (by rfl) ⟨439782, by rfl⟩ : syracuseStep 1172753 = 879565) B879565
theorem B779539 : Blo 778337 779539 := bstep (se 1 (by rfl) ⟨584654, by rfl⟩ : syracuseStep 779539 = 1169309) B1169309
theorem B779555 : Blo 778337 779555 := bstep (se 1 (by rfl) ⟨584666, by rfl⟩ : syracuseStep 779555 = 1169333) B1169333
theorem B1172771 : Blo 778337 1172771 := bstep (se 1 (by rfl) ⟨879578, by rfl⟩ : syracuseStep 1172771 = 1759157) B1759157
theorem B779571 : Blo 778337 779571 := bstep (se 1 (by rfl) ⟨584678, by rfl⟩ : syracuseStep 779571 = 1169357) B1169357
theorem B1172801 : Blo 778337 1172801 := bstep (se 2 (by rfl) ⟨439800, by rfl⟩ : syracuseStep 1172801 = 879601) B879601
theorem B779587 : Blo 778337 779587 := bstep (se 1 (by rfl) ⟨584690, by rfl⟩ : syracuseStep 779587 = 1169381) B1169381
theorem B877891 : Blo 778337 877891 := bstep (se 1 (by rfl) ⟨658418, by rfl⟩ : syracuseStep 877891 = 1316837) B1316837
theorem B779603 : Blo 778337 779603 := bstep (se 1 (by rfl) ⟨584702, by rfl⟩ : syracuseStep 779603 = 1169405) B1169405
theorem B1172819 : Blo 778337 1172819 := bstep (se 1 (by rfl) ⟨879614, by rfl⟩ : syracuseStep 1172819 = 1759229) B1759229
theorem B779619 : Blo 778337 779619 := bstep (se 1 (by rfl) ⟨584714, by rfl⟩ : syracuseStep 779619 = 1169429) B1169429
theorem B1172849 : Blo 778337 1172849 := bstep (se 2 (by rfl) ⟨439818, by rfl⟩ : syracuseStep 1172849 = 879637) B879637
theorem B779635 : Blo 778337 779635 := bstep (se 1 (by rfl) ⟨584726, by rfl⟩ : syracuseStep 779635 = 1169453) B1169453
theorem B779651 : Blo 778337 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B1172867 : Blo 778337 1172867 := bstep (se 1 (by rfl) ⟨879650, by rfl⟩ : syracuseStep 1172867 = 1759301) B1759301
theorem B779667 : Blo 778337 779667 := bstep (se 1 (by rfl) ⟨584750, by rfl⟩ : syracuseStep 779667 = 1169501) B1169501
theorem B1172897 : Blo 778337 1172897 := bstep (se 2 (by rfl) ⟨439836, by rfl⟩ : syracuseStep 1172897 = 879673) B879673
theorem B779683 : Blo 778337 779683 := bstep (se 1 (by rfl) ⟨584762, by rfl⟩ : syracuseStep 779683 = 1169525) B1169525
theorem B779699 : Blo 778337 779699 := bstep (se 1 (by rfl) ⟨584774, by rfl⟩ : syracuseStep 779699 = 1169549) B1169549
theorem B1172915 : Blo 778337 1172915 := bstep (se 1 (by rfl) ⟨879686, by rfl⟩ : syracuseStep 1172915 = 1759373) B1759373
theorem B779715 : Blo 778337 779715 := bstep (se 1 (by rfl) ⟨584786, by rfl⟩ : syracuseStep 779715 = 1169573) B1169573
theorem B1172945 : Blo 778337 1172945 := bstep (se 2 (by rfl) ⟨439854, by rfl⟩ : syracuseStep 1172945 = 879709) B879709
theorem B779731 : Blo 778337 779731 := bstep (se 1 (by rfl) ⟨584798, by rfl⟩ : syracuseStep 779731 = 1169597) B1169597
theorem B878035 : Blo 778337 878035 := bstep (se 1 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 878035 = 1317053) B1317053
theorem B779747 : Blo 778337 779747 := bstep (se 1 (by rfl) ⟨584810, by rfl⟩ : syracuseStep 779747 = 1169621) B1169621
theorem B1172963 : Blo 778337 1172963 := bstep (se 1 (by rfl) ⟨879722, by rfl⟩ : syracuseStep 1172963 = 1759445) B1759445
theorem B779763 : Blo 778337 779763 := bstep (se 1 (by rfl) ⟨584822, by rfl⟩ : syracuseStep 779763 = 1169645) B1169645
theorem B1172993 : Blo 778337 1172993 := bstep (se 2 (by rfl) ⟨439872, by rfl⟩ : syracuseStep 1172993 = 879745) B879745
theorem B779779 : Blo 778337 779779 := bstep (se 1 (by rfl) ⟨584834, by rfl⟩ : syracuseStep 779779 = 1169669) B1169669
theorem B779795 : Blo 778337 779795 := bstep (se 1 (by rfl) ⟨584846, by rfl⟩ : syracuseStep 779795 = 1169693) B1169693
theorem B1173011 : Blo 778337 1173011 := bstep (se 1 (by rfl) ⟨879758, by rfl⟩ : syracuseStep 1173011 = 1759517) B1759517
theorem B779811 : Blo 778337 779811 := bstep (se 1 (by rfl) ⟨584858, by rfl⟩ : syracuseStep 779811 = 1169717) B1169717
theorem B3958307 : Blo 778337 3958307 := bstep (se 1 (by rfl) ⟨2968730, by rfl⟩ : syracuseStep 3958307 = 5937461) B5937461
theorem B1173041 : Blo 778337 1173041 := bstep (se 2 (by rfl) ⟨439890, by rfl⟩ : syracuseStep 1173041 = 879781) B879781
theorem B779827 : Blo 778337 779827 := bstep (se 1 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 779827 = 1169741) B1169741
theorem B779843 : Blo 778337 779843 := bstep (se 1 (by rfl) ⟨584882, by rfl⟩ : syracuseStep 779843 = 1169765) B1169765
theorem B1173059 : Blo 778337 1173059 := bstep (se 1 (by rfl) ⟨879794, by rfl⟩ : syracuseStep 1173059 = 1759589) B1759589
theorem B779859 : Blo 778337 779859 := bstep (se 1 (by rfl) ⟨584894, by rfl⟩ : syracuseStep 779859 = 1169789) B1169789
theorem B1173089 : Blo 778337 1173089 := bstep (se 2 (by rfl) ⟨439908, by rfl⟩ : syracuseStep 1173089 = 879817) B879817
theorem B779875 : Blo 778337 779875 := bstep (se 1 (by rfl) ⟨584906, by rfl⟩ : syracuseStep 779875 = 1169813) B1169813
theorem B878179 : Blo 778337 878179 := bstep (se 1 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 878179 = 1317269) B1317269
theorem B779891 : Blo 778337 779891 := bstep (se 1 (by rfl) ⟨584918, by rfl⟩ : syracuseStep 779891 = 1169837) B1169837
theorem B1173107 : Blo 778337 1173107 := bstep (se 1 (by rfl) ⟨879830, by rfl⟩ : syracuseStep 1173107 = 1759661) B1759661
theorem B779907 : Blo 778337 779907 := bstep (se 1 (by rfl) ⟨584930, by rfl⟩ : syracuseStep 779907 = 1169861) B1169861
theorem B1173137 : Blo 778337 1173137 := bstep (se 2 (by rfl) ⟨439926, by rfl⟩ : syracuseStep 1173137 = 879853) B879853
theorem B779923 : Blo 778337 779923 := bstep (se 1 (by rfl) ⟨584942, by rfl⟩ : syracuseStep 779923 = 1169885) B1169885
theorem B779939 : Blo 778337 779939 := bstep (se 1 (by rfl) ⟨584954, by rfl⟩ : syracuseStep 779939 = 1169909) B1169909
theorem B3335843 : Blo 778337 3335843 := bstep (se 1 (by rfl) ⟨2501882, by rfl⟩ : syracuseStep 3335843 = 5003765) B5003765
theorem B1173155 : Blo 778337 1173155 := bstep (se 1 (by rfl) ⟨879866, by rfl⟩ : syracuseStep 1173155 = 1759733) B1759733
theorem B779955 : Blo 778337 779955 := bstep (se 1 (by rfl) ⟨584966, by rfl⟩ : syracuseStep 779955 = 1169933) B1169933
theorem B1173185 : Blo 778337 1173185 := bstep (se 2 (by rfl) ⟨439944, by rfl⟩ : syracuseStep 1173185 = 879889) B879889
theorem B779971 : Blo 778337 779971 := bstep (se 1 (by rfl) ⟨584978, by rfl⟩ : syracuseStep 779971 = 1169957) B1169957
theorem B779987 : Blo 778337 779987 := bstep (se 1 (by rfl) ⟨584990, by rfl⟩ : syracuseStep 779987 = 1169981) B1169981
theorem B1173203 : Blo 778337 1173203 := bstep (se 1 (by rfl) ⟨879902, by rfl⟩ : syracuseStep 1173203 = 1759805) B1759805
theorem B780003 : Blo 778337 780003 := bstep (se 1 (by rfl) ⟨585002, by rfl⟩ : syracuseStep 780003 = 1170005) B1170005
theorem B1173233 : Blo 778337 1173233 := bstep (se 2 (by rfl) ⟨439962, by rfl⟩ : syracuseStep 1173233 = 879925) B879925
theorem B780019 : Blo 778337 780019 := bstep (se 1 (by rfl) ⟨585014, by rfl⟩ : syracuseStep 780019 = 1170029) B1170029
theorem B878323 : Blo 778337 878323 := bstep (se 1 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 878323 = 1317485) B1317485
theorem B780035 : Blo 778337 780035 := bstep (se 1 (by rfl) ⟨585026, by rfl⟩ : syracuseStep 780035 = 1170053) B1170053
theorem B1173251 : Blo 778337 1173251 := bstep (se 1 (by rfl) ⟨879938, by rfl⟩ : syracuseStep 1173251 = 1759877) B1759877
theorem B780051 : Blo 778337 780051 := bstep (se 1 (by rfl) ⟨585038, by rfl⟩ : syracuseStep 780051 = 1170077) B1170077
theorem B1173281 : Blo 778337 1173281 := bstep (se 2 (by rfl) ⟨439980, by rfl⟩ : syracuseStep 1173281 = 879961) B879961
theorem B1664803 : Blo 778337 1664803 := bstep (se 1 (by rfl) ⟨1248602, by rfl⟩ : syracuseStep 1664803 = 2497205) B2497205
theorem B780067 : Blo 778337 780067 := bstep (se 1 (by rfl) ⟨585050, by rfl⟩ : syracuseStep 780067 = 1170101) B1170101
theorem B780083 : Blo 778337 780083 := bstep (se 1 (by rfl) ⟨585062, by rfl⟩ : syracuseStep 780083 = 1170125) B1170125
theorem B1173299 : Blo 778337 1173299 := bstep (se 1 (by rfl) ⟨879974, by rfl⟩ : syracuseStep 1173299 = 1759949) B1759949
theorem B9987893 : Blo 778337 9987893 := bstep (se 5 (by rfl) ⟨468182, by rfl⟩ : syracuseStep 9987893 = 936365) B936365
theorem B780099 : Blo 778337 780099 := bstep (se 1 (by rfl) ⟨585074, by rfl⟩ : syracuseStep 780099 = 1170149) B1170149
theorem B2221901 : Blo 778337 2221901 := bstep (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) B833213
theorem B1173329 : Blo 778337 1173329 := bstep (se 2 (by rfl) ⟨439998, by rfl⟩ : syracuseStep 1173329 = 879997) B879997
theorem B780115 : Blo 778337 780115 := bstep (se 1 (by rfl) ⟨585086, by rfl⟩ : syracuseStep 780115 = 1170173) B1170173
theorem B780131 : Blo 778337 780131 := bstep (se 1 (by rfl) ⟨585098, by rfl⟩ : syracuseStep 780131 = 1170197) B1170197
theorem B1173347 : Blo 778337 1173347 := bstep (se 1 (by rfl) ⟨880010, by rfl⟩ : syracuseStep 1173347 = 1760021) B1760021
theorem B14444401 : Blo 778337 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B780147 : Blo 778337 780147 := bstep (se 1 (by rfl) ⟨585110, by rfl⟩ : syracuseStep 780147 = 1170221) B1170221
theorem B11265905 : Blo 778337 11265905 := bstep (se 2 (by rfl) ⟨4224714, by rfl⟩ : syracuseStep 11265905 = 8449429) B8449429
theorem B1173377 : Blo 778337 1173377 := bstep (se 2 (by rfl) ⟨440016, by rfl⟩ : syracuseStep 1173377 = 880033) B880033
theorem B780163 : Blo 778337 780163 := bstep (se 1 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 780163 = 1170245) B1170245
theorem B878467 : Blo 778337 878467 := bstep (se 1 (by rfl) ⟨658850, by rfl⟩ : syracuseStep 878467 = 1317701) B1317701
theorem B780179 : Blo 778337 780179 := bstep (se 1 (by rfl) ⟨585134, by rfl⟩ : syracuseStep 780179 = 1170269) B1170269
theorem B1173395 : Blo 778337 1173395 := bstep (se 1 (by rfl) ⟨880046, by rfl⟩ : syracuseStep 1173395 = 1760093) B1760093
theorem B780195 : Blo 778337 780195 := bstep (se 1 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 780195 = 1170293) B1170293
theorem B1173425 : Blo 778337 1173425 := bstep (se 2 (by rfl) ⟨440034, by rfl⟩ : syracuseStep 1173425 = 880069) B880069
theorem B780211 : Blo 778337 780211 := bstep (se 1 (by rfl) ⟨585158, by rfl⟩ : syracuseStep 780211 = 1170317) B1170317
theorem B780227 : Blo 778337 780227 := bstep (se 1 (by rfl) ⟨585170, by rfl⟩ : syracuseStep 780227 = 1170341) B1170341
theorem B1173443 : Blo 778337 1173443 := bstep (se 1 (by rfl) ⟨880082, by rfl⟩ : syracuseStep 1173443 = 1760165) B1760165
theorem B2779085 : Blo 778337 2779085 := bstep (se 3 (by rfl) ⟨521078, by rfl⟩ : syracuseStep 2779085 = 1042157) B1042157
theorem B780243 : Blo 778337 780243 := bstep (se 1 (by rfl) ⟨585182, by rfl⟩ : syracuseStep 780243 = 1170365) B1170365
theorem B1173473 : Blo 778337 1173473 := bstep (se 2 (by rfl) ⟨440052, by rfl⟩ : syracuseStep 1173473 = 880105) B880105
theorem B780259 : Blo 778337 780259 := bstep (se 1 (by rfl) ⟨585194, by rfl⟩ : syracuseStep 780259 = 1170389) B1170389
theorem B780275 : Blo 778337 780275 := bstep (se 1 (by rfl) ⟨585206, by rfl⟩ : syracuseStep 780275 = 1170413) B1170413
theorem B1173491 : Blo 778337 1173491 := bstep (se 1 (by rfl) ⟨880118, by rfl⟩ : syracuseStep 1173491 = 1760237) B1760237
theorem B780291 : Blo 778337 780291 := bstep (se 1 (by rfl) ⟨585218, by rfl⟩ : syracuseStep 780291 = 1170437) B1170437
theorem B2222083 : Blo 778337 2222083 := bstep (se 1 (by rfl) ⟨1666562, by rfl⟩ : syracuseStep 2222083 = 3333125) B3333125
theorem B780307 : Blo 778337 780307 := bstep (se 1 (by rfl) ⟨585230, by rfl⟩ : syracuseStep 780307 = 1170461) B1170461
theorem B878611 : Blo 778337 878611 := bstep (se 1 (by rfl) ⟨658958, by rfl⟩ : syracuseStep 878611 = 1317917) B1317917
theorem B780323 : Blo 778337 780323 := bstep (se 1 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 780323 = 1170485) B1170485
theorem B2222129 : Blo 778337 2222129 := bstep (se 2 (by rfl) ⟨833298, by rfl⟩ : syracuseStep 2222129 = 1666597) B1666597
theorem B780339 : Blo 778337 780339 := bstep (se 1 (by rfl) ⟨585254, by rfl⟩ : syracuseStep 780339 = 1170509) B1170509
theorem B780355 : Blo 778337 780355 := bstep (se 1 (by rfl) ⟨585266, by rfl⟩ : syracuseStep 780355 = 1170533) B1170533
theorem B7596101 : Blo 778337 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B780371 : Blo 778337 780371 := bstep (se 1 (by rfl) ⟨585278, by rfl⟩ : syracuseStep 780371 = 1170557) B1170557
theorem B780387 : Blo 778337 780387 := bstep (se 1 (by rfl) ⟨585290, by rfl⟩ : syracuseStep 780387 = 1170581) B1170581
theorem B780403 : Blo 778337 780403 := bstep (se 1 (by rfl) ⟨585302, by rfl⟩ : syracuseStep 780403 = 1170605) B1170605
theorem B780419 : Blo 778337 780419 := bstep (se 1 (by rfl) ⟨585314, by rfl⟩ : syracuseStep 780419 = 1170629) B1170629
theorem B780435 : Blo 778337 780435 := bstep (se 1 (by rfl) ⟨585326, by rfl⟩ : syracuseStep 780435 = 1170653) B1170653
theorem B780451 : Blo 778337 780451 := bstep (se 1 (by rfl) ⟨585338, by rfl⟩ : syracuseStep 780451 = 1170677) B1170677
theorem B878755 : Blo 778337 878755 := bstep (se 1 (by rfl) ⟨659066, by rfl⟩ : syracuseStep 878755 = 1318133) B1318133
theorem B780467 : Blo 778337 780467 := bstep (se 1 (by rfl) ⟨585350, by rfl⟩ : syracuseStep 780467 = 1170701) B1170701
theorem B780483 : Blo 778337 780483 := bstep (se 1 (by rfl) ⟨585362, by rfl⟩ : syracuseStep 780483 = 1170725) B1170725
theorem B780499 : Blo 778337 780499 := bstep (se 1 (by rfl) ⟨585374, by rfl⟩ : syracuseStep 780499 = 1170749) B1170749
theorem B780515 : Blo 778337 780515 := bstep (se 1 (by rfl) ⟨585386, by rfl⟩ : syracuseStep 780515 = 1170773) B1170773
theorem B780531 : Blo 778337 780531 := bstep (se 1 (by rfl) ⟨585398, by rfl⟩ : syracuseStep 780531 = 1170797) B1170797
theorem B780547 : Blo 778337 780547 := bstep (se 1 (by rfl) ⟨585410, by rfl⟩ : syracuseStep 780547 = 1170821) B1170821
theorem B5335301 : Blo 778337 5335301 := bstep (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) B1000369
theorem B780563 : Blo 778337 780563 := bstep (se 1 (by rfl) ⟨585422, by rfl⟩ : syracuseStep 780563 = 1170845) B1170845
theorem B780579 : Blo 778337 780579 := bstep (se 1 (by rfl) ⟨585434, by rfl⟩ : syracuseStep 780579 = 1170869) B1170869
theorem B780595 : Blo 778337 780595 := bstep (se 1 (by rfl) ⟨585446, by rfl⟩ : syracuseStep 780595 = 1170893) B1170893
theorem B878899 : Blo 778337 878899 := bstep (se 1 (by rfl) ⟨659174, by rfl⟩ : syracuseStep 878899 = 1318349) B1318349
theorem B780611 : Blo 778337 780611 := bstep (se 1 (by rfl) ⟨585458, by rfl⟩ : syracuseStep 780611 = 1170917) B1170917
theorem B3959117 : Blo 778337 3959117 := bstep (se 3 (by rfl) ⟨742334, by rfl⟩ : syracuseStep 3959117 = 1484669) B1484669
theorem B780627 : Blo 778337 780627 := bstep (se 1 (by rfl) ⟨585470, by rfl⟩ : syracuseStep 780627 = 1170941) B1170941
theorem B780643 : Blo 778337 780643 := bstep (se 1 (by rfl) ⟨585482, by rfl⟩ : syracuseStep 780643 = 1170965) B1170965
theorem B780659 : Blo 778337 780659 := bstep (se 1 (by rfl) ⟨585494, by rfl⟩ : syracuseStep 780659 = 1170989) B1170989
theorem B780675 : Blo 778337 780675 := bstep (se 1 (by rfl) ⟨585506, by rfl⟩ : syracuseStep 780675 = 1171013) B1171013
theorem B780691 : Blo 778337 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B780707 : Blo 778337 780707 := bstep (se 1 (by rfl) ⟨585530, by rfl⟩ : syracuseStep 780707 = 1171061) B1171061
theorem B780723 : Blo 778337 780723 := bstep (se 1 (by rfl) ⟨585542, by rfl⟩ : syracuseStep 780723 = 1171085) B1171085
theorem B780739 : Blo 778337 780739 := bstep (se 1 (by rfl) ⟨585554, by rfl⟩ : syracuseStep 780739 = 1171109) B1171109
theorem B879043 : Blo 778337 879043 := bstep (se 1 (by rfl) ⟨659282, by rfl⟩ : syracuseStep 879043 = 1318565) B1318565
theorem B780755 : Blo 778337 780755 := bstep (se 1 (by rfl) ⟨585566, by rfl⟩ : syracuseStep 780755 = 1171133) B1171133
theorem B780771 : Blo 778337 780771 := bstep (se 1 (by rfl) ⟨585578, by rfl⟩ : syracuseStep 780771 = 1171157) B1171157
theorem B780787 : Blo 778337 780787 := bstep (se 1 (by rfl) ⟨585590, by rfl⟩ : syracuseStep 780787 = 1171181) B1171181
theorem B780803 : Blo 778337 780803 := bstep (se 1 (by rfl) ⟨585602, by rfl⟩ : syracuseStep 780803 = 1171205) B1171205
theorem B780819 : Blo 778337 780819 := bstep (se 1 (by rfl) ⟨585614, by rfl⟩ : syracuseStep 780819 = 1171229) B1171229
theorem B1108513 : Blo 778337 1108513 := bstep (se 2 (by rfl) ⟨415692, by rfl⟩ : syracuseStep 1108513 = 831385) B831385
theorem B780835 : Blo 778337 780835 := bstep (se 1 (by rfl) ⟨585626, by rfl⟩ : syracuseStep 780835 = 1171253) B1171253
theorem B1141297 : Blo 778337 1141297 := bstep (se 2 (by rfl) ⟨427986, by rfl⟩ : syracuseStep 1141297 = 855973) B855973
theorem B780851 : Blo 778337 780851 := bstep (se 1 (by rfl) ⟨585638, by rfl⟩ : syracuseStep 780851 = 1171277) B1171277
theorem B780867 : Blo 778337 780867 := bstep (se 1 (by rfl) ⟨585650, by rfl⟩ : syracuseStep 780867 = 1171301) B1171301
theorem B780883 : Blo 778337 780883 := bstep (se 1 (by rfl) ⟨585662, by rfl⟩ : syracuseStep 780883 = 1171325) B1171325
theorem B879187 : Blo 778337 879187 := bstep (se 1 (by rfl) ⟨659390, by rfl⟩ : syracuseStep 879187 = 1318781) B1318781
theorem B780899 : Blo 778337 780899 := bstep (se 1 (by rfl) ⟨585674, by rfl⟩ : syracuseStep 780899 = 1171349) B1171349
theorem B780915 : Blo 778337 780915 := bstep (se 1 (by rfl) ⟨585686, by rfl⟩ : syracuseStep 780915 = 1171373) B1171373
theorem B780931 : Blo 778337 780931 := bstep (se 1 (by rfl) ⟨585698, by rfl⟩ : syracuseStep 780931 = 1171397) B1171397
theorem B780947 : Blo 778337 780947 := bstep (se 1 (by rfl) ⟨585710, by rfl⟩ : syracuseStep 780947 = 1171421) B1171421
theorem B780963 : Blo 778337 780963 := bstep (se 1 (by rfl) ⟨585722, by rfl⟩ : syracuseStep 780963 = 1171445) B1171445
theorem B780979 : Blo 778337 780979 := bstep (se 1 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 780979 = 1171469) B1171469
theorem B780995 : Blo 778337 780995 := bstep (se 1 (by rfl) ⟨585746, by rfl⟩ : syracuseStep 780995 = 1171493) B1171493
theorem B781011 : Blo 778337 781011 := bstep (se 1 (by rfl) ⟨585758, by rfl⟩ : syracuseStep 781011 = 1171517) B1171517
theorem B781027 : Blo 778337 781027 := bstep (se 1 (by rfl) ⟨585770, by rfl⟩ : syracuseStep 781027 = 1171541) B1171541
theorem B879331 : Blo 778337 879331 := bstep (se 1 (by rfl) ⟨659498, by rfl⟩ : syracuseStep 879331 = 1318997) B1318997
theorem B5630705 : Blo 778337 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B781043 : Blo 778337 781043 := bstep (se 1 (by rfl) ⟨585782, by rfl⟩ : syracuseStep 781043 = 1171565) B1171565
theorem B781059 : Blo 778337 781059 := bstep (se 1 (by rfl) ⟨585794, by rfl⟩ : syracuseStep 781059 = 1171589) B1171589
theorem B781075 : Blo 778337 781075 := bstep (se 1 (by rfl) ⟨585806, by rfl⟩ : syracuseStep 781075 = 1171613) B1171613
theorem B781091 : Blo 778337 781091 := bstep (se 1 (by rfl) ⟨585818, by rfl⟩ : syracuseStep 781091 = 1171637) B1171637
theorem B781107 : Blo 778337 781107 := bstep (se 1 (by rfl) ⟨585830, by rfl⟩ : syracuseStep 781107 = 1171661) B1171661
theorem B781123 : Blo 778337 781123 := bstep (se 1 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 781123 = 1171685) B1171685
theorem B781139 : Blo 778337 781139 := bstep (se 1 (by rfl) ⟨585854, by rfl⟩ : syracuseStep 781139 = 1171709) B1171709
theorem B781155 : Blo 778337 781155 := bstep (se 1 (by rfl) ⟨585866, by rfl⟩ : syracuseStep 781155 = 1171733) B1171733
theorem B781171 : Blo 778337 781171 := bstep (se 1 (by rfl) ⟨585878, by rfl⟩ : syracuseStep 781171 = 1171757) B1171757
theorem B879475 : Blo 778337 879475 := bstep (se 1 (by rfl) ⟨659606, by rfl⟩ : syracuseStep 879475 = 1319213) B1319213
theorem B781187 : Blo 778337 781187 := bstep (se 1 (by rfl) ⟨585890, by rfl⟩ : syracuseStep 781187 = 1171781) B1171781
theorem B781203 : Blo 778337 781203 := bstep (se 1 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 781203 = 1171805) B1171805
theorem B781219 : Blo 778337 781219 := bstep (se 1 (by rfl) ⟨585914, by rfl⟩ : syracuseStep 781219 = 1171829) B1171829
theorem B781235 : Blo 778337 781235 := bstep (se 1 (by rfl) ⟨585926, by rfl⟩ : syracuseStep 781235 = 1171853) B1171853
theorem B781251 : Blo 778337 781251 := bstep (se 1 (by rfl) ⟨585938, by rfl⟩ : syracuseStep 781251 = 1171877) B1171877
theorem B781267 : Blo 778337 781267 := bstep (se 1 (by rfl) ⟨585950, by rfl⟩ : syracuseStep 781267 = 1171901) B1171901
theorem B781283 : Blo 778337 781283 := bstep (se 1 (by rfl) ⟨585962, by rfl⟩ : syracuseStep 781283 = 1171925) B1171925
theorem B5499875 : Blo 778337 5499875 := bstep (se 1 (by rfl) ⟨4124906, by rfl⟩ : syracuseStep 5499875 = 8249813) B8249813
theorem B781299 : Blo 778337 781299 := bstep (se 1 (by rfl) ⟨585974, by rfl⟩ : syracuseStep 781299 = 1171949) B1171949
theorem B781315 : Blo 778337 781315 := bstep (se 1 (by rfl) ⟨585986, by rfl⟩ : syracuseStep 781315 = 1171973) B1171973
theorem B879619 : Blo 778337 879619 := bstep (se 1 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 879619 = 1319429) B1319429
theorem B781331 : Blo 778337 781331 := bstep (se 1 (by rfl) ⟨585998, by rfl⟩ : syracuseStep 781331 = 1171997) B1171997
theorem B781347 : Blo 778337 781347 := bstep (se 1 (by rfl) ⟨586010, by rfl⟩ : syracuseStep 781347 = 1172021) B1172021
theorem B781363 : Blo 778337 781363 := bstep (se 1 (by rfl) ⟨586022, by rfl⟩ : syracuseStep 781363 = 1172045) B1172045
theorem B781379 : Blo 778337 781379 := bstep (se 1 (by rfl) ⟨586034, by rfl⟩ : syracuseStep 781379 = 1172069) B1172069
theorem B781395 : Blo 778337 781395 := bstep (se 1 (by rfl) ⟨586046, by rfl⟩ : syracuseStep 781395 = 1172093) B1172093
theorem B781411 : Blo 778337 781411 := bstep (se 1 (by rfl) ⟨586058, by rfl⟩ : syracuseStep 781411 = 1172117) B1172117
theorem B781427 : Blo 778337 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B781443 : Blo 778337 781443 := bstep (se 1 (by rfl) ⟨586082, by rfl⟩ : syracuseStep 781443 = 1172165) B1172165
theorem B781459 : Blo 778337 781459 := bstep (se 1 (by rfl) ⟨586094, by rfl⟩ : syracuseStep 781459 = 1172189) B1172189
theorem B879763 : Blo 778337 879763 := bstep (se 1 (by rfl) ⟨659822, by rfl⟩ : syracuseStep 879763 = 1319645) B1319645
theorem B781475 : Blo 778337 781475 := bstep (se 1 (by rfl) ⟨586106, by rfl⟩ : syracuseStep 781475 = 1172213) B1172213
theorem B781491 : Blo 778337 781491 := bstep (se 1 (by rfl) ⟨586118, by rfl⟩ : syracuseStep 781491 = 1172237) B1172237
theorem B781507 : Blo 778337 781507 := bstep (se 1 (by rfl) ⟨586130, by rfl⟩ : syracuseStep 781507 = 1172261) B1172261
theorem B781523 : Blo 778337 781523 := bstep (se 1 (by rfl) ⟨586142, by rfl⟩ : syracuseStep 781523 = 1172285) B1172285
theorem B1109219 : Blo 778337 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B1502435 : Blo 778337 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B781539 : Blo 778337 781539 := bstep (se 1 (by rfl) ⟨586154, by rfl⟩ : syracuseStep 781539 = 1172309) B1172309
theorem B1666289 : Blo 778337 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B781555 : Blo 778337 781555 := bstep (se 1 (by rfl) ⟨586166, by rfl⟩ : syracuseStep 781555 = 1172333) B1172333
theorem B1666307 : Blo 778337 1666307 := bstep (se 1 (by rfl) ⟨1249730, by rfl⟩ : syracuseStep 1666307 = 2499461) B2499461
theorem B781571 : Blo 778337 781571 := bstep (se 1 (by rfl) ⟨586178, by rfl⟩ : syracuseStep 781571 = 1172357) B1172357
theorem B781587 : Blo 778337 781587 := bstep (se 1 (by rfl) ⟨586190, by rfl⟩ : syracuseStep 781587 = 1172381) B1172381
theorem B781603 : Blo 778337 781603 := bstep (se 1 (by rfl) ⟨586202, by rfl⟩ : syracuseStep 781603 = 1172405) B1172405
theorem B879907 : Blo 778337 879907 := bstep (se 1 (by rfl) ⟨659930, by rfl⟩ : syracuseStep 879907 = 1319861) B1319861
theorem B781619 : Blo 778337 781619 := bstep (se 1 (by rfl) ⟨586214, by rfl⟩ : syracuseStep 781619 = 1172429) B1172429
theorem B781635 : Blo 778337 781635 := bstep (se 1 (by rfl) ⟨586226, by rfl⟩ : syracuseStep 781635 = 1172453) B1172453
theorem B5008709 : Blo 778337 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B781651 : Blo 778337 781651 := bstep (se 1 (by rfl) ⟨586238, by rfl⟩ : syracuseStep 781651 = 1172477) B1172477
theorem B1404259 : Blo 778337 1404259 := bstep (se 1 (by rfl) ⟨1053194, by rfl⟩ : syracuseStep 1404259 = 2106389) B2106389
theorem B781667 : Blo 778337 781667 := bstep (se 1 (by rfl) ⟨586250, by rfl⟩ : syracuseStep 781667 = 1172501) B1172501
theorem B781683 : Blo 778337 781683 := bstep (se 1 (by rfl) ⟨586262, by rfl⟩ : syracuseStep 781683 = 1172525) B1172525
theorem B781699 : Blo 778337 781699 := bstep (se 1 (by rfl) ⟨586274, by rfl⟩ : syracuseStep 781699 = 1172549) B1172549
theorem B781715 : Blo 778337 781715 := bstep (se 1 (by rfl) ⟨586286, by rfl⟩ : syracuseStep 781715 = 1172573) B1172573
theorem B781731 : Blo 778337 781731 := bstep (se 1 (by rfl) ⟨586298, by rfl⟩ : syracuseStep 781731 = 1172597) B1172597
theorem B781747 : Blo 778337 781747 := bstep (se 1 (by rfl) ⟨586310, by rfl⟩ : syracuseStep 781747 = 1172621) B1172621
theorem B880051 : Blo 778337 880051 := bstep (se 1 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 880051 = 1320077) B1320077
theorem B781763 : Blo 778337 781763 := bstep (se 1 (by rfl) ⟨586322, by rfl⟩ : syracuseStep 781763 = 1172645) B1172645
theorem B781779 : Blo 778337 781779 := bstep (se 1 (by rfl) ⟨586334, by rfl⟩ : syracuseStep 781779 = 1172669) B1172669
theorem B2223587 : Blo 778337 2223587 := bstep (se 1 (by rfl) ⟨1667690, by rfl⟩ : syracuseStep 2223587 = 3335381) B3335381
theorem B781795 : Blo 778337 781795 := bstep (se 1 (by rfl) ⟨586346, by rfl⟩ : syracuseStep 781795 = 1172693) B1172693
theorem B781811 : Blo 778337 781811 := bstep (se 1 (by rfl) ⟨586358, by rfl⟩ : syracuseStep 781811 = 1172717) B1172717
theorem B781827 : Blo 778337 781827 := bstep (se 1 (by rfl) ⟨586370, by rfl⟩ : syracuseStep 781827 = 1172741) B1172741
theorem B781843 : Blo 778337 781843 := bstep (se 1 (by rfl) ⟨586382, by rfl⟩ : syracuseStep 781843 = 1172765) B1172765
theorem B781859 : Blo 778337 781859 := bstep (se 1 (by rfl) ⟨586394, by rfl⟩ : syracuseStep 781859 = 1172789) B1172789
theorem B781875 : Blo 778337 781875 := bstep (se 1 (by rfl) ⟨586406, by rfl⟩ : syracuseStep 781875 = 1172813) B1172813
theorem B781891 : Blo 778337 781891 := bstep (se 1 (by rfl) ⟨586418, by rfl⟩ : syracuseStep 781891 = 1172837) B1172837
theorem B781907 : Blo 778337 781907 := bstep (se 1 (by rfl) ⟨586430, by rfl⟩ : syracuseStep 781907 = 1172861) B1172861
theorem B781923 : Blo 778337 781923 := bstep (se 1 (by rfl) ⟨586442, by rfl⟩ : syracuseStep 781923 = 1172885) B1172885
theorem B3337841 : Blo 778337 3337841 := bstep (se 2 (by rfl) ⟨1251690, by rfl⟩ : syracuseStep 3337841 = 2503381) B2503381
theorem B781939 : Blo 778337 781939 := bstep (se 1 (by rfl) ⟨586454, by rfl⟩ : syracuseStep 781939 = 1172909) B1172909
theorem B781955 : Blo 778337 781955 := bstep (se 1 (by rfl) ⟨586466, by rfl⟩ : syracuseStep 781955 = 1172933) B1172933
theorem B781971 : Blo 778337 781971 := bstep (se 1 (by rfl) ⟨586478, by rfl⟩ : syracuseStep 781971 = 1172957) B1172957
theorem B781987 : Blo 778337 781987 := bstep (se 1 (by rfl) ⟨586490, by rfl⟩ : syracuseStep 781987 = 1172981) B1172981
theorem B782003 : Blo 778337 782003 := bstep (se 1 (by rfl) ⟨586502, by rfl⟩ : syracuseStep 782003 = 1173005) B1173005
theorem B782019 : Blo 778337 782019 := bstep (se 1 (by rfl) ⟨586514, by rfl⟩ : syracuseStep 782019 = 1173029) B1173029
theorem B782035 : Blo 778337 782035 := bstep (se 1 (by rfl) ⟨586526, by rfl⟩ : syracuseStep 782035 = 1173053) B1173053
theorem B782051 : Blo 778337 782051 := bstep (se 1 (by rfl) ⟨586538, by rfl⟩ : syracuseStep 782051 = 1173077) B1173077
theorem B782067 : Blo 778337 782067 := bstep (se 1 (by rfl) ⟨586550, by rfl⟩ : syracuseStep 782067 = 1173101) B1173101
theorem B782083 : Blo 778337 782083 := bstep (se 1 (by rfl) ⟨586562, by rfl⟩ : syracuseStep 782083 = 1173125) B1173125
theorem B782099 : Blo 778337 782099 := bstep (se 1 (by rfl) ⟨586574, by rfl⟩ : syracuseStep 782099 = 1173149) B1173149
theorem B782115 : Blo 778337 782115 := bstep (se 1 (by rfl) ⟨586586, by rfl⟩ : syracuseStep 782115 = 1173173) B1173173
theorem B782131 : Blo 778337 782131 := bstep (se 1 (by rfl) ⟨586598, by rfl⟩ : syracuseStep 782131 = 1173197) B1173197
theorem B782147 : Blo 778337 782147 := bstep (se 1 (by rfl) ⟨586610, by rfl⟩ : syracuseStep 782147 = 1173221) B1173221
theorem B782163 : Blo 778337 782163 := bstep (se 1 (by rfl) ⟨586622, by rfl⟩ : syracuseStep 782163 = 1173245) B1173245
theorem B1109857 : Blo 778337 1109857 := bstep (se 2 (by rfl) ⟨416196, by rfl⟩ : syracuseStep 1109857 = 832393) B832393
theorem B782179 : Blo 778337 782179 := bstep (se 1 (by rfl) ⟨586634, by rfl⟩ : syracuseStep 782179 = 1173269) B1173269
theorem B5926769 : Blo 778337 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B782195 : Blo 778337 782195 := bstep (se 1 (by rfl) ⟨586646, by rfl⟩ : syracuseStep 782195 = 1173293) B1173293
theorem B782211 : Blo 778337 782211 := bstep (se 1 (by rfl) ⟨586658, by rfl⟩ : syracuseStep 782211 = 1173317) B1173317
theorem B782227 : Blo 778337 782227 := bstep (se 1 (by rfl) ⟨586670, by rfl⟩ : syracuseStep 782227 = 1173341) B1173341
theorem B782243 : Blo 778337 782243 := bstep (se 1 (by rfl) ⟨586682, by rfl⟩ : syracuseStep 782243 = 1173365) B1173365
theorem B782259 : Blo 778337 782259 := bstep (se 1 (by rfl) ⟨586694, by rfl⟩ : syracuseStep 782259 = 1173389) B1173389
theorem B782275 : Blo 778337 782275 := bstep (se 1 (by rfl) ⟨586706, by rfl⟩ : syracuseStep 782275 = 1173413) B1173413
theorem B1109971 : Blo 778337 1109971 := bstep (se 1 (by rfl) ⟨832478, by rfl⟩ : syracuseStep 1109971 = 1664957) B1664957
theorem B782291 : Blo 778337 782291 := bstep (se 1 (by rfl) ⟨586718, by rfl⟩ : syracuseStep 782291 = 1173437) B1173437
theorem B782307 : Blo 778337 782307 := bstep (se 1 (by rfl) ⟨586730, by rfl⟩ : syracuseStep 782307 = 1173461) B1173461
theorem B782323 : Blo 778337 782323 := bstep (se 1 (by rfl) ⟨586742, by rfl⟩ : syracuseStep 782323 = 1173485) B1173485
theorem B1405009 : Blo 778337 1405009 := bstep (se 2 (by rfl) ⟨526878, by rfl⟩ : syracuseStep 1405009 = 1053757) B1053757
theorem B21328069 : Blo 778337 21328069 := bstep (se 4 (by rfl) ⟨1999506, by rfl⟩ : syracuseStep 21328069 = 3999013) B3999013
theorem B4878563 : Blo 778337 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B1667537 : Blo 778337 1667537 := bstep (se 2 (by rfl) ⟨625326, by rfl⟩ : syracuseStep 1667537 = 1250653) B1250653
theorem B3338765 : Blo 778337 3338765 := bstep (se 3 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 3338765 = 1252037) B1252037
theorem B2224817 : Blo 778337 2224817 := bstep (se 2 (by rfl) ⟨834306, by rfl⟩ : syracuseStep 2224817 = 1668613) B1668613
theorem B1504003 : Blo 778337 1504003 := bstep (se 1 (by rfl) ⟨1128002, by rfl⟩ : syracuseStep 1504003 = 2256005) B2256005
theorem B4453325 : Blo 778337 4453325 := bstep (se 3 (by rfl) ⟨834998, by rfl⟩ : syracuseStep 4453325 = 1669997) B1669997
theorem B8909837 : Blo 778337 8909837 := bstep (se 3 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 8909837 = 3341189) B3341189
theorem B3994829 : Blo 778337 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B5010659 : Blo 778337 5010659 := bstep (se 1 (by rfl) ⟨3757994, by rfl⟩ : syracuseStep 5010659 = 7515989) B7515989
theorem B1111315 : Blo 778337 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B2848241 : Blo 778337 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B2815843 : Blo 778337 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1669091 : Blo 778337 1669091 := bstep (se 1 (by rfl) ⟨1251818, by rfl⟩ : syracuseStep 1669091 = 2503637) B2503637
theorem B2226275 : Blo 778337 2226275 := bstep (se 1 (by rfl) ⟨1669706, by rfl⟩ : syracuseStep 2226275 = 3339413) B3339413
theorem B1407331 : Blo 778337 1407331 := bstep (se 1 (by rfl) ⟨1055498, by rfl⟩ : syracuseStep 1407331 = 2110997) B2110997
theorem B1112449 : Blo 778337 1112449 := bstep (se 2 (by rfl) ⟨417168, by rfl⟩ : syracuseStep 1112449 = 834337) B834337
theorem B1112545 : Blo 778337 1112545 := bstep (se 2 (by rfl) ⟨417204, by rfl⟩ : syracuseStep 1112545 = 834409) B834409
theorem B2849293 : Blo 778337 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B1407793 : Blo 778337 1407793 := bstep (se 2 (by rfl) ⟨527922, by rfl⟩ : syracuseStep 1407793 = 1055845) B1055845
theorem B2227085 : Blo 778337 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B1113041 : Blo 778337 1113041 := bstep (se 2 (by rfl) ⟨417390, by rfl⟩ : syracuseStep 1113041 = 834781) B834781
theorem B4815877 : Blo 778337 4815877 := bstep (se 4 (by rfl) ⟨451488, by rfl⟩ : syracuseStep 4815877 = 902977) B902977
theorem B2227277 : Blo 778337 2227277 := bstep (se 3 (by rfl) ⟨417614, by rfl⟩ : syracuseStep 2227277 = 835229) B835229
theorem B4455557 : Blo 778337 4455557 := bstep (se 4 (by rfl) ⟨417708, by rfl⟩ : syracuseStep 4455557 = 835417) B835417
theorem B1408369 : Blo 778337 1408369 := bstep (se 2 (by rfl) ⟨528138, by rfl⟩ : syracuseStep 1408369 = 1056277) B1056277
theorem B1113907 : Blo 778337 1113907 := bstep (se 1 (by rfl) ⟨835430, by rfl⟩ : syracuseStep 1113907 = 1670861) B1670861
theorem B1408931 : Blo 778337 1408931 := bstep (se 1 (by rfl) ⟨1056698, by rfl⟩ : syracuseStep 1408931 = 2113397) B2113397
theorem B1409177 : Blo 778337 1409177 := bstep (se 2 (by rfl) ⟨528441, by rfl⟩ : syracuseStep 1409177 = 1056883) B1056883
theorem B1409537 : Blo 778337 1409537 := bstep (se 2 (by rfl) ⟨528576, by rfl⟩ : syracuseStep 1409537 = 1057153) B1057153
theorem B2818583 : Blo 778337 2818583 := bstep (se 1 (by rfl) ⟨2113937, by rfl⟩ : syracuseStep 2818583 = 4227875) B4227875
theorem B13009501 : Blo 778337 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B5637221 : Blo 778337 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B2819245 : Blo 778337 2819245 := bstep (se 3 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 2819245 = 1057217) B1057217
theorem B4752857 : Blo 778337 4752857 := bstep (se 2 (by rfl) ⟨1782321, by rfl⟩ : syracuseStep 4752857 = 3564643) B3564643
theorem B1246795 : Blo 778337 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B1607347 : Blo 778337 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B985547 : Blo 778337 985547 := bstep (se 1 (by rfl) ⟨739160, by rfl⟩ : syracuseStep 985547 = 1478321) B1478321
theorem B5933573 : Blo 778337 5933573 := bstep (se 4 (by rfl) ⟨556272, by rfl⟩ : syracuseStep 5933573 = 1112545) B1112545
theorem B1313867 : Blo 778337 1313867 := bstep (se 1 (by rfl) ⟨985400, by rfl⟩ : syracuseStep 1313867 = 1970801) B1970801
theorem B986251 : Blo 778337 986251 := bstep (se 1 (by rfl) ⟨739688, by rfl⟩ : syracuseStep 986251 = 1479377) B1479377
theorem B1477835 : Blo 778337 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B1313995 : Blo 778337 1313995 := bstep (se 1 (by rfl) ⟨985496, by rfl⟩ : syracuseStep 1313995 = 1970993) B1970993
theorem B888023 : Blo 778337 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B1314137 : Blo 778337 1314137 := bstep (se 2 (by rfl) ⟨492801, by rfl⟩ : syracuseStep 1314137 = 985603) B985603
theorem B1478017 : Blo 778337 1478017 := bstep (se 2 (by rfl) ⟨554256, by rfl⟩ : syracuseStep 1478017 = 1108513) B1108513
theorem B36015509 : Blo 778337 36015509 := bstep (se 6 (by rfl) ⟨844113, by rfl⟩ : syracuseStep 36015509 = 1688227) B1688227
theorem B986519 : Blo 778337 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B6098327 : Blo 778337 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B2493899 : Blo 778337 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B1314265 : Blo 778337 1314265 := bstep (se 2 (by rfl) ⟨492849, by rfl⟩ : syracuseStep 1314265 = 985699) B985699
theorem B16912003 : Blo 778337 16912003 := bstep (se 1 (by rfl) ⟨12684002, by rfl⟩ : syracuseStep 16912003 = 25368005) B25368005
theorem B1314839 : Blo 778337 1314839 := bstep (se 1 (by rfl) ⟨986129, by rfl⟩ : syracuseStep 1314839 = 1972259) B1972259
theorem B1478731 : Blo 778337 1478731 := bstep (se 1 (by rfl) ⟨1109048, by rfl⟩ : syracuseStep 1478731 = 2218097) B2218097
theorem B987223 : Blo 778337 987223 := bstep (se 1 (by rfl) ⟨740417, by rfl⟩ : syracuseStep 987223 = 1480835) B1480835
theorem B1478807 : Blo 778337 1478807 := bstep (se 1 (by rfl) ⟨1109105, by rfl⟩ : syracuseStep 1478807 = 2218211) B2218211
theorem B1314967 : Blo 778337 1314967 := bstep (se 1 (by rfl) ⟨986225, by rfl⟩ : syracuseStep 1314967 = 1972451) B1972451
theorem B1052887 : Blo 778337 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B1970507 : Blo 778337 1970507 := bstep (se 1 (by rfl) ⟨1477880, by rfl⟩ : syracuseStep 1970507 = 2955761) B2955761
theorem B889483 : Blo 778337 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B1315595 : Blo 778337 1315595 := bstep (se 1 (by rfl) ⟨986696, by rfl⟩ : syracuseStep 1315595 = 1973393) B1973393
theorem B1479475 : Blo 778337 1479475 := bstep (se 1 (by rfl) ⟨1109606, by rfl⟩ : syracuseStep 1479475 = 2219213) B2219213
theorem B5936003 : Blo 778337 5936003 := bstep (se 1 (by rfl) ⟨4452002, by rfl⟩ : syracuseStep 5936003 = 8904005) B8904005
theorem B1315723 : Blo 778337 1315723 := bstep (se 1 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 1315723 = 1973585) B1973585
theorem B1479703 : Blo 778337 1479703 := bstep (se 1 (by rfl) ⟨1109777, by rfl⟩ : syracuseStep 1479703 = 2219555) B2219555
theorem B1315865 : Blo 778337 1315865 := bstep (se 2 (by rfl) ⟨493449, by rfl⟩ : syracuseStep 1315865 = 986899) B986899
theorem B1578035 : Blo 778337 1578035 := bstep (se 1 (by rfl) ⟨1183526, by rfl⟩ : syracuseStep 1578035 = 2367053) B2367053
theorem B1479809 : Blo 778337 1479809 := bstep (se 2 (by rfl) ⟨554928, by rfl⟩ : syracuseStep 1479809 = 1109857) B1109857
theorem B1315993 : Blo 778337 1315993 := bstep (se 2 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 1315993 = 986995) B986995
theorem B890039 : Blo 778337 890039 := bstep (se 1 (by rfl) ⟨667529, by rfl⟩ : syracuseStep 890039 = 1335059) B1335059
theorem B1971479 : Blo 778337 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B1479961 : Blo 778337 1479961 := bstep (se 2 (by rfl) ⟨554985, by rfl⟩ : syracuseStep 1479961 = 1109971) B1109971
theorem B16258421 : Blo 778337 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B1250839 : Blo 778337 1250839 := bstep (se 1 (by rfl) ⟨938129, by rfl⟩ : syracuseStep 1250839 = 1876259) B1876259
theorem B10688075 : Blo 778337 10688075 := bstep (se 1 (by rfl) ⟨8016056, by rfl⟩ : syracuseStep 10688075 = 16032113) B16032113
theorem B1316567 : Blo 778337 1316567 := bstep (se 1 (by rfl) ⟨987425, by rfl⟩ : syracuseStep 1316567 = 1974851) B1974851
theorem B988939 : Blo 778337 988939 := bstep (se 1 (by rfl) ⟨741704, by rfl⟩ : syracuseStep 988939 = 1483409) B1483409
theorem B2856779 : Blo 778337 2856779 := bstep (se 1 (by rfl) ⟨2142584, by rfl⟩ : syracuseStep 2856779 = 4285169) B4285169
theorem B1316695 : Blo 778337 1316695 := bstep (se 1 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 1316695 = 1975043) B1975043
theorem B11409329 : Blo 778337 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B1972147 : Blo 778337 1972147 := bstep (se 1 (by rfl) ⟨1479110, by rfl⟩ : syracuseStep 1972147 = 2958221) B2958221
theorem B2627531 : Blo 778337 2627531 := bstep (se 1 (by rfl) ⟨1970648, by rfl⟩ : syracuseStep 2627531 = 3941297) B3941297
theorem B1185817 : Blo 778337 1185817 := bstep (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) B889363
theorem B1972289 : Blo 778337 1972289 := bstep (se 2 (by rfl) ⟨739608, by rfl⟩ : syracuseStep 1972289 = 1479217) B1479217
theorem B792779 : Blo 778337 792779 := bstep (se 1 (by rfl) ⟨594584, by rfl⟩ : syracuseStep 792779 = 1189169) B1189169
theorem B2627801 : Blo 778337 2627801 := bstep (se 2 (by rfl) ⟨985425, by rfl⟩ : syracuseStep 2627801 = 1970851) B1970851
theorem B1579225 : Blo 778337 1579225 := bstep (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) B1184419
theorem B6658321 : Blo 778337 6658321 := bstep (se 2 (by rfl) ⟨2496870, by rfl⟩ : syracuseStep 6658321 = 4993741) B4993741
theorem B1251659 : Blo 778337 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B2005337 : Blo 778337 2005337 := bstep (se 2 (by rfl) ⟨752001, by rfl⟩ : syracuseStep 2005337 = 1504003) B1504003
theorem B1317323 : Blo 778337 1317323 := bstep (se 1 (by rfl) ⟨987992, by rfl⟩ : syracuseStep 1317323 = 1975985) B1975985
theorem B6658595 : Blo 778337 6658595 := bstep (se 1 (by rfl) ⟨4993946, by rfl⟩ : syracuseStep 6658595 = 9987893) B9987893
theorem B1481267 : Blo 778337 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B1317451 : Blo 778337 1317451 := bstep (se 1 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 1317451 = 1976177) B1976177
theorem B7510603 : Blo 778337 7510603 := bstep (se 1 (by rfl) ⟨5632952, by rfl⟩ : syracuseStep 7510603 = 11265905) B11265905
theorem B1481419 : Blo 778337 1481419 := bstep (se 1 (by rfl) ⟨1111064, by rfl⟩ : syracuseStep 1481419 = 2222129) B2222129
theorem B989911 : Blo 778337 989911 := bstep (se 1 (by rfl) ⟨742433, by rfl⟩ : syracuseStep 989911 = 1484867) B1484867
theorem B1317593 : Blo 778337 1317593 := bstep (se 2 (by rfl) ⟨494097, by rfl⟩ : syracuseStep 1317593 = 988195) B988195
theorem B1317721 : Blo 778337 1317721 := bstep (se 2 (by rfl) ⟨494145, by rfl⟩ : syracuseStep 1317721 = 988291) B988291
theorem B2628503 : Blo 778337 2628503 := bstep (se 1 (by rfl) ⟨1971377, by rfl⟩ : syracuseStep 2628503 = 3942755) B3942755
theorem B1481753 : Blo 778337 1481753 := bstep (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) B1111315
theorem B4987979 : Blo 778337 4987979 := bstep (se 1 (by rfl) ⟨3740984, by rfl⟩ : syracuseStep 4987979 = 7481969) B7481969
theorem B1580311 : Blo 778337 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B1973555 : Blo 778337 1973555 := bstep (se 1 (by rfl) ⟨1480166, by rfl⟩ : syracuseStep 1973555 = 2960333) B2960333
theorem B29957525 : Blo 778337 29957525 := bstep (se 6 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 29957525 = 1404259) B1404259
theorem B1318295 : Blo 778337 1318295 := bstep (se 1 (by rfl) ⟨988721, by rfl⟩ : syracuseStep 1318295 = 1977443) B1977443
theorem B2629043 : Blo 778337 2629043 := bstep (se 1 (by rfl) ⟨1971782, by rfl⟩ : syracuseStep 2629043 = 3943565) B3943565
theorem B1318423 : Blo 778337 1318423 := bstep (se 1 (by rfl) ⟨988817, by rfl⟩ : syracuseStep 1318423 = 1977635) B1977635
theorem B2956931 : Blo 778337 2956931 := bstep (se 1 (by rfl) ⟨2217698, by rfl⟩ : syracuseStep 2956931 = 4435397) B4435397
theorem B2956945 : Blo 778337 2956945 := bstep (se 2 (by rfl) ⟨1108854, by rfl⟩ : syracuseStep 2956945 = 2217709) B2217709
theorem B1482391 : Blo 778337 1482391 := bstep (se 1 (by rfl) ⟨1111793, by rfl⟩ : syracuseStep 1482391 = 2223587) B2223587
theorem B1777331 : Blo 778337 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B2629313 : Blo 778337 2629313 := bstep (se 2 (by rfl) ⟨985992, by rfl⟩ : syracuseStep 2629313 = 1971985) B1971985
theorem B1974091 : Blo 778337 1974091 := bstep (se 1 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 1974091 = 2961137) B2961137
theorem B2957249 : Blo 778337 2957249 := bstep (se 2 (by rfl) ⟨1108968, by rfl⟩ : syracuseStep 2957249 = 2217937) B2217937
theorem B1974233 : Blo 778337 1974233 := bstep (se 2 (by rfl) ⟨740337, by rfl⟩ : syracuseStep 1974233 = 1480675) B1480675
theorem B4005953 : Blo 778337 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B1319051 : Blo 778337 1319051 := bstep (se 1 (by rfl) ⟨989288, by rfl⟩ : syracuseStep 1319051 = 1978577) B1978577
theorem B1712281 : Blo 778337 1712281 := bstep (se 2 (by rfl) ⟨642105, by rfl⟩ : syracuseStep 1712281 = 1284211) B1284211
theorem B5939405 : Blo 778337 5939405 := bstep (se 3 (by rfl) ⟨1113638, by rfl⟩ : syracuseStep 5939405 = 2227277) B2227277
theorem B2629853 : Blo 778337 2629853 := bstep (se 3 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 2629853 = 986195) B986195
theorem B1319179 : Blo 778337 1319179 := bstep (se 1 (by rfl) ⟨989384, by rfl⟩ : syracuseStep 1319179 = 1978769) B1978769
theorem B2105689 : Blo 778337 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B1319321 : Blo 778337 1319321 := bstep (se 2 (by rfl) ⟨494745, by rfl⟩ : syracuseStep 1319321 = 989491) B989491
theorem B1483211 : Blo 778337 1483211 := bstep (se 1 (by rfl) ⟨1112408, by rfl⟩ : syracuseStep 1483211 = 2224817) B2224817
theorem B1876441 : Blo 778337 1876441 := bstep (se 2 (by rfl) ⟨703665, by rfl⟩ : syracuseStep 1876441 = 1407331) B1407331
theorem B1483265 : Blo 778337 1483265 := bstep (se 2 (by rfl) ⟨556224, by rfl⟩ : syracuseStep 1483265 = 1112449) B1112449
theorem B1319449 : Blo 778337 1319449 := bstep (se 2 (by rfl) ⟨494793, by rfl⟩ : syracuseStep 1319449 = 989587) B989587
theorem B2957917 : Blo 778337 2957917 := bstep (se 3 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 2957917 = 1109219) B1109219
theorem B4006493 : Blo 778337 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B5939891 : Blo 778337 5939891 := bstep (se 1 (by rfl) ⟨4454918, by rfl⟩ : syracuseStep 5939891 = 8909837) B8909837
theorem B1975063 : Blo 778337 1975063 := bstep (se 1 (by rfl) ⟨1481297, by rfl⟩ : syracuseStep 1975063 = 2962595) B2962595
theorem B2663219 : Blo 778337 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B4432913 : Blo 778337 4432913 := bstep (se 2 (by rfl) ⟨1662342, by rfl⟩ : syracuseStep 4432913 = 3324685) B3324685
theorem B1877057 : Blo 778337 1877057 := bstep (se 2 (by rfl) ⟨703896, by rfl⟩ : syracuseStep 1877057 = 1407793) B1407793
theorem B1320023 : Blo 778337 1320023 := bstep (se 1 (by rfl) ⟨990017, by rfl⟩ : syracuseStep 1320023 = 1980035) B1980035
theorem B1975499 : Blo 778337 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B1320151 : Blo 778337 1320151 := bstep (se 1 (by rfl) ⟨990113, by rfl⟩ : syracuseStep 1320151 = 1980227) B1980227
theorem B2630987 : Blo 778337 2630987 := bstep (se 1 (by rfl) ⟨1973240, by rfl⟩ : syracuseStep 2630987 = 3946481) B3946481
theorem B1779083 : Blo 778337 1779083 := bstep (se 1 (by rfl) ⟨1334312, by rfl⟩ : syracuseStep 1779083 = 2668625) B2668625
theorem B3941783 : Blo 778337 3941783 := bstep (se 1 (by rfl) ⟨2956337, by rfl⟩ : syracuseStep 3941783 = 5912675) B5912675
theorem B1484183 : Blo 778337 1484183 := bstep (se 1 (by rfl) ⟨1113137, by rfl⟩ : syracuseStep 1484183 = 2226275) B2226275
theorem B1975873 : Blo 778337 1975873 := bstep (se 2 (by rfl) ⟨740952, by rfl⟩ : syracuseStep 1975873 = 1481905) B1481905
theorem B2631257 : Blo 778337 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B4990643 : Blo 778337 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B2107073 : Blo 778337 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B1877825 : Blo 778337 1877825 := bstep (se 2 (by rfl) ⟨704184, by rfl⟩ : syracuseStep 1877825 = 1408369) B1408369
theorem B2959193 : Blo 778337 2959193 := bstep (se 2 (by rfl) ⟨1109697, by rfl⟩ : syracuseStep 2959193 = 2219395) B2219395
theorem B4990871 : Blo 778337 4990871 := bstep (se 1 (by rfl) ⟨3743153, by rfl⟩ : syracuseStep 4990871 = 7486307) B7486307
theorem B1484723 : Blo 778337 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B1976471 : Blo 778337 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B2631959 : Blo 778337 2631959 := bstep (se 1 (by rfl) ⟨1973969, by rfl⟩ : syracuseStep 2631959 = 3947939) B3947939
theorem B1583425 : Blo 778337 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B1485209 : Blo 778337 1485209 := bstep (se 2 (by rfl) ⟨556953, by rfl⟩ : syracuseStep 1485209 = 1113907) B1113907
theorem B12036701 : Blo 778337 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B2632499 : Blo 778337 2632499 := bstep (se 1 (by rfl) ⟨1974374, by rfl⟩ : syracuseStep 2632499 = 3948749) B3948749
theorem B1977281 : Blo 778337 1977281 := bstep (se 2 (by rfl) ⟨741480, by rfl⟩ : syracuseStep 1977281 = 1482961) B1482961
theorem B2632769 : Blo 778337 2632769 := bstep (se 2 (by rfl) ⟨987288, by rfl⟩ : syracuseStep 2632769 = 1974577) B1974577
theorem B1584203 : Blo 778337 1584203 := bstep (se 1 (by rfl) ⟨1188152, by rfl⟩ : syracuseStep 1584203 = 2376305) B2376305
theorem B4992101 : Blo 778337 4992101 := bstep (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) B936019
theorem B3288385 : Blo 778337 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B2960819 : Blo 778337 2960819 := bstep (se 1 (by rfl) ⟨2220614, by rfl⟩ : syracuseStep 2960819 = 4441229) B4441229
theorem B2960833 : Blo 778337 2960833 := bstep (se 2 (by rfl) ⟨1110312, by rfl⟩ : syracuseStep 2960833 = 2220625) B2220625
theorem B1977817 : Blo 778337 1977817 := bstep (se 2 (by rfl) ⟨741681, by rfl⟩ : syracuseStep 1977817 = 1483363) B1483363
theorem B3157507 : Blo 778337 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B1781299 : Blo 778337 1781299 := bstep (se 1 (by rfl) ⟨1335974, by rfl⟩ : syracuseStep 1781299 = 2671949) B2671949
theorem B2633309 : Blo 778337 2633309 := bstep (se 3 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 2633309 = 987491) B987491
theorem B2109149 : Blo 778337 2109149 := bstep (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) B790931
theorem B3551321 : Blo 778337 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B4436147 : Blo 778337 4436147 := bstep (se 1 (by rfl) ⟨3327110, by rfl⟩ : syracuseStep 4436147 = 6654221) B6654221
theorem B831979 : Blo 778337 831979 := bstep (se 1 (by rfl) ⟨623984, by rfl⟩ : syracuseStep 831979 = 1247969) B1247969
theorem B1978931 : Blo 778337 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B2110045 : Blo 778337 2110045 := bstep (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) B791267
theorem B5911217 : Blo 778337 5911217 := bstep (se 2 (by rfl) ⟨2216706, by rfl⟩ : syracuseStep 5911217 = 4433413) B4433413
theorem B2634443 : Blo 778337 2634443 := bstep (se 1 (by rfl) ⟨1975832, by rfl⟩ : syracuseStep 2634443 = 3951665) B3951665
theorem B2110283 : Blo 778337 2110283 := bstep (se 1 (by rfl) ⟨1582712, by rfl⟩ : syracuseStep 2110283 = 3165425) B3165425
theorem B1979225 : Blo 778337 1979225 := bstep (se 2 (by rfl) ⟨742209, by rfl⟩ : syracuseStep 1979225 = 1484419) B1484419
theorem B3945347 : Blo 778337 3945347 := bstep (se 1 (by rfl) ⟨2959010, by rfl⟩ : syracuseStep 3945347 = 5918021) B5918021
theorem B1782667 : Blo 778337 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B2634713 : Blo 778337 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B5911703 : Blo 778337 5911703 := bstep (se 1 (by rfl) ⟨4433777, by rfl⟩ : syracuseStep 5911703 = 8867555) B8867555
theorem B2503831 : Blo 778337 2503831 := bstep (se 1 (by rfl) ⟨1877873, by rfl⟩ : syracuseStep 2503831 = 3755747) B3755747
theorem B3421505 : Blo 778337 3421505 := bstep (se 2 (by rfl) ⟨1283064, by rfl⟩ : syracuseStep 3421505 = 2566129) B2566129
theorem B2962763 : Blo 778337 2962763 := bstep (se 1 (by rfl) ⟨2222072, by rfl⟩ : syracuseStep 2962763 = 4444145) B4444145
theorem B2962777 : Blo 778337 2962777 := bstep (se 2 (by rfl) ⟨1111041, by rfl⟩ : syracuseStep 2962777 = 2222083) B2222083
theorem B2373143 : Blo 778337 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B4437605 : Blo 778337 4437605 := bstep (se 4 (by rfl) ⟨416025, by rfl⟩ : syracuseStep 4437605 = 832051) B832051
theorem B2635415 : Blo 778337 2635415 := bstep (se 1 (by rfl) ⟨1976561, by rfl⟩ : syracuseStep 2635415 = 3953123) B3953123
theorem B2111321 : Blo 778337 2111321 := bstep (se 2 (by rfl) ⟨791745, by rfl⟩ : syracuseStep 2111321 = 1583491) B1583491
theorem B10696549 : Blo 778337 10696549 := bstep (se 4 (by rfl) ⟨1002801, by rfl⟩ : syracuseStep 10696549 = 2005603) B2005603
theorem B833495 : Blo 778337 833495 := bstep (se 1 (by rfl) ⟨625121, by rfl⟩ : syracuseStep 833495 = 1250243) B1250243
theorem B4438061 : Blo 778337 4438061 := bstep (se 3 (by rfl) ⟨832136, by rfl⟩ : syracuseStep 4438061 = 1664273) B1664273
theorem B2635955 : Blo 778337 2635955 := bstep (se 1 (by rfl) ⟨1976966, by rfl⟩ : syracuseStep 2635955 = 3953933) B3953933
theorem B2963735 : Blo 778337 2963735 := bstep (se 1 (by rfl) ⟨2222801, by rfl⟩ : syracuseStep 2963735 = 4445603) B4445603
theorem B1751435 : Blo 778337 1751435 := bstep (se 1 (by rfl) ⟨1313576, by rfl⟩ : syracuseStep 1751435 = 2627153) B2627153
theorem B1751489 : Blo 778337 1751489 := bstep (se 2 (by rfl) ⟨656808, by rfl⟩ : syracuseStep 1751489 = 1313617) B1313617
theorem B2636225 : Blo 778337 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B2505163 : Blo 778337 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B834187 : Blo 778337 834187 := bstep (se 1 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 834187 = 1251281) B1251281
theorem B1751705 : Blo 778337 1751705 := bstep (se 2 (by rfl) ⟨656889, by rfl⟩ : syracuseStep 1751705 = 1313779) B1313779
theorem B4438745 : Blo 778337 4438745 := bstep (se 2 (by rfl) ⟨1664529, by rfl⟩ : syracuseStep 4438745 = 3329059) B3329059
theorem B1751795 : Blo 778337 1751795 := bstep (se 1 (by rfl) ⟨1313846, by rfl⟩ : syracuseStep 1751795 = 2627693) B2627693
theorem B1751831 : Blo 778337 1751831 := bstep (se 1 (by rfl) ⟨1313873, by rfl⟩ : syracuseStep 1751831 = 2627747) B2627747
theorem B3160883 : Blo 778337 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B1752011 : Blo 778337 1752011 := bstep (se 1 (by rfl) ⟨1314008, by rfl⟩ : syracuseStep 1752011 = 2628017) B2628017
theorem B6339545 : Blo 778337 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B2636765 : Blo 778337 2636765 := bstep (se 3 (by rfl) ⟨494393, by rfl⟩ : syracuseStep 2636765 = 988787) B988787
theorem B1752065 : Blo 778337 1752065 := bstep (se 2 (by rfl) ⟨657024, by rfl⟩ : syracuseStep 1752065 = 1314049) B1314049
theorem B30063637 : Blo 778337 30063637 := bstep (se 6 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 30063637 = 1409233) B1409233
theorem B2505779 : Blo 778337 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B1752281 : Blo 778337 1752281 := bstep (se 2 (by rfl) ⟨657105, by rfl⟩ : syracuseStep 1752281 = 1314211) B1314211
theorem B1752371 : Blo 778337 1752371 := bstep (se 1 (by rfl) ⟨1314278, by rfl⟩ : syracuseStep 1752371 = 2628557) B2628557
theorem B1752407 : Blo 778337 1752407 := bstep (se 1 (by rfl) ⟨1314305, by rfl⟩ : syracuseStep 1752407 = 2628611) B2628611
theorem B2964995 : Blo 778337 2964995 := bstep (se 1 (by rfl) ⟨2223746, by rfl⟩ : syracuseStep 2964995 = 4447493) B4447493
theorem B1752587 : Blo 778337 1752587 := bstep (se 1 (by rfl) ⟨1314440, by rfl⟩ : syracuseStep 1752587 = 2628881) B2628881
theorem B3554867 : Blo 778337 3554867 := bstep (se 1 (by rfl) ⟨2666150, by rfl⟩ : syracuseStep 3554867 = 5332301) B5332301
theorem B1752641 : Blo 778337 1752641 := bstep (se 2 (by rfl) ⟨657240, by rfl⟩ : syracuseStep 1752641 = 1314481) B1314481
theorem B3325643 : Blo 778337 3325643 := bstep (se 1 (by rfl) ⟨2494232, by rfl⟩ : syracuseStep 3325643 = 4988465) B4988465
theorem B1752857 : Blo 778337 1752857 := bstep (se 2 (by rfl) ⟨657321, by rfl⟩ : syracuseStep 1752857 = 1314643) B1314643
theorem B1752947 : Blo 778337 1752947 := bstep (se 1 (by rfl) ⟨1314710, by rfl⟩ : syracuseStep 1752947 = 2629421) B2629421
theorem B1752983 : Blo 778337 1752983 := bstep (se 1 (by rfl) ⟨1314737, by rfl⟩ : syracuseStep 1752983 = 2629475) B2629475
theorem B3326017 : Blo 778337 3326017 := bstep (se 2 (by rfl) ⟨1247256, by rfl⟩ : syracuseStep 3326017 = 2494513) B2494513
theorem B1753163 : Blo 778337 1753163 := bstep (se 1 (by rfl) ⟨1314872, by rfl⟩ : syracuseStep 1753163 = 2629745) B2629745
theorem B2637899 : Blo 778337 2637899 := bstep (se 1 (by rfl) ⟨1978424, by rfl⟩ : syracuseStep 2637899 = 3956849) B3956849
theorem B1753217 : Blo 778337 1753217 := bstep (se 2 (by rfl) ⟨657456, by rfl⟩ : syracuseStep 1753217 = 1314913) B1314913
theorem B1753433 : Blo 778337 1753433 := bstep (se 2 (by rfl) ⟨657537, by rfl⟩ : syracuseStep 1753433 = 1315075) B1315075
theorem B2638169 : Blo 778337 2638169 := bstep (se 2 (by rfl) ⟨989313, by rfl⟩ : syracuseStep 2638169 = 1978627) B1978627
theorem B3326359 : Blo 778337 3326359 := bstep (se 1 (by rfl) ⟨2494769, by rfl⟩ : syracuseStep 3326359 = 4989539) B4989539
theorem B7487923 : Blo 778337 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B1753523 : Blo 778337 1753523 := bstep (se 1 (by rfl) ⟨1315142, by rfl⟩ : syracuseStep 1753523 = 2630285) B2630285
theorem B1753559 : Blo 778337 1753559 := bstep (se 1 (by rfl) ⟨1315169, by rfl⟩ : syracuseStep 1753559 = 2630339) B2630339
theorem B3949073 : Blo 778337 3949073 := bstep (se 2 (by rfl) ⟨1480902, by rfl⟩ : syracuseStep 3949073 = 2961805) B2961805
theorem B9978461 : Blo 778337 9978461 := bstep (se 3 (by rfl) ⟨1870961, by rfl⟩ : syracuseStep 9978461 = 3741923) B3741923
theorem B48611933 : Blo 778337 48611933 := bstep (se 3 (by rfl) ⟨9114737, by rfl⟩ : syracuseStep 48611933 = 18229475) B18229475
theorem B1753739 : Blo 778337 1753739 := bstep (se 1 (by rfl) ⟨1315304, by rfl⟩ : syracuseStep 1753739 = 2630609) B2630609
theorem B3949235 : Blo 778337 3949235 := bstep (se 1 (by rfl) ⟨2961926, by rfl⟩ : syracuseStep 3949235 = 5923853) B5923853
theorem B1753793 : Blo 778337 1753793 := bstep (se 2 (by rfl) ⟨657672, by rfl⟩ : syracuseStep 1753793 = 1315345) B1315345
theorem B25608901 : Blo 778337 25608901 := bstep (se 4 (by rfl) ⟨2400834, by rfl⟩ : syracuseStep 25608901 = 4801669) B4801669
theorem B1754009 : Blo 778337 1754009 := bstep (se 2 (by rfl) ⟨657753, by rfl⟩ : syracuseStep 1754009 = 1315507) B1315507
theorem B1754099 : Blo 778337 1754099 := bstep (se 1 (by rfl) ⟨1315574, by rfl⟩ : syracuseStep 1754099 = 2631149) B2631149
theorem B1754135 : Blo 778337 1754135 := bstep (se 1 (by rfl) ⟨1315601, by rfl⟩ : syracuseStep 1754135 = 2631203) B2631203
theorem B2638871 : Blo 778337 2638871 := bstep (se 1 (by rfl) ⟨1979153, by rfl⟩ : syracuseStep 2638871 = 3958307) B3958307
theorem B1754315 : Blo 778337 1754315 := bstep (se 1 (by rfl) ⟨1315736, by rfl⟩ : syracuseStep 1754315 = 2631473) B2631473
theorem B1754369 : Blo 778337 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B1852723 : Blo 778337 1852723 := bstep (se 1 (by rfl) ⟨1389542, by rfl⟩ : syracuseStep 1852723 = 2779085) B2779085
theorem B5064067 : Blo 778337 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B1754585 : Blo 778337 1754585 := bstep (se 2 (by rfl) ⟨657969, by rfl⟩ : syracuseStep 1754585 = 1315939) B1315939
theorem B3556867 : Blo 778337 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B1754675 : Blo 778337 1754675 := bstep (se 1 (by rfl) ⟨1316006, by rfl⟩ : syracuseStep 1754675 = 2632013) B2632013
theorem B2639411 : Blo 778337 2639411 := bstep (se 1 (by rfl) ⟨1979558, by rfl⟩ : syracuseStep 2639411 = 3959117) B3959117
theorem B1754711 : Blo 778337 1754711 := bstep (se 1 (by rfl) ⟨1316033, by rfl⟩ : syracuseStep 1754711 = 2632067) B2632067
theorem B1754891 : Blo 778337 1754891 := bstep (se 1 (by rfl) ⟨1316168, by rfl⟩ : syracuseStep 1754891 = 2632337) B2632337
theorem B1754945 : Blo 778337 1754945 := bstep (se 2 (by rfl) ⟨658104, by rfl⟩ : syracuseStep 1754945 = 1316209) B1316209
theorem B2639681 : Blo 778337 2639681 := bstep (se 2 (by rfl) ⟨989880, by rfl⟩ : syracuseStep 2639681 = 1979761) B1979761
theorem B3753803 : Blo 778337 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B3163997 : Blo 778337 3163997 := bstep (se 3 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 3163997 = 1186499) B1186499
theorem B4507571 : Blo 778337 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B1755161 : Blo 778337 1755161 := bstep (se 2 (by rfl) ⟨658185, by rfl⟩ : syracuseStep 1755161 = 1316371) B1316371
theorem B12634181 : Blo 778337 12634181 := bstep (se 4 (by rfl) ⟨1184454, by rfl⟩ : syracuseStep 12634181 = 2368909) B2368909
theorem B1755251 : Blo 778337 1755251 := bstep (se 1 (by rfl) ⟨1316438, by rfl⟩ : syracuseStep 1755251 = 2632877) B2632877
theorem B1755287 : Blo 778337 1755287 := bstep (se 1 (by rfl) ⟨1316465, by rfl⟩ : syracuseStep 1755287 = 2632931) B2632931
theorem B1689751 : Blo 778337 1689751 := bstep (se 1 (by rfl) ⟨1267313, by rfl⟩ : syracuseStep 1689751 = 2534627) B2534627
theorem B903403 : Blo 778337 903403 := bstep (se 1 (by rfl) ⟨677552, by rfl⟩ : syracuseStep 903403 = 1355105) B1355105
theorem B1755467 : Blo 778337 1755467 := bstep (se 1 (by rfl) ⟨1316600, by rfl⟩ : syracuseStep 1755467 = 2633201) B2633201
theorem B2640221 : Blo 778337 2640221 := bstep (se 3 (by rfl) ⟨495041, by rfl⟩ : syracuseStep 2640221 = 990083) B990083
theorem B1755521 : Blo 778337 1755521 := bstep (se 2 (by rfl) ⟨658320, by rfl⟩ : syracuseStep 1755521 = 1316641) B1316641
theorem B3754457 : Blo 778337 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B2968109 : Blo 778337 2968109 := bstep (se 3 (by rfl) ⟨556520, by rfl⟩ : syracuseStep 2968109 = 1113041) B1113041
theorem B3951179 : Blo 778337 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B1755737 : Blo 778337 1755737 := bstep (se 2 (by rfl) ⟨658401, by rfl⟩ : syracuseStep 1755737 = 1316803) B1316803
theorem B1755827 : Blo 778337 1755827 := bstep (se 1 (by rfl) ⟨1316870, by rfl⟩ : syracuseStep 1755827 = 2633741) B2633741
theorem B1755863 : Blo 778337 1755863 := bstep (se 1 (by rfl) ⟨1316897, by rfl⟩ : syracuseStep 1755863 = 2633795) B2633795
theorem B1756043 : Blo 778337 1756043 := bstep (se 1 (by rfl) ⟨1317032, by rfl⟩ : syracuseStep 1756043 = 2634065) B2634065
theorem B1756097 : Blo 778337 1756097 := bstep (se 2 (by rfl) ⟨658536, by rfl⟩ : syracuseStep 1756097 = 1317073) B1317073
theorem B1756313 : Blo 778337 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B1756403 : Blo 778337 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B1756439 : Blo 778337 1756439 := bstep (se 1 (by rfl) ⟨1317329, by rfl⟩ : syracuseStep 1756439 = 2634659) B2634659
theorem B4443437 : Blo 778337 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B2968883 : Blo 778337 2968883 := bstep (se 1 (by rfl) ⟨2226662, by rfl⟩ : syracuseStep 2968883 = 4453325) B4453325
theorem B6671717 : Blo 778337 6671717 := bstep (se 4 (by rfl) ⟨625473, by rfl⟩ : syracuseStep 6671717 = 1250947) B1250947
theorem B1756619 : Blo 778337 1756619 := bstep (se 1 (by rfl) ⟨1317464, by rfl⟩ : syracuseStep 1756619 = 2634929) B2634929
theorem B1756673 : Blo 778337 1756673 := bstep (se 2 (by rfl) ⟨658752, by rfl⟩ : syracuseStep 1756673 = 1317505) B1317505
theorem B1756889 : Blo 778337 1756889 := bstep (se 2 (by rfl) ⟨658833, by rfl⟩ : syracuseStep 1756889 = 1317667) B1317667
theorem B1756979 : Blo 778337 1756979 := bstep (se 1 (by rfl) ⟨1317734, by rfl⟩ : syracuseStep 1756979 = 2635469) B2635469
theorem B1757015 : Blo 778337 1757015 := bstep (se 1 (by rfl) ⟨1317761, by rfl⟩ : syracuseStep 1757015 = 2635523) B2635523
theorem B6311773 : Blo 778337 6311773 := bstep (se 3 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 6311773 = 2366915) B2366915
theorem B1953715 : Blo 778337 1953715 := bstep (se 1 (by rfl) ⟨1465286, by rfl⟩ : syracuseStep 1953715 = 2930573) B2930573
theorem B1757195 : Blo 778337 1757195 := bstep (se 1 (by rfl) ⟨1317896, by rfl⟩ : syracuseStep 1757195 = 2635793) B2635793
theorem B6672401 : Blo 778337 6672401 := bstep (se 2 (by rfl) ⟨2502150, by rfl⟩ : syracuseStep 6672401 = 5004301) B5004301
theorem B1757249 : Blo 778337 1757249 := bstep (se 2 (by rfl) ⟨658968, by rfl⟩ : syracuseStep 1757249 = 1317937) B1317937
theorem B2805853 : Blo 778337 2805853 := bstep (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) B1052195
theorem B1167563 : Blo 778337 1167563 := bstep (se 1 (by rfl) ⟨875672, by rfl⟩ : syracuseStep 1167563 = 1751345) B1751345
theorem B1167575 : Blo 778337 1167575 := bstep (se 1 (by rfl) ⟨875681, by rfl⟩ : syracuseStep 1167575 = 1751363) B1751363
theorem B5918993 : Blo 778337 5918993 := bstep (se 2 (by rfl) ⟨2219622, by rfl⟩ : syracuseStep 5918993 = 4439245) B4439245
theorem B1167641 : Blo 778337 1167641 := bstep (se 2 (by rfl) ⟨437865, by rfl⟩ : syracuseStep 1167641 = 875731) B875731
theorem B1757465 : Blo 778337 1757465 := bstep (se 2 (by rfl) ⟨659049, by rfl⟩ : syracuseStep 1757465 = 1318099) B1318099
theorem B3952961 : Blo 778337 3952961 := bstep (se 2 (by rfl) ⟨1482360, by rfl⟩ : syracuseStep 3952961 = 2964721) B2964721
theorem B1757555 : Blo 778337 1757555 := bstep (se 1 (by rfl) ⟨1318166, by rfl⟩ : syracuseStep 1757555 = 2636333) B2636333
theorem B1167755 : Blo 778337 1167755 := bstep (se 1 (by rfl) ⟨875816, by rfl⟩ : syracuseStep 1167755 = 1751633) B1751633
theorem B1167767 : Blo 778337 1167767 := bstep (se 1 (by rfl) ⟨875825, by rfl⟩ : syracuseStep 1167767 = 1751651) B1751651
theorem B1757591 : Blo 778337 1757591 := bstep (se 1 (by rfl) ⟨1318193, by rfl⟩ : syracuseStep 1757591 = 2636387) B2636387
theorem B1167833 : Blo 778337 1167833 := bstep (se 2 (by rfl) ⟨437937, by rfl⟩ : syracuseStep 1167833 = 875875) B875875
theorem B1167947 : Blo 778337 1167947 := bstep (se 1 (by rfl) ⟨875960, by rfl⟩ : syracuseStep 1167947 = 1751921) B1751921
theorem B1757771 : Blo 778337 1757771 := bstep (se 1 (by rfl) ⟨1318328, by rfl⟩ : syracuseStep 1757771 = 2636657) B2636657
theorem B1167959 : Blo 778337 1167959 := bstep (se 1 (by rfl) ⟨875969, by rfl⟩ : syracuseStep 1167959 = 1751939) B1751939
theorem B1757825 : Blo 778337 1757825 := bstep (se 2 (by rfl) ⟨659184, by rfl⟩ : syracuseStep 1757825 = 1318369) B1318369
theorem B1168025 : Blo 778337 1168025 := bstep (se 2 (by rfl) ⟨438009, by rfl⟩ : syracuseStep 1168025 = 876019) B876019
theorem B3330733 : Blo 778337 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B2970371 : Blo 778337 2970371 := bstep (se 1 (by rfl) ⟨2227778, by rfl⟩ : syracuseStep 2970371 = 4455557) B4455557
theorem B1168139 : Blo 778337 1168139 := bstep (se 1 (by rfl) ⟨876104, by rfl⟩ : syracuseStep 1168139 = 1752209) B1752209
theorem B1168151 : Blo 778337 1168151 := bstep (se 1 (by rfl) ⟨876113, by rfl⟩ : syracuseStep 1168151 = 1752227) B1752227
theorem B4510529 : Blo 778337 4510529 := bstep (se 2 (by rfl) ⟨1691448, by rfl⟩ : syracuseStep 4510529 = 3382897) B3382897
theorem B1168217 : Blo 778337 1168217 := bstep (se 2 (by rfl) ⟨438081, by rfl⟩ : syracuseStep 1168217 = 876163) B876163
theorem B1758041 : Blo 778337 1758041 := bstep (se 2 (by rfl) ⟨659265, by rfl⟩ : syracuseStep 1758041 = 1318531) B1318531
theorem B1758131 : Blo 778337 1758131 := bstep (se 1 (by rfl) ⟨1318598, by rfl⟩ : syracuseStep 1758131 = 2637197) B2637197
theorem B1168331 : Blo 778337 1168331 := bstep (se 1 (by rfl) ⟨876248, by rfl⟩ : syracuseStep 1168331 = 1752497) B1752497
theorem B1168343 : Blo 778337 1168343 := bstep (se 1 (by rfl) ⟨876257, by rfl⟩ : syracuseStep 1168343 = 1752515) B1752515
theorem B1758167 : Blo 778337 1758167 := bstep (se 1 (by rfl) ⟨1318625, by rfl⟩ : syracuseStep 1758167 = 2637251) B2637251
theorem B1168409 : Blo 778337 1168409 := bstep (se 2 (by rfl) ⟨438153, by rfl⟩ : syracuseStep 1168409 = 876307) B876307
theorem B1168523 : Blo 778337 1168523 := bstep (se 1 (by rfl) ⟨876392, by rfl⟩ : syracuseStep 1168523 = 1752785) B1752785
theorem B1758347 : Blo 778337 1758347 := bstep (se 1 (by rfl) ⟨1318760, by rfl⟩ : syracuseStep 1758347 = 2637521) B2637521
theorem B1168535 : Blo 778337 1168535 := bstep (se 1 (by rfl) ⟨876401, by rfl⟩ : syracuseStep 1168535 = 1752803) B1752803
theorem B3003571 : Blo 778337 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B36066485 : Blo 778337 36066485 := bstep (se 5 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 36066485 = 3381233) B3381233
theorem B1758401 : Blo 778337 1758401 := bstep (se 2 (by rfl) ⟨659400, by rfl⟩ : syracuseStep 1758401 = 1318801) B1318801
theorem B1168601 : Blo 778337 1168601 := bstep (se 2 (by rfl) ⟨438225, by rfl⟩ : syracuseStep 1168601 = 876451) B876451
theorem B939287 : Blo 778337 939287 := bstep (se 1 (by rfl) ⟨704465, by rfl⟩ : syracuseStep 939287 = 1408931) B1408931
theorem B1168715 : Blo 778337 1168715 := bstep (se 1 (by rfl) ⟨876536, by rfl⟩ : syracuseStep 1168715 = 1753073) B1753073
theorem B1168727 : Blo 778337 1168727 := bstep (se 1 (by rfl) ⟨876545, by rfl⟩ : syracuseStep 1168727 = 1753091) B1753091
theorem B1168793 : Blo 778337 1168793 := bstep (se 2 (by rfl) ⟨438297, by rfl⟩ : syracuseStep 1168793 = 876595) B876595
theorem B1758617 : Blo 778337 1758617 := bstep (se 2 (by rfl) ⟨659481, by rfl⟩ : syracuseStep 1758617 = 1318963) B1318963
theorem B939479 : Blo 778337 939479 := bstep (se 1 (by rfl) ⟨704609, by rfl⟩ : syracuseStep 939479 = 1409219) B1409219
theorem B1758707 : Blo 778337 1758707 := bstep (se 1 (by rfl) ⟨1319030, by rfl⟩ : syracuseStep 1758707 = 2638061) B2638061
theorem B1168907 : Blo 778337 1168907 := bstep (se 1 (by rfl) ⟨876680, by rfl⟩ : syracuseStep 1168907 = 1753361) B1753361
theorem B3036689 : Blo 778337 3036689 := bstep (se 2 (by rfl) ⟨1138758, by rfl⟩ : syracuseStep 3036689 = 2277517) B2277517
theorem B1168919 : Blo 778337 1168919 := bstep (se 1 (by rfl) ⟨876689, by rfl⟩ : syracuseStep 1168919 = 1753379) B1753379
theorem B1758743 : Blo 778337 1758743 := bstep (se 1 (by rfl) ⟨1319057, by rfl⟩ : syracuseStep 1758743 = 2638115) B2638115
theorem B939595 : Blo 778337 939595 := bstep (se 1 (by rfl) ⟨704696, by rfl⟩ : syracuseStep 939595 = 1409393) B1409393
theorem B1168985 : Blo 778337 1168985 := bstep (se 2 (by rfl) ⟨438369, by rfl⟩ : syracuseStep 1168985 = 876739) B876739
theorem B1169099 : Blo 778337 1169099 := bstep (se 1 (by rfl) ⟨876824, by rfl⟩ : syracuseStep 1169099 = 1753649) B1753649
theorem B1758923 : Blo 778337 1758923 := bstep (se 1 (by rfl) ⟨1319192, by rfl⟩ : syracuseStep 1758923 = 2638385) B2638385
theorem B1005259 : Blo 778337 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B1169111 : Blo 778337 1169111 := bstep (se 1 (by rfl) ⟨876833, by rfl⟩ : syracuseStep 1169111 = 1753667) B1753667
theorem B1758977 : Blo 778337 1758977 := bstep (se 2 (by rfl) ⟨659616, by rfl⟩ : syracuseStep 1758977 = 1319233) B1319233
theorem B7493381 : Blo 778337 7493381 := bstep (se 4 (by rfl) ⟨702504, by rfl⟩ : syracuseStep 7493381 = 1405009) B1405009
theorem B1169177 : Blo 778337 1169177 := bstep (se 2 (by rfl) ⟨438441, by rfl⟩ : syracuseStep 1169177 = 876883) B876883
theorem B1169291 : Blo 778337 1169291 := bstep (se 1 (by rfl) ⟨876968, by rfl⟩ : syracuseStep 1169291 = 1753937) B1753937
theorem B1169303 : Blo 778337 1169303 := bstep (se 1 (by rfl) ⟨876977, by rfl⟩ : syracuseStep 1169303 = 1753955) B1753955
theorem B1169369 : Blo 778337 1169369 := bstep (se 2 (by rfl) ⟨438513, by rfl⟩ : syracuseStep 1169369 = 877027) B877027
theorem B1759193 : Blo 778337 1759193 := bstep (se 2 (by rfl) ⟨659697, by rfl⟩ : syracuseStep 1759193 = 1319395) B1319395
theorem B1759283 : Blo 778337 1759283 := bstep (se 1 (by rfl) ⟨1319462, by rfl⟩ : syracuseStep 1759283 = 2638925) B2638925
theorem B1169483 : Blo 778337 1169483 := bstep (se 1 (by rfl) ⟨877112, by rfl⟩ : syracuseStep 1169483 = 1754225) B1754225
theorem B1169495 : Blo 778337 1169495 := bstep (se 1 (by rfl) ⟨877121, by rfl⟩ : syracuseStep 1169495 = 1754243) B1754243
theorem B1759319 : Blo 778337 1759319 := bstep (se 1 (by rfl) ⟨1319489, by rfl⟩ : syracuseStep 1759319 = 2638979) B2638979
theorem B1169561 : Blo 778337 1169561 := bstep (se 2 (by rfl) ⟨438585, by rfl⟩ : syracuseStep 1169561 = 877171) B877171
theorem B3954905 : Blo 778337 3954905 := bstep (se 2 (by rfl) ⟨1483089, by rfl⟩ : syracuseStep 3954905 = 2966179) B2966179
theorem B1169675 : Blo 778337 1169675 := bstep (se 1 (by rfl) ⟨877256, by rfl⟩ : syracuseStep 1169675 = 1754513) B1754513
theorem B1759499 : Blo 778337 1759499 := bstep (se 1 (by rfl) ⟨1319624, by rfl⟩ : syracuseStep 1759499 = 2639249) B2639249
theorem B1169687 : Blo 778337 1169687 := bstep (se 1 (by rfl) ⟨877265, by rfl⟩ : syracuseStep 1169687 = 1754531) B1754531
theorem B1759553 : Blo 778337 1759553 := bstep (se 2 (by rfl) ⟨659832, by rfl⟩ : syracuseStep 1759553 = 1319665) B1319665
theorem B1169753 : Blo 778337 1169753 := bstep (se 2 (by rfl) ⟨438657, by rfl⟩ : syracuseStep 1169753 = 877315) B877315
theorem B3332441 : Blo 778337 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B1169867 : Blo 778337 1169867 := bstep (se 1 (by rfl) ⟨877400, by rfl⟩ : syracuseStep 1169867 = 1754801) B1754801
theorem B1169879 : Blo 778337 1169879 := bstep (se 1 (by rfl) ⟨877409, by rfl⟩ : syracuseStep 1169879 = 1754819) B1754819
theorem B11983373 : Blo 778337 11983373 := bstep (se 3 (by rfl) ⟨2246882, by rfl⟩ : syracuseStep 11983373 = 4493765) B4493765
theorem B1169945 : Blo 778337 1169945 := bstep (se 2 (by rfl) ⟨438729, by rfl⟩ : syracuseStep 1169945 = 877459) B877459
theorem B1759769 : Blo 778337 1759769 := bstep (se 2 (by rfl) ⟨659913, by rfl⟩ : syracuseStep 1759769 = 1319827) B1319827
theorem B1759859 : Blo 778337 1759859 := bstep (se 1 (by rfl) ⟨1319894, by rfl⟩ : syracuseStep 1759859 = 2639789) B2639789
theorem B1170059 : Blo 778337 1170059 := bstep (se 1 (by rfl) ⟨877544, by rfl⟩ : syracuseStep 1170059 = 1755089) B1755089
theorem B1170071 : Blo 778337 1170071 := bstep (se 1 (by rfl) ⟨877553, by rfl⟩ : syracuseStep 1170071 = 1755107) B1755107
theorem B1759895 : Blo 778337 1759895 := bstep (se 1 (by rfl) ⟨1319921, by rfl⟩ : syracuseStep 1759895 = 2639843) B2639843
theorem B1170137 : Blo 778337 1170137 := bstep (se 2 (by rfl) ⟨438801, by rfl⟩ : syracuseStep 1170137 = 877603) B877603
theorem B5003993 : Blo 778337 5003993 := bstep (se 2 (by rfl) ⟨1876497, by rfl⟩ : syracuseStep 5003993 = 3752995) B3752995
theorem B1170251 : Blo 778337 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B1760075 : Blo 778337 1760075 := bstep (se 1 (by rfl) ⟨1320056, by rfl⟩ : syracuseStep 1760075 = 2640113) B2640113
theorem B1170263 : Blo 778337 1170263 := bstep (se 1 (by rfl) ⟨877697, by rfl⟩ : syracuseStep 1170263 = 1755395) B1755395
theorem B1760129 : Blo 778337 1760129 := bstep (se 2 (by rfl) ⟨660048, by rfl⟩ : syracuseStep 1760129 = 1320097) B1320097
theorem B1170329 : Blo 778337 1170329 := bstep (se 2 (by rfl) ⟨438873, by rfl⟩ : syracuseStep 1170329 = 877747) B877747
theorem B104225753 : Blo 778337 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B1170443 : Blo 778337 1170443 := bstep (se 1 (by rfl) ⟨877832, by rfl⟩ : syracuseStep 1170443 = 1755665) B1755665
theorem B1170455 : Blo 778337 1170455 := bstep (se 1 (by rfl) ⟨877841, by rfl⟩ : syracuseStep 1170455 = 1755683) B1755683
theorem B10017827 : Blo 778337 10017827 := bstep (se 1 (by rfl) ⟨7513370, by rfl⟩ : syracuseStep 10017827 = 15026741) B15026741
theorem B1170521 : Blo 778337 1170521 := bstep (se 2 (by rfl) ⟨438945, by rfl⟩ : syracuseStep 1170521 = 877891) B877891
theorem B875659 : Blo 778337 875659 := bstep (se 1 (by rfl) ⟨656744, by rfl⟩ : syracuseStep 875659 = 1313489) B1313489
theorem B1170635 : Blo 778337 1170635 := bstep (se 1 (by rfl) ⟨877976, by rfl⟩ : syracuseStep 1170635 = 1755953) B1755953
theorem B1170647 : Blo 778337 1170647 := bstep (se 1 (by rfl) ⟨877985, by rfl⟩ : syracuseStep 1170647 = 1755971) B1755971
theorem B875767 : Blo 778337 875767 := bstep (se 1 (by rfl) ⟨656825, by rfl⟩ : syracuseStep 875767 = 1313651) B1313651
theorem B1170713 : Blo 778337 1170713 := bstep (se 2 (by rfl) ⟨439017, by rfl⟩ : syracuseStep 1170713 = 878035) B878035
theorem B2219339 : Blo 778337 2219339 := bstep (se 1 (by rfl) ⟨1664504, by rfl⟩ : syracuseStep 2219339 = 3329009) B3329009
theorem B1170827 : Blo 778337 1170827 := bstep (se 1 (by rfl) ⟨878120, by rfl⟩ : syracuseStep 1170827 = 1756241) B1756241
theorem B1170839 : Blo 778337 1170839 := bstep (se 1 (by rfl) ⟨878129, by rfl⟩ : syracuseStep 1170839 = 1756259) B1756259
theorem B875947 : Blo 778337 875947 := bstep (se 1 (by rfl) ⟨656960, by rfl⟩ : syracuseStep 875947 = 1313921) B1313921
theorem B3857843 : Blo 778337 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B1170905 : Blo 778337 1170905 := bstep (se 2 (by rfl) ⟨439089, by rfl⟩ : syracuseStep 1170905 = 878179) B878179
theorem B876055 : Blo 778337 876055 := bstep (se 1 (by rfl) ⟨657041, by rfl⟩ : syracuseStep 876055 = 1314083) B1314083
theorem B3333707 : Blo 778337 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B1171019 : Blo 778337 1171019 := bstep (se 1 (by rfl) ⟨878264, by rfl⟩ : syracuseStep 1171019 = 1756529) B1756529
theorem B1171031 : Blo 778337 1171031 := bstep (se 1 (by rfl) ⟨878273, by rfl⟩ : syracuseStep 1171031 = 1756547) B1756547
theorem B1171097 : Blo 778337 1171097 := bstep (se 2 (by rfl) ⟨439161, by rfl⟩ : syracuseStep 1171097 = 878323) B878323
theorem B876235 : Blo 778337 876235 := bstep (se 1 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 876235 = 1314353) B1314353
theorem B2219737 : Blo 778337 2219737 := bstep (se 2 (by rfl) ⟨832401, by rfl⟩ : syracuseStep 2219737 = 1664803) B1664803
theorem B1171211 : Blo 778337 1171211 := bstep (se 1 (by rfl) ⟨878408, by rfl⟩ : syracuseStep 1171211 = 1756817) B1756817
theorem B1171223 : Blo 778337 1171223 := bstep (se 1 (by rfl) ⟨878417, by rfl⟩ : syracuseStep 1171223 = 1756835) B1756835
theorem B3956525 : Blo 778337 3956525 := bstep (se 3 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 3956525 = 1483697) B1483697
theorem B876343 : Blo 778337 876343 := bstep (se 1 (by rfl) ⟨657257, by rfl⟩ : syracuseStep 876343 = 1314515) B1314515
theorem B19259201 : Blo 778337 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B1171289 : Blo 778337 1171289 := bstep (se 2 (by rfl) ⟨439233, by rfl⟩ : syracuseStep 1171289 = 878467) B878467
theorem B3334067 : Blo 778337 3334067 := bstep (se 1 (by rfl) ⟨2500550, by rfl⟩ : syracuseStep 3334067 = 5001101) B5001101
theorem B1171403 : Blo 778337 1171403 := bstep (se 1 (by rfl) ⟨878552, by rfl⟩ : syracuseStep 1171403 = 1757105) B1757105
theorem B1171415 : Blo 778337 1171415 := bstep (se 1 (by rfl) ⟨878561, by rfl⟩ : syracuseStep 1171415 = 1757123) B1757123
theorem B2809817 : Blo 778337 2809817 := bstep (se 2 (by rfl) ⟨1053681, by rfl⟩ : syracuseStep 2809817 = 2107363) B2107363
theorem B876523 : Blo 778337 876523 := bstep (se 1 (by rfl) ⟨657392, by rfl⟩ : syracuseStep 876523 = 1314785) B1314785
theorem B1663001 : Blo 778337 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B1171481 : Blo 778337 1171481 := bstep (se 2 (by rfl) ⟨439305, by rfl⟩ : syracuseStep 1171481 = 878611) B878611
theorem B5922881 : Blo 778337 5922881 := bstep (se 2 (by rfl) ⟨2221080, by rfl⟩ : syracuseStep 5922881 = 4442161) B4442161
theorem B876631 : Blo 778337 876631 := bstep (se 1 (by rfl) ⟨657473, by rfl⟩ : syracuseStep 876631 = 1314947) B1314947
theorem B778347 : Blo 778337 778347 := bstep (se 1 (by rfl) ⟨583760, by rfl⟩ : syracuseStep 778347 = 1167521) B1167521
theorem B778359 : Blo 778337 778359 := bstep (se 1 (by rfl) ⟨583769, by rfl⟩ : syracuseStep 778359 = 1167539) B1167539
theorem B778379 : Blo 778337 778379 := bstep (se 1 (by rfl) ⟨583784, by rfl⟩ : syracuseStep 778379 = 1167569) B1167569
theorem B1171595 : Blo 778337 1171595 := bstep (se 1 (by rfl) ⟨878696, by rfl⟩ : syracuseStep 1171595 = 1757393) B1757393
theorem B778391 : Blo 778337 778391 := bstep (se 1 (by rfl) ⟨583793, by rfl⟩ : syracuseStep 778391 = 1167587) B1167587
theorem B1171607 : Blo 778337 1171607 := bstep (se 1 (by rfl) ⟨878705, by rfl⟩ : syracuseStep 1171607 = 1757411) B1757411
theorem B778411 : Blo 778337 778411 := bstep (se 1 (by rfl) ⟨583808, by rfl⟩ : syracuseStep 778411 = 1167617) B1167617
theorem B778423 : Blo 778337 778423 := bstep (se 1 (by rfl) ⟨583817, by rfl⟩ : syracuseStep 778423 = 1167635) B1167635
theorem B778443 : Blo 778337 778443 := bstep (se 1 (by rfl) ⟨583832, by rfl⟩ : syracuseStep 778443 = 1167665) B1167665
theorem B778455 : Blo 778337 778455 := bstep (se 1 (by rfl) ⟨583841, by rfl⟩ : syracuseStep 778455 = 1167683) B1167683
theorem B1171673 : Blo 778337 1171673 := bstep (se 2 (by rfl) ⟨439377, by rfl⟩ : syracuseStep 1171673 = 878755) B878755
theorem B778475 : Blo 778337 778475 := bstep (se 1 (by rfl) ⟨583856, by rfl⟩ : syracuseStep 778475 = 1167713) B1167713
theorem B778487 : Blo 778337 778487 := bstep (se 1 (by rfl) ⟨583865, by rfl⟩ : syracuseStep 778487 = 1167731) B1167731
theorem B6086917 : Blo 778337 6086917 := bstep (se 4 (by rfl) ⟨570648, by rfl⟩ : syracuseStep 6086917 = 1141297) B1141297
theorem B778507 : Blo 778337 778507 := bstep (se 1 (by rfl) ⟨583880, by rfl⟩ : syracuseStep 778507 = 1167761) B1167761
theorem B876811 : Blo 778337 876811 := bstep (se 1 (by rfl) ⟨657608, by rfl⟩ : syracuseStep 876811 = 1315217) B1315217
theorem B778519 : Blo 778337 778519 := bstep (se 1 (by rfl) ⟨583889, by rfl⟩ : syracuseStep 778519 = 1167779) B1167779
theorem B778539 : Blo 778337 778539 := bstep (se 1 (by rfl) ⟨583904, by rfl⟩ : syracuseStep 778539 = 1167809) B1167809
theorem B778551 : Blo 778337 778551 := bstep (se 1 (by rfl) ⟨583913, by rfl⟩ : syracuseStep 778551 = 1167827) B1167827
theorem B5005633 : Blo 778337 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B778571 : Blo 778337 778571 := bstep (se 1 (by rfl) ⟨583928, by rfl⟩ : syracuseStep 778571 = 1167857) B1167857
theorem B1171787 : Blo 778337 1171787 := bstep (se 1 (by rfl) ⟨878840, by rfl⟩ : syracuseStep 1171787 = 1757681) B1757681
theorem B778583 : Blo 778337 778583 := bstep (se 1 (by rfl) ⟨583937, by rfl⟩ : syracuseStep 778583 = 1167875) B1167875
theorem B1171799 : Blo 778337 1171799 := bstep (se 1 (by rfl) ⟨878849, by rfl⟩ : syracuseStep 1171799 = 1757699) B1757699
theorem B778603 : Blo 778337 778603 := bstep (se 1 (by rfl) ⟨583952, by rfl⟩ : syracuseStep 778603 = 1167905) B1167905
theorem B778615 : Blo 778337 778615 := bstep (se 1 (by rfl) ⟨583961, by rfl⟩ : syracuseStep 778615 = 1167923) B1167923
theorem B876919 : Blo 778337 876919 := bstep (se 1 (by rfl) ⟨657689, by rfl⟩ : syracuseStep 876919 = 1315379) B1315379
theorem B778635 : Blo 778337 778635 := bstep (se 1 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 778635 = 1167953) B1167953
theorem B778647 : Blo 778337 778647 := bstep (se 1 (by rfl) ⟨583985, by rfl⟩ : syracuseStep 778647 = 1167971) B1167971
theorem B1171865 : Blo 778337 1171865 := bstep (se 2 (by rfl) ⟨439449, by rfl⟩ : syracuseStep 1171865 = 878899) B878899
theorem B778667 : Blo 778337 778667 := bstep (se 1 (by rfl) ⟨584000, by rfl⟩ : syracuseStep 778667 = 1168001) B1168001
theorem B1663411 : Blo 778337 1663411 := bstep (se 1 (by rfl) ⟨1247558, by rfl⟩ : syracuseStep 1663411 = 2495117) B2495117
theorem B778679 : Blo 778337 778679 := bstep (se 1 (by rfl) ⟨584009, by rfl⟩ : syracuseStep 778679 = 1168019) B1168019
theorem B778699 : Blo 778337 778699 := bstep (se 1 (by rfl) ⟨584024, by rfl⟩ : syracuseStep 778699 = 1168049) B1168049
theorem B778711 : Blo 778337 778711 := bstep (se 1 (by rfl) ⟨584033, by rfl⟩ : syracuseStep 778711 = 1168067) B1168067
theorem B778731 : Blo 778337 778731 := bstep (se 1 (by rfl) ⟨584048, by rfl⟩ : syracuseStep 778731 = 1168097) B1168097
theorem B778743 : Blo 778337 778743 := bstep (se 1 (by rfl) ⟨584057, by rfl⟩ : syracuseStep 778743 = 1168115) B1168115
theorem B778763 : Blo 778337 778763 := bstep (se 1 (by rfl) ⟨584072, by rfl⟩ : syracuseStep 778763 = 1168145) B1168145
theorem B1171979 : Blo 778337 1171979 := bstep (se 1 (by rfl) ⟨878984, by rfl⟩ : syracuseStep 1171979 = 1757969) B1757969
theorem B778775 : Blo 778337 778775 := bstep (se 1 (by rfl) ⟨584081, by rfl⟩ : syracuseStep 778775 = 1168163) B1168163
theorem B1171991 : Blo 778337 1171991 := bstep (se 1 (by rfl) ⟨878993, by rfl⟩ : syracuseStep 1171991 = 1757987) B1757987
theorem B7103011 : Blo 778337 7103011 := bstep (se 1 (by rfl) ⟨5327258, by rfl⟩ : syracuseStep 7103011 = 10654517) B10654517
theorem B778795 : Blo 778337 778795 := bstep (se 1 (by rfl) ⟨584096, by rfl⟩ : syracuseStep 778795 = 1168193) B1168193
theorem B877099 : Blo 778337 877099 := bstep (se 1 (by rfl) ⟨657824, by rfl⟩ : syracuseStep 877099 = 1315649) B1315649
theorem B778807 : Blo 778337 778807 := bstep (se 1 (by rfl) ⟨584105, by rfl⟩ : syracuseStep 778807 = 1168211) B1168211
theorem B778827 : Blo 778337 778827 := bstep (se 1 (by rfl) ⟨584120, by rfl⟩ : syracuseStep 778827 = 1168241) B1168241
theorem B778839 : Blo 778337 778839 := bstep (se 1 (by rfl) ⟨584129, by rfl⟩ : syracuseStep 778839 = 1168259) B1168259
theorem B1172057 : Blo 778337 1172057 := bstep (se 2 (by rfl) ⟨439521, by rfl⟩ : syracuseStep 1172057 = 879043) B879043
theorem B778859 : Blo 778337 778859 := bstep (se 1 (by rfl) ⟨584144, by rfl⟩ : syracuseStep 778859 = 1168289) B1168289
theorem B778871 : Blo 778337 778871 := bstep (se 1 (by rfl) ⟨584153, by rfl⟩ : syracuseStep 778871 = 1168307) B1168307
theorem B778891 : Blo 778337 778891 := bstep (se 1 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 778891 = 1168337) B1168337
theorem B778903 : Blo 778337 778903 := bstep (se 1 (by rfl) ⟨584177, by rfl⟩ : syracuseStep 778903 = 1168355) B1168355
theorem B877207 : Blo 778337 877207 := bstep (se 1 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 877207 = 1315811) B1315811
theorem B778923 : Blo 778337 778923 := bstep (se 1 (by rfl) ⟨584192, by rfl⟩ : syracuseStep 778923 = 1168385) B1168385
theorem B778935 : Blo 778337 778935 := bstep (se 1 (by rfl) ⟨584201, by rfl⟩ : syracuseStep 778935 = 1168403) B1168403
theorem B778955 : Blo 778337 778955 := bstep (se 1 (by rfl) ⟨584216, by rfl⟩ : syracuseStep 778955 = 1168433) B1168433
theorem B1172171 : Blo 778337 1172171 := bstep (se 1 (by rfl) ⟨879128, by rfl⟩ : syracuseStep 1172171 = 1758257) B1758257
theorem B778967 : Blo 778337 778967 := bstep (se 1 (by rfl) ⟨584225, by rfl⟩ : syracuseStep 778967 = 1168451) B1168451
theorem B1172183 : Blo 778337 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B778987 : Blo 778337 778987 := bstep (se 1 (by rfl) ⟨584240, by rfl⟩ : syracuseStep 778987 = 1168481) B1168481
theorem B778999 : Blo 778337 778999 := bstep (se 1 (by rfl) ⟨584249, by rfl⟩ : syracuseStep 778999 = 1168499) B1168499
theorem B779019 : Blo 778337 779019 := bstep (se 1 (by rfl) ⟨584264, by rfl⟩ : syracuseStep 779019 = 1168529) B1168529
theorem B4743953 : Blo 778337 4743953 := bstep (se 2 (by rfl) ⟨1778982, by rfl⟩ : syracuseStep 4743953 = 3557965) B3557965
theorem B779031 : Blo 778337 779031 := bstep (se 1 (by rfl) ⟨584273, by rfl⟩ : syracuseStep 779031 = 1168547) B1168547
theorem B1172249 : Blo 778337 1172249 := bstep (se 2 (by rfl) ⟨439593, by rfl⟩ : syracuseStep 1172249 = 879187) B879187
theorem B779051 : Blo 778337 779051 := bstep (se 1 (by rfl) ⟨584288, by rfl⟩ : syracuseStep 779051 = 1168577) B1168577
theorem B779063 : Blo 778337 779063 := bstep (se 1 (by rfl) ⟨584297, by rfl⟩ : syracuseStep 779063 = 1168595) B1168595
theorem B779083 : Blo 778337 779083 := bstep (se 1 (by rfl) ⟨584312, by rfl⟩ : syracuseStep 779083 = 1168625) B1168625
theorem B2810699 : Blo 778337 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B877387 : Blo 778337 877387 := bstep (se 1 (by rfl) ⟨658040, by rfl⟩ : syracuseStep 877387 = 1316081) B1316081
theorem B779095 : Blo 778337 779095 := bstep (se 1 (by rfl) ⟨584321, by rfl⟩ : syracuseStep 779095 = 1168643) B1168643
theorem B779115 : Blo 778337 779115 := bstep (se 1 (by rfl) ⟨584336, by rfl⟩ : syracuseStep 779115 = 1168673) B1168673
theorem B779127 : Blo 778337 779127 := bstep (se 1 (by rfl) ⟨584345, by rfl⟩ : syracuseStep 779127 = 1168691) B1168691
theorem B779147 : Blo 778337 779147 := bstep (se 1 (by rfl) ⟨584360, by rfl⟩ : syracuseStep 779147 = 1168721) B1168721
theorem B1172363 : Blo 778337 1172363 := bstep (se 1 (by rfl) ⟨879272, by rfl⟩ : syracuseStep 1172363 = 1758545) B1758545
theorem B779159 : Blo 778337 779159 := bstep (se 1 (by rfl) ⟨584369, by rfl⟩ : syracuseStep 779159 = 1168739) B1168739
theorem B1663897 : Blo 778337 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B1172375 : Blo 778337 1172375 := bstep (se 1 (by rfl) ⟨879281, by rfl⟩ : syracuseStep 1172375 = 1758563) B1758563
theorem B779179 : Blo 778337 779179 := bstep (se 1 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 779179 = 1168769) B1168769
theorem B2220979 : Blo 778337 2220979 := bstep (se 1 (by rfl) ⟨1665734, by rfl⟩ : syracuseStep 2220979 = 3331469) B3331469
theorem B779191 : Blo 778337 779191 := bstep (se 1 (by rfl) ⟨584393, by rfl⟩ : syracuseStep 779191 = 1168787) B1168787
theorem B877495 : Blo 778337 877495 := bstep (se 1 (by rfl) ⟨658121, by rfl⟩ : syracuseStep 877495 = 1316243) B1316243
theorem B779211 : Blo 778337 779211 := bstep (se 1 (by rfl) ⟨584408, by rfl⟩ : syracuseStep 779211 = 1168817) B1168817
theorem B779223 : Blo 778337 779223 := bstep (se 1 (by rfl) ⟨584417, by rfl⟩ : syracuseStep 779223 = 1168835) B1168835
theorem B1172441 : Blo 778337 1172441 := bstep (se 2 (by rfl) ⟨439665, by rfl⟩ : syracuseStep 1172441 = 879331) B879331
theorem B779243 : Blo 778337 779243 := bstep (se 1 (by rfl) ⟨584432, by rfl⟩ : syracuseStep 779243 = 1168865) B1168865
theorem B779255 : Blo 778337 779255 := bstep (se 1 (by rfl) ⟨584441, by rfl⟩ : syracuseStep 779255 = 1168883) B1168883
theorem B779275 : Blo 778337 779275 := bstep (se 1 (by rfl) ⟨584456, by rfl⟩ : syracuseStep 779275 = 1168913) B1168913
theorem B779287 : Blo 778337 779287 := bstep (se 1 (by rfl) ⟨584465, by rfl⟩ : syracuseStep 779287 = 1168931) B1168931
theorem B779307 : Blo 778337 779307 := bstep (se 1 (by rfl) ⟨584480, by rfl⟩ : syracuseStep 779307 = 1168961) B1168961
theorem B779319 : Blo 778337 779319 := bstep (se 1 (by rfl) ⟨584489, by rfl⟩ : syracuseStep 779319 = 1168979) B1168979
theorem B779339 : Blo 778337 779339 := bstep (se 1 (by rfl) ⟨584504, by rfl⟩ : syracuseStep 779339 = 1169009) B1169009
theorem B1172555 : Blo 778337 1172555 := bstep (se 1 (by rfl) ⟨879416, by rfl⟩ : syracuseStep 1172555 = 1758833) B1758833
theorem B779351 : Blo 778337 779351 := bstep (se 1 (by rfl) ⟨584513, by rfl⟩ : syracuseStep 779351 = 1169027) B1169027
theorem B1172567 : Blo 778337 1172567 := bstep (se 1 (by rfl) ⟨879425, by rfl⟩ : syracuseStep 1172567 = 1758851) B1758851
theorem B779371 : Blo 778337 779371 := bstep (se 1 (by rfl) ⟨584528, by rfl⟩ : syracuseStep 779371 = 1169057) B1169057
theorem B877675 : Blo 778337 877675 := bstep (se 1 (by rfl) ⟨658256, by rfl⟩ : syracuseStep 877675 = 1316513) B1316513
theorem B779383 : Blo 778337 779383 := bstep (se 1 (by rfl) ⟨584537, by rfl⟩ : syracuseStep 779383 = 1169075) B1169075
theorem B779403 : Blo 778337 779403 := bstep (se 1 (by rfl) ⟨584552, by rfl⟩ : syracuseStep 779403 = 1169105) B1169105
theorem B779415 : Blo 778337 779415 := bstep (se 1 (by rfl) ⟨584561, by rfl⟩ : syracuseStep 779415 = 1169123) B1169123
theorem B1172633 : Blo 778337 1172633 := bstep (se 2 (by rfl) ⟨439737, by rfl⟩ : syracuseStep 1172633 = 879475) B879475
theorem B779435 : Blo 778337 779435 := bstep (se 1 (by rfl) ⟨584576, by rfl⟩ : syracuseStep 779435 = 1169153) B1169153
theorem B779447 : Blo 778337 779447 := bstep (se 1 (by rfl) ⟨584585, by rfl⟩ : syracuseStep 779447 = 1169171) B1169171
theorem B779467 : Blo 778337 779467 := bstep (se 1 (by rfl) ⟨584600, by rfl⟩ : syracuseStep 779467 = 1169201) B1169201
theorem B779479 : Blo 778337 779479 := bstep (se 1 (by rfl) ⟨584609, by rfl⟩ : syracuseStep 779479 = 1169219) B1169219
theorem B877783 : Blo 778337 877783 := bstep (se 1 (by rfl) ⟨658337, by rfl⟩ : syracuseStep 877783 = 1316675) B1316675
theorem B779499 : Blo 778337 779499 := bstep (se 1 (by rfl) ⟨584624, by rfl⟩ : syracuseStep 779499 = 1169249) B1169249
theorem B779511 : Blo 778337 779511 := bstep (se 1 (by rfl) ⟨584633, by rfl⟩ : syracuseStep 779511 = 1169267) B1169267
theorem B779531 : Blo 778337 779531 := bstep (se 1 (by rfl) ⟨584648, by rfl⟩ : syracuseStep 779531 = 1169297) B1169297
theorem B1172747 : Blo 778337 1172747 := bstep (se 1 (by rfl) ⟨879560, by rfl⟩ : syracuseStep 1172747 = 1759121) B1759121
theorem B779543 : Blo 778337 779543 := bstep (se 1 (by rfl) ⟨584657, by rfl⟩ : syracuseStep 779543 = 1169315) B1169315
theorem B1172759 : Blo 778337 1172759 := bstep (se 1 (by rfl) ⟨879569, by rfl⟩ : syracuseStep 1172759 = 1759139) B1759139
theorem B779563 : Blo 778337 779563 := bstep (se 1 (by rfl) ⟨584672, by rfl⟩ : syracuseStep 779563 = 1169345) B1169345
theorem B7595309 : Blo 778337 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B4744493 : Blo 778337 4744493 := bstep (se 3 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 4744493 = 1779185) B1779185
theorem B779575 : Blo 778337 779575 := bstep (se 1 (by rfl) ⟨584681, by rfl⟩ : syracuseStep 779575 = 1169363) B1169363
theorem B8348993 : Blo 778337 8348993 := bstep (se 2 (by rfl) ⟨3130872, by rfl⟩ : syracuseStep 8348993 = 6261745) B6261745
theorem B779595 : Blo 778337 779595 := bstep (se 1 (by rfl) ⟨584696, by rfl⟩ : syracuseStep 779595 = 1169393) B1169393
theorem B779607 : Blo 778337 779607 := bstep (se 1 (by rfl) ⟨584705, by rfl⟩ : syracuseStep 779607 = 1169411) B1169411
theorem B1172825 : Blo 778337 1172825 := bstep (se 2 (by rfl) ⟨439809, by rfl⟩ : syracuseStep 1172825 = 879619) B879619
theorem B779627 : Blo 778337 779627 := bstep (se 1 (by rfl) ⟨584720, by rfl⟩ : syracuseStep 779627 = 1169441) B1169441
theorem B779639 : Blo 778337 779639 := bstep (se 1 (by rfl) ⟨584729, by rfl⟩ : syracuseStep 779639 = 1169459) B1169459
theorem B779659 : Blo 778337 779659 := bstep (se 1 (by rfl) ⟨584744, by rfl⟩ : syracuseStep 779659 = 1169489) B1169489
theorem B877963 : Blo 778337 877963 := bstep (se 1 (by rfl) ⟨658472, by rfl⟩ : syracuseStep 877963 = 1316945) B1316945
theorem B779671 : Blo 778337 779671 := bstep (se 1 (by rfl) ⟨584753, by rfl⟩ : syracuseStep 779671 = 1169507) B1169507
theorem B779691 : Blo 778337 779691 := bstep (se 1 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 779691 = 1169537) B1169537
theorem B779703 : Blo 778337 779703 := bstep (se 1 (by rfl) ⟨584777, by rfl⟩ : syracuseStep 779703 = 1169555) B1169555
theorem B779723 : Blo 778337 779723 := bstep (se 1 (by rfl) ⟨584792, by rfl⟩ : syracuseStep 779723 = 1169585) B1169585
theorem B1172939 : Blo 778337 1172939 := bstep (se 1 (by rfl) ⟨879704, by rfl⟩ : syracuseStep 1172939 = 1759409) B1759409
theorem B779735 : Blo 778337 779735 := bstep (se 1 (by rfl) ⟨584801, by rfl⟩ : syracuseStep 779735 = 1169603) B1169603
theorem B1172951 : Blo 778337 1172951 := bstep (se 1 (by rfl) ⟨879713, by rfl⟩ : syracuseStep 1172951 = 1759427) B1759427
theorem B779755 : Blo 778337 779755 := bstep (se 1 (by rfl) ⟨584816, by rfl⟩ : syracuseStep 779755 = 1169633) B1169633
theorem B779767 : Blo 778337 779767 := bstep (se 1 (by rfl) ⟨584825, by rfl⟩ : syracuseStep 779767 = 1169651) B1169651
theorem B878071 : Blo 778337 878071 := bstep (se 1 (by rfl) ⟨658553, by rfl⟩ : syracuseStep 878071 = 1317107) B1317107
theorem B779787 : Blo 778337 779787 := bstep (se 1 (by rfl) ⟨584840, by rfl⟩ : syracuseStep 779787 = 1169681) B1169681
theorem B779799 : Blo 778337 779799 := bstep (se 1 (by rfl) ⟨584849, by rfl⟩ : syracuseStep 779799 = 1169699) B1169699
theorem B1173017 : Blo 778337 1173017 := bstep (se 2 (by rfl) ⟨439881, by rfl⟩ : syracuseStep 1173017 = 879763) B879763
theorem B779819 : Blo 778337 779819 := bstep (se 1 (by rfl) ⟨584864, by rfl⟩ : syracuseStep 779819 = 1169729) B1169729
theorem B779831 : Blo 778337 779831 := bstep (se 1 (by rfl) ⟨584873, by rfl⟩ : syracuseStep 779831 = 1169747) B1169747
theorem B779851 : Blo 778337 779851 := bstep (se 1 (by rfl) ⟨584888, by rfl⟩ : syracuseStep 779851 = 1169777) B1169777
theorem B779863 : Blo 778337 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B779883 : Blo 778337 779883 := bstep (se 1 (by rfl) ⟨584912, by rfl⟩ : syracuseStep 779883 = 1169825) B1169825
theorem B779895 : Blo 778337 779895 := bstep (se 1 (by rfl) ⟨584921, by rfl⟩ : syracuseStep 779895 = 1169843) B1169843
theorem B1664641 : Blo 778337 1664641 := bstep (se 2 (by rfl) ⟨624240, by rfl⟩ : syracuseStep 1664641 = 1248481) B1248481
theorem B779915 : Blo 778337 779915 := bstep (se 1 (by rfl) ⟨584936, by rfl⟩ : syracuseStep 779915 = 1169873) B1169873
theorem B1173131 : Blo 778337 1173131 := bstep (se 1 (by rfl) ⟨879848, by rfl⟩ : syracuseStep 1173131 = 1759697) B1759697
theorem B779927 : Blo 778337 779927 := bstep (se 1 (by rfl) ⟨584945, by rfl⟩ : syracuseStep 779927 = 1169891) B1169891
theorem B1173143 : Blo 778337 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B779947 : Blo 778337 779947 := bstep (se 1 (by rfl) ⟨584960, by rfl⟩ : syracuseStep 779947 = 1169921) B1169921
theorem B878251 : Blo 778337 878251 := bstep (se 1 (by rfl) ⟨658688, by rfl⟩ : syracuseStep 878251 = 1317377) B1317377
theorem B779959 : Blo 778337 779959 := bstep (se 1 (by rfl) ⟨584969, by rfl⟩ : syracuseStep 779959 = 1169939) B1169939
theorem B779979 : Blo 778337 779979 := bstep (se 1 (by rfl) ⟨584984, by rfl⟩ : syracuseStep 779979 = 1169969) B1169969
theorem B779991 : Blo 778337 779991 := bstep (se 1 (by rfl) ⟨584993, by rfl⟩ : syracuseStep 779991 = 1169987) B1169987
theorem B1173209 : Blo 778337 1173209 := bstep (se 2 (by rfl) ⟨439953, by rfl⟩ : syracuseStep 1173209 = 879907) B879907
theorem B780011 : Blo 778337 780011 := bstep (se 1 (by rfl) ⟨585008, by rfl⟩ : syracuseStep 780011 = 1170017) B1170017
theorem B780023 : Blo 778337 780023 := bstep (se 1 (by rfl) ⟨585017, by rfl⟩ : syracuseStep 780023 = 1170035) B1170035
theorem B780043 : Blo 778337 780043 := bstep (se 1 (by rfl) ⟨585032, by rfl⟩ : syracuseStep 780043 = 1170065) B1170065
theorem B780055 : Blo 778337 780055 := bstep (se 1 (by rfl) ⟨585041, by rfl⟩ : syracuseStep 780055 = 1170083) B1170083
theorem B878359 : Blo 778337 878359 := bstep (se 1 (by rfl) ⟨658769, by rfl⟩ : syracuseStep 878359 = 1317539) B1317539
theorem B780075 : Blo 778337 780075 := bstep (se 1 (by rfl) ⟨585056, by rfl⟩ : syracuseStep 780075 = 1170113) B1170113
theorem B780087 : Blo 778337 780087 := bstep (se 1 (by rfl) ⟨585065, by rfl⟩ : syracuseStep 780087 = 1170131) B1170131
theorem B780107 : Blo 778337 780107 := bstep (se 1 (by rfl) ⟨585080, by rfl⟩ : syracuseStep 780107 = 1170161) B1170161
theorem B1173323 : Blo 778337 1173323 := bstep (se 1 (by rfl) ⟨879992, by rfl⟩ : syracuseStep 1173323 = 1759985) B1759985
theorem B780119 : Blo 778337 780119 := bstep (se 1 (by rfl) ⟨585089, by rfl⟩ : syracuseStep 780119 = 1170179) B1170179
theorem B1173335 : Blo 778337 1173335 := bstep (se 1 (by rfl) ⟨880001, by rfl⟩ : syracuseStep 1173335 = 1760003) B1760003
theorem B780139 : Blo 778337 780139 := bstep (se 1 (by rfl) ⟨585104, by rfl⟩ : syracuseStep 780139 = 1170209) B1170209
theorem B780151 : Blo 778337 780151 := bstep (se 1 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 780151 = 1170227) B1170227
theorem B780171 : Blo 778337 780171 := bstep (se 1 (by rfl) ⟨585128, by rfl⟩ : syracuseStep 780171 = 1170257) B1170257
theorem B780183 : Blo 778337 780183 := bstep (se 1 (by rfl) ⟨585137, by rfl⟩ : syracuseStep 780183 = 1170275) B1170275
theorem B1173401 : Blo 778337 1173401 := bstep (se 2 (by rfl) ⟨440025, by rfl⟩ : syracuseStep 1173401 = 880051) B880051
theorem B780203 : Blo 778337 780203 := bstep (se 1 (by rfl) ⟨585152, by rfl⟩ : syracuseStep 780203 = 1170305) B1170305
theorem B12642227 : Blo 778337 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B15001523 : Blo 778337 15001523 := bstep (se 1 (by rfl) ⟨11251142, by rfl⟩ : syracuseStep 15001523 = 22502285) B22502285
theorem B780215 : Blo 778337 780215 := bstep (se 1 (by rfl) ⟨585161, by rfl⟩ : syracuseStep 780215 = 1170323) B1170323
theorem B780235 : Blo 778337 780235 := bstep (se 1 (by rfl) ⟨585176, by rfl⟩ : syracuseStep 780235 = 1170353) B1170353
theorem B878539 : Blo 778337 878539 := bstep (se 1 (by rfl) ⟨658904, by rfl⟩ : syracuseStep 878539 = 1317809) B1317809
theorem B780247 : Blo 778337 780247 := bstep (se 1 (by rfl) ⟨585185, by rfl⟩ : syracuseStep 780247 = 1170371) B1170371
theorem B5924825 : Blo 778337 5924825 := bstep (se 2 (by rfl) ⟨2221809, by rfl⟩ : syracuseStep 5924825 = 4443619) B4443619
theorem B780267 : Blo 778337 780267 := bstep (se 1 (by rfl) ⟨585200, by rfl⟩ : syracuseStep 780267 = 1170401) B1170401
theorem B780279 : Blo 778337 780279 := bstep (se 1 (by rfl) ⟨585209, by rfl⟩ : syracuseStep 780279 = 1170419) B1170419
theorem B780299 : Blo 778337 780299 := bstep (se 1 (by rfl) ⟨585224, by rfl⟩ : syracuseStep 780299 = 1170449) B1170449
theorem B780311 : Blo 778337 780311 := bstep (se 1 (by rfl) ⟨585233, by rfl⟩ : syracuseStep 780311 = 1170467) B1170467
theorem B780331 : Blo 778337 780331 := bstep (se 1 (by rfl) ⟨585248, by rfl⟩ : syracuseStep 780331 = 1170497) B1170497
theorem B5335085 : Blo 778337 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B780343 : Blo 778337 780343 := bstep (se 1 (by rfl) ⟨585257, by rfl⟩ : syracuseStep 780343 = 1170515) B1170515
theorem B878647 : Blo 778337 878647 := bstep (se 1 (by rfl) ⟨658985, by rfl⟩ : syracuseStep 878647 = 1317971) B1317971
theorem B54716485 : Blo 778337 54716485 := bstep (se 4 (by rfl) ⟨5129670, by rfl⟩ : syracuseStep 54716485 = 10259341) B10259341
theorem B780363 : Blo 778337 780363 := bstep (se 1 (by rfl) ⟨585272, by rfl⟩ : syracuseStep 780363 = 1170545) B1170545
theorem B780375 : Blo 778337 780375 := bstep (se 1 (by rfl) ⟨585281, by rfl⟩ : syracuseStep 780375 = 1170563) B1170563
theorem B780395 : Blo 778337 780395 := bstep (se 1 (by rfl) ⟨585296, by rfl⟩ : syracuseStep 780395 = 1170593) B1170593
theorem B780407 : Blo 778337 780407 := bstep (se 1 (by rfl) ⟨585305, by rfl⟩ : syracuseStep 780407 = 1170611) B1170611
theorem B780427 : Blo 778337 780427 := bstep (se 1 (by rfl) ⟨585320, by rfl⟩ : syracuseStep 780427 = 1170641) B1170641
theorem B780439 : Blo 778337 780439 := bstep (se 1 (by rfl) ⟨585329, by rfl⟩ : syracuseStep 780439 = 1170659) B1170659
theorem B780459 : Blo 778337 780459 := bstep (se 1 (by rfl) ⟨585344, by rfl⟩ : syracuseStep 780459 = 1170689) B1170689
theorem B780471 : Blo 778337 780471 := bstep (se 1 (by rfl) ⟨585353, by rfl⟩ : syracuseStep 780471 = 1170707) B1170707
theorem B780491 : Blo 778337 780491 := bstep (se 1 (by rfl) ⟨585368, by rfl⟩ : syracuseStep 780491 = 1170737) B1170737
theorem B780503 : Blo 778337 780503 := bstep (se 1 (by rfl) ⟨585377, by rfl⟩ : syracuseStep 780503 = 1170755) B1170755
theorem B780523 : Blo 778337 780523 := bstep (se 1 (by rfl) ⟨585392, by rfl⟩ : syracuseStep 780523 = 1170785) B1170785
theorem B878827 : Blo 778337 878827 := bstep (se 1 (by rfl) ⟨659120, by rfl⟩ : syracuseStep 878827 = 1318241) B1318241
theorem B780535 : Blo 778337 780535 := bstep (se 1 (by rfl) ⟨585401, by rfl⟩ : syracuseStep 780535 = 1170803) B1170803
theorem B780555 : Blo 778337 780555 := bstep (se 1 (by rfl) ⟨585416, by rfl⟩ : syracuseStep 780555 = 1170833) B1170833
theorem B780567 : Blo 778337 780567 := bstep (se 1 (by rfl) ⟨585425, by rfl⟩ : syracuseStep 780567 = 1170851) B1170851
theorem B780587 : Blo 778337 780587 := bstep (se 1 (by rfl) ⟨585440, by rfl⟩ : syracuseStep 780587 = 1170881) B1170881
theorem B780599 : Blo 778337 780599 := bstep (se 1 (by rfl) ⟨585449, by rfl⟩ : syracuseStep 780599 = 1170899) B1170899
theorem B780619 : Blo 778337 780619 := bstep (se 1 (by rfl) ⟨585464, by rfl⟩ : syracuseStep 780619 = 1170929) B1170929
theorem B780631 : Blo 778337 780631 := bstep (se 1 (by rfl) ⟨585473, by rfl⟩ : syracuseStep 780631 = 1170947) B1170947
theorem B878935 : Blo 778337 878935 := bstep (se 1 (by rfl) ⟨659201, by rfl⟩ : syracuseStep 878935 = 1318403) B1318403
theorem B780651 : Blo 778337 780651 := bstep (se 1 (by rfl) ⟨585488, by rfl⟩ : syracuseStep 780651 = 1170977) B1170977
theorem B780663 : Blo 778337 780663 := bstep (se 1 (by rfl) ⟨585497, by rfl⟩ : syracuseStep 780663 = 1170995) B1170995
theorem B780683 : Blo 778337 780683 := bstep (se 1 (by rfl) ⟨585512, by rfl⟩ : syracuseStep 780683 = 1171025) B1171025
theorem B780695 : Blo 778337 780695 := bstep (se 1 (by rfl) ⟨585521, by rfl⟩ : syracuseStep 780695 = 1171043) B1171043
theorem B780715 : Blo 778337 780715 := bstep (se 1 (by rfl) ⟨585536, by rfl⟩ : syracuseStep 780715 = 1171073) B1171073
theorem B780727 : Blo 778337 780727 := bstep (se 1 (by rfl) ⟨585545, by rfl⟩ : syracuseStep 780727 = 1171091) B1171091
theorem B780747 : Blo 778337 780747 := bstep (se 1 (by rfl) ⟨585560, by rfl⟩ : syracuseStep 780747 = 1171121) B1171121
theorem B780759 : Blo 778337 780759 := bstep (se 1 (by rfl) ⟨585569, by rfl⟩ : syracuseStep 780759 = 1171139) B1171139
theorem B780779 : Blo 778337 780779 := bstep (se 1 (by rfl) ⟨585584, by rfl⟩ : syracuseStep 780779 = 1171169) B1171169
theorem B780791 : Blo 778337 780791 := bstep (se 1 (by rfl) ⟨585593, by rfl⟩ : syracuseStep 780791 = 1171187) B1171187
theorem B780811 : Blo 778337 780811 := bstep (se 1 (by rfl) ⟨585608, by rfl⟩ : syracuseStep 780811 = 1171217) B1171217
theorem B879115 : Blo 778337 879115 := bstep (se 1 (by rfl) ⟨659336, by rfl⟩ : syracuseStep 879115 = 1318673) B1318673
theorem B780823 : Blo 778337 780823 := bstep (se 1 (by rfl) ⟨585617, by rfl⟩ : syracuseStep 780823 = 1171235) B1171235
theorem B780843 : Blo 778337 780843 := bstep (se 1 (by rfl) ⟨585632, by rfl⟩ : syracuseStep 780843 = 1171265) B1171265
theorem B780855 : Blo 778337 780855 := bstep (se 1 (by rfl) ⟨585641, by rfl⟩ : syracuseStep 780855 = 1171283) B1171283
theorem B780875 : Blo 778337 780875 := bstep (se 1 (by rfl) ⟨585656, by rfl⟩ : syracuseStep 780875 = 1171313) B1171313
theorem B1665623 : Blo 778337 1665623 := bstep (se 1 (by rfl) ⟨1249217, by rfl⟩ : syracuseStep 1665623 = 2498435) B2498435
theorem B780887 : Blo 778337 780887 := bstep (se 1 (by rfl) ⟨585665, by rfl⟩ : syracuseStep 780887 = 1171331) B1171331
theorem B4450909 : Blo 778337 4450909 := bstep (se 3 (by rfl) ⟨834545, by rfl⟩ : syracuseStep 4450909 = 1669091) B1669091
theorem B780907 : Blo 778337 780907 := bstep (se 1 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 780907 = 1171361) B1171361
theorem B780919 : Blo 778337 780919 := bstep (se 1 (by rfl) ⟨585689, by rfl⟩ : syracuseStep 780919 = 1171379) B1171379
theorem B879223 : Blo 778337 879223 := bstep (se 1 (by rfl) ⟨659417, by rfl⟩ : syracuseStep 879223 = 1318835) B1318835
theorem B780939 : Blo 778337 780939 := bstep (se 1 (by rfl) ⟨585704, by rfl⟩ : syracuseStep 780939 = 1171409) B1171409
theorem B780951 : Blo 778337 780951 := bstep (se 1 (by rfl) ⟨585713, by rfl⟩ : syracuseStep 780951 = 1171427) B1171427
theorem B780971 : Blo 778337 780971 := bstep (se 1 (by rfl) ⟨585728, by rfl⟩ : syracuseStep 780971 = 1171457) B1171457
theorem B780983 : Blo 778337 780983 := bstep (se 1 (by rfl) ⟨585737, by rfl⟩ : syracuseStep 780983 = 1171475) B1171475
theorem B781003 : Blo 778337 781003 := bstep (se 1 (by rfl) ⟨585752, by rfl⟩ : syracuseStep 781003 = 1171505) B1171505
theorem B781015 : Blo 778337 781015 := bstep (se 1 (by rfl) ⟨585761, by rfl⟩ : syracuseStep 781015 = 1171523) B1171523
theorem B781035 : Blo 778337 781035 := bstep (se 1 (by rfl) ⟨585776, by rfl⟩ : syracuseStep 781035 = 1171553) B1171553
theorem B781047 : Blo 778337 781047 := bstep (se 1 (by rfl) ⟨585785, by rfl⟩ : syracuseStep 781047 = 1171571) B1171571
theorem B781067 : Blo 778337 781067 := bstep (se 1 (by rfl) ⟨585800, by rfl⟩ : syracuseStep 781067 = 1171601) B1171601
theorem B781079 : Blo 778337 781079 := bstep (se 1 (by rfl) ⟨585809, by rfl⟩ : syracuseStep 781079 = 1171619) B1171619
theorem B781099 : Blo 778337 781099 := bstep (se 1 (by rfl) ⟨585824, by rfl⟩ : syracuseStep 781099 = 1171649) B1171649
theorem B879403 : Blo 778337 879403 := bstep (se 1 (by rfl) ⟨659552, by rfl⟩ : syracuseStep 879403 = 1319105) B1319105
theorem B781111 : Blo 778337 781111 := bstep (se 1 (by rfl) ⟨585833, by rfl⟩ : syracuseStep 781111 = 1171667) B1171667
theorem B781131 : Blo 778337 781131 := bstep (se 1 (by rfl) ⟨585848, by rfl⟩ : syracuseStep 781131 = 1171697) B1171697
theorem B781143 : Blo 778337 781143 := bstep (se 1 (by rfl) ⟨585857, by rfl⟩ : syracuseStep 781143 = 1171715) B1171715
theorem B781163 : Blo 778337 781163 := bstep (se 1 (by rfl) ⟨585872, by rfl⟩ : syracuseStep 781163 = 1171745) B1171745
theorem B781175 : Blo 778337 781175 := bstep (se 1 (by rfl) ⟨585881, by rfl⟩ : syracuseStep 781175 = 1171763) B1171763
theorem B781195 : Blo 778337 781195 := bstep (se 1 (by rfl) ⟨585896, by rfl⟩ : syracuseStep 781195 = 1171793) B1171793
theorem B781207 : Blo 778337 781207 := bstep (se 1 (by rfl) ⟨585905, by rfl⟩ : syracuseStep 781207 = 1171811) B1171811
theorem B879511 : Blo 778337 879511 := bstep (se 1 (by rfl) ⟨659633, by rfl⟩ : syracuseStep 879511 = 1319267) B1319267
theorem B781227 : Blo 778337 781227 := bstep (se 1 (by rfl) ⟨585920, by rfl⟩ : syracuseStep 781227 = 1171841) B1171841
theorem B28437425 : Blo 778337 28437425 := bstep (se 2 (by rfl) ⟨10664034, by rfl⟩ : syracuseStep 28437425 = 21328069) B21328069
theorem B781239 : Blo 778337 781239 := bstep (se 1 (by rfl) ⟨585929, by rfl⟩ : syracuseStep 781239 = 1171859) B1171859
theorem B781259 : Blo 778337 781259 := bstep (se 1 (by rfl) ⟨585944, by rfl⟩ : syracuseStep 781259 = 1171889) B1171889
theorem B781271 : Blo 778337 781271 := bstep (se 1 (by rfl) ⟨585953, by rfl⟩ : syracuseStep 781271 = 1171907) B1171907
theorem B781291 : Blo 778337 781291 := bstep (se 1 (by rfl) ⟨585968, by rfl⟩ : syracuseStep 781291 = 1171937) B1171937
theorem B781303 : Blo 778337 781303 := bstep (se 1 (by rfl) ⟨585977, by rfl⟩ : syracuseStep 781303 = 1171955) B1171955
theorem B781323 : Blo 778337 781323 := bstep (se 1 (by rfl) ⟨585992, by rfl⟩ : syracuseStep 781323 = 1171985) B1171985
theorem B781335 : Blo 778337 781335 := bstep (se 1 (by rfl) ⟨586001, by rfl⟩ : syracuseStep 781335 = 1172003) B1172003
theorem B1403929 : Blo 778337 1403929 := bstep (se 2 (by rfl) ⟨526473, by rfl⟩ : syracuseStep 1403929 = 1052947) B1052947
theorem B781355 : Blo 778337 781355 := bstep (se 1 (by rfl) ⟨586016, by rfl⟩ : syracuseStep 781355 = 1172033) B1172033
theorem B781367 : Blo 778337 781367 := bstep (se 1 (by rfl) ⟨586025, by rfl⟩ : syracuseStep 781367 = 1172051) B1172051
theorem B781387 : Blo 778337 781387 := bstep (se 1 (by rfl) ⟨586040, by rfl⟩ : syracuseStep 781387 = 1172081) B1172081
theorem B879691 : Blo 778337 879691 := bstep (se 1 (by rfl) ⟨659768, by rfl⟩ : syracuseStep 879691 = 1319537) B1319537
theorem B781399 : Blo 778337 781399 := bstep (se 1 (by rfl) ⟨586049, by rfl⟩ : syracuseStep 781399 = 1172099) B1172099
theorem B781419 : Blo 778337 781419 := bstep (se 1 (by rfl) ⟨586064, by rfl⟩ : syracuseStep 781419 = 1172129) B1172129
theorem B781431 : Blo 778337 781431 := bstep (se 1 (by rfl) ⟨586073, by rfl⟩ : syracuseStep 781431 = 1172147) B1172147
theorem B1666187 : Blo 778337 1666187 := bstep (se 1 (by rfl) ⟨1249640, by rfl⟩ : syracuseStep 1666187 = 2499281) B2499281
theorem B781451 : Blo 778337 781451 := bstep (se 1 (by rfl) ⟨586088, by rfl⟩ : syracuseStep 781451 = 1172177) B1172177
theorem B781463 : Blo 778337 781463 := bstep (se 1 (by rfl) ⟨586097, by rfl⟩ : syracuseStep 781463 = 1172195) B1172195
theorem B781483 : Blo 778337 781483 := bstep (se 1 (by rfl) ⟨586112, by rfl⟩ : syracuseStep 781483 = 1172225) B1172225
theorem B781495 : Blo 778337 781495 := bstep (se 1 (by rfl) ⟨586121, by rfl⟩ : syracuseStep 781495 = 1172243) B1172243
theorem B879799 : Blo 778337 879799 := bstep (se 1 (by rfl) ⟨659849, by rfl⟩ : syracuseStep 879799 = 1319699) B1319699
theorem B781515 : Blo 778337 781515 := bstep (se 1 (by rfl) ⟨586136, by rfl⟩ : syracuseStep 781515 = 1172273) B1172273
theorem B781527 : Blo 778337 781527 := bstep (se 1 (by rfl) ⟨586145, by rfl⟩ : syracuseStep 781527 = 1172291) B1172291
theorem B205090019 : Blo 778337 205090019 := bstep (se 1 (by rfl) ⟨153817514, by rfl⟩ : syracuseStep 205090019 = 307635029) B307635029
theorem B781547 : Blo 778337 781547 := bstep (se 1 (by rfl) ⟨586160, by rfl⟩ : syracuseStep 781547 = 1172321) B1172321
theorem B781559 : Blo 778337 781559 := bstep (se 1 (by rfl) ⟨586169, by rfl⟩ : syracuseStep 781559 = 1172339) B1172339
theorem B781579 : Blo 778337 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B781591 : Blo 778337 781591 := bstep (se 1 (by rfl) ⟨586193, by rfl⟩ : syracuseStep 781591 = 1172387) B1172387
theorem B781611 : Blo 778337 781611 := bstep (se 1 (by rfl) ⟨586208, by rfl⟩ : syracuseStep 781611 = 1172417) B1172417
theorem B781623 : Blo 778337 781623 := bstep (se 1 (by rfl) ⟨586217, by rfl⟩ : syracuseStep 781623 = 1172435) B1172435
theorem B781643 : Blo 778337 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B781655 : Blo 778337 781655 := bstep (se 1 (by rfl) ⟨586241, by rfl⟩ : syracuseStep 781655 = 1172483) B1172483
theorem B781675 : Blo 778337 781675 := bstep (se 1 (by rfl) ⟨586256, by rfl⟩ : syracuseStep 781675 = 1172513) B1172513
theorem B879979 : Blo 778337 879979 := bstep (se 1 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 879979 = 1319969) B1319969
theorem B781687 : Blo 778337 781687 := bstep (se 1 (by rfl) ⟨586265, by rfl⟩ : syracuseStep 781687 = 1172531) B1172531
theorem B781707 : Blo 778337 781707 := bstep (se 1 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 781707 = 1172561) B1172561
theorem B781719 : Blo 778337 781719 := bstep (se 1 (by rfl) ⟨586289, by rfl⟩ : syracuseStep 781719 = 1172579) B1172579
theorem B781739 : Blo 778337 781739 := bstep (se 1 (by rfl) ⟨586304, by rfl⟩ : syracuseStep 781739 = 1172609) B1172609
theorem B2813363 : Blo 778337 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B781751 : Blo 778337 781751 := bstep (se 1 (by rfl) ⟨586313, by rfl⟩ : syracuseStep 781751 = 1172627) B1172627
theorem B781771 : Blo 778337 781771 := bstep (se 1 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 781771 = 1172657) B1172657
theorem B781783 : Blo 778337 781783 := bstep (se 1 (by rfl) ⟨586337, by rfl⟩ : syracuseStep 781783 = 1172675) B1172675
theorem B880087 : Blo 778337 880087 := bstep (se 1 (by rfl) ⟨660065, by rfl⟩ : syracuseStep 880087 = 1320131) B1320131
theorem B781803 : Blo 778337 781803 := bstep (se 1 (by rfl) ⟨586352, by rfl⟩ : syracuseStep 781803 = 1172705) B1172705
theorem B781815 : Blo 778337 781815 := bstep (se 1 (by rfl) ⟨586361, by rfl⟩ : syracuseStep 781815 = 1172723) B1172723
theorem B781835 : Blo 778337 781835 := bstep (se 1 (by rfl) ⟨586376, by rfl⟩ : syracuseStep 781835 = 1172753) B1172753
theorem B781847 : Blo 778337 781847 := bstep (se 1 (by rfl) ⟨586385, by rfl⟩ : syracuseStep 781847 = 1172771) B1172771
theorem B781867 : Blo 778337 781867 := bstep (se 1 (by rfl) ⟨586400, by rfl⟩ : syracuseStep 781867 = 1172801) B1172801
theorem B781879 : Blo 778337 781879 := bstep (se 1 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 781879 = 1172819) B1172819
theorem B781899 : Blo 778337 781899 := bstep (se 1 (by rfl) ⟨586424, by rfl⟩ : syracuseStep 781899 = 1172849) B1172849
theorem B781911 : Blo 778337 781911 := bstep (se 1 (by rfl) ⟨586433, by rfl⟩ : syracuseStep 781911 = 1172867) B1172867
theorem B1666649 : Blo 778337 1666649 := bstep (se 2 (by rfl) ⟨624993, by rfl⟩ : syracuseStep 1666649 = 1249987) B1249987
theorem B3960413 : Blo 778337 3960413 := bstep (se 3 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 3960413 = 1485155) B1485155
theorem B781931 : Blo 778337 781931 := bstep (se 1 (by rfl) ⟨586448, by rfl⟩ : syracuseStep 781931 = 1172897) B1172897
theorem B781943 : Blo 778337 781943 := bstep (se 1 (by rfl) ⟨586457, by rfl⟩ : syracuseStep 781943 = 1172915) B1172915
theorem B781963 : Blo 778337 781963 := bstep (se 1 (by rfl) ⟨586472, by rfl⟩ : syracuseStep 781963 = 1172945) B1172945
theorem B781975 : Blo 778337 781975 := bstep (se 1 (by rfl) ⟨586481, by rfl⟩ : syracuseStep 781975 = 1172963) B1172963
theorem B781995 : Blo 778337 781995 := bstep (se 1 (by rfl) ⟨586496, by rfl⟩ : syracuseStep 781995 = 1172993) B1172993
theorem B782007 : Blo 778337 782007 := bstep (se 1 (by rfl) ⟨586505, by rfl⟩ : syracuseStep 782007 = 1173011) B1173011
theorem B782027 : Blo 778337 782027 := bstep (se 1 (by rfl) ⟨586520, by rfl⟩ : syracuseStep 782027 = 1173041) B1173041
theorem B782039 : Blo 778337 782039 := bstep (se 1 (by rfl) ⟨586529, by rfl⟩ : syracuseStep 782039 = 1173059) B1173059
theorem B782059 : Blo 778337 782059 := bstep (se 1 (by rfl) ⟨586544, by rfl⟩ : syracuseStep 782059 = 1173089) B1173089
theorem B782071 : Blo 778337 782071 := bstep (se 1 (by rfl) ⟨586553, by rfl⟩ : syracuseStep 782071 = 1173107) B1173107
theorem B1601281 : Blo 778337 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B782091 : Blo 778337 782091 := bstep (se 1 (by rfl) ⟨586568, by rfl⟩ : syracuseStep 782091 = 1173137) B1173137
theorem B2223895 : Blo 778337 2223895 := bstep (se 1 (by rfl) ⟨1667921, by rfl⟩ : syracuseStep 2223895 = 3335843) B3335843
theorem B782103 : Blo 778337 782103 := bstep (se 1 (by rfl) ⟨586577, by rfl⟩ : syracuseStep 782103 = 1173155) B1173155
theorem B782123 : Blo 778337 782123 := bstep (se 1 (by rfl) ⟨586592, by rfl⟩ : syracuseStep 782123 = 1173185) B1173185
theorem B782135 : Blo 778337 782135 := bstep (se 1 (by rfl) ⟨586601, by rfl⟩ : syracuseStep 782135 = 1173203) B1173203
theorem B782155 : Blo 778337 782155 := bstep (se 1 (by rfl) ⟨586616, by rfl⟩ : syracuseStep 782155 = 1173233) B1173233
theorem B782167 : Blo 778337 782167 := bstep (se 1 (by rfl) ⟨586625, by rfl⟩ : syracuseStep 782167 = 1173251) B1173251
theorem B4222813 : Blo 778337 4222813 := bstep (se 3 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 4222813 = 1583555) B1583555
theorem B782187 : Blo 778337 782187 := bstep (se 1 (by rfl) ⟨586640, by rfl⟩ : syracuseStep 782187 = 1173281) B1173281
theorem B782199 : Blo 778337 782199 := bstep (se 1 (by rfl) ⟨586649, by rfl⟩ : syracuseStep 782199 = 1173299) B1173299
theorem B782219 : Blo 778337 782219 := bstep (se 1 (by rfl) ⟨586664, by rfl⟩ : syracuseStep 782219 = 1173329) B1173329
theorem B782231 : Blo 778337 782231 := bstep (se 1 (by rfl) ⟨586673, by rfl⟩ : syracuseStep 782231 = 1173347) B1173347
theorem B782251 : Blo 778337 782251 := bstep (se 1 (by rfl) ⟨586688, by rfl⟩ : syracuseStep 782251 = 1173377) B1173377
theorem B782263 : Blo 778337 782263 := bstep (se 1 (by rfl) ⟨586697, by rfl⟩ : syracuseStep 782263 = 1173395) B1173395
theorem B782283 : Blo 778337 782283 := bstep (se 1 (by rfl) ⟨586712, by rfl⟩ : syracuseStep 782283 = 1173425) B1173425
theorem B782295 : Blo 778337 782295 := bstep (se 1 (by rfl) ⟨586721, by rfl⟩ : syracuseStep 782295 = 1173443) B1173443
theorem B782315 : Blo 778337 782315 := bstep (se 1 (by rfl) ⟨586736, by rfl⟩ : syracuseStep 782315 = 1173473) B1173473
theorem B782327 : Blo 778337 782327 := bstep (se 1 (by rfl) ⟨586745, by rfl⟩ : syracuseStep 782327 = 1173491) B1173491
theorem B1110233 : Blo 778337 1110233 := bstep (se 2 (by rfl) ⟨416337, by rfl⟩ : syracuseStep 1110233 = 832675) B832675
theorem B10678877 : Blo 778337 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B3666583 : Blo 778337 3666583 := bstep (se 1 (by rfl) ⟨2749937, by rfl⟩ : syracuseStep 3666583 = 5499875) B5499875
theorem B1405643 : Blo 778337 1405643 := bstep (se 1 (by rfl) ⟨1054232, by rfl⟩ : syracuseStep 1405643 = 2108465) B2108465
theorem B1667827 : Blo 778337 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B1110871 : Blo 778337 1110871 := bstep (se 1 (by rfl) ⟨833153, by rfl⟩ : syracuseStep 1110871 = 1666307) B1666307
theorem B1405811 : Blo 778337 1405811 := bstep (se 1 (by rfl) ⟨1054358, by rfl⟩ : syracuseStep 1405811 = 2108717) B2108717
theorem B3339139 : Blo 778337 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B2225227 : Blo 778337 2225227 := bstep (se 1 (by rfl) ⟨1668920, by rfl⟩ : syracuseStep 2225227 = 3337841) B3337841
theorem B1668289 : Blo 778337 1668289 := bstep (se 2 (by rfl) ⟨625608, by rfl⟩ : syracuseStep 1668289 = 1251217) B1251217
theorem B3339481 : Blo 778337 3339481 := bstep (se 2 (by rfl) ⟨1252305, by rfl⟩ : syracuseStep 3339481 = 2504611) B2504611
theorem B5928227 : Blo 778337 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B6321473 : Blo 778337 6321473 := bstep (se 2 (by rfl) ⟨2370552, by rfl⟩ : syracuseStep 6321473 = 4741105) B4741105
theorem B2225501 : Blo 778337 2225501 := bstep (se 3 (by rfl) ⟨417281, by rfl⟩ : syracuseStep 2225501 = 834563) B834563
theorem B1111691 : Blo 778337 1111691 := bstep (se 1 (by rfl) ⟨833768, by rfl⟩ : syracuseStep 1111691 = 1667537) B1667537
theorem B2225843 : Blo 778337 2225843 := bstep (se 1 (by rfl) ⟨1669382, by rfl⟩ : syracuseStep 2225843 = 3338765) B3338765
theorem B1669015 : Blo 778337 1669015 := bstep (se 1 (by rfl) ⟨1251761, by rfl⟩ : syracuseStep 1669015 = 2503523) B2503523
theorem B3799057 : Blo 778337 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B1406999 : Blo 778337 1406999 := bstep (se 1 (by rfl) ⟨1055249, by rfl⟩ : syracuseStep 1406999 = 2110499) B2110499
theorem B3340439 : Blo 778337 3340439 := bstep (se 1 (by rfl) ⟨2505329, by rfl⟩ : syracuseStep 3340439 = 5010659) B5010659
theorem B6682925 : Blo 778337 6682925 := bstep (se 3 (by rfl) ⟨1253048, by rfl⟩ : syracuseStep 6682925 = 2506097) B2506097
theorem B6421169 : Blo 778337 6421169 := bstep (se 2 (by rfl) ⟨2407938, by rfl⟩ : syracuseStep 6421169 = 4815877) B4815877
theorem B1669835 : Blo 778337 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B10156805 : Blo 778337 10156805 := bstep (se 4 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 10156805 = 1904401) B1904401
theorem B1408001 : Blo 778337 1408001 := bstep (se 2 (by rfl) ⟨528000, by rfl⟩ : syracuseStep 1408001 = 1056001) B1056001
theorem B1408499 : Blo 778337 1408499 := bstep (se 1 (by rfl) ⟨1056374, by rfl⟩ : syracuseStep 1408499 = 2112749) B2112749
theorem B1670681 : Blo 778337 1670681 := bstep (se 2 (by rfl) ⟨626505, by rfl⟩ : syracuseStep 1670681 = 1253011) B1253011
theorem B13336325 : Blo 778337 13336325 := bstep (se 4 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 13336325 = 2500561) B2500561
theorem B3997457 : Blo 778337 3997457 := bstep (se 2 (by rfl) ⟨1499046, by rfl⟩ : syracuseStep 3997457 = 2998093) B2998093
theorem B9470189 : Blo 778337 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B6652307 : Blo 778337 6652307 := bstep (se 1 (by rfl) ⟨4989230, by rfl⟩ : syracuseStep 6652307 = 9978461) B9978461
theorem B32407955 : Blo 778337 32407955 := bstep (se 1 (by rfl) ⟨24305966, by rfl⟩ : syracuseStep 32407955 = 48611933) B48611933
theorem B9470681 : Blo 778337 9470681 := bstep (se 2 (by rfl) ⟨3551505, by rfl⟩ : syracuseStep 9470681 = 7103011) B7103011
theorem B9012005 : Blo 778337 9012005 := bstep (se 4 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 9012005 = 1689751) B1689751
theorem B34145201 : Blo 778337 34145201 := bstep (se 2 (by rfl) ⟨12804450, by rfl⟩ : syracuseStep 34145201 = 25608901) B25608901
theorem B8422787 : Blo 778337 8422787 := bstep (se 1 (by rfl) ⟨6317090, by rfl⟩ : syracuseStep 8422787 = 12634181) B12634181
theorem B6752089 : Blo 778337 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B8456309 : Blo 778337 8456309 := bstep (se 5 (by rfl) ⟨396389, by rfl⟩ : syracuseStep 8456309 = 792779) B792779
theorem B985223 : Blo 778337 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B4065551 : Blo 778337 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B985871 : Blo 778337 985871 := bstep (se 1 (by rfl) ⟨739403, by rfl⟩ : syracuseStep 985871 = 1478807) B1478807
theorem B1313671 : Blo 778337 1313671 := bstep (se 1 (by rfl) ⟨985253, by rfl⟩ : syracuseStep 1313671 = 1970507) B1970507
theorem B1052023 : Blo 778337 1052023 := bstep (se 1 (by rfl) ⟨789017, by rfl⟩ : syracuseStep 1052023 = 1578035) B1578035
theorem B20254157 : Blo 778337 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B5934545 : Blo 778337 5934545 := bstep (se 2 (by rfl) ⟨2225454, by rfl⟩ : syracuseStep 5934545 = 4450909) B4450909
theorem B1314319 : Blo 778337 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B1904519 : Blo 778337 1904519 := bstep (se 1 (by rfl) ⟨1428389, by rfl⟩ : syracuseStep 1904519 = 2856779) B2856779
theorem B7606219 : Blo 778337 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B1871905 : Blo 778337 1871905 := bstep (se 2 (by rfl) ⟨701964, by rfl⟩ : syracuseStep 1871905 = 1403929) B1403929
theorem B1314859 : Blo 778337 1314859 := bstep (se 1 (by rfl) ⟨986144, by rfl⟩ : syracuseStep 1314859 = 1972289) B1972289
theorem B6328381 : Blo 778337 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B1315001 : Blo 778337 1315001 := bstep (se 2 (by rfl) ⟨493125, by rfl⟩ : syracuseStep 1315001 = 986251) B986251
theorem B1970689 : Blo 778337 1970689 := bstep (se 2 (by rfl) ⟨739008, by rfl⟩ : syracuseStep 1970689 = 1478017) B1478017
theorem B9507557 : Blo 778337 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B22549337 : Blo 778337 22549337 := bstep (se 2 (by rfl) ⟨8456001, by rfl⟩ : syracuseStep 22549337 = 16912003) B16912003
theorem B1315703 : Blo 778337 1315703 := bstep (se 1 (by rfl) ⟨986777, by rfl⟩ : syracuseStep 1315703 = 1973555) B1973555
theorem B1479559 : Blo 778337 1479559 := bstep (se 1 (by rfl) ⟨1109669, by rfl⟩ : syracuseStep 1479559 = 2219339) B2219339
theorem B2135041 : Blo 778337 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B1971287 : Blo 778337 1971287 := bstep (se 1 (by rfl) ⟨1478465, by rfl⟩ : syracuseStep 1971287 = 2956931) B2956931
theorem B1184887 : Blo 778337 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B1971499 : Blo 778337 1971499 := bstep (se 1 (by rfl) ⟨1478624, by rfl⟩ : syracuseStep 1971499 = 2957249) B2957249
theorem B1873211 : Blo 778337 1873211 := bstep (se 1 (by rfl) ⟨1404908, by rfl⟩ : syracuseStep 1873211 = 2809817) B2809817
theorem B1316155 : Blo 778337 1316155 := bstep (se 1 (by rfl) ⟨987116, by rfl⟩ : syracuseStep 1316155 = 1974233) B1974233
theorem B1971641 : Blo 778337 1971641 := bstep (se 2 (by rfl) ⟨739365, by rfl⟩ : syracuseStep 1971641 = 1478731) B1478731
theorem B160339397 : Blo 778337 160339397 := bstep (se 4 (by rfl) ⟨15031818, by rfl⟩ : syracuseStep 160339397 = 30063637) B30063637
theorem B1316297 : Blo 778337 1316297 := bstep (se 2 (by rfl) ⟨493611, by rfl⟩ : syracuseStep 1316297 = 987223) B987223
theorem B3741137 : Blo 778337 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B988843 : Blo 778337 988843 := bstep (se 1 (by rfl) ⟨741632, by rfl⟩ : syracuseStep 988843 = 1483265) B1483265
theorem B1873799 : Blo 778337 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B2955275 : Blo 778337 2955275 := bstep (se 1 (by rfl) ⟨2216456, by rfl⟩ : syracuseStep 2955275 = 4432913) B4432913
theorem B1251371 : Blo 778337 1251371 := bstep (se 1 (by rfl) ⟨938528, by rfl⟩ : syracuseStep 1251371 = 1877057) B1877057
theorem B1316999 : Blo 778337 1316999 := bstep (se 1 (by rfl) ⟨987749, by rfl⟩ : syracuseStep 1316999 = 1975499) B1975499
theorem B1185977 : Blo 778337 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B4888777 : Blo 778337 4888777 := bstep (se 2 (by rfl) ⟨1833291, by rfl⟩ : syracuseStep 4888777 = 3666583) B3666583
theorem B8886509 : Blo 778337 8886509 := bstep (se 3 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 8886509 = 3332441) B3332441
theorem B5347565 : Blo 778337 5347565 := bstep (se 3 (by rfl) ⟨1002668, by rfl⟩ : syracuseStep 5347565 = 2005337) B2005337
theorem B1186055 : Blo 778337 1186055 := bstep (se 1 (by rfl) ⟨889541, by rfl⟩ : syracuseStep 1186055 = 1779083) B1779083
theorem B2627855 : Blo 778337 2627855 := bstep (se 1 (by rfl) ⟨1970891, by rfl⟩ : syracuseStep 2627855 = 3941783) B3941783
theorem B1972633 : Blo 778337 1972633 := bstep (se 2 (by rfl) ⟨739737, by rfl⟩ : syracuseStep 1972633 = 1479475) B1479475
theorem B1481161 : Blo 778337 1481161 := bstep (se 2 (by rfl) ⟨555435, by rfl⟩ : syracuseStep 1481161 = 1110871) B1110871
theorem B2628125 : Blo 778337 2628125 := bstep (se 3 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 2628125 = 985547) B985547
theorem B1251883 : Blo 778337 1251883 := bstep (se 1 (by rfl) ⟨938912, by rfl⟩ : syracuseStep 1251883 = 1877825) B1877825
theorem B1972795 : Blo 778337 1972795 := bstep (se 1 (by rfl) ⟨1479596, by rfl⟩ : syracuseStep 1972795 = 2959193) B2959193
theorem B8428151 : Blo 778337 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B10001015 : Blo 778337 10001015 := bstep (se 1 (by rfl) ⟨7500761, by rfl⟩ : syracuseStep 10001015 = 15001523) B15001523
theorem B989815 : Blo 778337 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B1972937 : Blo 778337 1972937 := bstep (se 2 (by rfl) ⟨739851, by rfl⟩ : syracuseStep 1972937 = 1479703) B1479703
theorem B1317647 : Blo 778337 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B990139 : Blo 778337 990139 := bstep (se 1 (by rfl) ⟨742604, by rfl⟩ : syracuseStep 990139 = 1485209) B1485209
theorem B17538053 : Blo 778337 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B1973281 : Blo 778337 1973281 := bstep (se 2 (by rfl) ⟨739980, by rfl⟩ : syracuseStep 1973281 = 1479961) B1479961
theorem B1318187 : Blo 778337 1318187 := bstep (se 1 (by rfl) ⟨988640, by rfl⟩ : syracuseStep 1318187 = 1977281) B1977281
theorem B1252793 : Blo 778337 1252793 := bstep (se 2 (by rfl) ⟨469797, by rfl⟩ : syracuseStep 1252793 = 939595) B939595
theorem B1973879 : Blo 778337 1973879 := bstep (se 1 (by rfl) ⟨1480409, by rfl⟩ : syracuseStep 1973879 = 2960819) B2960819
theorem B1875575 : Blo 778337 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B1318585 : Blo 778337 1318585 := bstep (se 2 (by rfl) ⟨494469, by rfl⟩ : syracuseStep 1318585 = 988939) B988939
theorem B14262065 : Blo 778337 14262065 := bstep (se 2 (by rfl) ⟨5348274, by rfl⟩ : syracuseStep 14262065 = 10696549) B10696549
theorem B2629529 : Blo 778337 2629529 := bstep (se 2 (by rfl) ⟨986073, by rfl⟩ : syracuseStep 2629529 = 1972147) B1972147
theorem B1581089 : Blo 778337 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B2957431 : Blo 778337 2957431 := bstep (se 1 (by rfl) ⟨2218073, by rfl⟩ : syracuseStep 2957431 = 4436147) B4436147
theorem B2105633 : Blo 778337 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B1319287 : Blo 778337 1319287 := bstep (se 1 (by rfl) ⟨989465, by rfl⟩ : syracuseStep 1319287 = 1978931) B1978931
theorem B7119251 : Blo 778337 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B3940811 : Blo 778337 3940811 := bstep (se 1 (by rfl) ⟨2955608, by rfl⟩ : syracuseStep 3940811 = 5911217) B5911217
theorem B1319483 : Blo 778337 1319483 := bstep (se 1 (by rfl) ⟨989612, by rfl⟩ : syracuseStep 1319483 = 1979225) B1979225
theorem B2368061 : Blo 778337 2368061 := bstep (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) B888023
theorem B2630231 : Blo 778337 2630231 := bstep (se 1 (by rfl) ⟨1972673, by rfl⟩ : syracuseStep 2630231 = 3945347) B3945347
theorem B3941135 : Blo 778337 3941135 := bstep (se 1 (by rfl) ⟨2955851, by rfl⟩ : syracuseStep 3941135 = 5911703) B5911703
theorem B1975175 : Blo 778337 1975175 := bstep (se 1 (by rfl) ⟨1481381, by rfl⟩ : syracuseStep 1975175 = 2962763) B2962763
theorem B1483667 : Blo 778337 1483667 := bstep (se 1 (by rfl) ⟨1112750, by rfl⟩ : syracuseStep 1483667 = 2225501) B2225501
theorem B1975225 : Blo 778337 1975225 := bstep (se 2 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 1975225 = 1481419) B1481419
theorem B1319881 : Blo 778337 1319881 := bstep (se 2 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 1319881 = 989911) B989911
theorem B2630717 : Blo 778337 2630717 := bstep (se 3 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 2630717 = 986519) B986519
theorem B2958403 : Blo 778337 2958403 := bstep (se 1 (by rfl) ⟨2218802, by rfl⟩ : syracuseStep 2958403 = 4437605) B4437605
theorem B1483895 : Blo 778337 1483895 := bstep (se 1 (by rfl) ⟨1112921, by rfl⟩ : syracuseStep 1483895 = 2225843) B2225843
theorem B2958707 : Blo 778337 2958707 := bstep (se 1 (by rfl) ⟨2219030, by rfl⟩ : syracuseStep 2958707 = 4438061) B4438061
theorem B1975823 : Blo 778337 1975823 := bstep (se 1 (by rfl) ⟨1481867, by rfl⟩ : syracuseStep 1975823 = 2963735) B2963735
theorem B2107081 : Blo 778337 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B2959163 : Blo 778337 2959163 := bstep (se 1 (by rfl) ⟨2219372, by rfl⟩ : syracuseStep 2959163 = 4438745) B4438745
theorem B2107255 : Blo 778337 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B3942593 : Blo 778337 3942593 := bstep (se 2 (by rfl) ⟨1478472, by rfl⟩ : syracuseStep 3942593 = 2956945) B2956945
theorem B1976521 : Blo 778337 1976521 := bstep (se 2 (by rfl) ⟨741195, by rfl⟩ : syracuseStep 1976521 = 1482391) B1482391
theorem B2959649 : Blo 778337 2959649 := bstep (se 2 (by rfl) ⟨1109868, by rfl⟩ : syracuseStep 2959649 = 2219737) B2219737
theorem B1976663 : Blo 778337 1976663 := bstep (se 1 (by rfl) ⟨1482497, by rfl⟩ : syracuseStep 1976663 = 2964995) B2964995
theorem B2369911 : Blo 778337 2369911 := bstep (se 1 (by rfl) ⟨1777433, by rfl⟩ : syracuseStep 2369911 = 3554867) B3554867
theorem B2632121 : Blo 778337 2632121 := bstep (se 2 (by rfl) ⟨987045, by rfl⟩ : syracuseStep 2632121 = 1974091) B1974091
theorem B8890883 : Blo 778337 8890883 := bstep (se 1 (by rfl) ⟨6668162, by rfl⟩ : syracuseStep 8890883 = 13336325) B13336325
theorem B2664971 : Blo 778337 2664971 := bstep (se 1 (by rfl) ⟨1998728, by rfl⟩ : syracuseStep 2664971 = 3997457) B3997457
theorem B4434689 : Blo 778337 4434689 := bstep (se 2 (by rfl) ⟨1663008, by rfl⟩ : syracuseStep 4434689 = 3326017) B3326017
theorem B2632715 : Blo 778337 2632715 := bstep (se 1 (by rfl) ⟨1974536, by rfl⟩ : syracuseStep 2632715 = 3949073) B3949073
theorem B1879055 : Blo 778337 1879055 := bstep (se 1 (by rfl) ⟨1409291, by rfl⟩ : syracuseStep 1879055 = 2818583) B2818583
theorem B2632823 : Blo 778337 2632823 := bstep (se 1 (by rfl) ⟨1974617, by rfl⟩ : syracuseStep 2632823 = 3949235) B3949235
theorem B4435145 : Blo 778337 4435145 := bstep (se 2 (by rfl) ⟨1663179, by rfl⟩ : syracuseStep 4435145 = 3326359) B3326359
theorem B2960621 : Blo 778337 2960621 := bstep (se 3 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 2960621 = 1110233) B1110233
theorem B2501921 : Blo 778337 2501921 := bstep (se 2 (by rfl) ⟨938220, by rfl⟩ : syracuseStep 2501921 = 1876441) B1876441
theorem B3943889 : Blo 778337 3943889 := bstep (se 2 (by rfl) ⟨1478958, by rfl⟩ : syracuseStep 3943889 = 2957917) B2957917
theorem B17346001 : Blo 778337 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B2633417 : Blo 778337 2633417 := bstep (se 2 (by rfl) ⟨987531, by rfl⟩ : syracuseStep 2633417 = 1975063) B1975063
theorem B2109331 : Blo 778337 2109331 := bstep (se 1 (by rfl) ⟨1581998, by rfl⟩ : syracuseStep 2109331 = 3163997) B3163997
theorem B2961305 : Blo 778337 2961305 := bstep (se 2 (by rfl) ⟨1110489, by rfl⟩ : syracuseStep 2961305 = 2220979) B2220979
theorem B2502971 : Blo 778337 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B1978739 : Blo 778337 1978739 := bstep (se 1 (by rfl) ⟨1484054, by rfl⟩ : syracuseStep 1978739 = 2968109) B2968109
theorem B2634119 : Blo 778337 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B2470297 : Blo 778337 2470297 := bstep (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) B1852723
theorem B2634497 : Blo 778337 2634497 := bstep (se 2 (by rfl) ⟨987936, by rfl⟩ : syracuseStep 2634497 = 1975873) B1975873
theorem B2962291 : Blo 778337 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B1979255 : Blo 778337 1979255 := bstep (se 1 (by rfl) ⟨1484441, by rfl⟩ : syracuseStep 1979255 = 2968883) B2968883
theorem B72955313 : Blo 778337 72955313 := bstep (se 2 (by rfl) ⟨27358242, by rfl⟩ : syracuseStep 72955313 = 54716485) B54716485
theorem B3945995 : Blo 778337 3945995 := bstep (se 1 (by rfl) ⟨2959496, by rfl⟩ : syracuseStep 3945995 = 5918993) B5918993
theorem B2635307 : Blo 778337 2635307 := bstep (se 1 (by rfl) ⟨1976480, by rfl⟩ : syracuseStep 2635307 = 3952961) B3952961
theorem B3946157 : Blo 778337 3946157 := bstep (se 3 (by rfl) ⟨739904, by rfl⟩ : syracuseStep 3946157 = 1479809) B1479809
theorem B2111233 : Blo 778337 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B2373437 : Blo 778337 2373437 := bstep (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) B890039
theorem B1980247 : Blo 778337 1980247 := bstep (se 1 (by rfl) ⟨1485185, by rfl⟩ : syracuseStep 1980247 = 2970371) B2970371
theorem B2504765 : Blo 778337 2504765 := bstep (se 3 (by rfl) ⟨469643, by rfl⟩ : syracuseStep 2504765 = 939287) B939287
theorem B9124013 : Blo 778337 9124013 := bstep (se 3 (by rfl) ⟨1710752, by rfl⟩ : syracuseStep 9124013 = 3421505) B3421505
theorem B7125383 : Blo 778337 7125383 := bstep (se 1 (by rfl) ⟨5344037, by rfl⟩ : syracuseStep 7125383 = 10688075) B10688075
theorem B4995587 : Blo 778337 4995587 := bstep (se 1 (by rfl) ⟨3746690, by rfl⟩ : syracuseStep 4995587 = 7493381) B7493381
theorem B2505277 : Blo 778337 2505277 := bstep (se 3 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 2505277 = 939479) B939479
theorem B1751687 : Blo 778337 1751687 := bstep (se 1 (by rfl) ⟨1313765, by rfl⟩ : syracuseStep 1751687 = 2627531) B2627531
theorem B1751867 : Blo 778337 1751867 := bstep (se 1 (by rfl) ⟨1313900, by rfl⟩ : syracuseStep 1751867 = 2627801) B2627801
theorem B2636603 : Blo 778337 2636603 := bstep (se 1 (by rfl) ⟨1977452, by rfl⟩ : syracuseStep 2636603 = 3954905) B3954905
theorem B1751993 : Blo 778337 1751993 := bstep (se 2 (by rfl) ⟨656997, by rfl⟩ : syracuseStep 1751993 = 1313995) B1313995
theorem B4439063 : Blo 778337 4439063 := bstep (se 1 (by rfl) ⟨3329297, by rfl⟩ : syracuseStep 4439063 = 6658595) B6658595
theorem B2964509 : Blo 778337 2964509 := bstep (se 3 (by rfl) ⟨555845, by rfl⟩ : syracuseStep 2964509 = 1111691) B1111691
theorem B3947777 : Blo 778337 3947777 := bstep (se 2 (by rfl) ⟨1480416, by rfl⟩ : syracuseStep 3947777 = 2960833) B2960833
theorem B1752335 : Blo 778337 1752335 := bstep (se 1 (by rfl) ⟨1314251, by rfl⟩ : syracuseStep 1752335 = 2628503) B2628503
theorem B1752353 : Blo 778337 1752353 := bstep (se 2 (by rfl) ⟨657132, by rfl⟩ : syracuseStep 1752353 = 1314265) B1314265
theorem B2637089 : Blo 778337 2637089 := bstep (se 2 (by rfl) ⟨988908, by rfl⟩ : syracuseStep 2637089 = 1977817) B1977817
theorem B69483835 : Blo 778337 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B3325319 : Blo 778337 3325319 := bstep (se 1 (by rfl) ⟨2493989, by rfl⟩ : syracuseStep 3325319 = 4987979) B4987979
theorem B2375065 : Blo 778337 2375065 := bstep (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) B1781299
theorem B10010141 : Blo 778337 10010141 := bstep (se 3 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 10010141 = 3753803) B3753803
theorem B19971683 : Blo 778337 19971683 := bstep (se 1 (by rfl) ⟨14978762, by rfl⟩ : syracuseStep 19971683 = 29957525) B29957525
theorem B1752695 : Blo 778337 1752695 := bstep (se 1 (by rfl) ⟨1314521, by rfl⟩ : syracuseStep 1752695 = 2629043) B2629043
theorem B2571895 : Blo 778337 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B2965193 : Blo 778337 2965193 := bstep (se 2 (by rfl) ⟨1111947, by rfl⟩ : syracuseStep 2965193 = 2223895) B2223895
theorem B1752875 : Blo 778337 1752875 := bstep (se 1 (by rfl) ⟨1314656, by rfl⟩ : syracuseStep 1752875 = 2629313) B2629313
theorem B2637683 : Blo 778337 2637683 := bstep (se 1 (by rfl) ⟨1978262, by rfl⟩ : syracuseStep 2637683 = 3956525) B3956525
theorem B2604953 : Blo 778337 2604953 := bstep (se 2 (by rfl) ⟨976857, by rfl⟩ : syracuseStep 2604953 = 1953715) B1953715
theorem B3948587 : Blo 778337 3948587 := bstep (se 1 (by rfl) ⟨2961440, by rfl⟩ : syracuseStep 3948587 = 5922881) B5922881
theorem B2670635 : Blo 778337 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1753235 : Blo 778337 1753235 := bstep (se 1 (by rfl) ⟨1314926, by rfl⟩ : syracuseStep 1753235 = 2629853) B2629853
theorem B1753289 : Blo 778337 1753289 := bstep (se 2 (by rfl) ⟨657483, by rfl⟩ : syracuseStep 1753289 = 1314967) B1314967
theorem B2670995 : Blo 778337 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B3162635 : Blo 778337 3162635 := bstep (se 1 (by rfl) ⟨2371976, by rfl⟩ : syracuseStep 3162635 = 4743953) B4743953
theorem B3162995 : Blo 778337 3162995 := bstep (se 1 (by rfl) ⟨2372246, by rfl⟩ : syracuseStep 3162995 = 4744493) B4744493
theorem B1753991 : Blo 778337 1753991 := bstep (se 1 (by rfl) ⟨1315493, by rfl⟩ : syracuseStep 1753991 = 2630987) B2630987
theorem B4440977 : Blo 778337 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B1754171 : Blo 778337 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B3327095 : Blo 778337 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B1754297 : Blo 778337 1754297 := bstep (se 2 (by rfl) ⟨657861, by rfl⟩ : syracuseStep 1754297 = 1315723) B1315723
theorem B3327247 : Blo 778337 3327247 := bstep (se 1 (by rfl) ⟨2495435, by rfl⟩ : syracuseStep 3327247 = 4990871) B4990871
theorem B3949883 : Blo 778337 3949883 := bstep (se 1 (by rfl) ⟨2962412, by rfl⟩ : syracuseStep 3949883 = 5924825) B5924825
theorem B3556723 : Blo 778337 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B2966969 : Blo 778337 2966969 := bstep (se 2 (by rfl) ⟨1112613, by rfl⟩ : syracuseStep 2966969 = 2225227) B2225227
theorem B3950045 : Blo 778337 3950045 := bstep (se 3 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 3950045 = 1481267) B1481267
theorem B1754639 : Blo 778337 1754639 := bstep (se 1 (by rfl) ⟨1315979, by rfl⟩ : syracuseStep 1754639 = 2631959) B2631959
theorem B1754657 : Blo 778337 1754657 := bstep (se 2 (by rfl) ⟨657996, by rfl⟩ : syracuseStep 1754657 = 1315993) B1315993
theorem B4441661 : Blo 778337 4441661 := bstep (se 3 (by rfl) ⟨832811, by rfl⟩ : syracuseStep 4441661 = 1665623) B1665623
theorem B32097869 : Blo 778337 32097869 := bstep (se 3 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 32097869 = 12036701) B12036701
theorem B3950369 : Blo 778337 3950369 := bstep (se 2 (by rfl) ⟨1481388, by rfl⟩ : syracuseStep 3950369 = 2962777) B2962777
theorem B1754999 : Blo 778337 1754999 := bstep (se 1 (by rfl) ⟨1316249, by rfl⟩ : syracuseStep 1754999 = 2632499) B2632499
theorem B18958283 : Blo 778337 18958283 := bstep (se 1 (by rfl) ⟨14218712, by rfl⟩ : syracuseStep 18958283 = 28437425) B28437425
theorem B1755179 : Blo 778337 1755179 := bstep (se 1 (by rfl) ⟨1316384, by rfl⟩ : syracuseStep 1755179 = 2632769) B2632769
theorem B3328067 : Blo 778337 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B14993525 : Blo 778337 14993525 := bstep (se 5 (by rfl) ⟨702821, by rfl⟩ : syracuseStep 14993525 = 1405643) B1405643
theorem B136726679 : Blo 778337 136726679 := bstep (se 1 (by rfl) ⟨102545009, by rfl⟩ : syracuseStep 136726679 = 205090019) B205090019
theorem B1755539 : Blo 778337 1755539 := bstep (se 1 (by rfl) ⟨1316654, by rfl⟩ : syracuseStep 1755539 = 2633309) B2633309
theorem B2640275 : Blo 778337 2640275 := bstep (se 1 (by rfl) ⟨1980206, by rfl⟩ : syracuseStep 2640275 = 3960413) B3960413
theorem B1755593 : Blo 778337 1755593 := bstep (se 2 (by rfl) ⟨658347, by rfl⟩ : syracuseStep 1755593 = 1316695) B1316695
theorem B3754669 : Blo 778337 3754669 := bstep (se 3 (by rfl) ⟨704000, by rfl⟩ : syracuseStep 3754669 = 1408001) B1408001
theorem B5065409 : Blo 778337 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B3951341 : Blo 778337 3951341 := bstep (se 3 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 3951341 = 1481753) B1481753
theorem B1756295 : Blo 778337 1756295 := bstep (se 1 (by rfl) ⟨1317221, by rfl⟩ : syracuseStep 1756295 = 2634443) B2634443
theorem B937207 : Blo 778337 937207 := bstep (se 1 (by rfl) ⟨702905, by rfl⟩ : syracuseStep 937207 = 1405811) B1405811
theorem B1756475 : Blo 778337 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B1756601 : Blo 778337 1756601 := bstep (se 2 (by rfl) ⟨658725, by rfl⟩ : syracuseStep 1756601 = 1317451) B1317451
theorem B10014137 : Blo 778337 10014137 := bstep (se 2 (by rfl) ⟨3755301, by rfl⟩ : syracuseStep 10014137 = 7510603) B7510603
theorem B3952151 : Blo 778337 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B4214315 : Blo 778337 4214315 := bstep (se 1 (by rfl) ⟨3160736, by rfl⟩ : syracuseStep 4214315 = 6321473) B6321473
theorem B8572517 : Blo 778337 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B1756943 : Blo 778337 1756943 := bstep (se 1 (by rfl) ⟨1317707, by rfl⟩ : syracuseStep 1756943 = 2635415) B2635415
theorem B1756961 : Blo 778337 1756961 := bstep (se 2 (by rfl) ⟨658860, by rfl⟩ : syracuseStep 1756961 = 1317721) B1317721
theorem B937999 : Blo 778337 937999 := bstep (se 1 (by rfl) ⟨703499, by rfl⟩ : syracuseStep 937999 = 1406999) B1406999
theorem B1757303 : Blo 778337 1757303 := bstep (se 1 (by rfl) ⟨1317977, by rfl⟩ : syracuseStep 1757303 = 2635955) B2635955
theorem B1167545 : Blo 778337 1167545 := bstep (se 2 (by rfl) ⟨437829, by rfl⟩ : syracuseStep 1167545 = 875659) B875659
theorem B1167623 : Blo 778337 1167623 := bstep (se 1 (by rfl) ⟨875717, by rfl⟩ : syracuseStep 1167623 = 1751435) B1751435
theorem B1167659 : Blo 778337 1167659 := bstep (se 1 (by rfl) ⟨875744, by rfl⟩ : syracuseStep 1167659 = 1751489) B1751489
theorem B1757483 : Blo 778337 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B1167689 : Blo 778337 1167689 := bstep (se 2 (by rfl) ⟨437883, by rfl⟩ : syracuseStep 1167689 = 875767) B875767
theorem B1167803 : Blo 778337 1167803 := bstep (se 1 (by rfl) ⟨875852, by rfl⟩ : syracuseStep 1167803 = 1751705) B1751705
theorem B4280779 : Blo 778337 4280779 := bstep (se 1 (by rfl) ⟨3210584, by rfl⟩ : syracuseStep 4280779 = 6421169) B6421169
theorem B1167863 : Blo 778337 1167863 := bstep (se 1 (by rfl) ⟨875897, by rfl⟩ : syracuseStep 1167863 = 1751795) B1751795
theorem B6771203 : Blo 778337 6771203 := bstep (se 1 (by rfl) ⟨5078402, by rfl⟩ : syracuseStep 6771203 = 10156805) B10156805
theorem B1167887 : Blo 778337 1167887 := bstep (se 1 (by rfl) ⟨875915, by rfl⟩ : syracuseStep 1167887 = 1751831) B1751831
theorem B1167929 : Blo 778337 1167929 := bstep (se 2 (by rfl) ⟨437973, by rfl⟩ : syracuseStep 1167929 = 875947) B875947
theorem B1168007 : Blo 778337 1168007 := bstep (se 1 (by rfl) ⟨876005, by rfl⟩ : syracuseStep 1168007 = 1752011) B1752011
theorem B1757843 : Blo 778337 1757843 := bstep (se 1 (by rfl) ⟨1318382, by rfl⟩ : syracuseStep 1757843 = 2636765) B2636765
theorem B1168043 : Blo 778337 1168043 := bstep (se 1 (by rfl) ⟨876032, by rfl⟩ : syracuseStep 1168043 = 1752065) B1752065
theorem B1168073 : Blo 778337 1168073 := bstep (se 2 (by rfl) ⟨438027, by rfl⟩ : syracuseStep 1168073 = 876055) B876055
theorem B1757897 : Blo 778337 1757897 := bstep (se 2 (by rfl) ⟨659211, by rfl⟩ : syracuseStep 1757897 = 1318423) B1318423
theorem B1168187 : Blo 778337 1168187 := bstep (se 1 (by rfl) ⟨876140, by rfl⟩ : syracuseStep 1168187 = 1752281) B1752281
theorem B1168247 : Blo 778337 1168247 := bstep (se 1 (by rfl) ⟨876185, by rfl⟩ : syracuseStep 1168247 = 1752371) B1752371
theorem B1168271 : Blo 778337 1168271 := bstep (se 1 (by rfl) ⟨876203, by rfl⟩ : syracuseStep 1168271 = 1752407) B1752407
theorem B1168313 : Blo 778337 1168313 := bstep (se 2 (by rfl) ⟨438117, by rfl⟩ : syracuseStep 1168313 = 876235) B876235
theorem B938999 : Blo 778337 938999 := bstep (se 1 (by rfl) ⟨704249, by rfl⟩ : syracuseStep 938999 = 1408499) B1408499
theorem B1168391 : Blo 778337 1168391 := bstep (se 1 (by rfl) ⟨876293, by rfl⟩ : syracuseStep 1168391 = 1752587) B1752587
theorem B1168427 : Blo 778337 1168427 := bstep (se 1 (by rfl) ⟨876320, by rfl⟩ : syracuseStep 1168427 = 1752641) B1752641
theorem B1168457 : Blo 778337 1168457 := bstep (se 2 (by rfl) ⟨438171, by rfl⟩ : syracuseStep 1168457 = 876343) B876343
theorem B2217095 : Blo 778337 2217095 := bstep (se 1 (by rfl) ⟨1662821, by rfl⟩ : syracuseStep 2217095 = 3325643) B3325643
theorem B1168571 : Blo 778337 1168571 := bstep (se 1 (by rfl) ⟨876428, by rfl⟩ : syracuseStep 1168571 = 1752857) B1752857
theorem B1168631 : Blo 778337 1168631 := bstep (se 1 (by rfl) ⟨876473, by rfl⟩ : syracuseStep 1168631 = 1752947) B1752947
theorem B1168655 : Blo 778337 1168655 := bstep (se 1 (by rfl) ⟨876491, by rfl⟩ : syracuseStep 1168655 = 1752983) B1752983
theorem B1168697 : Blo 778337 1168697 := bstep (se 2 (by rfl) ⟨438261, by rfl⟩ : syracuseStep 1168697 = 876523) B876523
theorem B1168775 : Blo 778337 1168775 := bstep (se 1 (by rfl) ⟨876581, by rfl⟩ : syracuseStep 1168775 = 1753163) B1753163
theorem B1758599 : Blo 778337 1758599 := bstep (se 1 (by rfl) ⟨1318949, by rfl⟩ : syracuseStep 1758599 = 2637899) B2637899
theorem B1168811 : Blo 778337 1168811 := bstep (se 1 (by rfl) ⟨876608, by rfl⟩ : syracuseStep 1168811 = 1753217) B1753217
theorem B939451 : Blo 778337 939451 := bstep (se 1 (by rfl) ⟨704588, by rfl⟩ : syracuseStep 939451 = 1409177) B1409177
theorem B1168841 : Blo 778337 1168841 := bstep (se 2 (by rfl) ⟨438315, by rfl⟩ : syracuseStep 1168841 = 876631) B876631
theorem B2283041 : Blo 778337 2283041 := bstep (se 2 (by rfl) ⟨856140, by rfl⟩ : syracuseStep 2283041 = 1712281) B1712281
theorem B1168955 : Blo 778337 1168955 := bstep (se 1 (by rfl) ⟨876716, by rfl⟩ : syracuseStep 1168955 = 1753433) B1753433
theorem B1758779 : Blo 778337 1758779 := bstep (se 1 (by rfl) ⟨1319084, by rfl⟩ : syracuseStep 1758779 = 2638169) B2638169
theorem B1169015 : Blo 778337 1169015 := bstep (se 1 (by rfl) ⟨876761, by rfl⟩ : syracuseStep 1169015 = 1753523) B1753523
theorem B1169039 : Blo 778337 1169039 := bstep (se 1 (by rfl) ⟨876779, by rfl⟩ : syracuseStep 1169039 = 1753559) B1753559
theorem B939691 : Blo 778337 939691 := bstep (se 1 (by rfl) ⟨704768, by rfl⟩ : syracuseStep 939691 = 1409537) B1409537
theorem B8115889 : Blo 778337 8115889 := bstep (se 2 (by rfl) ⟨3043458, by rfl⟩ : syracuseStep 8115889 = 6086917) B6086917
theorem B1169081 : Blo 778337 1169081 := bstep (se 2 (by rfl) ⟨438405, by rfl⟩ : syracuseStep 1169081 = 876811) B876811
theorem B1758905 : Blo 778337 1758905 := bstep (se 2 (by rfl) ⟨659589, by rfl⟩ : syracuseStep 1758905 = 1319179) B1319179
theorem B6674177 : Blo 778337 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B1169159 : Blo 778337 1169159 := bstep (se 1 (by rfl) ⟨876869, by rfl⟩ : syracuseStep 1169159 = 1753739) B1753739
theorem B2807585 : Blo 778337 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B1169195 : Blo 778337 1169195 := bstep (se 1 (by rfl) ⟨876896, by rfl⟩ : syracuseStep 1169195 = 1753793) B1753793
theorem B1169225 : Blo 778337 1169225 := bstep (se 2 (by rfl) ⟨438459, by rfl⟩ : syracuseStep 1169225 = 876919) B876919
theorem B2217881 : Blo 778337 2217881 := bstep (se 2 (by rfl) ⟨831705, by rfl⟩ : syracuseStep 2217881 = 1663411) B1663411
theorem B9983897 : Blo 778337 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B1169339 : Blo 778337 1169339 := bstep (se 1 (by rfl) ⟨877004, by rfl⟩ : syracuseStep 1169339 = 1754009) B1754009
theorem B1169399 : Blo 778337 1169399 := bstep (se 1 (by rfl) ⟨877049, by rfl⟩ : syracuseStep 1169399 = 1754099) B1754099
theorem B1169423 : Blo 778337 1169423 := bstep (se 1 (by rfl) ⟨877067, by rfl⟩ : syracuseStep 1169423 = 1754135) B1754135
theorem B1759247 : Blo 778337 1759247 := bstep (se 1 (by rfl) ⟨1319435, by rfl⟩ : syracuseStep 1759247 = 2638871) B2638871
theorem B1759265 : Blo 778337 1759265 := bstep (se 2 (by rfl) ⟨659724, by rfl⟩ : syracuseStep 1759265 = 1319449) B1319449
theorem B1169465 : Blo 778337 1169465 := bstep (se 2 (by rfl) ⟨438549, by rfl⟩ : syracuseStep 1169465 = 877099) B877099
theorem B3758147 : Blo 778337 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B16898165 : Blo 778337 16898165 := bstep (se 5 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 16898165 = 1584203) B1584203
theorem B1169543 : Blo 778337 1169543 := bstep (se 1 (by rfl) ⟨877157, by rfl⟩ : syracuseStep 1169543 = 1754315) B1754315
theorem B1169579 : Blo 778337 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B1169609 : Blo 778337 1169609 := bstep (se 2 (by rfl) ⟨438603, by rfl⟩ : syracuseStep 1169609 = 877207) B877207
theorem B1169723 : Blo 778337 1169723 := bstep (se 1 (by rfl) ⟨877292, by rfl⟩ : syracuseStep 1169723 = 1754585) B1754585
theorem B3168571 : Blo 778337 3168571 := bstep (se 1 (by rfl) ⟨2376428, by rfl⟩ : syracuseStep 3168571 = 4752857) B4752857
theorem B1169783 : Blo 778337 1169783 := bstep (se 1 (by rfl) ⟨877337, by rfl⟩ : syracuseStep 1169783 = 1754675) B1754675
theorem B1759607 : Blo 778337 1759607 := bstep (se 1 (by rfl) ⟨1319705, by rfl⟩ : syracuseStep 1759607 = 2639411) B2639411
theorem B1169807 : Blo 778337 1169807 := bstep (se 1 (by rfl) ⟨877355, by rfl⟩ : syracuseStep 1169807 = 1754711) B1754711
theorem B1169849 : Blo 778337 1169849 := bstep (se 2 (by rfl) ⟨438693, by rfl⟩ : syracuseStep 1169849 = 877387) B877387
theorem B1169927 : Blo 778337 1169927 := bstep (se 1 (by rfl) ⟨877445, by rfl⟩ : syracuseStep 1169927 = 1754891) B1754891
theorem B3955229 : Blo 778337 3955229 := bstep (se 3 (by rfl) ⟨741605, by rfl⟩ : syracuseStep 3955229 = 1483211) B1483211
theorem B2218529 : Blo 778337 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B1169963 : Blo 778337 1169963 := bstep (se 1 (by rfl) ⟨877472, by rfl⟩ : syracuseStep 1169963 = 1754945) B1754945
theorem B1759787 : Blo 778337 1759787 := bstep (se 1 (by rfl) ⟨1319840, by rfl⟩ : syracuseStep 1759787 = 2639681) B2639681
theorem B1169993 : Blo 778337 1169993 := bstep (se 2 (by rfl) ⟨438747, by rfl⟩ : syracuseStep 1169993 = 877495) B877495
theorem B3005047 : Blo 778337 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B1170107 : Blo 778337 1170107 := bstep (se 1 (by rfl) ⟨877580, by rfl⟩ : syracuseStep 1170107 = 1755161) B1755161
theorem B1170167 : Blo 778337 1170167 := bstep (se 1 (by rfl) ⟨877625, by rfl⟩ : syracuseStep 1170167 = 1755251) B1755251
theorem B1170191 : Blo 778337 1170191 := bstep (se 1 (by rfl) ⟨877643, by rfl⟩ : syracuseStep 1170191 = 1755287) B1755287
theorem B1170233 : Blo 778337 1170233 := bstep (se 2 (by rfl) ⟨438837, by rfl⟩ : syracuseStep 1170233 = 877675) B877675
theorem B1170311 : Blo 778337 1170311 := bstep (se 1 (by rfl) ⟨877733, by rfl⟩ : syracuseStep 1170311 = 1755467) B1755467
theorem B3758993 : Blo 778337 3758993 := bstep (se 2 (by rfl) ⟨1409622, by rfl⟩ : syracuseStep 3758993 = 2819245) B2819245
theorem B1760147 : Blo 778337 1760147 := bstep (se 1 (by rfl) ⟨1320110, by rfl⟩ : syracuseStep 1760147 = 2640221) B2640221
theorem B1170347 : Blo 778337 1170347 := bstep (se 1 (by rfl) ⟨877760, by rfl⟩ : syracuseStep 1170347 = 1755521) B1755521
theorem B1170377 : Blo 778337 1170377 := bstep (se 2 (by rfl) ⟨438891, by rfl⟩ : syracuseStep 1170377 = 877783) B877783
theorem B1760201 : Blo 778337 1760201 := bstep (se 2 (by rfl) ⟨660075, by rfl⟩ : syracuseStep 1760201 = 1320151) B1320151
theorem B3955715 : Blo 778337 3955715 := bstep (se 1 (by rfl) ⟨2966786, by rfl⟩ : syracuseStep 3955715 = 5933573) B5933573
theorem B1170491 : Blo 778337 1170491 := bstep (se 1 (by rfl) ⟨877868, by rfl⟩ : syracuseStep 1170491 = 1755737) B1755737
theorem B1170551 : Blo 778337 1170551 := bstep (se 1 (by rfl) ⟨877913, by rfl⟩ : syracuseStep 1170551 = 1755827) B1755827
theorem B1170575 : Blo 778337 1170575 := bstep (se 1 (by rfl) ⟨877931, by rfl⟩ : syracuseStep 1170575 = 1755863) B1755863
theorem B1170617 : Blo 778337 1170617 := bstep (se 2 (by rfl) ⟨438981, by rfl⟩ : syracuseStep 1170617 = 877963) B877963
theorem B1170695 : Blo 778337 1170695 := bstep (se 1 (by rfl) ⟨878021, by rfl⟩ : syracuseStep 1170695 = 1756043) B1756043
theorem B1170731 : Blo 778337 1170731 := bstep (se 1 (by rfl) ⟨878048, by rfl⟩ : syracuseStep 1170731 = 1756097) B1756097
theorem B1170761 : Blo 778337 1170761 := bstep (se 2 (by rfl) ⟨439035, by rfl⟩ : syracuseStep 1170761 = 878071) B878071
theorem B4742489 : Blo 778337 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B875911 : Blo 778337 875911 := bstep (se 1 (by rfl) ⟨656933, by rfl⟩ : syracuseStep 875911 = 1313867) B1313867
theorem B1170875 : Blo 778337 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B7101917 : Blo 778337 7101917 := bstep (se 3 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 7101917 = 2663219) B2663219
theorem B1170935 : Blo 778337 1170935 := bstep (se 1 (by rfl) ⟨878201, by rfl⟩ : syracuseStep 1170935 = 1756403) B1756403
theorem B2219521 : Blo 778337 2219521 := bstep (se 2 (by rfl) ⟨832320, by rfl⟩ : syracuseStep 2219521 = 1664641) B1664641
theorem B1170959 : Blo 778337 1170959 := bstep (se 1 (by rfl) ⟨878219, by rfl⟩ : syracuseStep 1170959 = 1756439) B1756439
theorem B1171001 : Blo 778337 1171001 := bstep (se 2 (by rfl) ⟨439125, by rfl⟩ : syracuseStep 1171001 = 878251) B878251
theorem B876091 : Blo 778337 876091 := bstep (se 1 (by rfl) ⟨657068, by rfl⟩ : syracuseStep 876091 = 1314137) B1314137
theorem B4447811 : Blo 778337 4447811 := bstep (se 1 (by rfl) ⟨3335858, by rfl⟩ : syracuseStep 4447811 = 6671717) B6671717
theorem B24010339 : Blo 778337 24010339 := bstep (se 1 (by rfl) ⟨18007754, by rfl⟩ : syracuseStep 24010339 = 36015509) B36015509
theorem B1662599 : Blo 778337 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B1171079 : Blo 778337 1171079 := bstep (se 1 (by rfl) ⟨878309, by rfl⟩ : syracuseStep 1171079 = 1756619) B1756619
theorem B1171115 : Blo 778337 1171115 := bstep (se 1 (by rfl) ⟨878336, by rfl⟩ : syracuseStep 1171115 = 1756673) B1756673
theorem B1171145 : Blo 778337 1171145 := bstep (se 2 (by rfl) ⟨439179, by rfl⟩ : syracuseStep 1171145 = 878359) B878359
theorem B1171259 : Blo 778337 1171259 := bstep (se 1 (by rfl) ⟨878444, by rfl⟩ : syracuseStep 1171259 = 1756889) B1756889
theorem B1171319 : Blo 778337 1171319 := bstep (se 1 (by rfl) ⟨878489, by rfl⟩ : syracuseStep 1171319 = 1756979) B1756979
theorem B1171343 : Blo 778337 1171343 := bstep (se 1 (by rfl) ⟨878507, by rfl⟩ : syracuseStep 1171343 = 1757015) B1757015
theorem B1171385 : Blo 778337 1171385 := bstep (se 2 (by rfl) ⟨439269, by rfl⟩ : syracuseStep 1171385 = 878539) B878539
theorem B1171463 : Blo 778337 1171463 := bstep (se 1 (by rfl) ⟨878597, by rfl⟩ : syracuseStep 1171463 = 1757195) B1757195
theorem B4448267 : Blo 778337 4448267 := bstep (se 1 (by rfl) ⟨3336200, by rfl⟩ : syracuseStep 4448267 = 6672401) B6672401
theorem B876559 : Blo 778337 876559 := bstep (se 1 (by rfl) ⟨657419, by rfl⟩ : syracuseStep 876559 = 1314839) B1314839
theorem B1171499 : Blo 778337 1171499 := bstep (se 1 (by rfl) ⟨878624, by rfl⟩ : syracuseStep 1171499 = 1757249) B1757249
theorem B1171529 : Blo 778337 1171529 := bstep (se 2 (by rfl) ⟨439323, by rfl⟩ : syracuseStep 1171529 = 878647) B878647
theorem B778375 : Blo 778337 778375 := bstep (se 1 (by rfl) ⟨583781, by rfl⟩ : syracuseStep 778375 = 1167563) B1167563
theorem B778383 : Blo 778337 778383 := bstep (se 1 (by rfl) ⟨583787, by rfl⟩ : syracuseStep 778383 = 1167575) B1167575
theorem B778427 : Blo 778337 778427 := bstep (se 1 (by rfl) ⟨583820, by rfl⟩ : syracuseStep 778427 = 1167641) B1167641
theorem B1171643 : Blo 778337 1171643 := bstep (se 1 (by rfl) ⟨878732, by rfl⟩ : syracuseStep 1171643 = 1757465) B1757465
theorem B1171703 : Blo 778337 1171703 := bstep (se 1 (by rfl) ⟨878777, by rfl⟩ : syracuseStep 1171703 = 1757555) B1757555
theorem B778503 : Blo 778337 778503 := bstep (se 1 (by rfl) ⟨583877, by rfl⟩ : syracuseStep 778503 = 1167755) B1167755
theorem B778511 : Blo 778337 778511 := bstep (se 1 (by rfl) ⟨583883, by rfl⟩ : syracuseStep 778511 = 1167767) B1167767
theorem B1171727 : Blo 778337 1171727 := bstep (se 1 (by rfl) ⟨878795, by rfl⟩ : syracuseStep 1171727 = 1757591) B1757591
theorem B1171769 : Blo 778337 1171769 := bstep (se 2 (by rfl) ⟨439413, by rfl⟩ : syracuseStep 1171769 = 878827) B878827
theorem B1204537 : Blo 778337 1204537 := bstep (se 2 (by rfl) ⟨451701, by rfl⟩ : syracuseStep 1204537 = 903403) B903403
theorem B778555 : Blo 778337 778555 := bstep (se 1 (by rfl) ⟨583916, by rfl⟩ : syracuseStep 778555 = 1167833) B1167833
theorem B778631 : Blo 778337 778631 := bstep (se 1 (by rfl) ⟨583973, by rfl⟩ : syracuseStep 778631 = 1167947) B1167947
theorem B1171847 : Blo 778337 1171847 := bstep (se 1 (by rfl) ⟨878885, by rfl⟩ : syracuseStep 1171847 = 1757771) B1757771
theorem B778639 : Blo 778337 778639 := bstep (se 1 (by rfl) ⟨583979, by rfl⟩ : syracuseStep 778639 = 1167959) B1167959
theorem B1171883 : Blo 778337 1171883 := bstep (se 1 (by rfl) ⟨878912, by rfl⟩ : syracuseStep 1171883 = 1757825) B1757825
theorem B778683 : Blo 778337 778683 := bstep (se 1 (by rfl) ⟨584012, by rfl⟩ : syracuseStep 778683 = 1168025) B1168025
theorem B1171913 : Blo 778337 1171913 := bstep (se 2 (by rfl) ⟨439467, by rfl⟩ : syracuseStep 1171913 = 878935) B878935
theorem B778759 : Blo 778337 778759 := bstep (se 1 (by rfl) ⟨584069, by rfl⟩ : syracuseStep 778759 = 1168139) B1168139
theorem B877063 : Blo 778337 877063 := bstep (se 1 (by rfl) ⟨657797, by rfl⟩ : syracuseStep 877063 = 1315595) B1315595
theorem B778767 : Blo 778337 778767 := bstep (se 1 (by rfl) ⟨584075, by rfl⟩ : syracuseStep 778767 = 1168151) B1168151
theorem B3007019 : Blo 778337 3007019 := bstep (se 1 (by rfl) ⟨2255264, by rfl⟩ : syracuseStep 3007019 = 4510529) B4510529
theorem B778811 : Blo 778337 778811 := bstep (se 1 (by rfl) ⟨584108, by rfl⟩ : syracuseStep 778811 = 1168217) B1168217
theorem B1172027 : Blo 778337 1172027 := bstep (se 1 (by rfl) ⟨879020, by rfl⟩ : syracuseStep 1172027 = 1758041) B1758041
theorem B3957335 : Blo 778337 3957335 := bstep (se 1 (by rfl) ⟨2968001, by rfl⟩ : syracuseStep 3957335 = 5936003) B5936003
theorem B1172087 : Blo 778337 1172087 := bstep (se 1 (by rfl) ⟨879065, by rfl⟩ : syracuseStep 1172087 = 1758131) B1758131
theorem B778887 : Blo 778337 778887 := bstep (se 1 (by rfl) ⟨584165, by rfl⟩ : syracuseStep 778887 = 1168331) B1168331
theorem B778895 : Blo 778337 778895 := bstep (se 1 (by rfl) ⟨584171, by rfl⟩ : syracuseStep 778895 = 1168343) B1168343
theorem B1172111 : Blo 778337 1172111 := bstep (se 1 (by rfl) ⟨879083, by rfl⟩ : syracuseStep 1172111 = 1758167) B1758167
theorem B1172153 : Blo 778337 1172153 := bstep (se 2 (by rfl) ⟨439557, by rfl⟩ : syracuseStep 1172153 = 879115) B879115
theorem B778939 : Blo 778337 778939 := bstep (se 1 (by rfl) ⟨584204, by rfl⟩ : syracuseStep 778939 = 1168409) B1168409
theorem B877243 : Blo 778337 877243 := bstep (se 1 (by rfl) ⟨657932, by rfl⟩ : syracuseStep 877243 = 1315865) B1315865
theorem B779015 : Blo 778337 779015 := bstep (se 1 (by rfl) ⟨584261, by rfl⟩ : syracuseStep 779015 = 1168523) B1168523
theorem B1172231 : Blo 778337 1172231 := bstep (se 1 (by rfl) ⟨879173, by rfl⟩ : syracuseStep 1172231 = 1758347) B1758347
theorem B779023 : Blo 778337 779023 := bstep (se 1 (by rfl) ⟨584267, by rfl⟩ : syracuseStep 779023 = 1168535) B1168535
theorem B24044323 : Blo 778337 24044323 := bstep (se 1 (by rfl) ⟨18033242, by rfl⟩ : syracuseStep 24044323 = 36066485) B36066485
theorem B1172267 : Blo 778337 1172267 := bstep (se 1 (by rfl) ⟨879200, by rfl⟩ : syracuseStep 1172267 = 1758401) B1758401
theorem B779067 : Blo 778337 779067 := bstep (se 1 (by rfl) ⟨584300, by rfl⟩ : syracuseStep 779067 = 1168601) B1168601
theorem B1172297 : Blo 778337 1172297 := bstep (se 2 (by rfl) ⟨439611, by rfl⟩ : syracuseStep 1172297 = 879223) B879223
theorem B779143 : Blo 778337 779143 := bstep (se 1 (by rfl) ⟨584357, by rfl⟩ : syracuseStep 779143 = 1168715) B1168715
theorem B779151 : Blo 778337 779151 := bstep (se 1 (by rfl) ⟨584363, by rfl⟩ : syracuseStep 779151 = 1168727) B1168727
theorem B10838947 : Blo 778337 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B779195 : Blo 778337 779195 := bstep (se 1 (by rfl) ⟨584396, by rfl⟩ : syracuseStep 779195 = 1168793) B1168793
theorem B1172411 : Blo 778337 1172411 := bstep (se 1 (by rfl) ⟨879308, by rfl⟩ : syracuseStep 1172411 = 1758617) B1758617
theorem B1172471 : Blo 778337 1172471 := bstep (se 1 (by rfl) ⟨879353, by rfl⟩ : syracuseStep 1172471 = 1758707) B1758707
theorem B779271 : Blo 778337 779271 := bstep (se 1 (by rfl) ⟨584453, by rfl⟩ : syracuseStep 779271 = 1168907) B1168907
theorem B2024459 : Blo 778337 2024459 := bstep (se 1 (by rfl) ⟨1518344, by rfl⟩ : syracuseStep 2024459 = 3036689) B3036689
theorem B779279 : Blo 778337 779279 := bstep (se 1 (by rfl) ⟨584459, by rfl⟩ : syracuseStep 779279 = 1168919) B1168919
theorem B1172495 : Blo 778337 1172495 := bstep (se 1 (by rfl) ⟨879371, by rfl⟩ : syracuseStep 1172495 = 1758743) B1758743
theorem B1172537 : Blo 778337 1172537 := bstep (se 2 (by rfl) ⟨439701, by rfl⟩ : syracuseStep 1172537 = 879403) B879403
theorem B779323 : Blo 778337 779323 := bstep (se 1 (by rfl) ⟨584492, by rfl⟩ : syracuseStep 779323 = 1168985) B1168985
theorem B3957821 : Blo 778337 3957821 := bstep (se 3 (by rfl) ⟨742091, by rfl⟩ : syracuseStep 3957821 = 1484183) B1484183
theorem B779399 : Blo 778337 779399 := bstep (se 1 (by rfl) ⟨584549, by rfl⟩ : syracuseStep 779399 = 1169099) B1169099
theorem B1172615 : Blo 778337 1172615 := bstep (se 1 (by rfl) ⟨879461, by rfl⟩ : syracuseStep 1172615 = 1758923) B1758923
theorem B779407 : Blo 778337 779407 := bstep (se 1 (by rfl) ⟨584555, by rfl⟩ : syracuseStep 779407 = 1169111) B1169111
theorem B877711 : Blo 778337 877711 := bstep (se 1 (by rfl) ⟨658283, by rfl⟩ : syracuseStep 877711 = 1316567) B1316567
theorem B1172651 : Blo 778337 1172651 := bstep (se 1 (by rfl) ⟨879488, by rfl⟩ : syracuseStep 1172651 = 1758977) B1758977
theorem B779451 : Blo 778337 779451 := bstep (se 1 (by rfl) ⟨584588, by rfl⟩ : syracuseStep 779451 = 1169177) B1169177
theorem B1172681 : Blo 778337 1172681 := bstep (se 2 (by rfl) ⟨439755, by rfl⟩ : syracuseStep 1172681 = 879511) B879511
theorem B779527 : Blo 778337 779527 := bstep (se 1 (by rfl) ⟨584645, by rfl⟩ : syracuseStep 779527 = 1169291) B1169291
theorem B779535 : Blo 778337 779535 := bstep (se 1 (by rfl) ⟨584651, by rfl⟩ : syracuseStep 779535 = 1169303) B1169303
theorem B779579 : Blo 778337 779579 := bstep (se 1 (by rfl) ⟨584684, by rfl⟩ : syracuseStep 779579 = 1169369) B1169369
theorem B1172795 : Blo 778337 1172795 := bstep (se 1 (by rfl) ⟨879596, by rfl⟩ : syracuseStep 1172795 = 1759193) B1759193
theorem B1172855 : Blo 778337 1172855 := bstep (se 1 (by rfl) ⟨879641, by rfl⟩ : syracuseStep 1172855 = 1759283) B1759283
theorem B779655 : Blo 778337 779655 := bstep (se 1 (by rfl) ⟨584741, by rfl⟩ : syracuseStep 779655 = 1169483) B1169483
theorem B779663 : Blo 778337 779663 := bstep (se 1 (by rfl) ⟨584747, by rfl⟩ : syracuseStep 779663 = 1169495) B1169495
theorem B1172879 : Blo 778337 1172879 := bstep (se 1 (by rfl) ⟨879659, by rfl⟩ : syracuseStep 1172879 = 1759319) B1759319
theorem B1172921 : Blo 778337 1172921 := bstep (se 2 (by rfl) ⟨439845, by rfl⟩ : syracuseStep 1172921 = 879691) B879691
theorem B779707 : Blo 778337 779707 := bstep (se 1 (by rfl) ⟨584780, by rfl⟩ : syracuseStep 779707 = 1169561) B1169561
theorem B779783 : Blo 778337 779783 := bstep (se 1 (by rfl) ⟨584837, by rfl⟩ : syracuseStep 779783 = 1169675) B1169675
theorem B1172999 : Blo 778337 1172999 := bstep (se 1 (by rfl) ⟨879749, by rfl⟩ : syracuseStep 1172999 = 1759499) B1759499
theorem B779791 : Blo 778337 779791 := bstep (se 1 (by rfl) ⟨584843, by rfl⟩ : syracuseStep 779791 = 1169687) B1169687
theorem B1173035 : Blo 778337 1173035 := bstep (se 1 (by rfl) ⟨879776, by rfl⟩ : syracuseStep 1173035 = 1759553) B1759553
theorem B779835 : Blo 778337 779835 := bstep (se 1 (by rfl) ⟨584876, by rfl⟩ : syracuseStep 779835 = 1169753) B1169753
theorem B1173065 : Blo 778337 1173065 := bstep (se 2 (by rfl) ⟨439899, by rfl⟩ : syracuseStep 1173065 = 879799) B879799
theorem B779911 : Blo 778337 779911 := bstep (se 1 (by rfl) ⟨584933, by rfl⟩ : syracuseStep 779911 = 1169867) B1169867
theorem B878215 : Blo 778337 878215 := bstep (se 1 (by rfl) ⟨658661, by rfl⟩ : syracuseStep 878215 = 1317323) B1317323
theorem B779919 : Blo 778337 779919 := bstep (se 1 (by rfl) ⟨584939, by rfl⟩ : syracuseStep 779919 = 1169879) B1169879
theorem B7988915 : Blo 778337 7988915 := bstep (se 1 (by rfl) ⟨5991686, by rfl⟩ : syracuseStep 7988915 = 11983373) B11983373
theorem B779963 : Blo 778337 779963 := bstep (se 1 (by rfl) ⟨584972, by rfl⟩ : syracuseStep 779963 = 1169945) B1169945
theorem B1173179 : Blo 778337 1173179 := bstep (se 1 (by rfl) ⟨879884, by rfl⟩ : syracuseStep 1173179 = 1759769) B1759769
theorem B1173239 : Blo 778337 1173239 := bstep (se 1 (by rfl) ⟨879929, by rfl⟩ : syracuseStep 1173239 = 1759859) B1759859
theorem B780039 : Blo 778337 780039 := bstep (se 1 (by rfl) ⟨585029, by rfl⟩ : syracuseStep 780039 = 1170059) B1170059
theorem B780047 : Blo 778337 780047 := bstep (se 1 (by rfl) ⟨585035, by rfl⟩ : syracuseStep 780047 = 1170071) B1170071
theorem B1173263 : Blo 778337 1173263 := bstep (se 1 (by rfl) ⟨879947, by rfl⟩ : syracuseStep 1173263 = 1759895) B1759895
theorem B1173305 : Blo 778337 1173305 := bstep (se 2 (by rfl) ⟨439989, by rfl⟩ : syracuseStep 1173305 = 879979) B879979
theorem B780091 : Blo 778337 780091 := bstep (se 1 (by rfl) ⟨585068, by rfl⟩ : syracuseStep 780091 = 1170137) B1170137
theorem B878395 : Blo 778337 878395 := bstep (se 1 (by rfl) ⟨658796, by rfl⟩ : syracuseStep 878395 = 1317593) B1317593
theorem B3335995 : Blo 778337 3335995 := bstep (se 1 (by rfl) ⟨2501996, by rfl⟩ : syracuseStep 3335995 = 5003993) B5003993
theorem B780167 : Blo 778337 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B1173383 : Blo 778337 1173383 := bstep (se 1 (by rfl) ⟨880037, by rfl⟩ : syracuseStep 1173383 = 1760075) B1760075
theorem B780175 : Blo 778337 780175 := bstep (se 1 (by rfl) ⟨585131, by rfl⟩ : syracuseStep 780175 = 1170263) B1170263
theorem B1173419 : Blo 778337 1173419 := bstep (se 1 (by rfl) ⟨880064, by rfl⟩ : syracuseStep 1173419 = 1760129) B1760129
theorem B780219 : Blo 778337 780219 := bstep (se 1 (by rfl) ⟨585164, by rfl⟩ : syracuseStep 780219 = 1170329) B1170329
theorem B1173449 : Blo 778337 1173449 := bstep (se 2 (by rfl) ⟨440043, by rfl⟩ : syracuseStep 1173449 = 880087) B880087
theorem B780295 : Blo 778337 780295 := bstep (se 1 (by rfl) ⟨585221, by rfl⟩ : syracuseStep 780295 = 1170443) B1170443
theorem B780303 : Blo 778337 780303 := bstep (se 1 (by rfl) ⟨585227, by rfl⟩ : syracuseStep 780303 = 1170455) B1170455
theorem B6678551 : Blo 778337 6678551 := bstep (se 1 (by rfl) ⟨5008913, by rfl⟩ : syracuseStep 6678551 = 10017827) B10017827
theorem B780347 : Blo 778337 780347 := bstep (se 1 (by rfl) ⟨585260, by rfl⟩ : syracuseStep 780347 = 1170521) B1170521
theorem B780423 : Blo 778337 780423 := bstep (se 1 (by rfl) ⟨585317, by rfl⟩ : syracuseStep 780423 = 1170635) B1170635
theorem B780431 : Blo 778337 780431 := bstep (se 1 (by rfl) ⟨585323, by rfl⟩ : syracuseStep 780431 = 1170647) B1170647
theorem B780475 : Blo 778337 780475 := bstep (se 1 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 780475 = 1170713) B1170713
theorem B780551 : Blo 778337 780551 := bstep (se 1 (by rfl) ⟨585413, by rfl⟩ : syracuseStep 780551 = 1170827) B1170827
theorem B780559 : Blo 778337 780559 := bstep (se 1 (by rfl) ⟨585419, by rfl⟩ : syracuseStep 780559 = 1170839) B1170839
theorem B878863 : Blo 778337 878863 := bstep (se 1 (by rfl) ⟨659147, by rfl⟩ : syracuseStep 878863 = 1318295) B1318295
theorem B780603 : Blo 778337 780603 := bstep (se 1 (by rfl) ⟨585452, by rfl⟩ : syracuseStep 780603 = 1170905) B1170905
theorem B2222471 : Blo 778337 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B780679 : Blo 778337 780679 := bstep (se 1 (by rfl) ⟨585509, by rfl⟩ : syracuseStep 780679 = 1171019) B1171019
theorem B780687 : Blo 778337 780687 := bstep (se 1 (by rfl) ⟨585515, by rfl⟩ : syracuseStep 780687 = 1171031) B1171031
theorem B780731 : Blo 778337 780731 := bstep (se 1 (by rfl) ⟨585548, by rfl⟩ : syracuseStep 780731 = 1171097) B1171097
theorem B8415697 : Blo 778337 8415697 := bstep (se 2 (by rfl) ⟨3155886, by rfl⟩ : syracuseStep 8415697 = 6311773) B6311773
theorem B5630417 : Blo 778337 5630417 := bstep (se 2 (by rfl) ⟨2111406, by rfl⟩ : syracuseStep 5630417 = 4222813) B4222813
theorem B780807 : Blo 778337 780807 := bstep (se 1 (by rfl) ⟨585605, by rfl⟩ : syracuseStep 780807 = 1171211) B1171211
theorem B780815 : Blo 778337 780815 := bstep (se 1 (by rfl) ⟨585611, by rfl⟩ : syracuseStep 780815 = 1171223) B1171223
theorem B12839467 : Blo 778337 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B780859 : Blo 778337 780859 := bstep (se 1 (by rfl) ⟨585644, by rfl⟩ : syracuseStep 780859 = 1171289) B1171289
theorem B2222653 : Blo 778337 2222653 := bstep (se 3 (by rfl) ⟨416747, by rfl⟩ : syracuseStep 2222653 = 833495) B833495
theorem B2222711 : Blo 778337 2222711 := bstep (se 1 (by rfl) ⟨1667033, by rfl⟩ : syracuseStep 2222711 = 3334067) B3334067
theorem B780935 : Blo 778337 780935 := bstep (se 1 (by rfl) ⟨585701, by rfl⟩ : syracuseStep 780935 = 1171403) B1171403
theorem B780943 : Blo 778337 780943 := bstep (se 1 (by rfl) ⟨585707, by rfl⟩ : syracuseStep 780943 = 1171415) B1171415
theorem B1108667 : Blo 778337 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B780987 : Blo 778337 780987 := bstep (se 1 (by rfl) ⟨585740, by rfl⟩ : syracuseStep 780987 = 1171481) B1171481
theorem B781063 : Blo 778337 781063 := bstep (se 1 (by rfl) ⟨585797, by rfl⟩ : syracuseStep 781063 = 1171595) B1171595
theorem B879367 : Blo 778337 879367 := bstep (se 1 (by rfl) ⟨659525, by rfl⟩ : syracuseStep 879367 = 1319051) B1319051
theorem B781071 : Blo 778337 781071 := bstep (se 1 (by rfl) ⟨585803, by rfl⟩ : syracuseStep 781071 = 1171607) B1171607
theorem B3959603 : Blo 778337 3959603 := bstep (se 1 (by rfl) ⟨2969702, by rfl⟩ : syracuseStep 3959603 = 5939405) B5939405
theorem B781115 : Blo 778337 781115 := bstep (se 1 (by rfl) ⟨585836, by rfl⟩ : syracuseStep 781115 = 1171673) B1171673
theorem B781191 : Blo 778337 781191 := bstep (se 1 (by rfl) ⟨585893, by rfl⟩ : syracuseStep 781191 = 1171787) B1171787
theorem B781199 : Blo 778337 781199 := bstep (se 1 (by rfl) ⟨585899, by rfl⟩ : syracuseStep 781199 = 1171799) B1171799
theorem B781243 : Blo 778337 781243 := bstep (se 1 (by rfl) ⟨585932, by rfl⟩ : syracuseStep 781243 = 1171865) B1171865
theorem B879547 : Blo 778337 879547 := bstep (se 1 (by rfl) ⟨659660, by rfl⟩ : syracuseStep 879547 = 1319321) B1319321
theorem B1403849 : Blo 778337 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B781319 : Blo 778337 781319 := bstep (se 1 (by rfl) ⟨585989, by rfl⟩ : syracuseStep 781319 = 1171979) B1171979
theorem B781327 : Blo 778337 781327 := bstep (se 1 (by rfl) ⟨585995, by rfl⟩ : syracuseStep 781327 = 1171991) B1171991
theorem B781371 : Blo 778337 781371 := bstep (se 1 (by rfl) ⟨586028, by rfl⟩ : syracuseStep 781371 = 1172057) B1172057
theorem B3959927 : Blo 778337 3959927 := bstep (se 1 (by rfl) ⟨2969945, by rfl⟩ : syracuseStep 3959927 = 5939891) B5939891
theorem B781447 : Blo 778337 781447 := bstep (se 1 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 781447 = 1172171) B1172171
theorem B781455 : Blo 778337 781455 := bstep (se 1 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 781455 = 1172183) B1172183
theorem B781499 : Blo 778337 781499 := bstep (se 1 (by rfl) ⟨586124, by rfl⟩ : syracuseStep 781499 = 1172249) B1172249
theorem B781575 : Blo 778337 781575 := bstep (se 1 (by rfl) ⟨586181, by rfl⟩ : syracuseStep 781575 = 1172363) B1172363
theorem B781583 : Blo 778337 781583 := bstep (se 1 (by rfl) ⟨586187, by rfl⟩ : syracuseStep 781583 = 1172375) B1172375
theorem B1109305 : Blo 778337 1109305 := bstep (se 2 (by rfl) ⟨415989, by rfl⟩ : syracuseStep 1109305 = 831979) B831979
theorem B781627 : Blo 778337 781627 := bstep (se 1 (by rfl) ⟨586220, by rfl⟩ : syracuseStep 781627 = 1172441) B1172441
theorem B781703 : Blo 778337 781703 := bstep (se 1 (by rfl) ⟨586277, by rfl⟩ : syracuseStep 781703 = 1172555) B1172555
theorem B781711 : Blo 778337 781711 := bstep (se 1 (by rfl) ⟨586283, by rfl⟩ : syracuseStep 781711 = 1172567) B1172567
theorem B880015 : Blo 778337 880015 := bstep (se 1 (by rfl) ⟨660011, by rfl⟩ : syracuseStep 880015 = 1320023) B1320023
theorem B781755 : Blo 778337 781755 := bstep (se 1 (by rfl) ⟨586316, by rfl⟩ : syracuseStep 781755 = 1172633) B1172633
theorem B2813393 : Blo 778337 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B781831 : Blo 778337 781831 := bstep (se 1 (by rfl) ⟨586373, by rfl⟩ : syracuseStep 781831 = 1172747) B1172747
theorem B781839 : Blo 778337 781839 := bstep (se 1 (by rfl) ⟨586379, by rfl⟩ : syracuseStep 781839 = 1172759) B1172759
theorem B3337757 : Blo 778337 3337757 := bstep (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) B1251659
theorem B5565995 : Blo 778337 5565995 := bstep (se 1 (by rfl) ⟨4174496, by rfl⟩ : syracuseStep 5565995 = 8348993) B8348993
theorem B781883 : Blo 778337 781883 := bstep (se 1 (by rfl) ⟨586412, by rfl⟩ : syracuseStep 781883 = 1172825) B1172825
theorem B16019045 : Blo 778337 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B781959 : Blo 778337 781959 := bstep (se 1 (by rfl) ⟨586469, by rfl⟩ : syracuseStep 781959 = 1172939) B1172939
theorem B781967 : Blo 778337 781967 := bstep (se 1 (by rfl) ⟨586475, by rfl⟩ : syracuseStep 781967 = 1172951) B1172951
theorem B2223769 : Blo 778337 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B782011 : Blo 778337 782011 := bstep (se 1 (by rfl) ⟨586508, by rfl⟩ : syracuseStep 782011 = 1173017) B1173017
theorem B782087 : Blo 778337 782087 := bstep (se 1 (by rfl) ⟨586565, by rfl⟩ : syracuseStep 782087 = 1173131) B1173131
theorem B782095 : Blo 778337 782095 := bstep (se 1 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 782095 = 1173143) B1173143
theorem B1404715 : Blo 778337 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B782139 : Blo 778337 782139 := bstep (se 1 (by rfl) ⟨586604, by rfl⟩ : syracuseStep 782139 = 1173209) B1173209
theorem B4452185 : Blo 778337 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B782215 : Blo 778337 782215 := bstep (se 1 (by rfl) ⟨586661, by rfl⟩ : syracuseStep 782215 = 1173323) B1173323
theorem B782223 : Blo 778337 782223 := bstep (se 1 (by rfl) ⟨586667, by rfl⟩ : syracuseStep 782223 = 1173335) B1173335
theorem B782267 : Blo 778337 782267 := bstep (se 1 (by rfl) ⟨586700, by rfl⟩ : syracuseStep 782267 = 1173401) B1173401
theorem B3338441 : Blo 778337 3338441 := bstep (se 2 (by rfl) ⟨1251915, by rfl⟩ : syracuseStep 3338441 = 2503831) B2503831
theorem B2224385 : Blo 778337 2224385 := bstep (se 2 (by rfl) ⟨834144, by rfl⟩ : syracuseStep 2224385 = 1668289) B1668289
theorem B4452641 : Blo 778337 4452641 := bstep (se 2 (by rfl) ⟨1669740, by rfl⟩ : syracuseStep 4452641 = 3339481) B3339481
theorem B4452893 : Blo 778337 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B1667785 : Blo 778337 1667785 := bstep (se 2 (by rfl) ⟨625419, by rfl⟩ : syracuseStep 1667785 = 1250839) B1250839
theorem B1110791 : Blo 778337 1110791 := bstep (se 1 (by rfl) ⟨833093, by rfl⟩ : syracuseStep 1110791 = 1666187) B1666187
theorem B1340345 : Blo 778337 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B1111099 : Blo 778337 1111099 := bstep (se 1 (by rfl) ⟨833324, by rfl⟩ : syracuseStep 1111099 = 1666649) B1666649
theorem B1406099 : Blo 778337 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B2225353 : Blo 778337 2225353 := bstep (se 2 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 2225353 = 1669015) B1669015
theorem B16840037 : Blo 778337 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B8877761 : Blo 778337 8877761 := bstep (se 2 (by rfl) ⟨3329160, by rfl⟩ : syracuseStep 8877761 = 6658321) B6658321
theorem B6649573 : Blo 778337 6649573 := bstep (se 4 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 6649573 = 1246795) B1246795
theorem B1406855 : Blo 778337 1406855 := bstep (se 1 (by rfl) ⟨1055141, by rfl⟩ : syracuseStep 1406855 = 2110283) B2110283
theorem B3340217 : Blo 778337 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B1112249 : Blo 778337 1112249 := bstep (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) B834187
theorem B1407547 : Blo 778337 1407547 := bstep (se 1 (by rfl) ⟨1055660, by rfl⟩ : syracuseStep 1407547 = 2111321) B2111321
theorem B2226959 : Blo 778337 2226959 := bstep (se 1 (by rfl) ⟨1670219, by rfl⟩ : syracuseStep 2226959 = 3340439) B3340439
theorem B4455283 : Blo 778337 4455283 := bstep (se 1 (by rfl) ⟨3341462, by rfl⟩ : syracuseStep 4455283 = 6682925) B6682925
theorem B4226363 : Blo 778337 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B1670519 : Blo 778337 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B1113787 : Blo 778337 1113787 := bstep (se 1 (by rfl) ⟨835340, by rfl⟩ : syracuseStep 1113787 = 1670681) B1670681
theorem B45547541 : Blo 778337 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B1606049 : Blo 778337 1606049 := bstep (se 2 (by rfl) ⟨602268, by rfl⟩ : syracuseStep 1606049 = 1204537) B1204537
theorem B21398579 : Blo 778337 21398579 := bstep (se 1 (by rfl) ⟨16048934, by rfl⟩ : syracuseStep 21398579 = 32097869) B32097869
theorem B14451929 : Blo 778337 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B9995683 : Blo 778337 9995683 := bstep (se 1 (by rfl) ⟨7496762, by rfl⟩ : syracuseStep 9995683 = 14993525) B14993525
theorem B5637539 : Blo 778337 5637539 := bstep (se 1 (by rfl) ⟨4228154, by rfl⟩ : syracuseStep 5637539 = 8456309) B8456309
theorem B3376939 : Blo 778337 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B13502771 : Blo 778337 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B3574253 : Blo 778337 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B16026917 : Blo 778337 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B1314191 : Blo 778337 1314191 := bstep (se 1 (by rfl) ⟨985643, by rfl⟩ : syracuseStep 1314191 = 1971287) B1971287
theorem B1478063 : Blo 778337 1478063 := bstep (se 1 (by rfl) ⟨1108547, by rfl⟩ : syracuseStep 1478063 = 2217095) B2217095
theorem B1314427 : Blo 778337 1314427 := bstep (se 1 (by rfl) ⟨985820, by rfl⟩ : syracuseStep 1314427 = 1971641) B1971641
theorem B2494091 : Blo 778337 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B1871723 : Blo 778337 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B1249199 : Blo 778337 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B1478587 : Blo 778337 1478587 := bstep (se 1 (by rfl) ⟨1108940, by rfl⟩ : syracuseStep 1478587 = 2217881) B2217881
theorem B6655931 : Blo 778337 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B1970183 : Blo 778337 1970183 := bstep (se 1 (by rfl) ⟨1477637, by rfl⟩ : syracuseStep 1970183 = 2955275) B2955275
theorem B790651 : Blo 778337 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B790703 : Blo 778337 790703 := bstep (se 1 (by rfl) ⟨593027, by rfl⟩ : syracuseStep 790703 = 1186055) B1186055
theorem B1249609 : Blo 778337 1249609 := bstep (se 2 (by rfl) ⟨468603, by rfl⟩ : syracuseStep 1249609 = 937207) B937207
theorem B1479073 : Blo 778337 1479073 := bstep (se 2 (by rfl) ⟨554652, by rfl⟩ : syracuseStep 1479073 = 1109305) B1109305
theorem B1315291 : Blo 778337 1315291 := bstep (se 1 (by rfl) ⟨986468, by rfl⟩ : syracuseStep 1315291 = 1972937) B1972937
theorem B21303773 : Blo 778337 21303773 := bstep (se 3 (by rfl) ⟨3994457, by rfl⟩ : syracuseStep 21303773 = 7988915) B7988915
theorem B1872953 : Blo 778337 1872953 := bstep (se 2 (by rfl) ⟨702357, by rfl⟩ : syracuseStep 1872953 = 1404715) B1404715
theorem B1315919 : Blo 778337 1315919 := bstep (se 1 (by rfl) ⟨986939, by rfl⟩ : syracuseStep 1315919 = 1973879) B1973879
theorem B9508043 : Blo 778337 9508043 := bstep (se 1 (by rfl) ⟨7131032, by rfl⟩ : syracuseStep 9508043 = 14262065) B14262065
theorem B2495873 : Blo 778337 2495873 := bstep (se 2 (by rfl) ⟨935952, by rfl⟩ : syracuseStep 2495873 = 1871905) B1871905
theorem B2627207 : Blo 778337 2627207 := bstep (se 1 (by rfl) ⟨1970405, by rfl⟩ : syracuseStep 2627207 = 3940811) B3940811
theorem B2627261 : Blo 778337 2627261 := bstep (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) B985223
theorem B2004679 : Blo 778337 2004679 := bstep (se 1 (by rfl) ⟨1503509, by rfl⟩ : syracuseStep 2004679 = 3007019) B3007019
theorem B1578707 : Blo 778337 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B2627423 : Blo 778337 2627423 := bstep (se 1 (by rfl) ⟨1970567, by rfl⟩ : syracuseStep 2627423 = 3941135) B3941135
theorem B1316783 : Blo 778337 1316783 := bstep (se 1 (by rfl) ⟨987587, by rfl⟩ : syracuseStep 1316783 = 1975175) B1975175
theorem B989111 : Blo 778337 989111 := bstep (se 1 (by rfl) ⟨741833, by rfl⟩ : syracuseStep 989111 = 1483667) B1483667
theorem B5707705 : Blo 778337 5707705 := bstep (se 2 (by rfl) ⟨2140389, by rfl⟩ : syracuseStep 5707705 = 4280779) B4280779
theorem B2627585 : Blo 778337 2627585 := bstep (se 2 (by rfl) ⟨985344, by rfl⟩ : syracuseStep 2627585 = 1970689) B1970689
theorem B1349639 : Blo 778337 1349639 := bstep (se 1 (by rfl) ⟨1012229, by rfl⟩ : syracuseStep 1349639 = 2024459) B2024459
theorem B989263 : Blo 778337 989263 := bstep (se 1 (by rfl) ⟨741947, by rfl⟩ : syracuseStep 989263 = 1483895) B1483895
theorem B1972471 : Blo 778337 1972471 := bstep (se 1 (by rfl) ⟨1479353, by rfl⟩ : syracuseStep 1972471 = 2958707) B2958707
theorem B1317215 : Blo 778337 1317215 := bstep (se 1 (by rfl) ⟨987911, by rfl⟩ : syracuseStep 1317215 = 1975823) B1975823
theorem B1972745 : Blo 778337 1972745 := bstep (se 2 (by rfl) ⟨739779, by rfl⟩ : syracuseStep 1972745 = 1479559) B1479559
theorem B1972775 : Blo 778337 1972775 := bstep (se 1 (by rfl) ⟨1479581, by rfl⟩ : syracuseStep 1972775 = 2959163) B2959163
theorem B1481465 : Blo 778337 1481465 := bstep (se 2 (by rfl) ⟨555549, by rfl⟩ : syracuseStep 1481465 = 1111099) B1111099
theorem B2628395 : Blo 778337 2628395 := bstep (se 1 (by rfl) ⟨1971296, by rfl⟩ : syracuseStep 2628395 = 3942593) B3942593
theorem B1973099 : Blo 778337 1973099 := bstep (se 1 (by rfl) ⟨1479824, by rfl⟩ : syracuseStep 1973099 = 2959649) B2959649
theorem B1317775 : Blo 778337 1317775 := bstep (se 1 (by rfl) ⟨988331, by rfl⟩ : syracuseStep 1317775 = 1976663) B1976663
theorem B1481647 : Blo 778337 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B370580453 : Blo 778337 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B1776647 : Blo 778337 1776647 := bstep (se 1 (by rfl) ⟨1332485, by rfl⟩ : syracuseStep 1776647 = 2664971) B2664971
theorem B2628665 : Blo 778337 2628665 := bstep (se 2 (by rfl) ⟨985749, by rfl⟩ : syracuseStep 2628665 = 1971499) B1971499
theorem B1481807 : Blo 778337 1481807 := bstep (se 1 (by rfl) ⟨1111355, by rfl⟩ : syracuseStep 1481807 = 2222711) B2222711
theorem B2956445 : Blo 778337 2956445 := bstep (se 3 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 2956445 = 1108667) B1108667
theorem B2956459 : Blo 778337 2956459 := bstep (se 1 (by rfl) ⟨2217344, by rfl⟩ : syracuseStep 2956459 = 4434689) B4434689
theorem B1252601 : Blo 778337 1252601 := bstep (se 2 (by rfl) ⟨469725, by rfl⟩ : syracuseStep 1252601 = 939451) B939451
theorem B1252703 : Blo 778337 1252703 := bstep (se 1 (by rfl) ⟨939527, by rfl⟩ : syracuseStep 1252703 = 1879055) B1879055
theorem B2628989 : Blo 778337 2628989 := bstep (se 3 (by rfl) ⟨492935, by rfl⟩ : syracuseStep 2628989 = 985871) B985871
theorem B2956763 : Blo 778337 2956763 := bstep (se 1 (by rfl) ⟨2217572, by rfl⟩ : syracuseStep 2956763 = 4435145) B4435145
theorem B1973747 : Blo 778337 1973747 := bstep (se 1 (by rfl) ⟨1480310, by rfl⟩ : syracuseStep 1973747 = 2960621) B2960621
theorem B1318457 : Blo 778337 1318457 := bstep (se 2 (by rfl) ⟨494421, by rfl⟩ : syracuseStep 1318457 = 988843) B988843
theorem B1252921 : Blo 778337 1252921 := bstep (se 2 (by rfl) ⟨469845, by rfl⟩ : syracuseStep 1252921 = 939691) B939691
theorem B10821185 : Blo 778337 10821185 := bstep (se 2 (by rfl) ⟨4057944, by rfl⟩ : syracuseStep 10821185 = 8115889) B8115889
theorem B2629259 : Blo 778337 2629259 := bstep (se 1 (by rfl) ⟨1971944, by rfl⟩ : syracuseStep 2629259 = 3943889) B3943889
theorem B3710663 : Blo 778337 3710663 := bstep (se 1 (by rfl) ⟨2782997, by rfl⟩ : syracuseStep 3710663 = 5565995) B5565995
theorem B3743597 : Blo 778337 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B1974203 : Blo 778337 1974203 := bstep (se 1 (by rfl) ⟨1480652, by rfl⟩ : syracuseStep 1974203 = 2961305) B2961305
theorem B46768141 : Blo 778337 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B1482923 : Blo 778337 1482923 := bstep (se 1 (by rfl) ⟨1112192, by rfl⟩ : syracuseStep 1482923 = 2224385) B2224385
theorem B1319159 : Blo 778337 1319159 := bstep (se 1 (by rfl) ⟨989369, by rfl⟩ : syracuseStep 1319159 = 1978739) B1978739
theorem B2630177 : Blo 778337 2630177 := bstep (se 2 (by rfl) ⟨986316, by rfl⟩ : syracuseStep 2630177 = 1972633) B1972633
theorem B1319503 : Blo 778337 1319503 := bstep (se 1 (by rfl) ⟨989627, by rfl⟩ : syracuseStep 1319503 = 1979255) B1979255
theorem B1974881 : Blo 778337 1974881 := bstep (se 2 (by rfl) ⟨740580, by rfl⟩ : syracuseStep 1974881 = 1481161) B1481161
theorem B2630393 : Blo 778337 2630393 := bstep (se 2 (by rfl) ⟨986397, by rfl⟩ : syracuseStep 2630393 = 1972795) B1972795
theorem B1876729 : Blo 778337 1876729 := bstep (se 2 (by rfl) ⟨703773, by rfl⟩ : syracuseStep 1876729 = 1407547) B1407547
theorem B1319753 : Blo 778337 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B48636875 : Blo 778337 48636875 := bstep (se 1 (by rfl) ⟨36477656, by rfl⟩ : syracuseStep 48636875 = 72955313) B72955313
theorem B2630663 : Blo 778337 2630663 := bstep (se 1 (by rfl) ⟨1972997, by rfl⟩ : syracuseStep 2630663 = 3945995) B3945995
theorem B2630771 : Blo 778337 2630771 := bstep (se 1 (by rfl) ⟨1973078, by rfl⟩ : syracuseStep 2630771 = 3946157) B3946157
theorem B5940377 : Blo 778337 5940377 := bstep (se 2 (by rfl) ⟨2227641, by rfl⟩ : syracuseStep 5940377 = 4455283) B4455283
theorem B1582291 : Blo 778337 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B1320185 : Blo 778337 1320185 := bstep (se 2 (by rfl) ⟨495069, by rfl⟩ : syracuseStep 1320185 = 990139) B990139
theorem B2631041 : Blo 778337 2631041 := bstep (se 2 (by rfl) ⟨986640, by rfl⟩ : syracuseStep 2631041 = 1973281) B1973281
theorem B1484639 : Blo 778337 1484639 := bstep (se 1 (by rfl) ⟨1113479, by rfl⟩ : syracuseStep 1484639 = 2226959) B2226959
theorem B2959361 : Blo 778337 2959361 := bstep (se 2 (by rfl) ⟨1109760, by rfl⟩ : syracuseStep 2959361 = 2219521) B2219521
theorem B2959375 : Blo 778337 2959375 := bstep (se 1 (by rfl) ⟨2219531, by rfl⟩ : syracuseStep 2959375 = 4439063) B4439063
theorem B1976339 : Blo 778337 1976339 := bstep (se 1 (by rfl) ⟨1482254, by rfl⟩ : syracuseStep 1976339 = 2964509) B2964509
theorem B2631851 : Blo 778337 2631851 := bstep (se 1 (by rfl) ⟨1973888, by rfl⟩ : syracuseStep 2631851 = 3947777) B3947777
theorem B1485049 : Blo 778337 1485049 := bstep (se 2 (by rfl) ⟨556893, by rfl⟩ : syracuseStep 1485049 = 1113787) B1113787
theorem B13314455 : Blo 778337 13314455 := bstep (se 1 (by rfl) ⟨9985841, by rfl⟩ : syracuseStep 13314455 = 19971683) B19971683
theorem B1976795 : Blo 778337 1976795 := bstep (se 1 (by rfl) ⟨1482596, by rfl⟩ : syracuseStep 1976795 = 2965193) B2965193
theorem B2632391 : Blo 778337 2632391 := bstep (se 1 (by rfl) ⟨1974293, by rfl⟩ : syracuseStep 2632391 = 3948587) B3948587
theorem B1780423 : Blo 778337 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B3943241 : Blo 778337 3943241 := bstep (se 2 (by rfl) ⟨1478715, by rfl⟩ : syracuseStep 3943241 = 2957431) B2957431
theorem B4434871 : Blo 778337 4434871 := bstep (se 1 (by rfl) ⟨3326153, by rfl⟩ : syracuseStep 4434871 = 6652307) B6652307
theorem B21605303 : Blo 778337 21605303 := bstep (se 1 (by rfl) ⟨16203977, by rfl⟩ : syracuseStep 21605303 = 32407955) B32407955
theorem B1780663 : Blo 778337 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B2108423 : Blo 778337 2108423 := bstep (se 1 (by rfl) ⟨1581317, by rfl⟩ : syracuseStep 2108423 = 3162635) B3162635
theorem B6008003 : Blo 778337 6008003 := bstep (se 1 (by rfl) ⟨4506002, by rfl⟩ : syracuseStep 6008003 = 9012005) B9012005
theorem B2108663 : Blo 778337 2108663 := bstep (se 1 (by rfl) ⟨1581497, by rfl⟩ : syracuseStep 2108663 = 3162995) B3162995
theorem B2960651 : Blo 778337 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B5615021 : Blo 778337 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B2633255 : Blo 778337 2633255 := bstep (se 1 (by rfl) ⟨1974941, by rfl⟩ : syracuseStep 2633255 = 3949883) B3949883
theorem B5615191 : Blo 778337 5615191 := bstep (se 1 (by rfl) ⟨4211393, by rfl⟩ : syracuseStep 5615191 = 8422787) B8422787
theorem B1977979 : Blo 778337 1977979 := bstep (se 1 (by rfl) ⟨1483484, by rfl⟩ : syracuseStep 1977979 = 2966969) B2966969
theorem B2633363 : Blo 778337 2633363 := bstep (se 1 (by rfl) ⟨1975022, by rfl⟩ : syracuseStep 2633363 = 3950045) B3950045
theorem B2961107 : Blo 778337 2961107 := bstep (se 1 (by rfl) ⟨2220830, by rfl⟩ : syracuseStep 2961107 = 4441661) B4441661
theorem B32059097 : Blo 778337 32059097 := bstep (se 2 (by rfl) ⟨12022161, by rfl⟩ : syracuseStep 32059097 = 24044323) B24044323
theorem B2633579 : Blo 778337 2633579 := bstep (se 1 (by rfl) ⟨1975184, by rfl⟩ : syracuseStep 2633579 = 3950369) B3950369
theorem B2633633 : Blo 778337 2633633 := bstep (se 2 (by rfl) ⟨987612, by rfl⟩ : syracuseStep 2633633 = 1975225) B1975225
theorem B3944537 : Blo 778337 3944537 := bstep (se 2 (by rfl) ⟨1479201, by rfl⟩ : syracuseStep 3944537 = 2958403) B2958403
theorem B4436329 : Blo 778337 4436329 := bstep (se 2 (by rfl) ⟨1663623, by rfl⟩ : syracuseStep 4436329 = 3327247) B3327247
theorem B2634227 : Blo 778337 2634227 := bstep (se 1 (by rfl) ⟨1975670, by rfl⟩ : syracuseStep 2634227 = 3951341) B3951341
theorem B2962109 : Blo 778337 2962109 := bstep (se 3 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 2962109 = 1110791) B1110791
theorem B2634767 : Blo 778337 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B5715011 : Blo 778337 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B2503997 : Blo 778337 2503997 := bstep (se 3 (by rfl) ⟨469499, by rfl⟩ : syracuseStep 2503997 = 938999) B938999
theorem B2635361 : Blo 778337 2635361 := bstep (se 2 (by rfl) ⟨988260, by rfl⟩ : syracuseStep 2635361 = 1976521) B1976521
theorem B3749597 : Blo 778337 3749597 := bstep (se 3 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 3749597 = 1406099) B1406099
theorem B6338371 : Blo 778337 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B3159881 : Blo 778337 3159881 := bstep (se 2 (by rfl) ⟨1184955, by rfl⟩ : syracuseStep 3159881 = 2369911) B2369911
theorem B11220929 : Blo 778337 11220929 := bstep (se 2 (by rfl) ⟨4207848, by rfl⟩ : syracuseStep 11220929 = 8415697) B8415697
theorem B17119289 : Blo 778337 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B2963537 : Blo 778337 2963537 := bstep (se 2 (by rfl) ⟨1111326, by rfl⟩ : syracuseStep 2963537 = 2222653) B2222653
theorem B4995229 : Blo 778337 4995229 := bstep (se 3 (by rfl) ⟨936605, by rfl⟩ : syracuseStep 4995229 = 1873211) B1873211
theorem B1522027 : Blo 778337 1522027 := bstep (se 1 (by rfl) ⟨1141520, by rfl⟩ : syracuseStep 1522027 = 2283041) B2283041
theorem B1751561 : Blo 778337 1751561 := bstep (se 2 (by rfl) ⟨656835, by rfl⟩ : syracuseStep 1751561 = 1313671) B1313671
theorem B427571725 : Blo 778337 427571725 := bstep (se 3 (by rfl) ⟨80169698, by rfl⟩ : syracuseStep 427571725 = 160339397) B160339397
theorem B834247 : Blo 778337 834247 := bstep (se 1 (by rfl) ⟨625685, by rfl⟩ : syracuseStep 834247 = 1251371) B1251371
theorem B2505431 : Blo 778337 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B1751903 : Blo 778337 1751903 := bstep (se 1 (by rfl) ⟨1313927, by rfl⟩ : syracuseStep 1751903 = 2627855) B2627855
theorem B1752083 : Blo 778337 1752083 := bstep (se 1 (by rfl) ⟨1314062, by rfl⟩ : syracuseStep 1752083 = 2628125) B2628125
theorem B2636819 : Blo 778337 2636819 := bstep (se 1 (by rfl) ⟨1977614, by rfl⟩ : syracuseStep 2636819 = 3955229) B3955229
theorem B6667343 : Blo 778337 6667343 := bstep (se 1 (by rfl) ⟨5000507, by rfl⟩ : syracuseStep 6667343 = 10001015) B10001015
theorem B2505995 : Blo 778337 2505995 := bstep (se 1 (by rfl) ⟨1879496, by rfl⟩ : syracuseStep 2505995 = 3758993) B3758993
theorem B2637143 : Blo 778337 2637143 := bstep (se 1 (by rfl) ⟨1977857, by rfl⟩ : syracuseStep 2637143 = 3955715) B3955715
theorem B1752425 : Blo 778337 1752425 := bstep (se 2 (by rfl) ⟨657159, by rfl⟩ : syracuseStep 1752425 = 1314319) B1314319
theorem B2965025 : Blo 778337 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B835195 : Blo 778337 835195 := bstep (se 1 (by rfl) ⟨626396, by rfl⟩ : syracuseStep 835195 = 1252793) B1252793
theorem B4734611 : Blo 778337 4734611 := bstep (se 1 (by rfl) ⟨3550958, by rfl⟩ : syracuseStep 4734611 = 7101917) B7101917
theorem B2965207 : Blo 778337 2965207 := bstep (se 1 (by rfl) ⟨2223905, by rfl⟩ : syracuseStep 2965207 = 4447811) B4447811
theorem B10141625 : Blo 778337 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B1753019 : Blo 778337 1753019 := bstep (se 1 (by rfl) ⟨1314764, by rfl⟩ : syracuseStep 1753019 = 2629529) B2629529
theorem B2965511 : Blo 778337 2965511 := bstep (se 1 (by rfl) ⟨2224133, by rfl⟩ : syracuseStep 2965511 = 4448267) B4448267
theorem B1753145 : Blo 778337 1753145 := bstep (se 2 (by rfl) ⟨657429, by rfl⟩ : syracuseStep 1753145 = 1314859) B1314859
theorem B8437841 : Blo 778337 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B1753487 : Blo 778337 1753487 := bstep (se 1 (by rfl) ⟨1315115, by rfl⟩ : syracuseStep 1753487 = 2630231) B2630231
theorem B2638223 : Blo 778337 2638223 := bstep (se 1 (by rfl) ⟨1978667, by rfl⟩ : syracuseStep 2638223 = 3957335) B3957335
theorem B2965997 : Blo 778337 2965997 := bstep (se 3 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 2965997 = 1112249) B1112249
theorem B3293729 : Blo 778337 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B1753811 : Blo 778337 1753811 := bstep (se 1 (by rfl) ⟨1315358, by rfl⟩ : syracuseStep 1753811 = 2630717) B2630717
theorem B2638547 : Blo 778337 2638547 := bstep (se 1 (by rfl) ⟨1978910, by rfl⟩ : syracuseStep 2638547 = 3957821) B3957821
theorem B3949721 : Blo 778337 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B5916077 : Blo 778337 5916077 := bstep (se 3 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 5916077 = 2218529) B2218529
theorem B2967137 : Blo 778337 2967137 := bstep (se 2 (by rfl) ⟨1112676, by rfl⟩ : syracuseStep 2967137 = 2225353) B2225353
theorem B1754747 : Blo 778337 1754747 := bstep (se 1 (by rfl) ⟨1316060, by rfl⟩ : syracuseStep 1754747 = 2632121) B2632121
theorem B3753611 : Blo 778337 3753611 := bstep (se 1 (by rfl) ⟨2815208, by rfl⟩ : syracuseStep 3753611 = 5630417) B5630417
theorem B1754873 : Blo 778337 1754873 := bstep (se 2 (by rfl) ⟨658077, by rfl⟩ : syracuseStep 1754873 = 1316155) B1316155
theorem B2639735 : Blo 778337 2639735 := bstep (se 1 (by rfl) ⟨1979801, by rfl⟩ : syracuseStep 2639735 = 3959603) B3959603
theorem B1755143 : Blo 778337 1755143 := bstep (se 1 (by rfl) ⟨1316357, by rfl⟩ : syracuseStep 1755143 = 2632715) B2632715
theorem B1755215 : Blo 778337 1755215 := bstep (se 1 (by rfl) ⟨1316411, by rfl⟩ : syracuseStep 1755215 = 2632823) B2632823
theorem B2639951 : Blo 778337 2639951 := bstep (se 1 (by rfl) ⟨1979963, by rfl⟩ : syracuseStep 2639951 = 3959927) B3959927
theorem B12667013 : Blo 778337 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B8866097 : Blo 778337 8866097 := bstep (se 2 (by rfl) ⟨3324786, by rfl⟩ : syracuseStep 8866097 = 6649573) B6649573
theorem B2640329 : Blo 778337 2640329 := bstep (se 2 (by rfl) ⟨990123, by rfl⟩ : syracuseStep 2640329 = 1980247) B1980247
theorem B1755611 : Blo 778337 1755611 := bstep (se 1 (by rfl) ⟨1316708, by rfl⟩ : syracuseStep 1755611 = 2633417) B2633417
theorem B2968123 : Blo 778337 2968123 := bstep (se 1 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 2968123 = 4452185) B4452185
theorem B2968427 : Blo 778337 2968427 := bstep (se 1 (by rfl) ⟨2226320, by rfl⟩ : syracuseStep 2968427 = 4452641) B4452641
theorem B1756079 : Blo 778337 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B2968595 : Blo 778337 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B1756331 : Blo 778337 1756331 := bstep (se 1 (by rfl) ⟨1317248, by rfl⟩ : syracuseStep 1756331 = 2634497) B2634497
theorem B13716773 : Blo 778337 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B11226691 : Blo 778337 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B1756871 : Blo 778337 1756871 := bstep (se 1 (by rfl) ⟨1317653, by rfl⟩ : syracuseStep 1756871 = 2635307) B2635307
theorem B5918507 : Blo 778337 5918507 := bstep (se 1 (by rfl) ⟨4438880, by rfl⟩ : syracuseStep 5918507 = 8877761) B8877761
theorem B937903 : Blo 778337 937903 := bstep (se 1 (by rfl) ⟨703427, by rfl⟩ : syracuseStep 937903 = 1406855) B1406855
theorem B6082675 : Blo 778337 6082675 := bstep (se 1 (by rfl) ⟨4562006, by rfl⟩ : syracuseStep 6082675 = 9124013) B9124013
theorem B5001533 : Blo 778337 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B3330391 : Blo 778337 3330391 := bstep (se 1 (by rfl) ⟨2497793, by rfl⟩ : syracuseStep 3330391 = 4995587) B4995587
theorem B1167791 : Blo 778337 1167791 := bstep (se 1 (by rfl) ⟨875843, by rfl⟩ : syracuseStep 1167791 = 1751687) B1751687
theorem B1167881 : Blo 778337 1167881 := bstep (se 2 (by rfl) ⟨437955, by rfl⟩ : syracuseStep 1167881 = 875911) B875911
theorem B1167911 : Blo 778337 1167911 := bstep (se 1 (by rfl) ⟨875933, by rfl⟩ : syracuseStep 1167911 = 1751867) B1751867
theorem B1757735 : Blo 778337 1757735 := bstep (se 1 (by rfl) ⟨1318301, by rfl⟩ : syracuseStep 1757735 = 2636603) B2636603
theorem B1167995 : Blo 778337 1167995 := bstep (se 1 (by rfl) ⟨875996, by rfl⟩ : syracuseStep 1167995 = 1751993) B1751993
theorem B1168121 : Blo 778337 1168121 := bstep (se 2 (by rfl) ⟨438045, by rfl⟩ : syracuseStep 1168121 = 876091) B876091
theorem B1168223 : Blo 778337 1168223 := bstep (se 1 (by rfl) ⟨876167, by rfl⟩ : syracuseStep 1168223 = 1752335) B1752335
theorem B1168235 : Blo 778337 1168235 := bstep (se 1 (by rfl) ⟨876176, by rfl⟩ : syracuseStep 1168235 = 1752353) B1752353
theorem B1758059 : Blo 778337 1758059 := bstep (se 1 (by rfl) ⟨1318544, by rfl⟩ : syracuseStep 1758059 = 2637089) B2637089
theorem B1758113 : Blo 778337 1758113 := bstep (se 2 (by rfl) ⟨659292, by rfl⟩ : syracuseStep 1758113 = 1318585) B1318585
theorem B2216879 : Blo 778337 2216879 := bstep (se 1 (by rfl) ⟨1662659, by rfl⟩ : syracuseStep 2216879 = 3325319) B3325319
theorem B6673427 : Blo 778337 6673427 := bstep (se 1 (by rfl) ⟨5005070, by rfl⟩ : syracuseStep 6673427 = 10010141) B10010141
theorem B1168463 : Blo 778337 1168463 := bstep (se 1 (by rfl) ⟨876347, by rfl⟩ : syracuseStep 1168463 = 1752695) B1752695
theorem B1168583 : Blo 778337 1168583 := bstep (se 1 (by rfl) ⟨876437, by rfl⟩ : syracuseStep 1168583 = 1752875) B1752875
theorem B1758455 : Blo 778337 1758455 := bstep (se 1 (by rfl) ⟨1318841, by rfl⟩ : syracuseStep 1758455 = 2637683) B2637683
theorem B1168745 : Blo 778337 1168745 := bstep (se 2 (by rfl) ⟨438279, by rfl⟩ : syracuseStep 1168745 = 876559) B876559
theorem B5002661 : Blo 778337 5002661 := bstep (se 4 (by rfl) ⟨468999, by rfl⟩ : syracuseStep 5002661 = 937999) B937999
theorem B1168823 : Blo 778337 1168823 := bstep (se 1 (by rfl) ⟨876617, by rfl⟩ : syracuseStep 1168823 = 1753235) B1753235
theorem B1168859 : Blo 778337 1168859 := bstep (se 1 (by rfl) ⟨876644, by rfl⟩ : syracuseStep 1168859 = 1753289) B1753289
theorem B6313459 : Blo 778337 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B16864949 : Blo 778337 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B6313787 : Blo 778337 6313787 := bstep (se 1 (by rfl) ⟨4735340, by rfl⟩ : syracuseStep 6313787 = 9470681) B9470681
theorem B1759049 : Blo 778337 1759049 := bstep (se 2 (by rfl) ⟨659643, by rfl⟩ : syracuseStep 1759049 = 1319287) B1319287
theorem B1169327 : Blo 778337 1169327 := bstep (se 1 (by rfl) ⟨876995, by rfl⟩ : syracuseStep 1169327 = 1753991) B1753991
theorem B22763467 : Blo 778337 22763467 := bstep (se 1 (by rfl) ⟨17072600, by rfl⟩ : syracuseStep 22763467 = 34145201) B34145201
theorem B1169417 : Blo 778337 1169417 := bstep (se 2 (by rfl) ⟨438531, by rfl⟩ : syracuseStep 1169417 = 877063) B877063
theorem B1169447 : Blo 778337 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B2218063 : Blo 778337 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B1169531 : Blo 778337 1169531 := bstep (se 1 (by rfl) ⟨877148, by rfl⟩ : syracuseStep 1169531 = 1754297) B1754297
theorem B1169657 : Blo 778337 1169657 := bstep (se 2 (by rfl) ⟨438621, by rfl⟩ : syracuseStep 1169657 = 877243) B877243
theorem B1169759 : Blo 778337 1169759 := bstep (se 1 (by rfl) ⟨877319, by rfl⟩ : syracuseStep 1169759 = 1754639) B1754639
theorem B1169771 : Blo 778337 1169771 := bstep (se 1 (by rfl) ⟨877328, by rfl⟩ : syracuseStep 1169771 = 1754657) B1754657
theorem B1169999 : Blo 778337 1169999 := bstep (se 1 (by rfl) ⟨877499, by rfl⟩ : syracuseStep 1169999 = 1754999) B1754999
theorem B1759841 : Blo 778337 1759841 := bstep (se 2 (by rfl) ⟨659940, by rfl⟩ : syracuseStep 1759841 = 1319881) B1319881
theorem B12638855 : Blo 778337 12638855 := bstep (se 1 (by rfl) ⟨9479141, by rfl⟩ : syracuseStep 12638855 = 18958283) B18958283
theorem B1170119 : Blo 778337 1170119 := bstep (se 1 (by rfl) ⟨877589, by rfl⟩ : syracuseStep 1170119 = 1755179) B1755179
theorem B91151119 : Blo 778337 91151119 := bstep (se 1 (by rfl) ⟨68363339, by rfl⟩ : syracuseStep 91151119 = 136726679) B136726679
theorem B2710367 : Blo 778337 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B1170281 : Blo 778337 1170281 := bstep (se 2 (by rfl) ⟨438855, by rfl⟩ : syracuseStep 1170281 = 877711) B877711
theorem B1170359 : Blo 778337 1170359 := bstep (se 1 (by rfl) ⟨877769, by rfl⟩ : syracuseStep 1170359 = 1755539) B1755539
theorem B1760183 : Blo 778337 1760183 := bstep (se 1 (by rfl) ⟨1320137, by rfl⟩ : syracuseStep 1760183 = 2640275) B2640275
theorem B1170395 : Blo 778337 1170395 := bstep (se 1 (by rfl) ⟨877796, by rfl⟩ : syracuseStep 1170395 = 1755593) B1755593
theorem B4742297 : Blo 778337 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B1170863 : Blo 778337 1170863 := bstep (se 1 (by rfl) ⟨878147, by rfl⟩ : syracuseStep 1170863 = 1756295) B1756295
theorem B1170953 : Blo 778337 1170953 := bstep (se 2 (by rfl) ⟨439107, by rfl⟩ : syracuseStep 1170953 = 878215) B878215
theorem B1170983 : Blo 778337 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B2809441 : Blo 778337 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B1171067 : Blo 778337 1171067 := bstep (se 1 (by rfl) ⟨878300, by rfl⟩ : syracuseStep 1171067 = 1756601) B1756601
theorem B6676091 : Blo 778337 6676091 := bstep (se 1 (by rfl) ⟨5007068, by rfl⟩ : syracuseStep 6676091 = 10014137) B10014137
theorem B3956363 : Blo 778337 3956363 := bstep (se 1 (by rfl) ⟨2967272, by rfl⟩ : syracuseStep 3956363 = 5934545) B5934545
theorem B1171193 : Blo 778337 1171193 := bstep (se 2 (by rfl) ⟨439197, by rfl⟩ : syracuseStep 1171193 = 878395) B878395
theorem B4447993 : Blo 778337 4447993 := bstep (se 2 (by rfl) ⟨1667997, by rfl⟩ : syracuseStep 4447993 = 3335995) B3335995
theorem B9002785 : Blo 778337 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B2809673 : Blo 778337 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B1171295 : Blo 778337 1171295 := bstep (se 1 (by rfl) ⟨878471, by rfl⟩ : syracuseStep 1171295 = 1756943) B1756943
theorem B1171307 : Blo 778337 1171307 := bstep (se 1 (by rfl) ⟨878480, by rfl⟩ : syracuseStep 1171307 = 1756961) B1756961
theorem B1269679 : Blo 778337 1269679 := bstep (se 1 (by rfl) ⟨952259, by rfl⟩ : syracuseStep 1269679 = 1904519) B1904519
theorem B1171535 : Blo 778337 1171535 := bstep (se 1 (by rfl) ⟨878651, by rfl⟩ : syracuseStep 1171535 = 1757303) B1757303
theorem B778363 : Blo 778337 778363 := bstep (se 1 (by rfl) ⟨583772, by rfl⟩ : syracuseStep 778363 = 1167545) B1167545
theorem B876667 : Blo 778337 876667 := bstep (se 1 (by rfl) ⟨657500, by rfl⟩ : syracuseStep 876667 = 1315001) B1315001
theorem B778415 : Blo 778337 778415 := bstep (se 1 (by rfl) ⟨583811, by rfl⟩ : syracuseStep 778415 = 1167623) B1167623
theorem B778439 : Blo 778337 778439 := bstep (se 1 (by rfl) ⟨583829, by rfl⟩ : syracuseStep 778439 = 1167659) B1167659
theorem B1171655 : Blo 778337 1171655 := bstep (se 1 (by rfl) ⟨878741, by rfl⟩ : syracuseStep 1171655 = 1757483) B1757483
theorem B778459 : Blo 778337 778459 := bstep (se 1 (by rfl) ⟨583844, by rfl⟩ : syracuseStep 778459 = 1167689) B1167689
theorem B778535 : Blo 778337 778535 := bstep (se 1 (by rfl) ⟨583901, by rfl⟩ : syracuseStep 778535 = 1167803) B1167803
theorem B778575 : Blo 778337 778575 := bstep (se 1 (by rfl) ⟨583931, by rfl⟩ : syracuseStep 778575 = 1167863) B1167863
theorem B4514135 : Blo 778337 4514135 := bstep (se 1 (by rfl) ⟨3385601, by rfl⟩ : syracuseStep 4514135 = 6771203) B6771203
theorem B778591 : Blo 778337 778591 := bstep (se 1 (by rfl) ⟨583943, by rfl⟩ : syracuseStep 778591 = 1167887) B1167887
theorem B1171817 : Blo 778337 1171817 := bstep (se 2 (by rfl) ⟨439431, by rfl⟩ : syracuseStep 1171817 = 878863) B878863
theorem B778619 : Blo 778337 778619 := bstep (se 1 (by rfl) ⟨583964, by rfl⟩ : syracuseStep 778619 = 1167929) B1167929
theorem B778671 : Blo 778337 778671 := bstep (se 1 (by rfl) ⟨584003, by rfl⟩ : syracuseStep 778671 = 1168007) B1168007
theorem B1171895 : Blo 778337 1171895 := bstep (se 1 (by rfl) ⟨878921, by rfl⟩ : syracuseStep 1171895 = 1757843) B1757843
theorem B778695 : Blo 778337 778695 := bstep (se 1 (by rfl) ⟨584021, by rfl⟩ : syracuseStep 778695 = 1168043) B1168043
theorem B778715 : Blo 778337 778715 := bstep (se 1 (by rfl) ⟨584036, by rfl⟩ : syracuseStep 778715 = 1168073) B1168073
theorem B1171931 : Blo 778337 1171931 := bstep (se 1 (by rfl) ⟨878948, by rfl⟩ : syracuseStep 1171931 = 1757897) B1757897
theorem B778791 : Blo 778337 778791 := bstep (se 1 (by rfl) ⟨584093, by rfl⟩ : syracuseStep 778791 = 1168187) B1168187
theorem B15032891 : Blo 778337 15032891 := bstep (se 1 (by rfl) ⟨11274668, by rfl⟩ : syracuseStep 15032891 = 22549337) B22549337
theorem B778831 : Blo 778337 778831 := bstep (se 1 (by rfl) ⟨584123, by rfl⟩ : syracuseStep 778831 = 1168247) B1168247
theorem B877135 : Blo 778337 877135 := bstep (se 1 (by rfl) ⟨657851, by rfl⟩ : syracuseStep 877135 = 1315703) B1315703
theorem B778847 : Blo 778337 778847 := bstep (se 1 (by rfl) ⟨584135, by rfl⟩ : syracuseStep 778847 = 1168271) B1168271
theorem B778875 : Blo 778337 778875 := bstep (se 1 (by rfl) ⟨584156, by rfl⟩ : syracuseStep 778875 = 1168313) B1168313
theorem B778927 : Blo 778337 778927 := bstep (se 1 (by rfl) ⟨584195, by rfl⟩ : syracuseStep 778927 = 1168391) B1168391
theorem B778951 : Blo 778337 778951 := bstep (se 1 (by rfl) ⟨584213, by rfl⟩ : syracuseStep 778951 = 1168427) B1168427
theorem B778971 : Blo 778337 778971 := bstep (se 1 (by rfl) ⟨584228, by rfl⟩ : syracuseStep 778971 = 1168457) B1168457
theorem B779047 : Blo 778337 779047 := bstep (se 1 (by rfl) ⟨584285, by rfl⟩ : syracuseStep 779047 = 1168571) B1168571
theorem B779087 : Blo 778337 779087 := bstep (se 1 (by rfl) ⟨584315, by rfl⟩ : syracuseStep 779087 = 1168631) B1168631
theorem B779103 : Blo 778337 779103 := bstep (se 1 (by rfl) ⟨584327, by rfl⟩ : syracuseStep 779103 = 1168655) B1168655
theorem B779131 : Blo 778337 779131 := bstep (se 1 (by rfl) ⟨584348, by rfl⟩ : syracuseStep 779131 = 1168697) B1168697
theorem B5006225 : Blo 778337 5006225 := bstep (se 2 (by rfl) ⟨1877334, by rfl⟩ : syracuseStep 5006225 = 3754669) B3754669
theorem B779183 : Blo 778337 779183 := bstep (se 1 (by rfl) ⟨584387, by rfl⟩ : syracuseStep 779183 = 1168775) B1168775
theorem B1172399 : Blo 778337 1172399 := bstep (se 1 (by rfl) ⟨879299, by rfl⟩ : syracuseStep 1172399 = 1758599) B1758599
theorem B779207 : Blo 778337 779207 := bstep (se 1 (by rfl) ⟨584405, by rfl⟩ : syracuseStep 779207 = 1168811) B1168811
theorem B779227 : Blo 778337 779227 := bstep (se 1 (by rfl) ⟨584420, by rfl⟩ : syracuseStep 779227 = 1168841) B1168841
theorem B877531 : Blo 778337 877531 := bstep (se 1 (by rfl) ⟨658148, by rfl⟩ : syracuseStep 877531 = 1316297) B1316297
theorem B1172489 : Blo 778337 1172489 := bstep (se 2 (by rfl) ⟨439683, by rfl⟩ : syracuseStep 1172489 = 879367) B879367
theorem B779303 : Blo 778337 779303 := bstep (se 1 (by rfl) ⟨584477, by rfl⟩ : syracuseStep 779303 = 1168955) B1168955
theorem B1172519 : Blo 778337 1172519 := bstep (se 1 (by rfl) ⟨879389, by rfl⟩ : syracuseStep 1172519 = 1758779) B1758779
theorem B779343 : Blo 778337 779343 := bstep (se 1 (by rfl) ⟨584507, by rfl⟩ : syracuseStep 779343 = 1169015) B1169015
theorem B779359 : Blo 778337 779359 := bstep (se 1 (by rfl) ⟨584519, by rfl⟩ : syracuseStep 779359 = 1169039) B1169039
theorem B779387 : Blo 778337 779387 := bstep (se 1 (by rfl) ⟨584540, by rfl⟩ : syracuseStep 779387 = 1169081) B1169081
theorem B1172603 : Blo 778337 1172603 := bstep (se 1 (by rfl) ⟨879452, by rfl⟩ : syracuseStep 1172603 = 1758905) B1758905
theorem B4449451 : Blo 778337 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B779439 : Blo 778337 779439 := bstep (se 1 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 779439 = 1169159) B1169159
theorem B779463 : Blo 778337 779463 := bstep (se 1 (by rfl) ⟨584597, by rfl⟩ : syracuseStep 779463 = 1169195) B1169195
theorem B779483 : Blo 778337 779483 := bstep (se 1 (by rfl) ⟨584612, by rfl⟩ : syracuseStep 779483 = 1169225) B1169225
theorem B1172729 : Blo 778337 1172729 := bstep (se 2 (by rfl) ⟨439773, by rfl⟩ : syracuseStep 1172729 = 879547) B879547
theorem B779559 : Blo 778337 779559 := bstep (se 1 (by rfl) ⟨584669, by rfl⟩ : syracuseStep 779559 = 1169339) B1169339
theorem B779599 : Blo 778337 779599 := bstep (se 1 (by rfl) ⟨584699, by rfl⟩ : syracuseStep 779599 = 1169399) B1169399
theorem B779615 : Blo 778337 779615 := bstep (se 1 (by rfl) ⟨584711, by rfl⟩ : syracuseStep 779615 = 1169423) B1169423
theorem B1172831 : Blo 778337 1172831 := bstep (se 1 (by rfl) ⟨879623, by rfl⟩ : syracuseStep 1172831 = 1759247) B1759247
theorem B1172843 : Blo 778337 1172843 := bstep (se 1 (by rfl) ⟨879632, by rfl⟩ : syracuseStep 1172843 = 1759265) B1759265
theorem B779643 : Blo 778337 779643 := bstep (se 1 (by rfl) ⟨584732, by rfl⟩ : syracuseStep 779643 = 1169465) B1169465
theorem B11265443 : Blo 778337 11265443 := bstep (se 1 (by rfl) ⟨8449082, by rfl⟩ : syracuseStep 11265443 = 16898165) B16898165
theorem B779695 : Blo 778337 779695 := bstep (se 1 (by rfl) ⟨584771, by rfl⟩ : syracuseStep 779695 = 1169543) B1169543
theorem B877999 : Blo 778337 877999 := bstep (se 1 (by rfl) ⟨658499, by rfl⟩ : syracuseStep 877999 = 1316999) B1316999
theorem B779719 : Blo 778337 779719 := bstep (se 1 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 779719 = 1169579) B1169579
theorem B779739 : Blo 778337 779739 := bstep (se 1 (by rfl) ⟨584804, by rfl⟩ : syracuseStep 779739 = 1169609) B1169609
theorem B5924339 : Blo 778337 5924339 := bstep (se 1 (by rfl) ⟨4443254, by rfl⟩ : syracuseStep 5924339 = 8886509) B8886509
theorem B3565043 : Blo 778337 3565043 := bstep (se 1 (by rfl) ⟨2673782, by rfl⟩ : syracuseStep 3565043 = 5347565) B5347565
theorem B779815 : Blo 778337 779815 := bstep (se 1 (by rfl) ⟨584861, by rfl⟩ : syracuseStep 779815 = 1169723) B1169723
theorem B779855 : Blo 778337 779855 := bstep (se 1 (by rfl) ⟨584891, by rfl⟩ : syracuseStep 779855 = 1169783) B1169783
theorem B1173071 : Blo 778337 1173071 := bstep (se 1 (by rfl) ⟨879803, by rfl⟩ : syracuseStep 1173071 = 1759607) B1759607
theorem B779871 : Blo 778337 779871 := bstep (se 1 (by rfl) ⟨584903, by rfl⟩ : syracuseStep 779871 = 1169807) B1169807
theorem B779899 : Blo 778337 779899 := bstep (se 1 (by rfl) ⟨584924, by rfl⟩ : syracuseStep 779899 = 1169849) B1169849
theorem B779951 : Blo 778337 779951 := bstep (se 1 (by rfl) ⟨584963, by rfl⟩ : syracuseStep 779951 = 1169927) B1169927
theorem B779975 : Blo 778337 779975 := bstep (se 1 (by rfl) ⟨584981, by rfl⟩ : syracuseStep 779975 = 1169963) B1169963
theorem B1173191 : Blo 778337 1173191 := bstep (se 1 (by rfl) ⟨879893, by rfl⟩ : syracuseStep 1173191 = 1759787) B1759787
theorem B779995 : Blo 778337 779995 := bstep (se 1 (by rfl) ⟨584996, by rfl⟩ : syracuseStep 779995 = 1169993) B1169993
theorem B780071 : Blo 778337 780071 := bstep (se 1 (by rfl) ⟨585053, by rfl⟩ : syracuseStep 780071 = 1170107) B1170107
theorem B1402697 : Blo 778337 1402697 := bstep (se 2 (by rfl) ⟨526011, by rfl⟩ : syracuseStep 1402697 = 1052023) B1052023
theorem B780111 : Blo 778337 780111 := bstep (se 1 (by rfl) ⟨585083, by rfl⟩ : syracuseStep 780111 = 1170167) B1170167
theorem B780127 : Blo 778337 780127 := bstep (se 1 (by rfl) ⟨585095, by rfl⟩ : syracuseStep 780127 = 1170191) B1170191
theorem B878431 : Blo 778337 878431 := bstep (se 1 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 878431 = 1317647) B1317647
theorem B1173353 : Blo 778337 1173353 := bstep (se 2 (by rfl) ⟨440007, by rfl⟩ : syracuseStep 1173353 = 880015) B880015
theorem B780155 : Blo 778337 780155 := bstep (se 1 (by rfl) ⟨585116, by rfl⟩ : syracuseStep 780155 = 1170233) B1170233
theorem B780207 : Blo 778337 780207 := bstep (se 1 (by rfl) ⟨585155, by rfl⟩ : syracuseStep 780207 = 1170311) B1170311
theorem B1173431 : Blo 778337 1173431 := bstep (se 1 (by rfl) ⟨880073, by rfl⟩ : syracuseStep 1173431 = 1760147) B1760147
theorem B23128001 : Blo 778337 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B780231 : Blo 778337 780231 := bstep (se 1 (by rfl) ⟨585173, by rfl⟩ : syracuseStep 780231 = 1170347) B1170347
theorem B780251 : Blo 778337 780251 := bstep (se 1 (by rfl) ⟨585188, by rfl⟩ : syracuseStep 780251 = 1170377) B1170377
theorem B1173467 : Blo 778337 1173467 := bstep (se 1 (by rfl) ⟨880100, by rfl⟩ : syracuseStep 1173467 = 1760201) B1760201
theorem B780327 : Blo 778337 780327 := bstep (se 1 (by rfl) ⟨585245, by rfl⟩ : syracuseStep 780327 = 1170491) B1170491
theorem B780367 : Blo 778337 780367 := bstep (se 1 (by rfl) ⟨585275, by rfl⟩ : syracuseStep 780367 = 1170551) B1170551
theorem B780383 : Blo 778337 780383 := bstep (se 1 (by rfl) ⟨585287, by rfl⟩ : syracuseStep 780383 = 1170575) B1170575
theorem B780411 : Blo 778337 780411 := bstep (se 1 (by rfl) ⟨585308, by rfl⟩ : syracuseStep 780411 = 1170617) B1170617
theorem B780463 : Blo 778337 780463 := bstep (se 1 (by rfl) ⟨585347, by rfl⟩ : syracuseStep 780463 = 1170695) B1170695
theorem B780487 : Blo 778337 780487 := bstep (se 1 (by rfl) ⟨585365, by rfl⟩ : syracuseStep 780487 = 1170731) B1170731
theorem B878791 : Blo 778337 878791 := bstep (se 1 (by rfl) ⟨659093, by rfl⟩ : syracuseStep 878791 = 1318187) B1318187
theorem B780507 : Blo 778337 780507 := bstep (se 1 (by rfl) ⟨585380, by rfl⟩ : syracuseStep 780507 = 1170761) B1170761
theorem B780583 : Blo 778337 780583 := bstep (se 1 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 780583 = 1170875) B1170875
theorem B780623 : Blo 778337 780623 := bstep (se 1 (by rfl) ⟨585467, by rfl⟩ : syracuseStep 780623 = 1170935) B1170935
theorem B780639 : Blo 778337 780639 := bstep (se 1 (by rfl) ⟨585479, by rfl⟩ : syracuseStep 780639 = 1170959) B1170959
theorem B780667 : Blo 778337 780667 := bstep (se 1 (by rfl) ⟨585500, by rfl⟩ : syracuseStep 780667 = 1171001) B1171001
theorem B1108399 : Blo 778337 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B780719 : Blo 778337 780719 := bstep (se 1 (by rfl) ⟨585539, by rfl⟩ : syracuseStep 780719 = 1171079) B1171079
theorem B780743 : Blo 778337 780743 := bstep (se 1 (by rfl) ⟨585557, by rfl⟩ : syracuseStep 780743 = 1171115) B1171115
theorem B780763 : Blo 778337 780763 := bstep (se 1 (by rfl) ⟨585572, by rfl⟩ : syracuseStep 780763 = 1171145) B1171145
theorem B2812441 : Blo 778337 2812441 := bstep (se 2 (by rfl) ⟨1054665, by rfl⟩ : syracuseStep 2812441 = 2109331) B2109331
theorem B780839 : Blo 778337 780839 := bstep (se 1 (by rfl) ⟨585629, by rfl⟩ : syracuseStep 780839 = 1171259) B1171259
theorem B780879 : Blo 778337 780879 := bstep (se 1 (by rfl) ⟨585659, by rfl⟩ : syracuseStep 780879 = 1171319) B1171319
theorem B780895 : Blo 778337 780895 := bstep (se 1 (by rfl) ⟨585671, by rfl⟩ : syracuseStep 780895 = 1171343) B1171343
theorem B780923 : Blo 778337 780923 := bstep (se 1 (by rfl) ⟨585692, by rfl⟩ : syracuseStep 780923 = 1171385) B1171385
theorem B780975 : Blo 778337 780975 := bstep (se 1 (by rfl) ⟨585731, by rfl⟩ : syracuseStep 780975 = 1171463) B1171463
theorem B780999 : Blo 778337 780999 := bstep (se 1 (by rfl) ⟨585749, by rfl⟩ : syracuseStep 780999 = 1171499) B1171499
theorem B781019 : Blo 778337 781019 := bstep (se 1 (by rfl) ⟨585764, by rfl⟩ : syracuseStep 781019 = 1171529) B1171529
theorem B781095 : Blo 778337 781095 := bstep (se 1 (by rfl) ⟨585821, by rfl⟩ : syracuseStep 781095 = 1171643) B1171643
theorem B781135 : Blo 778337 781135 := bstep (se 1 (by rfl) ⟨585851, by rfl⟩ : syracuseStep 781135 = 1171703) B1171703
theorem B8874845 : Blo 778337 8874845 := bstep (se 3 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 8874845 = 3328067) B3328067
theorem B781151 : Blo 778337 781151 := bstep (se 1 (by rfl) ⟨585863, by rfl⟩ : syracuseStep 781151 = 1171727) B1171727
theorem B781179 : Blo 778337 781179 := bstep (se 1 (by rfl) ⟨585884, by rfl⟩ : syracuseStep 781179 = 1171769) B1171769
theorem B781231 : Blo 778337 781231 := bstep (se 1 (by rfl) ⟨585923, by rfl⟩ : syracuseStep 781231 = 1171847) B1171847
theorem B4746167 : Blo 778337 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B781255 : Blo 778337 781255 := bstep (se 1 (by rfl) ⟨585941, by rfl⟩ : syracuseStep 781255 = 1171883) B1171883
theorem B781275 : Blo 778337 781275 := bstep (se 1 (by rfl) ⟨585956, by rfl⟩ : syracuseStep 781275 = 1171913) B1171913
theorem B781351 : Blo 778337 781351 := bstep (se 1 (by rfl) ⟨586013, by rfl⟩ : syracuseStep 781351 = 1172027) B1172027
theorem B879655 : Blo 778337 879655 := bstep (se 1 (by rfl) ⟨659741, by rfl⟩ : syracuseStep 879655 = 1319483) B1319483
theorem B781391 : Blo 778337 781391 := bstep (se 1 (by rfl) ⟨586043, by rfl⟩ : syracuseStep 781391 = 1172087) B1172087
theorem B781407 : Blo 778337 781407 := bstep (se 1 (by rfl) ⟨586055, by rfl⟩ : syracuseStep 781407 = 1172111) B1172111
theorem B781435 : Blo 778337 781435 := bstep (se 1 (by rfl) ⟨586076, by rfl⟩ : syracuseStep 781435 = 1172153) B1172153
theorem B781487 : Blo 778337 781487 := bstep (se 1 (by rfl) ⟨586115, by rfl⟩ : syracuseStep 781487 = 1172231) B1172231
theorem B781511 : Blo 778337 781511 := bstep (se 1 (by rfl) ⟨586133, by rfl⟩ : syracuseStep 781511 = 1172267) B1172267
theorem B781531 : Blo 778337 781531 := bstep (se 1 (by rfl) ⟨586148, by rfl⟩ : syracuseStep 781531 = 1172297) B1172297
theorem B6319397 : Blo 778337 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B781607 : Blo 778337 781607 := bstep (se 1 (by rfl) ⟨586205, by rfl⟩ : syracuseStep 781607 = 1172411) B1172411
theorem B781647 : Blo 778337 781647 := bstep (se 1 (by rfl) ⟨586235, by rfl⟩ : syracuseStep 781647 = 1172471) B1172471
theorem B781663 : Blo 778337 781663 := bstep (se 1 (by rfl) ⟨586247, by rfl⟩ : syracuseStep 781663 = 1172495) B1172495
theorem B781691 : Blo 778337 781691 := bstep (se 1 (by rfl) ⟨586268, by rfl⟩ : syracuseStep 781691 = 1172537) B1172537
theorem B781743 : Blo 778337 781743 := bstep (se 1 (by rfl) ⟨586307, by rfl⟩ : syracuseStep 781743 = 1172615) B1172615
theorem B781767 : Blo 778337 781767 := bstep (se 1 (by rfl) ⟨586325, by rfl⟩ : syracuseStep 781767 = 1172651) B1172651
theorem B781787 : Blo 778337 781787 := bstep (se 1 (by rfl) ⟨586340, by rfl⟩ : syracuseStep 781787 = 1172681) B1172681
theorem B781863 : Blo 778337 781863 := bstep (se 1 (by rfl) ⟨586397, by rfl⟩ : syracuseStep 781863 = 1172795) B1172795
theorem B781903 : Blo 778337 781903 := bstep (se 1 (by rfl) ⟨586427, by rfl⟩ : syracuseStep 781903 = 1172855) B1172855
theorem B781919 : Blo 778337 781919 := bstep (se 1 (by rfl) ⟨586439, by rfl⟩ : syracuseStep 781919 = 1172879) B1172879
theorem B2223713 : Blo 778337 2223713 := bstep (se 2 (by rfl) ⟨833892, by rfl⟩ : syracuseStep 2223713 = 1667785) B1667785
theorem B781947 : Blo 778337 781947 := bstep (se 1 (by rfl) ⟨586460, by rfl⟩ : syracuseStep 781947 = 1172921) B1172921
theorem B781999 : Blo 778337 781999 := bstep (se 1 (by rfl) ⟨586499, by rfl⟩ : syracuseStep 781999 = 1172999) B1172999
theorem B782023 : Blo 778337 782023 := bstep (se 1 (by rfl) ⟨586517, by rfl⟩ : syracuseStep 782023 = 1173035) B1173035
theorem B782043 : Blo 778337 782043 := bstep (se 1 (by rfl) ⟨586532, by rfl⟩ : syracuseStep 782043 = 1173065) B1173065
theorem B782119 : Blo 778337 782119 := bstep (se 1 (by rfl) ⟨586589, by rfl⟩ : syracuseStep 782119 = 1173179) B1173179
theorem B782159 : Blo 778337 782159 := bstep (se 1 (by rfl) ⟨586619, by rfl⟩ : syracuseStep 782159 = 1173239) B1173239
theorem B782175 : Blo 778337 782175 := bstep (se 1 (by rfl) ⟨586631, by rfl⟩ : syracuseStep 782175 = 1173263) B1173263
theorem B782203 : Blo 778337 782203 := bstep (se 1 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 782203 = 1173305) B1173305
theorem B782255 : Blo 778337 782255 := bstep (se 1 (by rfl) ⟨586691, by rfl⟩ : syracuseStep 782255 = 1173383) B1173383
theorem B782279 : Blo 778337 782279 := bstep (se 1 (by rfl) ⟨586709, by rfl⟩ : syracuseStep 782279 = 1173419) B1173419
theorem B782299 : Blo 778337 782299 := bstep (se 1 (by rfl) ⟨586724, by rfl⟩ : syracuseStep 782299 = 1173449) B1173449
theorem B4452367 : Blo 778337 4452367 := bstep (se 1 (by rfl) ⟨3339275, by rfl⟩ : syracuseStep 4452367 = 6678551) B6678551
theorem B22475069 : Blo 778337 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B5927255 : Blo 778337 5927255 := bstep (se 1 (by rfl) ⟨4445441, by rfl⟩ : syracuseStep 5927255 = 8890883) B8890883
theorem B1667947 : Blo 778337 1667947 := bstep (se 1 (by rfl) ⟨1250960, by rfl⟩ : syracuseStep 1667947 = 2501921) B2501921
theorem B2814977 : Blo 778337 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B2225171 : Blo 778337 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B10679363 : Blo 778337 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B2225627 : Blo 778337 2225627 := bstep (se 1 (by rfl) ⟨1669220, by rfl⟩ : syracuseStep 2225627 = 3338441) B3338441
theorem B1668647 : Blo 778337 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B6518369 : Blo 778337 6518369 := bstep (se 2 (by rfl) ⟨2444388, by rfl⟩ : syracuseStep 6518369 = 4888777) B4888777
theorem B4224761 : Blo 778337 4224761 := bstep (se 2 (by rfl) ⟨1584285, by rfl⟩ : syracuseStep 4224761 = 3168571) B3168571
theorem B1669177 : Blo 778337 1669177 := bstep (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) B1251883
theorem B3340369 : Blo 778337 3340369 := bstep (se 2 (by rfl) ⟨1252638, by rfl⟩ : syracuseStep 3340369 = 2505277) B2505277
theorem B12646637 : Blo 778337 12646637 := bstep (se 3 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 12646637 = 4742489) B4742489
theorem B7502381 : Blo 778337 7502381 := bstep (se 3 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 7502381 = 2813393) B2813393
theorem B2226811 : Blo 778337 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B1669843 : Blo 778337 1669843 := bstep (se 1 (by rfl) ⟨1252382, by rfl⟩ : syracuseStep 1669843 = 2504765) B2504765
theorem B11238173 : Blo 778337 11238173 := bstep (se 3 (by rfl) ⟨2107157, by rfl⟩ : syracuseStep 11238173 = 4214315) B4214315
theorem B4750255 : Blo 778337 4750255 := bstep (se 1 (by rfl) ⟨3562691, by rfl⟩ : syracuseStep 4750255 = 7125383) B7125383
theorem B32013785 : Blo 778337 32013785 := bstep (se 2 (by rfl) ⟨12005169, by rfl⟩ : syracuseStep 32013785 = 24010339) B24010339
theorem B2817575 : Blo 778337 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B1113679 : Blo 778337 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B6946541 : Blo 778337 6946541 := bstep (se 3 (by rfl) ⟨1302476, by rfl⟩ : syracuseStep 6946541 = 2604953) B2604953
theorem B62357521 : Blo 778337 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B2195819 : Blo 778337 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B32440933 : Blo 778337 32440933 := bstep (se 4 (by rfl) ⟨3041337, by rfl⟩ : syracuseStep 32440933 = 6082675) B6082675
theorem B9634619 : Blo 778337 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B5932601 : Blo 778337 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B9144515 : Blo 778337 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B985375 : Blo 778337 985375 := bstep (se 1 (by rfl) ⟨739031, by rfl⟩ : syracuseStep 985375 = 1478063) B1478063
theorem B1247815 : Blo 778337 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B1313455 : Blo 778337 1313455 := bstep (se 1 (by rfl) ⟨985091, by rfl⟩ : syracuseStep 1313455 = 1970183) B1970183
theorem B1477865 : Blo 778337 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1477919 : Blo 778337 1477919 := bstep (se 1 (by rfl) ⟨1108439, by rfl⟩ : syracuseStep 1477919 = 2216879) B2216879
theorem B1248635 : Blo 778337 1248635 := bstep (se 1 (by rfl) ⟨936476, by rfl⟩ : syracuseStep 1248635 = 1872953) B1872953
theorem B11243299 : Blo 778337 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B1052471 : Blo 778337 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B1315163 : Blo 778337 1315163 := bstep (se 1 (by rfl) ⟨986372, by rfl⟩ : syracuseStep 1315163 = 1972745) B1972745
theorem B1315183 : Blo 778337 1315183 := bstep (se 1 (by rfl) ⟨986387, by rfl⟩ : syracuseStep 1315183 = 1972775) B1972775
theorem B8425903 : Blo 778337 8425903 := bstep (se 1 (by rfl) ⟨6319427, by rfl⟩ : syracuseStep 8425903 = 12638855) B12638855
theorem B987643 : Blo 778337 987643 := bstep (se 1 (by rfl) ⟨740732, by rfl⟩ : syracuseStep 987643 = 1481465) B1481465
theorem B1806911 : Blo 778337 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B1315399 : Blo 778337 1315399 := bstep (se 1 (by rfl) ⟨986549, by rfl⟩ : syracuseStep 1315399 = 1973099) B1973099
theorem B1184431 : Blo 778337 1184431 := bstep (se 1 (by rfl) ⟨888323, by rfl⟩ : syracuseStep 1184431 = 1776647) B1776647
theorem B987871 : Blo 778337 987871 := bstep (se 1 (by rfl) ⟨740903, by rfl⟩ : syracuseStep 987871 = 1481807) B1481807
theorem B1970963 : Blo 778337 1970963 := bstep (se 1 (by rfl) ⟨1478222, by rfl⟩ : syracuseStep 1970963 = 2956445) B2956445
theorem B1971175 : Blo 778337 1971175 := bstep (se 1 (by rfl) ⟨1478381, by rfl⟩ : syracuseStep 1971175 = 2956763) B2956763
theorem B1315831 : Blo 778337 1315831 := bstep (se 1 (by rfl) ⟨986873, by rfl⟩ : syracuseStep 1315831 = 1973747) B1973747
theorem B7214123 : Blo 778337 7214123 := bstep (se 1 (by rfl) ⟨5410592, by rfl⟩ : syracuseStep 7214123 = 10821185) B10821185
theorem B1873115 : Blo 778337 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B1250537 : Blo 778337 1250537 := bstep (se 2 (by rfl) ⟨468951, by rfl⟩ : syracuseStep 1250537 = 937903) B937903
theorem B1971449 : Blo 778337 1971449 := bstep (se 2 (by rfl) ⟨739293, by rfl⟩ : syracuseStep 1971449 = 1478587) B1478587
theorem B1316135 : Blo 778337 1316135 := bstep (se 1 (by rfl) ⟨987101, by rfl⟩ : syracuseStep 1316135 = 1974203) B1974203
theorem B5936489 : Blo 778337 5936489 := bstep (se 2 (by rfl) ⟨2226183, by rfl⟩ : syracuseStep 5936489 = 4452367) B4452367
theorem B988615 : Blo 778337 988615 := bstep (se 1 (by rfl) ⟨741461, by rfl⟩ : syracuseStep 988615 = 1482923) B1482923
theorem B1054201 : Blo 778337 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B1316587 : Blo 778337 1316587 := bstep (se 1 (by rfl) ⟨987440, by rfl⟩ : syracuseStep 1316587 = 1974881) B1974881
theorem B1972097 : Blo 778337 1972097 := bstep (se 2 (by rfl) ⟨739536, by rfl⟩ : syracuseStep 1972097 = 1479073) B1479073
theorem B7510295 : Blo 778337 7510295 := bstep (se 1 (by rfl) ⟨5632721, by rfl⟩ : syracuseStep 7510295 = 11265443) B11265443
theorem B989759 : Blo 778337 989759 := bstep (se 1 (by rfl) ⟨742319, by rfl⟩ : syracuseStep 989759 = 1484639) B1484639
theorem B1972907 : Blo 778337 1972907 := bstep (se 1 (by rfl) ⟨1479680, by rfl⟩ : syracuseStep 1972907 = 2959361) B2959361
theorem B1317559 : Blo 778337 1317559 := bstep (se 1 (by rfl) ⟨988169, by rfl⟩ : syracuseStep 1317559 = 1976339) B1976339
theorem B1317863 : Blo 778337 1317863 := bstep (se 1 (by rfl) ⟨988397, by rfl⟩ : syracuseStep 1317863 = 1976795) B1976795
theorem B2628827 : Blo 778337 2628827 := bstep (se 1 (by rfl) ⟨1971620, by rfl⟩ : syracuseStep 2628827 = 3943241) B3943241
theorem B4005335 : Blo 778337 4005335 := bstep (se 1 (by rfl) ⟨3004001, by rfl⟩ : syracuseStep 4005335 = 6008003) B6008003
theorem B1973767 : Blo 778337 1973767 := bstep (se 1 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 1973767 = 2960651) B2960651
theorem B3743347 : Blo 778337 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1482475 : Blo 778337 1482475 := bstep (se 1 (by rfl) ⟨1111856, by rfl⟩ : syracuseStep 1482475 = 2223713) B2223713
theorem B1974071 : Blo 778337 1974071 := bstep (se 1 (by rfl) ⟨1480553, by rfl⟩ : syracuseStep 1974071 = 2961107) B2961107
theorem B21372731 : Blo 778337 21372731 := bstep (se 1 (by rfl) ⟨16029548, by rfl⟩ : syracuseStep 21372731 = 32059097) B32059097
theorem B57614141 : Blo 778337 57614141 := bstep (se 3 (by rfl) ⟨10802651, by rfl⟩ : syracuseStep 57614141 = 21605303) B21605303
theorem B7610273 : Blo 778337 7610273 := bstep (se 2 (by rfl) ⟨2853852, by rfl⟩ : syracuseStep 7610273 = 5707705) B5707705
theorem B30351289 : Blo 778337 30351289 := bstep (se 2 (by rfl) ⟨11381733, by rfl⟩ : syracuseStep 30351289 = 22763467) B22763467
theorem B2629691 : Blo 778337 2629691 := bstep (se 1 (by rfl) ⟨1972268, by rfl⟩ : syracuseStep 2629691 = 3944537) B3944537
theorem B2957417 : Blo 778337 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B1319017 : Blo 778337 1319017 := bstep (se 2 (by rfl) ⟨494631, by rfl⟩ : syracuseStep 1319017 = 989263) B989263
theorem B6660305 : Blo 778337 6660305 := bstep (se 2 (by rfl) ⟨2497614, by rfl⟩ : syracuseStep 6660305 = 4995229) B4995229
theorem B14983379 : Blo 778337 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B2629961 : Blo 778337 2629961 := bstep (se 2 (by rfl) ⟨986235, by rfl⟩ : syracuseStep 2629961 = 1972471) B1972471
theorem B1974739 : Blo 778337 1974739 := bstep (se 1 (by rfl) ⟨1481054, by rfl⟩ : syracuseStep 1974739 = 2962109) B2962109
theorem B1876651 : Blo 778337 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B1483447 : Blo 778337 1483447 := bstep (se 1 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 1483447 = 2225171) B2225171
theorem B7119575 : Blo 778337 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B3810007 : Blo 778337 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B16851725 : Blo 778337 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B42738445 : Blo 778337 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B1483751 : Blo 778337 1483751 := bstep (se 1 (by rfl) ⟨1112813, by rfl⟩ : syracuseStep 1483751 = 2225627) B2225627
theorem B2499731 : Blo 778337 2499731 := bstep (se 1 (by rfl) ⟨1874798, by rfl⟩ : syracuseStep 2499731 = 3749597) B3749597
theorem B2106587 : Blo 778337 2106587 := bstep (se 1 (by rfl) ⟨1579940, by rfl⟩ : syracuseStep 2106587 = 3159881) B3159881
theorem B1975529 : Blo 778337 1975529 := bstep (se 2 (by rfl) ⟨740823, by rfl⟩ : syracuseStep 1975529 = 1481647) B1481647
theorem B6333673 : Blo 778337 6333673 := bstep (se 2 (by rfl) ⟨2375127, by rfl⟩ : syracuseStep 6333673 = 4750255) B4750255
theorem B7480619 : Blo 778337 7480619 := bstep (se 1 (by rfl) ⟨5610464, by rfl⟩ : syracuseStep 7480619 = 11220929) B11220929
theorem B11412859 : Blo 778337 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B1975691 : Blo 778337 1975691 := bstep (se 1 (by rfl) ⟨1481768, by rfl⟩ : syracuseStep 1975691 = 2963537) B2963537
theorem B8431091 : Blo 778337 8431091 := bstep (se 1 (by rfl) ⟨6323318, by rfl⟩ : syracuseStep 8431091 = 12646637) B12646637
theorem B3941945 : Blo 778337 3941945 := bstep (se 2 (by rfl) ⟨1478229, by rfl⟩ : syracuseStep 3941945 = 2956459) B2956459
theorem B1484905 : Blo 778337 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B3745921 : Blo 778337 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B21342523 : Blo 778337 21342523 := bstep (se 1 (by rfl) ⟨16006892, by rfl⟩ : syracuseStep 21342523 = 32013785) B32013785
theorem B1976683 : Blo 778337 1976683 := bstep (se 1 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 1976683 = 2965025) B2965025
theorem B1878383 : Blo 778337 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B12003713 : Blo 778337 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B3156407 : Blo 778337 3156407 := bstep (se 1 (by rfl) ⟨2367305, by rfl⟩ : syracuseStep 3156407 = 4734611) B4734611
theorem B4631027 : Blo 778337 4631027 := bstep (se 1 (by rfl) ⟨3473270, by rfl⟩ : syracuseStep 4631027 = 6946541) B6946541
theorem B6761083 : Blo 778337 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B1977007 : Blo 778337 1977007 := bstep (se 1 (by rfl) ⟨1482755, by rfl⟩ : syracuseStep 1977007 = 2965511) B2965511
theorem B1977331 : Blo 778337 1977331 := bstep (se 1 (by rfl) ⟨1482998, by rfl⟩ : syracuseStep 1977331 = 2965997) B2965997
theorem B14265719 : Blo 778337 14265719 := bstep (se 1 (by rfl) ⟨10699289, by rfl⟩ : syracuseStep 14265719 = 21398579) B21398579
theorem B2633147 : Blo 778337 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B12037693 : Blo 778337 12037693 := bstep (se 3 (by rfl) ⟨2257067, by rfl⟩ : syracuseStep 12037693 = 4514135) B4514135
theorem B3944051 : Blo 778337 3944051 := bstep (se 1 (by rfl) ⟨2958038, by rfl⟩ : syracuseStep 3944051 = 5916077) B5916077
theorem B2502305 : Blo 778337 2502305 := bstep (se 2 (by rfl) ⟨938364, by rfl⟩ : syracuseStep 2502305 = 1876729) B1876729
theorem B1978091 : Blo 778337 1978091 := bstep (se 1 (by rfl) ⟨1483568, by rfl⟩ : syracuseStep 1978091 = 2967137) B2967137
theorem B2502407 : Blo 778337 2502407 := bstep (se 1 (by rfl) ⟨1876805, by rfl⟩ : syracuseStep 2502407 = 3753611) B3753611
theorem B5910731 : Blo 778337 5910731 := bstep (se 1 (by rfl) ⟨4433048, by rfl⟩ : syracuseStep 5910731 = 8866097) B8866097
theorem B2109721 : Blo 778337 2109721 := bstep (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) B1582291
theorem B1978951 : Blo 778337 1978951 := bstep (se 1 (by rfl) ⟨1484213, by rfl⟩ : syracuseStep 1978951 = 2968427) B2968427
theorem B1979063 : Blo 778337 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B4502585 : Blo 778337 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B3945671 : Blo 778337 3945671 := bstep (se 1 (by rfl) ⟨2959253, by rfl⟩ : syracuseStep 3945671 = 5918507) B5918507
theorem B832799 : Blo 778337 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B4437287 : Blo 778337 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B3945833 : Blo 778337 3945833 := bstep (se 2 (by rfl) ⟨1479687, by rfl⟩ : syracuseStep 3945833 = 2959375) B2959375
theorem B14202515 : Blo 778337 14202515 := bstep (se 1 (by rfl) ⟨10651886, by rfl⟩ : syracuseStep 14202515 = 21303773) B21303773
theorem B1980065 : Blo 778337 1980065 := bstep (se 2 (by rfl) ⟨742524, by rfl⟩ : syracuseStep 1980065 = 1485049) B1485049
theorem B3749921 : Blo 778337 3749921 := bstep (se 2 (by rfl) ⟨1406220, by rfl⟩ : syracuseStep 3749921 = 2812441) B2812441
theorem B1751471 : Blo 778337 1751471 := bstep (se 1 (by rfl) ⟨1313603, by rfl⟩ : syracuseStep 1751471 = 2627207) B2627207
theorem B1751507 : Blo 778337 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B4209191 : Blo 778337 4209191 := bstep (se 1 (by rfl) ⟨3156893, by rfl⟩ : syracuseStep 4209191 = 6313787) B6313787
theorem B1751615 : Blo 778337 1751615 := bstep (se 1 (by rfl) ⟨1313711, by rfl⟩ : syracuseStep 1751615 = 2627423) B2627423
theorem B5913161 : Blo 778337 5913161 := bstep (se 2 (by rfl) ⟨2217435, by rfl⟩ : syracuseStep 5913161 = 4434871) B4434871
theorem B2374217 : Blo 778337 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B1751723 : Blo 778337 1751723 := bstep (se 1 (by rfl) ⟨1313792, by rfl⟩ : syracuseStep 1751723 = 2627585) B2627585
theorem B899759 : Blo 778337 899759 := bstep (se 1 (by rfl) ⟨674819, by rfl⟩ : syracuseStep 899759 = 1349639) B1349639
theorem B1752263 : Blo 778337 1752263 := bstep (se 1 (by rfl) ⟨1314197, by rfl⟩ : syracuseStep 1752263 = 2628395) B2628395
theorem B247053635 : Blo 778337 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B1752443 : Blo 778337 1752443 := bstep (se 1 (by rfl) ⟨1314332, by rfl⟩ : syracuseStep 1752443 = 2628665) B2628665
theorem B3161531 : Blo 778337 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B7486921 : Blo 778337 7486921 := bstep (se 2 (by rfl) ⟨2807595, by rfl⟩ : syracuseStep 7486921 = 5615191) B5615191
theorem B1752569 : Blo 778337 1752569 := bstep (se 2 (by rfl) ⟨657213, by rfl⟩ : syracuseStep 1752569 = 1314427) B1314427
theorem B2637305 : Blo 778337 2637305 := bstep (se 2 (by rfl) ⟨988989, by rfl⟩ : syracuseStep 2637305 = 1977979) B1977979
theorem B835067 : Blo 778337 835067 := bstep (se 1 (by rfl) ⟨626300, by rfl⟩ : syracuseStep 835067 = 1252601) B1252601
theorem B1752659 : Blo 778337 1752659 := bstep (se 1 (by rfl) ⟨1314494, by rfl⟩ : syracuseStep 1752659 = 2628989) B2628989
theorem B1752839 : Blo 778337 1752839 := bstep (se 1 (by rfl) ⟨1314629, by rfl⟩ : syracuseStep 1752839 = 2629259) B2629259
theorem B2637575 : Blo 778337 2637575 := bstep (se 1 (by rfl) ⟨1978181, by rfl⟩ : syracuseStep 2637575 = 3956363) B3956363
theorem B2473775 : Blo 778337 2473775 := bstep (se 1 (by rfl) ⟨1855331, by rfl⟩ : syracuseStep 2473775 = 3710663) B3710663
theorem B2637629 : Blo 778337 2637629 := bstep (se 3 (by rfl) ⟨494555, by rfl⟩ : syracuseStep 2637629 = 989111) B989111
theorem B1753451 : Blo 778337 1753451 := bstep (se 1 (by rfl) ⟨1315088, by rfl⟩ : syracuseStep 1753451 = 2630177) B2630177
theorem B4440521 : Blo 778337 4440521 := bstep (se 2 (by rfl) ⟨1665195, by rfl⟩ : syracuseStep 4440521 = 3330391) B3330391
theorem B5915105 : Blo 778337 5915105 := bstep (se 2 (by rfl) ⟨2218164, by rfl⟩ : syracuseStep 5915105 = 4436329) B4436329
theorem B1753595 : Blo 778337 1753595 := bstep (se 1 (by rfl) ⟨1315196, by rfl⟩ : syracuseStep 1753595 = 2630393) B2630393
theorem B1753721 : Blo 778337 1753721 := bstep (se 2 (by rfl) ⟨657645, by rfl⟩ : syracuseStep 1753721 = 1315291) B1315291
theorem B32424583 : Blo 778337 32424583 := bstep (se 1 (by rfl) ⟨24318437, by rfl⟩ : syracuseStep 32424583 = 48636875) B48636875
theorem B1753775 : Blo 778337 1753775 := bstep (se 1 (by rfl) ⟨1315331, by rfl⟩ : syracuseStep 1753775 = 2630663) B2630663
theorem B1753847 : Blo 778337 1753847 := bstep (se 1 (by rfl) ⟨1315385, by rfl⟩ : syracuseStep 1753847 = 2630771) B2630771
theorem B1754027 : Blo 778337 1754027 := bstep (se 1 (by rfl) ⟨1315520, by rfl⟩ : syracuseStep 1754027 = 2631041) B2631041
theorem B3949559 : Blo 778337 3949559 := bstep (se 1 (by rfl) ⟨2962169, by rfl⟩ : syracuseStep 3949559 = 5924339) B5924339
theorem B2376695 : Blo 778337 2376695 := bstep (se 1 (by rfl) ⟨1782521, by rfl⟩ : syracuseStep 2376695 = 3565043) B3565043
theorem B935131 : Blo 778337 935131 := bstep (se 1 (by rfl) ⟨701348, by rfl⟩ : syracuseStep 935131 = 1402697) B1402697
theorem B15418667 : Blo 778337 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B1754567 : Blo 778337 1754567 := bstep (se 1 (by rfl) ⟨1315925, by rfl⟩ : syracuseStep 1754567 = 2631851) B2631851
theorem B1754927 : Blo 778337 1754927 := bstep (se 1 (by rfl) ⟨1316195, by rfl⟩ : syracuseStep 1754927 = 2632391) B2632391
theorem B5916563 : Blo 778337 5916563 := bstep (se 1 (by rfl) ⟨4437422, by rfl⟩ : syracuseStep 5916563 = 8874845) B8874845
theorem B3164111 : Blo 778337 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B33736661 : Blo 778337 33736661 := bstep (se 7 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 33736661 = 790703) B790703
theorem B2672905 : Blo 778337 2672905 := bstep (se 2 (by rfl) ⟨1002339, by rfl⟩ : syracuseStep 2672905 = 2004679) B2004679
theorem B1755503 : Blo 778337 1755503 := bstep (se 1 (by rfl) ⟨1316627, by rfl⟩ : syracuseStep 1755503 = 2633255) B2633255
theorem B1755575 : Blo 778337 1755575 := bstep (se 1 (by rfl) ⟨1316681, by rfl⟩ : syracuseStep 1755575 = 2633363) B2633363
theorem B1755719 : Blo 778337 1755719 := bstep (se 1 (by rfl) ⟨1316789, by rfl⟩ : syracuseStep 1755719 = 2633579) B2633579
theorem B1755755 : Blo 778337 1755755 := bstep (se 1 (by rfl) ⟨1316816, by rfl⟩ : syracuseStep 1755755 = 2633633) B2633633
theorem B3951503 : Blo 778337 3951503 := bstep (se 1 (by rfl) ⟨2963627, by rfl⟩ : syracuseStep 3951503 = 5927255) B5927255
theorem B1756151 : Blo 778337 1756151 := bstep (se 1 (by rfl) ⟨1317113, by rfl⟩ : syracuseStep 1756151 = 2634227) B2634227
theorem B1756511 : Blo 778337 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B2969081 : Blo 778337 2969081 := bstep (se 2 (by rfl) ⟨1113405, by rfl⟩ : syracuseStep 2969081 = 2226811) B2226811
theorem B1756907 : Blo 778337 1756907 := bstep (se 1 (by rfl) ⟨1317680, by rfl⟩ : syracuseStep 1756907 = 2635361) B2635361
theorem B4345579 : Blo 778337 4345579 := bstep (se 1 (by rfl) ⟨3259184, by rfl⟩ : syracuseStep 4345579 = 6518369) B6518369
theorem B1757033 : Blo 778337 1757033 := bstep (se 2 (by rfl) ⟨658887, by rfl⟩ : syracuseStep 1757033 = 1317775) B1317775
theorem B1167707 : Blo 778337 1167707 := bstep (se 1 (by rfl) ⟨875780, by rfl⟩ : syracuseStep 1167707 = 1751561) B1751561
theorem B5001587 : Blo 778337 5001587 := bstep (se 1 (by rfl) ⟨3751190, by rfl⟩ : syracuseStep 5001587 = 7502381) B7502381
theorem B7492115 : Blo 778337 7492115 := bstep (se 1 (by rfl) ⟨5619086, by rfl⟩ : syracuseStep 7492115 = 11238173) B11238173
theorem B1167935 : Blo 778337 1167935 := bstep (se 1 (by rfl) ⟨875951, by rfl⟩ : syracuseStep 1167935 = 1751903) B1751903
theorem B1168055 : Blo 778337 1168055 := bstep (se 1 (by rfl) ⟨876041, by rfl⟩ : syracuseStep 1168055 = 1752083) B1752083
theorem B1757879 : Blo 778337 1757879 := bstep (se 1 (by rfl) ⟨1318409, by rfl⟩ : syracuseStep 1757879 = 2636819) B2636819
theorem B4444895 : Blo 778337 4444895 := bstep (se 1 (by rfl) ⟨3333671, by rfl⟩ : syracuseStep 4444895 = 6667343) B6667343
theorem B1758095 : Blo 778337 1758095 := bstep (se 1 (by rfl) ⟨1318571, by rfl⟩ : syracuseStep 1758095 = 2637143) B2637143
theorem B1168283 : Blo 778337 1168283 := bstep (se 1 (by rfl) ⟨876212, by rfl⟩ : syracuseStep 1168283 = 1752425) B1752425
theorem B3953609 : Blo 778337 3953609 := bstep (se 2 (by rfl) ⟨1482603, by rfl⟩ : syracuseStep 3953609 = 2965207) B2965207
theorem B9982925 : Blo 778337 9982925 := bstep (se 3 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 9982925 = 3743597) B3743597
theorem B1692905 : Blo 778337 1692905 := bstep (se 2 (by rfl) ⟨634839, by rfl⟩ : syracuseStep 1692905 = 1269679) B1269679
theorem B1168679 : Blo 778337 1168679 := bstep (se 1 (by rfl) ⟨876509, by rfl⟩ : syracuseStep 1168679 = 1753019) B1753019
theorem B30365027 : Blo 778337 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B1168763 : Blo 778337 1168763 := bstep (se 1 (by rfl) ⟨876572, by rfl⟩ : syracuseStep 1168763 = 1753145) B1753145
theorem B5625227 : Blo 778337 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B1168889 : Blo 778337 1168889 := bstep (se 2 (by rfl) ⟨438333, by rfl⟩ : syracuseStep 1168889 = 876667) B876667
theorem B1168991 : Blo 778337 1168991 := bstep (se 1 (by rfl) ⟨876743, by rfl⟩ : syracuseStep 1168991 = 1753487) B1753487
theorem B1758815 : Blo 778337 1758815 := bstep (se 1 (by rfl) ⟨1319111, by rfl⟩ : syracuseStep 1758815 = 2638223) B2638223
theorem B1070699 : Blo 778337 1070699 := bstep (se 1 (by rfl) ⟨803024, by rfl⟩ : syracuseStep 1070699 = 1606049) B1606049
theorem B1169207 : Blo 778337 1169207 := bstep (se 1 (by rfl) ⟨876905, by rfl⟩ : syracuseStep 1169207 = 1753811) B1753811
theorem B1759031 : Blo 778337 1759031 := bstep (se 1 (by rfl) ⟨1319273, by rfl⟩ : syracuseStep 1759031 = 2638547) B2638547
theorem B1169513 : Blo 778337 1169513 := bstep (se 2 (by rfl) ⟨438567, by rfl⟩ : syracuseStep 1169513 = 877135) B877135
theorem B1759337 : Blo 778337 1759337 := bstep (se 2 (by rfl) ⟨659751, by rfl⟩ : syracuseStep 1759337 = 1319503) B1319503
theorem B1169831 : Blo 778337 1169831 := bstep (se 1 (by rfl) ⟨877373, by rfl⟩ : syracuseStep 1169831 = 1754747) B1754747
theorem B1169915 : Blo 778337 1169915 := bstep (se 1 (by rfl) ⟨877436, by rfl⟩ : syracuseStep 1169915 = 1754873) B1754873
theorem B1759823 : Blo 778337 1759823 := bstep (se 1 (by rfl) ⟨1319867, by rfl⟩ : syracuseStep 1759823 = 2639735) B2639735
theorem B1170041 : Blo 778337 1170041 := bstep (se 2 (by rfl) ⟨438765, by rfl⟩ : syracuseStep 1170041 = 877531) B877531
theorem B1170095 : Blo 778337 1170095 := bstep (se 1 (by rfl) ⟨877571, by rfl⟩ : syracuseStep 1170095 = 1755143) B1755143
theorem B1170143 : Blo 778337 1170143 := bstep (se 1 (by rfl) ⟨877607, by rfl⟩ : syracuseStep 1170143 = 1755215) B1755215
theorem B1759967 : Blo 778337 1759967 := bstep (se 1 (by rfl) ⟨1319975, by rfl⟩ : syracuseStep 1759967 = 2639951) B2639951
theorem B8444675 : Blo 778337 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B9001847 : Blo 778337 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B1760219 : Blo 778337 1760219 := bstep (se 1 (by rfl) ⟨1320164, by rfl⟩ : syracuseStep 1760219 = 2640329) B2640329
theorem B1170407 : Blo 778337 1170407 := bstep (se 1 (by rfl) ⟨877805, by rfl⟩ : syracuseStep 1170407 = 1755611) B1755611
theorem B13327577 : Blo 778337 13327577 := bstep (se 2 (by rfl) ⟨4997841, by rfl⟩ : syracuseStep 13327577 = 9995683) B9995683
theorem B1170665 : Blo 778337 1170665 := bstep (se 2 (by rfl) ⟨438999, by rfl⟩ : syracuseStep 1170665 = 877999) B877999
theorem B1170719 : Blo 778337 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B1170887 : Blo 778337 1170887 := bstep (se 1 (by rfl) ⟨878165, by rfl⟩ : syracuseStep 1170887 = 1756331) B1756331
theorem B876127 : Blo 778337 876127 := bstep (se 1 (by rfl) ⟨657095, by rfl⟩ : syracuseStep 876127 = 1314191) B1314191
theorem B1171241 : Blo 778337 1171241 := bstep (se 2 (by rfl) ⟨439215, by rfl⟩ : syracuseStep 1171241 = 878431) B878431
theorem B1171247 : Blo 778337 1171247 := bstep (se 1 (by rfl) ⟨878435, by rfl⟩ : syracuseStep 1171247 = 1756871) B1756871
theorem B3334355 : Blo 778337 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B1171721 : Blo 778337 1171721 := bstep (se 2 (by rfl) ⟨439395, by rfl⟩ : syracuseStep 1171721 = 878791) B878791
theorem B778527 : Blo 778337 778527 := bstep (se 1 (by rfl) ⟨583895, by rfl⟩ : syracuseStep 778527 = 1167791) B1167791
theorem B778587 : Blo 778337 778587 := bstep (se 1 (by rfl) ⟨583940, by rfl⟩ : syracuseStep 778587 = 1167881) B1167881
theorem B778607 : Blo 778337 778607 := bstep (se 1 (by rfl) ⟨583955, by rfl⟩ : syracuseStep 778607 = 1167911) B1167911
theorem B1171823 : Blo 778337 1171823 := bstep (se 1 (by rfl) ⟨878867, by rfl⟩ : syracuseStep 1171823 = 1757735) B1757735
theorem B778663 : Blo 778337 778663 := bstep (se 1 (by rfl) ⟨583997, by rfl⟩ : syracuseStep 778663 = 1167995) B1167995
theorem B778747 : Blo 778337 778747 := bstep (se 1 (by rfl) ⟨584060, by rfl⟩ : syracuseStep 778747 = 1168121) B1168121
theorem B25354781 : Blo 778337 25354781 := bstep (se 3 (by rfl) ⟨4754021, by rfl⟩ : syracuseStep 25354781 = 9508043) B9508043
theorem B778815 : Blo 778337 778815 := bstep (se 1 (by rfl) ⟨584111, by rfl⟩ : syracuseStep 778815 = 1168223) B1168223
theorem B778823 : Blo 778337 778823 := bstep (se 1 (by rfl) ⟨584117, by rfl⟩ : syracuseStep 778823 = 1168235) B1168235
theorem B1172039 : Blo 778337 1172039 := bstep (se 1 (by rfl) ⟨879029, by rfl⟩ : syracuseStep 1172039 = 1758059) B1758059
theorem B1172075 : Blo 778337 1172075 := bstep (se 1 (by rfl) ⟨879056, by rfl⟩ : syracuseStep 1172075 = 1758113) B1758113
theorem B4448951 : Blo 778337 4448951 := bstep (se 1 (by rfl) ⟨3336713, by rfl⟩ : syracuseStep 4448951 = 6673427) B6673427
theorem B778975 : Blo 778337 778975 := bstep (se 1 (by rfl) ⟨584231, by rfl⟩ : syracuseStep 778975 = 1168463) B1168463
theorem B877279 : Blo 778337 877279 := bstep (se 1 (by rfl) ⟨657959, by rfl⟩ : syracuseStep 877279 = 1315919) B1315919
theorem B3957497 : Blo 778337 3957497 := bstep (se 2 (by rfl) ⟨1484061, by rfl⟩ : syracuseStep 3957497 = 2968123) B2968123
theorem B779055 : Blo 778337 779055 := bstep (se 1 (by rfl) ⟨584291, by rfl⟩ : syracuseStep 779055 = 1168583) B1168583
theorem B1172303 : Blo 778337 1172303 := bstep (se 1 (by rfl) ⟨879227, by rfl⟩ : syracuseStep 1172303 = 1758455) B1758455
theorem B779163 : Blo 778337 779163 := bstep (se 1 (by rfl) ⟨584372, by rfl⟩ : syracuseStep 779163 = 1168745) B1168745
theorem B1663915 : Blo 778337 1663915 := bstep (se 1 (by rfl) ⟨1247936, by rfl⟩ : syracuseStep 1663915 = 2495873) B2495873
theorem B3335107 : Blo 778337 3335107 := bstep (se 1 (by rfl) ⟨2501330, by rfl⟩ : syracuseStep 3335107 = 5002661) B5002661
theorem B779215 : Blo 778337 779215 := bstep (se 1 (by rfl) ⟨584411, by rfl⟩ : syracuseStep 779215 = 1168823) B1168823
theorem B779239 : Blo 778337 779239 := bstep (se 1 (by rfl) ⟨584429, by rfl⟩ : syracuseStep 779239 = 1168859) B1168859
theorem B9495589 : Blo 778337 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B15033437 : Blo 778337 15033437 := bstep (se 3 (by rfl) ⟨2818769, by rfl⟩ : syracuseStep 15033437 = 5637539) B5637539
theorem B1172699 : Blo 778337 1172699 := bstep (se 1 (by rfl) ⟨879524, by rfl⟩ : syracuseStep 1172699 = 1759049) B1759049
theorem B779551 : Blo 778337 779551 := bstep (se 1 (by rfl) ⟨584663, by rfl⟩ : syracuseStep 779551 = 1169327) B1169327
theorem B877855 : Blo 778337 877855 := bstep (se 1 (by rfl) ⟨658391, by rfl⟩ : syracuseStep 877855 = 1316783) B1316783
theorem B779611 : Blo 778337 779611 := bstep (se 1 (by rfl) ⟨584708, by rfl⟩ : syracuseStep 779611 = 1169417) B1169417
theorem B779631 : Blo 778337 779631 := bstep (se 1 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 779631 = 1169447) B1169447
theorem B1172873 : Blo 778337 1172873 := bstep (se 2 (by rfl) ⟨439827, by rfl⟩ : syracuseStep 1172873 = 879655) B879655
theorem B779687 : Blo 778337 779687 := bstep (se 1 (by rfl) ⟨584765, by rfl⟩ : syracuseStep 779687 = 1169531) B1169531
theorem B4449725 : Blo 778337 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B779771 : Blo 778337 779771 := bstep (se 1 (by rfl) ⟨584828, by rfl⟩ : syracuseStep 779771 = 1169657) B1169657
theorem B779839 : Blo 778337 779839 := bstep (se 1 (by rfl) ⟨584879, by rfl⟩ : syracuseStep 779839 = 1169759) B1169759
theorem B878143 : Blo 778337 878143 := bstep (se 1 (by rfl) ⟨658607, by rfl⟩ : syracuseStep 878143 = 1317215) B1317215
theorem B779847 : Blo 778337 779847 := bstep (se 1 (by rfl) ⟨584885, by rfl⟩ : syracuseStep 779847 = 1169771) B1169771
theorem B779999 : Blo 778337 779999 := bstep (se 1 (by rfl) ⟨584999, by rfl⟩ : syracuseStep 779999 = 1169999) B1169999
theorem B1173227 : Blo 778337 1173227 := bstep (se 1 (by rfl) ⟨879920, by rfl⟩ : syracuseStep 1173227 = 1759841) B1759841
theorem B780079 : Blo 778337 780079 := bstep (se 1 (by rfl) ⟨585059, by rfl⟩ : syracuseStep 780079 = 1170119) B1170119
theorem B780187 : Blo 778337 780187 := bstep (se 1 (by rfl) ⟨585140, by rfl⟩ : syracuseStep 780187 = 1170281) B1170281
theorem B780239 : Blo 778337 780239 := bstep (se 1 (by rfl) ⟨585179, by rfl⟩ : syracuseStep 780239 = 1170359) B1170359
theorem B1173455 : Blo 778337 1173455 := bstep (se 1 (by rfl) ⟨880091, by rfl⟩ : syracuseStep 1173455 = 1760183) B1760183
theorem B780263 : Blo 778337 780263 := bstep (se 1 (by rfl) ⟨585197, by rfl⟩ : syracuseStep 780263 = 1170395) B1170395
theorem B14968921 : Blo 778337 14968921 := bstep (se 2 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 14968921 = 11226691) B11226691
theorem B780575 : Blo 778337 780575 := bstep (se 1 (by rfl) ⟨585431, by rfl⟩ : syracuseStep 780575 = 1170863) B1170863
theorem B780635 : Blo 778337 780635 := bstep (se 1 (by rfl) ⟨585476, by rfl⟩ : syracuseStep 780635 = 1170953) B1170953
theorem B780655 : Blo 778337 780655 := bstep (se 1 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 780655 = 1170983) B1170983
theorem B878971 : Blo 778337 878971 := bstep (se 1 (by rfl) ⟨659228, by rfl⟩ : syracuseStep 878971 = 1318457) B1318457
theorem B780711 : Blo 778337 780711 := bstep (se 1 (by rfl) ⟨585533, by rfl⟩ : syracuseStep 780711 = 1171067) B1171067
theorem B4450727 : Blo 778337 4450727 := bstep (se 1 (by rfl) ⟨3338045, by rfl⟩ : syracuseStep 4450727 = 6676091) B6676091
theorem B780795 : Blo 778337 780795 := bstep (se 1 (by rfl) ⟨585596, by rfl⟩ : syracuseStep 780795 = 1171193) B1171193
theorem B780863 : Blo 778337 780863 := bstep (se 1 (by rfl) ⟨585647, by rfl⟩ : syracuseStep 780863 = 1171295) B1171295
theorem B780871 : Blo 778337 780871 := bstep (se 1 (by rfl) ⟨585653, by rfl⟩ : syracuseStep 780871 = 1171307) B1171307
theorem B781023 : Blo 778337 781023 := bstep (se 1 (by rfl) ⟨585767, by rfl⟩ : syracuseStep 781023 = 1171535) B1171535
theorem B781103 : Blo 778337 781103 := bstep (se 1 (by rfl) ⟨585827, by rfl⟩ : syracuseStep 781103 = 1171655) B1171655
theorem B879439 : Blo 778337 879439 := bstep (se 1 (by rfl) ⟨659579, by rfl⟩ : syracuseStep 879439 = 1319159) B1319159
theorem B781211 : Blo 778337 781211 := bstep (se 1 (by rfl) ⟨585908, by rfl⟩ : syracuseStep 781211 = 1171817) B1171817
theorem B781263 : Blo 778337 781263 := bstep (se 1 (by rfl) ⟨585947, by rfl⟩ : syracuseStep 781263 = 1171895) B1171895
theorem B781287 : Blo 778337 781287 := bstep (se 1 (by rfl) ⟨585965, by rfl⟩ : syracuseStep 781287 = 1171931) B1171931
theorem B10021927 : Blo 778337 10021927 := bstep (se 1 (by rfl) ⟨7516445, by rfl⟩ : syracuseStep 10021927 = 15032891) B15032891
theorem B1666145 : Blo 778337 1666145 := bstep (se 2 (by rfl) ⟨624804, by rfl⟩ : syracuseStep 1666145 = 1249609) B1249609
theorem B879835 : Blo 778337 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B3337483 : Blo 778337 3337483 := bstep (se 1 (by rfl) ⟨2503112, by rfl⟩ : syracuseStep 3337483 = 5006225) B5006225
theorem B781599 : Blo 778337 781599 := bstep (se 1 (by rfl) ⟨586199, by rfl⟩ : syracuseStep 781599 = 1172399) B1172399
theorem B781659 : Blo 778337 781659 := bstep (se 1 (by rfl) ⟨586244, by rfl⟩ : syracuseStep 781659 = 1172489) B1172489
theorem B781679 : Blo 778337 781679 := bstep (se 1 (by rfl) ⟨586259, by rfl⟩ : syracuseStep 781679 = 1172519) B1172519
theorem B781735 : Blo 778337 781735 := bstep (se 1 (by rfl) ⟨586301, by rfl⟩ : syracuseStep 781735 = 1172603) B1172603
theorem B3960251 : Blo 778337 3960251 := bstep (se 1 (by rfl) ⟨2970188, by rfl⟩ : syracuseStep 3960251 = 5940377) B5940377
theorem B781819 : Blo 778337 781819 := bstep (se 1 (by rfl) ⟨586364, by rfl⟩ : syracuseStep 781819 = 1172729) B1172729
theorem B880123 : Blo 778337 880123 := bstep (se 1 (by rfl) ⟨660092, by rfl⟩ : syracuseStep 880123 = 1320185) B1320185
theorem B781887 : Blo 778337 781887 := bstep (se 1 (by rfl) ⟨586415, by rfl⟩ : syracuseStep 781887 = 1172831) B1172831
theorem B781895 : Blo 778337 781895 := bstep (se 1 (by rfl) ⟨586421, by rfl⟩ : syracuseStep 781895 = 1172843) B1172843
theorem B782047 : Blo 778337 782047 := bstep (se 1 (by rfl) ⟨586535, by rfl⟩ : syracuseStep 782047 = 1173071) B1173071
theorem B782127 : Blo 778337 782127 := bstep (se 1 (by rfl) ⟨586595, by rfl⟩ : syracuseStep 782127 = 1173191) B1173191
theorem B2223929 : Blo 778337 2223929 := bstep (se 2 (by rfl) ⟨833973, by rfl⟩ : syracuseStep 2223929 = 1667947) B1667947
theorem B782235 : Blo 778337 782235 := bstep (se 1 (by rfl) ⟨586676, by rfl⟩ : syracuseStep 782235 = 1173353) B1173353
theorem B9531341 : Blo 778337 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B782287 : Blo 778337 782287 := bstep (se 1 (by rfl) ⟨586715, by rfl⟩ : syracuseStep 782287 = 1173431) B1173431
theorem B782311 : Blo 778337 782311 := bstep (se 1 (by rfl) ⟨586733, by rfl⟩ : syracuseStep 782311 = 1173467) B1173467
theorem B8876303 : Blo 778337 8876303 := bstep (se 1 (by rfl) ⟨6657227, by rfl⟩ : syracuseStep 8876303 = 13314455) B13314455
theorem B6681149 : Blo 778337 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B8417945 : Blo 778337 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B1405615 : Blo 778337 1405615 := bstep (se 1 (by rfl) ⟨1054211, by rfl⟩ : syracuseStep 1405615 = 2108423) B2108423
theorem B1405775 : Blo 778337 1405775 := bstep (se 1 (by rfl) ⟨1054331, by rfl⟩ : syracuseStep 1405775 = 2108663) B2108663
theorem B8451161 : Blo 778337 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B2225569 : Blo 778337 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B4453825 : Blo 778337 4453825 := bstep (se 2 (by rfl) ⟨1670184, by rfl⟩ : syracuseStep 4453825 = 3340369) B3340369
theorem B2029369 : Blo 778337 2029369 := bstep (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) B1522027
theorem B570095633 : Blo 778337 570095633 := bstep (se 2 (by rfl) ⟨213785862, by rfl⟩ : syracuseStep 570095633 = 427571725) B427571725
theorem B1669331 : Blo 778337 1669331 := bstep (se 1 (by rfl) ⟨1251998, by rfl⟩ : syracuseStep 1669331 = 2503997) B2503997
theorem B3340541 : Blo 778337 3340541 := bstep (se 3 (by rfl) ⟨626351, by rfl⟩ : syracuseStep 3340541 = 1252703) B1252703
theorem B1112329 : Blo 778337 1112329 := bstep (se 2 (by rfl) ⟨417123, by rfl⟩ : syracuseStep 1112329 = 834247) B834247
theorem B2226457 : Blo 778337 2226457 := bstep (se 2 (by rfl) ⟨834921, by rfl⟩ : syracuseStep 2226457 = 1669843) B1669843
theorem B121534825 : Blo 778337 121534825 := bstep (se 2 (by rfl) ⟨45575559, by rfl⟩ : syracuseStep 121534825 = 91151119) B91151119
theorem B2816507 : Blo 778337 2816507 := bstep (se 1 (by rfl) ⟨2112380, by rfl⟩ : syracuseStep 2816507 = 4224761) B4224761
theorem B6650909 : Blo 778337 6650909 := bstep (se 3 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 6650909 = 2494091) B2494091
theorem B1670561 : Blo 778337 1670561 := bstep (se 2 (by rfl) ⟨626460, by rfl⟩ : syracuseStep 1670561 = 1252921) B1252921
theorem B1113593 : Blo 778337 1113593 := bstep (se 2 (by rfl) ⟨417597, by rfl⟩ : syracuseStep 1113593 = 835195) B835195
theorem B1670663 : Blo 778337 1670663 := bstep (se 1 (by rfl) ⟨1252997, by rfl⟩ : syracuseStep 1670663 = 2505995) B2505995
theorem B5930657 : Blo 778337 5930657 := bstep (se 2 (by rfl) ⟨2223996, by rfl⟩ : syracuseStep 5930657 = 4447993) B4447993
theorem B6423079 : Blo 778337 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B43254577 : Blo 778337 43254577 := bstep (se 2 (by rfl) ⟨16220466, by rfl⟩ : syracuseStep 43254577 = 32440933) B32440933
theorem B5080009 : Blo 778337 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B56984593 : Blo 778337 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B6096343 : Blo 778337 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B1246841 : Blo 778337 1246841 := bstep (se 2 (by rfl) ⟨467565, by rfl⟩ : syracuseStep 1246841 = 935131) B935131
theorem B985279 : Blo 778337 985279 := bstep (se 1 (by rfl) ⟨738959, by rfl⟩ : syracuseStep 985279 = 1477919) B1477919
theorem B19958561 : Blo 778337 19958561 := bstep (se 2 (by rfl) ⟨7484460, by rfl⟩ : syracuseStep 19958561 = 14968921) B14968921
theorem B1313833 : Blo 778337 1313833 := bstep (se 2 (by rfl) ⟨492687, by rfl⟩ : syracuseStep 1313833 = 985375) B985375
theorem B1313975 : Blo 778337 1313975 := bstep (se 1 (by rfl) ⟨985481, by rfl⟩ : syracuseStep 1313975 = 1970963) B1970963
theorem B6655283 : Blo 778337 6655283 := bstep (se 1 (by rfl) ⟨4991462, by rfl⟩ : syracuseStep 6655283 = 9982925) B9982925
theorem B1248743 : Blo 778337 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B9014777 : Blo 778337 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1314299 : Blo 778337 1314299 := bstep (se 1 (by rfl) ⟨985724, by rfl⟩ : syracuseStep 1314299 = 1971449) B1971449
theorem B1314731 : Blo 778337 1314731 := bstep (se 1 (by rfl) ⟨986048, by rfl⟩ : syracuseStep 1314731 = 1972097) B1972097
theorem B2855197 : Blo 778337 2855197 := bstep (se 3 (by rfl) ⟨535349, by rfl⟩ : syracuseStep 2855197 = 1070699) B1070699
theorem B1315271 : Blo 778337 1315271 := bstep (se 1 (by rfl) ⟨986453, by rfl⟩ : syracuseStep 1315271 = 1972907) B1972907
theorem B6001231 : Blo 778337 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B8885051 : Blo 778337 8885051 := bstep (se 1 (by rfl) ⟨6663788, by rfl⟩ : syracuseStep 8885051 = 13327577) B13327577
theorem B1316047 : Blo 778337 1316047 := bstep (se 1 (by rfl) ⟨987035, by rfl⟩ : syracuseStep 1316047 = 1974071) B1974071
theorem B38409427 : Blo 778337 38409427 := bstep (se 1 (by rfl) ⟨28807070, by rfl⟩ : syracuseStep 38409427 = 57614141) B57614141
theorem B1971611 : Blo 778337 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B989167 : Blo 778337 989167 := bstep (se 1 (by rfl) ⟨741875, by rfl⟩ : syracuseStep 989167 = 1483751) B1483751
theorem B1316857 : Blo 778337 1316857 := bstep (se 2 (by rfl) ⟨493821, by rfl⟩ : syracuseStep 1316857 = 987643) B987643
theorem B1317019 : Blo 778337 1317019 := bstep (se 1 (by rfl) ⟨987764, by rfl⟩ : syracuseStep 1317019 = 1975529) B1975529
theorem B4987079 : Blo 778337 4987079 := bstep (se 1 (by rfl) ⟨3740309, by rfl⟩ : syracuseStep 4987079 = 7480619) B7480619
theorem B1579241 : Blo 778337 1579241 := bstep (se 2 (by rfl) ⟨592215, by rfl⟩ : syracuseStep 1579241 = 1184431) B1184431
theorem B1874153 : Blo 778337 1874153 := bstep (se 2 (by rfl) ⟨702807, by rfl⟩ : syracuseStep 1874153 = 1405615) B1405615
theorem B1317127 : Blo 778337 1317127 := bstep (se 1 (by rfl) ⟨987845, by rfl⟩ : syracuseStep 1317127 = 1975691) B1975691
theorem B1317161 : Blo 778337 1317161 := bstep (se 2 (by rfl) ⟨493935, by rfl⟩ : syracuseStep 1317161 = 987871) B987871
theorem B2627963 : Blo 778337 2627963 := bstep (se 1 (by rfl) ⟨1970972, by rfl⟩ : syracuseStep 2627963 = 3941945) B3941945
theorem B2628233 : Blo 778337 2628233 := bstep (se 2 (by rfl) ⟨985587, by rfl⟩ : syracuseStep 2628233 = 1971175) B1971175
theorem B1252255 : Blo 778337 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B8002475 : Blo 778337 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B2104271 : Blo 778337 2104271 := bstep (se 1 (by rfl) ⟨1578203, by rfl⟩ : syracuseStep 2104271 = 3156407) B3156407
theorem B2399357 : Blo 778337 2399357 := bstep (se 3 (by rfl) ⟨449879, by rfl⟩ : syracuseStep 2399357 = 899759) B899759
theorem B5938433 : Blo 778337 5938433 := bstep (se 2 (by rfl) ⟨2226912, by rfl⟩ : syracuseStep 5938433 = 4453825) B4453825
theorem B1318153 : Blo 778337 1318153 := bstep (se 2 (by rfl) ⟨494307, by rfl⟩ : syracuseStep 1318153 = 988615) B988615
theorem B9510479 : Blo 778337 9510479 := bstep (se 1 (by rfl) ⟨7132859, by rfl⟩ : syracuseStep 9510479 = 14265719) B14265719
theorem B2629367 : Blo 778337 2629367 := bstep (se 1 (by rfl) ⟨1972025, by rfl⟩ : syracuseStep 2629367 = 3944051) B3944051
theorem B1318727 : Blo 778337 1318727 := bstep (se 1 (by rfl) ⟨989045, by rfl⟩ : syracuseStep 1318727 = 1978091) B1978091
theorem B1482619 : Blo 778337 1482619 := bstep (se 1 (by rfl) ⟨1111964, by rfl⟩ : syracuseStep 1482619 = 2223929) B2223929
theorem B3940487 : Blo 778337 3940487 := bstep (se 1 (by rfl) ⟨2955365, by rfl⟩ : syracuseStep 3940487 = 5910731) B5910731
theorem B1483105 : Blo 778337 1483105 := bstep (se 2 (by rfl) ⟨556164, by rfl⟩ : syracuseStep 1483105 = 1112329) B1112329
theorem B5611963 : Blo 778337 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B1319375 : Blo 778337 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B162046433 : Blo 778337 162046433 := bstep (se 2 (by rfl) ⟨60767412, by rfl⟩ : syracuseStep 162046433 = 121534825) B121534825
theorem B3940973 : Blo 778337 3940973 := bstep (se 3 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 3940973 = 1477865) B1477865
theorem B2630447 : Blo 778337 2630447 := bstep (se 1 (by rfl) ⟨1972835, by rfl⟩ : syracuseStep 2630447 = 3945671) B3945671
theorem B2958191 : Blo 778337 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B2630555 : Blo 778337 2630555 := bstep (se 1 (by rfl) ⟨1972916, by rfl⟩ : syracuseStep 2630555 = 3945833) B3945833
theorem B1320043 : Blo 778337 1320043 := bstep (se 1 (by rfl) ⟨990032, by rfl⟩ : syracuseStep 1320043 = 1980065) B1980065
theorem B8430749 : Blo 778337 8430749 := bstep (se 3 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 8430749 = 3161531) B3161531
theorem B2499947 : Blo 778337 2499947 := bstep (se 1 (by rfl) ⟨1874960, by rfl⟩ : syracuseStep 2499947 = 3749921) B3749921
theorem B1877671 : Blo 778337 1877671 := bstep (se 1 (by rfl) ⟨1408253, by rfl⟩ : syracuseStep 1877671 = 2816507) B2816507
theorem B3942107 : Blo 778337 3942107 := bstep (se 1 (by rfl) ⟨2956580, by rfl⟩ : syracuseStep 3942107 = 5913161) B5913161
theorem B1582811 : Blo 778337 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B2631689 : Blo 778337 2631689 := bstep (se 2 (by rfl) ⟨986883, by rfl⟩ : syracuseStep 2631689 = 1973767) B1973767
theorem B4433939 : Blo 778337 4433939 := bstep (se 1 (by rfl) ⟨3325454, by rfl⟩ : syracuseStep 4433939 = 6650909) B6650909
theorem B4991129 : Blo 778337 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B164702423 : Blo 778337 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B1976633 : Blo 778337 1976633 := bstep (se 2 (by rfl) ⟨741237, by rfl⟩ : syracuseStep 1976633 = 1482475) B1482475
theorem B1649183 : Blo 778337 1649183 := bstep (se 1 (by rfl) ⟨1236887, by rfl⟩ : syracuseStep 1649183 = 2473775) B2473775
theorem B83143361 : Blo 778337 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B2960347 : Blo 778337 2960347 := bstep (se 1 (by rfl) ⟨2220260, by rfl⟩ : syracuseStep 2960347 = 4440521) B4440521
theorem B3943403 : Blo 778337 3943403 := bstep (se 1 (by rfl) ⟨2957552, by rfl⟩ : syracuseStep 3943403 = 5915105) B5915105
theorem B2632985 : Blo 778337 2632985 := bstep (se 2 (by rfl) ⟨987369, by rfl⟩ : syracuseStep 2632985 = 1974739) B1974739
theorem B2633039 : Blo 778337 2633039 := bstep (se 1 (by rfl) ⟨1974779, by rfl⟩ : syracuseStep 2633039 = 3949559) B3949559
theorem B1584463 : Blo 778337 1584463 := bstep (se 1 (by rfl) ⟨1188347, by rfl⟩ : syracuseStep 1584463 = 2376695) B2376695
theorem B43232777 : Blo 778337 43232777 := bstep (se 2 (by rfl) ⟨16212291, by rfl⟩ : syracuseStep 43232777 = 32424583) B32424583
theorem B1977929 : Blo 778337 1977929 := bstep (se 2 (by rfl) ⟨741723, by rfl⟩ : syracuseStep 1977929 = 1483447) B1483447
theorem B3944375 : Blo 778337 3944375 := bstep (se 1 (by rfl) ⟨2958281, by rfl⟩ : syracuseStep 3944375 = 5916563) B5916563
theorem B2109407 : Blo 778337 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B22491107 : Blo 778337 22491107 := bstep (se 1 (by rfl) ⟨16868330, by rfl⟩ : syracuseStep 22491107 = 33736661) B33736661
theorem B12660785 : Blo 778337 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B15217145 : Blo 778337 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B2634335 : Blo 778337 2634335 := bstep (se 1 (by rfl) ⟨1975751, by rfl⟩ : syracuseStep 2634335 = 3951503) B3951503
theorem B1979387 : Blo 778337 1979387 := bstep (se 1 (by rfl) ⟨1484540, by rfl⟩ : syracuseStep 1979387 = 2969081) B2969081
theorem B1979873 : Blo 778337 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B12006893 : Blo 778337 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B4994561 : Blo 778337 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B4994743 : Blo 778337 4994743 := bstep (se 1 (by rfl) ⟨3746057, by rfl⟩ : syracuseStep 4994743 = 7492115) B7492115
theorem B28456697 : Blo 778337 28456697 := bstep (se 2 (by rfl) ⟨10671261, by rfl⟩ : syracuseStep 28456697 = 21342523) B21342523
theorem B2635577 : Blo 778337 2635577 := bstep (se 2 (by rfl) ⟨988341, by rfl⟩ : syracuseStep 2635577 = 1976683) B1976683
theorem B2963263 : Blo 778337 2963263 := bstep (se 1 (by rfl) ⟨2222447, by rfl⟩ : syracuseStep 2963263 = 4444895) B4444895
theorem B2635739 : Blo 778337 2635739 := bstep (se 1 (by rfl) ⟨1976804, by rfl⟩ : syracuseStep 2635739 = 3953609) B3953609
theorem B10008805 : Blo 778337 10008805 := bstep (se 4 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 10008805 = 1876651) B1876651
theorem B1751273 : Blo 778337 1751273 := bstep (se 2 (by rfl) ⟨656727, by rfl⟩ : syracuseStep 1751273 = 1313455) B1313455
theorem B2636009 : Blo 778337 2636009 := bstep (se 2 (by rfl) ⟨988503, by rfl⟩ : syracuseStep 2636009 = 1977007) B1977007
theorem B3750151 : Blo 778337 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B2636441 : Blo 778337 2636441 := bstep (se 2 (by rfl) ⟨988665, by rfl⟩ : syracuseStep 2636441 = 1977331) B1977331
theorem B1752551 : Blo 778337 1752551 := bstep (se 1 (by rfl) ⟨1314413, by rfl⟩ : syracuseStep 1752551 = 2628827) B2628827
theorem B14991065 : Blo 778337 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B49397621 : Blo 778337 49397621 := bstep (se 5 (by rfl) ⟨2315513, by rfl⟩ : syracuseStep 49397621 = 4631027) B4631027
theorem B1753127 : Blo 778337 1753127 := bstep (se 1 (by rfl) ⟨1314845, by rfl⟩ : syracuseStep 1753127 = 2629691) B2629691
theorem B4440203 : Blo 778337 4440203 := bstep (se 1 (by rfl) ⟨3330152, by rfl⟩ : syracuseStep 4440203 = 6660305) B6660305
theorem B1753307 : Blo 778337 1753307 := bstep (se 1 (by rfl) ⟨1314980, by rfl⟩ : syracuseStep 1753307 = 2629961) B2629961
theorem B2965967 : Blo 778337 2965967 := bstep (se 1 (by rfl) ⟨2224475, by rfl⟩ : syracuseStep 2965967 = 4448951) B4448951
theorem B1753577 : Blo 778337 1753577 := bstep (se 2 (by rfl) ⟨657591, by rfl⟩ : syracuseStep 1753577 = 1315183) B1315183
theorem B2638331 : Blo 778337 2638331 := bstep (se 1 (by rfl) ⟨1978748, by rfl⟩ : syracuseStep 2638331 = 3957497) B3957497
theorem B1753865 : Blo 778337 1753865 := bstep (se 2 (by rfl) ⟨657699, by rfl⟩ : syracuseStep 1753865 = 1315399) B1315399
theorem B2638601 : Blo 778337 2638601 := bstep (se 2 (by rfl) ⟨989475, by rfl⟩ : syracuseStep 2638601 = 1978951) B1978951
theorem B2966483 : Blo 778337 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B5620727 : Blo 778337 5620727 := bstep (se 1 (by rfl) ⟨4215545, by rfl⟩ : syracuseStep 5620727 = 8431091) B8431091
theorem B1754441 : Blo 778337 1754441 := bstep (se 2 (by rfl) ⟨657915, by rfl⟩ : syracuseStep 1754441 = 1315831) B1315831
theorem B2639357 : Blo 778337 2639357 := bstep (se 3 (by rfl) ⟨494879, by rfl⟩ : syracuseStep 2639357 = 989759) B989759
theorem B2967151 : Blo 778337 2967151 := bstep (se 1 (by rfl) ⟨2225363, by rfl⟩ : syracuseStep 2967151 = 4450727) B4450727
theorem B2967425 : Blo 778337 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B1755431 : Blo 778337 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B2640167 : Blo 778337 2640167 := bstep (se 1 (by rfl) ⟨1980125, by rfl⟩ : syracuseStep 2640167 = 3960251) B3960251
theorem B1755449 : Blo 778337 1755449 := bstep (se 2 (by rfl) ⟨658293, by rfl⟩ : syracuseStep 1755449 = 1316587) B1316587
theorem B2705825 : Blo 778337 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B5917535 : Blo 778337 5917535 := bstep (se 1 (by rfl) ⟨4438151, by rfl⟩ : syracuseStep 5917535 = 8876303) B8876303
theorem B2968609 : Blo 778337 2968609 := bstep (se 2 (by rfl) ⟨1113228, by rfl⟩ : syracuseStep 2968609 = 2226457) B2226457
theorem B937183 : Blo 778337 937183 := bstep (se 1 (by rfl) ⟨702887, by rfl⟩ : syracuseStep 937183 = 1405775) B1405775
theorem B1756745 : Blo 778337 1756745 := bstep (se 2 (by rfl) ⟨658779, by rfl⟩ : syracuseStep 1756745 = 1317559) B1317559
theorem B3329693 : Blo 778337 3329693 := bstep (se 3 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 3329693 = 1248635) B1248635
theorem B2969581 : Blo 778337 2969581 := bstep (se 3 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 2969581 = 1113593) B1113593
theorem B380063755 : Blo 778337 380063755 := bstep (se 1 (by rfl) ⟨285047816, by rfl⟩ : syracuseStep 380063755 = 570095633) B570095633
theorem B1167647 : Blo 778337 1167647 := bstep (se 1 (by rfl) ⟨875735, by rfl⟩ : syracuseStep 1167647 = 1751471) B1751471
theorem B1167671 : Blo 778337 1167671 := bstep (se 1 (by rfl) ⟨875753, by rfl⟩ : syracuseStep 1167671 = 1751507) B1751507
theorem B2806127 : Blo 778337 2806127 := bstep (se 1 (by rfl) ⟨2104595, by rfl⟩ : syracuseStep 2806127 = 4209191) B4209191
theorem B1167743 : Blo 778337 1167743 := bstep (se 1 (by rfl) ⟨875807, by rfl⟩ : syracuseStep 1167743 = 1751615) B1751615
theorem B1167815 : Blo 778337 1167815 := bstep (se 1 (by rfl) ⟨875861, by rfl⟩ : syracuseStep 1167815 = 1751723) B1751723
theorem B9982561 : Blo 778337 9982561 := bstep (se 2 (by rfl) ⟨3743460, by rfl⟩ : syracuseStep 9982561 = 7486921) B7486921
theorem B1168169 : Blo 778337 1168169 := bstep (se 2 (by rfl) ⟨438063, by rfl⟩ : syracuseStep 1168169 = 876127) B876127
theorem B1168175 : Blo 778337 1168175 := bstep (se 1 (by rfl) ⟨876131, by rfl⟩ : syracuseStep 1168175 = 1752263) B1752263
theorem B2806589 : Blo 778337 2806589 := bstep (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) B1052471
theorem B1168295 : Blo 778337 1168295 := bstep (se 1 (by rfl) ⟨876221, by rfl⟩ : syracuseStep 1168295 = 1752443) B1752443
theorem B1168379 : Blo 778337 1168379 := bstep (se 1 (by rfl) ⟨876284, by rfl⟩ : syracuseStep 1168379 = 1752569) B1752569
theorem B1758203 : Blo 778337 1758203 := bstep (se 1 (by rfl) ⟨1318652, by rfl⟩ : syracuseStep 1758203 = 2637305) B2637305
theorem B1168439 : Blo 778337 1168439 := bstep (se 1 (by rfl) ⟨876329, by rfl⟩ : syracuseStep 1168439 = 1752659) B1752659
theorem B3953771 : Blo 778337 3953771 := bstep (se 1 (by rfl) ⟨2965328, by rfl⟩ : syracuseStep 3953771 = 5930657) B5930657
theorem B1168559 : Blo 778337 1168559 := bstep (se 1 (by rfl) ⟨876419, by rfl⟩ : syracuseStep 1168559 = 1752839) B1752839
theorem B1758383 : Blo 778337 1758383 := bstep (se 1 (by rfl) ⟨1318787, by rfl⟩ : syracuseStep 1758383 = 2637575) B2637575
theorem B1758419 : Blo 778337 1758419 := bstep (se 1 (by rfl) ⟨1318814, by rfl⟩ : syracuseStep 1758419 = 2637629) B2637629
theorem B1758689 : Blo 778337 1758689 := bstep (se 2 (by rfl) ⟨659508, by rfl⟩ : syracuseStep 1758689 = 1319017) B1319017
theorem B1168967 : Blo 778337 1168967 := bstep (se 1 (by rfl) ⟨876725, by rfl⟩ : syracuseStep 1168967 = 1753451) B1753451
theorem B1463879 : Blo 778337 1463879 := bstep (se 1 (by rfl) ⟨1097909, by rfl⟩ : syracuseStep 1463879 = 2195819) B2195819
theorem B1169063 : Blo 778337 1169063 := bstep (se 1 (by rfl) ⟨876797, by rfl⟩ : syracuseStep 1169063 = 1753595) B1753595
theorem B1169147 : Blo 778337 1169147 := bstep (se 1 (by rfl) ⟨876860, by rfl⟩ : syracuseStep 1169147 = 1753721) B1753721
theorem B1169183 : Blo 778337 1169183 := bstep (se 1 (by rfl) ⟨876887, by rfl⟩ : syracuseStep 1169183 = 1753775) B1753775
theorem B1169231 : Blo 778337 1169231 := bstep (se 1 (by rfl) ⟨876923, by rfl⟩ : syracuseStep 1169231 = 1753847) B1753847
theorem B1169351 : Blo 778337 1169351 := bstep (se 1 (by rfl) ⟨877013, by rfl⟩ : syracuseStep 1169351 = 1754027) B1754027
theorem B10279111 : Blo 778337 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B1169705 : Blo 778337 1169705 := bstep (se 2 (by rfl) ⟨438639, by rfl⟩ : syracuseStep 1169705 = 877279) B877279
theorem B1169711 : Blo 778337 1169711 := bstep (se 1 (by rfl) ⟨877283, by rfl⟩ : syracuseStep 1169711 = 1754567) B1754567
theorem B3955067 : Blo 778337 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B1169951 : Blo 778337 1169951 := bstep (se 1 (by rfl) ⟨877463, by rfl⟩ : syracuseStep 1169951 = 1754927) B1754927
theorem B2218553 : Blo 778337 2218553 := bstep (se 2 (by rfl) ⟨831957, by rfl⟩ : syracuseStep 2218553 = 1663915) B1663915
theorem B4446809 : Blo 778337 4446809 := bstep (se 2 (by rfl) ⟨1667553, by rfl⟩ : syracuseStep 4446809 = 3335107) B3335107
theorem B1170335 : Blo 778337 1170335 := bstep (se 1 (by rfl) ⟨877751, by rfl⟩ : syracuseStep 1170335 = 1755503) B1755503
theorem B1170383 : Blo 778337 1170383 := bstep (se 1 (by rfl) ⟨877787, by rfl⟩ : syracuseStep 1170383 = 1755575) B1755575
theorem B8444897 : Blo 778337 8444897 := bstep (se 2 (by rfl) ⟨3166836, by rfl⟩ : syracuseStep 8444897 = 6333673) B6333673
theorem B1170473 : Blo 778337 1170473 := bstep (se 2 (by rfl) ⟨438927, by rfl⟩ : syracuseStep 1170473 = 877855) B877855
theorem B1170479 : Blo 778337 1170479 := bstep (se 1 (by rfl) ⟨877859, by rfl⟩ : syracuseStep 1170479 = 1755719) B1755719
theorem B1170503 : Blo 778337 1170503 := bstep (se 1 (by rfl) ⟨877877, by rfl⟩ : syracuseStep 1170503 = 1755755) B1755755
theorem B1170767 : Blo 778337 1170767 := bstep (se 1 (by rfl) ⟨878075, by rfl⟩ : syracuseStep 1170767 = 1756151) B1756151
theorem B1170857 : Blo 778337 1170857 := bstep (se 2 (by rfl) ⟨439071, by rfl⟩ : syracuseStep 1170857 = 878143) B878143
theorem B1171007 : Blo 778337 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B1171271 : Blo 778337 1171271 := bstep (se 1 (by rfl) ⟨878453, by rfl⟩ : syracuseStep 1171271 = 1756907) B1756907
theorem B1171355 : Blo 778337 1171355 := bstep (se 1 (by rfl) ⟨878516, by rfl⟩ : syracuseStep 1171355 = 1757033) B1757033
theorem B778471 : Blo 778337 778471 := bstep (se 1 (by rfl) ⟨583853, by rfl⟩ : syracuseStep 778471 = 1167707) B1167707
theorem B876775 : Blo 778337 876775 := bstep (se 1 (by rfl) ⟨657581, by rfl⟩ : syracuseStep 876775 = 1315163) B1315163
theorem B3334391 : Blo 778337 3334391 := bstep (se 1 (by rfl) ⟨2500793, by rfl⟩ : syracuseStep 3334391 = 5001587) B5001587
theorem B3563873 : Blo 778337 3563873 := bstep (se 2 (by rfl) ⟨1336452, by rfl⟩ : syracuseStep 3563873 = 2672905) B2672905
theorem B778623 : Blo 778337 778623 := bstep (se 1 (by rfl) ⟨583967, by rfl⟩ : syracuseStep 778623 = 1167935) B1167935
theorem B1204607 : Blo 778337 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B778703 : Blo 778337 778703 := bstep (se 1 (by rfl) ⟨584027, by rfl⟩ : syracuseStep 778703 = 1168055) B1168055
theorem B1171919 : Blo 778337 1171919 := bstep (se 1 (by rfl) ⟨878939, by rfl⟩ : syracuseStep 1171919 = 1757879) B1757879
theorem B1171961 : Blo 778337 1171961 := bstep (se 2 (by rfl) ⟨439485, by rfl⟩ : syracuseStep 1171961 = 878971) B878971
theorem B1172063 : Blo 778337 1172063 := bstep (se 1 (by rfl) ⟨879047, by rfl⟩ : syracuseStep 1172063 = 1758095) B1758095
theorem B778855 : Blo 778337 778855 := bstep (se 1 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 778855 = 1168283) B1168283
theorem B3334765 : Blo 778337 3334765 := bstep (se 3 (by rfl) ⟨625268, by rfl⟩ : syracuseStep 3334765 = 1250537) B1250537
theorem B4514413 : Blo 778337 4514413 := bstep (se 3 (by rfl) ⟨846452, by rfl⟩ : syracuseStep 4514413 = 1692905) B1692905
theorem B4809415 : Blo 778337 4809415 := bstep (se 1 (by rfl) ⟨3607061, by rfl⟩ : syracuseStep 4809415 = 7214123) B7214123
theorem B2220797 : Blo 778337 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B1663753 : Blo 778337 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B779119 : Blo 778337 779119 := bstep (se 1 (by rfl) ⟨584339, by rfl⟩ : syracuseStep 779119 = 1168679) B1168679
theorem B877423 : Blo 778337 877423 := bstep (se 1 (by rfl) ⟨658067, by rfl⟩ : syracuseStep 877423 = 1316135) B1316135
theorem B20243351 : Blo 778337 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B3957659 : Blo 778337 3957659 := bstep (se 1 (by rfl) ⟨2968244, by rfl⟩ : syracuseStep 3957659 = 5936489) B5936489
theorem B779175 : Blo 778337 779175 := bstep (se 1 (by rfl) ⟨584381, by rfl⟩ : syracuseStep 779175 = 1168763) B1168763
theorem B779259 : Blo 778337 779259 := bstep (se 1 (by rfl) ⟨584444, by rfl⟩ : syracuseStep 779259 = 1168889) B1168889
theorem B779327 : Blo 778337 779327 := bstep (se 1 (by rfl) ⟨584495, by rfl⟩ : syracuseStep 779327 = 1168991) B1168991
theorem B1172543 : Blo 778337 1172543 := bstep (se 1 (by rfl) ⟨879407, by rfl⟩ : syracuseStep 1172543 = 1758815) B1758815
theorem B1172585 : Blo 778337 1172585 := bstep (se 2 (by rfl) ⟨439719, by rfl⟩ : syracuseStep 1172585 = 879439) B879439
theorem B779471 : Blo 778337 779471 := bstep (se 1 (by rfl) ⟨584603, by rfl⟩ : syracuseStep 779471 = 1169207) B1169207
theorem B1172687 : Blo 778337 1172687 := bstep (se 1 (by rfl) ⟨879515, by rfl⟩ : syracuseStep 1172687 = 1759031) B1759031
theorem B13362569 : Blo 778337 13362569 := bstep (se 2 (by rfl) ⟨5010963, by rfl⟩ : syracuseStep 13362569 = 10021927) B10021927
theorem B779675 : Blo 778337 779675 := bstep (se 1 (by rfl) ⟨584756, by rfl⟩ : syracuseStep 779675 = 1169513) B1169513
theorem B1172891 : Blo 778337 1172891 := bstep (se 1 (by rfl) ⟨879668, by rfl⟩ : syracuseStep 1172891 = 1759337) B1759337
theorem B5006863 : Blo 778337 5006863 := bstep (se 1 (by rfl) ⟨3755147, by rfl⟩ : syracuseStep 5006863 = 7510295) B7510295
theorem B779887 : Blo 778337 779887 := bstep (se 1 (by rfl) ⟨584915, by rfl⟩ : syracuseStep 779887 = 1169831) B1169831
theorem B1173113 : Blo 778337 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B779943 : Blo 778337 779943 := bstep (se 1 (by rfl) ⟨584957, by rfl⟩ : syracuseStep 779943 = 1169915) B1169915
theorem B4449977 : Blo 778337 4449977 := bstep (se 2 (by rfl) ⟨1668741, by rfl⟩ : syracuseStep 4449977 = 3337483) B3337483
theorem B1173215 : Blo 778337 1173215 := bstep (se 1 (by rfl) ⟨879911, by rfl⟩ : syracuseStep 1173215 = 1759823) B1759823
theorem B780027 : Blo 778337 780027 := bstep (se 1 (by rfl) ⟨585020, by rfl⟩ : syracuseStep 780027 = 1170041) B1170041
theorem B780063 : Blo 778337 780063 := bstep (se 1 (by rfl) ⟨585047, by rfl⟩ : syracuseStep 780063 = 1170095) B1170095
theorem B780095 : Blo 778337 780095 := bstep (se 1 (by rfl) ⟨585071, by rfl⟩ : syracuseStep 780095 = 1170143) B1170143
theorem B1173311 : Blo 778337 1173311 := bstep (se 1 (by rfl) ⟨879983, by rfl⟩ : syracuseStep 1173311 = 1759967) B1759967
theorem B5629783 : Blo 778337 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B1173479 : Blo 778337 1173479 := bstep (se 1 (by rfl) ⟨880109, by rfl⟩ : syracuseStep 1173479 = 1760219) B1760219
theorem B780271 : Blo 778337 780271 := bstep (se 1 (by rfl) ⟨585203, by rfl⟩ : syracuseStep 780271 = 1170407) B1170407
theorem B878575 : Blo 778337 878575 := bstep (se 1 (by rfl) ⟨658931, by rfl⟩ : syracuseStep 878575 = 1317863) B1317863
theorem B1173497 : Blo 778337 1173497 := bstep (se 2 (by rfl) ⟨440061, by rfl⟩ : syracuseStep 1173497 = 880123) B880123
theorem B16050257 : Blo 778337 16050257 := bstep (se 2 (by rfl) ⟨6018846, by rfl⟩ : syracuseStep 16050257 = 12037693) B12037693
theorem B780443 : Blo 778337 780443 := bstep (se 1 (by rfl) ⟨585332, by rfl⟩ : syracuseStep 780443 = 1170665) B1170665
theorem B780479 : Blo 778337 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B780591 : Blo 778337 780591 := bstep (se 1 (by rfl) ⟨585443, by rfl⟩ : syracuseStep 780591 = 1170887) B1170887
theorem B5794105 : Blo 778337 5794105 := bstep (se 2 (by rfl) ⟨2172789, by rfl⟩ : syracuseStep 5794105 = 4345579) B4345579
theorem B780827 : Blo 778337 780827 := bstep (se 1 (by rfl) ⟨585620, by rfl⟩ : syracuseStep 780827 = 1171241) B1171241
theorem B780831 : Blo 778337 780831 := bstep (se 1 (by rfl) ⟨585623, by rfl⟩ : syracuseStep 780831 = 1171247) B1171247
theorem B14248487 : Blo 778337 14248487 := bstep (se 1 (by rfl) ⟨10686365, by rfl⟩ : syracuseStep 14248487 = 21372731) B21372731
theorem B5073515 : Blo 778337 5073515 := bstep (se 1 (by rfl) ⟨3805136, by rfl⟩ : syracuseStep 5073515 = 7610273) B7610273
theorem B9988919 : Blo 778337 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B2222903 : Blo 778337 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B781147 : Blo 778337 781147 := bstep (se 1 (by rfl) ⟨585860, by rfl⟩ : syracuseStep 781147 = 1171721) B1171721
theorem B781215 : Blo 778337 781215 := bstep (se 1 (by rfl) ⟨585911, by rfl⟩ : syracuseStep 781215 = 1171823) B1171823
theorem B16903187 : Blo 778337 16903187 := bstep (se 1 (by rfl) ⟨12677390, by rfl⟩ : syracuseStep 16903187 = 25354781) B25354781
theorem B2812961 : Blo 778337 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B781359 : Blo 778337 781359 := bstep (se 1 (by rfl) ⟨586019, by rfl⟩ : syracuseStep 781359 = 1172039) B1172039
theorem B781383 : Blo 778337 781383 := bstep (se 1 (by rfl) ⟨586037, by rfl⟩ : syracuseStep 781383 = 1172075) B1172075
theorem B4746383 : Blo 778337 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B11234483 : Blo 778337 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B781535 : Blo 778337 781535 := bstep (se 1 (by rfl) ⟨586151, by rfl⟩ : syracuseStep 781535 = 1172303) B1172303
theorem B11234537 : Blo 778337 11234537 := bstep (se 2 (by rfl) ⟨4212951, by rfl⟩ : syracuseStep 11234537 = 8425903) B8425903
theorem B10022291 : Blo 778337 10022291 := bstep (se 1 (by rfl) ⟨7516718, by rfl⟩ : syracuseStep 10022291 = 15033437) B15033437
theorem B1666487 : Blo 778337 1666487 := bstep (se 1 (by rfl) ⟨1249865, by rfl⟩ : syracuseStep 1666487 = 2499731) B2499731
theorem B1404391 : Blo 778337 1404391 := bstep (se 1 (by rfl) ⟨1053293, by rfl⟩ : syracuseStep 1404391 = 2106587) B2106587
theorem B781799 : Blo 778337 781799 := bstep (se 1 (by rfl) ⟨586349, by rfl⟩ : syracuseStep 781799 = 1172699) B1172699
theorem B781915 : Blo 778337 781915 := bstep (se 1 (by rfl) ⟨586436, by rfl⟩ : syracuseStep 781915 = 1172873) B1172873
theorem B782151 : Blo 778337 782151 := bstep (se 1 (by rfl) ⟨586613, by rfl⟩ : syracuseStep 782151 = 1173227) B1173227
theorem B782303 : Blo 778337 782303 := bstep (se 1 (by rfl) ⟨586727, by rfl⟩ : syracuseStep 782303 = 1173455) B1173455
theorem B1405601 : Blo 778337 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B1110763 : Blo 778337 1110763 := bstep (se 1 (by rfl) ⟨833072, by rfl⟩ : syracuseStep 1110763 = 1666145) B1666145
theorem B1668203 : Blo 778337 1668203 := bstep (se 1 (by rfl) ⟨1251152, by rfl⟩ : syracuseStep 1668203 = 2502305) B2502305
theorem B1668271 : Blo 778337 1668271 := bstep (se 1 (by rfl) ⟨1251203, by rfl⟩ : syracuseStep 1668271 = 2502407) B2502407
theorem B6354227 : Blo 778337 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B4454099 : Blo 778337 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B5634107 : Blo 778337 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B9468343 : Blo 778337 9468343 := bstep (se 1 (by rfl) ⟨7101257, by rfl⟩ : syracuseStep 9468343 = 14202515) B14202515
theorem B10680893 : Blo 778337 10680893 := bstep (se 3 (by rfl) ⟨2002667, by rfl⟩ : syracuseStep 10680893 = 4005335) B4005335
theorem B2226845 : Blo 778337 2226845 := bstep (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) B835067
theorem B4455101 : Blo 778337 4455101 := bstep (se 3 (by rfl) ⟨835331, by rfl⟩ : syracuseStep 4455101 = 1670663) B1670663
theorem B1112887 : Blo 778337 1112887 := bstep (se 1 (by rfl) ⟨834665, by rfl⟩ : syracuseStep 1112887 = 1669331) B1669331
theorem B2227027 : Blo 778337 2227027 := bstep (se 1 (by rfl) ⟨1670270, by rfl⟩ : syracuseStep 2227027 = 3340541) B3340541
theorem B1113707 : Blo 778337 1113707 := bstep (se 1 (by rfl) ⟨835280, by rfl⟩ : syracuseStep 1113707 = 1670561) B1670561
theorem B40468385 : Blo 778337 40468385 := bstep (se 2 (by rfl) ⟨15175644, by rfl⟩ : syracuseStep 40468385 = 30351289) B30351289
theorem B57672769 : Blo 778337 57672769 := bstep (se 2 (by rfl) ⟨21627288, by rfl⟩ : syracuseStep 57672769 = 43254577) B43254577
theorem B1803883 : Blo 778337 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B13305707 : Blo 778337 13305707 := bstep (se 1 (by rfl) ⟨9979280, by rfl⟩ : syracuseStep 13305707 = 19958561) B19958561
theorem B8128457 : Blo 778337 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B7506377 : Blo 778337 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B1870751 : Blo 778337 1870751 := bstep (se 1 (by rfl) ⟨1403063, by rfl⟩ : syracuseStep 1870751 = 2806127) B2806127
theorem B1313705 : Blo 778337 1313705 := bstep (se 2 (by rfl) ⟨492639, by rfl⟩ : syracuseStep 1313705 = 985279) B985279
theorem B1871059 : Blo 778337 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B1314407 : Blo 778337 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B1052827 : Blo 778337 1052827 := bstep (se 1 (by rfl) ⟨789620, by rfl⟩ : syracuseStep 1052827 = 1579241) B1579241
theorem B1249435 : Blo 778337 1249435 := bstep (se 1 (by rfl) ⟨937076, by rfl⟩ : syracuseStep 1249435 = 1874153) B1874153
theorem B3903677 : Blo 778337 3903677 := bstep (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) B1463879
theorem B1249577 : Blo 778337 1249577 := bstep (se 2 (by rfl) ⟨468591, by rfl⟩ : syracuseStep 1249577 = 937183) B937183
theorem B1479035 : Blo 778337 1479035 := bstep (se 1 (by rfl) ⟨1109276, by rfl⟩ : syracuseStep 1479035 = 2218553) B2218553
theorem B1872521 : Blo 778337 1872521 := bstep (se 2 (by rfl) ⟨702195, by rfl⟩ : syracuseStep 1872521 = 1404391) B1404391
theorem B2626991 : Blo 778337 2626991 := bstep (se 1 (by rfl) ⟨1970243, by rfl⟩ : syracuseStep 2626991 = 3940487) B3940487
theorem B3806929 : Blo 778337 3806929 := bstep (se 2 (by rfl) ⟨1427598, by rfl⟩ : syracuseStep 3806929 = 2855197) B2855197
theorem B2627315 : Blo 778337 2627315 := bstep (se 1 (by rfl) ⟨1970486, by rfl⟩ : syracuseStep 2627315 = 3940973) B3940973
theorem B1480531 : Blo 778337 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B1972127 : Blo 778337 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B8001641 : Blo 778337 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B13310081 : Blo 778337 13310081 := bstep (se 2 (by rfl) ⟨4991280, by rfl⟩ : syracuseStep 13310081 = 9982561) B9982561
theorem B1481017 : Blo 778337 1481017 := bstep (se 2 (by rfl) ⟨555381, by rfl⟩ : syracuseStep 1481017 = 1110763) B1110763
theorem B2628071 : Blo 778337 2628071 := bstep (se 1 (by rfl) ⟨1971053, by rfl⟩ : syracuseStep 2628071 = 3942107) B3942107
theorem B1055207 : Blo 778337 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B2955959 : Blo 778337 2955959 := bstep (se 1 (by rfl) ⟨2216969, by rfl⟩ : syracuseStep 2955959 = 4433939) B4433939
theorem B1317755 : Blo 778337 1317755 := bstep (se 1 (by rfl) ⟨988316, by rfl⟩ : syracuseStep 1317755 = 1976633) B1976633
theorem B3382343 : Blo 778337 3382343 := bstep (se 1 (by rfl) ⟨2536757, by rfl⟩ : syracuseStep 3382343 = 5073515) B5073515
theorem B6659279 : Blo 778337 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B2628935 : Blo 778337 2628935 := bstep (se 1 (by rfl) ⟨1971701, by rfl⟩ : syracuseStep 2628935 = 3943403) B3943403
theorem B1875307 : Blo 778337 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B6659657 : Blo 778337 6659657 := bstep (se 2 (by rfl) ⟨2497371, by rfl⟩ : syracuseStep 6659657 = 4994743) B4994743
theorem B1318619 : Blo 778337 1318619 := bstep (se 1 (by rfl) ⟨988964, by rfl⟩ : syracuseStep 1318619 = 1977929) B1977929
theorem B2629583 : Blo 778337 2629583 := bstep (se 1 (by rfl) ⟨1972187, by rfl⟩ : syracuseStep 2629583 = 3944375) B3944375
theorem B1318889 : Blo 778337 1318889 := bstep (se 2 (by rfl) ⟨494583, by rfl⟩ : syracuseStep 1318889 = 989167) B989167
theorem B13705481 : Blo 778337 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B13345073 : Blo 778337 13345073 := bstep (se 2 (by rfl) ⟨5004402, by rfl⟩ : syracuseStep 13345073 = 10008805) B10008805
theorem B12624457 : Blo 778337 12624457 := bstep (se 2 (by rfl) ⟨4734171, by rfl⟩ : syracuseStep 12624457 = 9468343) B9468343
theorem B1319591 : Blo 778337 1319591 := bstep (se 1 (by rfl) ⟨989693, by rfl⟩ : syracuseStep 1319591 = 1979387) B1979387
theorem B4236151 : Blo 778337 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B1319915 : Blo 778337 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B8004595 : Blo 778337 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B1483849 : Blo 778337 1483849 := bstep (se 2 (by rfl) ⟨556443, by rfl⟩ : syracuseStep 1483849 = 1112887) B1112887
theorem B7120595 : Blo 778337 7120595 := bstep (se 1 (by rfl) ⟨5340446, by rfl⟩ : syracuseStep 7120595 = 10680893) B10680893
theorem B1484563 : Blo 778337 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B1976825 : Blo 778337 1976825 := bstep (se 2 (by rfl) ⟨741309, by rfl⟩ : syracuseStep 1976825 = 1482619) B1482619
theorem B26978923 : Blo 778337 26978923 := bstep (se 1 (by rfl) ⟨20234192, by rfl⟩ : syracuseStep 26978923 = 40468385) B40468385
theorem B2960135 : Blo 778337 2960135 := bstep (se 1 (by rfl) ⟨2220101, by rfl⟩ : syracuseStep 2960135 = 4440203) B4440203
theorem B1977311 : Blo 778337 1977311 := bstep (se 1 (by rfl) ⟨1482983, by rfl⟩ : syracuseStep 1977311 = 2965967) B2965967
theorem B1977473 : Blo 778337 1977473 := bstep (se 2 (by rfl) ⟨741552, by rfl⟩ : syracuseStep 1977473 = 1483105) B1483105
theorem B7482617 : Blo 778337 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B1977655 : Blo 778337 1977655 := bstep (se 1 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 1977655 = 2966483) B2966483
theorem B3747151 : Blo 778337 3747151 := bstep (se 1 (by rfl) ⟨2810363, by rfl⟩ : syracuseStep 3747151 = 5620727) B5620727
theorem B8564105 : Blo 778337 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B831227 : Blo 778337 831227 := bstep (se 1 (by rfl) ⟨623420, by rfl⟩ : syracuseStep 831227 = 1246841) B1246841
theorem B1978283 : Blo 778337 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B3945023 : Blo 778337 3945023 := bstep (se 1 (by rfl) ⟨2958767, by rfl⟩ : syracuseStep 3945023 = 5917535) B5917535
theorem B4436855 : Blo 778337 4436855 := bstep (se 1 (by rfl) ⟨3327641, by rfl⟩ : syracuseStep 4436855 = 6655283) B6655283
theorem B2503561 : Blo 778337 2503561 := bstep (se 2 (by rfl) ⟨938835, by rfl⟩ : syracuseStep 2503561 = 1877671) B1877671
theorem B6009851 : Blo 778337 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B2635847 : Blo 778337 2635847 := bstep (se 1 (by rfl) ⟨1976885, by rfl⟩ : syracuseStep 2635847 = 3953771) B3953771
theorem B3947129 : Blo 778337 3947129 := bstep (se 2 (by rfl) ⟨1480173, by rfl⟩ : syracuseStep 3947129 = 2960347) B2960347
theorem B13318829 : Blo 778337 13318829 := bstep (se 3 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 13318829 = 4994561) B4994561
theorem B1751777 : Blo 778337 1751777 := bstep (se 2 (by rfl) ⟨656916, by rfl⟩ : syracuseStep 1751777 = 1313833) B1313833
theorem B3324719 : Blo 778337 3324719 := bstep (se 1 (by rfl) ⟨2493539, by rfl⟩ : syracuseStep 3324719 = 4987079) B4987079
theorem B1751975 : Blo 778337 1751975 := bstep (se 1 (by rfl) ⟨1313981, by rfl⟩ : syracuseStep 1751975 = 2627963) B2627963
theorem B2636711 : Blo 778337 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B2964539 : Blo 778337 2964539 := bstep (se 1 (by rfl) ⟨2223404, by rfl⟩ : syracuseStep 2964539 = 4446809) B4446809
theorem B1752155 : Blo 778337 1752155 := bstep (se 1 (by rfl) ⟨1314116, by rfl⟩ : syracuseStep 1752155 = 2628233) B2628233
theorem B2112617 : Blo 778337 2112617 := bstep (se 2 (by rfl) ⟨792231, by rfl⟩ : syracuseStep 2112617 = 1584463) B1584463
theorem B6340319 : Blo 778337 6340319 := bstep (se 1 (by rfl) ⟨4755239, by rfl⟩ : syracuseStep 6340319 = 9510479) B9510479
theorem B1752911 : Blo 778337 1752911 := bstep (se 1 (by rfl) ⟨1314683, by rfl⟩ : syracuseStep 1752911 = 2629367) B2629367
theorem B2375915 : Blo 778337 2375915 := bstep (se 1 (by rfl) ⟨1781936, by rfl⟩ : syracuseStep 2375915 = 3563873) B3563873
theorem B803071 : Blo 778337 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B1753631 : Blo 778337 1753631 := bstep (se 1 (by rfl) ⟨1315223, by rfl⟩ : syracuseStep 1753631 = 2630447) B2630447
theorem B1753703 : Blo 778337 1753703 := bstep (se 1 (by rfl) ⟨1315277, by rfl⟩ : syracuseStep 1753703 = 2630555) B2630555
theorem B2638439 : Blo 778337 2638439 := bstep (se 1 (by rfl) ⟨1978829, by rfl⟩ : syracuseStep 2638439 = 3957659) B3957659
theorem B5620499 : Blo 778337 5620499 := bstep (se 1 (by rfl) ⟨4215374, by rfl⟩ : syracuseStep 5620499 = 8430749) B8430749
theorem B2966651 : Blo 778337 2966651 := bstep (se 1 (by rfl) ⟨2224988, by rfl⟩ : syracuseStep 2966651 = 4449977) B4449977
theorem B1754459 : Blo 778337 1754459 := bstep (se 1 (by rfl) ⟨1315844, by rfl⟩ : syracuseStep 1754459 = 2631689) B2631689
theorem B10700171 : Blo 778337 10700171 := bstep (se 1 (by rfl) ⟨8025128, by rfl⟩ : syracuseStep 10700171 = 16050257) B16050257
theorem B3327419 : Blo 778337 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B1754729 : Blo 778337 1754729 := bstep (se 2 (by rfl) ⟨658023, by rfl⟩ : syracuseStep 1754729 = 1316047) B1316047
theorem B55428907 : Blo 778337 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B3164255 : Blo 778337 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B7489655 : Blo 778337 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B7489691 : Blo 778337 7489691 := bstep (se 1 (by rfl) ⟨5617268, by rfl⟩ : syracuseStep 7489691 = 11234537) B11234537
theorem B1755323 : Blo 778337 1755323 := bstep (se 1 (by rfl) ⟨1316492, by rfl⟩ : syracuseStep 1755323 = 2632985) B2632985
theorem B1755359 : Blo 778337 1755359 := bstep (se 1 (by rfl) ⟨1316519, by rfl⟩ : syracuseStep 1755359 = 2633039) B2633039
theorem B28821851 : Blo 778337 28821851 := bstep (se 1 (by rfl) ⟨21616388, by rfl⟩ : syracuseStep 28821851 = 43232777) B43232777
theorem B3951017 : Blo 778337 3951017 := bstep (se 2 (by rfl) ⟨1481631, by rfl⟩ : syracuseStep 3951017 = 2963263) B2963263
theorem B14994071 : Blo 778337 14994071 := bstep (se 1 (by rfl) ⟨11245553, by rfl⟩ : syracuseStep 14994071 = 22491107) B22491107
theorem B1755809 : Blo 778337 1755809 := bstep (se 2 (by rfl) ⟨658428, by rfl⟩ : syracuseStep 1755809 = 1316857) B1316857
theorem B8440523 : Blo 778337 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B1756025 : Blo 778337 1756025 := bstep (se 2 (by rfl) ⟨658509, by rfl⟩ : syracuseStep 1756025 = 1317019) B1317019
theorem B10144763 : Blo 778337 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B5000201 : Blo 778337 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B1756169 : Blo 778337 1756169 := bstep (se 2 (by rfl) ⟨658563, by rfl⟩ : syracuseStep 1756169 = 1317127) B1317127
theorem B1756223 : Blo 778337 1756223 := bstep (se 1 (by rfl) ⟨1317167, by rfl⟩ : syracuseStep 1756223 = 2634335) B2634335
theorem B937067 : Blo 778337 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B2969369 : Blo 778337 2969369 := bstep (se 2 (by rfl) ⟨1113513, by rfl⟩ : syracuseStep 2969369 = 2227027) B2227027
theorem B2969399 : Blo 778337 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B1757051 : Blo 778337 1757051 := bstep (se 1 (by rfl) ⟨1317788, by rfl⟩ : syracuseStep 1757051 = 2635577) B2635577
theorem B3329981 : Blo 778337 3329981 := bstep (se 3 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 3329981 = 1248743) B1248743
theorem B1757159 : Blo 778337 1757159 := bstep (se 1 (by rfl) ⟨1317869, by rfl⟩ : syracuseStep 1757159 = 2635739) B2635739
theorem B3756071 : Blo 778337 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B1167515 : Blo 778337 1167515 := bstep (se 1 (by rfl) ⟨875636, by rfl⟩ : syracuseStep 1167515 = 1751273) B1751273
theorem B1757339 : Blo 778337 1757339 := bstep (se 1 (by rfl) ⟨1318004, by rfl⟩ : syracuseStep 1757339 = 2636009) B2636009
theorem B2969885 : Blo 778337 2969885 := bstep (se 3 (by rfl) ⟨556853, by rfl⟩ : syracuseStep 2969885 = 1113707) B1113707
theorem B1757537 : Blo 778337 1757537 := bstep (se 2 (by rfl) ⟨659076, by rfl⟩ : syracuseStep 1757537 = 1318153) B1318153
theorem B1757627 : Blo 778337 1757627 := bstep (se 1 (by rfl) ⟨1318220, by rfl⟩ : syracuseStep 1757627 = 2636441) B2636441
theorem B2970067 : Blo 778337 2970067 := bstep (se 1 (by rfl) ⟨2227550, by rfl⟩ : syracuseStep 2970067 = 4455101) B4455101
theorem B1168367 : Blo 778337 1168367 := bstep (se 1 (by rfl) ⟨876275, by rfl⟩ : syracuseStep 1168367 = 1752551) B1752551
theorem B5625085 : Blo 778337 5625085 := bstep (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) B2109407
theorem B1168751 : Blo 778337 1168751 := bstep (se 1 (by rfl) ⟨876563, by rfl⟩ : syracuseStep 1168751 = 1753127) B1753127
theorem B1168871 : Blo 778337 1168871 := bstep (se 1 (by rfl) ⟨876653, by rfl⟩ : syracuseStep 1168871 = 1753307) B1753307
theorem B1169033 : Blo 778337 1169033 := bstep (se 2 (by rfl) ⟨438387, by rfl⟩ : syracuseStep 1169033 = 876775) B876775
theorem B1169051 : Blo 778337 1169051 := bstep (se 1 (by rfl) ⟨876788, by rfl⟩ : syracuseStep 1169051 = 1753577) B1753577
theorem B1758887 : Blo 778337 1758887 := bstep (se 1 (by rfl) ⟨1319165, by rfl⟩ : syracuseStep 1758887 = 2638331) B2638331
theorem B1169243 : Blo 778337 1169243 := bstep (se 1 (by rfl) ⟨876932, by rfl⟩ : syracuseStep 1169243 = 1753865) B1753865
theorem B1759067 : Blo 778337 1759067 := bstep (se 1 (by rfl) ⟨1319300, by rfl⟩ : syracuseStep 1759067 = 2638601) B2638601
theorem B4446353 : Blo 778337 4446353 := bstep (se 2 (by rfl) ⟨1667382, by rfl⟩ : syracuseStep 4446353 = 3334765) B3334765
theorem B6019217 : Blo 778337 6019217 := bstep (se 2 (by rfl) ⟨2257206, by rfl⟩ : syracuseStep 6019217 = 4514413) B4514413
theorem B1169627 : Blo 778337 1169627 := bstep (se 1 (by rfl) ⟨877220, by rfl⟩ : syracuseStep 1169627 = 1754441) B1754441
theorem B6412553 : Blo 778337 6412553 := bstep (se 2 (by rfl) ⟨2404707, by rfl⟩ : syracuseStep 6412553 = 4809415) B4809415
theorem B1759571 : Blo 778337 1759571 := bstep (se 1 (by rfl) ⟨1319678, by rfl⟩ : syracuseStep 1759571 = 2639357) B2639357
theorem B2218337 : Blo 778337 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B1169897 : Blo 778337 1169897 := bstep (se 2 (by rfl) ⟨438711, by rfl⟩ : syracuseStep 1169897 = 877423) B877423
theorem B6773345 : Blo 778337 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B75979457 : Blo 778337 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B1760057 : Blo 778337 1760057 := bstep (se 2 (by rfl) ⟨660021, by rfl⟩ : syracuseStep 1760057 = 1320043) B1320043
theorem B1170287 : Blo 778337 1170287 := bstep (se 1 (by rfl) ⟨877715, by rfl⟩ : syracuseStep 1170287 = 1755431) B1755431
theorem B1760111 : Blo 778337 1760111 := bstep (se 1 (by rfl) ⟨1320083, by rfl⟩ : syracuseStep 1760111 = 2640167) B2640167
theorem B1170299 : Blo 778337 1170299 := bstep (se 1 (by rfl) ⟨877724, by rfl⟩ : syracuseStep 1170299 = 1755449) B1755449
theorem B6675817 : Blo 778337 6675817 := bstep (se 2 (by rfl) ⟨2503431, by rfl⟩ : syracuseStep 6675817 = 5006863) B5006863
theorem B875983 : Blo 778337 875983 := bstep (se 1 (by rfl) ⟨656987, by rfl⟩ : syracuseStep 875983 = 1313975) B1313975
theorem B3956201 : Blo 778337 3956201 := bstep (se 2 (by rfl) ⟨1483575, by rfl⟩ : syracuseStep 3956201 = 2967151) B2967151
theorem B876199 : Blo 778337 876199 := bstep (se 1 (by rfl) ⟨657149, by rfl⟩ : syracuseStep 876199 = 1314299) B1314299
theorem B1171163 : Blo 778337 1171163 := bstep (se 1 (by rfl) ⟨878372, by rfl⟩ : syracuseStep 1171163 = 1756745) B1756745
theorem B2219795 : Blo 778337 2219795 := bstep (se 1 (by rfl) ⟨1664846, by rfl⟩ : syracuseStep 2219795 = 3329693) B3329693
theorem B876487 : Blo 778337 876487 := bstep (se 1 (by rfl) ⟨657365, by rfl⟩ : syracuseStep 876487 = 1314731) B1314731
theorem B1171433 : Blo 778337 1171433 := bstep (se 2 (by rfl) ⟨439287, by rfl⟩ : syracuseStep 1171433 = 878575) B878575
theorem B778431 : Blo 778337 778431 := bstep (se 1 (by rfl) ⟨583823, by rfl⟩ : syracuseStep 778431 = 1167647) B1167647
theorem B778447 : Blo 778337 778447 := bstep (se 1 (by rfl) ⟨583835, by rfl⟩ : syracuseStep 778447 = 1167671) B1167671
theorem B778495 : Blo 778337 778495 := bstep (se 1 (by rfl) ⟨583871, by rfl⟩ : syracuseStep 778495 = 1167743) B1167743
theorem B778543 : Blo 778337 778543 := bstep (se 1 (by rfl) ⟨583907, by rfl⟩ : syracuseStep 778543 = 1167815) B1167815
theorem B876847 : Blo 778337 876847 := bstep (se 1 (by rfl) ⟨657635, by rfl⟩ : syracuseStep 876847 = 1315271) B1315271
theorem B7725473 : Blo 778337 7725473 := bstep (se 2 (by rfl) ⟨2897052, by rfl⟩ : syracuseStep 7725473 = 5794105) B5794105
theorem B778779 : Blo 778337 778779 := bstep (se 1 (by rfl) ⟨584084, by rfl⟩ : syracuseStep 778779 = 1168169) B1168169
theorem B778783 : Blo 778337 778783 := bstep (se 1 (by rfl) ⟨584087, by rfl⟩ : syracuseStep 778783 = 1168175) B1168175
theorem B5923367 : Blo 778337 5923367 := bstep (se 1 (by rfl) ⟨4442525, by rfl⟩ : syracuseStep 5923367 = 8885051) B8885051
theorem B778863 : Blo 778337 778863 := bstep (se 1 (by rfl) ⟨584147, by rfl⟩ : syracuseStep 778863 = 1168295) B1168295
theorem B778919 : Blo 778337 778919 := bstep (se 1 (by rfl) ⟨584189, by rfl⟩ : syracuseStep 778919 = 1168379) B1168379
theorem B1172135 : Blo 778337 1172135 := bstep (se 1 (by rfl) ⟨879101, by rfl⟩ : syracuseStep 1172135 = 1758203) B1758203
theorem B778959 : Blo 778337 778959 := bstep (se 1 (by rfl) ⟨584219, by rfl⟩ : syracuseStep 778959 = 1168439) B1168439
theorem B779039 : Blo 778337 779039 := bstep (se 1 (by rfl) ⟨584279, by rfl⟩ : syracuseStep 779039 = 1168559) B1168559
theorem B1172255 : Blo 778337 1172255 := bstep (se 1 (by rfl) ⟨879191, by rfl⟩ : syracuseStep 1172255 = 1758383) B1758383
theorem B1172279 : Blo 778337 1172279 := bstep (se 1 (by rfl) ⟨879209, by rfl⟩ : syracuseStep 1172279 = 1758419) B1758419
theorem B1172459 : Blo 778337 1172459 := bstep (se 1 (by rfl) ⟨879344, by rfl⟩ : syracuseStep 1172459 = 1758689) B1758689
theorem B779311 : Blo 778337 779311 := bstep (se 1 (by rfl) ⟨584483, by rfl⟩ : syracuseStep 779311 = 1168967) B1168967
theorem B779375 : Blo 778337 779375 := bstep (se 1 (by rfl) ⟨584531, by rfl⟩ : syracuseStep 779375 = 1169063) B1169063
theorem B779431 : Blo 778337 779431 := bstep (se 1 (by rfl) ⟨584573, by rfl⟩ : syracuseStep 779431 = 1169147) B1169147
theorem B779455 : Blo 778337 779455 := bstep (se 1 (by rfl) ⟨584591, by rfl⟩ : syracuseStep 779455 = 1169183) B1169183
theorem B779487 : Blo 778337 779487 := bstep (se 1 (by rfl) ⟨584615, by rfl⟩ : syracuseStep 779487 = 1169231) B1169231
theorem B779567 : Blo 778337 779567 := bstep (se 1 (by rfl) ⟨584675, by rfl⟩ : syracuseStep 779567 = 1169351) B1169351
theorem B3958145 : Blo 778337 3958145 := bstep (se 2 (by rfl) ⟨1484304, by rfl⟩ : syracuseStep 3958145 = 2968609) B2968609
theorem B779803 : Blo 778337 779803 := bstep (se 1 (by rfl) ⟨584852, by rfl⟩ : syracuseStep 779803 = 1169705) B1169705
theorem B878107 : Blo 778337 878107 := bstep (se 1 (by rfl) ⟨658580, by rfl⟩ : syracuseStep 878107 = 1317161) B1317161
theorem B779807 : Blo 778337 779807 := bstep (se 1 (by rfl) ⟨584855, by rfl⟩ : syracuseStep 779807 = 1169711) B1169711
theorem B779967 : Blo 778337 779967 := bstep (se 1 (by rfl) ⟨584975, by rfl⟩ : syracuseStep 779967 = 1169951) B1169951
theorem B780223 : Blo 778337 780223 := bstep (se 1 (by rfl) ⟨585167, by rfl⟩ : syracuseStep 780223 = 1170335) B1170335
theorem B5334983 : Blo 778337 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B1402847 : Blo 778337 1402847 := bstep (se 1 (by rfl) ⟨1052135, by rfl⟩ : syracuseStep 1402847 = 2104271) B2104271
theorem B780255 : Blo 778337 780255 := bstep (se 1 (by rfl) ⟨585191, by rfl⟩ : syracuseStep 780255 = 1170383) B1170383
theorem B5629931 : Blo 778337 5629931 := bstep (se 1 (by rfl) ⟨4222448, by rfl⟩ : syracuseStep 5629931 = 8444897) B8444897
theorem B780315 : Blo 778337 780315 := bstep (se 1 (by rfl) ⟨585236, by rfl⟩ : syracuseStep 780315 = 1170473) B1170473
theorem B780319 : Blo 778337 780319 := bstep (se 1 (by rfl) ⟨585239, by rfl⟩ : syracuseStep 780319 = 1170479) B1170479
theorem B780335 : Blo 778337 780335 := bstep (se 1 (by rfl) ⟨585251, by rfl⟩ : syracuseStep 780335 = 1170503) B1170503
theorem B1599571 : Blo 778337 1599571 := bstep (se 1 (by rfl) ⟨1199678, by rfl⟩ : syracuseStep 1599571 = 2399357) B2399357
theorem B3958955 : Blo 778337 3958955 := bstep (se 1 (by rfl) ⟨2969216, by rfl⟩ : syracuseStep 3958955 = 5938433) B5938433
theorem B780511 : Blo 778337 780511 := bstep (se 1 (by rfl) ⟨585383, by rfl⟩ : syracuseStep 780511 = 1170767) B1170767
theorem B780571 : Blo 778337 780571 := bstep (se 1 (by rfl) ⟨585428, by rfl⟩ : syracuseStep 780571 = 1170857) B1170857
theorem B780671 : Blo 778337 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B780847 : Blo 778337 780847 := bstep (se 1 (by rfl) ⟨585635, by rfl⟩ : syracuseStep 780847 = 1171271) B1171271
theorem B879151 : Blo 778337 879151 := bstep (se 1 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 879151 = 1318727) B1318727
theorem B780903 : Blo 778337 780903 := bstep (se 1 (by rfl) ⟨585677, by rfl⟩ : syracuseStep 780903 = 1171355) B1171355
theorem B3959441 : Blo 778337 3959441 := bstep (se 2 (by rfl) ⟨1484790, by rfl⟩ : syracuseStep 3959441 = 2969581) B2969581
theorem B506751673 : Blo 778337 506751673 := bstep (se 2 (by rfl) ⟨190031877, by rfl⟩ : syracuseStep 506751673 = 380063755) B380063755
theorem B2222927 : Blo 778337 2222927 := bstep (se 1 (by rfl) ⟨1667195, by rfl⟩ : syracuseStep 2222927 = 3334391) B3334391
theorem B781279 : Blo 778337 781279 := bstep (se 1 (by rfl) ⟨585959, by rfl⟩ : syracuseStep 781279 = 1171919) B1171919
theorem B879583 : Blo 778337 879583 := bstep (se 1 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 879583 = 1319375) B1319375
theorem B108030955 : Blo 778337 108030955 := bstep (se 1 (by rfl) ⟨81023216, by rfl⟩ : syracuseStep 108030955 = 162046433) B162046433
theorem B17591285 : Blo 778337 17591285 := bstep (se 5 (by rfl) ⟨824591, by rfl⟩ : syracuseStep 17591285 = 1649183) B1649183
theorem B781307 : Blo 778337 781307 := bstep (se 1 (by rfl) ⟨585980, by rfl⟩ : syracuseStep 781307 = 1171961) B1171961
theorem B781375 : Blo 778337 781375 := bstep (se 1 (by rfl) ⟨586031, by rfl⟩ : syracuseStep 781375 = 1172063) B1172063
theorem B13495567 : Blo 778337 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B781695 : Blo 778337 781695 := bstep (se 1 (by rfl) ⟨586271, by rfl⟩ : syracuseStep 781695 = 1172543) B1172543
theorem B781723 : Blo 778337 781723 := bstep (se 1 (by rfl) ⟨586292, by rfl⟩ : syracuseStep 781723 = 1172585) B1172585
theorem B781791 : Blo 778337 781791 := bstep (se 1 (by rfl) ⟨586343, by rfl⟩ : syracuseStep 781791 = 1172687) B1172687
theorem B1666631 : Blo 778337 1666631 := bstep (se 1 (by rfl) ⟨1249973, by rfl⟩ : syracuseStep 1666631 = 2499947) B2499947
theorem B8908379 : Blo 778337 8908379 := bstep (se 1 (by rfl) ⟨6681284, by rfl⟩ : syracuseStep 8908379 = 13362569) B13362569
theorem B781927 : Blo 778337 781927 := bstep (se 1 (by rfl) ⟨586445, by rfl⟩ : syracuseStep 781927 = 1172891) B1172891
theorem B782075 : Blo 778337 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B782143 : Blo 778337 782143 := bstep (se 1 (by rfl) ⟨586607, by rfl⟩ : syracuseStep 782143 = 1173215) B1173215
theorem B782207 : Blo 778337 782207 := bstep (se 1 (by rfl) ⟨586655, by rfl⟩ : syracuseStep 782207 = 1173311) B1173311
theorem B782319 : Blo 778337 782319 := bstep (se 1 (by rfl) ⟨586739, by rfl⟩ : syracuseStep 782319 = 1173479) B1173479
theorem B782331 : Blo 778337 782331 := bstep (se 1 (by rfl) ⟨586748, by rfl⟩ : syracuseStep 782331 = 1173497) B1173497
theorem B109801615 : Blo 778337 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B2224361 : Blo 778337 2224361 := bstep (se 2 (by rfl) ⟨834135, by rfl⟩ : syracuseStep 2224361 = 1668271) B1668271
theorem B51212569 : Blo 778337 51212569 := bstep (se 2 (by rfl) ⟨19204713, by rfl⟩ : syracuseStep 51212569 = 38409427) B38409427
theorem B9498991 : Blo 778337 9498991 := bstep (se 1 (by rfl) ⟨7124243, by rfl⟩ : syracuseStep 9498991 = 14248487) B14248487
theorem B11268791 : Blo 778337 11268791 := bstep (se 1 (by rfl) ⟨8451593, by rfl⟩ : syracuseStep 11268791 = 16903187) B16903187
theorem B5927741 : Blo 778337 5927741 := bstep (se 3 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 5927741 = 2222903) B2222903
theorem B6681527 : Blo 778337 6681527 := bstep (se 1 (by rfl) ⟨5011145, by rfl⟩ : syracuseStep 6681527 = 10022291) B10022291
theorem B1110991 : Blo 778337 1110991 := bstep (se 1 (by rfl) ⟨833243, by rfl⟩ : syracuseStep 1110991 = 1666487) B1666487
theorem B1112135 : Blo 778337 1112135 := bstep (se 1 (by rfl) ⟨834101, by rfl⟩ : syracuseStep 1112135 = 1668203) B1668203
theorem B18971131 : Blo 778337 18971131 := bstep (se 1 (by rfl) ⟨14228348, by rfl⟩ : syracuseStep 18971131 = 28456697) B28456697
theorem B1669673 : Blo 778337 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B131726989 : Blo 778337 131726989 := bstep (se 3 (by rfl) ⟨24698810, by rfl⟩ : syracuseStep 131726989 = 49397621) B49397621
theorem B9994043 : Blo 778337 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B5931629 : Blo 778337 5931629 := bstep (se 3 (by rfl) ⟨1112180, by rfl⟩ : syracuseStep 5931629 = 2224361) B2224361
theorem B9996047 : Blo 778337 9996047 := bstep (se 1 (by rfl) ⟨7497035, by rfl⟩ : syracuseStep 9996047 = 14994071) B14994071
theorem B1247167 : Blo 778337 1247167 := bstep (se 1 (by rfl) ⟨935375, by rfl⟩ : syracuseStep 1247167 = 1870751) B1870751
theorem B2132761 : Blo 778337 2132761 := bstep (se 2 (by rfl) ⟨799785, by rfl⟩ : syracuseStep 2132761 = 1599571) B1599571
theorem B986023 : Blo 778337 986023 := bstep (se 1 (by rfl) ⟨739517, by rfl⟩ : syracuseStep 986023 = 1479035) B1479035
theorem B1248347 : Blo 778337 1248347 := bstep (se 1 (by rfl) ⟨936260, by rfl⟩ : syracuseStep 1248347 = 1872521) B1872521
theorem B1314751 : Blo 778337 1314751 := bstep (se 1 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 1314751 = 1972127) B1972127
theorem B1478891 : Blo 778337 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B2494745 : Blo 778337 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B17994089 : Blo 778337 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B1970639 : Blo 778337 1970639 := bstep (se 1 (by rfl) ⟨1477979, by rfl⟩ : syracuseStep 1970639 = 2955959) B2955959
theorem B1479863 : Blo 778337 1479863 := bstep (se 1 (by rfl) ⟨1109897, by rfl⟩ : syracuseStep 1479863 = 2219795) B2219795
theorem B5150315 : Blo 778337 5150315 := bstep (se 1 (by rfl) ⟨3862736, by rfl⟩ : syracuseStep 5150315 = 7725473) B7725473
theorem B1481321 : Blo 778337 1481321 := bstep (se 2 (by rfl) ⟨555495, by rfl⟩ : syracuseStep 1481321 = 1110991) B1110991
theorem B1317883 : Blo 778337 1317883 := bstep (se 1 (by rfl) ⟨988412, by rfl⟩ : syracuseStep 1317883 = 1976825) B1976825
theorem B1973423 : Blo 778337 1973423 := bstep (se 1 (by rfl) ⟨1480067, by rfl⟩ : syracuseStep 1973423 = 2960135) B2960135
theorem B1481951 : Blo 778337 1481951 := bstep (se 1 (by rfl) ⟨1111463, by rfl⟩ : syracuseStep 1481951 = 2222927) B2222927
theorem B1318207 : Blo 778337 1318207 := bstep (se 1 (by rfl) ⟨988655, by rfl⟩ : syracuseStep 1318207 = 1977311) B1977311
theorem B1318315 : Blo 778337 1318315 := bstep (se 1 (by rfl) ⟨988736, by rfl⟩ : syracuseStep 1318315 = 1977473) B1977473
theorem B4988411 : Blo 778337 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B5709403 : Blo 778337 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B5938919 : Blo 778337 5938919 := bstep (se 1 (by rfl) ⟨4454189, by rfl⟩ : syracuseStep 5938919 = 8908379) B8908379
theorem B1974041 : Blo 778337 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B1318855 : Blo 778337 1318855 := bstep (se 1 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 1318855 = 1978283) B1978283
theorem B2498845 : Blo 778337 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B2630015 : Blo 778337 2630015 := bstep (se 1 (by rfl) ⟨1972511, by rfl⟩ : syracuseStep 2630015 = 3945023) B3945023
theorem B1974689 : Blo 778337 1974689 := bstep (se 2 (by rfl) ⟨740508, by rfl⟩ : syracuseStep 1974689 = 1481017) B1481017
theorem B7512527 : Blo 778337 7512527 := bstep (se 1 (by rfl) ⟨5634395, by rfl⟩ : syracuseStep 7512527 = 11268791) B11268791
theorem B2957903 : Blo 778337 2957903 := bstep (se 1 (by rfl) ⟨2218427, by rfl⟩ : syracuseStep 2957903 = 4436855) B4436855
theorem B4006567 : Blo 778337 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B2631419 : Blo 778337 2631419 := bstep (se 1 (by rfl) ⟨1973564, by rfl⟩ : syracuseStep 2631419 = 3947129) B3947129
theorem B2500409 : Blo 778337 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B1976359 : Blo 778337 1976359 := bstep (se 1 (by rfl) ⟨1482269, by rfl⟩ : syracuseStep 1976359 = 2964539) B2964539
theorem B6662695 : Blo 778337 6662695 := bstep (se 1 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 6662695 = 9994043) B9994043
theorem B3746999 : Blo 778337 3746999 := bstep (se 1 (by rfl) ⟨2810249, by rfl⟩ : syracuseStep 3746999 = 5620499) B5620499
theorem B36547949 : Blo 778337 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B1977767 : Blo 778337 1977767 := bstep (se 1 (by rfl) ⟨1483325, by rfl⟩ : syracuseStep 1977767 = 2966651) B2966651
theorem B5615077 : Blo 778337 5615077 := bstep (se 4 (by rfl) ⟨526413, by rfl⟩ : syracuseStep 5615077 = 1052827) B1052827
theorem B6663653 : Blo 778337 6663653 := bstep (se 4 (by rfl) ⟨624717, by rfl⟩ : syracuseStep 6663653 = 1249435) B1249435
theorem B5648201 : Blo 778337 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B5418971 : Blo 778337 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B2109503 : Blo 778337 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B4993103 : Blo 778337 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B1978465 : Blo 778337 1978465 := bstep (se 2 (by rfl) ⟨741924, by rfl⟩ : syracuseStep 1978465 = 1483849) B1483849
theorem B4993127 : Blo 778337 4993127 := bstep (se 1 (by rfl) ⟨3744845, by rfl⟩ : syracuseStep 4993127 = 7489691) B7489691
theorem B19214567 : Blo 778337 19214567 := bstep (se 1 (by rfl) ⟨14410925, by rfl⟩ : syracuseStep 19214567 = 28821851) B28821851
theorem B2634011 : Blo 778337 2634011 := bstep (se 1 (by rfl) ⟨1975508, by rfl⟩ : syracuseStep 2634011 = 3951017) B3951017
theorem B6763175 : Blo 778337 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B2405177 : Blo 778337 2405177 := bstep (se 2 (by rfl) ⟨901941, by rfl⟩ : syracuseStep 2405177 = 1803883) B1803883
theorem B1979417 : Blo 778337 1979417 := bstep (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) B1484563
theorem B73905209 : Blo 778337 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B25343093 : Blo 778337 25343093 := bstep (se 5 (by rfl) ⟨1187957, by rfl⟩ : syracuseStep 25343093 = 2375915) B2375915
theorem B1979579 : Blo 778337 1979579 := bstep (se 1 (by rfl) ⟨1484684, by rfl⟩ : syracuseStep 1979579 = 2969369) B2969369
theorem B1979599 : Blo 778337 1979599 := bstep (se 1 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 1979599 = 2969399) B2969399
theorem B2504047 : Blo 778337 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B2602451 : Blo 778337 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B1979923 : Blo 778337 1979923 := bstep (se 1 (by rfl) ⟨1484942, by rfl⟩ : syracuseStep 1979923 = 2969885) B2969885
theorem B833051 : Blo 778337 833051 := bstep (se 1 (by rfl) ⟨624788, by rfl⟩ : syracuseStep 833051 = 1249577) B1249577
theorem B1751327 : Blo 778337 1751327 := bstep (se 1 (by rfl) ⟨1313495, by rfl⟩ : syracuseStep 1751327 = 2626991) B2626991
theorem B1751543 : Blo 778337 1751543 := bstep (se 1 (by rfl) ⟨1313657, by rfl⟩ : syracuseStep 1751543 = 2627315) B2627315
theorem B2964235 : Blo 778337 2964235 := bstep (se 1 (by rfl) ⟨2223176, by rfl⟩ : syracuseStep 2964235 = 4446353) B4446353
theorem B4012811 : Blo 778337 4012811 := bstep (se 1 (by rfl) ⟨3009608, by rfl⟩ : syracuseStep 4012811 = 6019217) B6019217
theorem B4275035 : Blo 778337 4275035 := bstep (se 1 (by rfl) ⟨3206276, by rfl⟩ : syracuseStep 4275035 = 6412553) B6412553
theorem B1752047 : Blo 778337 1752047 := bstep (se 1 (by rfl) ⟨1314035, by rfl⟩ : syracuseStep 1752047 = 2628071) B2628071
theorem B2636873 : Blo 778337 2636873 := bstep (se 2 (by rfl) ⟨988827, by rfl⟩ : syracuseStep 2636873 = 1977655) B1977655
theorem B18988253 : Blo 778337 18988253 := bstep (se 3 (by rfl) ⟨3560297, by rfl⟩ : syracuseStep 18988253 = 7120595) B7120595
theorem B4439519 : Blo 778337 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B1752623 : Blo 778337 1752623 := bstep (se 1 (by rfl) ⟨1314467, by rfl⟩ : syracuseStep 1752623 = 2628935) B2628935
theorem B2637467 : Blo 778337 2637467 := bstep (se 1 (by rfl) ⟨1978100, by rfl⟩ : syracuseStep 2637467 = 3956201) B3956201
theorem B4439771 : Blo 778337 4439771 := bstep (se 1 (by rfl) ⟨3329828, by rfl⟩ : syracuseStep 4439771 = 6659657) B6659657
theorem B1753055 : Blo 778337 1753055 := bstep (se 1 (by rfl) ⟨1314791, by rfl⟩ : syracuseStep 1753055 = 2629583) B2629583
theorem B2965693 : Blo 778337 2965693 := bstep (se 3 (by rfl) ⟨556067, by rfl⟩ : syracuseStep 2965693 = 1112135) B1112135
theorem B8896715 : Blo 778337 8896715 := bstep (se 1 (by rfl) ⟨6672536, by rfl⟩ : syracuseStep 8896715 = 13345073) B13345073
theorem B3948911 : Blo 778337 3948911 := bstep (se 1 (by rfl) ⟨2961683, by rfl⟩ : syracuseStep 3948911 = 5923367) B5923367
theorem B12665321 : Blo 778337 12665321 := bstep (se 2 (by rfl) ⟨4749495, by rfl⟩ : syracuseStep 12665321 = 9498991) B9498991
theorem B2638763 : Blo 778337 2638763 := bstep (se 1 (by rfl) ⟨1979072, by rfl⟩ : syracuseStep 2638763 = 3958145) B3958145
theorem B3556655 : Blo 778337 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B935231 : Blo 778337 935231 := bstep (se 1 (by rfl) ⟨701423, by rfl⟩ : syracuseStep 935231 = 1402847) B1402847
theorem B3753287 : Blo 778337 3753287 := bstep (se 1 (by rfl) ⟨2814965, by rfl⟩ : syracuseStep 3753287 = 5629931) B5629931
theorem B2639303 : Blo 778337 2639303 := bstep (se 1 (by rfl) ⟨1979477, by rfl⟩ : syracuseStep 2639303 = 3958955) B3958955
theorem B2639627 : Blo 778337 2639627 := bstep (se 1 (by rfl) ⟨1979720, by rfl⟩ : syracuseStep 2639627 = 3959441) B3959441
theorem B3951827 : Blo 778337 3951827 := bstep (se 1 (by rfl) ⟨2963870, by rfl⟩ : syracuseStep 3951827 = 5927741) B5927741
theorem B1757231 : Blo 778337 1757231 := bstep (se 1 (by rfl) ⟨1317923, by rfl⟩ : syracuseStep 1757231 = 2635847) B2635847
theorem B8901089 : Blo 778337 8901089 := bstep (se 2 (by rfl) ⟨3337908, by rfl⟩ : syracuseStep 8901089 = 6675817) B6675817
theorem B1167851 : Blo 778337 1167851 := bstep (se 1 (by rfl) ⟨875888, by rfl⟩ : syracuseStep 1167851 = 1751777) B1751777
theorem B2216479 : Blo 778337 2216479 := bstep (se 1 (by rfl) ⟨1662359, by rfl⟩ : syracuseStep 2216479 = 3324719) B3324719
theorem B1167977 : Blo 778337 1167977 := bstep (se 2 (by rfl) ⟨437991, by rfl⟩ : syracuseStep 1167977 = 875983) B875983
theorem B1167983 : Blo 778337 1167983 := bstep (se 1 (by rfl) ⟨875987, by rfl⟩ : syracuseStep 1167983 = 1751975) B1751975
theorem B1757807 : Blo 778337 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B2216605 : Blo 778337 2216605 := bstep (se 3 (by rfl) ⟨415613, by rfl⟩ : syracuseStep 2216605 = 831227) B831227
theorem B1168103 : Blo 778337 1168103 := bstep (se 1 (by rfl) ⟨876077, by rfl⟩ : syracuseStep 1168103 = 1752155) B1752155
theorem B1168265 : Blo 778337 1168265 := bstep (se 2 (by rfl) ⟨438099, by rfl⟩ : syracuseStep 1168265 = 876199) B876199
theorem B1168607 : Blo 778337 1168607 := bstep (se 1 (by rfl) ⟨876455, by rfl⟩ : syracuseStep 1168607 = 1752911) B1752911
theorem B1168649 : Blo 778337 1168649 := bstep (se 2 (by rfl) ⟨438243, by rfl⟩ : syracuseStep 1168649 = 876487) B876487
theorem B1070761 : Blo 778337 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B1169087 : Blo 778337 1169087 := bstep (se 1 (by rfl) ⟨876815, by rfl⟩ : syracuseStep 1169087 = 1753631) B1753631
theorem B1169129 : Blo 778337 1169129 := bstep (se 2 (by rfl) ⟨438423, by rfl⟩ : syracuseStep 1169129 = 876847) B876847
theorem B1169135 : Blo 778337 1169135 := bstep (se 1 (by rfl) ⟨876851, by rfl⟩ : syracuseStep 1169135 = 1753703) B1753703
theorem B1758959 : Blo 778337 1758959 := bstep (se 1 (by rfl) ⟨1319219, by rfl⟩ : syracuseStep 1758959 = 2638439) B2638439
theorem B16832609 : Blo 778337 16832609 := bstep (se 2 (by rfl) ⟨6312228, by rfl⟩ : syracuseStep 16832609 = 12624457) B12624457
theorem B1169639 : Blo 778337 1169639 := bstep (se 1 (by rfl) ⟨877229, by rfl⟩ : syracuseStep 1169639 = 1754459) B1754459
theorem B7133447 : Blo 778337 7133447 := bstep (se 1 (by rfl) ⟨5350085, by rfl⟩ : syracuseStep 7133447 = 10700171) B10700171
theorem B2218279 : Blo 778337 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B1169819 : Blo 778337 1169819 := bstep (se 1 (by rfl) ⟨877364, by rfl⟩ : syracuseStep 1169819 = 1754729) B1754729
theorem B8870471 : Blo 778337 8870471 := bstep (se 1 (by rfl) ⟨6652853, by rfl⟩ : syracuseStep 8870471 = 13305707) B13305707
theorem B10672793 : Blo 778337 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B76897025 : Blo 778337 76897025 := bstep (se 2 (by rfl) ⟨28836384, by rfl⟩ : syracuseStep 76897025 = 57672769) B57672769
theorem B1170215 : Blo 778337 1170215 := bstep (se 1 (by rfl) ⟨877661, by rfl⟩ : syracuseStep 1170215 = 1755323) B1755323
theorem B1170239 : Blo 778337 1170239 := bstep (se 1 (by rfl) ⟨877679, by rfl⟩ : syracuseStep 1170239 = 1755359) B1755359
theorem B5004251 : Blo 778337 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B1170539 : Blo 778337 1170539 := bstep (se 1 (by rfl) ⟨877904, by rfl⟩ : syracuseStep 1170539 = 1755809) B1755809
theorem B5627015 : Blo 778337 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B1170683 : Blo 778337 1170683 := bstep (se 1 (by rfl) ⟨878012, by rfl⟩ : syracuseStep 1170683 = 1756025) B1756025
theorem B875803 : Blo 778337 875803 := bstep (se 1 (by rfl) ⟨656852, by rfl⟩ : syracuseStep 875803 = 1313705) B1313705
theorem B3333467 : Blo 778337 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B1170779 : Blo 778337 1170779 := bstep (se 1 (by rfl) ⟨878084, by rfl⟩ : syracuseStep 1170779 = 1756169) B1756169
theorem B1170809 : Blo 778337 1170809 := bstep (se 2 (by rfl) ⟨439053, by rfl⟩ : syracuseStep 1170809 = 878107) B878107
theorem B1170815 : Blo 778337 1170815 := bstep (se 1 (by rfl) ⟨878111, by rfl⟩ : syracuseStep 1170815 = 1756223) B1756223
theorem B876271 : Blo 778337 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B1171367 : Blo 778337 1171367 := bstep (se 1 (by rfl) ⟨878525, by rfl⟩ : syracuseStep 1171367 = 1757051) B1757051
theorem B2219987 : Blo 778337 2219987 := bstep (se 1 (by rfl) ⟨1664990, by rfl⟩ : syracuseStep 2219987 = 3329981) B3329981
theorem B1171439 : Blo 778337 1171439 := bstep (se 1 (by rfl) ⟨878579, by rfl⟩ : syracuseStep 1171439 = 1757159) B1757159
theorem B778343 : Blo 778337 778343 := bstep (se 1 (by rfl) ⟨583757, by rfl⟩ : syracuseStep 778343 = 1167515) B1167515
theorem B1171559 : Blo 778337 1171559 := bstep (se 1 (by rfl) ⟨878669, by rfl⟩ : syracuseStep 1171559 = 1757339) B1757339
theorem B1171691 : Blo 778337 1171691 := bstep (se 1 (by rfl) ⟨878768, by rfl⟩ : syracuseStep 1171691 = 1757537) B1757537
theorem B1171751 : Blo 778337 1171751 := bstep (se 1 (by rfl) ⟨878813, by rfl⟩ : syracuseStep 1171751 = 1757627) B1757627
theorem B778911 : Blo 778337 778911 := bstep (se 1 (by rfl) ⟨584183, by rfl⟩ : syracuseStep 778911 = 1168367) B1168367
theorem B1172201 : Blo 778337 1172201 := bstep (se 2 (by rfl) ⟨439575, by rfl⟩ : syracuseStep 1172201 = 879151) B879151
theorem B35971897 : Blo 778337 35971897 := bstep (se 2 (by rfl) ⟨13489461, by rfl⟩ : syracuseStep 35971897 = 26978923) B26978923
theorem B779167 : Blo 778337 779167 := bstep (se 1 (by rfl) ⟨584375, by rfl⟩ : syracuseStep 779167 = 1168751) B1168751
theorem B675668897 : Blo 778337 675668897 := bstep (se 2 (by rfl) ⟨253375836, by rfl⟩ : syracuseStep 675668897 = 506751673) B506751673
theorem B779247 : Blo 778337 779247 := bstep (se 1 (by rfl) ⟨584435, by rfl⟩ : syracuseStep 779247 = 1168871) B1168871
theorem B779355 : Blo 778337 779355 := bstep (se 1 (by rfl) ⟨584516, by rfl⟩ : syracuseStep 779355 = 1169033) B1169033
theorem B779367 : Blo 778337 779367 := bstep (se 1 (by rfl) ⟨584525, by rfl⟩ : syracuseStep 779367 = 1169051) B1169051
theorem B1172591 : Blo 778337 1172591 := bstep (se 1 (by rfl) ⟨879443, by rfl⟩ : syracuseStep 1172591 = 1758887) B1758887
theorem B779495 : Blo 778337 779495 := bstep (se 1 (by rfl) ⟨584621, by rfl⟩ : syracuseStep 779495 = 1169243) B1169243
theorem B1172711 : Blo 778337 1172711 := bstep (se 1 (by rfl) ⟨879533, by rfl⟩ : syracuseStep 1172711 = 1759067) B1759067
theorem B1172777 : Blo 778337 1172777 := bstep (se 2 (by rfl) ⟨439791, by rfl⟩ : syracuseStep 1172777 = 879583) B879583
theorem B144041273 : Blo 778337 144041273 := bstep (se 2 (by rfl) ⟨54015477, by rfl⟩ : syracuseStep 144041273 = 108030955) B108030955
theorem B5334427 : Blo 778337 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B8873387 : Blo 778337 8873387 := bstep (se 1 (by rfl) ⟨6655040, by rfl⟩ : syracuseStep 8873387 = 13310081) B13310081
theorem B779751 : Blo 778337 779751 := bstep (se 1 (by rfl) ⟨584813, by rfl⟩ : syracuseStep 779751 = 1169627) B1169627
theorem B1173047 : Blo 778337 1173047 := bstep (se 1 (by rfl) ⟨879785, by rfl⟩ : syracuseStep 1173047 = 1759571) B1759571
theorem B779931 : Blo 778337 779931 := bstep (se 1 (by rfl) ⟨584948, by rfl⟩ : syracuseStep 779931 = 1169897) B1169897
theorem B4515563 : Blo 778337 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B50652971 : Blo 778337 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B1173371 : Blo 778337 1173371 := bstep (se 1 (by rfl) ⟨880028, by rfl⟩ : syracuseStep 1173371 = 1760057) B1760057
theorem B780191 : Blo 778337 780191 := bstep (se 1 (by rfl) ⟨585143, by rfl⟩ : syracuseStep 780191 = 1170287) B1170287
theorem B1173407 : Blo 778337 1173407 := bstep (se 1 (by rfl) ⟨880055, by rfl⟩ : syracuseStep 1173407 = 1760111) B1760111
theorem B780199 : Blo 778337 780199 := bstep (se 1 (by rfl) ⟨585149, by rfl⟩ : syracuseStep 780199 = 1170299) B1170299
theorem B878503 : Blo 778337 878503 := bstep (se 1 (by rfl) ⟨658877, by rfl⟩ : syracuseStep 878503 = 1317755) B1317755
theorem B2254895 : Blo 778337 2254895 := bstep (se 1 (by rfl) ⟨1691171, by rfl⟩ : syracuseStep 2254895 = 3382343) B3382343
theorem B780775 : Blo 778337 780775 := bstep (se 1 (by rfl) ⟨585581, by rfl⟩ : syracuseStep 780775 = 1171163) B1171163
theorem B879079 : Blo 778337 879079 := bstep (se 1 (by rfl) ⟨659309, by rfl⟩ : syracuseStep 879079 = 1318619) B1318619
theorem B780955 : Blo 778337 780955 := bstep (se 1 (by rfl) ⟨585716, by rfl⟩ : syracuseStep 780955 = 1171433) B1171433
theorem B879259 : Blo 778337 879259 := bstep (se 1 (by rfl) ⟨659444, by rfl⟩ : syracuseStep 879259 = 1318889) B1318889
theorem B146402153 : Blo 778337 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B68283425 : Blo 778337 68283425 := bstep (se 2 (by rfl) ⟨25606284, by rfl⟩ : syracuseStep 68283425 = 51212569) B51212569
theorem B781423 : Blo 778337 781423 := bstep (se 1 (by rfl) ⟨586067, by rfl⟩ : syracuseStep 781423 = 1172135) B1172135
theorem B879727 : Blo 778337 879727 := bstep (se 1 (by rfl) ⟨659795, by rfl⟩ : syracuseStep 879727 = 1319591) B1319591
theorem B781503 : Blo 778337 781503 := bstep (se 1 (by rfl) ⟨586127, by rfl⟩ : syracuseStep 781503 = 1172255) B1172255
theorem B781519 : Blo 778337 781519 := bstep (se 1 (by rfl) ⟨586139, by rfl⟩ : syracuseStep 781519 = 1172279) B1172279
theorem B3960089 : Blo 778337 3960089 := bstep (se 2 (by rfl) ⟨1485033, by rfl⟩ : syracuseStep 3960089 = 2970067) B2970067
theorem B781639 : Blo 778337 781639 := bstep (se 1 (by rfl) ⟨586229, by rfl⟩ : syracuseStep 781639 = 1172459) B1172459
theorem B879943 : Blo 778337 879943 := bstep (se 1 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 879943 = 1319915) B1319915
theorem B3338081 : Blo 778337 3338081 := bstep (se 2 (by rfl) ⟨1251780, by rfl⟩ : syracuseStep 3338081 = 2503561) B2503561
theorem B2813885 : Blo 778337 2813885 := bstep (se 3 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 2813885 = 1055207) B1055207
theorem B7500113 : Blo 778337 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B19984805 : Blo 778337 19984805 := bstep (se 4 (by rfl) ⟨1873575, by rfl⟩ : syracuseStep 19984805 = 3747151) B3747151
theorem B11727523 : Blo 778337 11727523 := bstep (se 1 (by rfl) ⟨8795642, by rfl⟩ : syracuseStep 11727523 = 17591285) B17591285
theorem B5075905 : Blo 778337 5075905 := bstep (se 2 (by rfl) ⟨1903464, by rfl⟩ : syracuseStep 5075905 = 3806929) B3806929
theorem B1111087 : Blo 778337 1111087 := bstep (se 1 (by rfl) ⟨833315, by rfl⟩ : syracuseStep 1111087 = 1666631) B1666631
theorem B4454351 : Blo 778337 4454351 := bstep (se 1 (by rfl) ⟨3340763, by rfl⟩ : syracuseStep 4454351 = 6681527) B6681527
theorem B25294841 : Blo 778337 25294841 := bstep (se 2 (by rfl) ⟨9485565, by rfl⟩ : syracuseStep 25294841 = 18971131) B18971131
theorem B1113115 : Blo 778337 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B8879219 : Blo 778337 8879219 := bstep (se 1 (by rfl) ⟨6659414, by rfl⟩ : syracuseStep 8879219 = 13318829) B13318829
theorem B1408411 : Blo 778337 1408411 := bstep (se 1 (by rfl) ⟨1056308, by rfl⟩ : syracuseStep 1408411 = 2112617) B2112617
theorem B175635985 : Blo 778337 175635985 := bstep (se 2 (by rfl) ⟨65863494, by rfl⟩ : syracuseStep 175635985 = 131726989) B131726989
theorem B4226879 : Blo 778337 4226879 := bstep (se 1 (by rfl) ⟨3170159, by rfl⟩ : syracuseStep 4226879 = 6340319) B6340319
theorem B5931143 : Blo 778337 5931143 := bstep (se 1 (by rfl) ⟨4448357, by rfl⟩ : syracuseStep 5931143 = 8896715) B8896715
theorem B7112569 : Blo 778337 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B985927 : Blo 778337 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B1313759 : Blo 778337 1313759 := bstep (se 1 (by rfl) ⟨985319, by rfl⟩ : syracuseStep 1313759 = 1970639) B1970639
theorem B5934059 : Blo 778337 5934059 := bstep (se 1 (by rfl) ⟨4450544, by rfl⟩ : syracuseStep 5934059 = 8901089) B8901089
theorem B8883593 : Blo 778337 8883593 := bstep (se 2 (by rfl) ⟨3331347, by rfl⟩ : syracuseStep 8883593 = 6662695) B6662695
theorem B986575 : Blo 778337 986575 := bstep (se 1 (by rfl) ⟨739931, by rfl⟩ : syracuseStep 986575 = 1479863) B1479863
theorem B21368357 : Blo 778337 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B1314697 : Blo 778337 1314697 := bstep (se 2 (by rfl) ⟨493011, by rfl⟩ : syracuseStep 1314697 = 986023) B986023
theorem B4755631 : Blo 778337 4755631 := bstep (se 1 (by rfl) ⟨3566723, by rfl⟩ : syracuseStep 4755631 = 7133447) B7133447
theorem B13734173 : Blo 778337 13734173 := bstep (se 3 (by rfl) ⟨2575157, by rfl⟩ : syracuseStep 13734173 = 5150315) B5150315
theorem B987547 : Blo 778337 987547 := bstep (se 1 (by rfl) ⟨740660, by rfl⟩ : syracuseStep 987547 = 1481321) B1481321
theorem B7115195 : Blo 778337 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B1315615 : Blo 778337 1315615 := bstep (se 1 (by rfl) ⟨986711, by rfl⟩ : syracuseStep 1315615 = 1973423) B1973423
theorem B987967 : Blo 778337 987967 := bstep (se 1 (by rfl) ⟨740975, by rfl⟩ : syracuseStep 987967 = 1481951) B1481951
theorem B1316027 : Blo 778337 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B1316459 : Blo 778337 1316459 := bstep (se 1 (by rfl) ⟨987344, by rfl⟩ : syracuseStep 1316459 = 1974689) B1974689
theorem B1971935 : Blo 778337 1971935 := bstep (se 1 (by rfl) ⟨1478951, by rfl⟩ : syracuseStep 1971935 = 2957903) B2957903
theorem B2955305 : Blo 778337 2955305 := bstep (se 2 (by rfl) ⟨1108239, by rfl⟩ : syracuseStep 2955305 = 2216479) B2216479
theorem B2955473 : Blo 778337 2955473 := bstep (se 2 (by rfl) ⟨1108302, by rfl⟩ : syracuseStep 2955473 = 2216605) B2216605
theorem B45522283 : Blo 778337 45522283 := bstep (se 1 (by rfl) ⟨34141712, by rfl⟩ : syracuseStep 45522283 = 68283425) B68283425
theorem B2497999 : Blo 778337 2497999 := bstep (se 1 (by rfl) ⟨1873499, by rfl⟩ : syracuseStep 2497999 = 3746999) B3746999
theorem B7511525 : Blo 778337 7511525 := bstep (se 4 (by rfl) ⟨704205, by rfl⟩ : syracuseStep 7511525 = 1408411) B1408411
theorem B1318511 : Blo 778337 1318511 := bstep (se 1 (by rfl) ⟨988883, by rfl⟩ : syracuseStep 1318511 = 1977767) B1977767
theorem B1875923 : Blo 778337 1875923 := bstep (se 1 (by rfl) ⟨1406942, by rfl⟩ : syracuseStep 1875923 = 2813885) B2813885
theorem B3612647 : Blo 778337 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B2957705 : Blo 778337 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B1319611 : Blo 778337 1319611 := bstep (se 1 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 1319611 = 1979417) B1979417
theorem B1319719 : Blo 778337 1319719 := bstep (se 1 (by rfl) ⟨989789, by rfl⟩ : syracuseStep 1319719 = 1979579) B1979579
theorem B1484153 : Blo 778337 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B7612537 : Blo 778337 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B12658835 : Blo 778337 12658835 := bstep (se 1 (by rfl) ⟨9494126, by rfl⟩ : syracuseStep 12658835 = 18988253) B18988253
theorem B2959679 : Blo 778337 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B2959847 : Blo 778337 2959847 := bstep (se 1 (by rfl) ⟨2219885, by rfl⟩ : syracuseStep 2959847 = 4439771) B4439771
theorem B2632607 : Blo 778337 2632607 := bstep (se 1 (by rfl) ⟨1974455, by rfl⟩ : syracuseStep 2632607 = 3948911) B3948911
theorem B2371103 : Blo 778337 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B2502191 : Blo 778337 2502191 := bstep (se 1 (by rfl) ⟨1876643, by rfl⟩ : syracuseStep 2502191 = 3753287) B3753287
theorem B47984237 : Blo 778337 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B6664031 : Blo 778337 6664031 := bstep (se 1 (by rfl) ⟨4998023, by rfl⟩ : syracuseStep 6664031 = 9996047) B9996047
theorem B832231 : Blo 778337 832231 := bstep (se 1 (by rfl) ⟨624173, by rfl⟩ : syracuseStep 832231 = 1248347) B1248347
theorem B2634551 : Blo 778337 2634551 := bstep (se 1 (by rfl) ⟨1975913, by rfl⟩ : syracuseStep 2634551 = 3951827) B3951827
theorem B2635145 : Blo 778337 2635145 := bstep (se 2 (by rfl) ⟨988179, by rfl⟩ : syracuseStep 2635145 = 1976359) B1976359
theorem B9975797 : Blo 778337 9975797 := bstep (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) B935231
theorem B11221739 : Blo 778337 11221739 := bstep (se 1 (by rfl) ⟨8416304, by rfl⟩ : syracuseStep 11221739 = 16832609) B16832609
theorem B5913647 : Blo 778337 5913647 := bstep (se 1 (by rfl) ⟨4435235, by rfl⟩ : syracuseStep 5913647 = 8870471) B8870471
theorem B51264683 : Blo 778337 51264683 := bstep (se 1 (by rfl) ⟨38448512, by rfl⟩ : syracuseStep 51264683 = 76897025) B76897025
theorem B7486769 : Blo 778337 7486769 := bstep (se 2 (by rfl) ⟨2807538, by rfl⟩ : syracuseStep 7486769 = 5615077) B5615077
theorem B3751343 : Blo 778337 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B3325607 : Blo 778337 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B1753001 : Blo 778337 1753001 := bstep (se 2 (by rfl) ⟨657375, by rfl⟩ : syracuseStep 1753001 = 1314751) B1314751
theorem B2637953 : Blo 778337 2637953 := bstep (se 2 (by rfl) ⟨989232, by rfl⟩ : syracuseStep 2637953 = 1978465) B1978465
theorem B1753343 : Blo 778337 1753343 := bstep (se 1 (by rfl) ⟨1315007, by rfl⟩ : syracuseStep 1753343 = 2630015) B2630015
theorem B450445931 : Blo 778337 450445931 := bstep (se 1 (by rfl) ⟨337834448, by rfl⟩ : syracuseStep 450445931 = 675668897) B675668897
theorem B96027515 : Blo 778337 96027515 := bstep (se 1 (by rfl) ⟨72020636, by rfl⟩ : syracuseStep 96027515 = 144041273) B144041273
theorem B5915591 : Blo 778337 5915591 := bstep (se 1 (by rfl) ⟨4436693, by rfl⟩ : syracuseStep 5915591 = 8873387) B8873387
theorem B1754279 : Blo 778337 1754279 := bstep (se 1 (by rfl) ⟨1315709, by rfl⟩ : syracuseStep 1754279 = 2631419) B2631419
theorem B33768647 : Blo 778337 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B6767873 : Blo 778337 6767873 := bstep (se 2 (by rfl) ⟨2537952, by rfl⟩ : syracuseStep 6767873 = 5075905) B5075905
theorem B2639465 : Blo 778337 2639465 := bstep (se 2 (by rfl) ⟨989799, by rfl⟩ : syracuseStep 2639465 = 1979599) B1979599
theorem B97601435 : Blo 778337 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B2639897 : Blo 778337 2639897 := bstep (se 2 (by rfl) ⟨989961, by rfl⟩ : syracuseStep 2639897 = 1979923) B1979923
theorem B2640059 : Blo 778337 2640059 := bstep (se 1 (by rfl) ⟨1980044, by rfl⟩ : syracuseStep 2640059 = 3960089) B3960089
theorem B1427681 : Blo 778337 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B24365299 : Blo 778337 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B4442435 : Blo 778337 4442435 := bstep (se 1 (by rfl) ⟨3331826, by rfl⟩ : syracuseStep 4442435 = 6663653) B6663653
theorem B3328735 : Blo 778337 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B3328751 : Blo 778337 3328751 := bstep (se 1 (by rfl) ⟨2496563, by rfl⟩ : syracuseStep 3328751 = 4993127) B4993127
theorem B1756007 : Blo 778337 1756007 := bstep (se 1 (by rfl) ⟨1317005, by rfl⟩ : syracuseStep 1756007 = 2634011) B2634011
theorem B5000075 : Blo 778337 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B13323203 : Blo 778337 13323203 := bstep (se 1 (by rfl) ⟨9992402, by rfl⟩ : syracuseStep 13323203 = 19984805) B19984805
theorem B4508783 : Blo 778337 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B49270139 : Blo 778337 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B16895395 : Blo 778337 16895395 := bstep (se 1 (by rfl) ⟨12671546, by rfl⟩ : syracuseStep 16895395 = 25343093) B25343093
theorem B3952313 : Blo 778337 3952313 := bstep (se 2 (by rfl) ⟨1482117, by rfl⟩ : syracuseStep 3952313 = 2964235) B2964235
theorem B2969567 : Blo 778337 2969567 := bstep (se 1 (by rfl) ⟨2227175, by rfl⟩ : syracuseStep 2969567 = 4454351) B4454351
theorem B1757177 : Blo 778337 1757177 := bstep (se 2 (by rfl) ⟨658941, by rfl⟩ : syracuseStep 1757177 = 1317883) B1317883
theorem B16863227 : Blo 778337 16863227 := bstep (se 1 (by rfl) ⟨12647420, by rfl⟩ : syracuseStep 16863227 = 25294841) B25294841
theorem B1167551 : Blo 778337 1167551 := bstep (se 1 (by rfl) ⟨875663, by rfl⟩ : syracuseStep 1167551 = 1751327) B1751327
theorem B1167695 : Blo 778337 1167695 := bstep (se 1 (by rfl) ⟨875771, by rfl⟩ : syracuseStep 1167695 = 1751543) B1751543
theorem B1167737 : Blo 778337 1167737 := bstep (se 2 (by rfl) ⟨437901, by rfl⟩ : syracuseStep 1167737 = 875803) B875803
theorem B1757609 : Blo 778337 1757609 := bstep (se 2 (by rfl) ⟨659103, by rfl⟩ : syracuseStep 1757609 = 1318207) B1318207
theorem B2675207 : Blo 778337 2675207 := bstep (se 1 (by rfl) ⟨2006405, by rfl⟩ : syracuseStep 2675207 = 4012811) B4012811
theorem B1757753 : Blo 778337 1757753 := bstep (se 2 (by rfl) ⟨659157, by rfl⟩ : syracuseStep 1757753 = 1318315) B1318315
theorem B1168031 : Blo 778337 1168031 := bstep (se 1 (by rfl) ⟨876023, by rfl⟩ : syracuseStep 1168031 = 1752047) B1752047
theorem B234181313 : Blo 778337 234181313 := bstep (se 2 (by rfl) ⟨87817992, by rfl⟩ : syracuseStep 234181313 = 175635985) B175635985
theorem B1757915 : Blo 778337 1757915 := bstep (se 1 (by rfl) ⟨1318436, by rfl⟩ : syracuseStep 1757915 = 2636873) B2636873
theorem B5919479 : Blo 778337 5919479 := bstep (se 1 (by rfl) ⟨4439609, by rfl⟩ : syracuseStep 5919479 = 8879219) B8879219
theorem B1168361 : Blo 778337 1168361 := bstep (se 2 (by rfl) ⟨438135, by rfl⟩ : syracuseStep 1168361 = 876271) B876271
theorem B1168415 : Blo 778337 1168415 := bstep (se 1 (by rfl) ⟨876311, by rfl⟩ : syracuseStep 1168415 = 1752623) B1752623
theorem B1758311 : Blo 778337 1758311 := bstep (se 1 (by rfl) ⟨1318733, by rfl⟩ : syracuseStep 1758311 = 2637467) B2637467
theorem B5919965 : Blo 778337 5919965 := bstep (se 3 (by rfl) ⟨1109993, by rfl⟩ : syracuseStep 5919965 = 2219987) B2219987
theorem B1758473 : Blo 778337 1758473 := bstep (se 2 (by rfl) ⟨659427, by rfl⟩ : syracuseStep 1758473 = 1318855) B1318855
theorem B1168703 : Blo 778337 1168703 := bstep (se 1 (by rfl) ⟨876527, by rfl⟩ : syracuseStep 1168703 = 1753055) B1753055
theorem B5625341 : Blo 778337 5625341 := bstep (se 3 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 5625341 = 2109503) B2109503
theorem B3954257 : Blo 778337 3954257 := bstep (se 2 (by rfl) ⟨1482846, by rfl⟩ : syracuseStep 3954257 = 2965693) B2965693
theorem B8443547 : Blo 778337 8443547 := bstep (se 1 (by rfl) ⟨6332660, by rfl⟩ : syracuseStep 8443547 = 12665321) B12665321
theorem B3331793 : Blo 778337 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B3954419 : Blo 778337 3954419 := bstep (se 1 (by rfl) ⟨2965814, by rfl⟩ : syracuseStep 3954419 = 5931629) B5931629
theorem B1759175 : Blo 778337 1759175 := bstep (se 1 (by rfl) ⟨1319381, by rfl⟩ : syracuseStep 1759175 = 2638763) B2638763
theorem B1759535 : Blo 778337 1759535 := bstep (se 1 (by rfl) ⟨1319651, by rfl⟩ : syracuseStep 1759535 = 2639303) B2639303
theorem B47962529 : Blo 778337 47962529 := bstep (se 2 (by rfl) ⟨17985948, by rfl⟩ : syracuseStep 47962529 = 35971897) B35971897
theorem B1759751 : Blo 778337 1759751 := bstep (se 1 (by rfl) ⟨1319813, by rfl⟩ : syracuseStep 1759751 = 2639627) B2639627
theorem B1171337 : Blo 778337 1171337 := bstep (se 2 (by rfl) ⟨439251, by rfl⟩ : syracuseStep 1171337 = 878503) B878503
theorem B1171487 : Blo 778337 1171487 := bstep (se 1 (by rfl) ⟨878615, by rfl⟩ : syracuseStep 1171487 = 1757231) B1757231
theorem B1663163 : Blo 778337 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B778567 : Blo 778337 778567 := bstep (se 1 (by rfl) ⟨583925, by rfl⟩ : syracuseStep 778567 = 1167851) B1167851
theorem B778651 : Blo 778337 778651 := bstep (se 1 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 778651 = 1167977) B1167977
theorem B778655 : Blo 778337 778655 := bstep (se 1 (by rfl) ⟨583991, by rfl⟩ : syracuseStep 778655 = 1167983) B1167983
theorem B1171871 : Blo 778337 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B778735 : Blo 778337 778735 := bstep (se 1 (by rfl) ⟨584051, by rfl⟩ : syracuseStep 778735 = 1168103) B1168103
theorem B778843 : Blo 778337 778843 := bstep (se 1 (by rfl) ⟨584132, by rfl⟩ : syracuseStep 778843 = 1168265) B1168265
theorem B1172105 : Blo 778337 1172105 := bstep (se 2 (by rfl) ⟨439539, by rfl⟩ : syracuseStep 1172105 = 879079) B879079
theorem B779071 : Blo 778337 779071 := bstep (se 1 (by rfl) ⟨584303, by rfl⟩ : syracuseStep 779071 = 1168607) B1168607
theorem B779099 : Blo 778337 779099 := bstep (se 1 (by rfl) ⟨584324, by rfl⟩ : syracuseStep 779099 = 1168649) B1168649
theorem B62546789 : Blo 778337 62546789 := bstep (se 4 (by rfl) ⟨5863761, by rfl⟩ : syracuseStep 62546789 = 11727523) B11727523
theorem B1172345 : Blo 778337 1172345 := bstep (se 2 (by rfl) ⟨439629, by rfl⟩ : syracuseStep 1172345 = 879259) B879259
theorem B2843681 : Blo 778337 2843681 := bstep (se 2 (by rfl) ⟨1066380, by rfl⟩ : syracuseStep 2843681 = 2132761) B2132761
theorem B779391 : Blo 778337 779391 := bstep (se 1 (by rfl) ⟨584543, by rfl⟩ : syracuseStep 779391 = 1169087) B1169087
theorem B779419 : Blo 778337 779419 := bstep (se 1 (by rfl) ⟨584564, by rfl⟩ : syracuseStep 779419 = 1169129) B1169129
theorem B779423 : Blo 778337 779423 := bstep (se 1 (by rfl) ⟨584567, by rfl⟩ : syracuseStep 779423 = 1169135) B1169135
theorem B1172639 : Blo 778337 1172639 := bstep (se 1 (by rfl) ⟨879479, by rfl⟩ : syracuseStep 1172639 = 1758959) B1758959
theorem B2221469 : Blo 778337 2221469 := bstep (se 3 (by rfl) ⟨416525, by rfl⟩ : syracuseStep 2221469 = 833051) B833051
theorem B1172969 : Blo 778337 1172969 := bstep (se 2 (by rfl) ⟨439863, by rfl⟩ : syracuseStep 1172969 = 879727) B879727
theorem B779759 : Blo 778337 779759 := bstep (se 1 (by rfl) ⟨584819, by rfl⟩ : syracuseStep 779759 = 1169639) B1169639
theorem B779879 : Blo 778337 779879 := bstep (se 1 (by rfl) ⟨584909, by rfl⟩ : syracuseStep 779879 = 1169819) B1169819
theorem B1173257 : Blo 778337 1173257 := bstep (se 2 (by rfl) ⟨439971, by rfl⟩ : syracuseStep 1173257 = 879943) B879943
theorem B780143 : Blo 778337 780143 := bstep (se 1 (by rfl) ⟨585107, by rfl⟩ : syracuseStep 780143 = 1170215) B1170215
theorem B780159 : Blo 778337 780159 := bstep (se 1 (by rfl) ⟨585119, by rfl⟩ : syracuseStep 780159 = 1170239) B1170239
theorem B3336167 : Blo 778337 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B780359 : Blo 778337 780359 := bstep (se 1 (by rfl) ⟨585269, by rfl⟩ : syracuseStep 780359 = 1170539) B1170539
theorem B780455 : Blo 778337 780455 := bstep (se 1 (by rfl) ⟨585341, by rfl⟩ : syracuseStep 780455 = 1170683) B1170683
theorem B2222311 : Blo 778337 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B780519 : Blo 778337 780519 := bstep (se 1 (by rfl) ⟨585389, by rfl⟩ : syracuseStep 780519 = 1170779) B1170779
theorem B780539 : Blo 778337 780539 := bstep (se 1 (by rfl) ⟨585404, by rfl⟩ : syracuseStep 780539 = 1170809) B1170809
theorem B780543 : Blo 778337 780543 := bstep (se 1 (by rfl) ⟨585407, by rfl⟩ : syracuseStep 780543 = 1170815) B1170815
theorem B3959279 : Blo 778337 3959279 := bstep (se 1 (by rfl) ⟨2969459, by rfl⟩ : syracuseStep 3959279 = 5938919) B5938919
theorem B780911 : Blo 778337 780911 := bstep (se 1 (by rfl) ⟨585683, by rfl⟩ : syracuseStep 780911 = 1171367) B1171367
theorem B780959 : Blo 778337 780959 := bstep (se 1 (by rfl) ⟨585719, by rfl⟩ : syracuseStep 780959 = 1171439) B1171439
theorem B781039 : Blo 778337 781039 := bstep (se 1 (by rfl) ⟨585779, by rfl⟩ : syracuseStep 781039 = 1171559) B1171559
theorem B781127 : Blo 778337 781127 := bstep (se 1 (by rfl) ⟨585845, by rfl⟩ : syracuseStep 781127 = 1171691) B1171691
theorem B781167 : Blo 778337 781167 := bstep (se 1 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 781167 = 1171751) B1171751
theorem B5925797 : Blo 778337 5925797 := bstep (se 4 (by rfl) ⟨555543, by rfl⟩ : syracuseStep 5925797 = 1111087) B1111087
theorem B5008351 : Blo 778337 5008351 := bstep (se 1 (by rfl) ⟨3756263, by rfl⟩ : syracuseStep 5008351 = 7512527) B7512527
theorem B781467 : Blo 778337 781467 := bstep (se 1 (by rfl) ⟨586100, by rfl⟩ : syracuseStep 781467 = 1172201) B1172201
theorem B781727 : Blo 778337 781727 := bstep (se 1 (by rfl) ⟨586295, by rfl⟩ : syracuseStep 781727 = 1172591) B1172591
theorem B781807 : Blo 778337 781807 := bstep (se 1 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 781807 = 1172711) B1172711
theorem B781851 : Blo 778337 781851 := bstep (se 1 (by rfl) ⟨586388, by rfl⟩ : syracuseStep 781851 = 1172777) B1172777
theorem B782031 : Blo 778337 782031 := bstep (se 1 (by rfl) ⟨586523, by rfl⟩ : syracuseStep 782031 = 1173047) B1173047
theorem B3010375 : Blo 778337 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B1666939 : Blo 778337 1666939 := bstep (se 1 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 1666939 = 2500409) B2500409
theorem B782247 : Blo 778337 782247 := bstep (se 1 (by rfl) ⟨586685, by rfl⟩ : syracuseStep 782247 = 1173371) B1173371
theorem B782271 : Blo 778337 782271 := bstep (se 1 (by rfl) ⟨586703, by rfl⟩ : syracuseStep 782271 = 1173407) B1173407
theorem B1503263 : Blo 778337 1503263 := bstep (se 1 (by rfl) ⟨1127447, by rfl⟩ : syracuseStep 1503263 = 2254895) B2254895
theorem B3338729 : Blo 778337 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B3765467 : Blo 778337 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B2225387 : Blo 778337 2225387 := bstep (se 1 (by rfl) ⟨1669040, by rfl⟩ : syracuseStep 2225387 = 3338081) B3338081
theorem B12809711 : Blo 778337 12809711 := bstep (se 1 (by rfl) ⟨9607283, by rfl⟩ : syracuseStep 12809711 = 19214567) B19214567
theorem B1603451 : Blo 778337 1603451 := bstep (se 1 (by rfl) ⟨1202588, by rfl⟩ : syracuseStep 1603451 = 2405177) B2405177
theorem B1734967 : Blo 778337 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B2850023 : Blo 778337 2850023 := bstep (se 1 (by rfl) ⟨2137517, by rfl⟩ : syracuseStep 2850023 = 4275035) B4275035
theorem B6651557 : Blo 778337 6651557 := bstep (se 4 (by rfl) ⟨623583, by rfl⟩ : syracuseStep 6651557 = 1247167) B1247167
theorem B2817919 : Blo 778337 2817919 := bstep (se 1 (by rfl) ⟨2113439, by rfl⟩ : syracuseStep 2817919 = 4226879) B4226879
theorem B22512431 : Blo 778337 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B951787 : Blo 778337 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B8882135 : Blo 778337 8882135 := bstep (se 1 (by rfl) ⟨6661601, by rfl⟩ : syracuseStep 8882135 = 13323203) B13323203
theorem B166791437 : Blo 778337 166791437 := bstep (se 3 (by rfl) ⟨31273394, by rfl⟩ : syracuseStep 166791437 = 62546789) B62546789
theorem B11242151 : Blo 778337 11242151 := bstep (se 1 (by rfl) ⟨8431613, by rfl⟩ : syracuseStep 11242151 = 16863227) B16863227
theorem B1314569 : Blo 778337 1314569 := bstep (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) B985927
theorem B1314623 : Blo 778337 1314623 := bstep (se 1 (by rfl) ⟨985967, by rfl⟩ : syracuseStep 1314623 = 1971935) B1971935
theorem B1970203 : Blo 778337 1970203 := bstep (se 1 (by rfl) ⟨1477652, by rfl⟩ : syracuseStep 1970203 = 2955305) B2955305
theorem B1970315 : Blo 778337 1970315 := bstep (se 1 (by rfl) ⟨1477736, by rfl⟩ : syracuseStep 1970315 = 2955473) B2955473
theorem B1315433 : Blo 778337 1315433 := bstep (se 2 (by rfl) ⟨493287, by rfl⟩ : syracuseStep 1315433 = 986575) B986575
theorem B1250615 : Blo 778337 1250615 := bstep (se 1 (by rfl) ⟨937961, by rfl⟩ : syracuseStep 1250615 = 1875923) B1875923
theorem B1971803 : Blo 778337 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B1316729 : Blo 778337 1316729 := bstep (se 2 (by rfl) ⟨493773, by rfl⟩ : syracuseStep 1316729 = 987547) B987547
theorem B989435 : Blo 778337 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B1480979 : Blo 778337 1480979 := bstep (se 1 (by rfl) ⟨1110734, by rfl⟩ : syracuseStep 1480979 = 2221469) B2221469
theorem B1317289 : Blo 778337 1317289 := bstep (se 2 (by rfl) ⟨493983, by rfl⟩ : syracuseStep 1317289 = 987967) B987967
theorem B1973119 : Blo 778337 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B1973231 : Blo 778337 1973231 := bstep (se 1 (by rfl) ⟨1479923, by rfl⟩ : syracuseStep 1973231 = 2959847) B2959847
theorem B1580735 : Blo 778337 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B31989491 : Blo 778337 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B1483591 : Blo 778337 1483591 := bstep (se 1 (by rfl) ⟨1112693, by rfl⟩ : syracuseStep 1483591 = 2225387) B2225387
theorem B60696377 : Blo 778337 60696377 := bstep (se 2 (by rfl) ⟨22761141, by rfl⟩ : syracuseStep 60696377 = 45522283) B45522283
theorem B7481159 : Blo 778337 7481159 := bstep (se 1 (by rfl) ⟨5610869, by rfl⟩ : syracuseStep 7481159 = 11221739) B11221739
theorem B3942431 : Blo 778337 3942431 := bstep (se 1 (by rfl) ⟨2956823, by rfl⟩ : syracuseStep 3942431 = 5913647) B5913647
theorem B4991179 : Blo 778337 4991179 := bstep (se 1 (by rfl) ⟨3743384, by rfl⟩ : syracuseStep 4991179 = 7486769) B7486769
theorem B2500895 : Blo 778337 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B4434371 : Blo 778337 4434371 := bstep (se 1 (by rfl) ⟨3325778, by rfl⟩ : syracuseStep 4434371 = 6651557) B6651557
theorem B4008701 : Blo 778337 4008701 := bstep (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) B1503263
theorem B300297287 : Blo 778337 300297287 := bstep (se 1 (by rfl) ⟨225222965, by rfl⟩ : syracuseStep 300297287 = 450445931) B450445931
theorem B3943727 : Blo 778337 3943727 := bstep (se 1 (by rfl) ⟨2957795, by rfl⟩ : syracuseStep 3943727 = 5915591) B5915591
theorem B2961623 : Blo 778337 2961623 := bstep (se 1 (by rfl) ⟨2221217, by rfl⟩ : syracuseStep 2961623 = 4442435) B4442435
theorem B32846759 : Blo 778337 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B2634875 : Blo 778337 2634875 := bstep (se 1 (by rfl) ⟨1976156, by rfl⟩ : syracuseStep 2634875 = 3952313) B3952313
theorem B9483425 : Blo 778337 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B1979711 : Blo 778337 1979711 := bstep (se 1 (by rfl) ⟨1484783, by rfl⟩ : syracuseStep 1979711 = 2969567) B2969567
theorem B7583149 : Blo 778337 7583149 := bstep (se 3 (by rfl) ⟨1421840, by rfl⟩ : syracuseStep 7583149 = 2843681) B2843681
theorem B9156115 : Blo 778337 9156115 := bstep (se 1 (by rfl) ⟨6867086, by rfl⟩ : syracuseStep 9156115 = 13734173) B13734173
theorem B2963081 : Blo 778337 2963081 := bstep (se 2 (by rfl) ⟨1111155, by rfl⟩ : syracuseStep 2963081 = 2222311) B2222311
theorem B32487065 : Blo 778337 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B1783471 : Blo 778337 1783471 := bstep (se 1 (by rfl) ⟨1337603, by rfl⟩ : syracuseStep 1783471 = 2675207) B2675207
theorem B156120875 : Blo 778337 156120875 := bstep (se 1 (by rfl) ⟨117090656, by rfl⟩ : syracuseStep 156120875 = 234181313) B234181313
theorem B3946319 : Blo 778337 3946319 := bstep (se 1 (by rfl) ⟨2959739, by rfl⟩ : syracuseStep 3946319 = 5919479) B5919479
theorem B10041245 : Blo 778337 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B3946643 : Blo 778337 3946643 := bstep (se 1 (by rfl) ⟨2959982, by rfl⟩ : syracuseStep 3946643 = 5919965) B5919965
theorem B4438313 : Blo 778337 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B3750227 : Blo 778337 3750227 := bstep (se 1 (by rfl) ⟨2812670, by rfl⟩ : syracuseStep 3750227 = 5625341) B5625341
theorem B2636171 : Blo 778337 2636171 := bstep (se 1 (by rfl) ⟨1977128, by rfl⟩ : syracuseStep 2636171 = 3954257) B3954257
theorem B2636279 : Blo 778337 2636279 := bstep (se 1 (by rfl) ⟨1977209, by rfl⟩ : syracuseStep 2636279 = 3954419) B3954419
theorem B34159229 : Blo 778337 34159229 := bstep (se 3 (by rfl) ⟨6404855, by rfl⟩ : syracuseStep 34159229 = 12809711) B12809711
theorem B22527193 : Blo 778337 22527193 := bstep (se 2 (by rfl) ⟨8447697, by rfl⟩ : syracuseStep 22527193 = 16895395) B16895395
theorem B1752929 : Blo 778337 1752929 := bstep (se 2 (by rfl) ⟨657348, by rfl⟩ : syracuseStep 1752929 = 1314697) B1314697
theorem B6340841 : Blo 778337 6340841 := bstep (se 2 (by rfl) ⟨2377815, by rfl⟩ : syracuseStep 6340841 = 4755631) B4755631
theorem B1754153 : Blo 778337 1754153 := bstep (se 2 (by rfl) ⟨657807, by rfl⟩ : syracuseStep 1754153 = 1315615) B1315615
theorem B8439223 : Blo 778337 8439223 := bstep (se 1 (by rfl) ⟨6329417, by rfl⟩ : syracuseStep 8439223 = 12658835) B12658835
theorem B2639519 : Blo 778337 2639519 := bstep (se 1 (by rfl) ⟨1979639, by rfl⟩ : syracuseStep 2639519 = 3959279) B3959279
theorem B1755071 : Blo 778337 1755071 := bstep (se 1 (by rfl) ⟨1316303, by rfl⟩ : syracuseStep 1755071 = 2632607) B2632607
theorem B3950531 : Blo 778337 3950531 := bstep (se 1 (by rfl) ⟨2962898, by rfl⟩ : syracuseStep 3950531 = 5925797) B5925797
theorem B4442687 : Blo 778337 4442687 := bstep (se 1 (by rfl) ⟨3332015, by rfl⟩ : syracuseStep 4442687 = 6664031) B6664031
theorem B2313289 : Blo 778337 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B1756367 : Blo 778337 1756367 := bstep (se 1 (by rfl) ⟨1317275, by rfl⟩ : syracuseStep 1756367 = 2634551) B2634551
theorem B1756763 : Blo 778337 1756763 := bstep (se 1 (by rfl) ⟨1317572, by rfl⟩ : syracuseStep 1756763 = 2635145) B2635145
theorem B1068967 : Blo 778337 1068967 := bstep (se 1 (by rfl) ⟨801725, by rfl⟩ : syracuseStep 1068967 = 1603451) B1603451
theorem B3330665 : Blo 778337 3330665 := bstep (se 2 (by rfl) ⟨1248999, by rfl⟩ : syracuseStep 3330665 = 2497999) B2497999
theorem B2217071 : Blo 778337 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B3757225 : Blo 778337 3757225 := bstep (se 2 (by rfl) ⟨1408959, by rfl⟩ : syracuseStep 3757225 = 2817919) B2817919
theorem B1168667 : Blo 778337 1168667 := bstep (se 1 (by rfl) ⟨876500, by rfl⟩ : syracuseStep 1168667 = 1753001) B1753001
theorem B1758635 : Blo 778337 1758635 := bstep (se 1 (by rfl) ⟨1318976, by rfl⟩ : syracuseStep 1758635 = 2637953) B2637953
theorem B3954095 : Blo 778337 3954095 := bstep (se 1 (by rfl) ⟨2965571, by rfl⟩ : syracuseStep 3954095 = 5931143) B5931143
theorem B1168895 : Blo 778337 1168895 := bstep (se 1 (by rfl) ⟨876671, by rfl⟩ : syracuseStep 1168895 = 1753343) B1753343
theorem B64018343 : Blo 778337 64018343 := bstep (se 1 (by rfl) ⟨48013757, by rfl⟩ : syracuseStep 64018343 = 96027515) B96027515
theorem B1169519 : Blo 778337 1169519 := bstep (se 1 (by rfl) ⟨877139, by rfl⟩ : syracuseStep 1169519 = 1754279) B1754279
theorem B4511915 : Blo 778337 4511915 := bstep (se 1 (by rfl) ⟨3383936, by rfl⟩ : syracuseStep 4511915 = 6767873) B6767873
theorem B1759481 : Blo 778337 1759481 := bstep (se 2 (by rfl) ⟨659805, by rfl⟩ : syracuseStep 1759481 = 1319611) B1319611
theorem B1759625 : Blo 778337 1759625 := bstep (se 2 (by rfl) ⟨659859, by rfl⟩ : syracuseStep 1759625 = 1319719) B1319719
theorem B1759643 : Blo 778337 1759643 := bstep (se 1 (by rfl) ⟨1319732, by rfl⟩ : syracuseStep 1759643 = 2639465) B2639465
theorem B65067623 : Blo 778337 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B1759931 : Blo 778337 1759931 := bstep (se 1 (by rfl) ⟨1319948, by rfl⟩ : syracuseStep 1759931 = 2639897) B2639897
theorem B1760039 : Blo 778337 1760039 := bstep (se 1 (by rfl) ⟨1320029, by rfl⟩ : syracuseStep 1760039 = 2640059) B2640059
theorem B2219167 : Blo 778337 2219167 := bstep (se 1 (by rfl) ⟨1664375, by rfl⟩ : syracuseStep 2219167 = 3328751) B3328751
theorem B1170671 : Blo 778337 1170671 := bstep (se 1 (by rfl) ⟨878003, by rfl⟩ : syracuseStep 1170671 = 1756007) B1756007
theorem B3333383 : Blo 778337 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B875839 : Blo 778337 875839 := bstep (se 1 (by rfl) ⟨656879, by rfl⟩ : syracuseStep 875839 = 1313759) B1313759
theorem B3956039 : Blo 778337 3956039 := bstep (se 1 (by rfl) ⟨2967029, by rfl⟩ : syracuseStep 3956039 = 5934059) B5934059
theorem B3005855 : Blo 778337 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B5922395 : Blo 778337 5922395 := bstep (se 1 (by rfl) ⟨4441796, by rfl⟩ : syracuseStep 5922395 = 8883593) B8883593
theorem B14245571 : Blo 778337 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B1171451 : Blo 778337 1171451 := bstep (se 1 (by rfl) ⟨878588, by rfl⟩ : syracuseStep 1171451 = 1757177) B1757177
theorem B778367 : Blo 778337 778367 := bstep (se 1 (by rfl) ⟨583775, by rfl⟩ : syracuseStep 778367 = 1167551) B1167551
theorem B10150049 : Blo 778337 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B778463 : Blo 778337 778463 := bstep (se 1 (by rfl) ⟨583847, by rfl⟩ : syracuseStep 778463 = 1167695) B1167695
theorem B778491 : Blo 778337 778491 := bstep (se 1 (by rfl) ⟨583868, by rfl⟩ : syracuseStep 778491 = 1167737) B1167737
theorem B1171739 : Blo 778337 1171739 := bstep (se 1 (by rfl) ⟨878804, by rfl⟩ : syracuseStep 1171739 = 1757609) B1757609
theorem B4743463 : Blo 778337 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B1171835 : Blo 778337 1171835 := bstep (se 1 (by rfl) ⟨878876, by rfl⟩ : syracuseStep 1171835 = 1757753) B1757753
theorem B778687 : Blo 778337 778687 := bstep (se 1 (by rfl) ⟨584015, by rfl⟩ : syracuseStep 778687 = 1168031) B1168031
theorem B1171943 : Blo 778337 1171943 := bstep (se 1 (by rfl) ⟨878957, by rfl⟩ : syracuseStep 1171943 = 1757915) B1757915
theorem B778907 : Blo 778337 778907 := bstep (se 1 (by rfl) ⟨584180, by rfl⟩ : syracuseStep 778907 = 1168361) B1168361
theorem B778943 : Blo 778337 778943 := bstep (se 1 (by rfl) ⟨584207, by rfl⟩ : syracuseStep 778943 = 1168415) B1168415
theorem B1172207 : Blo 778337 1172207 := bstep (se 1 (by rfl) ⟨879155, by rfl⟩ : syracuseStep 1172207 = 1758311) B1758311
theorem B877351 : Blo 778337 877351 := bstep (se 1 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 877351 = 1316027) B1316027
theorem B1172315 : Blo 778337 1172315 := bstep (se 1 (by rfl) ⟨879236, by rfl⟩ : syracuseStep 1172315 = 1758473) B1758473
theorem B779135 : Blo 778337 779135 := bstep (se 1 (by rfl) ⟨584351, by rfl⟩ : syracuseStep 779135 = 1168703) B1168703
theorem B877639 : Blo 778337 877639 := bstep (se 1 (by rfl) ⟨658229, by rfl⟩ : syracuseStep 877639 = 1316459) B1316459
theorem B5629031 : Blo 778337 5629031 := bstep (se 1 (by rfl) ⟨4221773, by rfl⟩ : syracuseStep 5629031 = 8443547) B8443547
theorem B2221195 : Blo 778337 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B6677801 : Blo 778337 6677801 := bstep (se 2 (by rfl) ⟨2504175, by rfl⟩ : syracuseStep 6677801 = 5008351) B5008351
theorem B1172783 : Blo 778337 1172783 := bstep (se 1 (by rfl) ⟨879587, by rfl⟩ : syracuseStep 1172783 = 1759175) B1759175
theorem B1173023 : Blo 778337 1173023 := bstep (se 1 (by rfl) ⟨879767, by rfl⟩ : syracuseStep 1173023 = 1759535) B1759535
theorem B31975019 : Blo 778337 31975019 := bstep (se 1 (by rfl) ⟨23981264, by rfl⟩ : syracuseStep 31975019 = 47962529) B47962529
theorem B1173167 : Blo 778337 1173167 := bstep (se 1 (by rfl) ⟨879875, by rfl⟩ : syracuseStep 1173167 = 1759751) B1759751
theorem B5007683 : Blo 778337 5007683 := bstep (se 1 (by rfl) ⟨3755762, by rfl⟩ : syracuseStep 5007683 = 7511525) B7511525
theorem B879007 : Blo 778337 879007 := bstep (se 1 (by rfl) ⟨659255, by rfl⟩ : syracuseStep 879007 = 1318511) B1318511
theorem B2222585 : Blo 778337 2222585 := bstep (se 2 (by rfl) ⟨833469, by rfl⟩ : syracuseStep 2222585 = 1666939) B1666939
theorem B780891 : Blo 778337 780891 := bstep (se 1 (by rfl) ⟨585668, by rfl⟩ : syracuseStep 780891 = 1171337) B1171337
theorem B780991 : Blo 778337 780991 := bstep (se 1 (by rfl) ⟨585743, by rfl⟩ : syracuseStep 780991 = 1171487) B1171487
theorem B1108775 : Blo 778337 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B781247 : Blo 778337 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B781403 : Blo 778337 781403 := bstep (se 1 (by rfl) ⟨586052, by rfl⟩ : syracuseStep 781403 = 1172105) B1172105
theorem B781563 : Blo 778337 781563 := bstep (se 1 (by rfl) ⟨586172, by rfl⟩ : syracuseStep 781563 = 1172345) B1172345
theorem B781759 : Blo 778337 781759 := bstep (se 1 (by rfl) ⟨586319, by rfl⟩ : syracuseStep 781759 = 1172639) B1172639
theorem B1109641 : Blo 778337 1109641 := bstep (se 2 (by rfl) ⟨416115, by rfl⟩ : syracuseStep 1109641 = 832231) B832231
theorem B781979 : Blo 778337 781979 := bstep (se 1 (by rfl) ⟨586484, by rfl⟩ : syracuseStep 781979 = 1172969) B1172969
theorem B782171 : Blo 778337 782171 := bstep (se 1 (by rfl) ⟨586628, by rfl⟩ : syracuseStep 782171 = 1173257) B1173257
theorem B2224111 : Blo 778337 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B1668127 : Blo 778337 1668127 := bstep (se 1 (by rfl) ⟨1251095, by rfl⟩ : syracuseStep 1668127 = 2502191) B2502191
theorem B2225819 : Blo 778337 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B7600061 : Blo 778337 7600061 := bstep (se 3 (by rfl) ⟨1425011, by rfl⟩ : syracuseStep 7600061 = 2850023) B2850023
theorem B6650531 : Blo 778337 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B16055333 : Blo 778337 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B34176455 : Blo 778337 34176455 := bstep (se 1 (by rfl) ⟨25632341, by rfl⟩ : syracuseStep 34176455 = 51264683) B51264683
theorem B9633725 : Blo 778337 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B4227227 : Blo 778337 4227227 := bstep (se 1 (by rfl) ⟨3170420, by rfl⟩ : syracuseStep 4227227 = 6340841) B6340841
theorem B6324617 : Blo 778337 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B15008287 : Blo 778337 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B1313543 : Blo 778337 1313543 := bstep (se 1 (by rfl) ⟨985157, by rfl⟩ : syracuseStep 1313543 = 1970315) B1970315
theorem B6654905 : Blo 778337 6654905 := bstep (se 2 (by rfl) ⟨2495589, by rfl⟩ : syracuseStep 6654905 = 4991179) B4991179
theorem B1314535 : Blo 778337 1314535 := bstep (se 1 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 1314535 = 1971803) B1971803
theorem B987319 : Blo 778337 987319 := bstep (se 1 (by rfl) ⟨740489, by rfl⟩ : syracuseStep 987319 = 1480979) B1480979
theorem B5935517 : Blo 778337 5935517 := bstep (se 3 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 5935517 = 2225819) B2225819
theorem B1315487 : Blo 778337 1315487 := bstep (se 1 (by rfl) ⟨986615, by rfl⟩ : syracuseStep 1315487 = 1973231) B1973231
theorem B1479521 : Blo 778337 1479521 := bstep (se 2 (by rfl) ⟨554820, by rfl⟩ : syracuseStep 1479521 = 1109641) B1109641
theorem B2003903 : Blo 778337 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B1053823 : Blo 778337 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B2626937 : Blo 778337 2626937 := bstep (se 2 (by rfl) ⟨985101, by rfl⟩ : syracuseStep 2626937 = 1970203) B1970203
theorem B4987439 : Blo 778337 4987439 := bstep (se 1 (by rfl) ⟨3740579, by rfl⟩ : syracuseStep 4987439 = 7481159) B7481159
theorem B2628287 : Blo 778337 2628287 := bstep (se 1 (by rfl) ⟨1971215, by rfl⟩ : syracuseStep 2628287 = 3942431) B3942431
theorem B2956247 : Blo 778337 2956247 := bstep (se 1 (by rfl) ⟨2217185, by rfl⟩ : syracuseStep 2956247 = 4434371) B4434371
theorem B1481723 : Blo 778337 1481723 := bstep (se 1 (by rfl) ⟨1111292, by rfl⟩ : syracuseStep 1481723 = 2222585) B2222585
theorem B10689869 : Blo 778337 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B2956733 : Blo 778337 2956733 := bstep (se 3 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 2956733 = 1108775) B1108775
theorem B2629151 : Blo 778337 2629151 := bstep (se 1 (by rfl) ⟨1971863, by rfl⟩ : syracuseStep 2629151 = 3943727) B3943727
theorem B40443461 : Blo 778337 40443461 := bstep (se 4 (by rfl) ⟨3791574, by rfl⟩ : syracuseStep 40443461 = 7583149) B7583149
theorem B1974415 : Blo 778337 1974415 := bstep (se 1 (by rfl) ⟨1480811, by rfl⟩ : syracuseStep 1974415 = 2961623) B2961623
theorem B21897839 : Blo 778337 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B1319807 : Blo 778337 1319807 := bstep (se 1 (by rfl) ⟨989855, by rfl⟩ : syracuseStep 1319807 = 1979711) B1979711
theorem B1975387 : Blo 778337 1975387 := bstep (se 1 (by rfl) ⟨1481540, by rfl⟩ : syracuseStep 1975387 = 2963081) B2963081
theorem B2630825 : Blo 778337 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B104080583 : Blo 778337 104080583 := bstep (se 1 (by rfl) ⟨78060437, by rfl⟩ : syracuseStep 104080583 = 156120875) B156120875
theorem B2630879 : Blo 778337 2630879 := bstep (se 1 (by rfl) ⟨1973159, by rfl⟩ : syracuseStep 2630879 = 3946319) B3946319
theorem B6694163 : Blo 778337 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B2631095 : Blo 778337 2631095 := bstep (se 1 (by rfl) ⟨1973321, by rfl⟩ : syracuseStep 2631095 = 3946643) B3946643
theorem B2958875 : Blo 778337 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B2958889 : Blo 778337 2958889 := bstep (se 2 (by rfl) ⟨1109583, by rfl⟩ : syracuseStep 2958889 = 2219167) B2219167
theorem B2500151 : Blo 778337 2500151 := bstep (se 1 (by rfl) ⟨1875113, by rfl⟩ : syracuseStep 2500151 = 3750227) B3750227
theorem B4433687 : Blo 778337 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B37988189 : Blo 778337 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B22784303 : Blo 778337 22784303 := bstep (se 1 (by rfl) ⟨17088227, by rfl⟩ : syracuseStep 22784303 = 34176455) B34176455
theorem B1978121 : Blo 778337 1978121 := bstep (se 2 (by rfl) ⟨741795, by rfl⟩ : syracuseStep 1978121 = 1483591) B1483591
theorem B2633687 : Blo 778337 2633687 := bstep (se 1 (by rfl) ⟨1975265, by rfl⟩ : syracuseStep 2633687 = 3950531) B3950531
theorem B111194291 : Blo 778337 111194291 := bstep (se 1 (by rfl) ⟨83395718, by rfl⟩ : syracuseStep 111194291 = 166791437) B166791437
theorem B2961593 : Blo 778337 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B2961791 : Blo 778337 2961791 := bstep (se 1 (by rfl) ⟨2221343, by rfl⟩ : syracuseStep 2961791 = 4442687) B4442687
theorem B11252297 : Blo 778337 11252297 := bstep (se 2 (by rfl) ⟨4219611, by rfl⟩ : syracuseStep 11252297 = 8439223) B8439223
theorem B5912189 : Blo 778337 5912189 := bstep (se 3 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 5912189 = 2217071) B2217071
theorem B833743 : Blo 778337 833743 := bstep (se 1 (by rfl) ⟨625307, by rfl⟩ : syracuseStep 833743 = 1250615) B1250615
theorem B2636063 : Blo 778337 2636063 := bstep (se 1 (by rfl) ⟨1977047, by rfl⟩ : syracuseStep 2636063 = 3954095) B3954095
theorem B42678895 : Blo 778337 42678895 := bstep (se 1 (by rfl) ⟨32009171, by rfl⟩ : syracuseStep 42678895 = 64018343) B64018343
theorem B2637359 : Blo 778337 2637359 := bstep (se 1 (by rfl) ⟨1978019, by rfl⟩ : syracuseStep 2637359 = 3956039) B3956039
theorem B3948263 : Blo 778337 3948263 := bstep (se 1 (by rfl) ⟨2961197, by rfl⟩ : syracuseStep 3948263 = 5922395) B5922395
theorem B1425289 : Blo 778337 1425289 := bstep (se 2 (by rfl) ⟨534483, by rfl⟩ : syracuseStep 1425289 = 1068967) B1068967
theorem B2965481 : Blo 778337 2965481 := bstep (se 2 (by rfl) ⟨1112055, by rfl⟩ : syracuseStep 2965481 = 2224111) B2224111
theorem B6766699 : Blo 778337 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B12337541 : Blo 778337 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B2638493 : Blo 778337 2638493 := bstep (se 3 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 2638493 = 989435) B989435
theorem B3752687 : Blo 778337 3752687 := bstep (se 1 (by rfl) ⟨2814515, by rfl⟩ : syracuseStep 3752687 = 5629031) B5629031
theorem B6669053 : Blo 778337 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B13353821 : Blo 778337 13353821 := bstep (se 3 (by rfl) ⟨2503841, by rfl⟩ : syracuseStep 13353821 = 5007683) B5007683
theorem B21316679 : Blo 778337 21316679 := bstep (se 1 (by rfl) ⟨15987509, by rfl⟩ : syracuseStep 21316679 = 31975019) B31975019
theorem B12208153 : Blo 778337 12208153 := bstep (se 2 (by rfl) ⟨4578057, by rfl⟩ : syracuseStep 12208153 = 9156115) B9156115
theorem B200198191 : Blo 778337 200198191 := bstep (se 1 (by rfl) ⟨150148643, by rfl⟩ : syracuseStep 200198191 = 300297287) B300297287
theorem B2377961 : Blo 778337 2377961 := bstep (se 2 (by rfl) ⟨891735, by rfl⟩ : syracuseStep 2377961 = 1783471) B1783471
theorem B1756385 : Blo 778337 1756385 := bstep (se 2 (by rfl) ⟨658644, by rfl⟩ : syracuseStep 1756385 = 1317289) B1317289
theorem B1756583 : Blo 778337 1756583 := bstep (se 1 (by rfl) ⟨1317437, by rfl⟩ : syracuseStep 1756583 = 2634875) B2634875
theorem B5066707 : Blo 778337 5066707 := bstep (se 1 (by rfl) ⟨3800030, by rfl⟩ : syracuseStep 5066707 = 7600061) B7600061
theorem B1757447 : Blo 778337 1757447 := bstep (se 1 (by rfl) ⟨1318085, by rfl⟩ : syracuseStep 1757447 = 2636171) B2636171
theorem B30036257 : Blo 778337 30036257 := bstep (se 2 (by rfl) ⟨11263596, by rfl⟩ : syracuseStep 30036257 = 22527193) B22527193
theorem B1757519 : Blo 778337 1757519 := bstep (se 1 (by rfl) ⟨1318139, by rfl⟩ : syracuseStep 1757519 = 2636279) B2636279
theorem B1167785 : Blo 778337 1167785 := bstep (se 2 (by rfl) ⟨437919, by rfl⟩ : syracuseStep 1167785 = 875839) B875839
theorem B10703555 : Blo 778337 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B1168619 : Blo 778337 1168619 := bstep (se 1 (by rfl) ⟨876464, by rfl⟩ : syracuseStep 1168619 = 1752929) B1752929
theorem B1169435 : Blo 778337 1169435 := bstep (se 1 (by rfl) ⟨877076, by rfl⟩ : syracuseStep 1169435 = 1754153) B1754153
theorem B1169801 : Blo 778337 1169801 := bstep (se 2 (by rfl) ⟨438675, by rfl⟩ : syracuseStep 1169801 = 877351) B877351
theorem B1759679 : Blo 778337 1759679 := bstep (se 1 (by rfl) ⟨1319759, by rfl⟩ : syracuseStep 1759679 = 2639519) B2639519
theorem B1170047 : Blo 778337 1170047 := bstep (se 1 (by rfl) ⟨877535, by rfl⟩ : syracuseStep 1170047 = 1755071) B1755071
theorem B5921423 : Blo 778337 5921423 := bstep (se 1 (by rfl) ⟨4441067, by rfl⟩ : syracuseStep 5921423 = 8882135) B8882135
theorem B1170185 : Blo 778337 1170185 := bstep (se 2 (by rfl) ⟨438819, by rfl⟩ : syracuseStep 1170185 = 877639) B877639
theorem B7494767 : Blo 778337 7494767 := bstep (se 1 (by rfl) ⟨5621075, by rfl⟩ : syracuseStep 7494767 = 11242151) B11242151
theorem B1269049 : Blo 778337 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B1170911 : Blo 778337 1170911 := bstep (se 1 (by rfl) ⟨878183, by rfl⟩ : syracuseStep 1170911 = 1756367) B1756367
theorem B1171175 : Blo 778337 1171175 := bstep (se 1 (by rfl) ⟨878381, by rfl⟩ : syracuseStep 1171175 = 1756763) B1756763
theorem B876379 : Blo 778337 876379 := bstep (se 1 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 876379 = 1314569) B1314569
theorem B876415 : Blo 778337 876415 := bstep (se 1 (by rfl) ⟨657311, by rfl⟩ : syracuseStep 876415 = 1314623) B1314623
theorem B876955 : Blo 778337 876955 := bstep (se 1 (by rfl) ⟨657716, by rfl⟩ : syracuseStep 876955 = 1315433) B1315433
theorem B2220443 : Blo 778337 2220443 := bstep (se 1 (by rfl) ⟨1665332, by rfl⟩ : syracuseStep 2220443 = 3330665) B3330665
theorem B1172009 : Blo 778337 1172009 := bstep (se 2 (by rfl) ⟨439503, by rfl⟩ : syracuseStep 1172009 = 879007) B879007
theorem B779111 : Blo 778337 779111 := bstep (se 1 (by rfl) ⟨584333, by rfl⟩ : syracuseStep 779111 = 1168667) B1168667
theorem B1172423 : Blo 778337 1172423 := bstep (se 1 (by rfl) ⟨879317, by rfl⟩ : syracuseStep 1172423 = 1758635) B1758635
theorem B779263 : Blo 778337 779263 := bstep (se 1 (by rfl) ⟨584447, by rfl⟩ : syracuseStep 779263 = 1168895) B1168895
theorem B877819 : Blo 778337 877819 := bstep (se 1 (by rfl) ⟨658364, by rfl⟩ : syracuseStep 877819 = 1316729) B1316729
theorem B779679 : Blo 778337 779679 := bstep (se 1 (by rfl) ⟨584759, by rfl⟩ : syracuseStep 779679 = 1169519) B1169519
theorem B3007943 : Blo 778337 3007943 := bstep (se 1 (by rfl) ⟨2255957, by rfl⟩ : syracuseStep 3007943 = 4511915) B4511915
theorem B1172987 : Blo 778337 1172987 := bstep (se 1 (by rfl) ⟨879740, by rfl⟩ : syracuseStep 1172987 = 1759481) B1759481
theorem B1173083 : Blo 778337 1173083 := bstep (se 1 (by rfl) ⟨879812, by rfl⟩ : syracuseStep 1173083 = 1759625) B1759625
theorem B1173095 : Blo 778337 1173095 := bstep (se 1 (by rfl) ⟨879821, by rfl⟩ : syracuseStep 1173095 = 1759643) B1759643
theorem B43378415 : Blo 778337 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B1173287 : Blo 778337 1173287 := bstep (se 1 (by rfl) ⟨879965, by rfl⟩ : syracuseStep 1173287 = 1759931) B1759931
theorem B1173359 : Blo 778337 1173359 := bstep (se 1 (by rfl) ⟨880019, by rfl⟩ : syracuseStep 1173359 = 1760039) B1760039
theorem B780447 : Blo 778337 780447 := bstep (se 1 (by rfl) ⟨585335, by rfl⟩ : syracuseStep 780447 = 1170671) B1170671
theorem B2222255 : Blo 778337 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B21326327 : Blo 778337 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B780967 : Blo 778337 780967 := bstep (se 1 (by rfl) ⟨585725, by rfl⟩ : syracuseStep 780967 = 1171451) B1171451
theorem B781159 : Blo 778337 781159 := bstep (se 1 (by rfl) ⟨585869, by rfl⟩ : syracuseStep 781159 = 1171739) B1171739
theorem B781223 : Blo 778337 781223 := bstep (se 1 (by rfl) ⟨585917, by rfl⟩ : syracuseStep 781223 = 1171835) B1171835
theorem B781295 : Blo 778337 781295 := bstep (se 1 (by rfl) ⟨585971, by rfl⟩ : syracuseStep 781295 = 1171943) B1171943
theorem B781471 : Blo 778337 781471 := bstep (se 1 (by rfl) ⟨586103, by rfl⟩ : syracuseStep 781471 = 1172207) B1172207
theorem B781543 : Blo 778337 781543 := bstep (se 1 (by rfl) ⟨586157, by rfl⟩ : syracuseStep 781543 = 1172315) B1172315
theorem B4451867 : Blo 778337 4451867 := bstep (se 1 (by rfl) ⟨3338900, by rfl⟩ : syracuseStep 4451867 = 6677801) B6677801
theorem B781855 : Blo 778337 781855 := bstep (se 1 (by rfl) ⟨586391, by rfl⟩ : syracuseStep 781855 = 1172783) B1172783
theorem B782015 : Blo 778337 782015 := bstep (se 1 (by rfl) ⟨586511, by rfl⟩ : syracuseStep 782015 = 1173023) B1173023
theorem B782111 : Blo 778337 782111 := bstep (se 1 (by rfl) ⟨586583, by rfl⟩ : syracuseStep 782111 = 1173167) B1173167
theorem B40464251 : Blo 778337 40464251 := bstep (se 1 (by rfl) ⟨30348188, by rfl⟩ : syracuseStep 40464251 = 60696377) B60696377
theorem B2224169 : Blo 778337 2224169 := bstep (se 2 (by rfl) ⟨834063, by rfl⟩ : syracuseStep 2224169 = 1668127) B1668127
theorem B5009633 : Blo 778337 5009633 := bstep (se 2 (by rfl) ⟨1878612, by rfl⟩ : syracuseStep 5009633 = 3757225) B3757225
theorem B6322283 : Blo 778337 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B21658043 : Blo 778337 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B22772819 : Blo 778337 22772819 := bstep (se 1 (by rfl) ⟨17079614, by rfl⟩ : syracuseStep 22772819 = 34159229) B34159229
theorem B6422483 : Blo 778337 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B2818151 : Blo 778337 2818151 := bstep (se 1 (by rfl) ⟨2113613, by rfl⟩ : syracuseStep 2818151 = 4227227) B4227227
theorem B8225027 : Blo 778337 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B266930921 : Blo 778337 266930921 := bstep (se 2 (by rfl) ⟨100099095, by rfl⟩ : syracuseStep 266930921 = 200198191) B200198191
theorem B20024171 : Blo 778337 20024171 := bstep (se 1 (by rfl) ⟨15018128, by rfl⟩ : syracuseStep 20024171 = 30036257) B30036257
theorem B277548221 : Blo 778337 277548221 := bstep (se 3 (by rfl) ⟨52040291, by rfl⟩ : syracuseStep 277548221 = 104080583) B104080583
theorem B986347 : Blo 778337 986347 := bstep (se 1 (by rfl) ⟨739760, by rfl⟩ : syracuseStep 986347 = 1479521) B1479521
theorem B1970831 : Blo 778337 1970831 := bstep (se 1 (by rfl) ⟨1478123, by rfl⟩ : syracuseStep 1970831 = 2956247) B2956247
theorem B987815 : Blo 778337 987815 := bstep (se 1 (by rfl) ⟨740861, by rfl⟩ : syracuseStep 987815 = 1481723) B1481723
theorem B1971155 : Blo 778337 1971155 := bstep (se 1 (by rfl) ⟨1478366, by rfl⟩ : syracuseStep 1971155 = 2956733) B2956733
theorem B6755609 : Blo 778337 6755609 := bstep (se 2 (by rfl) ⟨2533353, by rfl⟩ : syracuseStep 6755609 = 5066707) B5066707
theorem B1316425 : Blo 778337 1316425 := bstep (se 2 (by rfl) ⟨493659, by rfl⟩ : syracuseStep 1316425 = 987319) B987319
theorem B1480295 : Blo 778337 1480295 := bstep (se 1 (by rfl) ⟨1110221, by rfl⟩ : syracuseStep 1480295 = 2220443) B2220443
theorem B4462775 : Blo 778337 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B2005295 : Blo 778337 2005295 := bstep (se 1 (by rfl) ⟨1503971, by rfl⟩ : syracuseStep 2005295 = 3007943) B3007943
theorem B1972583 : Blo 778337 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B2955791 : Blo 778337 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B1481503 : Blo 778337 1481503 := bstep (se 1 (by rfl) ⟨1111127, by rfl⟩ : syracuseStep 1481503 = 2222255) B2222255
theorem B1318747 : Blo 778337 1318747 := bstep (se 1 (by rfl) ⟨989060, by rfl⟩ : syracuseStep 1318747 = 1978121) B1978121
theorem B26976167 : Blo 778337 26976167 := bstep (se 1 (by rfl) ⟨20232125, by rfl⟩ : syracuseStep 26976167 = 40464251) B40464251
theorem B1482779 : Blo 778337 1482779 := bstep (se 1 (by rfl) ⟨1112084, by rfl⟩ : syracuseStep 1482779 = 2224169) B2224169
theorem B74129527 : Blo 778337 74129527 := bstep (se 1 (by rfl) ⟨55597145, by rfl⟩ : syracuseStep 74129527 = 111194291) B111194291
theorem B1974395 : Blo 778337 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B1974527 : Blo 778337 1974527 := bstep (se 1 (by rfl) ⟨1480895, by rfl⟩ : syracuseStep 1974527 = 2961791) B2961791
theorem B3941459 : Blo 778337 3941459 := bstep (se 1 (by rfl) ⟨2956094, by rfl⟩ : syracuseStep 3941459 = 5912189) B5912189
theorem B15181879 : Blo 778337 15181879 := bstep (se 1 (by rfl) ⟨11386409, by rfl⟩ : syracuseStep 15181879 = 22772819) B22772819
theorem B2632175 : Blo 778337 2632175 := bstep (se 1 (by rfl) ⟨1974131, by rfl⟩ : syracuseStep 2632175 = 3948263) B3948263
theorem B1976987 : Blo 778337 1976987 := bstep (se 1 (by rfl) ⟨1482740, by rfl⟩ : syracuseStep 1976987 = 2965481) B2965481
theorem B9022265 : Blo 778337 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B2632553 : Blo 778337 2632553 := bstep (se 2 (by rfl) ⟨987207, by rfl⟩ : syracuseStep 2632553 = 1974415) B1974415
theorem B2633849 : Blo 778337 2633849 := bstep (se 2 (by rfl) ⟨987693, by rfl⟩ : syracuseStep 2633849 = 1975387) B1975387
theorem B1585307 : Blo 778337 1585307 := bstep (se 1 (by rfl) ⟨1188980, by rfl⟩ : syracuseStep 1585307 = 2377961) B2377961
theorem B4436603 : Blo 778337 4436603 := bstep (se 1 (by rfl) ⟨3327452, by rfl⟩ : syracuseStep 4436603 = 6654905) B6654905
theorem B10007165 : Blo 778337 10007165 := bstep (se 3 (by rfl) ⟨1876343, by rfl⟩ : syracuseStep 10007165 = 3752687) B3752687
theorem B3945185 : Blo 778337 3945185 := bstep (se 2 (by rfl) ⟨1479444, by rfl⟩ : syracuseStep 3945185 = 2958889) B2958889
theorem B1751291 : Blo 778337 1751291 := bstep (se 1 (by rfl) ⟨1313468, by rfl⟩ : syracuseStep 1751291 = 2626937) B2626937
theorem B6667069 : Blo 778337 6667069 := bstep (se 3 (by rfl) ⟨1250075, by rfl⟩ : syracuseStep 6667069 = 2500151) B2500151
theorem B3324959 : Blo 778337 3324959 := bstep (se 1 (by rfl) ⟨2493719, by rfl⟩ : syracuseStep 3324959 = 4987439) B4987439
theorem B3947615 : Blo 778337 3947615 := bstep (se 1 (by rfl) ⟨2960711, by rfl⟩ : syracuseStep 3947615 = 5921423) B5921423
theorem B1752191 : Blo 778337 1752191 := bstep (se 1 (by rfl) ⟨1314143, by rfl⟩ : syracuseStep 1752191 = 2628287) B2628287
theorem B4996511 : Blo 778337 4996511 := bstep (se 1 (by rfl) ⟨3747383, by rfl⟩ : syracuseStep 4996511 = 7494767) B7494767
theorem B7126579 : Blo 778337 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B1752713 : Blo 778337 1752713 := bstep (se 2 (by rfl) ⟨657267, by rfl⟩ : syracuseStep 1752713 = 1314535) B1314535
theorem B1752767 : Blo 778337 1752767 := bstep (se 1 (by rfl) ⟨1314575, by rfl⟩ : syracuseStep 1752767 = 2629151) B2629151
theorem B14598559 : Blo 778337 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B1753883 : Blo 778337 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B1753919 : Blo 778337 1753919 := bstep (se 1 (by rfl) ⟨1315439, by rfl⟩ : syracuseStep 1753919 = 2630879) B2630879
theorem B1754063 : Blo 778337 1754063 := bstep (se 1 (by rfl) ⟨1315547, by rfl⟩ : syracuseStep 1754063 = 2631095) B2631095
theorem B28918943 : Blo 778337 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B15189535 : Blo 778337 15189535 := bstep (se 1 (by rfl) ⟨11392151, by rfl⟩ : syracuseStep 15189535 = 22784303) B22784303
theorem B2967911 : Blo 778337 2967911 := bstep (se 1 (by rfl) ⟨2225933, by rfl⟩ : syracuseStep 2967911 = 4451867) B4451867
theorem B1755791 : Blo 778337 1755791 := bstep (se 1 (by rfl) ⟨1316843, by rfl⟩ : syracuseStep 1755791 = 2633687) B2633687
theorem B56905193 : Blo 778337 56905193 := bstep (se 2 (by rfl) ⟨21339447, by rfl⟩ : syracuseStep 56905193 = 42678895) B42678895
theorem B4214855 : Blo 778337 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B1757375 : Blo 778337 1757375 := bstep (se 1 (by rfl) ⟨1318031, by rfl⟩ : syracuseStep 1757375 = 2636063) B2636063
theorem B14438695 : Blo 778337 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B1692065 : Blo 778337 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B1758239 : Blo 778337 1758239 := bstep (se 1 (by rfl) ⟨1318679, by rfl⟩ : syracuseStep 1758239 = 2637359) B2637359
theorem B1168505 : Blo 778337 1168505 := bstep (se 2 (by rfl) ⟨438189, by rfl⟩ : syracuseStep 1168505 = 876379) B876379
theorem B1168553 : Blo 778337 1168553 := bstep (se 2 (by rfl) ⟨438207, by rfl⟩ : syracuseStep 1168553 = 876415) B876415
theorem B4281655 : Blo 778337 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B4216411 : Blo 778337 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1758995 : Blo 778337 1758995 := bstep (se 1 (by rfl) ⟨1319246, by rfl⟩ : syracuseStep 1758995 = 2638493) B2638493
theorem B4446035 : Blo 778337 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B1169273 : Blo 778337 1169273 := bstep (se 2 (by rfl) ⟨438477, by rfl⟩ : syracuseStep 1169273 = 876955) B876955
theorem B8902547 : Blo 778337 8902547 := bstep (se 1 (by rfl) ⟨6676910, by rfl⟩ : syracuseStep 8902547 = 13353821) B13353821
theorem B20011049 : Blo 778337 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B14211119 : Blo 778337 14211119 := bstep (se 1 (by rfl) ⟨10658339, by rfl⟩ : syracuseStep 14211119 = 21316679) B21316679
theorem B1170425 : Blo 778337 1170425 := bstep (se 2 (by rfl) ⟨438909, by rfl⟩ : syracuseStep 1170425 = 877819) B877819
theorem B875695 : Blo 778337 875695 := bstep (se 1 (by rfl) ⟨656771, by rfl⟩ : syracuseStep 875695 = 1313543) B1313543
theorem B1170923 : Blo 778337 1170923 := bstep (se 1 (by rfl) ⟨878192, by rfl⟩ : syracuseStep 1170923 = 1756385) B1756385
theorem B1171055 : Blo 778337 1171055 := bstep (se 1 (by rfl) ⟨878291, by rfl⟩ : syracuseStep 1171055 = 1756583) B1756583
theorem B16277537 : Blo 778337 16277537 := bstep (se 2 (by rfl) ⟨6104076, by rfl⟩ : syracuseStep 16277537 = 12208153) B12208153
theorem B1171631 : Blo 778337 1171631 := bstep (se 1 (by rfl) ⟨878723, by rfl⟩ : syracuseStep 1171631 = 1757447) B1757447
theorem B1171679 : Blo 778337 1171679 := bstep (se 1 (by rfl) ⟨878759, by rfl⟩ : syracuseStep 1171679 = 1757519) B1757519
theorem B3957011 : Blo 778337 3957011 := bstep (se 1 (by rfl) ⟨2967758, by rfl⟩ : syracuseStep 3957011 = 5935517) B5935517
theorem B778523 : Blo 778337 778523 := bstep (se 1 (by rfl) ⟨583892, by rfl⟩ : syracuseStep 778523 = 1167785) B1167785
theorem B876991 : Blo 778337 876991 := bstep (se 1 (by rfl) ⟨657743, by rfl⟩ : syracuseStep 876991 = 1315487) B1315487
theorem B7135703 : Blo 778337 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B1335935 : Blo 778337 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B779079 : Blo 778337 779079 := bstep (se 1 (by rfl) ⟨584309, by rfl⟩ : syracuseStep 779079 = 1168619) B1168619
theorem B779623 : Blo 778337 779623 := bstep (se 1 (by rfl) ⟨584717, by rfl⟩ : syracuseStep 779623 = 1169435) B1169435
theorem B779867 : Blo 778337 779867 := bstep (se 1 (by rfl) ⟨584900, by rfl⟩ : syracuseStep 779867 = 1169801) B1169801
theorem B1173119 : Blo 778337 1173119 := bstep (se 1 (by rfl) ⟨879839, by rfl⟩ : syracuseStep 1173119 = 1759679) B1759679
theorem B780031 : Blo 778337 780031 := bstep (se 1 (by rfl) ⟨585023, by rfl⟩ : syracuseStep 780031 = 1170047) B1170047
theorem B780123 : Blo 778337 780123 := bstep (se 1 (by rfl) ⟨585092, by rfl⟩ : syracuseStep 780123 = 1170185) B1170185
theorem B780607 : Blo 778337 780607 := bstep (se 1 (by rfl) ⟨585455, by rfl⟩ : syracuseStep 780607 = 1170911) B1170911
theorem B26962307 : Blo 778337 26962307 := bstep (se 1 (by rfl) ⟨20221730, by rfl⟩ : syracuseStep 26962307 = 40443461) B40443461
theorem B780783 : Blo 778337 780783 := bstep (se 1 (by rfl) ⟨585587, by rfl⟩ : syracuseStep 780783 = 1171175) B1171175
theorem B781339 : Blo 778337 781339 := bstep (se 1 (by rfl) ⟨586004, by rfl⟩ : syracuseStep 781339 = 1172009) B1172009
theorem B879871 : Blo 778337 879871 := bstep (se 1 (by rfl) ⟨659903, by rfl⟩ : syracuseStep 879871 = 1319807) B1319807
theorem B781615 : Blo 778337 781615 := bstep (se 1 (by rfl) ⟨586211, by rfl⟩ : syracuseStep 781615 = 1172423) B1172423
theorem B781991 : Blo 778337 781991 := bstep (se 1 (by rfl) ⟨586493, by rfl⟩ : syracuseStep 781991 = 1172987) B1172987
theorem B782055 : Blo 778337 782055 := bstep (se 1 (by rfl) ⟨586541, by rfl⟩ : syracuseStep 782055 = 1173083) B1173083
theorem B782063 : Blo 778337 782063 := bstep (se 1 (by rfl) ⟨586547, by rfl⟩ : syracuseStep 782063 = 1173095) B1173095
theorem B782191 : Blo 778337 782191 := bstep (se 1 (by rfl) ⟨586643, by rfl⟩ : syracuseStep 782191 = 1173287) B1173287
theorem B25325459 : Blo 778337 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B782239 : Blo 778337 782239 := bstep (se 1 (by rfl) ⟨586679, by rfl⟩ : syracuseStep 782239 = 1173359) B1173359
theorem B1405097 : Blo 778337 1405097 := bstep (se 2 (by rfl) ⟨526911, by rfl⟩ : syracuseStep 1405097 = 1053823) B1053823
theorem B14217551 : Blo 778337 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B3339755 : Blo 778337 3339755 := bstep (se 1 (by rfl) ⟨2504816, by rfl⟩ : syracuseStep 3339755 = 5009633) B5009633
theorem B1111657 : Blo 778337 1111657 := bstep (se 2 (by rfl) ⟨416871, by rfl⟩ : syracuseStep 1111657 = 833743) B833743
theorem B7501531 : Blo 778337 7501531 := bstep (se 1 (by rfl) ⟨5626148, by rfl⟩ : syracuseStep 7501531 = 11252297) B11252297
theorem B1900385 : Blo 778337 1900385 := bstep (se 2 (by rfl) ⟨712644, by rfl⟩ : syracuseStep 1900385 = 1425289) B1425289
theorem B19464745 : Blo 778337 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B1313887 : Blo 778337 1313887 := bstep (se 1 (by rfl) ⟨985415, by rfl⟩ : syracuseStep 1313887 = 1970831) B1970831
theorem B1314103 : Blo 778337 1314103 := bstep (se 1 (by rfl) ⟨985577, by rfl⟩ : syracuseStep 1314103 = 1971155) B1971155
theorem B5935031 : Blo 778337 5935031 := bstep (se 1 (by rfl) ⟨4451273, by rfl⟩ : syracuseStep 5935031 = 8902547) B8902547
theorem B13340699 : Blo 778337 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B9474079 : Blo 778337 9474079 := bstep (se 1 (by rfl) ⟨7105559, by rfl⟩ : syracuseStep 9474079 = 14211119) B14211119
theorem B1315055 : Blo 778337 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B1315129 : Blo 778337 1315129 := bstep (se 2 (by rfl) ⟨493173, by rfl⟩ : syracuseStep 1315129 = 986347) B986347
theorem B1970527 : Blo 778337 1970527 := bstep (se 1 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 1970527 = 2955791) B2955791
theorem B988519 : Blo 778337 988519 := bstep (se 1 (by rfl) ⟨741389, by rfl⟩ : syracuseStep 988519 = 1482779) B1482779
theorem B10851691 : Blo 778337 10851691 := bstep (se 1 (by rfl) ⟨8138768, by rfl⟩ : syracuseStep 10851691 = 16277537) B16277537
theorem B1316263 : Blo 778337 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B1316351 : Blo 778337 1316351 := bstep (se 1 (by rfl) ⟨987263, by rfl⟩ : syracuseStep 1316351 = 1974527) B1974527
theorem B4757135 : Blo 778337 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B890623 : Blo 778337 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B2627639 : Blo 778337 2627639 := bstep (se 1 (by rfl) ⟨1970729, by rfl⟩ : syracuseStep 2627639 = 3941459) B3941459
theorem B5347453 : Blo 778337 5347453 := bstep (se 3 (by rfl) ⟨1002647, by rfl⟩ : syracuseStep 5347453 = 2005295) B2005295
theorem B5708873 : Blo 778337 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B1317991 : Blo 778337 1317991 := bstep (se 1 (by rfl) ⟨988493, by rfl⟩ : syracuseStep 1317991 = 1976987) B1976987
theorem B1482209 : Blo 778337 1482209 := bstep (se 2 (by rfl) ⟨555828, by rfl⟩ : syracuseStep 1482209 = 1111657) B1111657
theorem B10002041 : Blo 778337 10002041 := bstep (se 2 (by rfl) ⟨3750765, by rfl⟩ : syracuseStep 10002041 = 7501531) B7501531
theorem B16883639 : Blo 778337 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B1056871 : Blo 778337 1056871 := bstep (se 1 (by rfl) ⟨792653, by rfl⟩ : syracuseStep 1056871 = 1585307) B1585307
theorem B81010853 : Blo 778337 81010853 := bstep (se 4 (by rfl) ⟨7594767, by rfl⟩ : syracuseStep 81010853 = 15189535) B15189535
theorem B9478367 : Blo 778337 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B2957735 : Blo 778337 2957735 := bstep (se 1 (by rfl) ⟨2218301, by rfl⟩ : syracuseStep 2957735 = 4436603) B4436603
theorem B2630123 : Blo 778337 2630123 := bstep (se 1 (by rfl) ⟨1972592, by rfl⟩ : syracuseStep 2630123 = 3945185) B3945185
theorem B1975337 : Blo 778337 1975337 := bstep (se 2 (by rfl) ⟨740751, by rfl⟩ : syracuseStep 1975337 = 1481503) B1481503
theorem B8889425 : Blo 778337 8889425 := bstep (se 2 (by rfl) ⟨3333534, by rfl⟩ : syracuseStep 8889425 = 6667069) B6667069
theorem B2631743 : Blo 778337 2631743 := bstep (se 1 (by rfl) ⟨1973807, by rfl⟩ : syracuseStep 2631743 = 3947615) B3947615
theorem B1878767 : Blo 778337 1878767 := bstep (se 1 (by rfl) ⟨1409075, by rfl⟩ : syracuseStep 1878767 = 2818151) B2818151
theorem B98839369 : Blo 778337 98839369 := bstep (se 2 (by rfl) ⟨37064763, by rfl⟩ : syracuseStep 98839369 = 74129527) B74129527
theorem B5483351 : Blo 778337 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B19279295 : Blo 778337 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B1978607 : Blo 778337 1978607 := bstep (se 1 (by rfl) ⟨1483955, by rfl⟩ : syracuseStep 1978607 = 2967911) B2967911
theorem B2634173 : Blo 778337 2634173 := bstep (se 3 (by rfl) ⟨493907, by rfl⟩ : syracuseStep 2634173 = 987815) B987815
theorem B13349447 : Blo 778337 13349447 := bstep (se 1 (by rfl) ⟨10012085, by rfl⟩ : syracuseStep 13349447 = 20024171) B20024171
theorem B1128043 : Blo 778337 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B2964023 : Blo 778337 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B3947453 : Blo 778337 3947453 := bstep (se 3 (by rfl) ⟨740147, by rfl⟩ : syracuseStep 3947453 = 1480295) B1480295
theorem B2638007 : Blo 778337 2638007 := bstep (se 1 (by rfl) ⟨1978505, by rfl⟩ : syracuseStep 2638007 = 3957011) B3957011
theorem B19251593 : Blo 778337 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B17974871 : Blo 778337 17974871 := bstep (se 1 (by rfl) ⟨13481153, by rfl⟩ : syracuseStep 17974871 = 26962307) B26962307
theorem B1754783 : Blo 778337 1754783 := bstep (se 1 (by rfl) ⟨1316087, by rfl⟩ : syracuseStep 1754783 = 2632175) B2632175
theorem B6014843 : Blo 778337 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B1755035 : Blo 778337 1755035 := bstep (se 1 (by rfl) ⟨1316276, by rfl⟩ : syracuseStep 1755035 = 2632553) B2632553
theorem B1755233 : Blo 778337 1755233 := bstep (se 2 (by rfl) ⟨658212, by rfl⟩ : syracuseStep 1755233 = 1316425) B1316425
theorem B5621881 : Blo 778337 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B1755899 : Blo 778337 1755899 := bstep (se 1 (by rfl) ⟨1316924, by rfl⟩ : syracuseStep 1755899 = 2633849) B2633849
theorem B936731 : Blo 778337 936731 := bstep (se 1 (by rfl) ⟨702548, by rfl⟩ : syracuseStep 936731 = 1405097) B1405097
theorem B6671443 : Blo 778337 6671443 := bstep (se 1 (by rfl) ⟨5003582, by rfl⟩ : syracuseStep 6671443 = 10007165) B10007165
theorem B1167527 : Blo 778337 1167527 := bstep (se 1 (by rfl) ⟨875645, by rfl⟩ : syracuseStep 1167527 = 1751291) B1751291
theorem B1167593 : Blo 778337 1167593 := bstep (se 2 (by rfl) ⟨437847, by rfl⟩ : syracuseStep 1167593 = 875695) B875695
theorem B2216639 : Blo 778337 2216639 := bstep (se 1 (by rfl) ⟨1662479, by rfl⟩ : syracuseStep 2216639 = 3324959) B3324959
theorem B1168127 : Blo 778337 1168127 := bstep (se 1 (by rfl) ⟨876095, by rfl⟩ : syracuseStep 1168127 = 1752191) B1752191
theorem B3331007 : Blo 778337 3331007 := bstep (se 1 (by rfl) ⟨2498255, by rfl⟩ : syracuseStep 3331007 = 4996511) B4996511
theorem B1168475 : Blo 778337 1168475 := bstep (se 1 (by rfl) ⟨876356, by rfl⟩ : syracuseStep 1168475 = 1752713) B1752713
theorem B1758329 : Blo 778337 1758329 := bstep (se 2 (by rfl) ⟨659373, by rfl⟩ : syracuseStep 1758329 = 1318747) B1318747
theorem B1168511 : Blo 778337 1168511 := bstep (se 1 (by rfl) ⟨876383, by rfl⟩ : syracuseStep 1168511 = 1752767) B1752767
theorem B1266923 : Blo 778337 1266923 := bstep (se 1 (by rfl) ⟨950192, by rfl⟩ : syracuseStep 1266923 = 1900385) B1900385
theorem B1169255 : Blo 778337 1169255 := bstep (se 1 (by rfl) ⟨876941, by rfl⟩ : syracuseStep 1169255 = 1753883) B1753883
theorem B1169279 : Blo 778337 1169279 := bstep (se 1 (by rfl) ⟨876959, by rfl⟩ : syracuseStep 1169279 = 1753919) B1753919
theorem B1169321 : Blo 778337 1169321 := bstep (se 2 (by rfl) ⟨438495, by rfl⟩ : syracuseStep 1169321 = 876991) B876991
theorem B1169375 : Blo 778337 1169375 := bstep (se 1 (by rfl) ⟨877031, by rfl⟩ : syracuseStep 1169375 = 1754063) B1754063
theorem B1170527 : Blo 778337 1170527 := bstep (se 1 (by rfl) ⟨877895, by rfl⟩ : syracuseStep 1170527 = 1755791) B1755791
theorem B37936795 : Blo 778337 37936795 := bstep (se 1 (by rfl) ⟨28452596, by rfl⟩ : syracuseStep 37936795 = 56905193) B56905193
theorem B2809903 : Blo 778337 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B20242505 : Blo 778337 20242505 := bstep (se 2 (by rfl) ⟨7590939, by rfl⟩ : syracuseStep 20242505 = 15181879) B15181879
theorem B1171583 : Blo 778337 1171583 := bstep (se 1 (by rfl) ⟨878687, by rfl⟩ : syracuseStep 1171583 = 1757375) B1757375
theorem B1172159 : Blo 778337 1172159 := bstep (se 1 (by rfl) ⟨879119, by rfl⟩ : syracuseStep 1172159 = 1758239) B1758239
theorem B18014957 : Blo 778337 18014957 := bstep (se 3 (by rfl) ⟨3377804, by rfl⟩ : syracuseStep 18014957 = 6755609) B6755609
theorem B779003 : Blo 778337 779003 := bstep (se 1 (by rfl) ⟨584252, by rfl⟩ : syracuseStep 779003 = 1168505) B1168505
theorem B779035 : Blo 778337 779035 := bstep (se 1 (by rfl) ⟨584276, by rfl⟩ : syracuseStep 779035 = 1168553) B1168553
theorem B1172663 : Blo 778337 1172663 := bstep (se 1 (by rfl) ⟨879497, by rfl⟩ : syracuseStep 1172663 = 1758995) B1758995
theorem B779515 : Blo 778337 779515 := bstep (se 1 (by rfl) ⟨584636, by rfl⟩ : syracuseStep 779515 = 1169273) B1169273
theorem B2975183 : Blo 778337 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B1173161 : Blo 778337 1173161 := bstep (se 2 (by rfl) ⟨439935, by rfl⟩ : syracuseStep 1173161 = 879871) B879871
theorem B780283 : Blo 778337 780283 := bstep (se 1 (by rfl) ⟨585212, by rfl⟩ : syracuseStep 780283 = 1170425) B1170425
theorem B780615 : Blo 778337 780615 := bstep (se 1 (by rfl) ⟨585461, by rfl⟩ : syracuseStep 780615 = 1170923) B1170923
theorem B780703 : Blo 778337 780703 := bstep (se 1 (by rfl) ⟨585527, by rfl⟩ : syracuseStep 780703 = 1171055) B1171055
theorem B17984111 : Blo 778337 17984111 := bstep (se 1 (by rfl) ⟨13488083, by rfl⟩ : syracuseStep 17984111 = 26976167) B26976167
theorem B781087 : Blo 778337 781087 := bstep (se 1 (by rfl) ⟨585815, by rfl⟩ : syracuseStep 781087 = 1171631) B1171631
theorem B781119 : Blo 778337 781119 := bstep (se 1 (by rfl) ⟨585839, by rfl⟩ : syracuseStep 781119 = 1171679) B1171679
theorem B782079 : Blo 778337 782079 := bstep (se 1 (by rfl) ⟨586559, by rfl⟩ : syracuseStep 782079 = 1173119) B1173119
theorem B711815789 : Blo 778337 711815789 := bstep (se 3 (by rfl) ⟨133465460, by rfl⟩ : syracuseStep 711815789 = 266930921) B266930921
theorem B740128589 : Blo 778337 740128589 := bstep (se 3 (by rfl) ⟨138774110, by rfl⟩ : syracuseStep 740128589 = 277548221) B277548221
theorem B2226503 : Blo 778337 2226503 := bstep (se 1 (by rfl) ⟨1669877, by rfl⟩ : syracuseStep 2226503 = 3339755) B3339755
theorem B9502105 : Blo 778337 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B1409161 : Blo 778337 1409161 := bstep (se 2 (by rfl) ⟨528435, by rfl⟩ : syracuseStep 1409161 = 1056871) B1056871
theorem B25952993 : Blo 778337 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B1477759 : Blo 778337 1477759 := bstep (se 1 (by rfl) ⟨1108319, by rfl⟩ : syracuseStep 1477759 = 2216639) B2216639
theorem B3378461 : Blo 778337 3378461 := bstep (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) B1266923
theorem B3805915 : Blo 778337 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B988139 : Blo 778337 988139 := bstep (se 1 (by rfl) ⟨741104, by rfl⟩ : syracuseStep 988139 = 1482209) B1482209
theorem B54007235 : Blo 778337 54007235 := bstep (se 1 (by rfl) ⟨40505426, by rfl⟩ : syracuseStep 54007235 = 81010853) B81010853
theorem B1971823 : Blo 778337 1971823 := bstep (se 1 (by rfl) ⟨1478867, by rfl⟩ : syracuseStep 1971823 = 2957735) B2957735
theorem B2627369 : Blo 778337 2627369 := bstep (se 2 (by rfl) ⟨985263, by rfl⟩ : syracuseStep 2627369 = 1970527) B1970527
theorem B1316891 : Blo 778337 1316891 := bstep (se 1 (by rfl) ⟨987668, by rfl⟩ : syracuseStep 1316891 = 1975337) B1975337
theorem B1318025 : Blo 778337 1318025 := bstep (se 2 (by rfl) ⟨494259, by rfl⟩ : syracuseStep 1318025 = 988519) B988519
theorem B1252511 : Blo 778337 1252511 := bstep (se 1 (by rfl) ⟨939383, by rfl⟩ : syracuseStep 1252511 = 1878767) B1878767
theorem B2497949 : Blo 778337 2497949 := bstep (se 3 (by rfl) ⟨468365, by rfl⟩ : syracuseStep 2497949 = 936731) B936731
theorem B12852863 : Blo 778337 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B1187497 : Blo 778337 1187497 := bstep (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) B890623
theorem B1319071 : Blo 778337 1319071 := bstep (se 1 (by rfl) ⟨989303, by rfl⟩ : syracuseStep 1319071 = 1978607) B1978607
theorem B1484335 : Blo 778337 1484335 := bstep (se 1 (by rfl) ⟨1113251, by rfl⟩ : syracuseStep 1484335 = 2226503) B2226503
theorem B1976015 : Blo 778337 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B2631635 : Blo 778337 2631635 := bstep (se 1 (by rfl) ⟨1973726, by rfl⟩ : syracuseStep 2631635 = 3947453) B3947453
theorem B3746537 : Blo 778337 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B53980013 : Blo 778337 53980013 := bstep (se 3 (by rfl) ⟨10121252, by rfl⟩ : syracuseStep 53980013 = 20242505) B20242505
theorem B4009895 : Blo 778337 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B8893799 : Blo 778337 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B1751759 : Blo 778337 1751759 := bstep (se 1 (by rfl) ⟨1313819, by rfl⟩ : syracuseStep 1751759 = 2627639) B2627639
theorem B8895257 : Blo 778337 8895257 := bstep (se 2 (by rfl) ⟨3335721, by rfl⟩ : syracuseStep 8895257 = 6671443) B6671443
theorem B1751849 : Blo 778337 1751849 := bstep (se 2 (by rfl) ⟨656943, by rfl⟩ : syracuseStep 1751849 = 1313887) B1313887
theorem B1752137 : Blo 778337 1752137 := bstep (se 2 (by rfl) ⟨657051, by rfl⟩ : syracuseStep 1752137 = 1314103) B1314103
theorem B6668027 : Blo 778337 6668027 := bstep (se 1 (by rfl) ⟨5001020, by rfl⟩ : syracuseStep 6668027 = 10002041) B10002041
theorem B11255759 : Blo 778337 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B12632105 : Blo 778337 12632105 := bstep (se 2 (by rfl) ⟨4737039, by rfl⟩ : syracuseStep 12632105 = 9474079) B9474079
theorem B1753415 : Blo 778337 1753415 := bstep (se 1 (by rfl) ⟨1315061, by rfl⟩ : syracuseStep 1753415 = 2630123) B2630123
theorem B1753505 : Blo 778337 1753505 := bstep (se 2 (by rfl) ⟨657564, by rfl⟩ : syracuseStep 1753505 = 1315129) B1315129
theorem B12009971 : Blo 778337 12009971 := bstep (se 1 (by rfl) ⟨9007478, by rfl⟩ : syracuseStep 12009971 = 18014957) B18014957
theorem B1983455 : Blo 778337 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B1754495 : Blo 778337 1754495 := bstep (se 1 (by rfl) ⟨1315871, by rfl⟩ : syracuseStep 1754495 = 2631743) B2631743
theorem B50742773 : Blo 778337 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B47957629 : Blo 778337 47957629 := bstep (se 3 (by rfl) ⟨8992055, by rfl⟩ : syracuseStep 47957629 = 17984111) B17984111
theorem B14468921 : Blo 778337 14468921 := bstep (se 2 (by rfl) ⟨5425845, by rfl⟩ : syracuseStep 14468921 = 10851691) B10851691
theorem B1755017 : Blo 778337 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B3655567 : Blo 778337 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B7129937 : Blo 778337 7129937 := bstep (se 2 (by rfl) ⟨2673726, by rfl⟩ : syracuseStep 7129937 = 5347453) B5347453
theorem B1756115 : Blo 778337 1756115 := bstep (se 1 (by rfl) ⟨1317086, by rfl⟩ : syracuseStep 1756115 = 2634173) B2634173
theorem B8899631 : Blo 778337 8899631 := bstep (se 1 (by rfl) ⟨6674723, by rfl⟩ : syracuseStep 8899631 = 13349447) B13349447
theorem B1757321 : Blo 778337 1757321 := bstep (se 2 (by rfl) ⟨658995, by rfl⟩ : syracuseStep 1757321 = 1317991) B1317991
theorem B12669473 : Blo 778337 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B50582393 : Blo 778337 50582393 := bstep (se 2 (by rfl) ⟨18968397, by rfl⟩ : syracuseStep 50582393 = 37936795) B37936795
theorem B1758671 : Blo 778337 1758671 := bstep (se 1 (by rfl) ⟨1319003, by rfl⟩ : syracuseStep 1758671 = 2638007) B2638007
theorem B12834395 : Blo 778337 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B11983247 : Blo 778337 11983247 := bstep (se 1 (by rfl) ⟨8987435, by rfl⟩ : syracuseStep 11983247 = 17974871) B17974871
theorem B1169855 : Blo 778337 1169855 := bstep (se 1 (by rfl) ⟨877391, by rfl⟩ : syracuseStep 1169855 = 1754783) B1754783
theorem B1170023 : Blo 778337 1170023 := bstep (se 1 (by rfl) ⟨877517, by rfl⟩ : syracuseStep 1170023 = 1755035) B1755035
theorem B1170155 : Blo 778337 1170155 := bstep (se 1 (by rfl) ⟨877616, by rfl⟩ : syracuseStep 1170155 = 1755233) B1755233
theorem B1170599 : Blo 778337 1170599 := bstep (se 1 (by rfl) ⟨877949, by rfl⟩ : syracuseStep 1170599 = 1755899) B1755899
theorem B3956687 : Blo 778337 3956687 := bstep (se 1 (by rfl) ⟨2967515, by rfl⟩ : syracuseStep 3956687 = 5935031) B5935031
theorem B778351 : Blo 778337 778351 := bstep (se 1 (by rfl) ⟨583763, by rfl⟩ : syracuseStep 778351 = 1167527) B1167527
theorem B778395 : Blo 778337 778395 := bstep (se 1 (by rfl) ⟨583796, by rfl⟩ : syracuseStep 778395 = 1167593) B1167593
theorem B876703 : Blo 778337 876703 := bstep (se 1 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 876703 = 1315055) B1315055
theorem B7495841 : Blo 778337 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B778751 : Blo 778337 778751 := bstep (se 1 (by rfl) ⟨584063, by rfl⟩ : syracuseStep 778751 = 1168127) B1168127
theorem B2220671 : Blo 778337 2220671 := bstep (se 1 (by rfl) ⟨1665503, by rfl⟩ : syracuseStep 2220671 = 3331007) B3331007
theorem B778983 : Blo 778337 778983 := bstep (se 1 (by rfl) ⟨584237, by rfl⟩ : syracuseStep 778983 = 1168475) B1168475
theorem B1172219 : Blo 778337 1172219 := bstep (se 1 (by rfl) ⟨879164, by rfl⟩ : syracuseStep 1172219 = 1758329) B1758329
theorem B779007 : Blo 778337 779007 := bstep (se 1 (by rfl) ⟨584255, by rfl⟩ : syracuseStep 779007 = 1168511) B1168511
theorem B877567 : Blo 778337 877567 := bstep (se 1 (by rfl) ⟨658175, by rfl⟩ : syracuseStep 877567 = 1316351) B1316351
theorem B131785825 : Blo 778337 131785825 := bstep (se 2 (by rfl) ⟨49419684, by rfl⟩ : syracuseStep 131785825 = 98839369) B98839369
theorem B779503 : Blo 778337 779503 := bstep (se 1 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 779503 = 1169255) B1169255
theorem B779519 : Blo 778337 779519 := bstep (se 1 (by rfl) ⟨584639, by rfl⟩ : syracuseStep 779519 = 1169279) B1169279
theorem B779547 : Blo 778337 779547 := bstep (se 1 (by rfl) ⟨584660, by rfl⟩ : syracuseStep 779547 = 1169321) B1169321
theorem B779583 : Blo 778337 779583 := bstep (se 1 (by rfl) ⟨584687, by rfl⟩ : syracuseStep 779583 = 1169375) B1169375
theorem B780351 : Blo 778337 780351 := bstep (se 1 (by rfl) ⟨585263, by rfl⟩ : syracuseStep 780351 = 1170527) B1170527
theorem B781055 : Blo 778337 781055 := bstep (se 1 (by rfl) ⟨585791, by rfl⟩ : syracuseStep 781055 = 1171583) B1171583
theorem B6318911 : Blo 778337 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B781439 : Blo 778337 781439 := bstep (se 1 (by rfl) ⟨586079, by rfl⟩ : syracuseStep 781439 = 1172159) B1172159
theorem B5926283 : Blo 778337 5926283 := bstep (se 1 (by rfl) ⟨4444712, by rfl⟩ : syracuseStep 5926283 = 8889425) B8889425
theorem B781775 : Blo 778337 781775 := bstep (se 1 (by rfl) ⟨586331, by rfl⟩ : syracuseStep 781775 = 1172663) B1172663
theorem B782107 : Blo 778337 782107 := bstep (se 1 (by rfl) ⟨586580, by rfl⟩ : syracuseStep 782107 = 1173161) B1173161
theorem B1504057 : Blo 778337 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B474543859 : Blo 778337 474543859 := bstep (se 1 (by rfl) ⟨355907894, by rfl⟩ : syracuseStep 474543859 = 711815789) B711815789
theorem B493419059 : Blo 778337 493419059 := bstep (se 1 (by rfl) ⟨370064294, by rfl⟩ : syracuseStep 493419059 = 740128589) B740128589
theorem B8421403 : Blo 778337 8421403 := bstep (se 1 (by rfl) ⟨6316052, by rfl⟩ : syracuseStep 8421403 = 12632105) B12632105
theorem B17301995 : Blo 778337 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B4753291 : Blo 778337 4753291 := bstep (se 1 (by rfl) ⟨3564968, by rfl⟩ : syracuseStep 4753291 = 7129937) B7129937
theorem B5933087 : Blo 778337 5933087 := bstep (se 1 (by rfl) ⟨4449815, by rfl⟩ : syracuseStep 5933087 = 8899631) B8899631
theorem B33721595 : Blo 778337 33721595 := bstep (se 1 (by rfl) ⟨25291196, by rfl⟩ : syracuseStep 33721595 = 50582393) B50582393
theorem B8556263 : Blo 778337 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B1970345 : Blo 778337 1970345 := bstep (se 2 (by rfl) ⟨738879, by rfl⟩ : syracuseStep 1970345 = 1477759) B1477759
theorem B1480447 : Blo 778337 1480447 := bstep (se 1 (by rfl) ⟨1110335, by rfl⟩ : syracuseStep 1480447 = 2220671) B2220671
theorem B2005409 : Blo 778337 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B1317343 : Blo 778337 1317343 := bstep (se 1 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 1317343 = 1976015) B1976015
theorem B2497691 : Blo 778337 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B35986675 : Blo 778337 35986675 := bstep (se 1 (by rfl) ⟨26990006, by rfl⟩ : syracuseStep 35986675 = 53980013) B53980013
theorem B2629097 : Blo 778337 2629097 := bstep (se 2 (by rfl) ⟨985911, by rfl⟩ : syracuseStep 2629097 = 1971823) B1971823
theorem B632725145 : Blo 778337 632725145 := bstep (se 2 (by rfl) ⟨237271929, by rfl⟩ : syracuseStep 632725145 = 474543859) B474543859
theorem B1583329 : Blo 778337 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B1878881 : Blo 778337 1878881 := bstep (se 2 (by rfl) ⟨704580, by rfl⟩ : syracuseStep 1878881 = 1409161) B1409161
theorem B1322303 : Blo 778337 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B33828515 : Blo 778337 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B9645947 : Blo 778337 9645947 := bstep (se 1 (by rfl) ⟨7234460, by rfl⟩ : syracuseStep 9645947 = 14468921) B14468921
theorem B32026589 : Blo 778337 32026589 := bstep (se 3 (by rfl) ⟨6004985, by rfl⟩ : syracuseStep 32026589 = 12009971) B12009971
theorem B175714433 : Blo 778337 175714433 := bstep (se 2 (by rfl) ⟨65892912, by rfl⟩ : syracuseStep 175714433 = 131785825) B131785825
theorem B1979113 : Blo 778337 1979113 := bstep (se 2 (by rfl) ⟨742167, by rfl⟩ : syracuseStep 1979113 = 1484335) B1484335
theorem B63943505 : Blo 778337 63943505 := bstep (se 2 (by rfl) ⟨23978814, by rfl⟩ : syracuseStep 63943505 = 47957629) B47957629
theorem B2635037 : Blo 778337 2635037 := bstep (se 3 (by rfl) ⟨494069, by rfl⟩ : syracuseStep 2635037 = 988139) B988139
theorem B1751579 : Blo 778337 1751579 := bstep (se 1 (by rfl) ⟨1313684, by rfl⟩ : syracuseStep 1751579 = 2627369) B2627369
theorem B835007 : Blo 778337 835007 := bstep (se 1 (by rfl) ⟨626255, by rfl⟩ : syracuseStep 835007 = 1252511) B1252511
theorem B8568575 : Blo 778337 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B2637791 : Blo 778337 2637791 := bstep (se 1 (by rfl) ⟨1978343, by rfl⟩ : syracuseStep 2637791 = 3956687) B3956687
theorem B4997227 : Blo 778337 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B1754423 : Blo 778337 1754423 := bstep (se 1 (by rfl) ⟨1315817, by rfl⟩ : syracuseStep 1754423 = 2631635) B2631635
theorem B4212607 : Blo 778337 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B3950855 : Blo 778337 3950855 := bstep (se 1 (by rfl) ⟨2963141, by rfl⟩ : syracuseStep 3950855 = 5926283) B5926283
theorem B2673263 : Blo 778337 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B328946039 : Blo 778337 328946039 := bstep (se 1 (by rfl) ⟨246709529, by rfl⟩ : syracuseStep 328946039 = 493419059) B493419059
theorem B1167839 : Blo 778337 1167839 := bstep (se 1 (by rfl) ⟨875879, by rfl⟩ : syracuseStep 1167839 = 1751759) B1751759
theorem B1167899 : Blo 778337 1167899 := bstep (se 1 (by rfl) ⟨875924, by rfl⟩ : syracuseStep 1167899 = 1751849) B1751849
theorem B1168091 : Blo 778337 1168091 := bstep (se 1 (by rfl) ⟨876068, by rfl⟩ : syracuseStep 1168091 = 1752137) B1752137
theorem B4445351 : Blo 778337 4445351 := bstep (se 1 (by rfl) ⟨3334013, by rfl⟩ : syracuseStep 4445351 = 6668027) B6668027
theorem B1168937 : Blo 778337 1168937 := bstep (se 2 (by rfl) ⟨438351, by rfl⟩ : syracuseStep 1168937 = 876703) B876703
theorem B1758761 : Blo 778337 1758761 := bstep (se 2 (by rfl) ⟨659535, by rfl⟩ : syracuseStep 1758761 = 1319071) B1319071
theorem B1168943 : Blo 778337 1168943 := bstep (se 1 (by rfl) ⟨876707, by rfl⟩ : syracuseStep 1168943 = 1753415) B1753415
theorem B1169003 : Blo 778337 1169003 := bstep (se 1 (by rfl) ⟨876752, by rfl⟩ : syracuseStep 1169003 = 1753505) B1753505
theorem B1169663 : Blo 778337 1169663 := bstep (se 1 (by rfl) ⟨877247, by rfl⟩ : syracuseStep 1169663 = 1754495) B1754495
theorem B1170011 : Blo 778337 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B1170089 : Blo 778337 1170089 := bstep (se 2 (by rfl) ⟨438783, by rfl⟩ : syracuseStep 1170089 = 877567) B877567
theorem B1170743 : Blo 778337 1170743 := bstep (se 1 (by rfl) ⟨878057, by rfl⟩ : syracuseStep 1170743 = 1756115) B1756115
theorem B4874089 : Blo 778337 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B1171547 : Blo 778337 1171547 := bstep (se 1 (by rfl) ⟨878660, by rfl⟩ : syracuseStep 1171547 = 1757321) B1757321
theorem B36036917 : Blo 778337 36036917 := bstep (se 5 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 36036917 = 3378461) B3378461
theorem B8446315 : Blo 778337 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B36004823 : Blo 778337 36004823 := bstep (se 1 (by rfl) ⟨27003617, by rfl⟩ : syracuseStep 36004823 = 54007235) B54007235
theorem B1172447 : Blo 778337 1172447 := bstep (se 1 (by rfl) ⟨879335, by rfl⟩ : syracuseStep 1172447 = 1758671) B1758671
theorem B877927 : Blo 778337 877927 := bstep (se 1 (by rfl) ⟨658445, by rfl⟩ : syracuseStep 877927 = 1316891) B1316891
theorem B7988831 : Blo 778337 7988831 := bstep (se 1 (by rfl) ⟨5991623, by rfl⟩ : syracuseStep 7988831 = 11983247) B11983247
theorem B779903 : Blo 778337 779903 := bstep (se 1 (by rfl) ⟨584927, by rfl⟩ : syracuseStep 779903 = 1169855) B1169855
theorem B780015 : Blo 778337 780015 := bstep (se 1 (by rfl) ⟨585011, by rfl⟩ : syracuseStep 780015 = 1170023) B1170023
theorem B780103 : Blo 778337 780103 := bstep (se 1 (by rfl) ⟨585077, by rfl⟩ : syracuseStep 780103 = 1170155) B1170155
theorem B878683 : Blo 778337 878683 := bstep (se 1 (by rfl) ⟨659012, by rfl⟩ : syracuseStep 878683 = 1318025) B1318025
theorem B780399 : Blo 778337 780399 := bstep (se 1 (by rfl) ⟨585299, by rfl⟩ : syracuseStep 780399 = 1170599) B1170599
theorem B1665299 : Blo 778337 1665299 := bstep (se 1 (by rfl) ⟨1248974, by rfl⟩ : syracuseStep 1665299 = 2497949) B2497949
theorem B781479 : Blo 778337 781479 := bstep (se 1 (by rfl) ⟨586109, by rfl⟩ : syracuseStep 781479 = 1172219) B1172219
theorem B5074553 : Blo 778337 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B5929199 : Blo 778337 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B5930171 : Blo 778337 5930171 := bstep (se 1 (by rfl) ⟨4447628, by rfl⟩ : syracuseStep 5930171 = 8895257) B8895257
theorem B7503839 : Blo 778337 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B11534663 : Blo 778337 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B22481063 : Blo 778337 22481063 := bstep (se 1 (by rfl) ⟨16860797, by rfl⟩ : syracuseStep 22481063 = 33721595) B33721595
theorem B5704175 : Blo 778337 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B1313563 : Blo 778337 1313563 := bstep (se 1 (by rfl) ⟨985172, by rfl⟩ : syracuseStep 1313563 = 1970345) B1970345
theorem B24024611 : Blo 778337 24024611 := bstep (se 1 (by rfl) ⟨18018458, by rfl⟩ : syracuseStep 24024611 = 36036917) B36036917
theorem B5347757 : Blo 778337 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B1973929 : Blo 778337 1973929 := bstep (se 2 (by rfl) ⟨740223, by rfl⟩ : syracuseStep 1973929 = 1480447) B1480447
theorem B3383035 : Blo 778337 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B22552343 : Blo 778337 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B6430631 : Blo 778337 6430631 := bstep (se 1 (by rfl) ⟨4822973, by rfl⟩ : syracuseStep 6430631 = 9645947) B9645947
theorem B47982233 : Blo 778337 47982233 := bstep (se 2 (by rfl) ⟨17993337, by rfl⟩ : syracuseStep 47982233 = 35986675) B35986675
theorem B6498785 : Blo 778337 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B5712383 : Blo 778337 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B6662969 : Blo 778337 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B2633903 : Blo 778337 2633903 := bstep (se 1 (by rfl) ⟨1975427, by rfl⟩ : syracuseStep 2633903 = 3950855) B3950855
theorem B1782175 : Blo 778337 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B5616809 : Blo 778337 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B6337721 : Blo 778337 6337721 := bstep (se 2 (by rfl) ⟨2376645, by rfl⟩ : syracuseStep 6337721 = 4753291) B4753291
theorem B219297359 : Blo 778337 219297359 := bstep (se 1 (by rfl) ⟨164473019, by rfl⟩ : syracuseStep 219297359 = 328946039) B328946039
theorem B2111105 : Blo 778337 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B2963567 : Blo 778337 2963567 := bstep (se 1 (by rfl) ⟨2222675, by rfl⟩ : syracuseStep 2963567 = 4445351) B4445351
theorem B1752731 : Blo 778337 1752731 := bstep (se 1 (by rfl) ⟨1314548, by rfl⟩ : syracuseStep 1752731 = 2629097) B2629097
theorem B24003215 : Blo 778337 24003215 := bstep (se 1 (by rfl) ⟨18002411, by rfl⟩ : syracuseStep 24003215 = 36004823) B36004823
theorem B2638817 : Blo 778337 2638817 := bstep (se 2 (by rfl) ⟨989556, by rfl⟩ : syracuseStep 2638817 = 1979113) B1979113
theorem B5325887 : Blo 778337 5325887 := bstep (se 1 (by rfl) ⟨3994415, by rfl⟩ : syracuseStep 5325887 = 7988831) B7988831
theorem B21351059 : Blo 778337 21351059 := bstep (se 1 (by rfl) ⟨16013294, by rfl⟩ : syracuseStep 21351059 = 32026589) B32026589
theorem B1756457 : Blo 778337 1756457 := bstep (se 2 (by rfl) ⟨658671, by rfl⟩ : syracuseStep 1756457 = 1317343) B1317343
theorem B3526141 : Blo 778337 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B1756691 : Blo 778337 1756691 := bstep (se 1 (by rfl) ⟨1317518, by rfl⟩ : syracuseStep 1756691 = 2635037) B2635037
theorem B3952799 : Blo 778337 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B1167719 : Blo 778337 1167719 := bstep (se 1 (by rfl) ⟨875789, by rfl⟩ : syracuseStep 1167719 = 1751579) B1751579
theorem B3953447 : Blo 778337 3953447 := bstep (se 1 (by rfl) ⟨2965085, by rfl⟩ : syracuseStep 3953447 = 5930171) B5930171
theorem B5002559 : Blo 778337 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B1758527 : Blo 778337 1758527 := bstep (se 1 (by rfl) ⟨1318895, by rfl⟩ : syracuseStep 1758527 = 2637791) B2637791
theorem B11228537 : Blo 778337 11228537 := bstep (se 2 (by rfl) ⟨4210701, by rfl⟩ : syracuseStep 11228537 = 8421403) B8421403
theorem B11261753 : Blo 778337 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B1169615 : Blo 778337 1169615 := bstep (se 1 (by rfl) ⟨877211, by rfl⟩ : syracuseStep 1169615 = 1754423) B1754423
theorem B3955391 : Blo 778337 3955391 := bstep (se 1 (by rfl) ⟨2966543, by rfl⟩ : syracuseStep 3955391 = 5933087) B5933087
theorem B1170569 : Blo 778337 1170569 := bstep (se 2 (by rfl) ⟨438963, by rfl⟩ : syracuseStep 1170569 = 877927) B877927
theorem B1171577 : Blo 778337 1171577 := bstep (se 2 (by rfl) ⟨439341, by rfl⟩ : syracuseStep 1171577 = 878683) B878683
theorem B778559 : Blo 778337 778559 := bstep (se 1 (by rfl) ⟨583919, by rfl⟩ : syracuseStep 778559 = 1167839) B1167839
theorem B778599 : Blo 778337 778599 := bstep (se 1 (by rfl) ⟨583949, by rfl⟩ : syracuseStep 778599 = 1167899) B1167899
theorem B778727 : Blo 778337 778727 := bstep (se 1 (by rfl) ⟨584045, by rfl⟩ : syracuseStep 778727 = 1168091) B1168091
theorem B779291 : Blo 778337 779291 := bstep (se 1 (by rfl) ⟨584468, by rfl⟩ : syracuseStep 779291 = 1168937) B1168937
theorem B1172507 : Blo 778337 1172507 := bstep (se 1 (by rfl) ⟨879380, by rfl⟩ : syracuseStep 1172507 = 1758761) B1758761
theorem B779295 : Blo 778337 779295 := bstep (se 1 (by rfl) ⟨584471, by rfl⟩ : syracuseStep 779295 = 1168943) B1168943
theorem B779335 : Blo 778337 779335 := bstep (se 1 (by rfl) ⟨584501, by rfl⟩ : syracuseStep 779335 = 1169003) B1169003
theorem B779775 : Blo 778337 779775 := bstep (se 1 (by rfl) ⟨584831, by rfl⟩ : syracuseStep 779775 = 1169663) B1169663
theorem B780007 : Blo 778337 780007 := bstep (se 1 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 780007 = 1170011) B1170011
theorem B780059 : Blo 778337 780059 := bstep (se 1 (by rfl) ⟨585044, by rfl⟩ : syracuseStep 780059 = 1170089) B1170089
theorem B1665127 : Blo 778337 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B780495 : Blo 778337 780495 := bstep (se 1 (by rfl) ⟨585371, by rfl⟩ : syracuseStep 780495 = 1170743) B1170743
theorem B421816763 : Blo 778337 421816763 := bstep (se 1 (by rfl) ⟨316362572, by rfl⟩ : syracuseStep 421816763 = 632725145) B632725145
theorem B781031 : Blo 778337 781031 := bstep (se 1 (by rfl) ⟨585773, by rfl⟩ : syracuseStep 781031 = 1171547) B1171547
theorem B781631 : Blo 778337 781631 := bstep (se 1 (by rfl) ⟨586223, by rfl⟩ : syracuseStep 781631 = 1172447) B1172447
theorem B1110199 : Blo 778337 1110199 := bstep (se 1 (by rfl) ⟨832649, by rfl⟩ : syracuseStep 1110199 = 1665299) B1665299
theorem B5010349 : Blo 778337 5010349 := bstep (se 3 (by rfl) ⟨939440, by rfl⟩ : syracuseStep 5010349 = 1878881) B1878881
theorem B117142955 : Blo 778337 117142955 := bstep (se 1 (by rfl) ⟨87857216, by rfl⟩ : syracuseStep 117142955 = 175714433) B175714433
theorem B42629003 : Blo 778337 42629003 := bstep (se 1 (by rfl) ⟨31971752, by rfl⟩ : syracuseStep 42629003 = 63943505) B63943505
theorem B2226685 : Blo 778337 2226685 := bstep (se 3 (by rfl) ⟨417503, by rfl⟩ : syracuseStep 2226685 = 835007) B835007
theorem B8880677 : Blo 778337 8880677 := bstep (se 4 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 8880677 = 1665127) B1665127
theorem B3802783 : Blo 778337 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B7507835 : Blo 778337 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B64065629 : Blo 778337 64065629 := bstep (se 3 (by rfl) ⟨12012305, by rfl⟩ : syracuseStep 64065629 = 24024611) B24024611
theorem B1480265 : Blo 778337 1480265 := bstep (se 2 (by rfl) ⟨555099, by rfl⟩ : syracuseStep 1480265 = 1110199) B1110199
theorem B4332523 : Blo 778337 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B3808255 : Blo 778337 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B3744539 : Blo 778337 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B78095303 : Blo 778337 78095303 := bstep (se 1 (by rfl) ⟨58571477, by rfl⟩ : syracuseStep 78095303 = 117142955) B117142955
theorem B28419335 : Blo 778337 28419335 := bstep (se 1 (by rfl) ⟨21314501, by rfl⟩ : syracuseStep 28419335 = 42629003) B42629003
theorem B1975711 : Blo 778337 1975711 := bstep (se 1 (by rfl) ⟨1481783, by rfl⟩ : syracuseStep 1975711 = 2963567) B2963567
theorem B68593397 : Blo 778337 68593397 := bstep (se 5 (by rfl) ⟨3215315, by rfl⟩ : syracuseStep 68593397 = 6430631) B6430631
theorem B2631905 : Blo 778337 2631905 := bstep (se 2 (by rfl) ⟨986964, by rfl⟩ : syracuseStep 2631905 = 1973929) B1973929
theorem B16002143 : Blo 778337 16002143 := bstep (se 1 (by rfl) ⟨12001607, by rfl⟩ : syracuseStep 16002143 = 24003215) B24003215
theorem B3550591 : Blo 778337 3550591 := bstep (se 1 (by rfl) ⟨2662943, by rfl⟩ : syracuseStep 3550591 = 5325887) B5325887
theorem B14987375 : Blo 778337 14987375 := bstep (se 1 (by rfl) ⟨11240531, by rfl⟩ : syracuseStep 14987375 = 22481063) B22481063
theorem B14234039 : Blo 778337 14234039 := bstep (se 1 (by rfl) ⟨10675529, by rfl⟩ : syracuseStep 14234039 = 21351059) B21351059
theorem B2635199 : Blo 778337 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B2635631 : Blo 778337 2635631 := bstep (se 1 (by rfl) ⟨1976723, by rfl⟩ : syracuseStep 2635631 = 3953447) B3953447
theorem B7485691 : Blo 778337 7485691 := bstep (se 1 (by rfl) ⟨5614268, by rfl⟩ : syracuseStep 7485691 = 11228537) B11228537
theorem B1751417 : Blo 778337 1751417 := bstep (se 2 (by rfl) ⟨656781, by rfl⟩ : syracuseStep 1751417 = 1313563) B1313563
theorem B2636927 : Blo 778337 2636927 := bstep (se 1 (by rfl) ⟨1977695, by rfl⟩ : syracuseStep 2636927 = 3955391) B3955391
theorem B4701521 : Blo 778337 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B2376233 : Blo 778337 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B4441979 : Blo 778337 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1755935 : Blo 778337 1755935 := bstep (se 1 (by rfl) ⟨1316951, by rfl⟩ : syracuseStep 1755935 = 2633903) B2633903
theorem B2968913 : Blo 778337 2968913 := bstep (se 2 (by rfl) ⟨1113342, by rfl⟩ : syracuseStep 2968913 = 2226685) B2226685
theorem B146198239 : Blo 778337 146198239 := bstep (se 1 (by rfl) ⟨109648679, by rfl⟩ : syracuseStep 146198239 = 219297359) B219297359
theorem B18042853 : Blo 778337 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B1168487 : Blo 778337 1168487 := bstep (se 1 (by rfl) ⟨876365, by rfl⟩ : syracuseStep 1168487 = 1752731) B1752731
theorem B7689775 : Blo 778337 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B1759211 : Blo 778337 1759211 := bstep (se 1 (by rfl) ⟨1319408, by rfl⟩ : syracuseStep 1759211 = 2638817) B2638817
theorem B1170971 : Blo 778337 1170971 := bstep (se 1 (by rfl) ⟨878228, by rfl⟩ : syracuseStep 1170971 = 1756457) B1756457
theorem B1171127 : Blo 778337 1171127 := bstep (se 1 (by rfl) ⟨878345, by rfl⟩ : syracuseStep 1171127 = 1756691) B1756691
theorem B778479 : Blo 778337 778479 := bstep (se 1 (by rfl) ⟨583859, by rfl⟩ : syracuseStep 778479 = 1167719) B1167719
theorem B16900589 : Blo 778337 16900589 := bstep (se 3 (by rfl) ⟨3168860, by rfl⟩ : syracuseStep 16900589 = 6337721) B6337721
theorem B3335039 : Blo 778337 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B1172351 : Blo 778337 1172351 := bstep (se 1 (by rfl) ⟨879263, by rfl⟩ : syracuseStep 1172351 = 1758527) B1758527
theorem B779743 : Blo 778337 779743 := bstep (se 1 (by rfl) ⟨584807, by rfl⟩ : syracuseStep 779743 = 1169615) B1169615
theorem B3565171 : Blo 778337 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B127952621 : Blo 778337 127952621 := bstep (se 3 (by rfl) ⟨23991116, by rfl⟩ : syracuseStep 127952621 = 47982233) B47982233
theorem B780379 : Blo 778337 780379 := bstep (se 1 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 780379 = 1170569) B1170569
theorem B15034895 : Blo 778337 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B781051 : Blo 778337 781051 := bstep (se 1 (by rfl) ⟨585788, by rfl⟩ : syracuseStep 781051 = 1171577) B1171577
theorem B781671 : Blo 778337 781671 := bstep (se 1 (by rfl) ⟨586253, by rfl⟩ : syracuseStep 781671 = 1172507) B1172507
theorem B6680465 : Blo 778337 6680465 := bstep (se 2 (by rfl) ⟨2505174, by rfl⟩ : syracuseStep 6680465 = 5010349) B5010349
theorem B281211175 : Blo 778337 281211175 := bstep (se 1 (by rfl) ⟨210908381, by rfl⟩ : syracuseStep 281211175 = 421816763) B421816763
theorem B1407403 : Blo 778337 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B4753561 : Blo 778337 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B986843 : Blo 778337 986843 := bstep (se 1 (by rfl) ⟨740132, by rfl⟩ : syracuseStep 986843 = 1480265) B1480265
theorem B24057137 : Blo 778337 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B2496359 : Blo 778337 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B18946223 : Blo 778337 18946223 := bstep (se 1 (by rfl) ⟨14209667, by rfl⟩ : syracuseStep 18946223 = 28419335) B28419335
theorem B85301747 : Blo 778337 85301747 := bstep (se 1 (by rfl) ⟨63976310, by rfl⟩ : syracuseStep 85301747 = 127952621) B127952621
theorem B1876537 : Blo 778337 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B779723941 : Blo 778337 779723941 := bstep (se 4 (by rfl) ⟨73099119, by rfl⟩ : syracuseStep 779723941 = 146198239) B146198239
theorem B5776697 : Blo 778337 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B1584155 : Blo 778337 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B2961319 : Blo 778337 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B2634281 : Blo 778337 2634281 := bstep (se 2 (by rfl) ⟨987855, by rfl⟩ : syracuseStep 2634281 = 1975711) B1975711
theorem B1979275 : Blo 778337 1979275 := bstep (se 1 (by rfl) ⟨1484456, by rfl⟩ : syracuseStep 1979275 = 2968913) B2968913
theorem B42710419 : Blo 778337 42710419 := bstep (se 1 (by rfl) ⟨32032814, by rfl⟩ : syracuseStep 42710419 = 64065629) B64065629
theorem B4734121 : Blo 778337 4734121 := bstep (se 2 (by rfl) ⟨1775295, by rfl⟩ : syracuseStep 4734121 = 3550591) B3550591
theorem B374948233 : Blo 778337 374948233 := bstep (se 2 (by rfl) ⟨140605587, by rfl⟩ : syracuseStep 374948233 = 281211175) B281211175
theorem B1754603 : Blo 778337 1754603 := bstep (se 1 (by rfl) ⟨1315952, by rfl⟩ : syracuseStep 1754603 = 2631905) B2631905
theorem B10668095 : Blo 778337 10668095 := bstep (se 1 (by rfl) ⟨8001071, by rfl⟩ : syracuseStep 10668095 = 16002143) B16002143
theorem B731662901 : Blo 778337 731662901 := bstep (se 5 (by rfl) ⟨34296698, by rfl⟩ : syracuseStep 731662901 = 68593397) B68593397
theorem B9489359 : Blo 778337 9489359 := bstep (se 1 (by rfl) ⟨7117019, by rfl⟩ : syracuseStep 9489359 = 14234039) B14234039
theorem B9980921 : Blo 778337 9980921 := bstep (se 2 (by rfl) ⟨3742845, by rfl⟩ : syracuseStep 9980921 = 7485691) B7485691
theorem B12537389 : Blo 778337 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B1756799 : Blo 778337 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B1757087 : Blo 778337 1757087 := bstep (se 1 (by rfl) ⟨1317815, by rfl⟩ : syracuseStep 1757087 = 2635631) B2635631
theorem B1167611 : Blo 778337 1167611 := bstep (se 1 (by rfl) ⟨875708, by rfl⟩ : syracuseStep 1167611 = 1751417) B1751417
theorem B1757951 : Blo 778337 1757951 := bstep (se 1 (by rfl) ⟨1318463, by rfl⟩ : syracuseStep 1757951 = 2636927) B2636927
theorem B5920451 : Blo 778337 5920451 := bstep (se 1 (by rfl) ⟨4440338, by rfl⟩ : syracuseStep 5920451 = 8880677) B8880677
theorem B1170623 : Blo 778337 1170623 := bstep (se 1 (by rfl) ⟨877967, by rfl⟩ : syracuseStep 1170623 = 1755935) B1755935
theorem B5070377 : Blo 778337 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B5005223 : Blo 778337 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B778991 : Blo 778337 778991 := bstep (se 1 (by rfl) ⟨584243, by rfl⟩ : syracuseStep 778991 = 1168487) B1168487
theorem B1172807 : Blo 778337 1172807 := bstep (se 1 (by rfl) ⟨879605, by rfl⟩ : syracuseStep 1172807 = 1759211) B1759211
theorem B780647 : Blo 778337 780647 := bstep (se 1 (by rfl) ⟨585485, by rfl⟩ : syracuseStep 780647 = 1170971) B1170971
theorem B780751 : Blo 778337 780751 := bstep (se 1 (by rfl) ⟨585563, by rfl⟩ : syracuseStep 780751 = 1171127) B1171127
theorem B11267059 : Blo 778337 11267059 := bstep (se 1 (by rfl) ⟨8450294, by rfl⟩ : syracuseStep 11267059 = 16900589) B16900589
theorem B2223359 : Blo 778337 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B781567 : Blo 778337 781567 := bstep (se 1 (by rfl) ⟨586175, by rfl⟩ : syracuseStep 781567 = 1172351) B1172351
theorem B52063535 : Blo 778337 52063535 := bstep (se 1 (by rfl) ⟨39047651, by rfl⟩ : syracuseStep 52063535 = 78095303) B78095303
theorem B10023263 : Blo 778337 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B10253033 : Blo 778337 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B4453643 : Blo 778337 4453643 := bstep (se 1 (by rfl) ⟨3340232, by rfl⟩ : syracuseStep 4453643 = 6680465) B6680465
theorem B9991583 : Blo 778337 9991583 := bstep (se 1 (by rfl) ⟨7493687, by rfl⟩ : syracuseStep 9991583 = 14987375) B14987375
theorem B5077673 : Blo 778337 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B7112063 : Blo 778337 7112063 := bstep (se 1 (by rfl) ⟨5334047, by rfl⟩ : syracuseStep 7112063 = 10668095) B10668095
theorem B1039631921 : Blo 778337 1039631921 := bstep (se 2 (by rfl) ⟨389861970, by rfl⟩ : syracuseStep 1039631921 = 779723941) B779723941
theorem B6653947 : Blo 778337 6653947 := bstep (se 1 (by rfl) ⟨4990460, by rfl⟩ : syracuseStep 6653947 = 9980921) B9980921
theorem B15404525 : Blo 778337 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B1482239 : Blo 778337 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B34709023 : Blo 778337 34709023 := bstep (se 1 (by rfl) ⟨26031767, by rfl⟩ : syracuseStep 34709023 = 52063535) B52063535
theorem B25304957 : Blo 778337 25304957 := bstep (se 3 (by rfl) ⟨4744679, by rfl⟩ : syracuseStep 25304957 = 9489359) B9489359
theorem B6661055 : Blo 778337 6661055 := bstep (se 1 (by rfl) ⟨4995791, by rfl⟩ : syracuseStep 6661055 = 9991583) B9991583
theorem B33433037 : Blo 778337 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B3385115 : Blo 778337 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B2631581 : Blo 778337 2631581 := bstep (se 3 (by rfl) ⟨493421, by rfl⟩ : syracuseStep 2631581 = 986843) B986843
theorem B2502049 : Blo 778337 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B6338081 : Blo 778337 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B16038091 : Blo 778337 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B3946967 : Blo 778337 3946967 := bstep (se 1 (by rfl) ⟨2960225, by rfl⟩ : syracuseStep 3946967 = 5920451) B5920451
theorem B15022745 : Blo 778337 15022745 := bstep (se 2 (by rfl) ⟨5633529, by rfl⟩ : syracuseStep 15022745 = 11267059) B11267059
theorem B12630815 : Blo 778337 12630815 := bstep (se 1 (by rfl) ⟨9473111, by rfl⟩ : syracuseStep 12630815 = 18946223) B18946223
theorem B56867831 : Blo 778337 56867831 := bstep (se 1 (by rfl) ⟨42650873, by rfl⟩ : syracuseStep 56867831 = 85301747) B85301747
theorem B3948425 : Blo 778337 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B2639033 : Blo 778337 2639033 := bstep (se 2 (by rfl) ⟨989637, by rfl⟩ : syracuseStep 2639033 = 1979275) B1979275
theorem B1756187 : Blo 778337 1756187 := bstep (se 1 (by rfl) ⟨1317140, by rfl⟩ : syracuseStep 1756187 = 2634281) B2634281
theorem B6835355 : Blo 778337 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B2969095 : Blo 778337 2969095 := bstep (se 1 (by rfl) ⟨2226821, by rfl⟩ : syracuseStep 2969095 = 4453643) B4453643
theorem B13521005 : Blo 778337 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B6312161 : Blo 778337 6312161 := bstep (se 2 (by rfl) ⟨2367060, by rfl⟩ : syracuseStep 6312161 = 4734121) B4734121
theorem B1169735 : Blo 778337 1169735 := bstep (se 1 (by rfl) ⟨877301, by rfl⟩ : syracuseStep 1169735 = 1754603) B1754603
theorem B487775267 : Blo 778337 487775267 := bstep (se 1 (by rfl) ⟨365831450, by rfl⟩ : syracuseStep 487775267 = 731662901) B731662901
theorem B1171199 : Blo 778337 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B1171391 : Blo 778337 1171391 := bstep (se 1 (by rfl) ⟨878543, by rfl⟩ : syracuseStep 1171391 = 1757087) B1757087
theorem B778407 : Blo 778337 778407 := bstep (se 1 (by rfl) ⟨583805, by rfl⟩ : syracuseStep 778407 = 1167611) B1167611
theorem B1171967 : Blo 778337 1171967 := bstep (se 1 (by rfl) ⟨878975, by rfl⟩ : syracuseStep 1171967 = 1757951) B1757951
theorem B1664239 : Blo 778337 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B780415 : Blo 778337 780415 := bstep (se 1 (by rfl) ⟨585311, by rfl⟩ : syracuseStep 780415 = 1170623) B1170623
theorem B3336815 : Blo 778337 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B781871 : Blo 778337 781871 := bstep (se 1 (by rfl) ⟨586403, by rfl⟩ : syracuseStep 781871 = 1172807) B1172807
theorem B56947225 : Blo 778337 56947225 := bstep (se 2 (by rfl) ⟨21355209, by rfl⟩ : syracuseStep 56947225 = 42710419) B42710419
theorem B4224413 : Blo 778337 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B7998895637 : Blo 778337 7998895637 := bstep (se 6 (by rfl) ⟨187474116, by rfl⟩ : syracuseStep 7998895637 = 374948233) B374948233
theorem B6682175 : Blo 778337 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B4556903 : Blo 778337 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B9014003 : Blo 778337 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B75929633 : Blo 778337 75929633 := bstep (se 2 (by rfl) ⟨28473612, by rfl⟩ : syracuseStep 75929633 = 56947225) B56947225
theorem B22288691 : Blo 778337 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B2631311 : Blo 778337 2631311 := bstep (se 1 (by rfl) ⟨1973483, by rfl⟩ : syracuseStep 2631311 = 3946967) B3946967
theorem B46278697 : Blo 778337 46278697 := bstep (se 2 (by rfl) ⟨17354511, by rfl⟩ : syracuseStep 46278697 = 34709023) B34709023
theorem B2632283 : Blo 778337 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B693087947 : Blo 778337 693087947 := bstep (se 1 (by rfl) ⟨519815960, by rfl⟩ : syracuseStep 693087947 = 1039631921) B1039631921
theorem B10269683 : Blo 778337 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B4208107 : Blo 778337 4208107 := bstep (se 1 (by rfl) ⟨3156080, by rfl⟩ : syracuseStep 4208107 = 6312161) B6312161
theorem B4440703 : Blo 778337 4440703 := bstep (se 1 (by rfl) ⟨3330527, by rfl⟩ : syracuseStep 4440703 = 6661055) B6661055
theorem B1754387 : Blo 778337 1754387 := bstep (se 1 (by rfl) ⟨1315790, by rfl⟩ : syracuseStep 1754387 = 2631581) B2631581
theorem B8898173 : Blo 778337 8898173 := bstep (se 3 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 8898173 = 3336815) B3336815
theorem B21384121 : Blo 778337 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B3952637 : Blo 778337 3952637 := bstep (se 3 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 3952637 = 1482239) B1482239
theorem B10015163 : Blo 778337 10015163 := bstep (se 1 (by rfl) ⟨7511372, by rfl⟩ : syracuseStep 10015163 = 15022745) B15022745
theorem B1759355 : Blo 778337 1759355 := bstep (se 1 (by rfl) ⟨1319516, by rfl⟩ : syracuseStep 1759355 = 2639033) B2639033
theorem B4741375 : Blo 778337 4741375 := bstep (se 1 (by rfl) ⟨3556031, by rfl⟩ : syracuseStep 4741375 = 7112063) B7112063
theorem B2218985 : Blo 778337 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B1170791 : Blo 778337 1170791 := bstep (se 1 (by rfl) ⟨878093, by rfl⟩ : syracuseStep 1170791 = 1756187) B1756187
theorem B8871929 : Blo 778337 8871929 := bstep (se 2 (by rfl) ⟨3326973, by rfl⟩ : syracuseStep 8871929 = 6653947) B6653947
theorem B11265101 : Blo 778337 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B779823 : Blo 778337 779823 := bstep (se 1 (by rfl) ⟨584867, by rfl⟩ : syracuseStep 779823 = 1169735) B1169735
theorem B3336065 : Blo 778337 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B3958793 : Blo 778337 3958793 := bstep (se 2 (by rfl) ⟨1484547, by rfl⟩ : syracuseStep 3958793 = 2969095) B2969095
theorem B325183511 : Blo 778337 325183511 := bstep (se 1 (by rfl) ⟨243887633, by rfl⟩ : syracuseStep 325183511 = 487775267) B487775267
theorem B780799 : Blo 778337 780799 := bstep (se 1 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 780799 = 1171199) B1171199
theorem B16869971 : Blo 778337 16869971 := bstep (se 1 (by rfl) ⟨12652478, by rfl⟩ : syracuseStep 16869971 = 25304957) B25304957
theorem B780927 : Blo 778337 780927 := bstep (se 1 (by rfl) ⟨585695, by rfl⟩ : syracuseStep 780927 = 1171391) B1171391
theorem B781311 : Blo 778337 781311 := bstep (se 1 (by rfl) ⟨585983, by rfl⟩ : syracuseStep 781311 = 1171967) B1171967
theorem B2256743 : Blo 778337 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B5332597091 : Blo 778337 5332597091 := bstep (se 1 (by rfl) ⟨3999447818, by rfl⟩ : syracuseStep 5332597091 = 7998895637) B7998895637
theorem B4225387 : Blo 778337 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B4454783 : Blo 778337 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B8420543 : Blo 778337 8420543 := bstep (se 1 (by rfl) ⟨6315407, by rfl⟩ : syracuseStep 8420543 = 12630815) B12630815
theorem B37911887 : Blo 778337 37911887 := bstep (se 1 (by rfl) ⟨28433915, by rfl⟩ : syracuseStep 37911887 = 56867831) B56867831
theorem B5932115 : Blo 778337 5932115 := bstep (se 1 (by rfl) ⟨4449086, by rfl⟩ : syracuseStep 5932115 = 8898173) B8898173
theorem B61704929 : Blo 778337 61704929 := bstep (se 2 (by rfl) ⟨23139348, by rfl⟩ : syracuseStep 61704929 = 46278697) B46278697
theorem B28512161 : Blo 778337 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B1479323 : Blo 778337 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B7510067 : Blo 778337 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B11246647 : Blo 778337 11246647 := bstep (se 1 (by rfl) ⟨8434985, by rfl⟩ : syracuseStep 11246647 = 16869971) B16869971
theorem B5610809 : Blo 778337 5610809 := bstep (se 2 (by rfl) ⟨2104053, by rfl⟩ : syracuseStep 5610809 = 4208107) B4208107
theorem B5613695 : Blo 778337 5613695 := bstep (se 1 (by rfl) ⟨4210271, by rfl⟩ : syracuseStep 5613695 = 8420543) B8420543
theorem B25274591 : Blo 778337 25274591 := bstep (se 1 (by rfl) ⟨18955943, by rfl⟩ : syracuseStep 25274591 = 37911887) B37911887
theorem B48606965 : Blo 778337 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B6009335 : Blo 778337 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B2635091 : Blo 778337 2635091 := bstep (se 1 (by rfl) ⟨1976318, by rfl⟩ : syracuseStep 2635091 = 3952637) B3952637
theorem B5914619 : Blo 778337 5914619 := bstep (se 1 (by rfl) ⟨4435964, by rfl⟩ : syracuseStep 5914619 = 8871929) B8871929
theorem B1754207 : Blo 778337 1754207 := bstep (se 1 (by rfl) ⟨1315655, by rfl⟩ : syracuseStep 1754207 = 2631311) B2631311
theorem B2639195 : Blo 778337 2639195 := bstep (se 1 (by rfl) ⟨1979396, by rfl⟩ : syracuseStep 2639195 = 3958793) B3958793
theorem B1754855 : Blo 778337 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B2969855 : Blo 778337 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B5920937 : Blo 778337 5920937 := bstep (se 2 (by rfl) ⟨2220351, by rfl⟩ : syracuseStep 5920937 = 4440703) B4440703
theorem B1169591 : Blo 778337 1169591 := bstep (se 1 (by rfl) ⟨877193, by rfl⟩ : syracuseStep 1169591 = 1754387) B1754387
theorem B6676775 : Blo 778337 6676775 := bstep (se 1 (by rfl) ⟨5007581, by rfl⟩ : syracuseStep 6676775 = 10015163) B10015163
theorem B50619755 : Blo 778337 50619755 := bstep (se 1 (by rfl) ⟨37964816, by rfl⟩ : syracuseStep 50619755 = 75929633) B75929633
theorem B1172903 : Blo 778337 1172903 := bstep (se 1 (by rfl) ⟨879677, by rfl⟩ : syracuseStep 1172903 = 1759355) B1759355
theorem B780527 : Blo 778337 780527 := bstep (se 1 (by rfl) ⟨585395, by rfl⟩ : syracuseStep 780527 = 1170791) B1170791
theorem B59436509 : Blo 778337 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B2224043 : Blo 778337 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B216789007 : Blo 778337 216789007 := bstep (se 1 (by rfl) ⟨162591755, by rfl⟩ : syracuseStep 216789007 = 325183511) B325183511
theorem B462058631 : Blo 778337 462058631 := bstep (se 1 (by rfl) ⟨346543973, by rfl⟩ : syracuseStep 462058631 = 693087947) B693087947
theorem B1504495 : Blo 778337 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B6321833 : Blo 778337 6321833 := bstep (se 2 (by rfl) ⟨2370687, by rfl⟩ : syracuseStep 6321833 = 4741375) B4741375
theorem B5633849 : Blo 778337 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B6846455 : Blo 778337 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B3555064727 : Blo 778337 3555064727 := bstep (se 1 (by rfl) ⟨2666298545, by rfl⟩ : syracuseStep 3555064727 = 5332597091) B5332597091
theorem B19008107 : Blo 778337 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B18257213 : Blo 778337 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B289052009 : Blo 778337 289052009 := bstep (se 2 (by rfl) ⟨108394503, by rfl⟩ : syracuseStep 289052009 = 216789007) B216789007
theorem B3742463 : Blo 778337 3742463 := bstep (se 1 (by rfl) ⟨2806847, by rfl⟩ : syracuseStep 3742463 = 5613695) B5613695
theorem B16849727 : Blo 778337 16849727 := bstep (se 1 (by rfl) ⟨12637295, by rfl⟩ : syracuseStep 16849727 = 25274591) B25274591
theorem B2005993 : Blo 778337 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B1482695 : Blo 778337 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B4006223 : Blo 778337 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B3943079 : Blo 778337 3943079 := bstep (se 1 (by rfl) ⟨2957309, by rfl⟩ : syracuseStep 3943079 = 5914619) B5914619
theorem B3944861 : Blo 778337 3944861 := bstep (se 3 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 3944861 = 1479323) B1479323
theorem B1979903 : Blo 778337 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B3947291 : Blo 778337 3947291 := bstep (se 1 (by rfl) ⟨2960468, by rfl⟩ : syracuseStep 3947291 = 5920937) B5920937
theorem B164546477 : Blo 778337 164546477 := bstep (se 3 (by rfl) ⟨30852464, by rfl⟩ : syracuseStep 164546477 = 61704929) B61704929
theorem B308039087 : Blo 778337 308039087 := bstep (se 1 (by rfl) ⟨231029315, by rfl⟩ : syracuseStep 308039087 = 462058631) B462058631
theorem B14962157 : Blo 778337 14962157 := bstep (se 3 (by rfl) ⟨2805404, by rfl⟩ : syracuseStep 14962157 = 5610809) B5610809
theorem B1756727 : Blo 778337 1756727 := bstep (se 1 (by rfl) ⟨1317545, by rfl⟩ : syracuseStep 1756727 = 2635091) B2635091
theorem B4214555 : Blo 778337 4214555 := bstep (se 1 (by rfl) ⟨3160916, by rfl⟩ : syracuseStep 4214555 = 6321833) B6321833
theorem B3755899 : Blo 778337 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B14995529 : Blo 778337 14995529 := bstep (se 2 (by rfl) ⟨5623323, by rfl⟩ : syracuseStep 14995529 = 11246647) B11246647
theorem B3954743 : Blo 778337 3954743 := bstep (se 1 (by rfl) ⟨2966057, by rfl⟩ : syracuseStep 3954743 = 5932115) B5932115
theorem B1169471 : Blo 778337 1169471 := bstep (se 1 (by rfl) ⟨877103, by rfl⟩ : syracuseStep 1169471 = 1754207) B1754207
theorem B1759463 : Blo 778337 1759463 := bstep (se 1 (by rfl) ⟨1319597, by rfl⟩ : syracuseStep 1759463 = 2639195) B2639195
theorem B1169903 : Blo 778337 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B5006711 : Blo 778337 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B779727 : Blo 778337 779727 := bstep (se 1 (by rfl) ⟨584795, by rfl⟩ : syracuseStep 779727 = 1169591) B1169591
theorem B4451183 : Blo 778337 4451183 := bstep (se 1 (by rfl) ⟨3338387, by rfl⟩ : syracuseStep 4451183 = 6676775) B6676775
theorem B33746503 : Blo 778337 33746503 := bstep (se 1 (by rfl) ⟨25309877, by rfl⟩ : syracuseStep 33746503 = 50619755) B50619755
theorem B781935 : Blo 778337 781935 := bstep (se 1 (by rfl) ⟨586451, by rfl⟩ : syracuseStep 781935 = 1172903) B1172903
theorem B32404643 : Blo 778337 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B158497357 : Blo 778337 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B2370043151 : Blo 778337 2370043151 := bstep (se 1 (by rfl) ⟨1777532363, by rfl⟩ : syracuseStep 2370043151 = 3555064727) B3555064727
theorem B205359391 : Blo 778337 205359391 := bstep (se 1 (by rfl) ⟨154019543, by rfl⟩ : syracuseStep 205359391 = 308039087) B308039087
theorem B9997019 : Blo 778337 9997019 := bstep (se 1 (by rfl) ⟨7497764, by rfl⟩ : syracuseStep 9997019 = 14995529) B14995529
theorem B2494975 : Blo 778337 2494975 := bstep (se 1 (by rfl) ⟨1871231, by rfl⟩ : syracuseStep 2494975 = 3742463) B3742463
theorem B44995337 : Blo 778337 44995337 := bstep (se 2 (by rfl) ⟨16873251, by rfl⟩ : syracuseStep 44995337 = 33746503) B33746503
theorem B988463 : Blo 778337 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B2628719 : Blo 778337 2628719 := bstep (se 1 (by rfl) ⟨1971539, by rfl⟩ : syracuseStep 2628719 = 3943079) B3943079
theorem B2629907 : Blo 778337 2629907 := bstep (se 1 (by rfl) ⟨1972430, by rfl⟩ : syracuseStep 2629907 = 3944861) B3944861
theorem B211329809 : Blo 778337 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B21603095 : Blo 778337 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B1319935 : Blo 778337 1319935 := bstep (se 1 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 1319935 = 1979903) B1979903
theorem B2631527 : Blo 778337 2631527 := bstep (se 1 (by rfl) ⟨1973645, by rfl⟩ : syracuseStep 2631527 = 3947291) B3947291
theorem B9974771 : Blo 778337 9974771 := bstep (se 1 (by rfl) ⟨7481078, by rfl⟩ : syracuseStep 9974771 = 14962157) B14962157
theorem B12171475 : Blo 778337 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B2636495 : Blo 778337 2636495 := bstep (se 1 (by rfl) ⟨1977371, by rfl⟩ : syracuseStep 2636495 = 3954743) B3954743
theorem B2670815 : Blo 778337 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B2967455 : Blo 778337 2967455 := bstep (se 1 (by rfl) ⟨2225591, by rfl⟩ : syracuseStep 2967455 = 4451183) B4451183
theorem B2674657 : Blo 778337 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B1580028767 : Blo 778337 1580028767 := bstep (se 1 (by rfl) ⟨1185021575, by rfl⟩ : syracuseStep 1580028767 = 2370043151) B2370043151
theorem B109697651 : Blo 778337 109697651 := bstep (se 1 (by rfl) ⟨82273238, by rfl⟩ : syracuseStep 109697651 = 164546477) B164546477
theorem B12672071 : Blo 778337 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B1171151 : Blo 778337 1171151 := bstep (se 1 (by rfl) ⟨878363, by rfl⟩ : syracuseStep 1171151 = 1756727) B1756727
theorem B2809703 : Blo 778337 2809703 := bstep (se 1 (by rfl) ⟨2107277, by rfl⟩ : syracuseStep 2809703 = 4214555) B4214555
theorem B192701339 : Blo 778337 192701339 := bstep (se 1 (by rfl) ⟨144526004, by rfl⟩ : syracuseStep 192701339 = 289052009) B289052009
theorem B779647 : Blo 778337 779647 := bstep (se 1 (by rfl) ⟨584735, by rfl⟩ : syracuseStep 779647 = 1169471) B1169471
theorem B1172975 : Blo 778337 1172975 := bstep (se 1 (by rfl) ⟨879731, by rfl⟩ : syracuseStep 1172975 = 1759463) B1759463
theorem B779935 : Blo 778337 779935 := bstep (se 1 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 779935 = 1169903) B1169903
theorem B11233151 : Blo 778337 11233151 := bstep (se 1 (by rfl) ⟨8424863, by rfl⟩ : syracuseStep 11233151 = 16849727) B16849727
theorem B5007865 : Blo 778337 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B3337807 : Blo 778337 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B64914533 : Blo 778337 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B273812521 : Blo 778337 273812521 := bstep (se 2 (by rfl) ⟨102679695, by rfl⟩ : syracuseStep 273812521 = 205359391) B205359391
theorem B1873135 : Blo 778337 1873135 := bstep (se 1 (by rfl) ⟨1404851, by rfl⟩ : syracuseStep 1873135 = 2809703) B2809703
theorem B1780543 : Blo 778337 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B1978303 : Blo 778337 1978303 := bstep (se 1 (by rfl) ⟨1483727, by rfl⟩ : syracuseStep 1978303 = 2967455) B2967455
theorem B6664679 : Blo 778337 6664679 := bstep (se 1 (by rfl) ⟨4998509, by rfl⟩ : syracuseStep 6664679 = 9997019) B9997019
theorem B29996891 : Blo 778337 29996891 := bstep (se 1 (by rfl) ⟨22497668, by rfl⟩ : syracuseStep 29996891 = 44995337) B44995337
theorem B2635901 : Blo 778337 2635901 := bstep (se 3 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 2635901 = 988463) B988463
theorem B1752479 : Blo 778337 1752479 := bstep (se 1 (by rfl) ⟨1314359, by rfl⟩ : syracuseStep 1752479 = 2628719) B2628719
theorem B1753271 : Blo 778337 1753271 := bstep (se 1 (by rfl) ⟨1314953, by rfl⟩ : syracuseStep 1753271 = 2629907) B2629907
theorem B140886539 : Blo 778337 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B14402063 : Blo 778337 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B128467559 : Blo 778337 128467559 := bstep (se 1 (by rfl) ⟨96350669, by rfl⟩ : syracuseStep 128467559 = 192701339) B192701339
theorem B3326633 : Blo 778337 3326633 := bstep (se 2 (by rfl) ⟨1247487, by rfl⟩ : syracuseStep 3326633 = 2494975) B2494975
theorem B1754351 : Blo 778337 1754351 := bstep (se 1 (by rfl) ⟨1315763, by rfl⟩ : syracuseStep 1754351 = 2631527) B2631527
theorem B7488767 : Blo 778337 7488767 := bstep (se 1 (by rfl) ⟨5616575, by rfl⟩ : syracuseStep 7488767 = 11233151) B11233151
theorem B1757663 : Blo 778337 1757663 := bstep (se 1 (by rfl) ⟨1318247, by rfl⟩ : syracuseStep 1757663 = 2636495) B2636495
theorem B1759913 : Blo 778337 1759913 := bstep (se 2 (by rfl) ⟨659967, by rfl⟩ : syracuseStep 1759913 = 1319935) B1319935
theorem B1053352511 : Blo 778337 1053352511 := bstep (se 1 (by rfl) ⟨790014383, by rfl⟩ : syracuseStep 1053352511 = 1580028767) B1580028767
theorem B6677153 : Blo 778337 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B73131767 : Blo 778337 73131767 := bstep (se 1 (by rfl) ⟨54848825, by rfl⟩ : syracuseStep 73131767 = 109697651) B109697651
theorem B8448047 : Blo 778337 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B4450409 : Blo 778337 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B780767 : Blo 778337 780767 := bstep (se 1 (by rfl) ⟨585575, by rfl⟩ : syracuseStep 780767 = 1171151) B1171151
theorem B3566209 : Blo 778337 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B781983 : Blo 778337 781983 := bstep (se 1 (by rfl) ⟨586487, by rfl⟩ : syracuseStep 781983 = 1172975) B1172975
theorem B6649847 : Blo 778337 6649847 := bstep (se 1 (by rfl) ⟨4987385, by rfl⟩ : syracuseStep 6649847 = 9974771) B9974771
theorem B9601375 : Blo 778337 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B4754945 : Blo 778337 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B2497513 : Blo 778337 2497513 := bstep (se 2 (by rfl) ⟨936567, by rfl⟩ : syracuseStep 2497513 = 1873135) B1873135
theorem B19997927 : Blo 778337 19997927 := bstep (se 1 (by rfl) ⟨14998445, by rfl⟩ : syracuseStep 19997927 = 29996891) B29996891
theorem B4433231 : Blo 778337 4433231 := bstep (se 1 (by rfl) ⟨3324923, by rfl⟩ : syracuseStep 4433231 = 6649847) B6649847
theorem B93924359 : Blo 778337 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B4992511 : Blo 778337 4992511 := bstep (se 1 (by rfl) ⟨3744383, by rfl⟩ : syracuseStep 4992511 = 7488767) B7488767
theorem B2374057 : Blo 778337 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B365083361 : Blo 778337 365083361 := bstep (se 2 (by rfl) ⟨136906260, by rfl⟩ : syracuseStep 365083361 = 273812521) B273812521
theorem B2637737 : Blo 778337 2637737 := bstep (se 2 (by rfl) ⟨989151, by rfl⟩ : syracuseStep 2637737 = 1978303) B1978303
theorem B702235007 : Blo 778337 702235007 := bstep (se 1 (by rfl) ⟨526676255, by rfl⟩ : syracuseStep 702235007 = 1053352511) B1053352511
theorem B2966939 : Blo 778337 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B4443119 : Blo 778337 4443119 := bstep (se 1 (by rfl) ⟨3332339, by rfl⟩ : syracuseStep 4443119 = 6664679) B6664679
theorem B1757267 : Blo 778337 1757267 := bstep (se 1 (by rfl) ⟨1317950, by rfl⟩ : syracuseStep 1757267 = 2635901) B2635901
theorem B1168319 : Blo 778337 1168319 := bstep (se 1 (by rfl) ⟨876239, by rfl⟩ : syracuseStep 1168319 = 1752479) B1752479
theorem B1168847 : Blo 778337 1168847 := bstep (se 1 (by rfl) ⟨876635, by rfl⟩ : syracuseStep 1168847 = 1753271) B1753271
theorem B85645039 : Blo 778337 85645039 := bstep (se 1 (by rfl) ⟨64233779, by rfl⟩ : syracuseStep 85645039 = 128467559) B128467559
theorem B2217755 : Blo 778337 2217755 := bstep (se 1 (by rfl) ⟨1663316, by rfl⟩ : syracuseStep 2217755 = 3326633) B3326633
theorem B43276355 : Blo 778337 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B1169567 : Blo 778337 1169567 := bstep (se 1 (by rfl) ⟨877175, by rfl⟩ : syracuseStep 1169567 = 1754351) B1754351
theorem B1171775 : Blo 778337 1171775 := bstep (se 1 (by rfl) ⟨878831, by rfl⟩ : syracuseStep 1171775 = 1757663) B1757663
theorem B1173275 : Blo 778337 1173275 := bstep (se 1 (by rfl) ⟨879956, by rfl⟩ : syracuseStep 1173275 = 1759913) B1759913
theorem B4451435 : Blo 778337 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B48754511 : Blo 778337 48754511 := bstep (se 1 (by rfl) ⟨36565883, by rfl⟩ : syracuseStep 48754511 = 73131767) B73131767
theorem B5632031 : Blo 778337 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B468156671 : Blo 778337 468156671 := bstep (se 1 (by rfl) ⟨351117503, by rfl⟩ : syracuseStep 468156671 = 702235007) B702235007
theorem B1478503 : Blo 778337 1478503 := bstep (se 1 (by rfl) ⟨1108877, by rfl⟩ : syracuseStep 1478503 = 2217755) B2217755
theorem B6656681 : Blo 778337 6656681 := bstep (se 2 (by rfl) ⟨2496255, by rfl⟩ : syracuseStep 6656681 = 4992511) B4992511
theorem B2955487 : Blo 778337 2955487 := bstep (se 1 (by rfl) ⟨2216615, by rfl⟩ : syracuseStep 2955487 = 4433231) B4433231
theorem B1977959 : Blo 778337 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B2962079 : Blo 778337 2962079 := bstep (se 1 (by rfl) ⟨2221559, by rfl⟩ : syracuseStep 2962079 = 4443119) B4443119
theorem B28850903 : Blo 778337 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B2967623 : Blo 778337 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B3754687 : Blo 778337 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B3165409 : Blo 778337 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B3330017 : Blo 778337 3330017 := bstep (se 2 (by rfl) ⟨1248756, by rfl⟩ : syracuseStep 3330017 = 2497513) B2497513
theorem B243388907 : Blo 778337 243388907 := bstep (se 1 (by rfl) ⟨182541680, by rfl⟩ : syracuseStep 243388907 = 365083361) B365083361
theorem B1758491 : Blo 778337 1758491 := bstep (se 1 (by rfl) ⟨1318868, by rfl⟩ : syracuseStep 1758491 = 2637737) B2637737
theorem B12801833 : Blo 778337 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B3169963 : Blo 778337 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B1171511 : Blo 778337 1171511 := bstep (se 1 (by rfl) ⟨878633, by rfl⟩ : syracuseStep 1171511 = 1757267) B1757267
theorem B778879 : Blo 778337 778879 := bstep (se 1 (by rfl) ⟨584159, by rfl⟩ : syracuseStep 778879 = 1168319) B1168319
theorem B779231 : Blo 778337 779231 := bstep (se 1 (by rfl) ⟨584423, by rfl⟩ : syracuseStep 779231 = 1168847) B1168847
theorem B779711 : Blo 778337 779711 := bstep (se 1 (by rfl) ⟨584783, by rfl⟩ : syracuseStep 779711 = 1169567) B1169567
theorem B781183 : Blo 778337 781183 := bstep (se 1 (by rfl) ⟨585887, by rfl⟩ : syracuseStep 781183 = 1171775) B1171775
theorem B13331951 : Blo 778337 13331951 := bstep (se 1 (by rfl) ⟨9998963, by rfl⟩ : syracuseStep 13331951 = 19997927) B19997927
theorem B782183 : Blo 778337 782183 := bstep (se 1 (by rfl) ⟨586637, by rfl⟩ : syracuseStep 782183 = 1173275) B1173275
theorem B62616239 : Blo 778337 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B114193385 : Blo 778337 114193385 := bstep (se 2 (by rfl) ⟨42822519, by rfl⟩ : syracuseStep 114193385 = 85645039) B85645039
theorem B32503007 : Blo 778337 32503007 := bstep (se 1 (by rfl) ⟨24377255, by rfl⟩ : syracuseStep 32503007 = 48754511) B48754511
theorem B1971337 : Blo 778337 1971337 := bstep (se 2 (by rfl) ⟨739251, by rfl⟩ : syracuseStep 1971337 = 1478503) B1478503
theorem B8887967 : Blo 778337 8887967 := bstep (se 1 (by rfl) ⟨6665975, by rfl⟩ : syracuseStep 8887967 = 13331951) B13331951
theorem B1318639 : Blo 778337 1318639 := bstep (se 1 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 1318639 = 1977959) B1977959
theorem B3940649 : Blo 778337 3940649 := bstep (se 2 (by rfl) ⟨1477743, by rfl⟩ : syracuseStep 3940649 = 2955487) B2955487
theorem B1974719 : Blo 778337 1974719 := bstep (se 1 (by rfl) ⟨1481039, by rfl⟩ : syracuseStep 1974719 = 2962079) B2962079
theorem B76128923 : Blo 778337 76128923 := bstep (se 1 (by rfl) ⟨57096692, by rfl⟩ : syracuseStep 76128923 = 114193385) B114193385
theorem B21668671 : Blo 778337 21668671 := bstep (se 1 (by rfl) ⟨16251503, by rfl⟩ : syracuseStep 21668671 = 32503007) B32503007
theorem B1978415 : Blo 778337 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B4437787 : Blo 778337 4437787 := bstep (se 1 (by rfl) ⟨3328340, by rfl⟩ : syracuseStep 4437787 = 6656681) B6656681
theorem B8534555 : Blo 778337 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B312104447 : Blo 778337 312104447 := bstep (se 1 (by rfl) ⟨234078335, by rfl⟩ : syracuseStep 312104447 = 468156671) B468156671
theorem B2220011 : Blo 778337 2220011 := bstep (se 1 (by rfl) ⟨1665008, by rfl⟩ : syracuseStep 2220011 = 3330017) B3330017
theorem B162259271 : Blo 778337 162259271 := bstep (se 1 (by rfl) ⟨121694453, by rfl⟩ : syracuseStep 162259271 = 243388907) B243388907
theorem B1172327 : Blo 778337 1172327 := bstep (se 1 (by rfl) ⟨879245, by rfl⟩ : syracuseStep 1172327 = 1758491) B1758491
theorem B5006249 : Blo 778337 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B4220545 : Blo 778337 4220545 := bstep (se 2 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 4220545 = 3165409) B3165409
theorem B781007 : Blo 778337 781007 := bstep (se 1 (by rfl) ⟨585755, by rfl⟩ : syracuseStep 781007 = 1171511) B1171511
theorem B41744159 : Blo 778337 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B19233935 : Blo 778337 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B4226617 : Blo 778337 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B1480007 : Blo 778337 1480007 := bstep (se 1 (by rfl) ⟨1110005, by rfl⟩ : syracuseStep 1480007 = 2220011) B2220011
theorem B2627099 : Blo 778337 2627099 := bstep (se 1 (by rfl) ⟨1970324, by rfl⟩ : syracuseStep 2627099 = 3940649) B3940649
theorem B108172847 : Blo 778337 108172847 := bstep (se 1 (by rfl) ⟨81129635, by rfl⟩ : syracuseStep 108172847 = 162259271) B162259271
theorem B1316479 : Blo 778337 1316479 := bstep (se 1 (by rfl) ⟨987359, by rfl⟩ : syracuseStep 1316479 = 1974719) B1974719
theorem B2628449 : Blo 778337 2628449 := bstep (se 2 (by rfl) ⟨985668, by rfl⟩ : syracuseStep 2628449 = 1971337) B1971337
theorem B1318943 : Blo 778337 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B27829439 : Blo 778337 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B12822623 : Blo 778337 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B5917049 : Blo 778337 5917049 := bstep (se 2 (by rfl) ⟨2218893, by rfl⟩ : syracuseStep 5917049 = 4437787) B4437787
theorem B5689703 : Blo 778337 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B1758185 : Blo 778337 1758185 := bstep (se 2 (by rfl) ⟨659319, by rfl⟩ : syracuseStep 1758185 = 1318639) B1318639
theorem B28891561 : Blo 778337 28891561 := bstep (se 2 (by rfl) ⟨10834335, by rfl⟩ : syracuseStep 28891561 = 21668671) B21668671
theorem B5627393 : Blo 778337 5627393 := bstep (se 2 (by rfl) ⟨2110272, by rfl⟩ : syracuseStep 5627393 = 4220545) B4220545
theorem B208069631 : Blo 778337 208069631 := bstep (se 1 (by rfl) ⟨156052223, by rfl⟩ : syracuseStep 208069631 = 312104447) B312104447
theorem B5925311 : Blo 778337 5925311 := bstep (se 1 (by rfl) ⟨4443983, by rfl⟩ : syracuseStep 5925311 = 8887967) B8887967
theorem B50752615 : Blo 778337 50752615 := bstep (se 1 (by rfl) ⟨38064461, by rfl⟩ : syracuseStep 50752615 = 76128923) B76128923
theorem B781551 : Blo 778337 781551 := bstep (se 1 (by rfl) ⟨586163, by rfl⟩ : syracuseStep 781551 = 1172327) B1172327
theorem B3337499 : Blo 778337 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B5635489 : Blo 778337 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B15172541 : Blo 778337 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B986671 : Blo 778337 986671 := bstep (se 1 (by rfl) ⟨740003, by rfl⟩ : syracuseStep 986671 = 1480007) B1480007
theorem B67670153 : Blo 778337 67670153 := bstep (se 2 (by rfl) ⟨25376307, by rfl⟩ : syracuseStep 67670153 = 50752615) B50752615
theorem B138713087 : Blo 778337 138713087 := bstep (se 1 (by rfl) ⟨104034815, by rfl⟩ : syracuseStep 138713087 = 208069631) B208069631
theorem B18552959 : Blo 778337 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B7513985 : Blo 778337 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B3944699 : Blo 778337 3944699 := bstep (se 1 (by rfl) ⟨2958524, by rfl⟩ : syracuseStep 3944699 = 5917049) B5917049
theorem B1751399 : Blo 778337 1751399 := bstep (se 1 (by rfl) ⟨1313549, by rfl⟩ : syracuseStep 1751399 = 2627099) B2627099
theorem B1752299 : Blo 778337 1752299 := bstep (se 1 (by rfl) ⟨1314224, by rfl⟩ : syracuseStep 1752299 = 2628449) B2628449
theorem B3751595 : Blo 778337 3751595 := bstep (se 1 (by rfl) ⟨2813696, by rfl⟩ : syracuseStep 3751595 = 5627393) B5627393
theorem B3950207 : Blo 778337 3950207 := bstep (se 1 (by rfl) ⟨2962655, by rfl⟩ : syracuseStep 3950207 = 5925311) B5925311
theorem B1755305 : Blo 778337 1755305 := bstep (se 2 (by rfl) ⟨658239, by rfl⟩ : syracuseStep 1755305 = 1316479) B1316479
theorem B38522081 : Blo 778337 38522081 := bstep (se 2 (by rfl) ⟨14445780, by rfl⟩ : syracuseStep 38522081 = 28891561) B28891561
theorem B1172123 : Blo 778337 1172123 := bstep (se 1 (by rfl) ⟨879092, by rfl⟩ : syracuseStep 1172123 = 1758185) B1758185
theorem B72115231 : Blo 778337 72115231 := bstep (se 1 (by rfl) ⟨54086423, by rfl⟩ : syracuseStep 72115231 = 108172847) B108172847
theorem B879295 : Blo 778337 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B8548415 : Blo 778337 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B2224999 : Blo 778337 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B1315561 : Blo 778337 1315561 := bstep (se 2 (by rfl) ⟨493335, by rfl⟩ : syracuseStep 1315561 = 986671) B986671
theorem B2629799 : Blo 778337 2629799 := bstep (se 1 (by rfl) ⟨1972349, by rfl⟩ : syracuseStep 2629799 = 3944699) B3944699
theorem B2501063 : Blo 778337 2501063 := bstep (se 1 (by rfl) ⟨1875797, by rfl⟩ : syracuseStep 2501063 = 3751595) B3751595
theorem B2633471 : Blo 778337 2633471 := bstep (se 1 (by rfl) ⟨1975103, by rfl⟩ : syracuseStep 2633471 = 3950207) B3950207
theorem B96153641 : Blo 778337 96153641 := bstep (se 2 (by rfl) ⟨36057615, by rfl⟩ : syracuseStep 96153641 = 72115231) B72115231
theorem B12368639 : Blo 778337 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B20037293 : Blo 778337 20037293 := bstep (se 3 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 20037293 = 7513985) B7513985
theorem B369901565 : Blo 778337 369901565 := bstep (se 3 (by rfl) ⟨69356543, by rfl⟩ : syracuseStep 369901565 = 138713087) B138713087
theorem B2966665 : Blo 778337 2966665 := bstep (se 2 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 2966665 = 2224999) B2224999
theorem B1167599 : Blo 778337 1167599 := bstep (se 1 (by rfl) ⟨875699, by rfl⟩ : syracuseStep 1167599 = 1751399) B1751399
theorem B1168199 : Blo 778337 1168199 := bstep (se 1 (by rfl) ⟨876149, by rfl⟩ : syracuseStep 1168199 = 1752299) B1752299
theorem B10115027 : Blo 778337 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B1170203 : Blo 778337 1170203 := bstep (se 1 (by rfl) ⟨877652, by rfl⟩ : syracuseStep 1170203 = 1755305) B1755305
theorem B25681387 : Blo 778337 25681387 := bstep (se 1 (by rfl) ⟨19261040, by rfl⟩ : syracuseStep 25681387 = 38522081) B38522081
theorem B45113435 : Blo 778337 45113435 := bstep (se 1 (by rfl) ⟨33835076, by rfl⟩ : syracuseStep 45113435 = 67670153) B67670153
theorem B1172393 : Blo 778337 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B781415 : Blo 778337 781415 := bstep (se 1 (by rfl) ⟨586061, by rfl⟩ : syracuseStep 781415 = 1172123) B1172123
theorem B5698943 : Blo 778337 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B64102427 : Blo 778337 64102427 := bstep (se 1 (by rfl) ⟨48076820, by rfl⟩ : syracuseStep 64102427 = 96153641) B96153641
theorem B1753199 : Blo 778337 1753199 := bstep (se 1 (by rfl) ⟨1314899, by rfl⟩ : syracuseStep 1753199 = 2629799) B2629799
theorem B1754081 : Blo 778337 1754081 := bstep (se 2 (by rfl) ⟨657780, by rfl⟩ : syracuseStep 1754081 = 1315561) B1315561
theorem B32983037 : Blo 778337 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B1755647 : Blo 778337 1755647 := bstep (se 1 (by rfl) ⟨1316735, by rfl⟩ : syracuseStep 1755647 = 2633471) B2633471
theorem B13358195 : Blo 778337 13358195 := bstep (se 1 (by rfl) ⟨10018646, by rfl⟩ : syracuseStep 13358195 = 20037293) B20037293
theorem B246601043 : Blo 778337 246601043 := bstep (se 1 (by rfl) ⟨184950782, by rfl⟩ : syracuseStep 246601043 = 369901565) B369901565
theorem B3955553 : Blo 778337 3955553 := bstep (se 2 (by rfl) ⟨1483332, by rfl⟩ : syracuseStep 3955553 = 2966665) B2966665
theorem B778399 : Blo 778337 778399 := bstep (se 1 (by rfl) ⟨583799, by rfl⟩ : syracuseStep 778399 = 1167599) B1167599
theorem B778799 : Blo 778337 778799 := bstep (se 1 (by rfl) ⟨584099, by rfl⟩ : syracuseStep 778799 = 1168199) B1168199
theorem B6743351 : Blo 778337 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B780135 : Blo 778337 780135 := bstep (se 1 (by rfl) ⟨585101, by rfl⟩ : syracuseStep 780135 = 1170203) B1170203
theorem B30075623 : Blo 778337 30075623 := bstep (se 1 (by rfl) ⟨22556717, by rfl⟩ : syracuseStep 30075623 = 45113435) B45113435
theorem B781595 : Blo 778337 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B1667375 : Blo 778337 1667375 := bstep (se 1 (by rfl) ⟨1250531, by rfl⟩ : syracuseStep 1667375 = 2501063) B2501063
theorem B3799295 : Blo 778337 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B34241849 : Blo 778337 34241849 := bstep (se 2 (by rfl) ⟨12840693, by rfl⟩ : syracuseStep 34241849 = 25681387) B25681387
theorem B21988691 : Blo 778337 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B164400695 : Blo 778337 164400695 := bstep (se 1 (by rfl) ⟨123300521, by rfl⟩ : syracuseStep 164400695 = 246601043) B246601043
theorem B42734951 : Blo 778337 42734951 := bstep (se 1 (by rfl) ⟨32051213, by rfl⟩ : syracuseStep 42734951 = 64102427) B64102427
theorem B4495567 : Blo 778337 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B2532863 : Blo 778337 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B2637035 : Blo 778337 2637035 := bstep (se 1 (by rfl) ⟨1977776, by rfl⟩ : syracuseStep 2637035 = 3955553) B3955553
theorem B22827899 : Blo 778337 22827899 := bstep (se 1 (by rfl) ⟨17120924, by rfl⟩ : syracuseStep 22827899 = 34241849) B34241849
theorem B1168799 : Blo 778337 1168799 := bstep (se 1 (by rfl) ⟨876599, by rfl⟩ : syracuseStep 1168799 = 1753199) B1753199
theorem B1169387 : Blo 778337 1169387 := bstep (se 1 (by rfl) ⟨877040, by rfl⟩ : syracuseStep 1169387 = 1754081) B1754081
theorem B1170431 : Blo 778337 1170431 := bstep (se 1 (by rfl) ⟨877823, by rfl⟩ : syracuseStep 1170431 = 1755647) B1755647
theorem B8905463 : Blo 778337 8905463 := bstep (se 1 (by rfl) ⟨6679097, by rfl⟩ : syracuseStep 8905463 = 13358195) B13358195
theorem B20050415 : Blo 778337 20050415 := bstep (se 1 (by rfl) ⟨15037811, by rfl⟩ : syracuseStep 20050415 = 30075623) B30075623
theorem B1111583 : Blo 778337 1111583 := bstep (se 1 (by rfl) ⟨833687, by rfl⟩ : syracuseStep 1111583 = 1667375) B1667375
theorem B5936975 : Blo 778337 5936975 := bstep (se 1 (by rfl) ⟨4452731, by rfl⟩ : syracuseStep 5936975 = 8905463) B8905463
theorem B14659127 : Blo 778337 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B15218599 : Blo 778337 15218599 := bstep (se 1 (by rfl) ⟨11413949, by rfl⟩ : syracuseStep 15218599 = 22827899) B22827899
theorem B28489967 : Blo 778337 28489967 := bstep (se 1 (by rfl) ⟨21367475, by rfl⟩ : syracuseStep 28489967 = 42734951) B42734951
theorem B2964221 : Blo 778337 2964221 := bstep (se 3 (by rfl) ⟨555791, by rfl⟩ : syracuseStep 2964221 = 1111583) B1111583
theorem B1688575 : Blo 778337 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B1758023 : Blo 778337 1758023 := bstep (se 1 (by rfl) ⟨1318517, by rfl⟩ : syracuseStep 1758023 = 2637035) B2637035
theorem B109600463 : Blo 778337 109600463 := bstep (se 1 (by rfl) ⟨82200347, by rfl⟩ : syracuseStep 109600463 = 164400695) B164400695
theorem B779199 : Blo 778337 779199 := bstep (se 1 (by rfl) ⟨584399, by rfl⟩ : syracuseStep 779199 = 1168799) B1168799
theorem B779591 : Blo 778337 779591 := bstep (se 1 (by rfl) ⟨584693, by rfl⟩ : syracuseStep 779591 = 1169387) B1169387
theorem B780287 : Blo 778337 780287 := bstep (se 1 (by rfl) ⟨585215, by rfl⟩ : syracuseStep 780287 = 1170431) B1170431
theorem B5994089 : Blo 778337 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B13366943 : Blo 778337 13366943 := bstep (se 1 (by rfl) ⟨10025207, by rfl⟩ : syracuseStep 13366943 = 20050415) B20050415
theorem B9772751 : Blo 778337 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B20291465 : Blo 778337 20291465 := bstep (se 2 (by rfl) ⟨7609299, by rfl⟩ : syracuseStep 20291465 = 15218599) B15218599
theorem B1976147 : Blo 778337 1976147 := bstep (se 1 (by rfl) ⟨1482110, by rfl⟩ : syracuseStep 1976147 = 2964221) B2964221
theorem B292267901 : Blo 778337 292267901 := bstep (se 3 (by rfl) ⟨54800231, by rfl⟩ : syracuseStep 292267901 = 109600463) B109600463
theorem B18993311 : Blo 778337 18993311 := bstep (se 1 (by rfl) ⟨14244983, by rfl⟩ : syracuseStep 18993311 = 28489967) B28489967
theorem B2251433 : Blo 778337 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B1172015 : Blo 778337 1172015 := bstep (se 1 (by rfl) ⟨879011, by rfl⟩ : syracuseStep 1172015 = 1758023) B1758023
theorem B3957983 : Blo 778337 3957983 := bstep (se 1 (by rfl) ⟨2968487, by rfl⟩ : syracuseStep 3957983 = 5936975) B5936975
theorem B3996059 : Blo 778337 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B8911295 : Blo 778337 8911295 := bstep (se 1 (by rfl) ⟨6683471, by rfl⟩ : syracuseStep 8911295 = 13366943) B13366943
theorem B10656157 : Blo 778337 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B1317431 : Blo 778337 1317431 := bstep (se 1 (by rfl) ⟨988073, by rfl⟩ : syracuseStep 1317431 = 1976147) B1976147
theorem B194845267 : Blo 778337 194845267 := bstep (se 1 (by rfl) ⟨146133950, by rfl⟩ : syracuseStep 194845267 = 292267901) B292267901
theorem B6003821 : Blo 778337 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B5940863 : Blo 778337 5940863 := bstep (se 1 (by rfl) ⟨4455647, by rfl⟩ : syracuseStep 5940863 = 8911295) B8911295
theorem B26060669 : Blo 778337 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B12662207 : Blo 778337 12662207 := bstep (se 1 (by rfl) ⟨9496655, by rfl⟩ : syracuseStep 12662207 = 18993311) B18993311
theorem B2638655 : Blo 778337 2638655 := bstep (se 1 (by rfl) ⟨1978991, by rfl⟩ : syracuseStep 2638655 = 3957983) B3957983
theorem B13527643 : Blo 778337 13527643 := bstep (se 1 (by rfl) ⟨10145732, by rfl⟩ : syracuseStep 13527643 = 20291465) B20291465
theorem B781343 : Blo 778337 781343 := bstep (se 1 (by rfl) ⟨586007, by rfl⟩ : syracuseStep 781343 = 1172015) B1172015
theorem B4002547 : Blo 778337 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B17373779 : Blo 778337 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B259793689 : Blo 778337 259793689 := bstep (se 2 (by rfl) ⟨97422633, by rfl⟩ : syracuseStep 259793689 = 194845267) B194845267
theorem B18036857 : Blo 778337 18036857 := bstep (se 2 (by rfl) ⟨6763821, by rfl⟩ : syracuseStep 18036857 = 13527643) B13527643
theorem B14208209 : Blo 778337 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B8441471 : Blo 778337 8441471 := bstep (se 1 (by rfl) ⟨6331103, by rfl⟩ : syracuseStep 8441471 = 12662207) B12662207
theorem B1759103 : Blo 778337 1759103 := bstep (se 1 (by rfl) ⟨1319327, by rfl⟩ : syracuseStep 1759103 = 2638655) B2638655
theorem B878287 : Blo 778337 878287 := bstep (se 1 (by rfl) ⟨658715, by rfl⟩ : syracuseStep 878287 = 1317431) B1317431
theorem B3960575 : Blo 778337 3960575 := bstep (se 1 (by rfl) ⟨2970431, by rfl⟩ : syracuseStep 3960575 = 5940863) B5940863
theorem B346391585 : Blo 778337 346391585 := bstep (se 2 (by rfl) ⟨129896844, by rfl⟩ : syracuseStep 346391585 = 259793689) B259793689
theorem B9472139 : Blo 778337 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B11582519 : Blo 778337 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B2640383 : Blo 778337 2640383 := bstep (se 1 (by rfl) ⟨1980287, by rfl⟩ : syracuseStep 2640383 = 3960575) B3960575
theorem B1171049 : Blo 778337 1171049 := bstep (se 2 (by rfl) ⟨439143, by rfl⟩ : syracuseStep 1171049 = 878287) B878287
theorem B5627647 : Blo 778337 5627647 := bstep (se 1 (by rfl) ⟨4220735, by rfl⟩ : syracuseStep 5627647 = 8441471) B8441471
theorem B1172735 : Blo 778337 1172735 := bstep (se 1 (by rfl) ⟨879551, by rfl⟩ : syracuseStep 1172735 = 1759103) B1759103
theorem B5336729 : Blo 778337 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B12024571 : Blo 778337 12024571 := bstep (se 1 (by rfl) ⟨9018428, by rfl⟩ : syracuseStep 12024571 = 18036857) B18036857
theorem B16032761 : Blo 778337 16032761 := bstep (se 2 (by rfl) ⟨6012285, by rfl⟩ : syracuseStep 16032761 = 12024571) B12024571
theorem B123546869 : Blo 778337 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B230927723 : Blo 778337 230927723 := bstep (se 1 (by rfl) ⟨173195792, by rfl⟩ : syracuseStep 230927723 = 346391585) B346391585
theorem B3557819 : Blo 778337 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B6314759 : Blo 778337 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B1760255 : Blo 778337 1760255 := bstep (se 1 (by rfl) ⟨1320191, by rfl⟩ : syracuseStep 1760255 = 2640383) B2640383
theorem B780699 : Blo 778337 780699 := bstep (se 1 (by rfl) ⟨585524, by rfl⟩ : syracuseStep 780699 = 1171049) B1171049
theorem B781823 : Blo 778337 781823 := bstep (se 1 (by rfl) ⟨586367, by rfl⟩ : syracuseStep 781823 = 1172735) B1172735
theorem B7503529 : Blo 778337 7503529 := bstep (se 2 (by rfl) ⟨2813823, by rfl⟩ : syracuseStep 7503529 = 5627647) B5627647
theorem B10688507 : Blo 778337 10688507 := bstep (se 1 (by rfl) ⟨8016380, by rfl⟩ : syracuseStep 10688507 = 16032761) B16032761
theorem B153951815 : Blo 778337 153951815 := bstep (se 1 (by rfl) ⟨115463861, by rfl⟩ : syracuseStep 153951815 = 230927723) B230927723
theorem B10004705 : Blo 778337 10004705 := bstep (se 2 (by rfl) ⟨3751764, by rfl⟩ : syracuseStep 10004705 = 7503529) B7503529
theorem B2371879 : Blo 778337 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B4209839 : Blo 778337 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B82364579 : Blo 778337 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B1173503 : Blo 778337 1173503 := bstep (se 1 (by rfl) ⟨880127, by rfl⟩ : syracuseStep 1173503 = 1760255) B1760255
theorem B102634543 : Blo 778337 102634543 := bstep (se 1 (by rfl) ⟨76975907, by rfl⟩ : syracuseStep 102634543 = 153951815) B153951815
theorem B7125671 : Blo 778337 7125671 := bstep (se 1 (by rfl) ⟨5344253, by rfl⟩ : syracuseStep 7125671 = 10688507) B10688507
theorem B3162505 : Blo 778337 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B6669803 : Blo 778337 6669803 := bstep (se 1 (by rfl) ⟨5002352, by rfl⟩ : syracuseStep 6669803 = 10004705) B10004705
theorem B2806559 : Blo 778337 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B54909719 : Blo 778337 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B782335 : Blo 778337 782335 := bstep (se 1 (by rfl) ⟨586751, by rfl⟩ : syracuseStep 782335 = 1173503) B1173503
theorem B1871039 : Blo 778337 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B36606479 : Blo 778337 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B136846057 : Blo 778337 136846057 := bstep (se 2 (by rfl) ⟨51317271, by rfl⟩ : syracuseStep 136846057 = 102634543) B102634543
theorem B4216673 : Blo 778337 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B4446535 : Blo 778337 4446535 := bstep (se 1 (by rfl) ⟨3334901, by rfl⟩ : syracuseStep 4446535 = 6669803) B6669803
theorem B4750447 : Blo 778337 4750447 := bstep (se 1 (by rfl) ⟨3562835, by rfl⟩ : syracuseStep 4750447 = 7125671) B7125671
theorem B97617277 : Blo 778337 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B4989437 : Blo 778337 4989437 := bstep (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) B1871039
theorem B182461409 : Blo 778337 182461409 := bstep (se 2 (by rfl) ⟨68423028, by rfl⟩ : syracuseStep 182461409 = 136846057) B136846057
theorem B6333929 : Blo 778337 6333929 := bstep (se 2 (by rfl) ⟨2375223, by rfl⟩ : syracuseStep 6333929 = 4750447) B4750447
theorem B2811115 : Blo 778337 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B5928713 : Blo 778337 5928713 := bstep (se 2 (by rfl) ⟨2223267, by rfl⟩ : syracuseStep 5928713 = 4446535) B4446535
theorem B121640939 : Blo 778337 121640939 := bstep (se 1 (by rfl) ⟨91230704, by rfl⟩ : syracuseStep 121640939 = 182461409) B182461409
theorem B520625477 : Blo 778337 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B3748153 : Blo 778337 3748153 := bstep (se 2 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 3748153 = 2811115) B2811115
theorem B3326291 : Blo 778337 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B3952475 : Blo 778337 3952475 := bstep (se 1 (by rfl) ⟨2964356, by rfl⟩ : syracuseStep 3952475 = 5928713) B5928713
theorem B4222619 : Blo 778337 4222619 := bstep (se 1 (by rfl) ⟨3166964, by rfl⟩ : syracuseStep 4222619 = 6333929) B6333929
theorem B347083651 : Blo 778337 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B2634983 : Blo 778337 2634983 := bstep (se 1 (by rfl) ⟨1976237, by rfl⟩ : syracuseStep 2634983 = 3952475) B3952475
theorem B4997537 : Blo 778337 4997537 := bstep (se 2 (by rfl) ⟨1874076, by rfl⟩ : syracuseStep 4997537 = 3748153) B3748153
theorem B2217527 : Blo 778337 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B81093959 : Blo 778337 81093959 := bstep (se 1 (by rfl) ⟨60820469, by rfl⟩ : syracuseStep 81093959 = 121640939) B121640939
theorem B2815079 : Blo 778337 2815079 := bstep (se 1 (by rfl) ⟨2111309, by rfl⟩ : syracuseStep 2815079 = 4222619) B4222619
theorem B7506877 : Blo 778337 7506877 := bstep (se 3 (by rfl) ⟨1407539, by rfl⟩ : syracuseStep 7506877 = 2815079) B2815079
theorem B1478351 : Blo 778337 1478351 := bstep (se 1 (by rfl) ⟨1108763, by rfl⟩ : syracuseStep 1478351 = 2217527) B2217527
theorem B1756655 : Blo 778337 1756655 := bstep (se 1 (by rfl) ⟨1317491, by rfl⟩ : syracuseStep 1756655 = 2634983) B2634983
theorem B3331691 : Blo 778337 3331691 := bstep (se 1 (by rfl) ⟨2498768, by rfl⟩ : syracuseStep 3331691 = 4997537) B4997537
theorem B54062639 : Blo 778337 54062639 := bstep (se 1 (by rfl) ⟨40546979, by rfl⟩ : syracuseStep 54062639 = 81093959) B81093959
theorem B462778201 : Blo 778337 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B3942269 : Blo 778337 3942269 := bstep (se 3 (by rfl) ⟨739175, by rfl⟩ : syracuseStep 3942269 = 1478351) B1478351
theorem B10009169 : Blo 778337 10009169 := bstep (se 2 (by rfl) ⟨3753438, by rfl⟩ : syracuseStep 10009169 = 7506877) B7506877
theorem B617037601 : Blo 778337 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B1171103 : Blo 778337 1171103 := bstep (se 1 (by rfl) ⟨878327, by rfl⟩ : syracuseStep 1171103 = 1756655) B1756655
theorem B2221127 : Blo 778337 2221127 := bstep (se 1 (by rfl) ⟨1665845, by rfl⟩ : syracuseStep 2221127 = 3331691) B3331691
theorem B36041759 : Blo 778337 36041759 := bstep (se 1 (by rfl) ⟨27031319, by rfl⟩ : syracuseStep 36041759 = 54062639) B54062639
theorem B1480751 : Blo 778337 1480751 := bstep (se 1 (by rfl) ⟨1110563, by rfl⟩ : syracuseStep 1480751 = 2221127) B2221127
theorem B2628179 : Blo 778337 2628179 := bstep (se 1 (by rfl) ⟨1971134, by rfl⟩ : syracuseStep 2628179 = 3942269) B3942269
theorem B24027839 : Blo 778337 24027839 := bstep (se 1 (by rfl) ⟨18020879, by rfl⟩ : syracuseStep 24027839 = 36041759) B36041759
theorem B822716801 : Blo 778337 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B6672779 : Blo 778337 6672779 := bstep (se 1 (by rfl) ⟨5004584, by rfl⟩ : syracuseStep 6672779 = 10009169) B10009169
theorem B780735 : Blo 778337 780735 := bstep (se 1 (by rfl) ⟨585551, by rfl⟩ : syracuseStep 780735 = 1171103) B1171103
theorem B987167 : Blo 778337 987167 := bstep (se 1 (by rfl) ⟨740375, by rfl⟩ : syracuseStep 987167 = 1480751) B1480751
theorem B548477867 : Blo 778337 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B1752119 : Blo 778337 1752119 := bstep (se 1 (by rfl) ⟨1314089, by rfl⟩ : syracuseStep 1752119 = 2628179) B2628179
theorem B4448519 : Blo 778337 4448519 := bstep (se 1 (by rfl) ⟨3336389, by rfl⟩ : syracuseStep 4448519 = 6672779) B6672779
theorem B16018559 : Blo 778337 16018559 := bstep (se 1 (by rfl) ⟨12013919, by rfl⟩ : syracuseStep 16018559 = 24027839) B24027839
theorem B2632445 : Blo 778337 2632445 := bstep (se 3 (by rfl) ⟨493583, by rfl⟩ : syracuseStep 2632445 = 987167) B987167
theorem B2965679 : Blo 778337 2965679 := bstep (se 1 (by rfl) ⟨2224259, by rfl⟩ : syracuseStep 2965679 = 4448519) B4448519
theorem B1168079 : Blo 778337 1168079 := bstep (se 1 (by rfl) ⟨876059, by rfl⟩ : syracuseStep 1168079 = 1752119) B1752119
theorem B365651911 : Blo 778337 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B10679039 : Blo 778337 10679039 := bstep (se 1 (by rfl) ⟨8009279, by rfl⟩ : syracuseStep 10679039 = 16018559) B16018559
theorem B7119359 : Blo 778337 7119359 := bstep (se 1 (by rfl) ⟨5339519, by rfl⟩ : syracuseStep 7119359 = 10679039) B10679039
theorem B1977119 : Blo 778337 1977119 := bstep (se 1 (by rfl) ⟨1482839, by rfl⟩ : syracuseStep 1977119 = 2965679) B2965679
theorem B487535881 : Blo 778337 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B1754963 : Blo 778337 1754963 := bstep (se 1 (by rfl) ⟨1316222, by rfl⟩ : syracuseStep 1754963 = 2632445) B2632445
theorem B778719 : Blo 778337 778719 := bstep (se 1 (by rfl) ⟨584039, by rfl⟩ : syracuseStep 778719 = 1168079) B1168079
theorem B1318079 : Blo 778337 1318079 := bstep (se 1 (by rfl) ⟨988559, by rfl⟩ : syracuseStep 1318079 = 1977119) B1977119
theorem B1169975 : Blo 778337 1169975 := bstep (se 1 (by rfl) ⟨877481, by rfl⟩ : syracuseStep 1169975 = 1754963) B1754963
theorem B4746239 : Blo 778337 4746239 := bstep (se 1 (by rfl) ⟨3559679, by rfl⟩ : syracuseStep 4746239 = 7119359) B7119359
theorem B650047841 : Blo 778337 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 778337 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B3164159 : Blo 778337 3164159 := bstep (se 1 (by rfl) ⟨2373119, by rfl⟩ : syracuseStep 3164159 = 4746239) B4746239
theorem B779983 : Blo 778337 779983 := bstep (se 1 (by rfl) ⟨584987, by rfl⟩ : syracuseStep 779983 = 1169975) B1169975
theorem B878719 : Blo 778337 878719 := bstep (se 1 (by rfl) ⟨659039, by rfl⟩ : syracuseStep 878719 = 1318079) B1318079
theorem B2109439 : Blo 778337 2109439 := bstep (se 1 (by rfl) ⟨1582079, by rfl⟩ : syracuseStep 2109439 = 3164159) B3164159
theorem B1171625 : Blo 778337 1171625 := bstep (se 2 (by rfl) ⟨439359, by rfl⟩ : syracuseStep 1171625 = 878719) B878719
theorem B288910151 : Blo 778337 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B2812585 : Blo 778337 2812585 := bstep (se 2 (by rfl) ⟨1054719, by rfl⟩ : syracuseStep 2812585 = 2109439) B2109439
theorem B781083 : Blo 778337 781083 := bstep (se 1 (by rfl) ⟨585812, by rfl⟩ : syracuseStep 781083 = 1171625) B1171625
theorem B192606767 : Blo 778337 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B3750113 : Blo 778337 3750113 := bstep (se 2 (by rfl) ⟨1406292, by rfl⟩ : syracuseStep 3750113 = 2812585) B2812585
theorem B128404511 : Blo 778337 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B2500075 : Blo 778337 2500075 := bstep (se 1 (by rfl) ⟨1875056, by rfl⟩ : syracuseStep 2500075 = 3750113) B3750113
theorem B85603007 : Blo 778337 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B57068671 : Blo 778337 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B3333433 : Blo 778337 3333433 := bstep (se 2 (by rfl) ⟨1250037, by rfl⟩ : syracuseStep 3333433 = 2500075) B2500075
theorem B76091561 : Blo 778337 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B4444577 : Blo 778337 4444577 := bstep (se 2 (by rfl) ⟨1666716, by rfl⟩ : syracuseStep 4444577 = 3333433) B3333433
theorem B50727707 : Blo 778337 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B2963051 : Blo 778337 2963051 := bstep (se 1 (by rfl) ⟨2222288, by rfl⟩ : syracuseStep 2963051 = 4444577) B4444577
theorem B33818471 : Blo 778337 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B1975367 : Blo 778337 1975367 := bstep (se 1 (by rfl) ⟨1481525, by rfl⟩ : syracuseStep 1975367 = 2963051) B2963051
theorem B22545647 : Blo 778337 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B1316911 : Blo 778337 1316911 := bstep (se 1 (by rfl) ⟨987683, by rfl⟩ : syracuseStep 1316911 = 1975367) B1975367
theorem B1755881 : Blo 778337 1755881 := bstep (se 2 (by rfl) ⟨658455, by rfl⟩ : syracuseStep 1755881 = 1316911) B1316911
theorem B15030431 : Blo 778337 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B1170587 : Blo 778337 1170587 := bstep (se 1 (by rfl) ⟨877940, by rfl⟩ : syracuseStep 1170587 = 1755881) B1755881
theorem B10020287 : Blo 778337 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B780391 : Blo 778337 780391 := bstep (se 1 (by rfl) ⟨585293, by rfl⟩ : syracuseStep 780391 = 1170587) B1170587
theorem B6680191 : Blo 778337 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B8906921 : Blo 778337 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5937947 : Blo 778337 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B3958631 : Blo 778337 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B2639087 : Blo 778337 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B1759391 : Blo 778337 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B1172927 : Blo 778337 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391
theorem B781951 : Blo 778337 781951 := bstep (se 1 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 781951 = 1172927) B1172927

theorem C0 (j : ℕ) (h1 : 194584 ≤ j) (h2 : j ≤ 195283) : Blo 778337 (4 * j + 3) := by
  interval_cases j
  · exact B778339
  · exact B778343
  · exact B778347
  · exact B778351
  · exact B778355
  · exact B778359
  · exact B778363
  · exact B778367
  · exact B778371
  · exact B778375
  · exact B778379
  · exact B778383
  · exact B778387
  · exact B778391
  · exact B778395
  · exact B778399
  · exact B778403
  · exact B778407
  · exact B778411
  · exact B778415
  · exact B778419
  · exact B778423
  · exact B778427
  · exact B778431
  · exact B778435
  · exact B778439
  · exact B778443
  · exact B778447
  · exact B778451
  · exact B778455
  · exact B778459
  · exact B778463
  · exact B778467
  · exact B778471
  · exact B778475
  · exact B778479
  · exact B778483
  · exact B778487
  · exact B778491
  · exact B778495
  · exact B778499
  · exact B778503
  · exact B778507
  · exact B778511
  · exact B778515
  · exact B778519
  · exact B778523
  · exact B778527
  · exact B778531
  · exact B778535
  · exact B778539
  · exact B778543
  · exact B778547
  · exact B778551
  · exact B778555
  · exact B778559
  · exact B778563
  · exact B778567
  · exact B778571
  · exact B778575
  · exact B778579
  · exact B778583
  · exact B778587
  · exact B778591
  · exact B778595
  · exact B778599
  · exact B778603
  · exact B778607
  · exact B778611
  · exact B778615
  · exact B778619
  · exact B778623
  · exact B778627
  · exact B778631
  · exact B778635
  · exact B778639
  · exact B778643
  · exact B778647
  · exact B778651
  · exact B778655
  · exact B778659
  · exact B778663
  · exact B778667
  · exact B778671
  · exact B778675
  · exact B778679
  · exact B778683
  · exact B778687
  · exact B778691
  · exact B778695
  · exact B778699
  · exact B778703
  · exact B778707
  · exact B778711
  · exact B778715
  · exact B778719
  · exact B778723
  · exact B778727
  · exact B778731
  · exact B778735
  · exact B778739
  · exact B778743
  · exact B778747
  · exact B778751
  · exact B778755
  · exact B778759
  · exact B778763
  · exact B778767
  · exact B778771
  · exact B778775
  · exact B778779
  · exact B778783
  · exact B778787
  · exact B778791
  · exact B778795
  · exact B778799
  · exact B778803
  · exact B778807
  · exact B778811
  · exact B778815
  · exact B778819
  · exact B778823
  · exact B778827
  · exact B778831
  · exact B778835
  · exact B778839
  · exact B778843
  · exact B778847
  · exact B778851
  · exact B778855
  · exact B778859
  · exact B778863
  · exact B778867
  · exact B778871
  · exact B778875
  · exact B778879
  · exact B778883
  · exact B778887
  · exact B778891
  · exact B778895
  · exact B778899
  · exact B778903
  · exact B778907
  · exact B778911
  · exact B778915
  · exact B778919
  · exact B778923
  · exact B778927
  · exact B778931
  · exact B778935
  · exact B778939
  · exact B778943
  · exact B778947
  · exact B778951
  · exact B778955
  · exact B778959
  · exact B778963
  · exact B778967
  · exact B778971
  · exact B778975
  · exact B778979
  · exact B778983
  · exact B778987
  · exact B778991
  · exact B778995
  · exact B778999
  · exact B779003
  · exact B779007
  · exact B779011
  · exact B779015
  · exact B779019
  · exact B779023
  · exact B779027
  · exact B779031
  · exact B779035
  · exact B779039
  · exact B779043
  · exact B779047
  · exact B779051
  · exact B779055
  · exact B779059
  · exact B779063
  · exact B779067
  · exact B779071
  · exact B779075
  · exact B779079
  · exact B779083
  · exact B779087
  · exact B779091
  · exact B779095
  · exact B779099
  · exact B779103
  · exact B779107
  · exact B779111
  · exact B779115
  · exact B779119
  · exact B779123
  · exact B779127
  · exact B779131
  · exact B779135
  · exact B779139
  · exact B779143
  · exact B779147
  · exact B779151
  · exact B779155
  · exact B779159
  · exact B779163
  · exact B779167
  · exact B779171
  · exact B779175
  · exact B779179
  · exact B779183
  · exact B779187
  · exact B779191
  · exact B779195
  · exact B779199
  · exact B779203
  · exact B779207
  · exact B779211
  · exact B779215
  · exact B779219
  · exact B779223
  · exact B779227
  · exact B779231
  · exact B779235
  · exact B779239
  · exact B779243
  · exact B779247
  · exact B779251
  · exact B779255
  · exact B779259
  · exact B779263
  · exact B779267
  · exact B779271
  · exact B779275
  · exact B779279
  · exact B779283
  · exact B779287
  · exact B779291
  · exact B779295
  · exact B779299
  · exact B779303
  · exact B779307
  · exact B779311
  · exact B779315
  · exact B779319
  · exact B779323
  · exact B779327
  · exact B779331
  · exact B779335
  · exact B779339
  · exact B779343
  · exact B779347
  · exact B779351
  · exact B779355
  · exact B779359
  · exact B779363
  · exact B779367
  · exact B779371
  · exact B779375
  · exact B779379
  · exact B779383
  · exact B779387
  · exact B779391
  · exact B779395
  · exact B779399
  · exact B779403
  · exact B779407
  · exact B779411
  · exact B779415
  · exact B779419
  · exact B779423
  · exact B779427
  · exact B779431
  · exact B779435
  · exact B779439
  · exact B779443
  · exact B779447
  · exact B779451
  · exact B779455
  · exact B779459
  · exact B779463
  · exact B779467
  · exact B779471
  · exact B779475
  · exact B779479
  · exact B779483
  · exact B779487
  · exact B779491
  · exact B779495
  · exact B779499
  · exact B779503
  · exact B779507
  · exact B779511
  · exact B779515
  · exact B779519
  · exact B779523
  · exact B779527
  · exact B779531
  · exact B779535
  · exact B779539
  · exact B779543
  · exact B779547
  · exact B779551
  · exact B779555
  · exact B779559
  · exact B779563
  · exact B779567
  · exact B779571
  · exact B779575
  · exact B779579
  · exact B779583
  · exact B779587
  · exact B779591
  · exact B779595
  · exact B779599
  · exact B779603
  · exact B779607
  · exact B779611
  · exact B779615
  · exact B779619
  · exact B779623
  · exact B779627
  · exact B779631
  · exact B779635
  · exact B779639
  · exact B779643
  · exact B779647
  · exact B779651
  · exact B779655
  · exact B779659
  · exact B779663
  · exact B779667
  · exact B779671
  · exact B779675
  · exact B779679
  · exact B779683
  · exact B779687
  · exact B779691
  · exact B779695
  · exact B779699
  · exact B779703
  · exact B779707
  · exact B779711
  · exact B779715
  · exact B779719
  · exact B779723
  · exact B779727
  · exact B779731
  · exact B779735
  · exact B779739
  · exact B779743
  · exact B779747
  · exact B779751
  · exact B779755
  · exact B779759
  · exact B779763
  · exact B779767
  · exact B779771
  · exact B779775
  · exact B779779
  · exact B779783
  · exact B779787
  · exact B779791
  · exact B779795
  · exact B779799
  · exact B779803
  · exact B779807
  · exact B779811
  · exact B779815
  · exact B779819
  · exact B779823
  · exact B779827
  · exact B779831
  · exact B779835
  · exact B779839
  · exact B779843
  · exact B779847
  · exact B779851
  · exact B779855
  · exact B779859
  · exact B779863
  · exact B779867
  · exact B779871
  · exact B779875
  · exact B779879
  · exact B779883
  · exact B779887
  · exact B779891
  · exact B779895
  · exact B779899
  · exact B779903
  · exact B779907
  · exact B779911
  · exact B779915
  · exact B779919
  · exact B779923
  · exact B779927
  · exact B779931
  · exact B779935
  · exact B779939
  · exact B779943
  · exact B779947
  · exact B779951
  · exact B779955
  · exact B779959
  · exact B779963
  · exact B779967
  · exact B779971
  · exact B779975
  · exact B779979
  · exact B779983
  · exact B779987
  · exact B779991
  · exact B779995
  · exact B779999
  · exact B780003
  · exact B780007
  · exact B780011
  · exact B780015
  · exact B780019
  · exact B780023
  · exact B780027
  · exact B780031
  · exact B780035
  · exact B780039
  · exact B780043
  · exact B780047
  · exact B780051
  · exact B780055
  · exact B780059
  · exact B780063
  · exact B780067
  · exact B780071
  · exact B780075
  · exact B780079
  · exact B780083
  · exact B780087
  · exact B780091
  · exact B780095
  · exact B780099
  · exact B780103
  · exact B780107
  · exact B780111
  · exact B780115
  · exact B780119
  · exact B780123
  · exact B780127
  · exact B780131
  · exact B780135
  · exact B780139
  · exact B780143
  · exact B780147
  · exact B780151
  · exact B780155
  · exact B780159
  · exact B780163
  · exact B780167
  · exact B780171
  · exact B780175
  · exact B780179
  · exact B780183
  · exact B780187
  · exact B780191
  · exact B780195
  · exact B780199
  · exact B780203
  · exact B780207
  · exact B780211
  · exact B780215
  · exact B780219
  · exact B780223
  · exact B780227
  · exact B780231
  · exact B780235
  · exact B780239
  · exact B780243
  · exact B780247
  · exact B780251
  · exact B780255
  · exact B780259
  · exact B780263
  · exact B780267
  · exact B780271
  · exact B780275
  · exact B780279
  · exact B780283
  · exact B780287
  · exact B780291
  · exact B780295
  · exact B780299
  · exact B780303
  · exact B780307
  · exact B780311
  · exact B780315
  · exact B780319
  · exact B780323
  · exact B780327
  · exact B780331
  · exact B780335
  · exact B780339
  · exact B780343
  · exact B780347
  · exact B780351
  · exact B780355
  · exact B780359
  · exact B780363
  · exact B780367
  · exact B780371
  · exact B780375
  · exact B780379
  · exact B780383
  · exact B780387
  · exact B780391
  · exact B780395
  · exact B780399
  · exact B780403
  · exact B780407
  · exact B780411
  · exact B780415
  · exact B780419
  · exact B780423
  · exact B780427
  · exact B780431
  · exact B780435
  · exact B780439
  · exact B780443
  · exact B780447
  · exact B780451
  · exact B780455
  · exact B780459
  · exact B780463
  · exact B780467
  · exact B780471
  · exact B780475
  · exact B780479
  · exact B780483
  · exact B780487
  · exact B780491
  · exact B780495
  · exact B780499
  · exact B780503
  · exact B780507
  · exact B780511
  · exact B780515
  · exact B780519
  · exact B780523
  · exact B780527
  · exact B780531
  · exact B780535
  · exact B780539
  · exact B780543
  · exact B780547
  · exact B780551
  · exact B780555
  · exact B780559
  · exact B780563
  · exact B780567
  · exact B780571
  · exact B780575
  · exact B780579
  · exact B780583
  · exact B780587
  · exact B780591
  · exact B780595
  · exact B780599
  · exact B780603
  · exact B780607
  · exact B780611
  · exact B780615
  · exact B780619
  · exact B780623
  · exact B780627
  · exact B780631
  · exact B780635
  · exact B780639
  · exact B780643
  · exact B780647
  · exact B780651
  · exact B780655
  · exact B780659
  · exact B780663
  · exact B780667
  · exact B780671
  · exact B780675
  · exact B780679
  · exact B780683
  · exact B780687
  · exact B780691
  · exact B780695
  · exact B780699
  · exact B780703
  · exact B780707
  · exact B780711
  · exact B780715
  · exact B780719
  · exact B780723
  · exact B780727
  · exact B780731
  · exact B780735
  · exact B780739
  · exact B780743
  · exact B780747
  · exact B780751
  · exact B780755
  · exact B780759
  · exact B780763
  · exact B780767
  · exact B780771
  · exact B780775
  · exact B780779
  · exact B780783
  · exact B780787
  · exact B780791
  · exact B780795
  · exact B780799
  · exact B780803
  · exact B780807
  · exact B780811
  · exact B780815
  · exact B780819
  · exact B780823
  · exact B780827
  · exact B780831
  · exact B780835
  · exact B780839
  · exact B780843
  · exact B780847
  · exact B780851
  · exact B780855
  · exact B780859
  · exact B780863
  · exact B780867
  · exact B780871
  · exact B780875
  · exact B780879
  · exact B780883
  · exact B780887
  · exact B780891
  · exact B780895
  · exact B780899
  · exact B780903
  · exact B780907
  · exact B780911
  · exact B780915
  · exact B780919
  · exact B780923
  · exact B780927
  · exact B780931
  · exact B780935
  · exact B780939
  · exact B780943
  · exact B780947
  · exact B780951
  · exact B780955
  · exact B780959
  · exact B780963
  · exact B780967
  · exact B780971
  · exact B780975
  · exact B780979
  · exact B780983
  · exact B780987
  · exact B780991
  · exact B780995
  · exact B780999
  · exact B781003
  · exact B781007
  · exact B781011
  · exact B781015
  · exact B781019
  · exact B781023
  · exact B781027
  · exact B781031
  · exact B781035
  · exact B781039
  · exact B781043
  · exact B781047
  · exact B781051
  · exact B781055
  · exact B781059
  · exact B781063
  · exact B781067
  · exact B781071
  · exact B781075
  · exact B781079
  · exact B781083
  · exact B781087
  · exact B781091
  · exact B781095
  · exact B781099
  · exact B781103
  · exact B781107
  · exact B781111
  · exact B781115
  · exact B781119
  · exact B781123
  · exact B781127
  · exact B781131
  · exact B781135

theorem C1 (j : ℕ) (h1 : 195284 ≤ j) (h2 : j ≤ 195583) : Blo 778337 (4 * j + 3) := by
  interval_cases j
  · exact B781139
  · exact B781143
  · exact B781147
  · exact B781151
  · exact B781155
  · exact B781159
  · exact B781163
  · exact B781167
  · exact B781171
  · exact B781175
  · exact B781179
  · exact B781183
  · exact B781187
  · exact B781191
  · exact B781195
  · exact B781199
  · exact B781203
  · exact B781207
  · exact B781211
  · exact B781215
  · exact B781219
  · exact B781223
  · exact B781227
  · exact B781231
  · exact B781235
  · exact B781239
  · exact B781243
  · exact B781247
  · exact B781251
  · exact B781255
  · exact B781259
  · exact B781263
  · exact B781267
  · exact B781271
  · exact B781275
  · exact B781279
  · exact B781283
  · exact B781287
  · exact B781291
  · exact B781295
  · exact B781299
  · exact B781303
  · exact B781307
  · exact B781311
  · exact B781315
  · exact B781319
  · exact B781323
  · exact B781327
  · exact B781331
  · exact B781335
  · exact B781339
  · exact B781343
  · exact B781347
  · exact B781351
  · exact B781355
  · exact B781359
  · exact B781363
  · exact B781367
  · exact B781371
  · exact B781375
  · exact B781379
  · exact B781383
  · exact B781387
  · exact B781391
  · exact B781395
  · exact B781399
  · exact B781403
  · exact B781407
  · exact B781411
  · exact B781415
  · exact B781419
  · exact B781423
  · exact B781427
  · exact B781431
  · exact B781435
  · exact B781439
  · exact B781443
  · exact B781447
  · exact B781451
  · exact B781455
  · exact B781459
  · exact B781463
  · exact B781467
  · exact B781471
  · exact B781475
  · exact B781479
  · exact B781483
  · exact B781487
  · exact B781491
  · exact B781495
  · exact B781499
  · exact B781503
  · exact B781507
  · exact B781511
  · exact B781515
  · exact B781519
  · exact B781523
  · exact B781527
  · exact B781531
  · exact B781535
  · exact B781539
  · exact B781543
  · exact B781547
  · exact B781551
  · exact B781555
  · exact B781559
  · exact B781563
  · exact B781567
  · exact B781571
  · exact B781575
  · exact B781579
  · exact B781583
  · exact B781587
  · exact B781591
  · exact B781595
  · exact B781599
  · exact B781603
  · exact B781607
  · exact B781611
  · exact B781615
  · exact B781619
  · exact B781623
  · exact B781627
  · exact B781631
  · exact B781635
  · exact B781639
  · exact B781643
  · exact B781647
  · exact B781651
  · exact B781655
  · exact B781659
  · exact B781663
  · exact B781667
  · exact B781671
  · exact B781675
  · exact B781679
  · exact B781683
  · exact B781687
  · exact B781691
  · exact B781695
  · exact B781699
  · exact B781703
  · exact B781707
  · exact B781711
  · exact B781715
  · exact B781719
  · exact B781723
  · exact B781727
  · exact B781731
  · exact B781735
  · exact B781739
  · exact B781743
  · exact B781747
  · exact B781751
  · exact B781755
  · exact B781759
  · exact B781763
  · exact B781767
  · exact B781771
  · exact B781775
  · exact B781779
  · exact B781783
  · exact B781787
  · exact B781791
  · exact B781795
  · exact B781799
  · exact B781803
  · exact B781807
  · exact B781811
  · exact B781815
  · exact B781819
  · exact B781823
  · exact B781827
  · exact B781831
  · exact B781835
  · exact B781839
  · exact B781843
  · exact B781847
  · exact B781851
  · exact B781855
  · exact B781859
  · exact B781863
  · exact B781867
  · exact B781871
  · exact B781875
  · exact B781879
  · exact B781883
  · exact B781887
  · exact B781891
  · exact B781895
  · exact B781899
  · exact B781903
  · exact B781907
  · exact B781911
  · exact B781915
  · exact B781919
  · exact B781923
  · exact B781927
  · exact B781931
  · exact B781935
  · exact B781939
  · exact B781943
  · exact B781947
  · exact B781951
  · exact B781955
  · exact B781959
  · exact B781963
  · exact B781967
  · exact B781971
  · exact B781975
  · exact B781979
  · exact B781983
  · exact B781987
  · exact B781991
  · exact B781995
  · exact B781999
  · exact B782003
  · exact B782007
  · exact B782011
  · exact B782015
  · exact B782019
  · exact B782023
  · exact B782027
  · exact B782031
  · exact B782035
  · exact B782039
  · exact B782043
  · exact B782047
  · exact B782051
  · exact B782055
  · exact B782059
  · exact B782063
  · exact B782067
  · exact B782071
  · exact B782075
  · exact B782079
  · exact B782083
  · exact B782087
  · exact B782091
  · exact B782095
  · exact B782099
  · exact B782103
  · exact B782107
  · exact B782111
  · exact B782115
  · exact B782119
  · exact B782123
  · exact B782127
  · exact B782131
  · exact B782135
  · exact B782139
  · exact B782143
  · exact B782147
  · exact B782151
  · exact B782155
  · exact B782159
  · exact B782163
  · exact B782167
  · exact B782171
  · exact B782175
  · exact B782179
  · exact B782183
  · exact B782187
  · exact B782191
  · exact B782195
  · exact B782199
  · exact B782203
  · exact B782207
  · exact B782211
  · exact B782215
  · exact B782219
  · exact B782223
  · exact B782227
  · exact B782231
  · exact B782235
  · exact B782239
  · exact B782243
  · exact B782247
  · exact B782251
  · exact B782255
  · exact B782259
  · exact B782263
  · exact B782267
  · exact B782271
  · exact B782275
  · exact B782279
  · exact B782283
  · exact B782287
  · exact B782291
  · exact B782295
  · exact B782299
  · exact B782303
  · exact B782307
  · exact B782311
  · exact B782315
  · exact B782319
  · exact B782323
  · exact B782327
  · exact B782331
  · exact B782335

theorem solution (m : ℕ) (hlo : 778337 ≤ m) (hhi : m ≤ 782337) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 194584 ≤ j := by omega
    have hj2 : j ≤ 195583 := by omega
    have hb : Blo 778337 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 195284 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
