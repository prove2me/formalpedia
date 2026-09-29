-- Prove2me | solution 1 for syracuse_descends_range_1576486_1578486
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:07:28.119043+00:00
-- url     : https://prove2.me/submissions/a8fc93af-5292-48d1-ad58-cc798d6737f2

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


theorem B2367509 : Blo 1576486 2367509 := bbase (se 6 (by rfl) ⟨55488, by rfl⟩ : syracuseStep 2367509 = 110977) (by norm_num)
theorem B2662429 : Blo 1576486 2662429 := bbase (se 3 (by rfl) ⟨499205, by rfl⟩ : syracuseStep 2662429 = 998411) (by norm_num)
theorem B2367533 : Blo 1576486 2367533 := bbase (se 3 (by rfl) ⟨443912, by rfl⟩ : syracuseStep 2367533 = 887825) (by norm_num)
theorem B3547205 : Blo 1576486 3547205 := bbase (se 4 (by rfl) ⟨332550, by rfl⟩ : syracuseStep 3547205 = 665101) (by norm_num)
theorem B2367557 : Blo 1576486 2367557 := bbase (se 4 (by rfl) ⟨221958, by rfl⟩ : syracuseStep 2367557 = 443917) (by norm_num)
theorem B5324885 : Blo 1576486 5324885 := bbase (se 8 (by rfl) ⟨31200, by rfl⟩ : syracuseStep 5324885 = 62401) (by norm_num)
theorem B2367581 : Blo 1576486 2367581 := bbase (se 3 (by rfl) ⟨443921, by rfl⟩ : syracuseStep 2367581 = 887843) (by norm_num)
theorem B2662517 : Blo 1576486 2662517 := bbase (se 5 (by rfl) ⟨124805, by rfl⟩ : syracuseStep 2662517 = 249611) (by norm_num)
theorem B2367605 : Blo 1576486 2367605 := bbase (se 5 (by rfl) ⟨110981, by rfl⟩ : syracuseStep 2367605 = 221963) (by norm_num)
theorem B3547277 : Blo 1576486 3547277 := bbase (se 3 (by rfl) ⟨665114, by rfl⟩ : syracuseStep 3547277 = 1330229) (by norm_num)
theorem B2367629 : Blo 1576486 2367629 := bbase (se 3 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 2367629 = 887861) (by norm_num)
theorem B2367653 : Blo 1576486 2367653 := bbase (se 4 (by rfl) ⟨221967, by rfl⟩ : syracuseStep 2367653 = 443935) (by norm_num)
theorem B2367677 : Blo 1576486 2367677 := bbase (se 3 (by rfl) ⟨443939, by rfl⟩ : syracuseStep 2367677 = 887879) (by norm_num)
theorem B3367109 : Blo 1576486 3367109 := bbase (se 4 (by rfl) ⟨315666, by rfl⟩ : syracuseStep 3367109 = 631333) (by norm_num)
theorem B3547349 : Blo 1576486 3547349 := bbase (se 7 (by rfl) ⟨41570, by rfl⟩ : syracuseStep 3547349 = 83141) (by norm_num)
theorem B2367701 : Blo 1576486 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B4489445 : Blo 1576486 4489445 := bbase (se 4 (by rfl) ⟨420885, by rfl⟩ : syracuseStep 4489445 = 841771) (by norm_num)
theorem B2367725 : Blo 1576486 2367725 := bbase (se 3 (by rfl) ⟨443948, by rfl⟩ : syracuseStep 2367725 = 887897) (by norm_num)
theorem B2367485 : Blo 1576486 2367485 := bbase (se 3 (by rfl) ⟨443903, by rfl⟩ : syracuseStep 2367485 = 887807) (by norm_num)
theorem B2662645 : Blo 1576486 2662645 := bbase (se 5 (by rfl) ⟨124811, by rfl⟩ : syracuseStep 2662645 = 249623) (by norm_num)
theorem B5988613 : Blo 1576486 5988613 := bbase (se 4 (by rfl) ⟨561432, by rfl⟩ : syracuseStep 5988613 = 1122865) (by norm_num)
theorem B3547421 : Blo 1576486 3547421 := bbase (se 3 (by rfl) ⟨665141, by rfl⟩ : syracuseStep 3547421 = 1330283) (by norm_num)
theorem B6832421 : Blo 1576486 6832421 := bbase (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) (by norm_num)
theorem B2662733 : Blo 1576486 2662733 := bbase (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) (by norm_num)
theorem B3547493 : Blo 1576486 3547493 := bbase (se 4 (by rfl) ⟨332577, by rfl⟩ : syracuseStep 3547493 = 665155) (by norm_num)
theorem B5120405 : Blo 1576486 5120405 := bbase (se 6 (by rfl) ⟨120009, by rfl⟩ : syracuseStep 5120405 = 240019) (by norm_num)
theorem B3547565 : Blo 1576486 3547565 := bbase (se 3 (by rfl) ⟨665168, by rfl⟩ : syracuseStep 3547565 = 1330337) (by norm_num)
theorem B6742453 : Blo 1576486 6742453 := bbase (se 5 (by rfl) ⟨316052, by rfl⟩ : syracuseStep 6742453 = 632105) (by norm_num)
theorem B2662861 : Blo 1576486 2662861 := bbase (se 3 (by rfl) ⟨499286, by rfl⟩ : syracuseStep 2662861 = 998573) (by norm_num)
theorem B4555237 : Blo 1576486 4555237 := bbase (se 4 (by rfl) ⟨427053, by rfl⟩ : syracuseStep 4555237 = 854107) (by norm_num)
theorem B3547637 : Blo 1576486 3547637 := bbase (se 5 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 3547637 = 332591) (by norm_num)
theorem B5325317 : Blo 1576486 5325317 := bbase (se 4 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 5325317 = 998497) (by norm_num)
theorem B7987733 : Blo 1576486 7987733 := bbase (se 6 (by rfl) ⟨187212, by rfl⟩ : syracuseStep 7987733 = 374425) (by norm_num)
theorem B2662949 : Blo 1576486 2662949 := bbase (se 4 (by rfl) ⟨249651, by rfl⟩ : syracuseStep 2662949 = 499303) (by norm_num)
theorem B5988917 : Blo 1576486 5988917 := bbase (se 5 (by rfl) ⟨280730, by rfl⟩ : syracuseStep 5988917 = 561461) (by norm_num)
theorem B3547709 : Blo 1576486 3547709 := bbase (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) (by norm_num)
theorem B3547781 : Blo 1576486 3547781 := bbase (se 4 (by rfl) ⟨332604, by rfl⟩ : syracuseStep 3547781 = 665209) (by norm_num)
theorem B2663077 : Blo 1576486 2663077 := bbase (se 4 (by rfl) ⟨249663, by rfl⟩ : syracuseStep 2663077 = 499327) (by norm_num)
theorem B3547853 : Blo 1576486 3547853 := bbase (se 3 (by rfl) ⟨665222, by rfl⟩ : syracuseStep 3547853 = 1330445) (by norm_num)
theorem B2663165 : Blo 1576486 2663165 := bbase (se 3 (by rfl) ⟨499343, by rfl⟩ : syracuseStep 2663165 = 998687) (by norm_num)
theorem B3547925 : Blo 1576486 3547925 := bbase (se 6 (by rfl) ⟨83154, by rfl⟩ : syracuseStep 3547925 = 166309) (by norm_num)
theorem B1598249 : Blo 1576486 1598249 := bbase (se 2 (by rfl) ⟨599343, by rfl⟩ : syracuseStep 1598249 = 1198687) (by norm_num)
theorem B3547997 : Blo 1576486 3547997 := bbase (se 3 (by rfl) ⟨665249, by rfl⟩ : syracuseStep 3547997 = 1330499) (by norm_num)
theorem B2663293 : Blo 1576486 2663293 := bbase (se 3 (by rfl) ⟨499367, by rfl⟩ : syracuseStep 2663293 = 998735) (by norm_num)
theorem B4490117 : Blo 1576486 4490117 := bbase (se 4 (by rfl) ⟨420948, by rfl⟩ : syracuseStep 4490117 = 841897) (by norm_num)
theorem B3548069 : Blo 1576486 3548069 := bbase (se 4 (by rfl) ⟨332631, by rfl⟩ : syracuseStep 3548069 = 665263) (by norm_num)
theorem B10101685 : Blo 1576486 10101685 := bbase (se 5 (by rfl) ⟨473516, by rfl⟩ : syracuseStep 10101685 = 947033) (by norm_num)
theorem B5325749 : Blo 1576486 5325749 := bbase (se 5 (by rfl) ⟨249644, by rfl⟩ : syracuseStep 5325749 = 499289) (by norm_num)
theorem B3990485 : Blo 1576486 3990485 := bbase (se 7 (by rfl) ⟨46763, by rfl⟩ : syracuseStep 3990485 = 93527) (by norm_num)
theorem B2663381 : Blo 1576486 2663381 := bbase (se 7 (by rfl) ⟨31211, by rfl⟩ : syracuseStep 2663381 = 62423) (by norm_num)
theorem B3548141 : Blo 1576486 3548141 := bbase (se 3 (by rfl) ⟨665276, by rfl⟩ : syracuseStep 3548141 = 1330553) (by norm_num)
theorem B3367973 : Blo 1576486 3367973 := bbase (se 4 (by rfl) ⟨315747, by rfl⟩ : syracuseStep 3367973 = 631495) (by norm_num)
theorem B3548213 : Blo 1576486 3548213 := bbase (se 5 (by rfl) ⟨166322, by rfl⟩ : syracuseStep 3548213 = 332645) (by norm_num)
theorem B1598549 : Blo 1576486 1598549 := bbase (se 8 (by rfl) ⟨9366, by rfl⟩ : syracuseStep 1598549 = 18733) (by norm_num)
theorem B2663509 : Blo 1576486 2663509 := bbase (se 8 (by rfl) ⟨15606, by rfl⟩ : syracuseStep 2663509 = 31213) (by norm_num)
theorem B3548285 : Blo 1576486 3548285 := bbase (se 3 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 3548285 = 1330607) (by norm_num)
theorem B2663597 : Blo 1576486 2663597 := bbase (se 3 (by rfl) ⟨499424, by rfl⟩ : syracuseStep 2663597 = 998849) (by norm_num)
theorem B3368117 : Blo 1576486 3368117 := bbase (se 5 (by rfl) ⟨157880, by rfl⟩ : syracuseStep 3368117 = 315761) (by norm_num)
theorem B3548357 : Blo 1576486 3548357 := bbase (se 4 (by rfl) ⟨332658, by rfl⟩ : syracuseStep 3548357 = 665317) (by norm_num)
theorem B3548429 : Blo 1576486 3548429 := bbase (se 3 (by rfl) ⟨665330, by rfl⟩ : syracuseStep 3548429 = 1330661) (by norm_num)
theorem B3990829 : Blo 1576486 3990829 := bbase (se 3 (by rfl) ⟨748280, by rfl⟩ : syracuseStep 3990829 = 1496561) (by norm_num)
theorem B4490549 : Blo 1576486 4490549 := bbase (se 5 (by rfl) ⟨210494, by rfl⟩ : syracuseStep 4490549 = 420989) (by norm_num)
theorem B3548501 : Blo 1576486 3548501 := bbase (se 12 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 3548501 = 2599) (by norm_num)
theorem B2245981 : Blo 1576486 2245981 := bbase (se 3 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 2245981 = 842243) (by norm_num)
theorem B5326181 : Blo 1576486 5326181 := bbase (se 4 (by rfl) ⟨499329, by rfl⟩ : syracuseStep 5326181 = 998659) (by norm_num)
theorem B3990941 : Blo 1576486 3990941 := bbase (se 3 (by rfl) ⟨748301, by rfl⟩ : syracuseStep 3990941 = 1496603) (by norm_num)
theorem B3548573 : Blo 1576486 3548573 := bbase (se 3 (by rfl) ⟨665357, by rfl⟩ : syracuseStep 3548573 = 1330715) (by norm_num)
theorem B1598897 : Blo 1576486 1598897 := bbase (se 2 (by rfl) ⟨599586, by rfl⟩ : syracuseStep 1598897 = 1199173) (by norm_num)
theorem B3548645 : Blo 1576486 3548645 := bbase (se 4 (by rfl) ⟨332685, by rfl⟩ : syracuseStep 3548645 = 665371) (by norm_num)
theorem B7579109 : Blo 1576486 7579109 := bbase (se 4 (by rfl) ⟨710541, by rfl⟩ : syracuseStep 7579109 = 1421083) (by norm_num)
theorem B3548717 : Blo 1576486 3548717 := bbase (se 3 (by rfl) ⟨665384, by rfl⟩ : syracuseStep 3548717 = 1330769) (by norm_num)
theorem B6735413 : Blo 1576486 6735413 := bbase (se 5 (by rfl) ⟨315722, by rfl⟩ : syracuseStep 6735413 = 631445) (by norm_num)
theorem B92227157 : Blo 1576486 92227157 := bbase (se 8 (by rfl) ⟨540393, by rfl⟩ : syracuseStep 92227157 = 1080787) (by norm_num)
theorem B3991133 : Blo 1576486 3991133 := bbase (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) (by norm_num)
theorem B3548789 : Blo 1576486 3548789 := bbase (se 5 (by rfl) ⟨166349, by rfl⟩ : syracuseStep 3548789 = 332699) (by norm_num)
theorem B1894009 : Blo 1576486 1894009 := bbase (se 2 (by rfl) ⟨710253, by rfl⟩ : syracuseStep 1894009 = 1420507) (by norm_num)
theorem B3597949 : Blo 1576486 3597949 := bbase (se 3 (by rfl) ⟨674615, by rfl⟩ : syracuseStep 3597949 = 1349231) (by norm_num)
theorem B3548861 : Blo 1576486 3548861 := bbase (se 3 (by rfl) ⟨665411, by rfl⟩ : syracuseStep 3548861 = 1330823) (by norm_num)
theorem B3548933 : Blo 1576486 3548933 := bbase (se 4 (by rfl) ⟨332712, by rfl⟩ : syracuseStep 3548933 = 665425) (by norm_num)
theorem B1894153 : Blo 1576486 1894153 := bbase (se 2 (by rfl) ⟨710307, by rfl⟩ : syracuseStep 1894153 = 1420615) (by norm_num)
theorem B17049365 : Blo 1576486 17049365 := bbase (se 6 (by rfl) ⟨399594, by rfl⟩ : syracuseStep 17049365 = 799189) (by norm_num)
theorem B5326613 : Blo 1576486 5326613 := bbase (se 6 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 5326613 = 249685) (by norm_num)
theorem B7989029 : Blo 1576486 7989029 := bbase (se 4 (by rfl) ⟨748971, by rfl⟩ : syracuseStep 7989029 = 1497943) (by norm_num)
theorem B16181045 : Blo 1576486 16181045 := bbase (se 5 (by rfl) ⟨758486, by rfl⟩ : syracuseStep 16181045 = 1516973) (by norm_num)
theorem B3549005 : Blo 1576486 3549005 := bbase (se 3 (by rfl) ⟨665438, by rfl⟩ : syracuseStep 3549005 = 1330877) (by norm_num)
theorem B17966933 : Blo 1576486 17966933 := bbase (se 9 (by rfl) ⟨52637, by rfl⟩ : syracuseStep 17966933 = 105275) (by norm_num)
theorem B3549077 : Blo 1576486 3549077 := bbase (se 6 (by rfl) ⟨83181, by rfl⟩ : syracuseStep 3549077 = 166363) (by norm_num)
theorem B3368861 : Blo 1576486 3368861 := bbase (se 3 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 3368861 = 1263323) (by norm_num)
theorem B2246573 : Blo 1576486 2246573 := bbase (se 3 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 2246573 = 842465) (by norm_num)
theorem B3991477 : Blo 1576486 3991477 := bbase (se 5 (by rfl) ⟨187100, by rfl⟩ : syracuseStep 3991477 = 374201) (by norm_num)
theorem B3598285 : Blo 1576486 3598285 := bbase (se 3 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 3598285 = 1349357) (by norm_num)
theorem B3549149 : Blo 1576486 3549149 := bbase (se 3 (by rfl) ⟨665465, by rfl⟩ : syracuseStep 3549149 = 1330931) (by norm_num)
theorem B8095733 : Blo 1576486 8095733 := bbase (se 5 (by rfl) ⟨379487, by rfl⟩ : syracuseStep 8095733 = 758975) (by norm_num)
theorem B2246653 : Blo 1576486 2246653 := bbase (se 3 (by rfl) ⟨421247, by rfl⟩ : syracuseStep 2246653 = 842495) (by norm_num)
theorem B3991589 : Blo 1576486 3991589 := bbase (se 4 (by rfl) ⟨374211, by rfl⟩ : syracuseStep 3991589 = 748423) (by norm_num)
theorem B4491301 : Blo 1576486 4491301 := bbase (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) (by norm_num)
theorem B3549221 : Blo 1576486 3549221 := bbase (se 4 (by rfl) ⟨332739, by rfl⟩ : syracuseStep 3549221 = 665479) (by norm_num)
theorem B5687333 : Blo 1576486 5687333 := bbase (se 4 (by rfl) ⟨533187, by rfl⟩ : syracuseStep 5687333 = 1066375) (by norm_num)
theorem B3844181 : Blo 1576486 3844181 := bbase (se 8 (by rfl) ⟨22524, by rfl⟩ : syracuseStep 3844181 = 45049) (by norm_num)
theorem B3549293 : Blo 1576486 3549293 := bbase (se 3 (by rfl) ⟨665492, by rfl⟩ : syracuseStep 3549293 = 1330985) (by norm_num)
theorem B2246773 : Blo 1576486 2246773 := bbase (se 5 (by rfl) ⟨105317, by rfl⟩ : syracuseStep 2246773 = 210635) (by norm_num)
theorem B3549365 : Blo 1576486 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B7981253 : Blo 1576486 7981253 := bbase (se 4 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 7981253 = 1496485) (by norm_num)
theorem B2132165 : Blo 1576486 2132165 := bbase (se 4 (by rfl) ⟨199890, by rfl⟩ : syracuseStep 2132165 = 399781) (by norm_num)
theorem B5327045 : Blo 1576486 5327045 := bbase (se 4 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 5327045 = 998821) (by norm_num)
theorem B2246869 : Blo 1576486 2246869 := bbase (se 7 (by rfl) ⟨26330, by rfl⟩ : syracuseStep 2246869 = 52661) (by norm_num)
theorem B3991781 : Blo 1576486 3991781 := bbase (se 4 (by rfl) ⟨374229, by rfl⟩ : syracuseStep 3991781 = 748459) (by norm_num)
theorem B3549437 : Blo 1576486 3549437 := bbase (se 3 (by rfl) ⟨665519, by rfl⟩ : syracuseStep 3549437 = 1331039) (by norm_num)
theorem B5056789 : Blo 1576486 5056789 := bbase (se 6 (by rfl) ⟨118518, by rfl⟩ : syracuseStep 5056789 = 237037) (by norm_num)
theorem B4262213 : Blo 1576486 4262213 := bbase (se 4 (by rfl) ⟨399582, by rfl⟩ : syracuseStep 4262213 = 799165) (by norm_num)
theorem B3549509 : Blo 1576486 3549509 := bbase (se 4 (by rfl) ⟨332766, by rfl⟩ : syracuseStep 3549509 = 665533) (by norm_num)
theorem B3549581 : Blo 1576486 3549581 := bbase (se 3 (by rfl) ⟨665546, by rfl⟩ : syracuseStep 3549581 = 1331093) (by norm_num)
theorem B3549653 : Blo 1576486 3549653 := bbase (se 7 (by rfl) ⟨41597, by rfl⟩ : syracuseStep 3549653 = 83195) (by norm_num)
theorem B5687765 : Blo 1576486 5687765 := bbase (se 7 (by rfl) ⟨66653, by rfl⟩ : syracuseStep 5687765 = 133307) (by norm_num)
theorem B4049365 : Blo 1576486 4049365 := bbase (se 7 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 4049365 = 94907) (by norm_num)
theorem B6736405 : Blo 1576486 6736405 := bbase (se 6 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 6736405 = 315769) (by norm_num)
theorem B3549725 : Blo 1576486 3549725 := bbase (se 3 (by rfl) ⟨665573, by rfl⟩ : syracuseStep 3549725 = 1331147) (by norm_num)
theorem B3992125 : Blo 1576486 3992125 := bbase (se 3 (by rfl) ⟨748523, by rfl⟩ : syracuseStep 3992125 = 1497047) (by norm_num)
theorem B3549797 : Blo 1576486 3549797 := bbase (se 4 (by rfl) ⟨332793, by rfl⟩ : syracuseStep 3549797 = 665587) (by norm_num)
theorem B5991029 : Blo 1576486 5991029 := bbase (se 5 (by rfl) ⟨280829, by rfl⟩ : syracuseStep 5991029 = 561659) (by norm_num)
theorem B3369613 : Blo 1576486 3369613 := bbase (se 3 (by rfl) ⟨631802, by rfl⟩ : syracuseStep 3369613 = 1263605) (by norm_num)
theorem B2525845 : Blo 1576486 2525845 := bbase (se 6 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 2525845 = 118399) (by norm_num)
theorem B11979413 : Blo 1576486 11979413 := bbase (se 6 (by rfl) ⟨280767, by rfl⟩ : syracuseStep 11979413 = 561535) (by norm_num)
theorem B3992237 : Blo 1576486 3992237 := bbase (se 3 (by rfl) ⟨748544, by rfl⟩ : syracuseStep 3992237 = 1497089) (by norm_num)
theorem B3549869 : Blo 1576486 3549869 := bbase (se 3 (by rfl) ⟨665600, by rfl⟩ : syracuseStep 3549869 = 1331201) (by norm_num)
theorem B2247365 : Blo 1576486 2247365 := bbase (se 4 (by rfl) ⟨210690, by rfl⟩ : syracuseStep 2247365 = 421381) (by norm_num)
theorem B9857749 : Blo 1576486 9857749 := bbase (se 7 (by rfl) ⟨115520, by rfl⟩ : syracuseStep 9857749 = 231041) (by norm_num)
theorem B3549941 : Blo 1576486 3549941 := bbase (se 5 (by rfl) ⟨166403, by rfl⟩ : syracuseStep 3549941 = 332807) (by norm_num)
theorem B3599117 : Blo 1576486 3599117 := bbase (se 3 (by rfl) ⟨674834, by rfl⟩ : syracuseStep 3599117 = 1349669) (by norm_num)
theorem B2992925 : Blo 1576486 2992925 := bbase (se 3 (by rfl) ⟨561173, by rfl⟩ : syracuseStep 2992925 = 1122347) (by norm_num)
theorem B3369757 : Blo 1576486 3369757 := bbase (se 3 (by rfl) ⟨631829, by rfl⟩ : syracuseStep 3369757 = 1263659) (by norm_num)
theorem B4049693 : Blo 1576486 4049693 := bbase (se 3 (by rfl) ⟨759317, by rfl⟩ : syracuseStep 4049693 = 1518635) (by norm_num)
theorem B3550013 : Blo 1576486 3550013 := bbase (se 3 (by rfl) ⟨665627, by rfl⟩ : syracuseStep 3550013 = 1331255) (by norm_num)
theorem B8096597 : Blo 1576486 8096597 := bbase (se 9 (by rfl) ⟨23720, by rfl⟩ : syracuseStep 8096597 = 47441) (by norm_num)
theorem B3992429 : Blo 1576486 3992429 := bbase (se 3 (by rfl) ⟨748580, by rfl⟩ : syracuseStep 3992429 = 1497161) (by norm_num)
theorem B3550085 : Blo 1576486 3550085 := bbase (se 4 (by rfl) ⟨332820, by rfl⟩ : syracuseStep 3550085 = 665641) (by norm_num)
theorem B5991317 : Blo 1576486 5991317 := bbase (se 6 (by rfl) ⟨140421, by rfl⟩ : syracuseStep 5991317 = 280843) (by norm_num)
theorem B3550157 : Blo 1576486 3550157 := bbase (se 3 (by rfl) ⟨665654, by rfl⟩ : syracuseStep 3550157 = 1331309) (by norm_num)
theorem B3550229 : Blo 1576486 3550229 := bbase (se 6 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 3550229 = 166417) (by norm_num)
theorem B1920025 : Blo 1576486 1920025 := bbase (se 2 (by rfl) ⟨720009, by rfl⟩ : syracuseStep 1920025 = 1440019) (by norm_num)
theorem B11971637 : Blo 1576486 11971637 := bbase (se 5 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 11971637 = 1122341) (by norm_num)
theorem B7990325 : Blo 1576486 7990325 := bbase (se 5 (by rfl) ⟨374546, by rfl⟩ : syracuseStep 7990325 = 749093) (by norm_num)
theorem B2993213 : Blo 1576486 2993213 := bbase (se 3 (by rfl) ⟨561227, by rfl⟩ : syracuseStep 2993213 = 1122455) (by norm_num)
theorem B1920061 : Blo 1576486 1920061 := bbase (se 3 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 1920061 = 720023) (by norm_num)
theorem B48557141 : Blo 1576486 48557141 := bbase (se 8 (by rfl) ⟨284514, by rfl⟩ : syracuseStep 48557141 = 569029) (by norm_num)
theorem B2526293 : Blo 1576486 2526293 := bbase (se 8 (by rfl) ⟨14802, by rfl⟩ : syracuseStep 2526293 = 29605) (by norm_num)
theorem B3550301 : Blo 1576486 3550301 := bbase (se 3 (by rfl) ⟨665681, by rfl⟩ : syracuseStep 3550301 = 1331363) (by norm_num)
theorem B3370133 : Blo 1576486 3370133 := bbase (se 6 (by rfl) ⟨78987, by rfl⟩ : syracuseStep 3370133 = 157975) (by norm_num)
theorem B3550373 : Blo 1576486 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B3992773 : Blo 1576486 3992773 := bbase (se 4 (by rfl) ⟨374322, by rfl⟩ : syracuseStep 3992773 = 748645) (by norm_num)
theorem B2993365 : Blo 1576486 2993365 := bbase (se 7 (by rfl) ⟨35078, by rfl⟩ : syracuseStep 2993365 = 70157) (by norm_num)
theorem B3550445 : Blo 1576486 3550445 := bbase (se 3 (by rfl) ⟨665708, by rfl⟩ : syracuseStep 3550445 = 1331417) (by norm_num)
theorem B2051317 : Blo 1576486 2051317 := bbase (se 5 (by rfl) ⟨96155, by rfl⟩ : syracuseStep 2051317 = 192311) (by norm_num)
theorem B1895681 : Blo 1576486 1895681 := bbase (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) (by norm_num)
theorem B3992885 : Blo 1576486 3992885 := bbase (se 5 (by rfl) ⟨187166, by rfl⟩ : syracuseStep 3992885 = 374333) (by norm_num)
theorem B3550517 : Blo 1576486 3550517 := bbase (se 5 (by rfl) ⟨166430, by rfl⟩ : syracuseStep 3550517 = 332861) (by norm_num)
theorem B3550589 : Blo 1576486 3550589 := bbase (se 3 (by rfl) ⟨665735, by rfl⟩ : syracuseStep 3550589 = 1331471) (by norm_num)
theorem B3550661 : Blo 1576486 3550661 := bbase (se 4 (by rfl) ⟨332874, by rfl⟩ : syracuseStep 3550661 = 665749) (by norm_num)
theorem B7982549 : Blo 1576486 7982549 := bbase (se 7 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 7982549 = 187091) (by norm_num)
theorem B3993077 : Blo 1576486 3993077 := bbase (se 5 (by rfl) ⟨187175, by rfl⟩ : syracuseStep 3993077 = 374351) (by norm_num)
theorem B2993669 : Blo 1576486 2993669 := bbase (se 4 (by rfl) ⟨280656, by rfl⟩ : syracuseStep 2993669 = 561313) (by norm_num)
theorem B3370501 : Blo 1576486 3370501 := bbase (se 4 (by rfl) ⟨315984, by rfl⟩ : syracuseStep 3370501 = 631969) (by norm_num)
theorem B3550733 : Blo 1576486 3550733 := bbase (se 3 (by rfl) ⟨665762, by rfl⟩ : syracuseStep 3550733 = 1331525) (by norm_num)
theorem B1895989 : Blo 1576486 1895989 := bbase (se 5 (by rfl) ⟨88874, by rfl⟩ : syracuseStep 1895989 = 177749) (by norm_num)
theorem B3550805 : Blo 1576486 3550805 := bbase (se 8 (by rfl) ⟨20805, by rfl⟩ : syracuseStep 3550805 = 41611) (by norm_num)
theorem B3198565 : Blo 1576486 3198565 := bbase (se 4 (by rfl) ⟨299865, by rfl⟩ : syracuseStep 3198565 = 599731) (by norm_num)
theorem B12136085 : Blo 1576486 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B1896085 : Blo 1576486 1896085 := bbase (se 6 (by rfl) ⟨44439, by rfl⟩ : syracuseStep 1896085 = 88879) (by norm_num)
theorem B3550877 : Blo 1576486 3550877 := bbase (se 3 (by rfl) ⟨665789, by rfl⟩ : syracuseStep 3550877 = 1331579) (by norm_num)
theorem B10104533 : Blo 1576486 10104533 := bbase (se 7 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 10104533 = 236825) (by norm_num)
theorem B3550949 : Blo 1576486 3550949 := bbase (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) (by norm_num)
theorem B1707797 : Blo 1576486 1707797 := bbase (se 6 (by rfl) ⟨40026, by rfl⟩ : syracuseStep 1707797 = 80053) (by norm_num)
theorem B3551021 : Blo 1576486 3551021 := bbase (se 3 (by rfl) ⟨665816, by rfl⟩ : syracuseStep 3551021 = 1331633) (by norm_num)
theorem B3993421 : Blo 1576486 3993421 := bbase (se 3 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 3993421 = 1497533) (by norm_num)
theorem B3551093 : Blo 1576486 3551093 := bbase (se 5 (by rfl) ⟨166457, by rfl⟩ : syracuseStep 3551093 = 332915) (by norm_num)
theorem B3993533 : Blo 1576486 3993533 := bbase (se 3 (by rfl) ⟨748787, by rfl⟩ : syracuseStep 3993533 = 1497575) (by norm_num)
theorem B3551165 : Blo 1576486 3551165 := bbase (se 3 (by rfl) ⟨665843, by rfl⟩ : syracuseStep 3551165 = 1331687) (by norm_num)
theorem B1773553 : Blo 1576486 1773553 := bbase (se 2 (by rfl) ⟨665082, by rfl⟩ : syracuseStep 1773553 = 1330165) (by norm_num)
theorem B3551237 : Blo 1576486 3551237 := bbase (se 4 (by rfl) ⟨332928, by rfl⟩ : syracuseStep 3551237 = 665857) (by norm_num)
theorem B1773589 : Blo 1576486 1773589 := bbase (se 6 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 1773589 = 83137) (by norm_num)
theorem B5992501 : Blo 1576486 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B1773625 : Blo 1576486 1773625 := bbase (se 2 (by rfl) ⟨665109, by rfl⟩ : syracuseStep 1773625 = 1330219) (by norm_num)
theorem B1708109 : Blo 1576486 1708109 := bbase (se 3 (by rfl) ⟨320270, by rfl⟩ : syracuseStep 1708109 = 640541) (by norm_num)
theorem B3551309 : Blo 1576486 3551309 := bbase (se 3 (by rfl) ⟨665870, by rfl⟩ : syracuseStep 3551309 = 1331741) (by norm_num)
theorem B1773661 : Blo 1576486 1773661 := bbase (se 3 (by rfl) ⟨332561, by rfl⟩ : syracuseStep 1773661 = 665123) (by norm_num)
theorem B3993725 : Blo 1576486 3993725 := bbase (se 3 (by rfl) ⟨748823, by rfl⟩ : syracuseStep 3993725 = 1497647) (by norm_num)
theorem B1773697 : Blo 1576486 1773697 := bbase (se 2 (by rfl) ⟨665136, by rfl⟩ : syracuseStep 1773697 = 1330273) (by norm_num)
theorem B3551381 : Blo 1576486 3551381 := bbase (se 6 (by rfl) ⟨83235, by rfl⟩ : syracuseStep 3551381 = 166471) (by norm_num)
theorem B1773733 : Blo 1576486 1773733 := bbase (se 4 (by rfl) ⟨166287, by rfl⟩ : syracuseStep 1773733 = 332575) (by norm_num)
theorem B2699453 : Blo 1576486 2699453 := bbase (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) (by norm_num)
theorem B1773769 : Blo 1576486 1773769 := bbase (se 2 (by rfl) ⟨665163, by rfl⟩ : syracuseStep 1773769 = 1330327) (by norm_num)
theorem B3551453 : Blo 1576486 3551453 := bbase (se 3 (by rfl) ⟨665897, by rfl⟩ : syracuseStep 3551453 = 1331795) (by norm_num)
theorem B1773805 : Blo 1576486 1773805 := bbase (se 3 (by rfl) ⟨332588, by rfl⟩ : syracuseStep 1773805 = 665177) (by norm_num)
theorem B2994421 : Blo 1576486 2994421 := bbase (se 5 (by rfl) ⟨140363, by rfl⟩ : syracuseStep 2994421 = 280727) (by norm_num)
theorem B1683713 : Blo 1576486 1683713 := bbase (se 2 (by rfl) ⟨631392, by rfl⟩ : syracuseStep 1683713 = 1262785) (by norm_num)
theorem B1773841 : Blo 1576486 1773841 := bbase (se 2 (by rfl) ⟨665190, by rfl⟩ : syracuseStep 1773841 = 1330381) (by norm_num)
theorem B5320997 : Blo 1576486 5320997 := bbase (se 4 (by rfl) ⟨498843, by rfl⟩ : syracuseStep 5320997 = 997687) (by norm_num)
theorem B3551525 : Blo 1576486 3551525 := bbase (se 4 (by rfl) ⟨332955, by rfl⟩ : syracuseStep 3551525 = 665911) (by norm_num)
theorem B4739381 : Blo 1576486 4739381 := bbase (se 5 (by rfl) ⟨222158, by rfl⟩ : syracuseStep 4739381 = 444317) (by norm_num)
theorem B1773877 : Blo 1576486 1773877 := bbase (se 5 (by rfl) ⟨83150, by rfl⟩ : syracuseStep 1773877 = 166301) (by norm_num)
theorem B1683785 : Blo 1576486 1683785 := bbase (se 2 (by rfl) ⟨631419, by rfl⟩ : syracuseStep 1683785 = 1262839) (by norm_num)
theorem B2773333 : Blo 1576486 2773333 := bbase (se 10 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 2773333 = 8125) (by norm_num)
theorem B1773913 : Blo 1576486 1773913 := bbase (se 2 (by rfl) ⟨665217, by rfl⟩ : syracuseStep 1773913 = 1330435) (by norm_num)
theorem B5992805 : Blo 1576486 5992805 := bbase (se 4 (by rfl) ⟨561825, by rfl⟩ : syracuseStep 5992805 = 1123651) (by norm_num)
theorem B1773949 : Blo 1576486 1773949 := bbase (se 3 (by rfl) ⟨332615, by rfl⟩ : syracuseStep 1773949 = 665231) (by norm_num)
theorem B2994565 : Blo 1576486 2994565 := bbase (se 4 (by rfl) ⟨280740, by rfl⟩ : syracuseStep 2994565 = 561481) (by norm_num)
theorem B1773985 : Blo 1576486 1773985 := bbase (se 2 (by rfl) ⟨665244, by rfl⟩ : syracuseStep 1773985 = 1330489) (by norm_num)
theorem B5394853 : Blo 1576486 5394853 := bbase (se 4 (by rfl) ⟨505767, by rfl⟩ : syracuseStep 5394853 = 1011535) (by norm_num)
theorem B1798573 : Blo 1576486 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B1774021 : Blo 1576486 1774021 := bbase (se 4 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 1774021 = 332629) (by norm_num)
theorem B3994069 : Blo 1576486 3994069 := bbase (se 7 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 3994069 = 93611) (by norm_num)
theorem B2699741 : Blo 1576486 2699741 := bbase (se 3 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 2699741 = 1012403) (by norm_num)
theorem B1774057 : Blo 1576486 1774057 := bbase (se 2 (by rfl) ⟨665271, by rfl⟩ : syracuseStep 1774057 = 1330543) (by norm_num)
theorem B1798633 : Blo 1576486 1798633 := bbase (se 2 (by rfl) ⟨674487, by rfl⟩ : syracuseStep 1798633 = 1348975) (by norm_num)
theorem B2560501 : Blo 1576486 2560501 := bbase (se 5 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 2560501 = 240047) (by norm_num)
theorem B1683973 : Blo 1576486 1683973 := bbase (se 4 (by rfl) ⟨157872, by rfl⟩ : syracuseStep 1683973 = 315745) (by norm_num)
theorem B1774093 : Blo 1576486 1774093 := bbase (se 3 (by rfl) ⟨332642, by rfl⟩ : syracuseStep 1774093 = 665285) (by norm_num)
theorem B1995293 : Blo 1576486 1995293 := bbase (se 3 (by rfl) ⟨374117, by rfl⟩ : syracuseStep 1995293 = 748235) (by norm_num)
theorem B2994725 : Blo 1576486 2994725 := bbase (se 4 (by rfl) ⟨280755, by rfl⟩ : syracuseStep 2994725 = 561511) (by norm_num)
theorem B1774129 : Blo 1576486 1774129 := bbase (se 2 (by rfl) ⟨665298, by rfl⟩ : syracuseStep 1774129 = 1330597) (by norm_num)
theorem B7582261 : Blo 1576486 7582261 := bbase (se 5 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 7582261 = 710837) (by norm_num)
theorem B2527805 : Blo 1576486 2527805 := bbase (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) (by norm_num)
theorem B3994181 : Blo 1576486 3994181 := bbase (se 4 (by rfl) ⟨374454, by rfl⟩ : syracuseStep 3994181 = 748909) (by norm_num)
theorem B1995349 : Blo 1576486 1995349 := bbase (se 8 (by rfl) ⟨11691, by rfl⟩ : syracuseStep 1995349 = 23383) (by norm_num)
theorem B1774165 : Blo 1576486 1774165 := bbase (se 8 (by rfl) ⟨10395, by rfl⟩ : syracuseStep 1774165 = 20791) (by norm_num)
theorem B1774201 : Blo 1576486 1774201 := bbase (se 2 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 1774201 = 1330651) (by norm_num)
theorem B1774237 : Blo 1576486 1774237 := bbase (se 3 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 1774237 = 665339) (by norm_num)
theorem B4264613 : Blo 1576486 4264613 := bbase (se 4 (by rfl) ⟨399807, by rfl⟩ : syracuseStep 4264613 = 799615) (by norm_num)
theorem B1995445 : Blo 1576486 1995445 := bbase (se 5 (by rfl) ⟨93536, by rfl⟩ : syracuseStep 1995445 = 187073) (by norm_num)
theorem B6394549 : Blo 1576486 6394549 := bbase (se 5 (by rfl) ⟨299744, by rfl⟩ : syracuseStep 6394549 = 599489) (by norm_num)
theorem B2994869 : Blo 1576486 2994869 := bbase (se 5 (by rfl) ⟨140384, by rfl⟩ : syracuseStep 2994869 = 280769) (by norm_num)
theorem B1684157 : Blo 1576486 1684157 := bbase (se 3 (by rfl) ⟨315779, by rfl⟩ : syracuseStep 1684157 = 631559) (by norm_num)
theorem B2527933 : Blo 1576486 2527933 := bbase (se 3 (by rfl) ⟨473987, by rfl⟩ : syracuseStep 2527933 = 947975) (by norm_num)
theorem B1774273 : Blo 1576486 1774273 := bbase (se 2 (by rfl) ⟨665352, by rfl⟩ : syracuseStep 1774273 = 1330705) (by norm_num)
theorem B3789517 : Blo 1576486 3789517 := bbase (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) (by norm_num)
theorem B5321429 : Blo 1576486 5321429 := bbase (se 7 (by rfl) ⟨62360, by rfl⟩ : syracuseStep 5321429 = 124721) (by norm_num)
theorem B7983845 : Blo 1576486 7983845 := bbase (se 4 (by rfl) ⟨748485, by rfl⟩ : syracuseStep 7983845 = 1496971) (by norm_num)
theorem B1774309 : Blo 1576486 1774309 := bbase (se 4 (by rfl) ⟨166341, by rfl⟩ : syracuseStep 1774309 = 332683) (by norm_num)
theorem B3994373 : Blo 1576486 3994373 := bbase (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) (by norm_num)
theorem B1774345 : Blo 1576486 1774345 := bbase (se 2 (by rfl) ⟨665379, by rfl⟩ : syracuseStep 1774345 = 1330759) (by norm_num)
theorem B1774381 : Blo 1576486 1774381 := bbase (se 3 (by rfl) ⟨332696, by rfl⟩ : syracuseStep 1774381 = 665393) (by norm_num)
theorem B4494149 : Blo 1576486 4494149 := bbase (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) (by norm_num)
theorem B1774417 : Blo 1576486 1774417 := bbase (se 2 (by rfl) ⟨665406, by rfl⟩ : syracuseStep 1774417 = 1330813) (by norm_num)
theorem B3789661 : Blo 1576486 3789661 := bbase (se 3 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 3789661 = 1421123) (by norm_num)
theorem B1995617 : Blo 1576486 1995617 := bbase (se 2 (by rfl) ⟨748356, by rfl⟩ : syracuseStep 1995617 = 1496713) (by norm_num)
theorem B1774453 : Blo 1576486 1774453 := bbase (se 5 (by rfl) ⟨83177, by rfl⟩ : syracuseStep 1774453 = 166355) (by norm_num)
theorem B1995673 : Blo 1576486 1995673 := bbase (se 2 (by rfl) ⟨748377, by rfl⟩ : syracuseStep 1995673 = 1496755) (by norm_num)
theorem B1774489 : Blo 1576486 1774489 := bbase (se 2 (by rfl) ⟨665433, by rfl⟩ : syracuseStep 1774489 = 1330867) (by norm_num)
theorem B1774525 : Blo 1576486 1774525 := bbase (se 3 (by rfl) ⟨332723, by rfl⟩ : syracuseStep 1774525 = 665447) (by norm_num)
theorem B2995157 : Blo 1576486 2995157 := bbase (se 7 (by rfl) ⟨35099, by rfl⟩ : syracuseStep 2995157 = 70199) (by norm_num)
theorem B1774561 : Blo 1576486 1774561 := bbase (se 2 (by rfl) ⟨665460, by rfl⟩ : syracuseStep 1774561 = 1330921) (by norm_num)
theorem B1995769 : Blo 1576486 1995769 := bbase (se 2 (by rfl) ⟨748413, by rfl⟩ : syracuseStep 1995769 = 1496827) (by norm_num)
theorem B1774597 : Blo 1576486 1774597 := bbase (se 4 (by rfl) ⟨166368, by rfl⟩ : syracuseStep 1774597 = 332737) (by norm_num)
theorem B1774633 : Blo 1576486 1774633 := bbase (se 2 (by rfl) ⟨665487, by rfl⟩ : syracuseStep 1774633 = 1330975) (by norm_num)
theorem B1774669 : Blo 1576486 1774669 := bbase (se 3 (by rfl) ⟨332750, by rfl⟩ : syracuseStep 1774669 = 665501) (by norm_num)
theorem B3994717 : Blo 1576486 3994717 := bbase (se 3 (by rfl) ⟨749009, by rfl⟩ : syracuseStep 3994717 = 1498019) (by norm_num)
theorem B2995309 : Blo 1576486 2995309 := bbase (se 3 (by rfl) ⟨561620, by rfl⟩ : syracuseStep 2995309 = 1123241) (by norm_num)
theorem B1774705 : Blo 1576486 1774705 := bbase (se 2 (by rfl) ⟨665514, by rfl⟩ : syracuseStep 1774705 = 1331029) (by norm_num)
theorem B5321861 : Blo 1576486 5321861 := bbase (se 4 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 5321861 = 997849) (by norm_num)
theorem B1774741 : Blo 1576486 1774741 := bbase (se 6 (by rfl) ⟨41595, by rfl⟩ : syracuseStep 1774741 = 83191) (by norm_num)
theorem B1995941 : Blo 1576486 1995941 := bbase (se 4 (by rfl) ⟨187119, by rfl⟩ : syracuseStep 1995941 = 374239) (by norm_num)
theorem B1774777 : Blo 1576486 1774777 := bbase (se 2 (by rfl) ⟨665541, by rfl⟩ : syracuseStep 1774777 = 1331083) (by norm_num)
theorem B3994829 : Blo 1576486 3994829 := bbase (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) (by norm_num)
theorem B1995997 : Blo 1576486 1995997 := bbase (se 3 (by rfl) ⟨374249, by rfl⟩ : syracuseStep 1995997 = 748499) (by norm_num)
theorem B1774813 : Blo 1576486 1774813 := bbase (se 3 (by rfl) ⟨332777, by rfl⟩ : syracuseStep 1774813 = 665555) (by norm_num)
theorem B13473013 : Blo 1576486 13473013 := bbase (se 5 (by rfl) ⟨631547, by rfl⟩ : syracuseStep 13473013 = 1263095) (by norm_num)
theorem B1774849 : Blo 1576486 1774849 := bbase (se 2 (by rfl) ⟨665568, by rfl⟩ : syracuseStep 1774849 = 1331137) (by norm_num)
theorem B5395733 : Blo 1576486 5395733 := bbase (se 6 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 5395733 = 252925) (by norm_num)
theorem B1774885 : Blo 1576486 1774885 := bbase (se 4 (by rfl) ⟨166395, by rfl⟩ : syracuseStep 1774885 = 332791) (by norm_num)
theorem B1996093 : Blo 1576486 1996093 := bbase (se 3 (by rfl) ⟨374267, by rfl⟩ : syracuseStep 1996093 = 748535) (by norm_num)
theorem B1774921 : Blo 1576486 1774921 := bbase (se 2 (by rfl) ⟨665595, by rfl⟩ : syracuseStep 1774921 = 1331191) (by norm_num)
theorem B2364749 : Blo 1576486 2364749 := bbase (se 3 (by rfl) ⟨443390, by rfl⟩ : syracuseStep 2364749 = 886781) (by norm_num)
theorem B2364773 : Blo 1576486 2364773 := bbase (se 4 (by rfl) ⟨221697, by rfl⟩ : syracuseStep 2364773 = 443395) (by norm_num)
theorem B1774957 : Blo 1576486 1774957 := bbase (se 3 (by rfl) ⟨332804, by rfl⟩ : syracuseStep 1774957 = 665609) (by norm_num)
theorem B5051765 : Blo 1576486 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B2364797 : Blo 1576486 2364797 := bbase (se 3 (by rfl) ⟨443399, by rfl⟩ : syracuseStep 2364797 = 886799) (by norm_num)
theorem B3995021 : Blo 1576486 3995021 := bbase (se 3 (by rfl) ⟨749066, by rfl⟩ : syracuseStep 3995021 = 1498133) (by norm_num)
theorem B1774993 : Blo 1576486 1774993 := bbase (se 2 (by rfl) ⟨665622, by rfl⟩ : syracuseStep 1774993 = 1331245) (by norm_num)
theorem B2364821 : Blo 1576486 2364821 := bbase (se 6 (by rfl) ⟨55425, by rfl⟩ : syracuseStep 2364821 = 110851) (by norm_num)
theorem B2995613 : Blo 1576486 2995613 := bbase (se 3 (by rfl) ⟨561677, by rfl⟩ : syracuseStep 2995613 = 1123355) (by norm_num)
theorem B2364845 : Blo 1576486 2364845 := bbase (se 3 (by rfl) ⟨443408, by rfl⟩ : syracuseStep 2364845 = 886817) (by norm_num)
theorem B1684909 : Blo 1576486 1684909 := bbase (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) (by norm_num)
theorem B1775029 : Blo 1576486 1775029 := bbase (se 5 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 1775029 = 166409) (by norm_num)
theorem B2364869 : Blo 1576486 2364869 := bbase (se 4 (by rfl) ⟨221706, by rfl⟩ : syracuseStep 2364869 = 443413) (by norm_num)
theorem B3790277 : Blo 1576486 3790277 := bbase (se 4 (by rfl) ⟨355338, by rfl⟩ : syracuseStep 3790277 = 710677) (by norm_num)
theorem B1775065 : Blo 1576486 1775065 := bbase (se 2 (by rfl) ⟨665649, by rfl⟩ : syracuseStep 1775065 = 1331299) (by norm_num)
theorem B2364893 : Blo 1576486 2364893 := bbase (se 3 (by rfl) ⟨443417, by rfl⟩ : syracuseStep 2364893 = 886835) (by norm_num)
theorem B1996265 : Blo 1576486 1996265 := bbase (se 2 (by rfl) ⟨748599, by rfl⟩ : syracuseStep 1996265 = 1497199) (by norm_num)
theorem B2364917 : Blo 1576486 2364917 := bbase (se 5 (by rfl) ⟨110855, by rfl⟩ : syracuseStep 2364917 = 221711) (by norm_num)
theorem B1684981 : Blo 1576486 1684981 := bbase (se 5 (by rfl) ⟨78983, by rfl⟩ : syracuseStep 1684981 = 157967) (by norm_num)
theorem B1775101 : Blo 1576486 1775101 := bbase (se 3 (by rfl) ⟨332831, by rfl⟩ : syracuseStep 1775101 = 665663) (by norm_num)
theorem B2364941 : Blo 1576486 2364941 := bbase (se 3 (by rfl) ⟨443426, by rfl⟩ : syracuseStep 2364941 = 886853) (by norm_num)
theorem B1996321 : Blo 1576486 1996321 := bbase (se 2 (by rfl) ⟨748620, by rfl⟩ : syracuseStep 1996321 = 1497241) (by norm_num)
theorem B1775137 : Blo 1576486 1775137 := bbase (se 2 (by rfl) ⟨665676, by rfl⟩ : syracuseStep 1775137 = 1331353) (by norm_num)
theorem B2364965 : Blo 1576486 2364965 := bbase (se 4 (by rfl) ⟨221715, by rfl⟩ : syracuseStep 2364965 = 443431) (by norm_num)
theorem B5322293 : Blo 1576486 5322293 := bbase (se 5 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 5322293 = 498965) (by norm_num)
theorem B2364989 : Blo 1576486 2364989 := bbase (se 3 (by rfl) ⟨443435, by rfl⟩ : syracuseStep 2364989 = 886871) (by norm_num)
theorem B2397757 : Blo 1576486 2397757 := bbase (se 3 (by rfl) ⟨449579, by rfl⟩ : syracuseStep 2397757 = 899159) (by norm_num)
theorem B1775173 : Blo 1576486 1775173 := bbase (se 4 (by rfl) ⟨166422, by rfl⟩ : syracuseStep 1775173 = 332845) (by norm_num)
theorem B2365013 : Blo 1576486 2365013 := bbase (se 8 (by rfl) ⟨13857, by rfl⟩ : syracuseStep 2365013 = 27715) (by norm_num)
theorem B1799777 : Blo 1576486 1799777 := bbase (se 2 (by rfl) ⟨674916, by rfl⟩ : syracuseStep 1799777 = 1349833) (by norm_num)
theorem B1775209 : Blo 1576486 1775209 := bbase (se 2 (by rfl) ⟨665703, by rfl⟩ : syracuseStep 1775209 = 1331407) (by norm_num)
theorem B2365037 : Blo 1576486 2365037 := bbase (se 3 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 2365037 = 886889) (by norm_num)
theorem B1996417 : Blo 1576486 1996417 := bbase (se 2 (by rfl) ⟨748656, by rfl⟩ : syracuseStep 1996417 = 1497313) (by norm_num)
theorem B2365061 : Blo 1576486 2365061 := bbase (se 4 (by rfl) ⟨221724, by rfl⟩ : syracuseStep 2365061 = 443449) (by norm_num)
theorem B1775245 : Blo 1576486 1775245 := bbase (se 3 (by rfl) ⟨332858, by rfl⟩ : syracuseStep 1775245 = 665717) (by norm_num)
theorem B28448405 : Blo 1576486 28448405 := bbase (se 6 (by rfl) ⟨666759, by rfl⟩ : syracuseStep 28448405 = 1333519) (by norm_num)
theorem B2365085 : Blo 1576486 2365085 := bbase (se 3 (by rfl) ⟨443453, by rfl⟩ : syracuseStep 2365085 = 886907) (by norm_num)
theorem B1685161 : Blo 1576486 1685161 := bbase (se 2 (by rfl) ⟨631935, by rfl⟩ : syracuseStep 1685161 = 1263871) (by norm_num)
theorem B1775281 : Blo 1576486 1775281 := bbase (se 2 (by rfl) ⟨665730, by rfl⟩ : syracuseStep 1775281 = 1331461) (by norm_num)
theorem B2365109 : Blo 1576486 2365109 := bbase (se 5 (by rfl) ⟨110864, by rfl⟩ : syracuseStep 2365109 = 221729) (by norm_num)
theorem B8099509 : Blo 1576486 8099509 := bbase (se 5 (by rfl) ⟨379664, by rfl⟩ : syracuseStep 8099509 = 759329) (by norm_num)
theorem B2365133 : Blo 1576486 2365133 := bbase (se 3 (by rfl) ⟨443462, by rfl⟩ : syracuseStep 2365133 = 886925) (by norm_num)
theorem B1775317 : Blo 1576486 1775317 := bbase (se 7 (by rfl) ⟨20804, by rfl⟩ : syracuseStep 1775317 = 41609) (by norm_num)
theorem B2365157 : Blo 1576486 2365157 := bbase (se 4 (by rfl) ⟨221733, by rfl⟩ : syracuseStep 2365157 = 443467) (by norm_num)
theorem B3995365 : Blo 1576486 3995365 := bbase (se 4 (by rfl) ⟨374565, by rfl⟩ : syracuseStep 3995365 = 749131) (by norm_num)
theorem B8763125 : Blo 1576486 8763125 := bbase (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) (by norm_num)
theorem B1775353 : Blo 1576486 1775353 := bbase (se 2 (by rfl) ⟨665757, by rfl⟩ : syracuseStep 1775353 = 1331515) (by norm_num)
theorem B2365181 : Blo 1576486 2365181 := bbase (se 3 (by rfl) ⟨443471, by rfl⟩ : syracuseStep 2365181 = 886943) (by norm_num)
theorem B2365205 : Blo 1576486 2365205 := bbase (se 6 (by rfl) ⟨55434, by rfl⟩ : syracuseStep 2365205 = 110869) (by norm_num)
theorem B3790613 : Blo 1576486 3790613 := bbase (se 6 (by rfl) ⟨88842, by rfl⟩ : syracuseStep 3790613 = 177685) (by norm_num)
theorem B1775389 : Blo 1576486 1775389 := bbase (se 3 (by rfl) ⟨332885, by rfl⟩ : syracuseStep 1775389 = 665771) (by norm_num)
theorem B2365229 : Blo 1576486 2365229 := bbase (se 3 (by rfl) ⟨443480, by rfl⟩ : syracuseStep 2365229 = 886961) (by norm_num)
theorem B1996589 : Blo 1576486 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B1775425 : Blo 1576486 1775425 := bbase (se 2 (by rfl) ⟨665784, by rfl⟩ : syracuseStep 1775425 = 1331569) (by norm_num)
theorem B2365253 : Blo 1576486 2365253 := bbase (se 4 (by rfl) ⟨221742, by rfl⟩ : syracuseStep 2365253 = 443485) (by norm_num)
theorem B3995477 : Blo 1576486 3995477 := bbase (se 9 (by rfl) ⟨11705, by rfl⟩ : syracuseStep 3995477 = 23411) (by norm_num)
theorem B2365277 : Blo 1576486 2365277 := bbase (se 3 (by rfl) ⟨443489, by rfl⟩ : syracuseStep 2365277 = 886979) (by norm_num)
theorem B1996645 : Blo 1576486 1996645 := bbase (se 4 (by rfl) ⟨187185, by rfl⟩ : syracuseStep 1996645 = 374371) (by norm_num)
theorem B1775461 : Blo 1576486 1775461 := bbase (se 4 (by rfl) ⟨166449, by rfl⟩ : syracuseStep 1775461 = 332899) (by norm_num)
theorem B2365301 : Blo 1576486 2365301 := bbase (se 5 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 2365301 = 221747) (by norm_num)
theorem B3790709 : Blo 1576486 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B1775497 : Blo 1576486 1775497 := bbase (se 2 (by rfl) ⟨665811, by rfl⟩ : syracuseStep 1775497 = 1331623) (by norm_num)
theorem B2365325 : Blo 1576486 2365325 := bbase (se 3 (by rfl) ⟨443498, by rfl⟩ : syracuseStep 2365325 = 886997) (by norm_num)
theorem B2365349 : Blo 1576486 2365349 := bbase (se 4 (by rfl) ⟨221751, by rfl⟩ : syracuseStep 2365349 = 443503) (by norm_num)
theorem B1775533 : Blo 1576486 1775533 := bbase (se 3 (by rfl) ⟨332912, by rfl⟩ : syracuseStep 1775533 = 665825) (by norm_num)
theorem B2365373 : Blo 1576486 2365373 := bbase (se 3 (by rfl) ⟨443507, by rfl⟩ : syracuseStep 2365373 = 887015) (by norm_num)
theorem B1996741 : Blo 1576486 1996741 := bbase (se 4 (by rfl) ⟨187194, by rfl⟩ : syracuseStep 1996741 = 374389) (by norm_num)
theorem B1775569 : Blo 1576486 1775569 := bbase (se 2 (by rfl) ⟨665838, by rfl⟩ : syracuseStep 1775569 = 1331677) (by norm_num)
theorem B2365397 : Blo 1576486 2365397 := bbase (se 7 (by rfl) ⟨27719, by rfl⟩ : syracuseStep 2365397 = 55439) (by norm_num)
theorem B5322725 : Blo 1576486 5322725 := bbase (se 4 (by rfl) ⟨499005, by rfl⟩ : syracuseStep 5322725 = 998011) (by norm_num)
theorem B2365421 : Blo 1576486 2365421 := bbase (se 3 (by rfl) ⟨443516, by rfl⟩ : syracuseStep 2365421 = 887033) (by norm_num)
theorem B7985141 : Blo 1576486 7985141 := bbase (se 5 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 7985141 = 748607) (by norm_num)
theorem B1775605 : Blo 1576486 1775605 := bbase (se 5 (by rfl) ⟨83231, by rfl⟩ : syracuseStep 1775605 = 166463) (by norm_num)
theorem B2660357 : Blo 1576486 2660357 := bbase (se 4 (by rfl) ⟨249408, by rfl⟩ : syracuseStep 2660357 = 498817) (by norm_num)
theorem B2365445 : Blo 1576486 2365445 := bbase (se 4 (by rfl) ⟨221760, by rfl⟩ : syracuseStep 2365445 = 443521) (by norm_num)
theorem B1775641 : Blo 1576486 1775641 := bbase (se 2 (by rfl) ⟨665865, by rfl⟩ : syracuseStep 1775641 = 1331731) (by norm_num)
theorem B2365469 : Blo 1576486 2365469 := bbase (se 3 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 2365469 = 887051) (by norm_num)
theorem B1620005 : Blo 1576486 1620005 := bbase (se 4 (by rfl) ⟨151875, by rfl⟩ : syracuseStep 1620005 = 303751) (by norm_num)
theorem B2365493 : Blo 1576486 2365493 := bbase (se 5 (by rfl) ⟨110882, by rfl⟩ : syracuseStep 2365493 = 221765) (by norm_num)
theorem B3790901 : Blo 1576486 3790901 := bbase (se 5 (by rfl) ⟨177698, by rfl⟩ : syracuseStep 3790901 = 355397) (by norm_num)
theorem B1775677 : Blo 1576486 1775677 := bbase (se 3 (by rfl) ⟨332939, by rfl⟩ : syracuseStep 1775677 = 665879) (by norm_num)
theorem B2365517 : Blo 1576486 2365517 := bbase (se 3 (by rfl) ⟨443534, by rfl⟩ : syracuseStep 2365517 = 887069) (by norm_num)
theorem B1775713 : Blo 1576486 1775713 := bbase (se 2 (by rfl) ⟨665892, by rfl⟩ : syracuseStep 1775713 = 1331785) (by norm_num)
theorem B2365541 : Blo 1576486 2365541 := bbase (se 4 (by rfl) ⟨221769, by rfl⟩ : syracuseStep 2365541 = 443539) (by norm_num)
theorem B1685605 : Blo 1576486 1685605 := bbase (se 4 (by rfl) ⟨158025, by rfl⟩ : syracuseStep 1685605 = 316051) (by norm_num)
theorem B1996913 : Blo 1576486 1996913 := bbase (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) (by norm_num)
theorem B2365565 : Blo 1576486 2365565 := bbase (se 3 (by rfl) ⟨443543, by rfl⟩ : syracuseStep 2365565 = 887087) (by norm_num)
theorem B2660485 : Blo 1576486 2660485 := bbase (se 4 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 2660485 = 498841) (by norm_num)
theorem B1775749 : Blo 1576486 1775749 := bbase (se 4 (by rfl) ⟨166476, by rfl⟩ : syracuseStep 1775749 = 332953) (by norm_num)
theorem B2996365 : Blo 1576486 2996365 := bbase (se 3 (by rfl) ⟨561818, by rfl⟩ : syracuseStep 2996365 = 1123637) (by norm_num)
theorem B2365589 : Blo 1576486 2365589 := bbase (se 6 (by rfl) ⟨55443, by rfl⟩ : syracuseStep 2365589 = 110887) (by norm_num)
theorem B1996969 : Blo 1576486 1996969 := bbase (se 2 (by rfl) ⟨748863, by rfl⟩ : syracuseStep 1996969 = 1497727) (by norm_num)
theorem B1775785 : Blo 1576486 1775785 := bbase (se 2 (by rfl) ⟨665919, by rfl⟩ : syracuseStep 1775785 = 1331839) (by norm_num)
theorem B2365613 : Blo 1576486 2365613 := bbase (se 3 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 2365613 = 887105) (by norm_num)
theorem B2365637 : Blo 1576486 2365637 := bbase (se 4 (by rfl) ⟨221778, by rfl⟩ : syracuseStep 2365637 = 443557) (by norm_num)
theorem B8984789 : Blo 1576486 8984789 := bbase (se 7 (by rfl) ⟨105290, by rfl⟩ : syracuseStep 8984789 = 210581) (by norm_num)
theorem B2660573 : Blo 1576486 2660573 := bbase (se 3 (by rfl) ⟨498857, by rfl⟩ : syracuseStep 2660573 = 997715) (by norm_num)
theorem B2365661 : Blo 1576486 2365661 := bbase (se 3 (by rfl) ⟨443561, by rfl⟩ : syracuseStep 2365661 = 887123) (by norm_num)
theorem B2365685 : Blo 1576486 2365685 := bbase (se 5 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 2365685 = 221783) (by norm_num)
theorem B1997065 : Blo 1576486 1997065 := bbase (se 2 (by rfl) ⟨748899, by rfl⟩ : syracuseStep 1997065 = 1497799) (by norm_num)
theorem B2365709 : Blo 1576486 2365709 := bbase (se 3 (by rfl) ⟨443570, by rfl⟩ : syracuseStep 2365709 = 887141) (by norm_num)
theorem B2996509 : Blo 1576486 2996509 := bbase (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) (by norm_num)
theorem B2365733 : Blo 1576486 2365733 := bbase (se 4 (by rfl) ⟨221787, by rfl⟩ : syracuseStep 2365733 = 443575) (by norm_num)
theorem B2365757 : Blo 1576486 2365757 := bbase (se 3 (by rfl) ⟨443579, by rfl⟩ : syracuseStep 2365757 = 887159) (by norm_num)
theorem B2365781 : Blo 1576486 2365781 := bbase (se 10 (by rfl) ⟨3465, by rfl⟩ : syracuseStep 2365781 = 6931) (by norm_num)
theorem B2660701 : Blo 1576486 2660701 := bbase (se 3 (by rfl) ⟨498881, by rfl⟩ : syracuseStep 2660701 = 997763) (by norm_num)
theorem B2365805 : Blo 1576486 2365805 := bbase (se 3 (by rfl) ⟨443588, by rfl⟩ : syracuseStep 2365805 = 887177) (by norm_num)
theorem B2365829 : Blo 1576486 2365829 := bbase (se 4 (by rfl) ⟨221796, by rfl⟩ : syracuseStep 2365829 = 443593) (by norm_num)
theorem B2161037 : Blo 1576486 2161037 := bbase (se 3 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 2161037 = 810389) (by norm_num)
theorem B5323157 : Blo 1576486 5323157 := bbase (se 6 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 5323157 = 249523) (by norm_num)
theorem B2365853 : Blo 1576486 2365853 := bbase (se 3 (by rfl) ⟨443597, by rfl⟩ : syracuseStep 2365853 = 887195) (by norm_num)
theorem B4045229 : Blo 1576486 4045229 := bbase (se 3 (by rfl) ⟨758480, by rfl⟩ : syracuseStep 4045229 = 1516961) (by norm_num)
theorem B2660789 : Blo 1576486 2660789 := bbase (se 5 (by rfl) ⟨124724, by rfl⟩ : syracuseStep 2660789 = 249449) (by norm_num)
theorem B2365877 : Blo 1576486 2365877 := bbase (se 5 (by rfl) ⟨110900, by rfl⟩ : syracuseStep 2365877 = 221801) (by norm_num)
theorem B1997237 : Blo 1576486 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B2365901 : Blo 1576486 2365901 := bbase (se 3 (by rfl) ⟨443606, by rfl⟩ : syracuseStep 2365901 = 887213) (by norm_num)
theorem B2365925 : Blo 1576486 2365925 := bbase (se 4 (by rfl) ⟨221805, by rfl⟩ : syracuseStep 2365925 = 443611) (by norm_num)
theorem B1997293 : Blo 1576486 1997293 := bbase (se 3 (by rfl) ⟨374492, by rfl⟩ : syracuseStep 1997293 = 748985) (by norm_num)
theorem B2365949 : Blo 1576486 2365949 := bbase (se 3 (by rfl) ⟨443615, by rfl⟩ : syracuseStep 2365949 = 887231) (by norm_num)
theorem B2365973 : Blo 1576486 2365973 := bbase (se 6 (by rfl) ⟨55452, by rfl⟩ : syracuseStep 2365973 = 110905) (by norm_num)
theorem B2365997 : Blo 1576486 2365997 := bbase (se 3 (by rfl) ⟨443624, by rfl⟩ : syracuseStep 2365997 = 887249) (by norm_num)
theorem B2660917 : Blo 1576486 2660917 := bbase (se 5 (by rfl) ⟨124730, by rfl⟩ : syracuseStep 2660917 = 249461) (by norm_num)
theorem B3463741 : Blo 1576486 3463741 := bbase (se 3 (by rfl) ⟨649451, by rfl⟩ : syracuseStep 3463741 = 1298903) (by norm_num)
theorem B2841157 : Blo 1576486 2841157 := bbase (se 4 (by rfl) ⟨266358, by rfl⟩ : syracuseStep 2841157 = 532717) (by norm_num)
theorem B2366021 : Blo 1576486 2366021 := bbase (se 4 (by rfl) ⟨221814, by rfl⟩ : syracuseStep 2366021 = 443629) (by norm_num)
theorem B1997389 : Blo 1576486 1997389 := bbase (se 3 (by rfl) ⟨374510, by rfl⟩ : syracuseStep 1997389 = 749021) (by norm_num)
theorem B2161237 : Blo 1576486 2161237 := bbase (se 8 (by rfl) ⟨12663, by rfl⟩ : syracuseStep 2161237 = 25327) (by norm_num)
theorem B2366045 : Blo 1576486 2366045 := bbase (se 3 (by rfl) ⟨443633, by rfl⟩ : syracuseStep 2366045 = 887267) (by norm_num)
theorem B2079325 : Blo 1576486 2079325 := bbase (se 3 (by rfl) ⟨389873, by rfl⟩ : syracuseStep 2079325 = 779747) (by norm_num)
theorem B2366069 : Blo 1576486 2366069 := bbase (se 5 (by rfl) ⟨110909, by rfl⟩ : syracuseStep 2366069 = 221819) (by norm_num)
theorem B2661005 : Blo 1576486 2661005 := bbase (se 3 (by rfl) ⟨498938, by rfl⟩ : syracuseStep 2661005 = 997877) (by norm_num)
theorem B2366093 : Blo 1576486 2366093 := bbase (se 3 (by rfl) ⟨443642, by rfl⟩ : syracuseStep 2366093 = 887285) (by norm_num)
theorem B2366117 : Blo 1576486 2366117 := bbase (se 4 (by rfl) ⟨221823, by rfl⟩ : syracuseStep 2366117 = 443647) (by norm_num)
theorem B2366141 : Blo 1576486 2366141 := bbase (se 3 (by rfl) ⟨443651, by rfl⟩ : syracuseStep 2366141 = 887303) (by norm_num)
theorem B2366165 : Blo 1576486 2366165 := bbase (se 7 (by rfl) ⟨27728, by rfl⟩ : syracuseStep 2366165 = 55457) (by norm_num)
theorem B2366189 : Blo 1576486 2366189 := bbase (se 3 (by rfl) ⟨443660, by rfl⟩ : syracuseStep 2366189 = 887321) (by norm_num)
theorem B1997561 : Blo 1576486 1997561 := bbase (se 2 (by rfl) ⟨749085, by rfl⟩ : syracuseStep 1997561 = 1498171) (by norm_num)
theorem B2366213 : Blo 1576486 2366213 := bbase (se 4 (by rfl) ⟨221832, by rfl⟩ : syracuseStep 2366213 = 443665) (by norm_num)
theorem B2661133 : Blo 1576486 2661133 := bbase (se 3 (by rfl) ⟨498962, by rfl⟩ : syracuseStep 2661133 = 997925) (by norm_num)
theorem B2366237 : Blo 1576486 2366237 := bbase (se 3 (by rfl) ⟨443669, by rfl⟩ : syracuseStep 2366237 = 887339) (by norm_num)
theorem B4799269 : Blo 1576486 4799269 := bbase (se 4 (by rfl) ⟨449931, by rfl⟩ : syracuseStep 4799269 = 899863) (by norm_num)
theorem B1997617 : Blo 1576486 1997617 := bbase (se 2 (by rfl) ⟨749106, by rfl⟩ : syracuseStep 1997617 = 1498213) (by norm_num)
theorem B2366261 : Blo 1576486 2366261 := bbase (se 5 (by rfl) ⟨110918, by rfl⟩ : syracuseStep 2366261 = 221837) (by norm_num)
theorem B5987141 : Blo 1576486 5987141 := bbase (se 4 (by rfl) ⟨561294, by rfl⟩ : syracuseStep 5987141 = 1122589) (by norm_num)
theorem B5323589 : Blo 1576486 5323589 := bbase (se 4 (by rfl) ⟨499086, by rfl⟩ : syracuseStep 5323589 = 998173) (by norm_num)
theorem B2366285 : Blo 1576486 2366285 := bbase (se 3 (by rfl) ⟨443678, by rfl⟩ : syracuseStep 2366285 = 887357) (by norm_num)
theorem B2661221 : Blo 1576486 2661221 := bbase (se 4 (by rfl) ⟨249489, by rfl⟩ : syracuseStep 2661221 = 498979) (by norm_num)
theorem B2366309 : Blo 1576486 2366309 := bbase (se 4 (by rfl) ⟨221841, by rfl⟩ : syracuseStep 2366309 = 443683) (by norm_num)
theorem B2366333 : Blo 1576486 2366333 := bbase (se 3 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 2366333 = 887375) (by norm_num)
theorem B1997713 : Blo 1576486 1997713 := bbase (se 2 (by rfl) ⟨749142, by rfl⟩ : syracuseStep 1997713 = 1498285) (by norm_num)
theorem B2366357 : Blo 1576486 2366357 := bbase (se 6 (by rfl) ⟨55461, by rfl⟩ : syracuseStep 2366357 = 110923) (by norm_num)
theorem B2366381 : Blo 1576486 2366381 := bbase (se 3 (by rfl) ⟨443696, by rfl⟩ : syracuseStep 2366381 = 887393) (by norm_num)
theorem B2366405 : Blo 1576486 2366405 := bbase (se 4 (by rfl) ⟨221850, by rfl⟩ : syracuseStep 2366405 = 443701) (by norm_num)
theorem B2366429 : Blo 1576486 2366429 := bbase (se 3 (by rfl) ⟨443705, by rfl⟩ : syracuseStep 2366429 = 887411) (by norm_num)
theorem B2661349 : Blo 1576486 2661349 := bbase (se 4 (by rfl) ⟨249501, by rfl⟩ : syracuseStep 2661349 = 499003) (by norm_num)
theorem B2366453 : Blo 1576486 2366453 := bbase (se 5 (by rfl) ⟨110927, by rfl⟩ : syracuseStep 2366453 = 221855) (by norm_num)
theorem B2366477 : Blo 1576486 2366477 := bbase (se 3 (by rfl) ⟨443714, by rfl⟩ : syracuseStep 2366477 = 887429) (by norm_num)
theorem B2366501 : Blo 1576486 2366501 := bbase (se 4 (by rfl) ⟨221859, by rfl⟩ : syracuseStep 2366501 = 443719) (by norm_num)
theorem B2661437 : Blo 1576486 2661437 := bbase (se 3 (by rfl) ⟨499019, by rfl⟩ : syracuseStep 2661437 = 998039) (by norm_num)
theorem B2366525 : Blo 1576486 2366525 := bbase (se 3 (by rfl) ⟨443723, by rfl⟩ : syracuseStep 2366525 = 887447) (by norm_num)
theorem B2276429 : Blo 1576486 2276429 := bbase (se 3 (by rfl) ⟨426830, by rfl⟩ : syracuseStep 2276429 = 853661) (by norm_num)
theorem B2366549 : Blo 1576486 2366549 := bbase (se 8 (by rfl) ⟨13866, by rfl⟩ : syracuseStep 2366549 = 27733) (by norm_num)
theorem B5987429 : Blo 1576486 5987429 := bbase (se 4 (by rfl) ⟨561321, by rfl⟩ : syracuseStep 5987429 = 1122643) (by norm_num)
theorem B2366573 : Blo 1576486 2366573 := bbase (se 3 (by rfl) ⟨443732, by rfl⟩ : syracuseStep 2366573 = 887465) (by norm_num)
theorem B2366597 : Blo 1576486 2366597 := bbase (se 4 (by rfl) ⟨221868, by rfl⟩ : syracuseStep 2366597 = 443737) (by norm_num)
theorem B2366621 : Blo 1576486 2366621 := bbase (se 3 (by rfl) ⟨443741, by rfl⟩ : syracuseStep 2366621 = 887483) (by norm_num)
theorem B13474997 : Blo 1576486 13474997 := bbase (se 5 (by rfl) ⟨631640, by rfl⟩ : syracuseStep 13474997 = 1263281) (by norm_num)
theorem B2366645 : Blo 1576486 2366645 := bbase (se 5 (by rfl) ⟨110936, by rfl⟩ : syracuseStep 2366645 = 221873) (by norm_num)
theorem B3792053 : Blo 1576486 3792053 := bbase (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) (by norm_num)
theorem B2661565 : Blo 1576486 2661565 := bbase (se 3 (by rfl) ⟨499043, by rfl⟩ : syracuseStep 2661565 = 998087) (by norm_num)
theorem B2399429 : Blo 1576486 2399429 := bbase (se 4 (by rfl) ⟨224946, by rfl⟩ : syracuseStep 2399429 = 449893) (by norm_num)
theorem B2366669 : Blo 1576486 2366669 := bbase (se 3 (by rfl) ⟨443750, by rfl⟩ : syracuseStep 2366669 = 887501) (by norm_num)
theorem B2841821 : Blo 1576486 2841821 := bbase (se 3 (by rfl) ⟨532841, by rfl⟩ : syracuseStep 2841821 = 1065683) (by norm_num)
theorem B2366693 : Blo 1576486 2366693 := bbase (se 4 (by rfl) ⟨221877, by rfl⟩ : syracuseStep 2366693 = 443755) (by norm_num)
theorem B5324021 : Blo 1576486 5324021 := bbase (se 5 (by rfl) ⟨249563, by rfl⟩ : syracuseStep 5324021 = 499127) (by norm_num)
theorem B2366717 : Blo 1576486 2366717 := bbase (se 3 (by rfl) ⟨443759, by rfl⟩ : syracuseStep 2366717 = 887519) (by norm_num)
theorem B7986437 : Blo 1576486 7986437 := bbase (se 4 (by rfl) ⟨748728, by rfl⟩ : syracuseStep 7986437 = 1497457) (by norm_num)
theorem B2661653 : Blo 1576486 2661653 := bbase (se 6 (by rfl) ⟨62382, by rfl⟩ : syracuseStep 2661653 = 124765) (by norm_num)
theorem B2366741 : Blo 1576486 2366741 := bbase (se 6 (by rfl) ⟨55470, by rfl⟩ : syracuseStep 2366741 = 110941) (by norm_num)
theorem B2366765 : Blo 1576486 2366765 := bbase (se 3 (by rfl) ⟨443768, by rfl⟩ : syracuseStep 2366765 = 887537) (by norm_num)
theorem B15162677 : Blo 1576486 15162677 := bbase (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) (by norm_num)
theorem B5053765 : Blo 1576486 5053765 := bbase (se 4 (by rfl) ⟨473790, by rfl⟩ : syracuseStep 5053765 = 947581) (by norm_num)
theorem B2366789 : Blo 1576486 2366789 := bbase (se 4 (by rfl) ⟨221886, by rfl⟩ : syracuseStep 2366789 = 443773) (by norm_num)
theorem B7585109 : Blo 1576486 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B2366813 : Blo 1576486 2366813 := bbase (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) (by norm_num)
theorem B2366837 : Blo 1576486 2366837 := bbase (se 5 (by rfl) ⟨110945, by rfl⟩ : syracuseStep 2366837 = 221891) (by norm_num)
theorem B2366861 : Blo 1576486 2366861 := bbase (se 3 (by rfl) ⟨443786, by rfl⟩ : syracuseStep 2366861 = 887573) (by norm_num)
theorem B2661781 : Blo 1576486 2661781 := bbase (se 6 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 2661781 = 124771) (by norm_num)
theorem B2366885 : Blo 1576486 2366885 := bbase (se 4 (by rfl) ⟨221895, by rfl⟩ : syracuseStep 2366885 = 443791) (by norm_num)
theorem B6741413 : Blo 1576486 6741413 := bbase (se 4 (by rfl) ⟨632007, by rfl⟩ : syracuseStep 6741413 = 1264015) (by norm_num)
theorem B3841453 : Blo 1576486 3841453 := bbase (se 3 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 3841453 = 1440545) (by norm_num)
theorem B2366909 : Blo 1576486 2366909 := bbase (se 3 (by rfl) ⟨443795, by rfl⟩ : syracuseStep 2366909 = 887591) (by norm_num)
theorem B1973705 : Blo 1576486 1973705 := bbase (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) (by norm_num)
theorem B2366933 : Blo 1576486 2366933 := bbase (se 7 (by rfl) ⟨27737, by rfl⟩ : syracuseStep 2366933 = 55475) (by norm_num)
theorem B2661869 : Blo 1576486 2661869 := bbase (se 3 (by rfl) ⟨499100, by rfl⟩ : syracuseStep 2661869 = 998201) (by norm_num)
theorem B2366957 : Blo 1576486 2366957 := bbase (se 3 (by rfl) ⟨443804, by rfl⟩ : syracuseStep 2366957 = 887609) (by norm_num)
theorem B2366981 : Blo 1576486 2366981 := bbase (se 4 (by rfl) ⟨221904, by rfl⟩ : syracuseStep 2366981 = 443809) (by norm_num)
theorem B2367005 : Blo 1576486 2367005 := bbase (se 3 (by rfl) ⟨443813, by rfl⟩ : syracuseStep 2367005 = 887627) (by norm_num)
theorem B14777909 : Blo 1576486 14777909 := bbase (se 5 (by rfl) ⟨692714, by rfl⟩ : syracuseStep 14777909 = 1385429) (by norm_num)
theorem B2367029 : Blo 1576486 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B2367053 : Blo 1576486 2367053 := bbase (se 3 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 2367053 = 887645) (by norm_num)
theorem B2367077 : Blo 1576486 2367077 := bbase (se 4 (by rfl) ⟨221913, by rfl⟩ : syracuseStep 2367077 = 443827) (by norm_num)
theorem B2661997 : Blo 1576486 2661997 := bbase (se 3 (by rfl) ⟨499124, by rfl⟩ : syracuseStep 2661997 = 998249) (by norm_num)
theorem B2367101 : Blo 1576486 2367101 := bbase (se 3 (by rfl) ⟨443831, by rfl⟩ : syracuseStep 2367101 = 887663) (by norm_num)
theorem B14384789 : Blo 1576486 14384789 := bbase (se 6 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 14384789 = 674287) (by norm_num)
theorem B2367125 : Blo 1576486 2367125 := bbase (se 6 (by rfl) ⟨55479, by rfl⟩ : syracuseStep 2367125 = 110959) (by norm_num)
theorem B5324453 : Blo 1576486 5324453 := bbase (se 4 (by rfl) ⟨499167, by rfl⟩ : syracuseStep 5324453 = 998335) (by norm_num)
theorem B2367149 : Blo 1576486 2367149 := bbase (se 3 (by rfl) ⟨443840, by rfl⟩ : syracuseStep 2367149 = 887681) (by norm_num)
theorem B2662085 : Blo 1576486 2662085 := bbase (se 4 (by rfl) ⟨249570, by rfl⟩ : syracuseStep 2662085 = 499141) (by norm_num)
theorem B2367173 : Blo 1576486 2367173 := bbase (se 4 (by rfl) ⟨221922, by rfl⟩ : syracuseStep 2367173 = 443845) (by norm_num)
theorem B6741701 : Blo 1576486 6741701 := bbase (se 4 (by rfl) ⟨632034, by rfl⟩ : syracuseStep 6741701 = 1264069) (by norm_num)
theorem B2367197 : Blo 1576486 2367197 := bbase (se 3 (by rfl) ⟨443849, by rfl⟩ : syracuseStep 2367197 = 887699) (by norm_num)
theorem B4046573 : Blo 1576486 4046573 := bbase (se 3 (by rfl) ⟨758732, by rfl⟩ : syracuseStep 4046573 = 1517465) (by norm_num)
theorem B2367221 : Blo 1576486 2367221 := bbase (se 5 (by rfl) ⟨110963, by rfl⟩ : syracuseStep 2367221 = 221927) (by norm_num)
theorem B2367245 : Blo 1576486 2367245 := bbase (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) (by norm_num)
theorem B2367269 : Blo 1576486 2367269 := bbase (se 4 (by rfl) ⟨221931, by rfl⟩ : syracuseStep 2367269 = 443863) (by norm_num)
theorem B2367293 : Blo 1576486 2367293 := bbase (se 3 (by rfl) ⟨443867, by rfl⟩ : syracuseStep 2367293 = 887735) (by norm_num)
theorem B2662213 : Blo 1576486 2662213 := bbase (se 4 (by rfl) ⟨249582, by rfl⟩ : syracuseStep 2662213 = 499165) (by norm_num)
theorem B2367317 : Blo 1576486 2367317 := bbase (se 9 (by rfl) ⟨6935, by rfl⟩ : syracuseStep 2367317 = 13871) (by norm_num)
theorem B2367341 : Blo 1576486 2367341 := bbase (se 3 (by rfl) ⟨443876, by rfl⟩ : syracuseStep 2367341 = 887753) (by norm_num)
theorem B2367365 : Blo 1576486 2367365 := bbase (se 4 (by rfl) ⟨221940, by rfl⟩ : syracuseStep 2367365 = 443881) (by norm_num)
theorem B6832021 : Blo 1576486 6832021 := bbase (se 6 (by rfl) ⟨160125, by rfl⟩ : syracuseStep 6832021 = 320251) (by norm_num)
theorem B2662301 : Blo 1576486 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B2367389 : Blo 1576486 2367389 := bbase (se 3 (by rfl) ⟨443885, by rfl⟩ : syracuseStep 2367389 = 887771) (by norm_num)
theorem B2842541 : Blo 1576486 2842541 := bbase (se 3 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 2842541 = 1065953) (by norm_num)
theorem B2367413 : Blo 1576486 2367413 := bbase (se 5 (by rfl) ⟨110972, by rfl⟩ : syracuseStep 2367413 = 221945) (by norm_num)
theorem B2367437 : Blo 1576486 2367437 := bbase (se 3 (by rfl) ⟨443894, by rfl⟩ : syracuseStep 2367437 = 887789) (by norm_num)
theorem B2367461 : Blo 1576486 2367461 := bbase (se 4 (by rfl) ⟨221949, by rfl⟩ : syracuseStep 2367461 = 443899) (by norm_num)
theorem B3547133 : Blo 1576486 3547133 := bbase (se 3 (by rfl) ⟨665087, by rfl⟩ : syracuseStep 3547133 = 1330175) (by norm_num)
theorem B2367491 : Blo 1576486 2367491 := bstep (se 1 (by rfl) ⟨1775618, by rfl⟩ : syracuseStep 2367491 = 3551237) B3551237
theorem B2367521 : Blo 1576486 2367521 := bstep (se 2 (by rfl) ⟨887820, by rfl⟩ : syracuseStep 2367521 = 1775641) B1775641
theorem B5988401 : Blo 1576486 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B2367539 : Blo 1576486 2367539 := bstep (se 1 (by rfl) ⟨1775654, by rfl⟩ : syracuseStep 2367539 = 3551309) B3551309
theorem B2367569 : Blo 1576486 2367569 := bstep (se 2 (by rfl) ⟨887838, by rfl⟩ : syracuseStep 2367569 = 1775677) B1775677
theorem B2662483 : Blo 1576486 2662483 := bstep (se 1 (by rfl) ⟨1996862, by rfl⟩ : syracuseStep 2662483 = 3993725) B3993725
theorem B2367587 : Blo 1576486 2367587 := bstep (se 1 (by rfl) ⟨1775690, by rfl⟩ : syracuseStep 2367587 = 3551381) B3551381
theorem B2367617 : Blo 1576486 2367617 := bstep (se 2 (by rfl) ⟨887856, by rfl⟩ : syracuseStep 2367617 = 1775713) B1775713
theorem B2367635 : Blo 1576486 2367635 := bstep (se 1 (by rfl) ⟨1775726, by rfl⟩ : syracuseStep 2367635 = 3551453) B3551453
theorem B3547313 : Blo 1576486 3547313 := bstep (se 2 (by rfl) ⟨1330242, by rfl⟩ : syracuseStep 3547313 = 2660485) B2660485
theorem B2367665 : Blo 1576486 2367665 := bstep (se 2 (by rfl) ⟨887874, by rfl⟩ : syracuseStep 2367665 = 1775749) B1775749
theorem B3547331 : Blo 1576486 3547331 := bstep (se 1 (by rfl) ⟨2660498, by rfl⟩ : syracuseStep 3547331 = 5320997) B5320997
theorem B4554947 : Blo 1576486 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B2367683 : Blo 1576486 2367683 := bstep (se 1 (by rfl) ⟨1775762, by rfl⟩ : syracuseStep 2367683 = 3551525) B3551525
theorem B6070477 : Blo 1576486 6070477 := bstep (se 3 (by rfl) ⟨1138214, by rfl⟩ : syracuseStep 6070477 = 2276429) B2276429
theorem B2662625 : Blo 1576486 2662625 := bstep (se 2 (by rfl) ⟨998484, by rfl⟩ : syracuseStep 2662625 = 1996969) B1996969
theorem B2367713 : Blo 1576486 2367713 := bstep (se 2 (by rfl) ⟨887892, by rfl⟩ : syracuseStep 2367713 = 1775785) B1775785
theorem B5325101 : Blo 1576486 5325101 := bstep (se 3 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 5325101 = 1996913) B1996913
theorem B18473285 : Blo 1576486 18473285 := bstep (se 4 (by rfl) ⟨1731870, by rfl⟩ : syracuseStep 18473285 = 3463741) B3463741
theorem B2662753 : Blo 1576486 2662753 := bstep (se 2 (by rfl) ⟨998532, by rfl⟩ : syracuseStep 2662753 = 1997065) B1997065
theorem B5325155 : Blo 1576486 5325155 := bstep (se 1 (by rfl) ⟨3993866, by rfl⟩ : syracuseStep 5325155 = 7987733) B7987733
theorem B6742385 : Blo 1576486 6742385 := bstep (se 2 (by rfl) ⟨2528394, by rfl⟩ : syracuseStep 6742385 = 5056789) B5056789
theorem B2662787 : Blo 1576486 2662787 := bstep (se 1 (by rfl) ⟨1997090, by rfl⟩ : syracuseStep 2662787 = 3994181) B3994181
theorem B8987021 : Blo 1576486 8987021 := bstep (se 3 (by rfl) ⟨1685066, by rfl⟩ : syracuseStep 8987021 = 3370133) B3370133
theorem B2843075 : Blo 1576486 2843075 := bstep (se 1 (by rfl) ⟨2132306, by rfl⟩ : syracuseStep 2843075 = 4264613) B4264613
theorem B3547601 : Blo 1576486 3547601 := bstep (se 2 (by rfl) ⟨1330350, by rfl⟩ : syracuseStep 3547601 = 2660701) B2660701
theorem B3547619 : Blo 1576486 3547619 := bstep (se 1 (by rfl) ⟨2660714, by rfl⟩ : syracuseStep 3547619 = 5321429) B5321429
theorem B2662915 : Blo 1576486 2662915 := bstep (se 1 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 2662915 = 3994373) B3994373
theorem B8978957 : Blo 1576486 8978957 := bstep (se 3 (by rfl) ⟨1683554, by rfl⟩ : syracuseStep 8978957 = 3367109) B3367109
theorem B5685773 : Blo 1576486 5685773 := bstep (se 3 (by rfl) ⟨1066082, by rfl⟩ : syracuseStep 5685773 = 2132165) B2132165
theorem B5325425 : Blo 1576486 5325425 := bstep (se 2 (by rfl) ⟨1997034, by rfl⟩ : syracuseStep 5325425 = 3994069) B3994069
theorem B5399153 : Blo 1576486 5399153 := bstep (se 2 (by rfl) ⟨2024682, by rfl⟩ : syracuseStep 5399153 = 4049365) B4049365
theorem B2663057 : Blo 1576486 2663057 := bstep (se 2 (by rfl) ⟨998646, by rfl⟩ : syracuseStep 2663057 = 1997293) B1997293
theorem B4489901 : Blo 1576486 4489901 := bstep (se 3 (by rfl) ⟨841856, by rfl⟩ : syracuseStep 4489901 = 1683713) B1683713
theorem B5055149 : Blo 1576486 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B2245315 : Blo 1576486 2245315 := bstep (se 1 (by rfl) ⟨1683986, by rfl⟩ : syracuseStep 2245315 = 3367973) B3367973
theorem B3547889 : Blo 1576486 3547889 := bstep (se 2 (by rfl) ⟨1330458, by rfl⟩ : syracuseStep 3547889 = 2660917) B2660917
theorem B10109681 : Blo 1576486 10109681 := bstep (se 2 (by rfl) ⟨3791130, by rfl⟩ : syracuseStep 10109681 = 7582261) B7582261
theorem B3547907 : Blo 1576486 3547907 := bstep (se 1 (by rfl) ⟨2660930, by rfl⟩ : syracuseStep 3547907 = 5321861) B5321861
theorem B2663185 : Blo 1576486 2663185 := bstep (se 2 (by rfl) ⟨998694, by rfl⟩ : syracuseStep 2663185 = 1997389) B1997389
theorem B2245411 : Blo 1576486 2245411 := bstep (se 1 (by rfl) ⟨1684058, by rfl⟩ : syracuseStep 2245411 = 3368117) B3368117
theorem B2663219 : Blo 1576486 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B18219829 : Blo 1576486 18219829 := bstep (se 5 (by rfl) ⟨854054, by rfl⟩ : syracuseStep 18219829 = 1708109) B1708109
theorem B3597155 : Blo 1576486 3597155 := bstep (se 1 (by rfl) ⟨2697866, by rfl⟩ : syracuseStep 3597155 = 5395733) B5395733
theorem B4490093 : Blo 1576486 4490093 := bstep (se 3 (by rfl) ⟨841892, by rfl⟩ : syracuseStep 4490093 = 1683785) B1683785
theorem B3367793 : Blo 1576486 3367793 := bstep (se 2 (by rfl) ⟨1262922, by rfl⟩ : syracuseStep 3367793 = 2525845) B2525845
theorem B2663347 : Blo 1576486 2663347 := bstep (se 1 (by rfl) ⟨1997510, by rfl⟩ : syracuseStep 2663347 = 3995021) B3995021
theorem B3548177 : Blo 1576486 3548177 := bstep (se 2 (by rfl) ⟨1330566, by rfl⟩ : syracuseStep 3548177 = 2661133) B2661133
theorem B3548195 : Blo 1576486 3548195 := bstep (se 1 (by rfl) ⟨2661146, by rfl⟩ : syracuseStep 3548195 = 5322293) B5322293
theorem B2663489 : Blo 1576486 2663489 := bstep (se 2 (by rfl) ⟨998808, by rfl⟩ : syracuseStep 2663489 = 1997617) B1997617
theorem B18965603 : Blo 1576486 18965603 := bstep (se 1 (by rfl) ⟨14224202, by rfl⟩ : syracuseStep 18965603 = 28448405) B28448405
theorem B5325965 : Blo 1576486 5325965 := bstep (se 3 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 5325965 = 1997237) B1997237
theorem B2663617 : Blo 1576486 2663617 := bstep (se 2 (by rfl) ⟨998856, by rfl⟩ : syracuseStep 2663617 = 1997713) B1997713
theorem B5326019 : Blo 1576486 5326019 := bstep (se 1 (by rfl) ⟨3994514, by rfl⟩ : syracuseStep 5326019 = 7989029) B7989029
theorem B11977955 : Blo 1576486 11977955 := bstep (se 1 (by rfl) ⟨8983466, by rfl⟩ : syracuseStep 11977955 = 17966933) B17966933
theorem B2663651 : Blo 1576486 2663651 := bstep (se 1 (by rfl) ⟨1997738, by rfl⟩ : syracuseStep 2663651 = 3995477) B3995477
theorem B13468913 : Blo 1576486 13468913 := bstep (se 2 (by rfl) ⟨5050842, by rfl⟩ : syracuseStep 13468913 = 10101685) B10101685
theorem B20210957 : Blo 1576486 20210957 := bstep (se 3 (by rfl) ⟨3789554, by rfl⟩ : syracuseStep 20210957 = 7579109) B7579109
theorem B2245907 : Blo 1576486 2245907 := bstep (se 1 (by rfl) ⟨1684430, by rfl⟩ : syracuseStep 2245907 = 3368861) B3368861
theorem B3548465 : Blo 1576486 3548465 := bstep (se 2 (by rfl) ⟨1330674, by rfl⟩ : syracuseStep 3548465 = 2661349) B2661349
theorem B3548483 : Blo 1576486 3548483 := bstep (se 1 (by rfl) ⟨2661362, by rfl⟩ : syracuseStep 3548483 = 5322725) B5322725
theorem B5326289 : Blo 1576486 5326289 := bstep (se 2 (by rfl) ⟨1997358, by rfl⟩ : syracuseStep 5326289 = 3994717) B3994717
theorem B5989859 : Blo 1576486 5989859 := bstep (se 1 (by rfl) ⟨4492394, by rfl⟩ : syracuseStep 5989859 = 8984789) B8984789
theorem B3548753 : Blo 1576486 3548753 := bstep (se 2 (by rfl) ⟨1330782, by rfl⟩ : syracuseStep 3548753 = 2661565) B2661565
theorem B3548771 : Blo 1576486 3548771 := bstep (se 1 (by rfl) ⟨2661578, by rfl⟩ : syracuseStep 3548771 = 5323157) B5323157
theorem B3991153 : Blo 1576486 3991153 := bstep (se 2 (by rfl) ⟨1496682, by rfl⟩ : syracuseStep 3991153 = 2993365) B2993365
theorem B2696819 : Blo 1576486 2696819 := bstep (se 1 (by rfl) ⟨2022614, by rfl⟩ : syracuseStep 2696819 = 4045229) B4045229
theorem B4491085 : Blo 1576486 4491085 := bstep (se 3 (by rfl) ⟨842078, by rfl⟩ : syracuseStep 4491085 = 1684157) B1684157
theorem B3549041 : Blo 1576486 3549041 := bstep (se 2 (by rfl) ⟨1330890, by rfl⟩ : syracuseStep 3549041 = 2661781) B2661781
theorem B3991427 : Blo 1576486 3991427 := bstep (se 1 (by rfl) ⟨2993570, by rfl⟩ : syracuseStep 3991427 = 5987141) B5987141
theorem B3549059 : Blo 1576486 3549059 := bstep (se 1 (by rfl) ⟨2661794, by rfl⟩ : syracuseStep 3549059 = 5323589) B5323589
theorem B5121937 : Blo 1576486 5121937 := bstep (se 2 (by rfl) ⟨1920726, by rfl⟩ : syracuseStep 5121937 = 3841453) B3841453
theorem B2246545 : Blo 1576486 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B5326829 : Blo 1576486 5326829 := bstep (se 3 (by rfl) ⟨998780, by rfl⟩ : syracuseStep 5326829 = 1997561) B1997561
theorem B7981091 : Blo 1576486 7981091 := bstep (se 1 (by rfl) ⟨5985818, by rfl⟩ : syracuseStep 7981091 = 11971637) B11971637
theorem B5326883 : Blo 1576486 5326883 := bstep (se 1 (by rfl) ⟨3995162, by rfl⟩ : syracuseStep 5326883 = 7990325) B7990325
theorem B3991619 : Blo 1576486 3991619 := bstep (se 1 (by rfl) ⟨2993714, by rfl⟩ : syracuseStep 3991619 = 5987429) B5987429
theorem B3197009 : Blo 1576486 3197009 := bstep (se 2 (by rfl) ⟨1198878, by rfl⟩ : syracuseStep 3197009 = 2397757) B2397757
theorem B4261997 : Blo 1576486 4261997 := bstep (se 3 (by rfl) ⟨799124, by rfl⟩ : syracuseStep 4261997 = 1598249) B1598249
theorem B1599619 : Blo 1576486 1599619 := bstep (se 1 (by rfl) ⟨1199714, by rfl⟩ : syracuseStep 1599619 = 2399429) B2399429
theorem B3549329 : Blo 1576486 3549329 := bstep (se 2 (by rfl) ⟨1330998, by rfl⟩ : syracuseStep 3549329 = 2661997) B2661997
theorem B1894547 : Blo 1576486 1894547 := bstep (se 1 (by rfl) ⟨1420910, by rfl⟩ : syracuseStep 1894547 = 2841821) B2841821
theorem B2525345 : Blo 1576486 2525345 := bstep (se 2 (by rfl) ⟨947004, by rfl⟩ : syracuseStep 2525345 = 1894009) B1894009
theorem B3549347 : Blo 1576486 3549347 := bstep (se 1 (by rfl) ⟨2662010, by rfl⟩ : syracuseStep 3549347 = 5324021) B5324021
theorem B28772549 : Blo 1576486 28772549 := bstep (se 4 (by rfl) ⟨2697426, by rfl⟩ : syracuseStep 28772549 = 5394853) B5394853
theorem B2246881 : Blo 1576486 2246881 := bstep (se 2 (by rfl) ⟨842580, by rfl⟩ : syracuseStep 2246881 = 1685161) B1685161
theorem B5056739 : Blo 1576486 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B10799345 : Blo 1576486 10799345 := bstep (se 2 (by rfl) ⟨4049754, by rfl⟩ : syracuseStep 10799345 = 8099509) B8099509
theorem B5327153 : Blo 1576486 5327153 := bstep (se 2 (by rfl) ⟨1997682, by rfl⟩ : syracuseStep 5327153 = 3995365) B3995365
theorem B2525537 : Blo 1576486 2525537 := bstep (se 2 (by rfl) ⟨947076, by rfl⟩ : syracuseStep 2525537 = 1894153) B1894153
theorem B3549617 : Blo 1576486 3549617 := bstep (se 2 (by rfl) ⟨1331106, by rfl⟩ : syracuseStep 3549617 = 2662213) B2662213
theorem B3549635 : Blo 1576486 3549635 := bstep (se 1 (by rfl) ⟨2662226, by rfl⟩ : syracuseStep 3549635 = 5324453) B5324453
theorem B5990861 : Blo 1576486 5990861 := bstep (se 3 (by rfl) ⟨1123286, by rfl⟩ : syracuseStep 5990861 = 2246573) B2246573
theorem B6736355 : Blo 1576486 6736355 := bstep (se 1 (by rfl) ⟨5052266, by rfl⟩ : syracuseStep 6736355 = 10104533) B10104533
theorem B2697715 : Blo 1576486 2697715 := bstep (se 1 (by rfl) ⟨2023286, by rfl⟩ : syracuseStep 2697715 = 4046573) B4046573
theorem B1895027 : Blo 1576486 1895027 := bstep (se 1 (by rfl) ⟨1421270, by rfl⟩ : syracuseStep 1895027 = 2842541) B2842541
theorem B8981189 : Blo 1576486 8981189 := bstep (se 4 (by rfl) ⟨841986, by rfl⟩ : syracuseStep 8981189 = 1683973) B1683973
theorem B3549905 : Blo 1576486 3549905 := bstep (se 2 (by rfl) ⟨1331214, by rfl⟩ : syracuseStep 3549905 = 2662429) B2662429
theorem B3549923 : Blo 1576486 3549923 := bstep (se 1 (by rfl) ⟨2662442, by rfl⟩ : syracuseStep 3549923 = 5324885) B5324885
theorem B7990001 : Blo 1576486 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B2247473 : Blo 1576486 2247473 := bstep (se 2 (by rfl) ⟨842802, by rfl⟩ : syracuseStep 2247473 = 1685605) B1685605
theorem B2992963 : Blo 1576486 2992963 := bstep (se 1 (by rfl) ⟨2244722, by rfl⟩ : syracuseStep 2992963 = 4489445) B4489445
theorem B7981901 : Blo 1576486 7981901 := bstep (se 3 (by rfl) ⟨1496606, by rfl⟩ : syracuseStep 7981901 = 2993213) B2993213
theorem B4262797 : Blo 1576486 4262797 := bstep (se 3 (by rfl) ⟨799274, by rfl⟩ : syracuseStep 4262797 = 1598549) B1598549
theorem B3992561 : Blo 1576486 3992561 := bstep (se 2 (by rfl) ⟨1497210, by rfl⟩ : syracuseStep 3992561 = 2994421) B2994421
theorem B3550193 : Blo 1576486 3550193 := bstep (se 2 (by rfl) ⟨1331322, by rfl⟩ : syracuseStep 3550193 = 2662645) B2662645
theorem B3550211 : Blo 1576486 3550211 := bstep (se 1 (by rfl) ⟨2662658, by rfl⟩ : syracuseStep 3550211 = 5325317) B5325317
theorem B3992611 : Blo 1576486 3992611 := bstep (se 1 (by rfl) ⟨2994458, by rfl⟩ : syracuseStep 3992611 = 5988917) B5988917
theorem B17280053 : Blo 1576486 17280053 := bstep (se 5 (by rfl) ⟨810002, by rfl⟩ : syracuseStep 17280053 = 1620005) B1620005
theorem B3697777 : Blo 1576486 3697777 := bstep (se 2 (by rfl) ⟨1386666, by rfl⟩ : syracuseStep 3697777 = 2773333) B2773333
theorem B10112141 : Blo 1576486 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B3992753 : Blo 1576486 3992753 := bstep (se 2 (by rfl) ⟨1497282, by rfl⟩ : syracuseStep 3992753 = 2994565) B2994565
theorem B8989937 : Blo 1576486 8989937 := bstep (se 2 (by rfl) ⟨3371226, by rfl⟩ : syracuseStep 8989937 = 6742453) B6742453
theorem B2993411 : Blo 1576486 2993411 := bstep (se 1 (by rfl) ⟨2245058, by rfl⟩ : syracuseStep 2993411 = 4490117) B4490117
theorem B3550481 : Blo 1576486 3550481 := bstep (se 2 (by rfl) ⟨1331430, by rfl⟩ : syracuseStep 3550481 = 2662861) B2662861
theorem B3550499 : Blo 1576486 3550499 := bstep (se 1 (by rfl) ⟨2662874, by rfl⟩ : syracuseStep 3550499 = 5325749) B5325749
theorem B6073649 : Blo 1576486 6073649 := bstep (se 2 (by rfl) ⟨2277618, by rfl⟩ : syracuseStep 6073649 = 4555237) B4555237
theorem B8981873 : Blo 1576486 8981873 := bstep (se 2 (by rfl) ⟨3368202, by rfl⟩ : syracuseStep 8981873 = 6736405) B6736405
theorem B3788209 : Blo 1576486 3788209 := bstep (se 2 (by rfl) ⟨1420578, by rfl⟩ : syracuseStep 3788209 = 2841157) B2841157
theorem B2772433 : Blo 1576486 2772433 := bstep (se 2 (by rfl) ⟨1039662, by rfl⟩ : syracuseStep 2772433 = 2079325) B2079325
theorem B4492817 : Blo 1576486 4492817 := bstep (se 2 (by rfl) ⟨1684806, by rfl⟩ : syracuseStep 4492817 = 3369613) B3369613
theorem B2993699 : Blo 1576486 2993699 := bstep (se 1 (by rfl) ⟨2245274, by rfl⟩ : syracuseStep 2993699 = 4490549) B4490549
theorem B3550769 : Blo 1576486 3550769 := bstep (se 2 (by rfl) ⟨1331538, by rfl⟩ : syracuseStep 3550769 = 2663077) B2663077
theorem B1576499 : Blo 1576486 1576499 := bstep (se 1 (by rfl) ⟨1182374, by rfl⟩ : syracuseStep 1576499 = 2364749) B2364749
theorem B1576515 : Blo 1576486 1576515 := bstep (se 1 (by rfl) ⟨1182386, by rfl⟩ : syracuseStep 1576515 = 2364773) B2364773
theorem B3550787 : Blo 1576486 3550787 := bstep (se 1 (by rfl) ⟨2663090, by rfl⟩ : syracuseStep 3550787 = 5326181) B5326181
theorem B3370577 : Blo 1576486 3370577 := bstep (se 2 (by rfl) ⟨1263966, by rfl⟩ : syracuseStep 3370577 = 2527933) B2527933
theorem B1576531 : Blo 1576486 1576531 := bstep (se 1 (by rfl) ⟨1182398, by rfl⟩ : syracuseStep 1576531 = 2364797) B2364797
theorem B1576547 : Blo 1576486 1576547 := bstep (se 1 (by rfl) ⟨1182410, by rfl⟩ : syracuseStep 1576547 = 2364821) B2364821
theorem B13143665 : Blo 1576486 13143665 := bstep (se 2 (by rfl) ⟨4928874, by rfl⟩ : syracuseStep 13143665 = 9857749) B9857749
theorem B1576563 : Blo 1576486 1576563 := bstep (se 1 (by rfl) ⟨1182422, by rfl⟩ : syracuseStep 1576563 = 2364845) B2364845
theorem B1576579 : Blo 1576486 1576579 := bstep (se 1 (by rfl) ⟨1182434, by rfl⟩ : syracuseStep 1576579 = 2364869) B2364869
theorem B2526851 : Blo 1576486 2526851 := bstep (se 1 (by rfl) ⟨1895138, by rfl⟩ : syracuseStep 2526851 = 3790277) B3790277
theorem B13471373 : Blo 1576486 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B1576595 : Blo 1576486 1576595 := bstep (se 1 (by rfl) ⟨1182446, by rfl⟩ : syracuseStep 1576595 = 2364893) B2364893
theorem B1576611 : Blo 1576486 1576611 := bstep (se 1 (by rfl) ⟨1182458, by rfl⟩ : syracuseStep 1576611 = 2364917) B2364917
theorem B1576627 : Blo 1576486 1576627 := bstep (se 1 (by rfl) ⟨1182470, by rfl⟩ : syracuseStep 1576627 = 2364941) B2364941
theorem B1576643 : Blo 1576486 1576643 := bstep (se 1 (by rfl) ⟨1182482, by rfl⟩ : syracuseStep 1576643 = 2364965) B2364965
theorem B5762765 : Blo 1576486 5762765 := bstep (se 3 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 5762765 = 2161037) B2161037
theorem B4493009 : Blo 1576486 4493009 := bstep (se 2 (by rfl) ⟨1684878, by rfl⟩ : syracuseStep 4493009 = 3369757) B3369757
theorem B1576659 : Blo 1576486 1576659 := bstep (se 1 (by rfl) ⟨1182494, by rfl⟩ : syracuseStep 1576659 = 2364989) B2364989
theorem B1576675 : Blo 1576486 1576675 := bstep (se 1 (by rfl) ⟨1182506, by rfl⟩ : syracuseStep 1576675 = 2365013) B2365013
theorem B61484771 : Blo 1576486 61484771 := bstep (se 1 (by rfl) ⟨46113578, by rfl⟩ : syracuseStep 61484771 = 92227157) B92227157
theorem B1576691 : Blo 1576486 1576691 := bstep (se 1 (by rfl) ⟨1182518, by rfl⟩ : syracuseStep 1576691 = 2365037) B2365037
theorem B1576707 : Blo 1576486 1576707 := bstep (se 1 (by rfl) ⟨1182530, by rfl⟩ : syracuseStep 1576707 = 2365061) B2365061
theorem B1576723 : Blo 1576486 1576723 := bstep (se 1 (by rfl) ⟨1182542, by rfl⟩ : syracuseStep 1576723 = 2365085) B2365085
theorem B1576739 : Blo 1576486 1576739 := bstep (se 1 (by rfl) ⟨1182554, by rfl⟩ : syracuseStep 1576739 = 2365109) B2365109
theorem B4263725 : Blo 1576486 4263725 := bstep (se 3 (by rfl) ⟨799448, by rfl⟩ : syracuseStep 4263725 = 1598897) B1598897
theorem B1576755 : Blo 1576486 1576755 := bstep (se 1 (by rfl) ⟨1182566, by rfl⟩ : syracuseStep 1576755 = 2365133) B2365133
theorem B1576771 : Blo 1576486 1576771 := bstep (se 1 (by rfl) ⟨1182578, by rfl⟩ : syracuseStep 1576771 = 2365157) B2365157
theorem B3551057 : Blo 1576486 3551057 := bstep (se 2 (by rfl) ⟨1331646, by rfl⟩ : syracuseStep 3551057 = 2663293) B2663293
theorem B1576787 : Blo 1576486 1576787 := bstep (se 1 (by rfl) ⟨1182590, by rfl⟩ : syracuseStep 1576787 = 2365181) B2365181
theorem B1576803 : Blo 1576486 1576803 := bstep (se 1 (by rfl) ⟨1182602, by rfl⟩ : syracuseStep 1576803 = 2365205) B2365205
theorem B11366243 : Blo 1576486 11366243 := bstep (se 1 (by rfl) ⟨8524682, by rfl⟩ : syracuseStep 11366243 = 17049365) B17049365
theorem B2527075 : Blo 1576486 2527075 := bstep (se 1 (by rfl) ⟨1895306, by rfl⟩ : syracuseStep 2527075 = 3790613) B3790613
theorem B3551075 : Blo 1576486 3551075 := bstep (se 1 (by rfl) ⟨2663306, by rfl⟩ : syracuseStep 3551075 = 5326613) B5326613
theorem B1576819 : Blo 1576486 1576819 := bstep (se 1 (by rfl) ⟨1182614, by rfl⟩ : syracuseStep 1576819 = 2365229) B2365229
theorem B1576835 : Blo 1576486 1576835 := bstep (se 1 (by rfl) ⟨1182626, by rfl⟩ : syracuseStep 1576835 = 2365253) B2365253
theorem B1576851 : Blo 1576486 1576851 := bstep (se 1 (by rfl) ⟨1182638, by rfl⟩ : syracuseStep 1576851 = 2365277) B2365277
theorem B1576867 : Blo 1576486 1576867 := bstep (se 1 (by rfl) ⟨1182650, by rfl⟩ : syracuseStep 1576867 = 2365301) B2365301
theorem B2527139 : Blo 1576486 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B1576883 : Blo 1576486 1576883 := bstep (se 1 (by rfl) ⟨1182662, by rfl⟩ : syracuseStep 1576883 = 2365325) B2365325
theorem B1576899 : Blo 1576486 1576899 := bstep (se 1 (by rfl) ⟨1182674, by rfl⟩ : syracuseStep 1576899 = 2365349) B2365349
theorem B1576915 : Blo 1576486 1576915 := bstep (se 1 (by rfl) ⟨1182686, by rfl⟩ : syracuseStep 1576915 = 2365373) B2365373
theorem B1576931 : Blo 1576486 1576931 := bstep (se 1 (by rfl) ⟨1182698, by rfl⟩ : syracuseStep 1576931 = 2365397) B2365397
theorem B1576947 : Blo 1576486 1576947 := bstep (se 1 (by rfl) ⟨1182710, by rfl⟩ : syracuseStep 1576947 = 2365421) B2365421
theorem B1773571 : Blo 1576486 1773571 := bstep (se 1 (by rfl) ⟨1330178, by rfl⟩ : syracuseStep 1773571 = 2660357) B2660357
theorem B1576963 : Blo 1576486 1576963 := bstep (se 1 (by rfl) ⟨1182722, by rfl⟩ : syracuseStep 1576963 = 2365445) B2365445
theorem B1576979 : Blo 1576486 1576979 := bstep (se 1 (by rfl) ⟨1182734, by rfl⟩ : syracuseStep 1576979 = 2365469) B2365469
theorem B2560033 : Blo 1576486 2560033 := bstep (se 2 (by rfl) ⟨960012, by rfl⟩ : syracuseStep 2560033 = 1920025) B1920025
theorem B1576995 : Blo 1576486 1576995 := bstep (se 1 (by rfl) ⟨1182746, by rfl⟩ : syracuseStep 1576995 = 2365493) B2365493
theorem B2527267 : Blo 1576486 2527267 := bstep (se 1 (by rfl) ⟨1895450, by rfl⟩ : syracuseStep 2527267 = 3790901) B3790901
theorem B1577011 : Blo 1576486 1577011 := bstep (se 1 (by rfl) ⟨1182758, by rfl⟩ : syracuseStep 1577011 = 2365517) B2365517
theorem B1577027 : Blo 1576486 1577027 := bstep (se 1 (by rfl) ⟨1182770, by rfl⟩ : syracuseStep 1577027 = 2365541) B2365541
theorem B5320781 : Blo 1576486 5320781 := bstep (se 3 (by rfl) ⟨997646, by rfl⟩ : syracuseStep 5320781 = 1995293) B1995293
theorem B2560081 : Blo 1576486 2560081 := bstep (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) B1920061
theorem B1577043 : Blo 1576486 1577043 := bstep (se 1 (by rfl) ⟨1182782, by rfl⟩ : syracuseStep 1577043 = 2365565) B2365565
theorem B1577059 : Blo 1576486 1577059 := bstep (se 1 (by rfl) ⟨1182794, by rfl⟩ : syracuseStep 1577059 = 2365589) B2365589
theorem B3551345 : Blo 1576486 3551345 := bstep (se 2 (by rfl) ⟨1331754, by rfl⟩ : syracuseStep 3551345 = 2663509) B2663509
theorem B1577075 : Blo 1576486 1577075 := bstep (se 1 (by rfl) ⟨1182806, by rfl⟩ : syracuseStep 1577075 = 2365613) B2365613
theorem B5320835 : Blo 1576486 5320835 := bstep (se 1 (by rfl) ⟨3990626, by rfl⟩ : syracuseStep 5320835 = 7981253) B7981253
theorem B1577091 : Blo 1576486 1577091 := bstep (se 1 (by rfl) ⟨1182818, by rfl⟩ : syracuseStep 1577091 = 2365637) B2365637
theorem B3551363 : Blo 1576486 3551363 := bstep (se 1 (by rfl) ⟨2663522, by rfl⟩ : syracuseStep 3551363 = 5327045) B5327045
theorem B17961101 : Blo 1576486 17961101 := bstep (se 3 (by rfl) ⟨3367706, by rfl⟩ : syracuseStep 17961101 = 6735413) B6735413
theorem B3993745 : Blo 1576486 3993745 := bstep (se 2 (by rfl) ⟨1497654, by rfl⟩ : syracuseStep 3993745 = 2995309) B2995309
theorem B1773715 : Blo 1576486 1773715 := bstep (se 1 (by rfl) ⟨1330286, by rfl⟩ : syracuseStep 1773715 = 2660573) B2660573
theorem B1577107 : Blo 1576486 1577107 := bstep (se 1 (by rfl) ⟨1182830, by rfl⟩ : syracuseStep 1577107 = 2365661) B2365661
theorem B1577123 : Blo 1576486 1577123 := bstep (se 1 (by rfl) ⟨1182842, by rfl⟩ : syracuseStep 1577123 = 2365685) B2365685
theorem B1577139 : Blo 1576486 1577139 := bstep (se 1 (by rfl) ⟨1182854, by rfl⟩ : syracuseStep 1577139 = 2365709) B2365709
theorem B1577155 : Blo 1576486 1577155 := bstep (se 1 (by rfl) ⟨1182866, by rfl⟩ : syracuseStep 1577155 = 2365733) B2365733
theorem B25596101 : Blo 1576486 25596101 := bstep (se 4 (by rfl) ⟨2399634, by rfl⟩ : syracuseStep 25596101 = 4799269) B4799269
theorem B1577171 : Blo 1576486 1577171 := bstep (se 1 (by rfl) ⟨1182878, by rfl⟩ : syracuseStep 1577171 = 2365757) B2365757
theorem B1577187 : Blo 1576486 1577187 := bstep (se 1 (by rfl) ⟨1182890, by rfl⟩ : syracuseStep 1577187 = 2365781) B2365781
theorem B1577203 : Blo 1576486 1577203 := bstep (se 1 (by rfl) ⟨1182902, by rfl⟩ : syracuseStep 1577203 = 2365805) B2365805
theorem B1577219 : Blo 1576486 1577219 := bstep (se 1 (by rfl) ⟨1182914, by rfl⟩ : syracuseStep 1577219 = 2365829) B2365829
theorem B1577235 : Blo 1576486 1577235 := bstep (se 1 (by rfl) ⟨1182926, by rfl⟩ : syracuseStep 1577235 = 2365853) B2365853
theorem B1773859 : Blo 1576486 1773859 := bstep (se 1 (by rfl) ⟨1330394, by rfl⟩ : syracuseStep 1773859 = 2660789) B2660789
theorem B1577251 : Blo 1576486 1577251 := bstep (se 1 (by rfl) ⟨1182938, by rfl⟩ : syracuseStep 1577251 = 2365877) B2365877
theorem B1577267 : Blo 1576486 1577267 := bstep (se 1 (by rfl) ⟨1182950, by rfl⟩ : syracuseStep 1577267 = 2365901) B2365901
theorem B1577283 : Blo 1576486 1577283 := bstep (se 1 (by rfl) ⟨1182962, by rfl⟩ : syracuseStep 1577283 = 2365925) B2365925
theorem B1577299 : Blo 1576486 1577299 := bstep (se 1 (by rfl) ⟨1182974, by rfl⟩ : syracuseStep 1577299 = 2365949) B2365949
theorem B1577315 : Blo 1576486 1577315 := bstep (se 1 (by rfl) ⟨1182986, by rfl⟩ : syracuseStep 1577315 = 2365973) B2365973
theorem B1577331 : Blo 1576486 1577331 := bstep (se 1 (by rfl) ⟨1182998, by rfl⟩ : syracuseStep 1577331 = 2365997) B2365997
theorem B1577347 : Blo 1576486 1577347 := bstep (se 1 (by rfl) ⟨1183010, by rfl⟩ : syracuseStep 1577347 = 2366021) B2366021
theorem B5321105 : Blo 1576486 5321105 := bstep (se 2 (by rfl) ⟨1995414, by rfl⟩ : syracuseStep 5321105 = 3990829) B3990829
theorem B1577363 : Blo 1576486 1577363 := bstep (se 1 (by rfl) ⟨1183022, by rfl⟩ : syracuseStep 1577363 = 2366045) B2366045
theorem B1577379 : Blo 1576486 1577379 := bstep (se 1 (by rfl) ⟨1183034, by rfl⟩ : syracuseStep 1577379 = 2366069) B2366069
theorem B3994019 : Blo 1576486 3994019 := bstep (se 1 (by rfl) ⟨2995514, by rfl⟩ : syracuseStep 3994019 = 5991029) B5991029
theorem B6738353 : Blo 1576486 6738353 := bstep (se 2 (by rfl) ⟨2526882, by rfl⟩ : syracuseStep 6738353 = 5053765) B5053765
theorem B1774003 : Blo 1576486 1774003 := bstep (se 1 (by rfl) ⟨1330502, by rfl⟩ : syracuseStep 1774003 = 2661005) B2661005
theorem B1577395 : Blo 1576486 1577395 := bstep (se 1 (by rfl) ⟨1183046, by rfl⟩ : syracuseStep 1577395 = 2366093) B2366093
theorem B1577411 : Blo 1576486 1577411 := bstep (se 1 (by rfl) ⟨1183058, by rfl⟩ : syracuseStep 1577411 = 2366117) B2366117
theorem B2994641 : Blo 1576486 2994641 := bstep (se 2 (by rfl) ⟨1122990, by rfl⟩ : syracuseStep 2994641 = 2245981) B2245981
theorem B1577427 : Blo 1576486 1577427 := bstep (se 1 (by rfl) ⟨1183070, by rfl⟩ : syracuseStep 1577427 = 2366141) B2366141
theorem B1577443 : Blo 1576486 1577443 := bstep (se 1 (by rfl) ⟨1183082, by rfl⟩ : syracuseStep 1577443 = 2366165) B2366165
theorem B1577459 : Blo 1576486 1577459 := bstep (se 1 (by rfl) ⟨1183094, by rfl⟩ : syracuseStep 1577459 = 2366189) B2366189
theorem B1577475 : Blo 1576486 1577475 := bstep (se 1 (by rfl) ⟨1183106, by rfl⟩ : syracuseStep 1577475 = 2366213) B2366213
theorem B5992973 : Blo 1576486 5992973 := bstep (se 3 (by rfl) ⟨1123682, by rfl⟩ : syracuseStep 5992973 = 2247365) B2247365
theorem B1995283 : Blo 1576486 1995283 := bstep (se 1 (by rfl) ⟨1496462, by rfl⟩ : syracuseStep 1995283 = 2992925) B2992925
theorem B1577491 : Blo 1576486 1577491 := bstep (se 1 (by rfl) ⟨1183118, by rfl⟩ : syracuseStep 1577491 = 2366237) B2366237
theorem B2699795 : Blo 1576486 2699795 := bstep (se 1 (by rfl) ⟨2024846, by rfl⟩ : syracuseStep 2699795 = 4049693) B4049693
theorem B1577507 : Blo 1576486 1577507 := bstep (se 1 (by rfl) ⟨1183130, by rfl⟩ : syracuseStep 1577507 = 2366261) B2366261
theorem B1577523 : Blo 1576486 1577523 := bstep (se 1 (by rfl) ⟨1183142, by rfl⟩ : syracuseStep 1577523 = 2366285) B2366285
theorem B1774147 : Blo 1576486 1774147 := bstep (se 1 (by rfl) ⟨1330610, by rfl⟩ : syracuseStep 1774147 = 2661221) B2661221
theorem B1577539 : Blo 1576486 1577539 := bstep (se 1 (by rfl) ⟨1183154, by rfl⟩ : syracuseStep 1577539 = 2366309) B2366309
theorem B1577555 : Blo 1576486 1577555 := bstep (se 1 (by rfl) ⟨1183166, by rfl⟩ : syracuseStep 1577555 = 2366333) B2366333
theorem B1577571 : Blo 1576486 1577571 := bstep (se 1 (by rfl) ⟨1183178, by rfl⟩ : syracuseStep 1577571 = 2366357) B2366357
theorem B3994211 : Blo 1576486 3994211 := bstep (se 1 (by rfl) ⟨2995658, by rfl⟩ : syracuseStep 3994211 = 5991317) B5991317
theorem B1577587 : Blo 1576486 1577587 := bstep (se 1 (by rfl) ⟨1183190, by rfl⟩ : syracuseStep 1577587 = 2366381) B2366381
theorem B1577603 : Blo 1576486 1577603 := bstep (se 1 (by rfl) ⟨1183202, by rfl⟩ : syracuseStep 1577603 = 2366405) B2366405
theorem B23368333 : Blo 1576486 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B1577619 : Blo 1576486 1577619 := bstep (se 1 (by rfl) ⟨1183214, by rfl⟩ : syracuseStep 1577619 = 2366429) B2366429
theorem B1577635 : Blo 1576486 1577635 := bstep (se 1 (by rfl) ⟨1183226, by rfl⟩ : syracuseStep 1577635 = 2366453) B2366453
theorem B4494001 : Blo 1576486 4494001 := bstep (se 2 (by rfl) ⟨1685250, by rfl⟩ : syracuseStep 4494001 = 3370501) B3370501
theorem B1577651 : Blo 1576486 1577651 := bstep (se 1 (by rfl) ⟨1183238, by rfl⟩ : syracuseStep 1577651 = 2366477) B2366477
theorem B1577667 : Blo 1576486 1577667 := bstep (se 1 (by rfl) ⟨1183250, by rfl⟩ : syracuseStep 1577667 = 2366501) B2366501
theorem B1774291 : Blo 1576486 1774291 := bstep (se 1 (by rfl) ⟨1330718, by rfl⟩ : syracuseStep 1774291 = 2661437) B2661437
theorem B1577683 : Blo 1576486 1577683 := bstep (se 1 (by rfl) ⟨1183262, by rfl⟩ : syracuseStep 1577683 = 2366525) B2366525
theorem B32371427 : Blo 1576486 32371427 := bstep (se 1 (by rfl) ⟨24278570, by rfl⟩ : syracuseStep 32371427 = 48557141) B48557141
theorem B1684195 : Blo 1576486 1684195 := bstep (se 1 (by rfl) ⟨1263146, by rfl⟩ : syracuseStep 1684195 = 2526293) B2526293
theorem B1577699 : Blo 1576486 1577699 := bstep (se 1 (by rfl) ⟨1183274, by rfl⟩ : syracuseStep 1577699 = 2366549) B2366549
theorem B2527985 : Blo 1576486 2527985 := bstep (se 2 (by rfl) ⟨947994, by rfl⟩ : syracuseStep 2527985 = 1895989) B1895989
theorem B1577715 : Blo 1576486 1577715 := bstep (se 1 (by rfl) ⟨1183286, by rfl⟩ : syracuseStep 1577715 = 2366573) B2366573
theorem B1577731 : Blo 1576486 1577731 := bstep (se 1 (by rfl) ⟨1183298, by rfl⟩ : syracuseStep 1577731 = 2366597) B2366597
theorem B1577747 : Blo 1576486 1577747 := bstep (se 1 (by rfl) ⟨1183310, by rfl⟩ : syracuseStep 1577747 = 2366621) B2366621
theorem B8983331 : Blo 1576486 8983331 := bstep (se 1 (by rfl) ⟨6737498, by rfl⟩ : syracuseStep 8983331 = 13474997) B13474997
theorem B1577763 : Blo 1576486 1577763 := bstep (se 1 (by rfl) ⟨1183322, by rfl⟩ : syracuseStep 1577763 = 2366645) B2366645
theorem B4264753 : Blo 1576486 4264753 := bstep (se 2 (by rfl) ⟨1599282, by rfl⟩ : syracuseStep 4264753 = 3198565) B3198565
theorem B1577779 : Blo 1576486 1577779 := bstep (se 1 (by rfl) ⟨1183334, by rfl⟩ : syracuseStep 1577779 = 2366669) B2366669
theorem B1577795 : Blo 1576486 1577795 := bstep (se 1 (by rfl) ⟨1183346, by rfl⟩ : syracuseStep 1577795 = 2366693) B2366693
theorem B4797265 : Blo 1576486 4797265 := bstep (se 2 (by rfl) ⟨1798974, by rfl⟩ : syracuseStep 4797265 = 3597949) B3597949
theorem B1577811 : Blo 1576486 1577811 := bstep (se 1 (by rfl) ⟨1183358, by rfl⟩ : syracuseStep 1577811 = 2366717) B2366717
theorem B1774435 : Blo 1576486 1774435 := bstep (se 1 (by rfl) ⟨1330826, by rfl⟩ : syracuseStep 1774435 = 2661653) B2661653
theorem B1577827 : Blo 1576486 1577827 := bstep (se 1 (by rfl) ⟨1183370, by rfl⟩ : syracuseStep 1577827 = 2366741) B2366741
theorem B2528113 : Blo 1576486 2528113 := bstep (se 2 (by rfl) ⟨948042, by rfl⟩ : syracuseStep 2528113 = 1896085) B1896085
theorem B1577843 : Blo 1576486 1577843 := bstep (se 1 (by rfl) ⟨1183382, by rfl⟩ : syracuseStep 1577843 = 2366765) B2366765
theorem B1577859 : Blo 1576486 1577859 := bstep (se 1 (by rfl) ⟨1183394, by rfl⟩ : syracuseStep 1577859 = 2366789) B2366789
theorem B1577875 : Blo 1576486 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B1577891 : Blo 1576486 1577891 := bstep (se 1 (by rfl) ⟨1183418, by rfl⟩ : syracuseStep 1577891 = 2366837) B2366837
theorem B5321645 : Blo 1576486 5321645 := bstep (se 3 (by rfl) ⟨997808, by rfl⟩ : syracuseStep 5321645 = 1995617) B1995617
theorem B1577907 : Blo 1576486 1577907 := bstep (se 1 (by rfl) ⟨1183430, by rfl⟩ : syracuseStep 1577907 = 2366861) B2366861
theorem B1577923 : Blo 1576486 1577923 := bstep (se 1 (by rfl) ⟨1183442, by rfl⟩ : syracuseStep 1577923 = 2366885) B2366885
theorem B4494275 : Blo 1576486 4494275 := bstep (se 1 (by rfl) ⟨3370706, by rfl⟩ : syracuseStep 4494275 = 6741413) B6741413
theorem B1577939 : Blo 1576486 1577939 := bstep (se 1 (by rfl) ⟨1183454, by rfl⟩ : syracuseStep 1577939 = 2366909) B2366909
theorem B5321699 : Blo 1576486 5321699 := bstep (se 1 (by rfl) ⟨3991274, by rfl⟩ : syracuseStep 5321699 = 7982549) B7982549
theorem B1577955 : Blo 1576486 1577955 := bstep (se 1 (by rfl) ⟨1183466, by rfl⟩ : syracuseStep 1577955 = 2366933) B2366933
theorem B1774579 : Blo 1576486 1774579 := bstep (se 1 (by rfl) ⟨1330934, by rfl⟩ : syracuseStep 1774579 = 2661869) B2661869
theorem B1577971 : Blo 1576486 1577971 := bstep (se 1 (by rfl) ⟨1183478, by rfl⟩ : syracuseStep 1577971 = 2366957) B2366957
theorem B1995779 : Blo 1576486 1995779 := bstep (se 1 (by rfl) ⟨1496834, by rfl⟩ : syracuseStep 1995779 = 2993669) B2993669
theorem B1577987 : Blo 1576486 1577987 := bstep (se 1 (by rfl) ⟨1183490, by rfl⟩ : syracuseStep 1577987 = 2366981) B2366981
theorem B1578003 : Blo 1576486 1578003 := bstep (se 1 (by rfl) ⟨1183502, by rfl⟩ : syracuseStep 1578003 = 2367005) B2367005
theorem B9851939 : Blo 1576486 9851939 := bstep (se 1 (by rfl) ⟨7388954, by rfl⟩ : syracuseStep 9851939 = 14777909) B14777909
theorem B1578019 : Blo 1576486 1578019 := bstep (se 1 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 1578019 = 2367029) B2367029
theorem B1578035 : Blo 1576486 1578035 := bstep (se 1 (by rfl) ⟨1183526, by rfl⟩ : syracuseStep 1578035 = 2367053) B2367053
theorem B1578051 : Blo 1576486 1578051 := bstep (se 1 (by rfl) ⟨1183538, by rfl⟩ : syracuseStep 1578051 = 2367077) B2367077
theorem B1578067 : Blo 1576486 1578067 := bstep (se 1 (by rfl) ⟨1183550, by rfl⟩ : syracuseStep 1578067 = 2367101) B2367101
theorem B8090723 : Blo 1576486 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B9589859 : Blo 1576486 9589859 := bstep (se 1 (by rfl) ⟨7192394, by rfl⟩ : syracuseStep 9589859 = 14384789) B14384789
theorem B1578083 : Blo 1576486 1578083 := bstep (se 1 (by rfl) ⟨1183562, by rfl⟩ : syracuseStep 1578083 = 2367125) B2367125
theorem B1578099 : Blo 1576486 1578099 := bstep (se 1 (by rfl) ⟨1183574, by rfl⟩ : syracuseStep 1578099 = 2367149) B2367149
theorem B1774723 : Blo 1576486 1774723 := bstep (se 1 (by rfl) ⟨1331042, by rfl⟩ : syracuseStep 1774723 = 2662085) B2662085
theorem B1578115 : Blo 1576486 1578115 := bstep (se 1 (by rfl) ⟨1183586, by rfl⟩ : syracuseStep 1578115 = 2367173) B2367173
theorem B4494467 : Blo 1576486 4494467 := bstep (se 1 (by rfl) ⟨3370850, by rfl⟩ : syracuseStep 4494467 = 6741701) B6741701
theorem B1578131 : Blo 1576486 1578131 := bstep (se 1 (by rfl) ⟨1183598, by rfl⟩ : syracuseStep 1578131 = 2367197) B2367197
theorem B1578147 : Blo 1576486 1578147 := bstep (se 1 (by rfl) ⟨1183610, by rfl⟩ : syracuseStep 1578147 = 2367221) B2367221
theorem B1578163 : Blo 1576486 1578163 := bstep (se 1 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 1578163 = 2367245) B2367245
theorem B1578179 : Blo 1576486 1578179 := bstep (se 1 (by rfl) ⟨1183634, by rfl⟩ : syracuseStep 1578179 = 2367269) B2367269
theorem B1578195 : Blo 1576486 1578195 := bstep (se 1 (by rfl) ⟨1183646, by rfl⟩ : syracuseStep 1578195 = 2367293) B2367293
theorem B1578211 : Blo 1576486 1578211 := bstep (se 1 (by rfl) ⟨1183658, by rfl⟩ : syracuseStep 1578211 = 2367317) B2367317
theorem B5321969 : Blo 1576486 5321969 := bstep (se 2 (by rfl) ⟨1995738, by rfl⟩ : syracuseStep 5321969 = 3991477) B3991477
theorem B1578227 : Blo 1576486 1578227 := bstep (se 1 (by rfl) ⟨1183670, by rfl⟩ : syracuseStep 1578227 = 2367341) B2367341
theorem B1578243 : Blo 1576486 1578243 := bstep (se 1 (by rfl) ⟨1183682, by rfl⟩ : syracuseStep 1578243 = 2367365) B2367365
theorem B4797713 : Blo 1576486 4797713 := bstep (se 2 (by rfl) ⟨1799142, by rfl⟩ : syracuseStep 4797713 = 3598285) B3598285
theorem B1774867 : Blo 1576486 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B1578259 : Blo 1576486 1578259 := bstep (se 1 (by rfl) ⟨1183694, by rfl⟩ : syracuseStep 1578259 = 2367389) B2367389
theorem B1578275 : Blo 1576486 1578275 := bstep (se 1 (by rfl) ⟨1183706, by rfl⟩ : syracuseStep 1578275 = 2367413) B2367413
theorem B1578291 : Blo 1576486 1578291 := bstep (se 1 (by rfl) ⟨1183718, by rfl⟩ : syracuseStep 1578291 = 2367437) B2367437
theorem B2364737 : Blo 1576486 2364737 := bstep (se 2 (by rfl) ⟨886776, by rfl⟩ : syracuseStep 2364737 = 1773553) B1773553
theorem B1578307 : Blo 1576486 1578307 := bstep (se 1 (by rfl) ⟨1183730, by rfl⟩ : syracuseStep 1578307 = 2367461) B2367461
theorem B2995537 : Blo 1576486 2995537 := bstep (se 2 (by rfl) ⟨1123326, by rfl⟩ : syracuseStep 2995537 = 2246653) B2246653
theorem B2364755 : Blo 1576486 2364755 := bstep (se 1 (by rfl) ⟨1773566, by rfl⟩ : syracuseStep 2364755 = 3547133) B3547133
theorem B1578323 : Blo 1576486 1578323 := bstep (se 1 (by rfl) ⟨1183742, by rfl⟩ : syracuseStep 1578323 = 2367485) B2367485
theorem B1578339 : Blo 1576486 1578339 := bstep (se 1 (by rfl) ⟨1183754, by rfl⟩ : syracuseStep 1578339 = 2367509) B2367509
theorem B2364785 : Blo 1576486 2364785 := bstep (se 2 (by rfl) ⟨886794, by rfl⟩ : syracuseStep 2364785 = 1773589) B1773589
theorem B1578355 : Blo 1576486 1578355 := bstep (se 1 (by rfl) ⟨1183766, by rfl⟩ : syracuseStep 1578355 = 2367533) B2367533
theorem B2364803 : Blo 1576486 2364803 := bstep (se 1 (by rfl) ⟨1773602, by rfl⟩ : syracuseStep 2364803 = 3547205) B3547205
theorem B1578371 : Blo 1576486 1578371 := bstep (se 1 (by rfl) ⟨1183778, by rfl⟩ : syracuseStep 1578371 = 2367557) B2367557
theorem B1578387 : Blo 1576486 1578387 := bstep (se 1 (by rfl) ⟨1183790, by rfl⟩ : syracuseStep 1578387 = 2367581) B2367581
theorem B2364833 : Blo 1576486 2364833 := bstep (se 2 (by rfl) ⟨886812, by rfl⟩ : syracuseStep 2364833 = 1773625) B1773625
theorem B1775011 : Blo 1576486 1775011 := bstep (se 1 (by rfl) ⟨1331258, by rfl⟩ : syracuseStep 1775011 = 2662517) B2662517
theorem B1578403 : Blo 1576486 1578403 := bstep (se 1 (by rfl) ⟨1183802, by rfl⟩ : syracuseStep 1578403 = 2367605) B2367605
theorem B2364851 : Blo 1576486 2364851 := bstep (se 1 (by rfl) ⟨1773638, by rfl⟩ : syracuseStep 2364851 = 3547277) B3547277
theorem B1578419 : Blo 1576486 1578419 := bstep (se 1 (by rfl) ⟨1183814, by rfl⟩ : syracuseStep 1578419 = 2367629) B2367629
theorem B1578435 : Blo 1576486 1578435 := bstep (se 1 (by rfl) ⟨1183826, by rfl⟩ : syracuseStep 1578435 = 2367653) B2367653
theorem B2364881 : Blo 1576486 2364881 := bstep (se 2 (by rfl) ⟨886830, by rfl⟩ : syracuseStep 2364881 = 1773661) B1773661
theorem B1578451 : Blo 1576486 1578451 := bstep (se 1 (by rfl) ⟨1183838, by rfl⟩ : syracuseStep 1578451 = 2367677) B2367677
theorem B2364899 : Blo 1576486 2364899 := bstep (se 1 (by rfl) ⟨1773674, by rfl⟩ : syracuseStep 2364899 = 3547349) B3547349
theorem B1578467 : Blo 1576486 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B2995697 : Blo 1576486 2995697 := bstep (se 2 (by rfl) ⟨1123386, by rfl⟩ : syracuseStep 2995697 = 2246773) B2246773
theorem B1578483 : Blo 1576486 1578483 := bstep (se 1 (by rfl) ⟨1183862, by rfl⟩ : syracuseStep 1578483 = 2367725) B2367725
theorem B2364929 : Blo 1576486 2364929 := bstep (se 2 (by rfl) ⟨886848, by rfl⟩ : syracuseStep 2364929 = 1773697) B1773697
theorem B3995153 : Blo 1576486 3995153 := bstep (se 2 (by rfl) ⟨1498182, by rfl⟩ : syracuseStep 3995153 = 2996365) B2996365
theorem B2364947 : Blo 1576486 2364947 := bstep (se 1 (by rfl) ⟨1773710, by rfl⟩ : syracuseStep 2364947 = 3547421) B3547421
theorem B3159587 : Blo 1576486 3159587 := bstep (se 1 (by rfl) ⟨2369690, by rfl⟩ : syracuseStep 3159587 = 4739381) B4739381
theorem B2364977 : Blo 1576486 2364977 := bstep (se 2 (by rfl) ⟨886866, by rfl⟩ : syracuseStep 2364977 = 1773733) B1773733
theorem B1775155 : Blo 1576486 1775155 := bstep (se 1 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 1775155 = 2662733) B2662733
theorem B2364995 : Blo 1576486 2364995 := bstep (se 1 (by rfl) ⟨1773746, by rfl⟩ : syracuseStep 2364995 = 3547493) B3547493
theorem B3995203 : Blo 1576486 3995203 := bstep (se 1 (by rfl) ⟨2996402, by rfl⟩ : syracuseStep 3995203 = 5992805) B5992805
theorem B2365025 : Blo 1576486 2365025 := bstep (se 2 (by rfl) ⟨886884, by rfl⟩ : syracuseStep 2365025 = 1773769) B1773769
theorem B3413603 : Blo 1576486 3413603 := bstep (se 1 (by rfl) ⟨2560202, by rfl⟩ : syracuseStep 3413603 = 5120405) B5120405
theorem B2365043 : Blo 1576486 2365043 := bstep (se 1 (by rfl) ⟨1773782, by rfl⟩ : syracuseStep 2365043 = 3547565) B3547565
theorem B2365073 : Blo 1576486 2365073 := bstep (se 2 (by rfl) ⟨886902, by rfl⟩ : syracuseStep 2365073 = 1773805) B1773805
theorem B1799827 : Blo 1576486 1799827 := bstep (se 1 (by rfl) ⟨1349870, by rfl⟩ : syracuseStep 1799827 = 2699741) B2699741
theorem B2365091 : Blo 1576486 2365091 := bstep (se 1 (by rfl) ⟨1773818, by rfl⟩ : syracuseStep 2365091 = 3547637) B3547637
theorem B7984817 : Blo 1576486 7984817 := bstep (se 2 (by rfl) ⟨2994306, by rfl⟩ : syracuseStep 7984817 = 5988613) B5988613
theorem B2365121 : Blo 1576486 2365121 := bstep (se 2 (by rfl) ⟨886920, by rfl⟩ : syracuseStep 2365121 = 1773841) B1773841
theorem B1996483 : Blo 1576486 1996483 := bstep (se 1 (by rfl) ⟨1497362, by rfl⟩ : syracuseStep 1996483 = 2994725) B2994725
theorem B1775299 : Blo 1576486 1775299 := bstep (se 1 (by rfl) ⟨1331474, by rfl⟩ : syracuseStep 1775299 = 2662949) B2662949
theorem B3995345 : Blo 1576486 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B2365139 : Blo 1576486 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B2365169 : Blo 1576486 2365169 := bstep (se 2 (by rfl) ⟨886938, by rfl⟩ : syracuseStep 2365169 = 1773877) B1773877
theorem B2365187 : Blo 1576486 2365187 := bstep (se 1 (by rfl) ⟨1773890, by rfl⟩ : syracuseStep 2365187 = 3547781) B3547781
theorem B5322509 : Blo 1576486 5322509 := bstep (se 3 (by rfl) ⟨997970, by rfl⟩ : syracuseStep 5322509 = 1995941) B1995941
theorem B2365217 : Blo 1576486 2365217 := bstep (se 2 (by rfl) ⟨886956, by rfl⟩ : syracuseStep 2365217 = 1773913) B1773913
theorem B1996579 : Blo 1576486 1996579 := bstep (se 1 (by rfl) ⟨1497434, by rfl⟩ : syracuseStep 1996579 = 2994869) B2994869
theorem B2365235 : Blo 1576486 2365235 := bstep (se 1 (by rfl) ⟨1773926, by rfl⟩ : syracuseStep 2365235 = 3547853) B3547853
theorem B5322563 : Blo 1576486 5322563 := bstep (se 1 (by rfl) ⟨3991922, by rfl⟩ : syracuseStep 5322563 = 7983845) B7983845
theorem B7198541 : Blo 1576486 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B2365265 : Blo 1576486 2365265 := bstep (se 2 (by rfl) ⟨886974, by rfl⟩ : syracuseStep 2365265 = 1773949) B1773949
theorem B1775443 : Blo 1576486 1775443 := bstep (se 1 (by rfl) ⟨1331582, by rfl⟩ : syracuseStep 1775443 = 2663165) B2663165
theorem B2365283 : Blo 1576486 2365283 := bstep (se 1 (by rfl) ⟨1773962, by rfl⟩ : syracuseStep 2365283 = 3547925) B3547925
theorem B2365313 : Blo 1576486 2365313 := bstep (se 2 (by rfl) ⟨886992, by rfl⟩ : syracuseStep 2365313 = 1773985) B1773985
theorem B2996099 : Blo 1576486 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B2398097 : Blo 1576486 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B2365331 : Blo 1576486 2365331 := bstep (se 1 (by rfl) ⟨1773998, by rfl⟩ : syracuseStep 2365331 = 3547997) B3547997
theorem B2365361 : Blo 1576486 2365361 := bstep (se 2 (by rfl) ⟨887010, by rfl⟩ : syracuseStep 2365361 = 1774021) B1774021
theorem B2365379 : Blo 1576486 2365379 := bstep (se 1 (by rfl) ⟨1774034, by rfl⟩ : syracuseStep 2365379 = 3548069) B3548069
theorem B2398177 : Blo 1576486 2398177 := bstep (se 2 (by rfl) ⟨899316, by rfl⟩ : syracuseStep 2398177 = 1798633) B1798633
theorem B2365409 : Blo 1576486 2365409 := bstep (se 2 (by rfl) ⟨887028, by rfl⟩ : syracuseStep 2365409 = 1774057) B1774057
theorem B2660323 : Blo 1576486 2660323 := bstep (se 1 (by rfl) ⟨1995242, by rfl⟩ : syracuseStep 2660323 = 3990485) B3990485
theorem B1775587 : Blo 1576486 1775587 := bstep (se 1 (by rfl) ⟨1331690, by rfl⟩ : syracuseStep 1775587 = 2663381) B2663381
theorem B2365427 : Blo 1576486 2365427 := bstep (se 1 (by rfl) ⟨1774070, by rfl⟩ : syracuseStep 2365427 = 3548141) B3548141
theorem B2365457 : Blo 1576486 2365457 := bstep (se 2 (by rfl) ⟨887046, by rfl⟩ : syracuseStep 2365457 = 1774093) B1774093
theorem B2365475 : Blo 1576486 2365475 := bstep (se 1 (by rfl) ⟨1774106, by rfl⟩ : syracuseStep 2365475 = 3548213) B3548213
theorem B2365505 : Blo 1576486 2365505 := bstep (se 2 (by rfl) ⟨887064, by rfl⟩ : syracuseStep 2365505 = 1774129) B1774129
theorem B5322833 : Blo 1576486 5322833 := bstep (se 2 (by rfl) ⟨1996062, by rfl⟩ : syracuseStep 5322833 = 3992125) B3992125
theorem B2365523 : Blo 1576486 2365523 := bstep (se 1 (by rfl) ⟨1774142, by rfl⟩ : syracuseStep 2365523 = 3548285) B3548285
theorem B2660465 : Blo 1576486 2660465 := bstep (se 2 (by rfl) ⟨997674, by rfl⟩ : syracuseStep 2660465 = 1995349) B1995349
theorem B2365553 : Blo 1576486 2365553 := bstep (se 2 (by rfl) ⟨887082, by rfl⟩ : syracuseStep 2365553 = 1774165) B1774165
theorem B2881649 : Blo 1576486 2881649 := bstep (se 2 (by rfl) ⟨1080618, by rfl⟩ : syracuseStep 2881649 = 2161237) B2161237
theorem B1775731 : Blo 1576486 1775731 := bstep (se 1 (by rfl) ⟨1331798, by rfl⟩ : syracuseStep 1775731 = 2663597) B2663597
theorem B2365571 : Blo 1576486 2365571 := bstep (se 1 (by rfl) ⟨1774178, by rfl⟩ : syracuseStep 2365571 = 3548357) B3548357
theorem B2365601 : Blo 1576486 2365601 := bstep (se 2 (by rfl) ⟨887100, by rfl⟩ : syracuseStep 2365601 = 1774201) B1774201
theorem B2365619 : Blo 1576486 2365619 := bstep (se 1 (by rfl) ⟨1774214, by rfl⟩ : syracuseStep 2365619 = 3548429) B3548429
theorem B2365649 : Blo 1576486 2365649 := bstep (se 2 (by rfl) ⟨887118, by rfl⟩ : syracuseStep 2365649 = 1774237) B1774237
theorem B2365667 : Blo 1576486 2365667 := bstep (se 1 (by rfl) ⟨1774250, by rfl⟩ : syracuseStep 2365667 = 3548501) B3548501
theorem B2660593 : Blo 1576486 2660593 := bstep (se 2 (by rfl) ⟨997722, by rfl⟩ : syracuseStep 2660593 = 1995445) B1995445
theorem B8526065 : Blo 1576486 8526065 := bstep (se 2 (by rfl) ⟨3197274, by rfl⟩ : syracuseStep 8526065 = 6394549) B6394549
theorem B2365697 : Blo 1576486 2365697 := bstep (se 2 (by rfl) ⟨887136, by rfl⟩ : syracuseStep 2365697 = 1774273) B1774273
theorem B5052689 : Blo 1576486 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B2660627 : Blo 1576486 2660627 := bstep (se 1 (by rfl) ⟨1995470, by rfl⟩ : syracuseStep 2660627 = 3990941) B3990941
theorem B2365715 : Blo 1576486 2365715 := bstep (se 1 (by rfl) ⟨1774286, by rfl⟩ : syracuseStep 2365715 = 3548573) B3548573
theorem B1997075 : Blo 1576486 1997075 := bstep (se 1 (by rfl) ⟨1497806, by rfl⟩ : syracuseStep 1997075 = 2995613) B2995613
theorem B2365745 : Blo 1576486 2365745 := bstep (se 2 (by rfl) ⟨887154, by rfl⟩ : syracuseStep 2365745 = 1774309) B1774309
theorem B2365763 : Blo 1576486 2365763 := bstep (se 1 (by rfl) ⟨1774322, by rfl⟩ : syracuseStep 2365763 = 3548645) B3548645
theorem B2365793 : Blo 1576486 2365793 := bstep (se 2 (by rfl) ⟨887172, by rfl⟩ : syracuseStep 2365793 = 1774345) B1774345
theorem B2365811 : Blo 1576486 2365811 := bstep (se 1 (by rfl) ⟨1774358, by rfl⟩ : syracuseStep 2365811 = 3548717) B3548717
theorem B2365841 : Blo 1576486 2365841 := bstep (se 2 (by rfl) ⟨887190, by rfl⟩ : syracuseStep 2365841 = 1774381) B1774381
theorem B2660755 : Blo 1576486 2660755 := bstep (se 1 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 2660755 = 3991133) B3991133
theorem B2365859 : Blo 1576486 2365859 := bstep (se 1 (by rfl) ⟨1774394, by rfl⟩ : syracuseStep 2365859 = 3548789) B3548789
theorem B2365889 : Blo 1576486 2365889 := bstep (se 2 (by rfl) ⟨887208, by rfl⟩ : syracuseStep 2365889 = 1774417) B1774417
theorem B11983301 : Blo 1576486 11983301 := bstep (se 4 (by rfl) ⟨1123434, by rfl⟩ : syracuseStep 11983301 = 2246869) B2246869
theorem B5052881 : Blo 1576486 5052881 := bstep (se 2 (by rfl) ⟨1894830, by rfl⟩ : syracuseStep 5052881 = 3789661) B3789661
theorem B2365907 : Blo 1576486 2365907 := bstep (se 1 (by rfl) ⟨1774430, by rfl⟩ : syracuseStep 2365907 = 3548861) B3548861
theorem B2365937 : Blo 1576486 2365937 := bstep (se 2 (by rfl) ⟨887226, by rfl⟩ : syracuseStep 2365937 = 1774453) B1774453
theorem B2365955 : Blo 1576486 2365955 := bstep (se 1 (by rfl) ⟨1774466, by rfl⟩ : syracuseStep 2365955 = 3548933) B3548933
theorem B2660897 : Blo 1576486 2660897 := bstep (se 2 (by rfl) ⟨997836, by rfl⟩ : syracuseStep 2660897 = 1995673) B1995673
theorem B2365985 : Blo 1576486 2365985 := bstep (se 2 (by rfl) ⟨887244, by rfl⟩ : syracuseStep 2365985 = 1774489) B1774489
theorem B10787363 : Blo 1576486 10787363 := bstep (se 1 (by rfl) ⟨8090522, by rfl⟩ : syracuseStep 10787363 = 16181045) B16181045
theorem B2366003 : Blo 1576486 2366003 := bstep (se 1 (by rfl) ⟨1774502, by rfl⟩ : syracuseStep 2366003 = 3549005) B3549005
theorem B2366033 : Blo 1576486 2366033 := bstep (se 2 (by rfl) ⟨887262, by rfl⟩ : syracuseStep 2366033 = 1774525) B1774525
theorem B2366051 : Blo 1576486 2366051 := bstep (se 1 (by rfl) ⟨1774538, by rfl⟩ : syracuseStep 2366051 = 3549077) B3549077
theorem B5323373 : Blo 1576486 5323373 := bstep (se 3 (by rfl) ⟨998132, by rfl⟩ : syracuseStep 5323373 = 1996265) B1996265
theorem B2366081 : Blo 1576486 2366081 := bstep (se 2 (by rfl) ⟨887280, by rfl⟩ : syracuseStep 2366081 = 1774561) B1774561
theorem B2366099 : Blo 1576486 2366099 := bstep (se 1 (by rfl) ⟨1774574, by rfl⟩ : syracuseStep 2366099 = 3549149) B3549149
theorem B2661025 : Blo 1576486 2661025 := bstep (se 2 (by rfl) ⟨997884, by rfl⟩ : syracuseStep 2661025 = 1995769) B1995769
theorem B5323427 : Blo 1576486 5323427 := bstep (se 1 (by rfl) ⟨3992570, by rfl⟩ : syracuseStep 5323427 = 7985141) B7985141
theorem B5397155 : Blo 1576486 5397155 := bstep (se 1 (by rfl) ⟨4047866, by rfl⟩ : syracuseStep 5397155 = 8095733) B8095733
theorem B2366129 : Blo 1576486 2366129 := bstep (se 2 (by rfl) ⟨887298, by rfl⟩ : syracuseStep 2366129 = 1774597) B1774597
theorem B2661059 : Blo 1576486 2661059 := bstep (se 1 (by rfl) ⟨1995794, by rfl⟩ : syracuseStep 2661059 = 3991589) B3991589
theorem B2366147 : Blo 1576486 2366147 := bstep (se 1 (by rfl) ⟨1774610, by rfl⟩ : syracuseStep 2366147 = 3549221) B3549221
theorem B3791555 : Blo 1576486 3791555 := bstep (se 1 (by rfl) ⟨2843666, by rfl⟩ : syracuseStep 3791555 = 5687333) B5687333
theorem B2366177 : Blo 1576486 2366177 := bstep (se 2 (by rfl) ⟨887316, by rfl⟩ : syracuseStep 2366177 = 1774633) B1774633
theorem B2562787 : Blo 1576486 2562787 := bstep (se 1 (by rfl) ⟨1922090, by rfl⟩ : syracuseStep 2562787 = 3844181) B3844181
theorem B2366195 : Blo 1576486 2366195 := bstep (se 1 (by rfl) ⟨1774646, by rfl⟩ : syracuseStep 2366195 = 3549293) B3549293
theorem B2366225 : Blo 1576486 2366225 := bstep (se 2 (by rfl) ⟨887334, by rfl⟩ : syracuseStep 2366225 = 1774669) B1774669
theorem B2366243 : Blo 1576486 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B2366273 : Blo 1576486 2366273 := bstep (se 2 (by rfl) ⟨887352, by rfl⟩ : syracuseStep 2366273 = 1774705) B1774705
theorem B2661187 : Blo 1576486 2661187 := bstep (se 1 (by rfl) ⟨1995890, by rfl⟩ : syracuseStep 2661187 = 3991781) B3991781
theorem B6740813 : Blo 1576486 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B2366291 : Blo 1576486 2366291 := bstep (se 1 (by rfl) ⟨1774718, by rfl⟩ : syracuseStep 2366291 = 3549437) B3549437
theorem B2366321 : Blo 1576486 2366321 := bstep (se 2 (by rfl) ⟨887370, by rfl⟩ : syracuseStep 2366321 = 1774741) B1774741
theorem B2841475 : Blo 1576486 2841475 := bstep (se 1 (by rfl) ⟨2131106, by rfl⟩ : syracuseStep 2841475 = 4262213) B4262213
theorem B2366339 : Blo 1576486 2366339 := bstep (se 1 (by rfl) ⟨1774754, by rfl⟩ : syracuseStep 2366339 = 3549509) B3549509
theorem B2366369 : Blo 1576486 2366369 := bstep (se 2 (by rfl) ⟨887388, by rfl⟩ : syracuseStep 2366369 = 1774777) B1774777
theorem B4799405 : Blo 1576486 4799405 := bstep (se 3 (by rfl) ⟨899888, by rfl⟩ : syracuseStep 4799405 = 1799777) B1799777
theorem B5323697 : Blo 1576486 5323697 := bstep (se 2 (by rfl) ⟨1996386, by rfl⟩ : syracuseStep 5323697 = 3992773) B3992773
theorem B2366387 : Blo 1576486 2366387 := bstep (se 1 (by rfl) ⟨1774790, by rfl⟩ : syracuseStep 2366387 = 3549581) B3549581
theorem B2661329 : Blo 1576486 2661329 := bstep (se 2 (by rfl) ⟨997998, by rfl⟩ : syracuseStep 2661329 = 1995997) B1995997
theorem B2366417 : Blo 1576486 2366417 := bstep (se 2 (by rfl) ⟨887406, by rfl⟩ : syracuseStep 2366417 = 1774813) B1774813
theorem B2366435 : Blo 1576486 2366435 := bstep (se 1 (by rfl) ⟨1774826, by rfl⟩ : syracuseStep 2366435 = 3549653) B3549653
theorem B3791843 : Blo 1576486 3791843 := bstep (se 1 (by rfl) ⟨2843882, by rfl⟩ : syracuseStep 3791843 = 5687765) B5687765
theorem B17964017 : Blo 1576486 17964017 := bstep (se 2 (by rfl) ⟨6736506, by rfl⟩ : syracuseStep 17964017 = 13473013) B13473013
theorem B2735089 : Blo 1576486 2735089 := bstep (se 2 (by rfl) ⟨1025658, by rfl⟩ : syracuseStep 2735089 = 2051317) B2051317
theorem B2366465 : Blo 1576486 2366465 := bstep (se 2 (by rfl) ⟨887424, by rfl⟩ : syracuseStep 2366465 = 1774849) B1774849
theorem B2366483 : Blo 1576486 2366483 := bstep (se 1 (by rfl) ⟨1774862, by rfl⟩ : syracuseStep 2366483 = 3549725) B3549725
theorem B2366513 : Blo 1576486 2366513 := bstep (se 2 (by rfl) ⟨887442, by rfl⟩ : syracuseStep 2366513 = 1774885) B1774885
theorem B2366531 : Blo 1576486 2366531 := bstep (se 1 (by rfl) ⟨1774898, by rfl⟩ : syracuseStep 2366531 = 3549797) B3549797
theorem B2661457 : Blo 1576486 2661457 := bstep (se 2 (by rfl) ⟨998046, by rfl⟩ : syracuseStep 2661457 = 1996093) B1996093
theorem B2366561 : Blo 1576486 2366561 := bstep (se 2 (by rfl) ⟨887460, by rfl⟩ : syracuseStep 2366561 = 1774921) B1774921
theorem B7986275 : Blo 1576486 7986275 := bstep (se 1 (by rfl) ⟨5989706, by rfl⟩ : syracuseStep 7986275 = 11979413) B11979413
theorem B2661491 : Blo 1576486 2661491 := bstep (se 1 (by rfl) ⟨1996118, by rfl⟩ : syracuseStep 2661491 = 3992237) B3992237
theorem B2366579 : Blo 1576486 2366579 := bstep (se 1 (by rfl) ⟨1774934, by rfl⟩ : syracuseStep 2366579 = 3549869) B3549869
theorem B2366609 : Blo 1576486 2366609 := bstep (se 2 (by rfl) ⟨887478, by rfl⟩ : syracuseStep 2366609 = 1774957) B1774957
theorem B2366627 : Blo 1576486 2366627 := bstep (se 1 (by rfl) ⟨1774970, by rfl⟩ : syracuseStep 2366627 = 3549941) B3549941
theorem B2399411 : Blo 1576486 2399411 := bstep (se 1 (by rfl) ⟨1799558, by rfl⟩ : syracuseStep 2399411 = 3599117) B3599117
theorem B2366657 : Blo 1576486 2366657 := bstep (se 2 (by rfl) ⟨887496, by rfl⟩ : syracuseStep 2366657 = 1774993) B1774993
theorem B2366675 : Blo 1576486 2366675 := bstep (se 1 (by rfl) ⟨1775006, by rfl⟩ : syracuseStep 2366675 = 3550013) B3550013
theorem B5397731 : Blo 1576486 5397731 := bstep (se 1 (by rfl) ⟨4048298, by rfl⟩ : syracuseStep 5397731 = 8096597) B8096597
theorem B2366705 : Blo 1576486 2366705 := bstep (se 2 (by rfl) ⟨887514, by rfl⟩ : syracuseStep 2366705 = 1775029) B1775029
theorem B2661619 : Blo 1576486 2661619 := bstep (se 1 (by rfl) ⟨1996214, by rfl⟩ : syracuseStep 2661619 = 3992429) B3992429
theorem B2366723 : Blo 1576486 2366723 := bstep (se 1 (by rfl) ⟨1775042, by rfl⟩ : syracuseStep 2366723 = 3550085) B3550085
theorem B2366753 : Blo 1576486 2366753 := bstep (se 2 (by rfl) ⟨887532, by rfl⟩ : syracuseStep 2366753 = 1775065) B1775065
theorem B2366771 : Blo 1576486 2366771 := bstep (se 1 (by rfl) ⟨1775078, by rfl⟩ : syracuseStep 2366771 = 3550157) B3550157
theorem B2366801 : Blo 1576486 2366801 := bstep (se 2 (by rfl) ⟨887550, by rfl⟩ : syracuseStep 2366801 = 1775101) B1775101
theorem B2366819 : Blo 1576486 2366819 := bstep (se 1 (by rfl) ⟨1775114, by rfl⟩ : syracuseStep 2366819 = 3550229) B3550229
theorem B2661761 : Blo 1576486 2661761 := bstep (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) B1996321
theorem B2366849 : Blo 1576486 2366849 := bstep (se 2 (by rfl) ⟨887568, by rfl⟩ : syracuseStep 2366849 = 1775137) B1775137
theorem B4554125 : Blo 1576486 4554125 := bstep (se 3 (by rfl) ⟨853898, by rfl⟩ : syracuseStep 4554125 = 1707797) B1707797
theorem B2366867 : Blo 1576486 2366867 := bstep (se 1 (by rfl) ⟨1775150, by rfl⟩ : syracuseStep 2366867 = 3550301) B3550301
theorem B2366897 : Blo 1576486 2366897 := bstep (se 2 (by rfl) ⟨887586, by rfl⟩ : syracuseStep 2366897 = 1775173) B1775173
theorem B21052853 : Blo 1576486 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B2366915 : Blo 1576486 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B5324237 : Blo 1576486 5324237 := bstep (se 3 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 5324237 = 1996589) B1996589
theorem B2366945 : Blo 1576486 2366945 := bstep (se 2 (by rfl) ⟨887604, by rfl⟩ : syracuseStep 2366945 = 1775209) B1775209
theorem B2366963 : Blo 1576486 2366963 := bstep (se 1 (by rfl) ⟨1775222, by rfl⟩ : syracuseStep 2366963 = 3550445) B3550445
theorem B2661889 : Blo 1576486 2661889 := bstep (se 2 (by rfl) ⟨998208, by rfl⟩ : syracuseStep 2661889 = 1996417) B1996417
theorem B5324291 : Blo 1576486 5324291 := bstep (se 1 (by rfl) ⟨3993218, by rfl⟩ : syracuseStep 5324291 = 7986437) B7986437
theorem B2366993 : Blo 1576486 2366993 := bstep (se 2 (by rfl) ⟨887622, by rfl⟩ : syracuseStep 2366993 = 1775245) B1775245
theorem B2661923 : Blo 1576486 2661923 := bstep (se 1 (by rfl) ⟨1996442, by rfl⟩ : syracuseStep 2661923 = 3992885) B3992885
theorem B10108451 : Blo 1576486 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B2367011 : Blo 1576486 2367011 := bstep (se 1 (by rfl) ⟨1775258, by rfl⟩ : syracuseStep 2367011 = 3550517) B3550517
theorem B2367041 : Blo 1576486 2367041 := bstep (se 2 (by rfl) ⟨887640, by rfl⟩ : syracuseStep 2367041 = 1775281) B1775281
theorem B2367059 : Blo 1576486 2367059 := bstep (se 1 (by rfl) ⟨1775294, by rfl⟩ : syracuseStep 2367059 = 3550589) B3550589
theorem B2367089 : Blo 1576486 2367089 := bstep (se 2 (by rfl) ⟨887658, by rfl⟩ : syracuseStep 2367089 = 1775317) B1775317
theorem B2367107 : Blo 1576486 2367107 := bstep (se 1 (by rfl) ⟨1775330, by rfl⟩ : syracuseStep 2367107 = 3550661) B3550661
theorem B2367137 : Blo 1576486 2367137 := bstep (se 2 (by rfl) ⟨887676, by rfl⟩ : syracuseStep 2367137 = 1775353) B1775353
theorem B2662051 : Blo 1576486 2662051 := bstep (se 1 (by rfl) ⟨1996538, by rfl⟩ : syracuseStep 2662051 = 3993077) B3993077
theorem B2367155 : Blo 1576486 2367155 := bstep (se 1 (by rfl) ⟨1775366, by rfl⟩ : syracuseStep 2367155 = 3550733) B3550733
theorem B2367185 : Blo 1576486 2367185 := bstep (se 2 (by rfl) ⟨887694, by rfl⟩ : syracuseStep 2367185 = 1775389) B1775389
theorem B2367203 : Blo 1576486 2367203 := bstep (se 1 (by rfl) ⟨1775402, by rfl⟩ : syracuseStep 2367203 = 3550805) B3550805
theorem B2367233 : Blo 1576486 2367233 := bstep (se 2 (by rfl) ⟨887712, by rfl⟩ : syracuseStep 2367233 = 1775425) B1775425
theorem B5324561 : Blo 1576486 5324561 := bstep (se 2 (by rfl) ⟨1996710, by rfl⟩ : syracuseStep 5324561 = 3993421) B3993421
theorem B2367251 : Blo 1576486 2367251 := bstep (se 1 (by rfl) ⟨1775438, by rfl⟩ : syracuseStep 2367251 = 3550877) B3550877
theorem B2662193 : Blo 1576486 2662193 := bstep (se 2 (by rfl) ⟨998322, by rfl⟩ : syracuseStep 2662193 = 1996645) B1996645
theorem B2367281 : Blo 1576486 2367281 := bstep (se 2 (by rfl) ⟨887730, by rfl⟩ : syracuseStep 2367281 = 1775461) B1775461
theorem B2367299 : Blo 1576486 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B2367329 : Blo 1576486 2367329 := bstep (se 2 (by rfl) ⟨887748, by rfl⟩ : syracuseStep 2367329 = 1775497) B1775497
theorem B9109361 : Blo 1576486 9109361 := bstep (se 2 (by rfl) ⟨3416010, by rfl⟩ : syracuseStep 9109361 = 6832021) B6832021
theorem B2367347 : Blo 1576486 2367347 := bstep (se 1 (by rfl) ⟨1775510, by rfl⟩ : syracuseStep 2367347 = 3551021) B3551021
theorem B7987085 : Blo 1576486 7987085 := bstep (se 3 (by rfl) ⟨1497578, by rfl⟩ : syracuseStep 7987085 = 2995157) B2995157
theorem B2367377 : Blo 1576486 2367377 := bstep (se 2 (by rfl) ⟨887766, by rfl⟩ : syracuseStep 2367377 = 1775533) B1775533
theorem B2367395 : Blo 1576486 2367395 := bstep (se 1 (by rfl) ⟨1775546, by rfl⟩ : syracuseStep 2367395 = 3551093) B3551093
theorem B2662321 : Blo 1576486 2662321 := bstep (se 2 (by rfl) ⟨998370, by rfl⟩ : syracuseStep 2662321 = 1996741) B1996741
theorem B2367425 : Blo 1576486 2367425 := bstep (se 2 (by rfl) ⟨887784, by rfl⟩ : syracuseStep 2367425 = 1775569) B1775569
theorem B13656005 : Blo 1576486 13656005 := bstep (se 4 (by rfl) ⟨1280250, by rfl⟩ : syracuseStep 13656005 = 2560501) B2560501
theorem B8986565 : Blo 1576486 8986565 := bstep (se 4 (by rfl) ⟨842490, by rfl⟩ : syracuseStep 8986565 = 1684981) B1684981
theorem B2662355 : Blo 1576486 2662355 := bstep (se 1 (by rfl) ⟨1996766, by rfl⟩ : syracuseStep 2662355 = 3993533) B3993533
theorem B2367443 : Blo 1576486 2367443 := bstep (se 1 (by rfl) ⟨1775582, by rfl⟩ : syracuseStep 2367443 = 3551165) B3551165
theorem B2367473 : Blo 1576486 2367473 := bstep (se 2 (by rfl) ⟨887802, by rfl⟩ : syracuseStep 2367473 = 1775605) B1775605
theorem B3547187 : Blo 1576486 3547187 := bstep (se 1 (by rfl) ⟨2660390, by rfl⟩ : syracuseStep 3547187 = 5320781) B5320781
theorem B2367563 : Blo 1576486 2367563 := bstep (se 1 (by rfl) ⟨1775672, by rfl⟩ : syracuseStep 2367563 = 3551345) B3551345
theorem B3547223 : Blo 1576486 3547223 := bstep (se 1 (by rfl) ⟨2660417, by rfl⟩ : syracuseStep 3547223 = 5320835) B5320835
theorem B2367575 : Blo 1576486 2367575 := bstep (se 1 (by rfl) ⟨1775681, by rfl⟩ : syracuseStep 2367575 = 3551363) B3551363
theorem B2367641 : Blo 1576486 2367641 := bstep (se 2 (by rfl) ⟨887865, by rfl⟩ : syracuseStep 2367641 = 1775731) B1775731
theorem B5324993 : Blo 1576486 5324993 := bstep (se 2 (by rfl) ⟨1996872, by rfl⟩ : syracuseStep 5324993 = 3993745) B3993745
theorem B3547403 : Blo 1576486 3547403 := bstep (se 1 (by rfl) ⟨2660552, by rfl⟩ : syracuseStep 3547403 = 5321105) B5321105
theorem B8093969 : Blo 1576486 8093969 := bstep (se 2 (by rfl) ⟨3035238, by rfl⟩ : syracuseStep 8093969 = 6070477) B6070477
theorem B2662679 : Blo 1576486 2662679 := bstep (se 1 (by rfl) ⟨1997009, by rfl⟩ : syracuseStep 2662679 = 3994019) B3994019
theorem B3547457 : Blo 1576486 3547457 := bstep (se 2 (by rfl) ⟨1330296, by rfl⟩ : syracuseStep 3547457 = 2660593) B2660593
theorem B11985245 : Blo 1576486 11985245 := bstep (se 3 (by rfl) ⟨2247233, by rfl⟩ : syracuseStep 11985245 = 4494467) B4494467
theorem B2662807 : Blo 1576486 2662807 := bstep (se 1 (by rfl) ⟨1997105, by rfl⟩ : syracuseStep 2662807 = 3994211) B3994211
theorem B68256269 : Blo 1576486 68256269 := bstep (se 3 (by rfl) ⟨12798050, by rfl⟩ : syracuseStep 68256269 = 25596101) B25596101
theorem B5988887 : Blo 1576486 5988887 := bstep (se 1 (by rfl) ⟨4491665, by rfl⟩ : syracuseStep 5988887 = 8983331) B8983331
theorem B3547673 : Blo 1576486 3547673 := bstep (se 2 (by rfl) ⟨1330377, by rfl⟩ : syracuseStep 3547673 = 2660755) B2660755
theorem B2245195 : Blo 1576486 2245195 := bstep (se 1 (by rfl) ⟨1683896, by rfl⟩ : syracuseStep 2245195 = 3367793) B3367793
theorem B3547763 : Blo 1576486 3547763 := bstep (se 1 (by rfl) ⟨2660822, by rfl⟩ : syracuseStep 3547763 = 5321645) B5321645
theorem B3547799 : Blo 1576486 3547799 := bstep (se 1 (by rfl) ⟨2660849, by rfl⟩ : syracuseStep 3547799 = 5321699) B5321699
theorem B5989085 : Blo 1576486 5989085 := bstep (se 3 (by rfl) ⟨1122953, by rfl⟩ : syracuseStep 5989085 = 2245907) B2245907
theorem B5325533 : Blo 1576486 5325533 := bstep (se 3 (by rfl) ⟨998537, by rfl⟩ : syracuseStep 5325533 = 1997075) B1997075
theorem B8979275 : Blo 1576486 8979275 := bstep (se 1 (by rfl) ⟨6734456, by rfl⟩ : syracuseStep 8979275 = 13468913) B13468913
theorem B3547979 : Blo 1576486 3547979 := bstep (se 1 (by rfl) ⟨2660984, by rfl⟩ : syracuseStep 3547979 = 5321969) B5321969
theorem B3548033 : Blo 1576486 3548033 := bstep (se 2 (by rfl) ⟨1330512, by rfl⟩ : syracuseStep 3548033 = 2661025) B2661025
theorem B6734765 : Blo 1576486 6734765 := bstep (se 3 (by rfl) ⟨1262768, by rfl⟩ : syracuseStep 6734765 = 2525537) B2525537
theorem B3417049 : Blo 1576486 3417049 := bstep (se 2 (by rfl) ⟨1281393, by rfl⟩ : syracuseStep 3417049 = 2562787) B2562787
theorem B2663435 : Blo 1576486 2663435 := bstep (se 1 (by rfl) ⟨1997576, by rfl⟩ : syracuseStep 2663435 = 3995153) B3995153
theorem B2106391 : Blo 1576486 2106391 := bstep (se 1 (by rfl) ⟨1579793, by rfl⟩ : syracuseStep 2106391 = 3159587) B3159587
theorem B5686337 : Blo 1576486 5686337 := bstep (se 2 (by rfl) ⟨2132376, by rfl⟩ : syracuseStep 5686337 = 4264753) B4264753
theorem B3990617 : Blo 1576486 3990617 := bstep (se 2 (by rfl) ⟨1496481, by rfl⟩ : syracuseStep 3990617 = 2992963) B2992963
theorem B3548249 : Blo 1576486 3548249 := bstep (se 2 (by rfl) ⟨1330593, by rfl⟩ : syracuseStep 3548249 = 2661187) B2661187
theorem B2663563 : Blo 1576486 2663563 := bstep (se 1 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 2663563 = 3995345) B3995345
theorem B3548339 : Blo 1576486 3548339 := bstep (se 1 (by rfl) ⟨2661254, by rfl⟩ : syracuseStep 3548339 = 5322509) B5322509
theorem B3548375 : Blo 1576486 3548375 := bstep (se 1 (by rfl) ⟨2661281, by rfl⟩ : syracuseStep 3548375 = 5322563) B5322563
theorem B2131339 : Blo 1576486 2131339 := bstep (se 1 (by rfl) ⟨1598504, by rfl⟩ : syracuseStep 2131339 = 3197009) B3197009
theorem B3548555 : Blo 1576486 3548555 := bstep (se 1 (by rfl) ⟨2661416, by rfl⟩ : syracuseStep 3548555 = 5322833) B5322833
theorem B3548609 : Blo 1576486 3548609 := bstep (se 2 (by rfl) ⟨1330728, by rfl⟩ : syracuseStep 3548609 = 2661457) B2661457
theorem B3368459 : Blo 1576486 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B8988205 : Blo 1576486 8988205 := bstep (se 3 (by rfl) ⟨1685288, by rfl⟩ : syracuseStep 8988205 = 3370577) B3370577
theorem B9102941 : Blo 1576486 9102941 := bstep (se 3 (by rfl) ⟨1706801, by rfl⟩ : syracuseStep 9102941 = 3413603) B3413603
theorem B7988867 : Blo 1576486 7988867 := bstep (se 1 (by rfl) ⟨5991650, by rfl⟩ : syracuseStep 7988867 = 11983301) B11983301
theorem B4490903 : Blo 1576486 4490903 := bstep (se 1 (by rfl) ⟨3368177, by rfl⟩ : syracuseStep 4490903 = 6736355) B6736355
theorem B3548825 : Blo 1576486 3548825 := bstep (se 2 (by rfl) ⟨1330809, by rfl⟩ : syracuseStep 3548825 = 2661619) B2661619
theorem B3548915 : Blo 1576486 3548915 := bstep (se 1 (by rfl) ⟨2661686, by rfl⟩ : syracuseStep 3548915 = 5323373) B5323373
theorem B3548951 : Blo 1576486 3548951 := bstep (se 1 (by rfl) ⟨2661713, by rfl⟩ : syracuseStep 3548951 = 5323427) B5323427
theorem B3598103 : Blo 1576486 3598103 := bstep (se 1 (by rfl) ⟨2698577, by rfl⟩ : syracuseStep 3598103 = 5397155) B5397155
theorem B5326667 : Blo 1576486 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B3549131 : Blo 1576486 3549131 := bstep (se 1 (by rfl) ⟨2661848, by rfl⟩ : syracuseStep 3549131 = 5323697) B5323697
theorem B3549185 : Blo 1576486 3549185 := bstep (se 2 (by rfl) ⟨1330944, by rfl⟩ : syracuseStep 3549185 = 2661889) B2661889
theorem B11520035 : Blo 1576486 11520035 := bstep (se 1 (by rfl) ⟨8640026, by rfl⟩ : syracuseStep 11520035 = 17280053) B17280053
theorem B5326937 : Blo 1576486 5326937 := bstep (se 2 (by rfl) ⟨1997601, by rfl⟩ : syracuseStep 5326937 = 3995203) B3995203
theorem B1599607 : Blo 1576486 1599607 := bstep (se 1 (by rfl) ⟨1199705, by rfl⟩ : syracuseStep 1599607 = 2399411) B2399411
theorem B3598487 : Blo 1576486 3598487 := bstep (se 1 (by rfl) ⟨2698865, by rfl⟩ : syracuseStep 3598487 = 5397731) B5397731
theorem B4049099 : Blo 1576486 4049099 := bstep (se 1 (by rfl) ⟨3036824, by rfl⟩ : syracuseStep 4049099 = 6073649) B6073649
theorem B3549401 : Blo 1576486 3549401 := bstep (se 2 (by rfl) ⟨1331025, by rfl⟩ : syracuseStep 3549401 = 2662051) B2662051
theorem B14035235 : Blo 1576486 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B3549491 : Blo 1576486 3549491 := bstep (se 1 (by rfl) ⟨2662118, by rfl⟩ : syracuseStep 3549491 = 5324237) B5324237
theorem B3549527 : Blo 1576486 3549527 := bstep (se 1 (by rfl) ⟨2662145, by rfl⟩ : syracuseStep 3549527 = 5324291) B5324291
theorem B8980915 : Blo 1576486 8980915 := bstep (se 1 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 8980915 = 13471373) B13471373
theorem B3369433 : Blo 1576486 3369433 := bstep (se 2 (by rfl) ⟨1263537, by rfl⟩ : syracuseStep 3369433 = 2527075) B2527075
theorem B3549707 : Blo 1576486 3549707 := bstep (se 1 (by rfl) ⟨2662280, by rfl⟩ : syracuseStep 3549707 = 5324561) B5324561
theorem B3549761 : Blo 1576486 3549761 := bstep (se 2 (by rfl) ⟨1331160, by rfl⟩ : syracuseStep 3549761 = 2662321) B2662321
theorem B6072907 : Blo 1576486 6072907 := bstep (se 1 (by rfl) ⟨4554680, by rfl⟩ : syracuseStep 6072907 = 9109361) B9109361
theorem B14387813 : Blo 1576486 14387813 := bstep (se 4 (by rfl) ⟨1348857, by rfl⟩ : syracuseStep 14387813 = 2697715) B2697715
theorem B3197569 : Blo 1576486 3197569 := bstep (se 2 (by rfl) ⟨1199088, by rfl⟩ : syracuseStep 3197569 = 2398177) B2398177
theorem B9104003 : Blo 1576486 9104003 := bstep (se 1 (by rfl) ⟨6828002, by rfl⟩ : syracuseStep 9104003 = 13656005) B13656005
theorem B5991043 : Blo 1576486 5991043 := bstep (se 1 (by rfl) ⟨4493282, by rfl⟩ : syracuseStep 5991043 = 8986565) B8986565
theorem B3992267 : Blo 1576486 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B3369689 : Blo 1576486 3369689 := bstep (se 2 (by rfl) ⟨1263633, by rfl⟩ : syracuseStep 3369689 = 2527267) B2527267
theorem B3549977 : Blo 1576486 3549977 := bstep (se 2 (by rfl) ⟨1331241, by rfl⟩ : syracuseStep 3549977 = 2662483) B2662483
theorem B2132825 : Blo 1576486 2132825 := bstep (se 2 (by rfl) ⟨799809, by rfl⟩ : syracuseStep 2132825 = 1599619) B1599619
theorem B3550067 : Blo 1576486 3550067 := bstep (se 1 (by rfl) ⟨2662550, by rfl⟩ : syracuseStep 3550067 = 5325101) B5325101
theorem B3550103 : Blo 1576486 3550103 := bstep (se 1 (by rfl) ⟨2662577, by rfl⟩ : syracuseStep 3550103 = 5325155) B5325155
theorem B5991347 : Blo 1576486 5991347 := bstep (se 1 (by rfl) ⟨4493510, by rfl⟩ : syracuseStep 5991347 = 8987021) B8987021
theorem B4492235 : Blo 1576486 4492235 := bstep (se 1 (by rfl) ⟨3369176, by rfl⟩ : syracuseStep 4492235 = 6738353) B6738353
theorem B1895383 : Blo 1576486 1895383 := bstep (se 1 (by rfl) ⟨1421537, by rfl⟩ : syracuseStep 1895383 = 2843075) B2843075
theorem B3550283 : Blo 1576486 3550283 := bstep (se 1 (by rfl) ⟨2662712, by rfl⟩ : syracuseStep 3550283 = 5325425) B5325425
theorem B3599435 : Blo 1576486 3599435 := bstep (se 1 (by rfl) ⟨2699576, by rfl⟩ : syracuseStep 3599435 = 5399153) B5399153
theorem B2993267 : Blo 1576486 2993267 := bstep (se 1 (by rfl) ⟨2244950, by rfl⟩ : syracuseStep 2993267 = 4489901) B4489901
theorem B3370099 : Blo 1576486 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B3550337 : Blo 1576486 3550337 := bstep (se 2 (by rfl) ⟨1331376, by rfl⟩ : syracuseStep 3550337 = 2662753) B2662753
theorem B21580951 : Blo 1576486 21580951 := bstep (se 1 (by rfl) ⟨16185713, by rfl⟩ : syracuseStep 21580951 = 32371427) B32371427
theorem B19721477 : Blo 1576486 19721477 := bstep (se 4 (by rfl) ⟨1848888, by rfl⟩ : syracuseStep 19721477 = 3697777) B3697777
theorem B22736173 : Blo 1576486 22736173 := bstep (se 3 (by rfl) ⟨4263032, by rfl⟩ : syracuseStep 22736173 = 8526065) B8526065
theorem B3550553 : Blo 1576486 3550553 := bstep (se 2 (by rfl) ⟨1331457, by rfl⟩ : syracuseStep 3550553 = 2662915) B2662915
theorem B6393239 : Blo 1576486 6393239 := bstep (se 1 (by rfl) ⟨4794929, by rfl⟩ : syracuseStep 6393239 = 9589859) B9589859
theorem B12643735 : Blo 1576486 12643735 := bstep (se 1 (by rfl) ⟨9482801, by rfl⟩ : syracuseStep 12643735 = 18965603) B18965603
theorem B3550643 : Blo 1576486 3550643 := bstep (se 1 (by rfl) ⟨2662982, by rfl⟩ : syracuseStep 3550643 = 5325965) B5325965
theorem B3550679 : Blo 1576486 3550679 := bstep (se 1 (by rfl) ⟨2663009, by rfl⟩ : syracuseStep 3550679 = 5326019) B5326019
theorem B3198475 : Blo 1576486 3198475 := bstep (se 1 (by rfl) ⟨2398856, by rfl⟩ : syracuseStep 3198475 = 4797713) B4797713
theorem B49262093 : Blo 1576486 49262093 := bstep (se 3 (by rfl) ⟨9236642, by rfl⟩ : syracuseStep 49262093 = 18473285) B18473285
theorem B31157777 : Blo 1576486 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B1576491 : Blo 1576486 1576491 := bstep (se 1 (by rfl) ⟨1182368, by rfl⟩ : syracuseStep 1576491 = 2364737) B2364737
theorem B1576503 : Blo 1576486 1576503 := bstep (se 1 (by rfl) ⟨1182377, by rfl⟩ : syracuseStep 1576503 = 2364755) B2364755
theorem B5992001 : Blo 1576486 5992001 := bstep (se 2 (by rfl) ⟨2247000, by rfl⟩ : syracuseStep 5992001 = 4494001) B4494001
theorem B1576523 : Blo 1576486 1576523 := bstep (se 1 (by rfl) ⟨1182392, by rfl⟩ : syracuseStep 1576523 = 2364785) B2364785
theorem B1576535 : Blo 1576486 1576535 := bstep (se 1 (by rfl) ⟨1182401, by rfl⟩ : syracuseStep 1576535 = 2364803) B2364803
theorem B2993753 : Blo 1576486 2993753 := bstep (se 2 (by rfl) ⟨1122657, by rfl⟩ : syracuseStep 2993753 = 2245315) B2245315
theorem B1576555 : Blo 1576486 1576555 := bstep (se 1 (by rfl) ⟨1182416, by rfl⟩ : syracuseStep 1576555 = 2364833) B2364833
theorem B1576567 : Blo 1576486 1576567 := bstep (se 1 (by rfl) ⟨1182425, by rfl⟩ : syracuseStep 1576567 = 2364851) B2364851
theorem B1576587 : Blo 1576486 1576587 := bstep (se 1 (by rfl) ⟨1182440, by rfl⟩ : syracuseStep 1576587 = 2364881) B2364881
theorem B3550859 : Blo 1576486 3550859 := bstep (se 1 (by rfl) ⟨2663144, by rfl⟩ : syracuseStep 3550859 = 5326289) B5326289
theorem B1576599 : Blo 1576486 1576599 := bstep (se 1 (by rfl) ⟨1182449, by rfl⟩ : syracuseStep 1576599 = 2364899) B2364899
theorem B3993239 : Blo 1576486 3993239 := bstep (se 1 (by rfl) ⟨2994929, by rfl⟩ : syracuseStep 3993239 = 5989859) B5989859
theorem B1576619 : Blo 1576486 1576619 := bstep (se 1 (by rfl) ⟨1182464, by rfl⟩ : syracuseStep 1576619 = 2364929) B2364929
theorem B1576631 : Blo 1576486 1576631 := bstep (se 1 (by rfl) ⟨1182473, by rfl⟩ : syracuseStep 1576631 = 2364947) B2364947
theorem B3550913 : Blo 1576486 3550913 := bstep (se 2 (by rfl) ⟨1331592, by rfl⟩ : syracuseStep 3550913 = 2663185) B2663185
theorem B1576651 : Blo 1576486 1576651 := bstep (se 1 (by rfl) ⟨1182488, by rfl⟩ : syracuseStep 1576651 = 2364977) B2364977
theorem B1576663 : Blo 1576486 1576663 := bstep (se 1 (by rfl) ⟨1182497, by rfl⟩ : syracuseStep 1576663 = 2364995) B2364995
theorem B1576683 : Blo 1576486 1576683 := bstep (se 1 (by rfl) ⟨1182512, by rfl⟩ : syracuseStep 1576683 = 2365025) B2365025
theorem B24293105 : Blo 1576486 24293105 := bstep (se 2 (by rfl) ⟨9109914, by rfl⟩ : syracuseStep 24293105 = 18219829) B18219829
theorem B1576695 : Blo 1576486 1576695 := bstep (se 1 (by rfl) ⟨1182521, by rfl⟩ : syracuseStep 1576695 = 2365043) B2365043
theorem B1576715 : Blo 1576486 1576715 := bstep (se 1 (by rfl) ⟨1182536, by rfl⟩ : syracuseStep 1576715 = 2365073) B2365073
theorem B1576727 : Blo 1576486 1576727 := bstep (se 1 (by rfl) ⟨1182545, by rfl⟩ : syracuseStep 1576727 = 2365091) B2365091
theorem B1576747 : Blo 1576486 1576747 := bstep (se 1 (by rfl) ⟨1182560, by rfl⟩ : syracuseStep 1576747 = 2365121) B2365121
theorem B1576759 : Blo 1576486 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B3370817 : Blo 1576486 3370817 := bstep (se 2 (by rfl) ⟨1264056, by rfl⟩ : syracuseStep 3370817 = 2528113) B2528113
theorem B1576779 : Blo 1576486 1576779 := bstep (se 1 (by rfl) ⟨1182584, by rfl⟩ : syracuseStep 1576779 = 2365169) B2365169
theorem B1576791 : Blo 1576486 1576791 := bstep (se 1 (by rfl) ⟨1182593, by rfl⟩ : syracuseStep 1576791 = 2365187) B2365187
theorem B3788633 : Blo 1576486 3788633 := bstep (se 2 (by rfl) ⟨1420737, by rfl⟩ : syracuseStep 3788633 = 2841475) B2841475
theorem B8982373 : Blo 1576486 8982373 := bstep (se 4 (by rfl) ⟨842097, by rfl⟩ : syracuseStep 8982373 = 1684195) B1684195
theorem B1576811 : Blo 1576486 1576811 := bstep (se 1 (by rfl) ⟨1182608, by rfl⟩ : syracuseStep 1576811 = 2365217) B2365217
theorem B20213621 : Blo 1576486 20213621 := bstep (se 5 (by rfl) ⟨947513, by rfl⟩ : syracuseStep 20213621 = 1895027) B1895027
theorem B1576823 : Blo 1576486 1576823 := bstep (se 1 (by rfl) ⟨1182617, by rfl⟩ : syracuseStep 1576823 = 2365235) B2365235
theorem B1576843 : Blo 1576486 1576843 := bstep (se 1 (by rfl) ⟨1182632, by rfl⟩ : syracuseStep 1576843 = 2365265) B2365265
theorem B1576855 : Blo 1576486 1576855 := bstep (se 1 (by rfl) ⟨1182641, by rfl⟩ : syracuseStep 1576855 = 2365283) B2365283
theorem B3551129 : Blo 1576486 3551129 := bstep (se 2 (by rfl) ⟨1331673, by rfl⟩ : syracuseStep 3551129 = 2663347) B2663347
theorem B1576875 : Blo 1576486 1576875 := bstep (se 1 (by rfl) ⟨1182656, by rfl⟩ : syracuseStep 1576875 = 2365313) B2365313
theorem B1576887 : Blo 1576486 1576887 := bstep (se 1 (by rfl) ⟨1182665, by rfl⟩ : syracuseStep 1576887 = 2365331) B2365331
theorem B1576907 : Blo 1576486 1576907 := bstep (se 1 (by rfl) ⟨1182680, by rfl⟩ : syracuseStep 1576907 = 2365361) B2365361
theorem B1576919 : Blo 1576486 1576919 := bstep (se 1 (by rfl) ⟨1182689, by rfl⟩ : syracuseStep 1576919 = 2365379) B2365379
theorem B1576939 : Blo 1576486 1576939 := bstep (se 1 (by rfl) ⟨1182704, by rfl⟩ : syracuseStep 1576939 = 2365409) B2365409
theorem B3551219 : Blo 1576486 3551219 := bstep (se 1 (by rfl) ⟨2663414, by rfl⟩ : syracuseStep 3551219 = 5326829) B5326829
theorem B1576951 : Blo 1576486 1576951 := bstep (se 1 (by rfl) ⟨1182713, by rfl⟩ : syracuseStep 1576951 = 2365427) B2365427
theorem B1576971 : Blo 1576486 1576971 := bstep (se 1 (by rfl) ⟨1182728, by rfl⟩ : syracuseStep 1576971 = 2365457) B2365457
theorem B5320727 : Blo 1576486 5320727 := bstep (se 1 (by rfl) ⟨3990545, by rfl⟩ : syracuseStep 5320727 = 7981091) B7981091
theorem B1576983 : Blo 1576486 1576983 := bstep (se 1 (by rfl) ⟨1182737, by rfl⟩ : syracuseStep 1576983 = 2365475) B2365475
theorem B3551255 : Blo 1576486 3551255 := bstep (se 1 (by rfl) ⟨2663441, by rfl⟩ : syracuseStep 3551255 = 5326883) B5326883
theorem B1577003 : Blo 1576486 1577003 := bstep (se 1 (by rfl) ⟨1182752, by rfl⟩ : syracuseStep 1577003 = 2365505) B2365505
theorem B1577015 : Blo 1576486 1577015 := bstep (se 1 (by rfl) ⟨1182761, by rfl⟩ : syracuseStep 1577015 = 2365523) B2365523
theorem B1773643 : Blo 1576486 1773643 := bstep (se 1 (by rfl) ⟨1330232, by rfl⟩ : syracuseStep 1773643 = 2660465) B2660465
theorem B1577035 : Blo 1576486 1577035 := bstep (se 1 (by rfl) ⟨1182776, by rfl⟩ : syracuseStep 1577035 = 2365553) B2365553
theorem B1921099 : Blo 1576486 1921099 := bstep (se 1 (by rfl) ⟨1440824, by rfl⟩ : syracuseStep 1921099 = 2881649) B2881649
theorem B1577047 : Blo 1576486 1577047 := bstep (se 1 (by rfl) ⟨1182785, by rfl⟩ : syracuseStep 1577047 = 2365571) B2365571
theorem B7983197 : Blo 1576486 7983197 := bstep (se 3 (by rfl) ⟨1496849, by rfl⟩ : syracuseStep 7983197 = 2993699) B2993699
theorem B1683563 : Blo 1576486 1683563 := bstep (se 1 (by rfl) ⟨1262672, by rfl⟩ : syracuseStep 1683563 = 2525345) B2525345
theorem B1577067 : Blo 1576486 1577067 := bstep (se 1 (by rfl) ⟨1182800, by rfl⟩ : syracuseStep 1577067 = 2365601) B2365601
theorem B1577079 : Blo 1576486 1577079 := bstep (se 1 (by rfl) ⟨1182809, by rfl⟩ : syracuseStep 1577079 = 2365619) B2365619
theorem B19181699 : Blo 1576486 19181699 := bstep (se 1 (by rfl) ⟨14386274, by rfl⟩ : syracuseStep 19181699 = 28772549) B28772549
theorem B1577099 : Blo 1576486 1577099 := bstep (se 1 (by rfl) ⟨1182824, by rfl⟩ : syracuseStep 1577099 = 2365649) B2365649
theorem B1577111 : Blo 1576486 1577111 := bstep (se 1 (by rfl) ⟨1182833, by rfl⟩ : syracuseStep 1577111 = 2365667) B2365667
theorem B3371159 : Blo 1576486 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B1577131 : Blo 1576486 1577131 := bstep (se 1 (by rfl) ⟨1182848, by rfl⟩ : syracuseStep 1577131 = 2365697) B2365697
theorem B1773751 : Blo 1576486 1773751 := bstep (se 1 (by rfl) ⟨1330313, by rfl⟩ : syracuseStep 1773751 = 2660627) B2660627
theorem B1577143 : Blo 1576486 1577143 := bstep (se 1 (by rfl) ⟨1182857, by rfl⟩ : syracuseStep 1577143 = 2365715) B2365715
theorem B1577163 : Blo 1576486 1577163 := bstep (se 1 (by rfl) ⟨1182872, by rfl⟩ : syracuseStep 1577163 = 2365745) B2365745
theorem B3551435 : Blo 1576486 3551435 := bstep (se 1 (by rfl) ⟨2663576, by rfl⟩ : syracuseStep 3551435 = 5327153) B5327153
theorem B1577175 : Blo 1576486 1577175 := bstep (se 1 (by rfl) ⟨1182881, by rfl⟩ : syracuseStep 1577175 = 2365763) B2365763
theorem B1577195 : Blo 1576486 1577195 := bstep (se 1 (by rfl) ⟨1182896, by rfl⟩ : syracuseStep 1577195 = 2365793) B2365793
theorem B1577207 : Blo 1576486 1577207 := bstep (se 1 (by rfl) ⟨1182905, by rfl⟩ : syracuseStep 1577207 = 2365811) B2365811
theorem B3551489 : Blo 1576486 3551489 := bstep (se 2 (by rfl) ⟨1331808, by rfl⟩ : syracuseStep 3551489 = 2663617) B2663617
theorem B1577227 : Blo 1576486 1577227 := bstep (se 1 (by rfl) ⟨1182920, by rfl⟩ : syracuseStep 1577227 = 2365841) B2365841
theorem B1577239 : Blo 1576486 1577239 := bstep (se 1 (by rfl) ⟨1182929, by rfl⟩ : syracuseStep 1577239 = 2365859) B2365859
theorem B1577259 : Blo 1576486 1577259 := bstep (se 1 (by rfl) ⟨1182944, by rfl⟩ : syracuseStep 1577259 = 2365889) B2365889
theorem B35049773 : Blo 1576486 35049773 := bstep (se 3 (by rfl) ⟨6571832, by rfl⟩ : syracuseStep 35049773 = 13143665) B13143665
theorem B3993907 : Blo 1576486 3993907 := bstep (se 1 (by rfl) ⟨2995430, by rfl⟩ : syracuseStep 3993907 = 5990861) B5990861
theorem B1577271 : Blo 1576486 1577271 := bstep (se 1 (by rfl) ⟨1182953, by rfl⟩ : syracuseStep 1577271 = 2365907) B2365907
theorem B1577291 : Blo 1576486 1577291 := bstep (se 1 (by rfl) ⟨1182968, by rfl⟩ : syracuseStep 1577291 = 2365937) B2365937
theorem B1577303 : Blo 1576486 1577303 := bstep (se 1 (by rfl) ⟨1182977, by rfl⟩ : syracuseStep 1577303 = 2365955) B2365955
theorem B1773931 : Blo 1576486 1773931 := bstep (se 1 (by rfl) ⟨1330448, by rfl⟩ : syracuseStep 1773931 = 2660897) B2660897
theorem B1577323 : Blo 1576486 1577323 := bstep (se 1 (by rfl) ⟨1182992, by rfl⟩ : syracuseStep 1577323 = 2365985) B2365985
theorem B1577335 : Blo 1576486 1577335 := bstep (se 1 (by rfl) ⟨1183001, by rfl⟩ : syracuseStep 1577335 = 2366003) B2366003
theorem B1577355 : Blo 1576486 1577355 := bstep (se 1 (by rfl) ⟨1183016, by rfl⟩ : syracuseStep 1577355 = 2366033) B2366033
theorem B1577367 : Blo 1576486 1577367 := bstep (se 1 (by rfl) ⟨1183025, by rfl⟩ : syracuseStep 1577367 = 2366051) B2366051
theorem B1577387 : Blo 1576486 1577387 := bstep (se 1 (by rfl) ⟨1183040, by rfl⟩ : syracuseStep 1577387 = 2366081) B2366081
theorem B1577399 : Blo 1576486 1577399 := bstep (se 1 (by rfl) ⟨1183049, by rfl⟩ : syracuseStep 1577399 = 2366099) B2366099
theorem B3994049 : Blo 1576486 3994049 := bstep (se 2 (by rfl) ⟨1497768, by rfl⟩ : syracuseStep 3994049 = 2995537) B2995537
theorem B1577419 : Blo 1576486 1577419 := bstep (se 1 (by rfl) ⟨1183064, by rfl⟩ : syracuseStep 1577419 = 2366129) B2366129
theorem B1774039 : Blo 1576486 1774039 := bstep (se 1 (by rfl) ⟨1330529, by rfl⟩ : syracuseStep 1774039 = 2661059) B2661059
theorem B1577431 : Blo 1576486 1577431 := bstep (se 1 (by rfl) ⟨1183073, by rfl⟩ : syracuseStep 1577431 = 2366147) B2366147
theorem B2527703 : Blo 1576486 2527703 := bstep (se 1 (by rfl) ⟨1895777, by rfl⟩ : syracuseStep 2527703 = 3791555) B3791555
theorem B1577451 : Blo 1576486 1577451 := bstep (se 1 (by rfl) ⟨1183088, by rfl⟩ : syracuseStep 1577451 = 2366177) B2366177
theorem B1577463 : Blo 1576486 1577463 := bstep (se 1 (by rfl) ⟨1183097, by rfl⟩ : syracuseStep 1577463 = 2366195) B2366195
theorem B1577483 : Blo 1576486 1577483 := bstep (se 1 (by rfl) ⟨1183112, by rfl⟩ : syracuseStep 1577483 = 2366225) B2366225
theorem B1577495 : Blo 1576486 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B1577515 : Blo 1576486 1577515 := bstep (se 1 (by rfl) ⟨1183136, by rfl⟩ : syracuseStep 1577515 = 2366273) B2366273
theorem B11981357 : Blo 1576486 11981357 := bstep (se 3 (by rfl) ⟨2246504, by rfl⟩ : syracuseStep 11981357 = 4493009) B4493009
theorem B5321267 : Blo 1576486 5321267 := bstep (se 1 (by rfl) ⟨3990950, by rfl⟩ : syracuseStep 5321267 = 7981901) B7981901
theorem B4493875 : Blo 1576486 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B1577527 : Blo 1576486 1577527 := bstep (se 1 (by rfl) ⟨1183145, by rfl⟩ : syracuseStep 1577527 = 2366291) B2366291
theorem B5050945 : Blo 1576486 5050945 := bstep (se 2 (by rfl) ⟨1894104, by rfl⟩ : syracuseStep 5050945 = 3788209) B3788209
theorem B1577547 : Blo 1576486 1577547 := bstep (se 1 (by rfl) ⟨1183160, by rfl⟩ : syracuseStep 1577547 = 2366321) B2366321
theorem B1577559 : Blo 1576486 1577559 := bstep (se 1 (by rfl) ⟨1183169, by rfl⟩ : syracuseStep 1577559 = 2366339) B2366339
theorem B1577579 : Blo 1576486 1577579 := bstep (se 1 (by rfl) ⟨1183184, by rfl⟩ : syracuseStep 1577579 = 2366369) B2366369
theorem B3199603 : Blo 1576486 3199603 := bstep (se 1 (by rfl) ⟨2399702, by rfl⟩ : syracuseStep 3199603 = 4799405) B4799405
theorem B1577591 : Blo 1576486 1577591 := bstep (se 1 (by rfl) ⟨1183193, by rfl⟩ : syracuseStep 1577591 = 2366387) B2366387
theorem B1774219 : Blo 1576486 1774219 := bstep (se 1 (by rfl) ⟨1330664, by rfl⟩ : syracuseStep 1774219 = 2661329) B2661329
theorem B1577611 : Blo 1576486 1577611 := bstep (se 1 (by rfl) ⟨1183208, by rfl⟩ : syracuseStep 1577611 = 2366417) B2366417
theorem B1577623 : Blo 1576486 1577623 := bstep (se 1 (by rfl) ⟨1183217, by rfl⟩ : syracuseStep 1577623 = 2366435) B2366435
theorem B2527895 : Blo 1576486 2527895 := bstep (se 1 (by rfl) ⟨1895921, by rfl⟩ : syracuseStep 2527895 = 3791843) B3791843
theorem B1577643 : Blo 1576486 1577643 := bstep (se 1 (by rfl) ⟨1183232, by rfl⟩ : syracuseStep 1577643 = 2366465) B2366465
theorem B1577655 : Blo 1576486 1577655 := bstep (se 1 (by rfl) ⟨1183241, by rfl⟩ : syracuseStep 1577655 = 2366483) B2366483
theorem B1577675 : Blo 1576486 1577675 := bstep (se 1 (by rfl) ⟨1183256, by rfl⟩ : syracuseStep 1577675 = 2366513) B2366513
theorem B1577687 : Blo 1576486 1577687 := bstep (se 1 (by rfl) ⟨1183265, by rfl⟩ : syracuseStep 1577687 = 2366531) B2366531
theorem B1577707 : Blo 1576486 1577707 := bstep (se 1 (by rfl) ⟨1183280, by rfl⟩ : syracuseStep 1577707 = 2366561) B2366561
theorem B1774327 : Blo 1576486 1774327 := bstep (se 1 (by rfl) ⟨1330745, by rfl⟩ : syracuseStep 1774327 = 2661491) B2661491
theorem B1577719 : Blo 1576486 1577719 := bstep (se 1 (by rfl) ⟨1183289, by rfl⟩ : syracuseStep 1577719 = 2366579) B2366579
theorem B27316997 : Blo 1576486 27316997 := bstep (se 4 (by rfl) ⟨2560968, by rfl⟩ : syracuseStep 27316997 = 5121937) B5121937
theorem B1577739 : Blo 1576486 1577739 := bstep (se 1 (by rfl) ⟨1183304, by rfl⟩ : syracuseStep 1577739 = 2366609) B2366609
theorem B1577751 : Blo 1576486 1577751 := bstep (se 1 (by rfl) ⟨1183313, by rfl⟩ : syracuseStep 1577751 = 2366627) B2366627
theorem B1577771 : Blo 1576486 1577771 := bstep (se 1 (by rfl) ⟨1183328, by rfl⟩ : syracuseStep 1577771 = 2366657) B2366657
theorem B5993261 : Blo 1576486 5993261 := bstep (se 3 (by rfl) ⟨1123736, by rfl⟩ : syracuseStep 5993261 = 2247473) B2247473
theorem B1577783 : Blo 1576486 1577783 := bstep (se 1 (by rfl) ⟨1183337, by rfl⟩ : syracuseStep 1577783 = 2366675) B2366675
theorem B5321537 : Blo 1576486 5321537 := bstep (se 2 (by rfl) ⟨1995576, by rfl⟩ : syracuseStep 5321537 = 3991153) B3991153
theorem B1577803 : Blo 1576486 1577803 := bstep (se 1 (by rfl) ⟨1183352, by rfl⟩ : syracuseStep 1577803 = 2366705) B2366705
theorem B5993291 : Blo 1576486 5993291 := bstep (se 1 (by rfl) ⟨4494968, by rfl⟩ : syracuseStep 5993291 = 8989937) B8989937
theorem B1995607 : Blo 1576486 1995607 := bstep (se 1 (by rfl) ⟨1496705, by rfl⟩ : syracuseStep 1995607 = 2993411) B2993411
theorem B1577815 : Blo 1576486 1577815 := bstep (se 1 (by rfl) ⟨1183361, by rfl⟩ : syracuseStep 1577815 = 2366723) B2366723
theorem B1577835 : Blo 1576486 1577835 := bstep (se 1 (by rfl) ⟨1183376, by rfl⟩ : syracuseStep 1577835 = 2366753) B2366753
theorem B1577847 : Blo 1576486 1577847 := bstep (se 1 (by rfl) ⟨1183385, by rfl⟩ : syracuseStep 1577847 = 2366771) B2366771
theorem B1577867 : Blo 1576486 1577867 := bstep (se 1 (by rfl) ⟨1183400, by rfl⟩ : syracuseStep 1577867 = 2366801) B2366801
theorem B1577879 : Blo 1576486 1577879 := bstep (se 1 (by rfl) ⟨1183409, by rfl⟩ : syracuseStep 1577879 = 2366819) B2366819
theorem B1774507 : Blo 1576486 1774507 := bstep (se 1 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 1774507 = 2661761) B2661761
theorem B1577899 : Blo 1576486 1577899 := bstep (se 1 (by rfl) ⟨1183424, by rfl⟩ : syracuseStep 1577899 = 2366849) B2366849
theorem B3036083 : Blo 1576486 3036083 := bstep (se 1 (by rfl) ⟨2277062, by rfl⟩ : syracuseStep 3036083 = 4554125) B4554125
theorem B1577911 : Blo 1576486 1577911 := bstep (se 1 (by rfl) ⟨1183433, by rfl⟩ : syracuseStep 1577911 = 2366867) B2366867
theorem B1577931 : Blo 1576486 1577931 := bstep (se 1 (by rfl) ⟨1183448, by rfl⟩ : syracuseStep 1577931 = 2366897) B2366897
theorem B11973581 : Blo 1576486 11973581 := bstep (se 3 (by rfl) ⟨2245046, by rfl⟩ : syracuseStep 11973581 = 4490093) B4490093
theorem B1577943 : Blo 1576486 1577943 := bstep (se 1 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 1577943 = 2366915) B2366915
theorem B1577963 : Blo 1576486 1577963 := bstep (se 1 (by rfl) ⟨1183472, by rfl⟩ : syracuseStep 1577963 = 2366945) B2366945
theorem B1577975 : Blo 1576486 1577975 := bstep (se 1 (by rfl) ⟨1183481, by rfl⟩ : syracuseStep 1577975 = 2366963) B2366963
theorem B2995211 : Blo 1576486 2995211 := bstep (se 1 (by rfl) ⟨2246408, by rfl⟩ : syracuseStep 2995211 = 4492817) B4492817
theorem B1577995 : Blo 1576486 1577995 := bstep (se 1 (by rfl) ⟨1183496, by rfl⟩ : syracuseStep 1577995 = 2366993) B2366993
theorem B1774615 : Blo 1576486 1774615 := bstep (se 1 (by rfl) ⟨1330961, by rfl⟩ : syracuseStep 1774615 = 2661923) B2661923
theorem B6738967 : Blo 1576486 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B1578007 : Blo 1576486 1578007 := bstep (se 1 (by rfl) ⟨1183505, by rfl⟩ : syracuseStep 1578007 = 2367011) B2367011
theorem B1578027 : Blo 1576486 1578027 := bstep (se 1 (by rfl) ⟨1183520, by rfl⟩ : syracuseStep 1578027 = 2367041) B2367041
theorem B6394925 : Blo 1576486 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B1578039 : Blo 1576486 1578039 := bstep (se 1 (by rfl) ⟨1183529, by rfl⟩ : syracuseStep 1578039 = 2367059) B2367059
theorem B1578059 : Blo 1576486 1578059 := bstep (se 1 (by rfl) ⟨1183544, by rfl⟩ : syracuseStep 1578059 = 2367089) B2367089
theorem B1684567 : Blo 1576486 1684567 := bstep (se 1 (by rfl) ⟨1263425, by rfl⟩ : syracuseStep 1684567 = 2526851) B2526851
theorem B1578071 : Blo 1576486 1578071 := bstep (se 1 (by rfl) ⟨1183553, by rfl⟩ : syracuseStep 1578071 = 2367107) B2367107
theorem B6739037 : Blo 1576486 6739037 := bstep (se 3 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 6739037 = 2527139) B2527139
theorem B1578091 : Blo 1576486 1578091 := bstep (se 1 (by rfl) ⟨1183568, by rfl⟩ : syracuseStep 1578091 = 2367137) B2367137
theorem B1578103 : Blo 1576486 1578103 := bstep (se 1 (by rfl) ⟨1183577, by rfl⟩ : syracuseStep 1578103 = 2367155) B2367155
theorem B1578123 : Blo 1576486 1578123 := bstep (se 1 (by rfl) ⟨1183592, by rfl⟩ : syracuseStep 1578123 = 2367185) B2367185
theorem B40989847 : Blo 1576486 40989847 := bstep (se 1 (by rfl) ⟨30742385, by rfl⟩ : syracuseStep 40989847 = 61484771) B61484771
theorem B1578135 : Blo 1576486 1578135 := bstep (se 1 (by rfl) ⟨1183601, by rfl⟩ : syracuseStep 1578135 = 2367203) B2367203
theorem B1578155 : Blo 1576486 1578155 := bstep (se 1 (by rfl) ⟨1183616, by rfl⟩ : syracuseStep 1578155 = 2367233) B2367233
theorem B1578167 : Blo 1576486 1578167 := bstep (se 1 (by rfl) ⟨1183625, by rfl⟩ : syracuseStep 1578167 = 2367251) B2367251
theorem B2995393 : Blo 1576486 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B1774795 : Blo 1576486 1774795 := bstep (se 1 (by rfl) ⟨1331096, by rfl⟩ : syracuseStep 1774795 = 2662193) B2662193
theorem B1578187 : Blo 1576486 1578187 := bstep (se 1 (by rfl) ⟨1183640, by rfl⟩ : syracuseStep 1578187 = 2367281) B2367281
theorem B1578199 : Blo 1576486 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B1578219 : Blo 1576486 1578219 := bstep (se 1 (by rfl) ⟨1183664, by rfl⟩ : syracuseStep 1578219 = 2367329) B2367329
theorem B1578231 : Blo 1576486 1578231 := bstep (se 1 (by rfl) ⟨1183673, by rfl⟩ : syracuseStep 1578231 = 2367347) B2367347
theorem B14587141 : Blo 1576486 14587141 := bstep (se 4 (by rfl) ⟨1367544, by rfl⟩ : syracuseStep 14587141 = 2735089) B2735089
theorem B1578251 : Blo 1576486 1578251 := bstep (se 1 (by rfl) ⟨1183688, by rfl⟩ : syracuseStep 1578251 = 2367377) B2367377
theorem B1578263 : Blo 1576486 1578263 := bstep (se 1 (by rfl) ⟨1183697, by rfl⟩ : syracuseStep 1578263 = 2367395) B2367395
theorem B1578283 : Blo 1576486 1578283 := bstep (se 1 (by rfl) ⟨1183712, by rfl⟩ : syracuseStep 1578283 = 2367425) B2367425
theorem B1774903 : Blo 1576486 1774903 := bstep (se 1 (by rfl) ⟨1331177, by rfl⟩ : syracuseStep 1774903 = 2662355) B2662355
theorem B1578295 : Blo 1576486 1578295 := bstep (se 1 (by rfl) ⟨1183721, by rfl⟩ : syracuseStep 1578295 = 2367443) B2367443
theorem B1578315 : Blo 1576486 1578315 := bstep (se 1 (by rfl) ⟨1183736, by rfl⟩ : syracuseStep 1578315 = 2367473) B2367473
theorem B1578327 : Blo 1576486 1578327 := bstep (se 1 (by rfl) ⟨1183745, by rfl⟩ : syracuseStep 1578327 = 2367491) B2367491
theorem B2364761 : Blo 1576486 2364761 := bstep (se 2 (by rfl) ⟨886785, by rfl⟩ : syracuseStep 2364761 = 1773571) B1773571
theorem B5322077 : Blo 1576486 5322077 := bstep (se 3 (by rfl) ⟨997889, by rfl⟩ : syracuseStep 5322077 = 1995779) B1995779
theorem B1578347 : Blo 1576486 1578347 := bstep (se 1 (by rfl) ⟨1183760, by rfl⟩ : syracuseStep 1578347 = 2367521) B2367521
theorem B1578359 : Blo 1576486 1578359 := bstep (se 1 (by rfl) ⟨1183769, by rfl⟩ : syracuseStep 1578359 = 2367539) B2367539
theorem B3413377 : Blo 1576486 3413377 := bstep (se 2 (by rfl) ⟨1280016, by rfl⟩ : syracuseStep 3413377 = 2560033) B2560033
theorem B1578379 : Blo 1576486 1578379 := bstep (se 1 (by rfl) ⟨1183784, by rfl⟩ : syracuseStep 1578379 = 2367569) B2367569
theorem B1578391 : Blo 1576486 1578391 := bstep (se 1 (by rfl) ⟨1183793, by rfl⟩ : syracuseStep 1578391 = 2367587) B2367587
theorem B1578411 : Blo 1576486 1578411 := bstep (se 1 (by rfl) ⟨1183808, by rfl⟩ : syracuseStep 1578411 = 2367617) B2367617
theorem B11974067 : Blo 1576486 11974067 := bstep (se 1 (by rfl) ⟨8980550, by rfl⟩ : syracuseStep 11974067 = 17961101) B17961101
theorem B1578423 : Blo 1576486 1578423 := bstep (se 1 (by rfl) ⟨1183817, by rfl⟩ : syracuseStep 1578423 = 2367635) B2367635
theorem B3413441 : Blo 1576486 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2364875 : Blo 1576486 2364875 := bstep (se 1 (by rfl) ⟨1773656, by rfl⟩ : syracuseStep 2364875 = 3547313) B3547313
theorem B1578443 : Blo 1576486 1578443 := bstep (se 1 (by rfl) ⟨1183832, by rfl⟩ : syracuseStep 1578443 = 2367665) B2367665
theorem B2364887 : Blo 1576486 2364887 := bstep (se 1 (by rfl) ⟨1773665, by rfl⟩ : syracuseStep 2364887 = 3547331) B3547331
theorem B3036631 : Blo 1576486 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B1578455 : Blo 1576486 1578455 := bstep (se 1 (by rfl) ⟨1183841, by rfl⟩ : syracuseStep 1578455 = 2367683) B2367683
theorem B1775083 : Blo 1576486 1775083 := bstep (se 1 (by rfl) ⟨1331312, by rfl⟩ : syracuseStep 1775083 = 2662625) B2662625
theorem B1578475 : Blo 1576486 1578475 := bstep (se 1 (by rfl) ⟨1183856, by rfl⟩ : syracuseStep 1578475 = 2367713) B2367713
theorem B2364953 : Blo 1576486 2364953 := bstep (se 2 (by rfl) ⟨886857, by rfl⟩ : syracuseStep 2364953 = 1773715) B1773715
theorem B4494923 : Blo 1576486 4494923 := bstep (se 1 (by rfl) ⟨3371192, by rfl⟩ : syracuseStep 4494923 = 6742385) B6742385
theorem B1775191 : Blo 1576486 1775191 := bstep (se 1 (by rfl) ⟨1331393, by rfl⟩ : syracuseStep 1775191 = 2662787) B2662787
theorem B21575261 : Blo 1576486 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B2995841 : Blo 1576486 2995841 := bstep (se 2 (by rfl) ⟨1123440, by rfl⟩ : syracuseStep 2995841 = 2246881) B2246881
theorem B2365067 : Blo 1576486 2365067 := bstep (se 1 (by rfl) ⟨1773800, by rfl⟩ : syracuseStep 2365067 = 3547601) B3547601
theorem B1996427 : Blo 1576486 1996427 := bstep (se 1 (by rfl) ⟨1497320, by rfl⟩ : syracuseStep 1996427 = 2994641) B2994641
theorem B2365079 : Blo 1576486 2365079 := bstep (se 1 (by rfl) ⟨1773809, by rfl⟩ : syracuseStep 2365079 = 3547619) B3547619
theorem B5985971 : Blo 1576486 5985971 := bstep (se 1 (by rfl) ⟨4489478, by rfl⟩ : syracuseStep 5985971 = 8978957) B8978957
theorem B1799863 : Blo 1576486 1799863 := bstep (se 1 (by rfl) ⟨1349897, by rfl⟩ : syracuseStep 1799863 = 2699795) B2699795
theorem B3995315 : Blo 1576486 3995315 := bstep (se 1 (by rfl) ⟨2996486, by rfl⟩ : syracuseStep 3995315 = 5992973) B5992973
theorem B26965709 : Blo 1576486 26965709 := bstep (se 3 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 26965709 = 10112141) B10112141
theorem B2365145 : Blo 1576486 2365145 := bstep (se 2 (by rfl) ⟨886929, by rfl⟩ : syracuseStep 2365145 = 1773859) B1773859
theorem B5052125 : Blo 1576486 5052125 := bstep (se 3 (by rfl) ⟨947273, by rfl⟩ : syracuseStep 5052125 = 1894547) B1894547
theorem B1775371 : Blo 1576486 1775371 := bstep (se 1 (by rfl) ⟨1331528, by rfl⟩ : syracuseStep 1775371 = 2663057) B2663057
theorem B2365259 : Blo 1576486 2365259 := bstep (se 1 (by rfl) ⟨1773944, by rfl⟩ : syracuseStep 2365259 = 3547889) B3547889
theorem B6739787 : Blo 1576486 6739787 := bstep (se 1 (by rfl) ⟨5054840, by rfl⟩ : syracuseStep 6739787 = 10109681) B10109681
theorem B1685323 : Blo 1576486 1685323 := bstep (se 1 (by rfl) ⟨1263992, by rfl⟩ : syracuseStep 1685323 = 2527985) B2527985
theorem B2365271 : Blo 1576486 2365271 := bstep (se 1 (by rfl) ⟨1773953, by rfl⟩ : syracuseStep 2365271 = 3547907) B3547907
theorem B1775479 : Blo 1576486 1775479 := bstep (se 1 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 1775479 = 2663219) B2663219
theorem B2398103 : Blo 1576486 2398103 := bstep (se 1 (by rfl) ⟨1798577, by rfl⟩ : syracuseStep 2398103 = 3597155) B3597155
theorem B2365337 : Blo 1576486 2365337 := bstep (se 2 (by rfl) ⟨887001, by rfl⟩ : syracuseStep 2365337 = 1774003) B1774003
theorem B2996183 : Blo 1576486 2996183 := bstep (se 1 (by rfl) ⟨2247137, by rfl⟩ : syracuseStep 2996183 = 4494275) B4494275
theorem B2365451 : Blo 1576486 2365451 := bstep (se 1 (by rfl) ⟨1774088, by rfl⟩ : syracuseStep 2365451 = 3548177) B3548177
theorem B6567959 : Blo 1576486 6567959 := bstep (se 1 (by rfl) ⟨4925969, by rfl⟩ : syracuseStep 6567959 = 9851939) B9851939
theorem B2365463 : Blo 1576486 2365463 := bstep (se 1 (by rfl) ⟨1774097, by rfl⟩ : syracuseStep 2365463 = 3548195) B3548195
theorem B2660377 : Blo 1576486 2660377 := bstep (se 2 (by rfl) ⟨997641, by rfl⟩ : syracuseStep 2660377 = 1995283) B1995283
theorem B1775659 : Blo 1576486 1775659 := bstep (se 1 (by rfl) ⟨1331744, by rfl⟩ : syracuseStep 1775659 = 2663489) B2663489
theorem B2365529 : Blo 1576486 2365529 := bstep (se 2 (by rfl) ⟨887073, by rfl⟩ : syracuseStep 2365529 = 1774147) B1774147
theorem B9599077 : Blo 1576486 9599077 := bstep (se 4 (by rfl) ⟨899913, by rfl⟩ : syracuseStep 9599077 = 1799827) B1799827
theorem B7985303 : Blo 1576486 7985303 := bstep (se 1 (by rfl) ⟨5988977, by rfl⟩ : syracuseStep 7985303 = 11977955) B11977955
theorem B1775767 : Blo 1576486 1775767 := bstep (se 1 (by rfl) ⟨1331825, by rfl⟩ : syracuseStep 1775767 = 2663651) B2663651
theorem B13473971 : Blo 1576486 13473971 := bstep (se 1 (by rfl) ⟨10105478, by rfl⟩ : syracuseStep 13473971 = 20210957) B20210957
theorem B2365643 : Blo 1576486 2365643 := bstep (se 1 (by rfl) ⟨1774232, by rfl⟩ : syracuseStep 2365643 = 3548465) B3548465
theorem B2365655 : Blo 1576486 2365655 := bstep (se 1 (by rfl) ⟨1774241, by rfl⟩ : syracuseStep 2365655 = 3548483) B3548483
theorem B2365721 : Blo 1576486 2365721 := bstep (se 2 (by rfl) ⟨887145, by rfl⟩ : syracuseStep 2365721 = 1774291) B1774291
theorem B1997131 : Blo 1576486 1997131 := bstep (se 1 (by rfl) ⟨1497848, by rfl⟩ : syracuseStep 1997131 = 2995697) B2995697
theorem B2365835 : Blo 1576486 2365835 := bstep (se 1 (by rfl) ⟨1774376, by rfl⟩ : syracuseStep 2365835 = 3548753) B3548753
theorem B2365847 : Blo 1576486 2365847 := bstep (se 1 (by rfl) ⟨1774385, by rfl⟩ : syracuseStep 2365847 = 3548771) B3548771
theorem B6396353 : Blo 1576486 6396353 := bstep (se 2 (by rfl) ⟨2398632, by rfl⟩ : syracuseStep 6396353 = 4797265) B4797265
theorem B5323211 : Blo 1576486 5323211 := bstep (se 1 (by rfl) ⟨3992408, by rfl⟩ : syracuseStep 5323211 = 7984817) B7984817
theorem B2365913 : Blo 1576486 2365913 := bstep (se 2 (by rfl) ⟨887217, by rfl⟩ : syracuseStep 2365913 = 1774435) B1774435
theorem B5683729 : Blo 1576486 5683729 := bstep (se 2 (by rfl) ⟨2131398, by rfl⟩ : syracuseStep 5683729 = 4262797) B4262797
theorem B13474349 : Blo 1576486 13474349 := bstep (se 3 (by rfl) ⟨2526440, by rfl⟩ : syracuseStep 13474349 = 5052881) B5052881
theorem B4799027 : Blo 1576486 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B2366027 : Blo 1576486 2366027 := bstep (se 1 (by rfl) ⟨1774520, by rfl⟩ : syracuseStep 2366027 = 3549041) B3549041
theorem B2660951 : Blo 1576486 2660951 := bstep (se 1 (by rfl) ⟨1995713, by rfl⟩ : syracuseStep 2660951 = 3991427) B3991427
theorem B2366039 : Blo 1576486 2366039 := bstep (se 1 (by rfl) ⟨1774529, by rfl⟩ : syracuseStep 2366039 = 3549059) B3549059
theorem B1997399 : Blo 1576486 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B2366105 : Blo 1576486 2366105 := bstep (se 2 (by rfl) ⟨887289, by rfl⟩ : syracuseStep 2366105 = 1774579) B1774579
theorem B15162061 : Blo 1576486 15162061 := bstep (se 3 (by rfl) ⟨2842886, by rfl⟩ : syracuseStep 15162061 = 5685773) B5685773
theorem B2661079 : Blo 1576486 2661079 := bstep (se 1 (by rfl) ⟨1995809, by rfl⟩ : syracuseStep 2661079 = 3991619) B3991619
theorem B5323481 : Blo 1576486 5323481 := bstep (se 2 (by rfl) ⟨1996305, by rfl⟩ : syracuseStep 5323481 = 3992611) B3992611
theorem B2841331 : Blo 1576486 2841331 := bstep (se 1 (by rfl) ⟨2130998, by rfl⟩ : syracuseStep 2841331 = 4261997) B4261997
theorem B2366219 : Blo 1576486 2366219 := bstep (se 1 (by rfl) ⟨1774664, by rfl⟩ : syracuseStep 2366219 = 3549329) B3549329
theorem B2366231 : Blo 1576486 2366231 := bstep (se 1 (by rfl) ⟨1774673, by rfl⟩ : syracuseStep 2366231 = 3549347) B3549347
theorem B7199563 : Blo 1576486 7199563 := bstep (se 1 (by rfl) ⟨5399672, by rfl⟩ : syracuseStep 7199563 = 10799345) B10799345
theorem B2366297 : Blo 1576486 2366297 := bstep (se 2 (by rfl) ⟨887361, by rfl⟩ : syracuseStep 2366297 = 1774723) B1774723
theorem B11975525 : Blo 1576486 11975525 := bstep (se 4 (by rfl) ⟨1122705, by rfl⟩ : syracuseStep 11975525 = 2245411) B2245411
theorem B2366411 : Blo 1576486 2366411 := bstep (se 1 (by rfl) ⟨1774808, by rfl⟩ : syracuseStep 2366411 = 3549617) B3549617
theorem B2366423 : Blo 1576486 2366423 := bstep (se 1 (by rfl) ⟨1774817, by rfl⟩ : syracuseStep 2366423 = 3549635) B3549635
theorem B7191517 : Blo 1576486 7191517 := bstep (se 3 (by rfl) ⟨1348409, by rfl⟩ : syracuseStep 7191517 = 2696819) B2696819
theorem B7191575 : Blo 1576486 7191575 := bstep (se 1 (by rfl) ⟨5393681, by rfl⟩ : syracuseStep 7191575 = 10787363) B10787363
theorem B2366489 : Blo 1576486 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B5987459 : Blo 1576486 5987459 := bstep (se 1 (by rfl) ⟨4490594, by rfl⟩ : syracuseStep 5987459 = 8981189) B8981189
theorem B2366603 : Blo 1576486 2366603 := bstep (se 1 (by rfl) ⟨1774952, by rfl⟩ : syracuseStep 2366603 = 3549905) B3549905
theorem B2366615 : Blo 1576486 2366615 := bstep (se 1 (by rfl) ⟨1774961, by rfl⟩ : syracuseStep 2366615 = 3549923) B3549923
theorem B2366681 : Blo 1576486 2366681 := bstep (se 2 (by rfl) ⟨887505, by rfl⟩ : syracuseStep 2366681 = 1775011) B1775011
theorem B11976011 : Blo 1576486 11976011 := bstep (se 1 (by rfl) ⟨8982008, by rfl⟩ : syracuseStep 11976011 = 17964017) B17964017
theorem B2661707 : Blo 1576486 2661707 := bstep (se 1 (by rfl) ⟨1996280, by rfl⟩ : syracuseStep 2661707 = 3992561) B3992561
theorem B2366795 : Blo 1576486 2366795 := bstep (se 1 (by rfl) ⟨1775096, by rfl⟩ : syracuseStep 2366795 = 3550193) B3550193
theorem B2366807 : Blo 1576486 2366807 := bstep (se 1 (by rfl) ⟨1775105, by rfl⟩ : syracuseStep 2366807 = 3550211) B3550211
theorem B5324183 : Blo 1576486 5324183 := bstep (se 1 (by rfl) ⟨3993137, by rfl⟩ : syracuseStep 5324183 = 7986275) B7986275
theorem B2366873 : Blo 1576486 2366873 := bstep (se 2 (by rfl) ⟨887577, by rfl⟩ : syracuseStep 2366873 = 1775155) B1775155
theorem B2661835 : Blo 1576486 2661835 := bstep (se 1 (by rfl) ⟨1996376, by rfl⟩ : syracuseStep 2661835 = 3992753) B3992753
theorem B11369933 : Blo 1576486 11369933 := bstep (se 3 (by rfl) ⟨2131862, by rfl⟩ : syracuseStep 11369933 = 4263725) B4263725
theorem B2366987 : Blo 1576486 2366987 := bstep (se 1 (by rfl) ⟨1775240, by rfl⟩ : syracuseStep 2366987 = 3550481) B3550481
theorem B2366999 : Blo 1576486 2366999 := bstep (se 1 (by rfl) ⟨1775249, by rfl⟩ : syracuseStep 2366999 = 3550499) B3550499
theorem B5987915 : Blo 1576486 5987915 := bstep (se 1 (by rfl) ⟨4490936, by rfl⟩ : syracuseStep 5987915 = 8981873) B8981873
theorem B2661977 : Blo 1576486 2661977 := bstep (se 2 (by rfl) ⟨998241, by rfl⟩ : syracuseStep 2661977 = 1996483) B1996483
theorem B2367065 : Blo 1576486 2367065 := bstep (se 2 (by rfl) ⟨887649, by rfl⟩ : syracuseStep 2367065 = 1775299) B1775299
theorem B2367179 : Blo 1576486 2367179 := bstep (se 1 (by rfl) ⟨1775384, by rfl⟩ : syracuseStep 2367179 = 3550769) B3550769
theorem B2367191 : Blo 1576486 2367191 := bstep (se 1 (by rfl) ⟨1775393, by rfl⟩ : syracuseStep 2367191 = 3550787) B3550787
theorem B2662105 : Blo 1576486 2662105 := bstep (se 2 (by rfl) ⟨998289, by rfl⟩ : syracuseStep 2662105 = 1996579) B1996579
theorem B14786309 : Blo 1576486 14786309 := bstep (se 4 (by rfl) ⟨1386216, by rfl⟩ : syracuseStep 14786309 = 2772433) B2772433
theorem B5988113 : Blo 1576486 5988113 := bstep (se 2 (by rfl) ⟨2245542, by rfl⟩ : syracuseStep 5988113 = 4491085) B4491085
theorem B2367257 : Blo 1576486 2367257 := bstep (se 2 (by rfl) ⟨887721, by rfl⟩ : syracuseStep 2367257 = 1775443) B1775443
theorem B3841843 : Blo 1576486 3841843 := bstep (se 1 (by rfl) ⟨2881382, by rfl⟩ : syracuseStep 3841843 = 5762765) B5762765
theorem B2367371 : Blo 1576486 2367371 := bstep (se 1 (by rfl) ⟨1775528, by rfl⟩ : syracuseStep 2367371 = 3551057) B3551057
theorem B7577495 : Blo 1576486 7577495 := bstep (se 1 (by rfl) ⟨5683121, by rfl⟩ : syracuseStep 7577495 = 11366243) B11366243
theorem B2367383 : Blo 1576486 2367383 := bstep (se 1 (by rfl) ⟨1775537, by rfl⟩ : syracuseStep 2367383 = 3551075) B3551075
theorem B5324723 : Blo 1576486 5324723 := bstep (se 1 (by rfl) ⟨3993542, by rfl⟩ : syracuseStep 5324723 = 7987085) B7987085
theorem B3547097 : Blo 1576486 3547097 := bstep (se 2 (by rfl) ⟨1330161, by rfl⟩ : syracuseStep 3547097 = 2660323) B2660323
theorem B2367449 : Blo 1576486 2367449 := bstep (se 2 (by rfl) ⟨887793, by rfl⟩ : syracuseStep 2367449 = 1775587) B1775587
theorem B3547151 : Blo 1576486 3547151 := bstep (se 1 (by rfl) ⟨2660363, by rfl⟩ : syracuseStep 3547151 = 5320727) B5320727
theorem B2367503 : Blo 1576486 2367503 := bstep (se 1 (by rfl) ⟨1775627, by rfl⟩ : syracuseStep 2367503 = 3551255) B3551255
theorem B3547169 : Blo 1576486 3547169 := bstep (se 2 (by rfl) ⟨1330188, by rfl⟩ : syracuseStep 3547169 = 2660377) B2660377
theorem B2367545 : Blo 1576486 2367545 := bstep (se 2 (by rfl) ⟨887829, by rfl⟩ : syracuseStep 2367545 = 1775659) B1775659
theorem B12787799 : Blo 1576486 12787799 := bstep (se 1 (by rfl) ⟨9590849, by rfl⟩ : syracuseStep 12787799 = 19181699) B19181699
theorem B2367623 : Blo 1576486 2367623 := bstep (se 1 (by rfl) ⟨1775717, by rfl⟩ : syracuseStep 2367623 = 3551435) B3551435
theorem B2367659 : Blo 1576486 2367659 := bstep (se 1 (by rfl) ⟨1775744, by rfl⟩ : syracuseStep 2367659 = 3551489) B3551489
theorem B2367689 : Blo 1576486 2367689 := bstep (se 2 (by rfl) ⟨887883, by rfl⟩ : syracuseStep 2367689 = 1775767) B1775767
theorem B4489501 : Blo 1576486 4489501 := bstep (se 3 (by rfl) ⟨841781, by rfl⟩ : syracuseStep 4489501 = 1683563) B1683563
theorem B2662699 : Blo 1576486 2662699 := bstep (se 1 (by rfl) ⟨1997024, by rfl⟩ : syracuseStep 2662699 = 3994049) B3994049
theorem B7987571 : Blo 1576486 7987571 := bstep (se 1 (by rfl) ⟨5990678, by rfl⟩ : syracuseStep 7987571 = 11981357) B11981357
theorem B3547511 : Blo 1576486 3547511 := bstep (se 1 (by rfl) ⟨2660633, by rfl⟩ : syracuseStep 3547511 = 5321267) B5321267
theorem B5325209 : Blo 1576486 5325209 := bstep (se 2 (by rfl) ⟨1996953, by rfl⟩ : syracuseStep 5325209 = 3993907) B3993907
theorem B2662841 : Blo 1576486 2662841 := bstep (se 2 (by rfl) ⟨998565, by rfl⟩ : syracuseStep 2662841 = 1997131) B1997131
theorem B18211331 : Blo 1576486 18211331 := bstep (se 1 (by rfl) ⟨13658498, by rfl⟩ : syracuseStep 18211331 = 27316997) B27316997
theorem B3547691 : Blo 1576486 3547691 := bstep (se 1 (by rfl) ⟨2660768, by rfl⟩ : syracuseStep 3547691 = 5321537) B5321537
theorem B4489843 : Blo 1576486 4489843 := bstep (se 1 (by rfl) ⟨3367382, by rfl⟩ : syracuseStep 4489843 = 6734765) B6734765
theorem B7578305 : Blo 1576486 7578305 := bstep (se 2 (by rfl) ⟨2841864, by rfl⟩ : syracuseStep 7578305 = 5683729) B5683729
theorem B6734593 : Blo 1576486 6734593 := bstep (se 2 (by rfl) ⟨2525472, by rfl⟩ : syracuseStep 6734593 = 5050945) B5050945
theorem B7988057 : Blo 1576486 7988057 := bstep (se 2 (by rfl) ⟨2995521, by rfl⟩ : syracuseStep 7988057 = 5991043) B5991043
theorem B3548051 : Blo 1576486 3548051 := bstep (se 1 (by rfl) ⟨2661038, by rfl⟩ : syracuseStep 3548051 = 5322077) B5322077
theorem B3548105 : Blo 1576486 3548105 := bstep (se 2 (by rfl) ⟨1330539, by rfl⟩ : syracuseStep 3548105 = 2661079) B2661079
theorem B2245639 : Blo 1576486 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B5325911 : Blo 1576486 5325911 := bstep (se 1 (by rfl) ⟨3994433, by rfl⟩ : syracuseStep 5325911 = 7988867) B7988867
theorem B3990647 : Blo 1576486 3990647 := bstep (se 1 (by rfl) ⟨2992985, by rfl⟩ : syracuseStep 3990647 = 5985971) B5985971
theorem B2663543 : Blo 1576486 2663543 := bstep (se 1 (by rfl) ⟨1997657, by rfl⟩ : syracuseStep 2663543 = 3995315) B3995315
theorem B3368083 : Blo 1576486 3368083 := bstep (se 1 (by rfl) ⟨2526062, by rfl⟩ : syracuseStep 3368083 = 5052125) B5052125
theorem B38397077 : Blo 1576486 38397077 := bstep (se 6 (by rfl) ⟨899931, by rfl⟩ : syracuseStep 38397077 = 1799863) B1799863
theorem B1598735 : Blo 1576486 1598735 := bstep (se 1 (by rfl) ⟨1199051, by rfl⟩ : syracuseStep 1598735 = 2398103) B2398103
theorem B5326397 : Blo 1576486 5326397 := bstep (se 3 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 5326397 = 1997399) B1997399
theorem B3548807 : Blo 1576486 3548807 := bstep (se 1 (by rfl) ⟨2661605, by rfl⟩ : syracuseStep 3548807 = 5323211) B5323211
theorem B19449521 : Blo 1576486 19449521 := bstep (se 2 (by rfl) ⟨7293570, by rfl⟩ : syracuseStep 19449521 = 14587141) B14587141
theorem B3548987 : Blo 1576486 3548987 := bstep (se 1 (by rfl) ⟨2661740, by rfl⟩ : syracuseStep 3548987 = 5323481) B5323481
theorem B2246459 : Blo 1576486 2246459 := bstep (se 1 (by rfl) ⟨1684844, by rfl⟩ : syracuseStep 2246459 = 3369689) B3369689
theorem B3549113 : Blo 1576486 3549113 := bstep (se 2 (by rfl) ⟨1330917, by rfl⟩ : syracuseStep 3549113 = 2661835) B2661835
theorem B4048841 : Blo 1576486 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B4794383 : Blo 1576486 4794383 := bstep (se 1 (by rfl) ⟨3595787, by rfl⟩ : syracuseStep 4794383 = 7191575) B7191575
theorem B3991639 : Blo 1576486 3991639 := bstep (se 1 (by rfl) ⟨2993729, by rfl⟩ : syracuseStep 3991639 = 5987459) B5987459
theorem B5687533 : Blo 1576486 5687533 := bstep (se 3 (by rfl) ⟨1066412, by rfl⟩ : syracuseStep 5687533 = 2132825) B2132825
theorem B4262159 : Blo 1576486 4262159 := bstep (se 1 (by rfl) ⟨3196619, by rfl⟩ : syracuseStep 4262159 = 6393239) B6393239
theorem B3549455 : Blo 1576486 3549455 := bstep (se 1 (by rfl) ⟨2662091, by rfl⟩ : syracuseStep 3549455 = 5324183) B5324183
theorem B3549473 : Blo 1576486 3549473 := bstep (se 2 (by rfl) ⟨1331052, by rfl⟩ : syracuseStep 3549473 = 2662105) B2662105
theorem B7579955 : Blo 1576486 7579955 := bstep (se 1 (by rfl) ⟨5684966, by rfl⟩ : syracuseStep 7579955 = 11369933) B11369933
theorem B3991943 : Blo 1576486 3991943 := bstep (se 1 (by rfl) ⟨2993957, by rfl⟩ : syracuseStep 3991943 = 5987915) B5987915
theorem B5122457 : Blo 1576486 5122457 := bstep (se 2 (by rfl) ⟨1920921, by rfl⟩ : syracuseStep 5122457 = 3841843) B3841843
theorem B2247097 : Blo 1576486 2247097 := bstep (se 2 (by rfl) ⟨842661, by rfl⟩ : syracuseStep 2247097 = 1685323) B1685323
theorem B8096221 : Blo 1576486 8096221 := bstep (se 3 (by rfl) ⟨1518041, by rfl⟩ : syracuseStep 8096221 = 3036083) B3036083
theorem B9857539 : Blo 1576486 9857539 := bstep (se 1 (by rfl) ⟨7393154, by rfl⟩ : syracuseStep 9857539 = 14786309) B14786309
theorem B3992075 : Blo 1576486 3992075 := bstep (se 1 (by rfl) ⟨2994056, by rfl⟩ : syracuseStep 3992075 = 5988113) B5988113
theorem B2247211 : Blo 1576486 2247211 := bstep (se 1 (by rfl) ⟨1685408, by rfl⟩ : syracuseStep 2247211 = 3370817) B3370817
theorem B2525755 : Blo 1576486 2525755 := bstep (se 1 (by rfl) ⟨1894316, by rfl⟩ : syracuseStep 2525755 = 3788633) B3788633
theorem B3549815 : Blo 1576486 3549815 := bstep (se 1 (by rfl) ⟨2662361, by rfl⟩ : syracuseStep 3549815 = 5324723) B5324723
theorem B2247439 : Blo 1576486 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B3549995 : Blo 1576486 3549995 := bstep (se 1 (by rfl) ⟨2662496, by rfl⟩ : syracuseStep 3549995 = 5324993) B5324993
theorem B12798769 : Blo 1576486 12798769 := bstep (se 2 (by rfl) ⟨4799538, by rfl⟩ : syracuseStep 12798769 = 9599077) B9599077
theorem B7990163 : Blo 1576486 7990163 := bstep (se 1 (by rfl) ⟨5992622, by rfl⟩ : syracuseStep 7990163 = 11985245) B11985245
theorem B3992591 : Blo 1576486 3992591 := bstep (se 1 (by rfl) ⟨2994443, by rfl⟩ : syracuseStep 3992591 = 5988887) B5988887
theorem B3992723 : Blo 1576486 3992723 := bstep (se 1 (by rfl) ⟨2994542, by rfl⟩ : syracuseStep 3992723 = 5989085) B5989085
theorem B3550355 : Blo 1576486 3550355 := bstep (se 1 (by rfl) ⟨2662766, by rfl⟩ : syracuseStep 3550355 = 5325533) B5325533
theorem B3550409 : Blo 1576486 3550409 := bstep (se 2 (by rfl) ⟨1331403, by rfl⟩ : syracuseStep 3550409 = 2662807) B2662807
theorem B4492577 : Blo 1576486 4492577 := bstep (se 2 (by rfl) ⟨1684716, by rfl⟩ : syracuseStep 4492577 = 3369433) B3369433
theorem B8531237 : Blo 1576486 8531237 := bstep (se 4 (by rfl) ⟨799803, by rfl⟩ : syracuseStep 8531237 = 1599607) B1599607
theorem B7982387 : Blo 1576486 7982387 := bstep (se 1 (by rfl) ⟨5986790, by rfl⟩ : syracuseStep 7982387 = 11973581) B11973581
theorem B4263283 : Blo 1576486 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B4492691 : Blo 1576486 4492691 := bstep (se 1 (by rfl) ⟨3369518, by rfl⟩ : syracuseStep 4492691 = 6739037) B6739037
theorem B5991833 : Blo 1576486 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B2993593 : Blo 1576486 2993593 := bstep (se 2 (by rfl) ⟨1122597, by rfl⟩ : syracuseStep 2993593 = 2245195) B2245195
theorem B8097209 : Blo 1576486 8097209 := bstep (se 2 (by rfl) ⟨3036453, by rfl⟩ : syracuseStep 8097209 = 6072907) B6072907
theorem B93466061 : Blo 1576486 93466061 := bstep (se 3 (by rfl) ⟨17524886, by rfl⟩ : syracuseStep 93466061 = 35049773) B35049773
theorem B4263425 : Blo 1576486 4263425 := bstep (se 2 (by rfl) ⟨1598784, by rfl⟩ : syracuseStep 4263425 = 3197569) B3197569
theorem B1576507 : Blo 1576486 1576507 := bstep (se 1 (by rfl) ⟨1182380, by rfl⟩ : syracuseStep 1576507 = 2364761) B2364761
theorem B7982711 : Blo 1576486 7982711 := bstep (se 1 (by rfl) ⟨5987033, by rfl⟩ : syracuseStep 7982711 = 11974067) B11974067
theorem B1576583 : Blo 1576486 1576583 := bstep (se 1 (by rfl) ⟨1182437, by rfl⟩ : syracuseStep 1576583 = 2364875) B2364875
theorem B1576591 : Blo 1576486 1576591 := bstep (se 1 (by rfl) ⟨1182443, by rfl⟩ : syracuseStep 1576591 = 2364887) B2364887
theorem B3788441 : Blo 1576486 3788441 := bstep (se 2 (by rfl) ⟨1420665, by rfl⟩ : syracuseStep 3788441 = 2841331) B2841331
theorem B1576635 : Blo 1576486 1576635 := bstep (se 1 (by rfl) ⟨1182476, by rfl⟩ : syracuseStep 1576635 = 2364953) B2364953
theorem B1576711 : Blo 1576486 1576711 := bstep (se 1 (by rfl) ⟨1182533, by rfl⟩ : syracuseStep 1576711 = 2365067) B2365067
theorem B1576719 : Blo 1576486 1576719 := bstep (se 1 (by rfl) ⟨1182539, by rfl⟩ : syracuseStep 1576719 = 2365079) B2365079
theorem B2993935 : Blo 1576486 2993935 := bstep (se 1 (by rfl) ⟨2245451, by rfl⟩ : syracuseStep 2993935 = 4490903) B4490903
theorem B17977139 : Blo 1576486 17977139 := bstep (se 1 (by rfl) ⟨13482854, by rfl⟩ : syracuseStep 17977139 = 26965709) B26965709
theorem B1576763 : Blo 1576486 1576763 := bstep (se 1 (by rfl) ⟨1182572, by rfl⟩ : syracuseStep 1576763 = 2365145) B2365145
theorem B1576839 : Blo 1576486 1576839 := bstep (se 1 (by rfl) ⟨1182629, by rfl⟩ : syracuseStep 1576839 = 2365259) B2365259
theorem B3551111 : Blo 1576486 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B1576847 : Blo 1576486 1576847 := bstep (se 1 (by rfl) ⟨1182635, by rfl⟩ : syracuseStep 1576847 = 2365271) B2365271
theorem B1576891 : Blo 1576486 1576891 := bstep (se 1 (by rfl) ⟨1182668, by rfl⟩ : syracuseStep 1576891 = 2365337) B2365337
theorem B9588689 : Blo 1576486 9588689 := bstep (se 2 (by rfl) ⟨3595758, by rfl⟩ : syracuseStep 9588689 = 7191517) B7191517
theorem B1576967 : Blo 1576486 1576967 := bstep (se 1 (by rfl) ⟨1182725, by rfl⟩ : syracuseStep 1576967 = 2365451) B2365451
theorem B4378639 : Blo 1576486 4378639 := bstep (se 1 (by rfl) ⟨3283979, by rfl⟩ : syracuseStep 4378639 = 6567959) B6567959
theorem B1576975 : Blo 1576486 1576975 := bstep (se 1 (by rfl) ⟨1182731, by rfl⟩ : syracuseStep 1576975 = 2365463) B2365463
theorem B7680023 : Blo 1576486 7680023 := bstep (se 1 (by rfl) ⟨5760017, by rfl⟩ : syracuseStep 7680023 = 11520035) B11520035
theorem B1577019 : Blo 1576486 1577019 := bstep (se 1 (by rfl) ⟨1182764, by rfl⟩ : syracuseStep 1577019 = 2365529) B2365529
theorem B3551291 : Blo 1576486 3551291 := bstep (se 1 (by rfl) ⟨2663468, by rfl⟩ : syracuseStep 3551291 = 5326937) B5326937
theorem B8982647 : Blo 1576486 8982647 := bstep (se 1 (by rfl) ⟨6736985, by rfl⟩ : syracuseStep 8982647 = 13473971) B13473971
theorem B1577095 : Blo 1576486 1577095 := bstep (se 1 (by rfl) ⟨1182821, by rfl⟩ : syracuseStep 1577095 = 2365643) B2365643
theorem B2699399 : Blo 1576486 2699399 := bstep (se 1 (by rfl) ⟨2024549, by rfl⟩ : syracuseStep 2699399 = 4049099) B4049099
theorem B1577103 : Blo 1576486 1577103 := bstep (se 1 (by rfl) ⟨1182827, by rfl⟩ : syracuseStep 1577103 = 2365655) B2365655
theorem B4493465 : Blo 1576486 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B1577147 : Blo 1576486 1577147 := bstep (se 1 (by rfl) ⟨1182860, by rfl⟩ : syracuseStep 1577147 = 2365721) B2365721
theorem B3551417 : Blo 1576486 3551417 := bstep (se 2 (by rfl) ⟨1331781, by rfl⟩ : syracuseStep 3551417 = 2663563) B2663563
theorem B28774601 : Blo 1576486 28774601 := bstep (se 2 (by rfl) ⟨10790475, by rfl⟩ : syracuseStep 28774601 = 21580951) B21580951
theorem B54653129 : Blo 1576486 54653129 := bstep (se 2 (by rfl) ⟨20494923, by rfl⟩ : syracuseStep 54653129 = 40989847) B40989847
theorem B3993857 : Blo 1576486 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1577223 : Blo 1576486 1577223 := bstep (se 1 (by rfl) ⟨1182917, by rfl⟩ : syracuseStep 1577223 = 2365835) B2365835
theorem B1577231 : Blo 1576486 1577231 := bstep (se 1 (by rfl) ⟨1182923, by rfl⟩ : syracuseStep 1577231 = 2365847) B2365847
theorem B4264235 : Blo 1576486 4264235 := bstep (se 1 (by rfl) ⟨3198176, by rfl⟩ : syracuseStep 4264235 = 6396353) B6396353
theorem B1577275 : Blo 1576486 1577275 := bstep (se 1 (by rfl) ⟨1182956, by rfl⟩ : syracuseStep 1577275 = 2365913) B2365913
theorem B8982899 : Blo 1576486 8982899 := bstep (se 1 (by rfl) ⟨6737174, by rfl⟩ : syracuseStep 8982899 = 13474349) B13474349
theorem B3199351 : Blo 1576486 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B1577351 : Blo 1576486 1577351 := bstep (se 1 (by rfl) ⟨1183013, by rfl⟩ : syracuseStep 1577351 = 2366027) B2366027
theorem B1773967 : Blo 1576486 1773967 := bstep (se 1 (by rfl) ⟨1330475, by rfl⟩ : syracuseStep 1773967 = 2660951) B2660951
theorem B1577359 : Blo 1576486 1577359 := bstep (se 1 (by rfl) ⟨1183019, by rfl⟩ : syracuseStep 1577359 = 2366039) B2366039
theorem B30314897 : Blo 1576486 30314897 := bstep (se 2 (by rfl) ⟨11368086, by rfl⟩ : syracuseStep 30314897 = 22736173) B22736173
theorem B1577403 : Blo 1576486 1577403 := bstep (se 1 (by rfl) ⟨1183052, by rfl⟩ : syracuseStep 1577403 = 2366105) B2366105
theorem B4551169 : Blo 1576486 4551169 := bstep (se 2 (by rfl) ⟨1706688, by rfl⟩ : syracuseStep 4551169 = 3413377) B3413377
theorem B1577479 : Blo 1576486 1577479 := bstep (se 1 (by rfl) ⟨1183109, by rfl⟩ : syracuseStep 1577479 = 2366219) B2366219
theorem B1577487 : Blo 1576486 1577487 := bstep (se 1 (by rfl) ⟨1183115, by rfl⟩ : syracuseStep 1577487 = 2366231) B2366231
theorem B1577531 : Blo 1576486 1577531 := bstep (se 1 (by rfl) ⟨1183148, by rfl⟩ : syracuseStep 1577531 = 2366297) B2366297
theorem B7983683 : Blo 1576486 7983683 := bstep (se 1 (by rfl) ⟨5987762, by rfl⟩ : syracuseStep 7983683 = 11975525) B11975525
theorem B3994231 : Blo 1576486 3994231 := bstep (se 1 (by rfl) ⟨2995673, by rfl⟩ : syracuseStep 3994231 = 5991347) B5991347
theorem B2994823 : Blo 1576486 2994823 := bstep (se 1 (by rfl) ⟨2246117, by rfl⟩ : syracuseStep 2994823 = 4492235) B4492235
theorem B1577607 : Blo 1576486 1577607 := bstep (se 1 (by rfl) ⟨1183205, by rfl⟩ : syracuseStep 1577607 = 2366411) B2366411
theorem B1577615 : Blo 1576486 1577615 := bstep (se 1 (by rfl) ⟨1183211, by rfl⟩ : syracuseStep 1577615 = 2366423) B2366423
theorem B4264633 : Blo 1576486 4264633 := bstep (se 2 (by rfl) ⟨1599237, by rfl⟩ : syracuseStep 4264633 = 3198475) B3198475
theorem B1577659 : Blo 1576486 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B1995511 : Blo 1576486 1995511 := bstep (se 1 (by rfl) ⟨1496633, by rfl⟩ : syracuseStep 1995511 = 2993267) B2993267
theorem B1577735 : Blo 1576486 1577735 := bstep (se 1 (by rfl) ⟨1183301, by rfl⟩ : syracuseStep 1577735 = 2366603) B2366603
theorem B1577743 : Blo 1576486 1577743 := bstep (se 1 (by rfl) ⟨1183307, by rfl⟩ : syracuseStep 1577743 = 2366615) B2366615
theorem B1577787 : Blo 1576486 1577787 := bstep (se 1 (by rfl) ⟨1183340, by rfl⟩ : syracuseStep 1577787 = 2366681) B2366681
theorem B7984007 : Blo 1576486 7984007 := bstep (se 1 (by rfl) ⟨5988005, by rfl⟩ : syracuseStep 7984007 = 11976011) B11976011
theorem B1774471 : Blo 1576486 1774471 := bstep (se 1 (by rfl) ⟨1330853, by rfl⟩ : syracuseStep 1774471 = 2661707) B2661707
theorem B1577863 : Blo 1576486 1577863 := bstep (se 1 (by rfl) ⟨1183397, by rfl⟩ : syracuseStep 1577863 = 2366795) B2366795
theorem B1577871 : Blo 1576486 1577871 := bstep (se 1 (by rfl) ⟨1183403, by rfl⟩ : syracuseStep 1577871 = 2366807) B2366807
theorem B1577915 : Blo 1576486 1577915 := bstep (se 1 (by rfl) ⟨1183436, by rfl⟩ : syracuseStep 1577915 = 2366873) B2366873
theorem B1577991 : Blo 1576486 1577991 := bstep (se 1 (by rfl) ⟨1183493, by rfl⟩ : syracuseStep 1577991 = 2366987) B2366987
theorem B20771851 : Blo 1576486 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B1577999 : Blo 1576486 1577999 := bstep (se 1 (by rfl) ⟨1183499, by rfl⟩ : syracuseStep 1577999 = 2366999) B2366999
theorem B3994667 : Blo 1576486 3994667 := bstep (se 1 (by rfl) ⟨2996000, by rfl⟩ : syracuseStep 3994667 = 5992001) B5992001
theorem B1995835 : Blo 1576486 1995835 := bstep (se 1 (by rfl) ⟨1496876, by rfl⟩ : syracuseStep 1995835 = 2993753) B2993753
theorem B1774651 : Blo 1576486 1774651 := bstep (se 1 (by rfl) ⟨1330988, by rfl⟩ : syracuseStep 1774651 = 2661977) B2661977
theorem B1578043 : Blo 1576486 1578043 := bstep (se 1 (by rfl) ⟨1183532, by rfl⟩ : syracuseStep 1578043 = 2367065) B2367065
theorem B1578119 : Blo 1576486 1578119 := bstep (se 1 (by rfl) ⟨1183589, by rfl⟩ : syracuseStep 1578119 = 2367179) B2367179
theorem B18224261 : Blo 1576486 18224261 := bstep (se 4 (by rfl) ⟨1708524, by rfl⟩ : syracuseStep 18224261 = 3417049) B3417049
theorem B1578127 : Blo 1576486 1578127 := bstep (se 1 (by rfl) ⟨1183595, by rfl⟩ : syracuseStep 1578127 = 2367191) B2367191
theorem B1578171 : Blo 1576486 1578171 := bstep (se 1 (by rfl) ⟨1183628, by rfl⟩ : syracuseStep 1578171 = 2367257) B2367257
theorem B1578247 : Blo 1576486 1578247 := bstep (se 1 (by rfl) ⟨1183685, by rfl⟩ : syracuseStep 1578247 = 2367371) B2367371
theorem B5051663 : Blo 1576486 5051663 := bstep (se 1 (by rfl) ⟨3788747, by rfl⟩ : syracuseStep 5051663 = 7577495) B7577495
theorem B1578255 : Blo 1576486 1578255 := bstep (se 1 (by rfl) ⟨1183691, by rfl⟩ : syracuseStep 1578255 = 2367383) B2367383
theorem B2364731 : Blo 1576486 2364731 := bstep (se 1 (by rfl) ⟨1773548, by rfl⟩ : syracuseStep 2364731 = 3547097) B3547097
theorem B1578299 : Blo 1576486 1578299 := bstep (se 1 (by rfl) ⟨1183724, by rfl⟩ : syracuseStep 1578299 = 2367449) B2367449
theorem B2364791 : Blo 1576486 2364791 := bstep (se 1 (by rfl) ⟨1773593, by rfl⟩ : syracuseStep 2364791 = 3547187) B3547187
theorem B1578375 : Blo 1576486 1578375 := bstep (se 1 (by rfl) ⟨1183781, by rfl⟩ : syracuseStep 1578375 = 2367563) B2367563
theorem B2364815 : Blo 1576486 2364815 := bstep (se 1 (by rfl) ⟨1773611, by rfl⟩ : syracuseStep 2364815 = 3547223) B3547223
theorem B1578383 : Blo 1576486 1578383 := bstep (se 1 (by rfl) ⟨1183787, by rfl⟩ : syracuseStep 1578383 = 2367575) B2367575
theorem B5322131 : Blo 1576486 5322131 := bstep (se 1 (by rfl) ⟨3991598, by rfl⟩ : syracuseStep 5322131 = 7983197) B7983197
theorem B2364857 : Blo 1576486 2364857 := bstep (se 2 (by rfl) ⟨886821, by rfl⟩ : syracuseStep 2364857 = 1773643) B1773643
theorem B2561465 : Blo 1576486 2561465 := bstep (se 2 (by rfl) ⟨960549, by rfl⟩ : syracuseStep 2561465 = 1921099) B1921099
theorem B1578427 : Blo 1576486 1578427 := bstep (se 1 (by rfl) ⟨1183820, by rfl⟩ : syracuseStep 1578427 = 2367641) B2367641
theorem B2364935 : Blo 1576486 2364935 := bstep (se 1 (by rfl) ⟨1773701, by rfl⟩ : syracuseStep 2364935 = 3547403) B3547403
theorem B5395979 : Blo 1576486 5395979 := bstep (se 1 (by rfl) ⟨4046984, by rfl⟩ : syracuseStep 5395979 = 8093969) B8093969
theorem B1775119 : Blo 1576486 1775119 := bstep (se 1 (by rfl) ⟨1331339, by rfl⟩ : syracuseStep 1775119 = 2662679) B2662679
theorem B9598493 : Blo 1576486 9598493 := bstep (se 3 (by rfl) ⟨1799717, by rfl⟩ : syracuseStep 9598493 = 3599435) B3599435
theorem B2364971 : Blo 1576486 2364971 := bstep (se 1 (by rfl) ⟨1773728, by rfl⟩ : syracuseStep 2364971 = 3547457) B3547457
theorem B2365001 : Blo 1576486 2365001 := bstep (se 2 (by rfl) ⟨886875, by rfl⟩ : syracuseStep 2365001 = 1773751) B1773751
theorem B1685135 : Blo 1576486 1685135 := bstep (se 1 (by rfl) ⟨1263851, by rfl⟩ : syracuseStep 1685135 = 2527703) B2527703
theorem B45504179 : Blo 1576486 45504179 := bstep (se 1 (by rfl) ⟨34128134, by rfl⟩ : syracuseStep 45504179 = 68256269) B68256269
theorem B2365115 : Blo 1576486 2365115 := bstep (se 1 (by rfl) ⟨1773836, by rfl⟩ : syracuseStep 2365115 = 3547673) B3547673
theorem B2365175 : Blo 1576486 2365175 := bstep (se 1 (by rfl) ⟨1773881, by rfl⟩ : syracuseStep 2365175 = 3547763) B3547763
theorem B2365199 : Blo 1576486 2365199 := bstep (se 1 (by rfl) ⟨1773899, by rfl⟩ : syracuseStep 2365199 = 3547799) B3547799
theorem B8984357 : Blo 1576486 8984357 := bstep (se 4 (by rfl) ⟨842283, by rfl⟩ : syracuseStep 8984357 = 1684567) B1684567
theorem B2365241 : Blo 1576486 2365241 := bstep (se 2 (by rfl) ⟨886965, by rfl⟩ : syracuseStep 2365241 = 1773931) B1773931
theorem B3995507 : Blo 1576486 3995507 := bstep (se 1 (by rfl) ⟨2996630, by rfl⟩ : syracuseStep 3995507 = 5993261) B5993261
theorem B5986183 : Blo 1576486 5986183 := bstep (se 1 (by rfl) ⟨4489637, by rfl⟩ : syracuseStep 5986183 = 8979275) B8979275
theorem B2365319 : Blo 1576486 2365319 := bstep (se 1 (by rfl) ⟨1773989, by rfl⟩ : syracuseStep 2365319 = 3547979) B3547979
theorem B3995527 : Blo 1576486 3995527 := bstep (se 1 (by rfl) ⟨2996645, by rfl⟩ : syracuseStep 3995527 = 5993291) B5993291
theorem B11974553 : Blo 1576486 11974553 := bstep (se 2 (by rfl) ⟨4490457, by rfl⟩ : syracuseStep 11974553 = 8980915) B8980915
theorem B2365355 : Blo 1576486 2365355 := bstep (se 1 (by rfl) ⟨1774016, by rfl⟩ : syracuseStep 2365355 = 3548033) B3548033
theorem B2365385 : Blo 1576486 2365385 := bstep (se 2 (by rfl) ⟨887019, by rfl⟩ : syracuseStep 2365385 = 1774039) B1774039
theorem B1996807 : Blo 1576486 1996807 := bstep (se 1 (by rfl) ⟨1497605, by rfl⟩ : syracuseStep 1996807 = 2995211) B2995211
theorem B1775623 : Blo 1576486 1775623 := bstep (se 1 (by rfl) ⟨1331717, by rfl⟩ : syracuseStep 1775623 = 2663435) B2663435
theorem B3790891 : Blo 1576486 3790891 := bstep (se 1 (by rfl) ⟨2843168, by rfl⟩ : syracuseStep 3790891 = 5686337) B5686337
theorem B2660411 : Blo 1576486 2660411 := bstep (se 1 (by rfl) ⟨1995308, by rfl⟩ : syracuseStep 2660411 = 3990617) B3990617
theorem B2365499 : Blo 1576486 2365499 := bstep (se 1 (by rfl) ⟨1774124, by rfl⟩ : syracuseStep 2365499 = 3548249) B3548249
theorem B37427293 : Blo 1576486 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B2365559 : Blo 1576486 2365559 := bstep (se 1 (by rfl) ⟨1774169, by rfl⟩ : syracuseStep 2365559 = 3548339) B3548339
theorem B2365583 : Blo 1576486 2365583 := bstep (se 1 (by rfl) ⟨1774187, by rfl⟩ : syracuseStep 2365583 = 3548375) B3548375
theorem B4266137 : Blo 1576486 4266137 := bstep (se 2 (by rfl) ⟨1599801, by rfl⟩ : syracuseStep 4266137 = 3199603) B3199603
theorem B2365625 : Blo 1576486 2365625 := bstep (se 2 (by rfl) ⟨887109, by rfl⟩ : syracuseStep 2365625 = 1774219) B1774219
theorem B2365703 : Blo 1576486 2365703 := bstep (se 1 (by rfl) ⟨1774277, by rfl⟩ : syracuseStep 2365703 = 3548555) B3548555
theorem B20216081 : Blo 1576486 20216081 := bstep (se 2 (by rfl) ⟨7581030, by rfl⟩ : syracuseStep 20216081 = 15162061) B15162061
theorem B2275627 : Blo 1576486 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B2365739 : Blo 1576486 2365739 := bstep (se 1 (by rfl) ⟨1774304, by rfl⟩ : syracuseStep 2365739 = 3548609) B3548609
theorem B2365769 : Blo 1576486 2365769 := bstep (se 2 (by rfl) ⟨887163, by rfl⟩ : syracuseStep 2365769 = 1774327) B1774327
theorem B2996615 : Blo 1576486 2996615 := bstep (se 1 (by rfl) ⟨2247461, by rfl⟩ : syracuseStep 2996615 = 4494923) B4494923
theorem B14383507 : Blo 1576486 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B6068627 : Blo 1576486 6068627 := bstep (se 1 (by rfl) ⟨4551470, by rfl⟩ : syracuseStep 6068627 = 9102941) B9102941
theorem B1997227 : Blo 1576486 1997227 := bstep (se 1 (by rfl) ⟨1497920, by rfl⟩ : syracuseStep 1997227 = 2995841) B2995841
theorem B9599417 : Blo 1576486 9599417 := bstep (se 2 (by rfl) ⟨3599781, by rfl⟩ : syracuseStep 9599417 = 7199563) B7199563
theorem B2365883 : Blo 1576486 2365883 := bstep (se 1 (by rfl) ⟨1774412, by rfl⟩ : syracuseStep 2365883 = 3548825) B3548825
theorem B2660809 : Blo 1576486 2660809 := bstep (se 2 (by rfl) ⟨997803, by rfl⟩ : syracuseStep 2660809 = 1995607) B1995607
theorem B2365943 : Blo 1576486 2365943 := bstep (se 1 (by rfl) ⟨1774457, by rfl⟩ : syracuseStep 2365943 = 3548915) B3548915
theorem B2365967 : Blo 1576486 2365967 := bstep (se 1 (by rfl) ⟨1774475, by rfl⟩ : syracuseStep 2365967 = 3548951) B3548951
theorem B2398735 : Blo 1576486 2398735 := bstep (se 1 (by rfl) ⟨1799051, by rfl⟩ : syracuseStep 2398735 = 3598103) B3598103
theorem B2366009 : Blo 1576486 2366009 := bstep (se 2 (by rfl) ⟨887253, by rfl⟩ : syracuseStep 2366009 = 1774507) B1774507
theorem B2366087 : Blo 1576486 2366087 := bstep (se 1 (by rfl) ⟨1774565, by rfl⟩ : syracuseStep 2366087 = 3549131) B3549131
theorem B1997455 : Blo 1576486 1997455 := bstep (se 1 (by rfl) ⟨1498091, by rfl⟩ : syracuseStep 1997455 = 2996183) B2996183
theorem B2366123 : Blo 1576486 2366123 := bstep (se 1 (by rfl) ⟨1774592, by rfl⟩ : syracuseStep 2366123 = 3549185) B3549185
theorem B2808521 : Blo 1576486 2808521 := bstep (se 2 (by rfl) ⟨1053195, by rfl⟩ : syracuseStep 2808521 = 2106391) B2106391
theorem B2366153 : Blo 1576486 2366153 := bstep (se 2 (by rfl) ⟨887307, by rfl⟩ : syracuseStep 2366153 = 1774615) B1774615
theorem B8985289 : Blo 1576486 8985289 := bstep (se 2 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 8985289 = 6738967) B6738967
theorem B5323535 : Blo 1576486 5323535 := bstep (se 1 (by rfl) ⟨3992651, by rfl⟩ : syracuseStep 5323535 = 7985303) B7985303
theorem B2398991 : Blo 1576486 2398991 := bstep (se 1 (by rfl) ⟨1799243, by rfl⟩ : syracuseStep 2398991 = 3598487) B3598487
theorem B2366267 : Blo 1576486 2366267 := bstep (se 1 (by rfl) ⟨1774700, by rfl⟩ : syracuseStep 2366267 = 3549401) B3549401
theorem B2366327 : Blo 1576486 2366327 := bstep (se 1 (by rfl) ⟨1774745, by rfl⟩ : syracuseStep 2366327 = 3549491) B3549491
theorem B2366351 : Blo 1576486 2366351 := bstep (se 1 (by rfl) ⟨1774763, by rfl⟩ : syracuseStep 2366351 = 3549527) B3549527
theorem B2366393 : Blo 1576486 2366393 := bstep (se 2 (by rfl) ⟨887397, by rfl⟩ : syracuseStep 2366393 = 1774795) B1774795
theorem B2366471 : Blo 1576486 2366471 := bstep (se 1 (by rfl) ⟨1774853, by rfl⟩ : syracuseStep 2366471 = 3549707) B3549707
theorem B5323805 : Blo 1576486 5323805 := bstep (se 3 (by rfl) ⟨998213, by rfl⟩ : syracuseStep 5323805 = 1996427) B1996427
theorem B2366507 : Blo 1576486 2366507 := bstep (se 1 (by rfl) ⟨1774880, by rfl⟩ : syracuseStep 2366507 = 3549761) B3549761
theorem B6741053 : Blo 1576486 6741053 := bstep (se 3 (by rfl) ⟨1263947, by rfl⟩ : syracuseStep 6741053 = 2527895) B2527895
theorem B9591875 : Blo 1576486 9591875 := bstep (se 1 (by rfl) ⟨7193906, by rfl⟩ : syracuseStep 9591875 = 14387813) B14387813
theorem B2366537 : Blo 1576486 2366537 := bstep (se 2 (by rfl) ⟨887451, by rfl⟩ : syracuseStep 2366537 = 1774903) B1774903
theorem B6069335 : Blo 1576486 6069335 := bstep (se 1 (by rfl) ⟨4552001, by rfl⟩ : syracuseStep 6069335 = 9104003) B9104003
theorem B2661511 : Blo 1576486 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B2841785 : Blo 1576486 2841785 := bstep (se 2 (by rfl) ⟨1065669, by rfl⟩ : syracuseStep 2841785 = 2131339) B2131339
theorem B2366651 : Blo 1576486 2366651 := bstep (se 1 (by rfl) ⟨1774988, by rfl⟩ : syracuseStep 2366651 = 3549977) B3549977
theorem B16858313 : Blo 1576486 16858313 := bstep (se 2 (by rfl) ⟨6321867, by rfl⟩ : syracuseStep 16858313 = 12643735) B12643735
theorem B2366711 : Blo 1576486 2366711 := bstep (se 1 (by rfl) ⟨1775033, by rfl⟩ : syracuseStep 2366711 = 3550067) B3550067
theorem B2366735 : Blo 1576486 2366735 := bstep (se 1 (by rfl) ⟨1775051, by rfl⟩ : syracuseStep 2366735 = 3550103) B3550103
theorem B2366777 : Blo 1576486 2366777 := bstep (se 2 (by rfl) ⟨887541, by rfl⟩ : syracuseStep 2366777 = 1775083) B1775083
theorem B2366855 : Blo 1576486 2366855 := bstep (se 1 (by rfl) ⟨1775141, by rfl⟩ : syracuseStep 2366855 = 3550283) B3550283
theorem B11984273 : Blo 1576486 11984273 := bstep (se 2 (by rfl) ⟨4494102, by rfl⟩ : syracuseStep 11984273 = 8988205) B8988205
theorem B2366891 : Blo 1576486 2366891 := bstep (se 1 (by rfl) ⟨1775168, by rfl⟩ : syracuseStep 2366891 = 3550337) B3550337
theorem B2366921 : Blo 1576486 2366921 := bstep (se 2 (by rfl) ⟨887595, by rfl⟩ : syracuseStep 2366921 = 1775191) B1775191
theorem B13147651 : Blo 1576486 13147651 := bstep (se 1 (by rfl) ⟨9860738, by rfl⟩ : syracuseStep 13147651 = 19721477) B19721477
theorem B17972765 : Blo 1576486 17972765 := bstep (se 3 (by rfl) ⟨3369893, by rfl⟩ : syracuseStep 17972765 = 6739787) B6739787
theorem B2367035 : Blo 1576486 2367035 := bstep (se 1 (by rfl) ⟨1775276, by rfl⟩ : syracuseStep 2367035 = 3550553) B3550553
theorem B2367095 : Blo 1576486 2367095 := bstep (se 1 (by rfl) ⟨1775321, by rfl⟩ : syracuseStep 2367095 = 3550643) B3550643
theorem B2367119 : Blo 1576486 2367119 := bstep (se 1 (by rfl) ⟨1775339, by rfl⟩ : syracuseStep 2367119 = 3550679) B3550679
theorem B32841395 : Blo 1576486 32841395 := bstep (se 1 (by rfl) ⟨24631046, by rfl⟩ : syracuseStep 32841395 = 49262093) B49262093
theorem B2367161 : Blo 1576486 2367161 := bstep (se 2 (by rfl) ⟨887685, by rfl⟩ : syracuseStep 2367161 = 1775371) B1775371
theorem B2367239 : Blo 1576486 2367239 := bstep (se 1 (by rfl) ⟨1775429, by rfl⟩ : syracuseStep 2367239 = 3550859) B3550859
theorem B2662159 : Blo 1576486 2662159 := bstep (se 1 (by rfl) ⟨1996619, by rfl⟩ : syracuseStep 2662159 = 3993239) B3993239
theorem B10108709 : Blo 1576486 10108709 := bstep (se 4 (by rfl) ⟨947691, by rfl⟩ : syracuseStep 10108709 = 1895383) B1895383
theorem B2367275 : Blo 1576486 2367275 := bstep (se 1 (by rfl) ⟨1775456, by rfl⟩ : syracuseStep 2367275 = 3550913) B3550913
theorem B11976497 : Blo 1576486 11976497 := bstep (se 2 (by rfl) ⟨4491186, by rfl⟩ : syracuseStep 11976497 = 8982373) B8982373
theorem B2367305 : Blo 1576486 2367305 := bstep (se 2 (by rfl) ⟨887739, by rfl⟩ : syracuseStep 2367305 = 1775479) B1775479
theorem B16195403 : Blo 1576486 16195403 := bstep (se 1 (by rfl) ⟨12146552, by rfl⟩ : syracuseStep 16195403 = 24293105) B24293105
theorem B13475747 : Blo 1576486 13475747 := bstep (se 1 (by rfl) ⟨10106810, by rfl⟩ : syracuseStep 13475747 = 20213621) B20213621
theorem B2367419 : Blo 1576486 2367419 := bstep (se 1 (by rfl) ⟨1775564, by rfl⟩ : syracuseStep 2367419 = 3551129) B3551129
theorem B2367479 : Blo 1576486 2367479 := bstep (se 1 (by rfl) ⟨1775609, by rfl⟩ : syracuseStep 2367479 = 3551219) B3551219
theorem B2662409 : Blo 1576486 2662409 := bstep (se 2 (by rfl) ⟨998403, by rfl⟩ : syracuseStep 2662409 = 1996807) B1996807
theorem B2367497 : Blo 1576486 2367497 := bstep (se 2 (by rfl) ⟨887811, by rfl⟩ : syracuseStep 2367497 = 1775623) B1775623
theorem B5120015 : Blo 1576486 5120015 := bstep (se 1 (by rfl) ⟨3840011, by rfl⟩ : syracuseStep 5120015 = 7680023) B7680023
theorem B2367527 : Blo 1576486 2367527 := bstep (se 1 (by rfl) ⟨1775645, by rfl⟩ : syracuseStep 2367527 = 3551291) B3551291
theorem B5988431 : Blo 1576486 5988431 := bstep (se 1 (by rfl) ⟨4491323, by rfl⟩ : syracuseStep 5988431 = 8982647) B8982647
theorem B2367611 : Blo 1576486 2367611 := bstep (se 1 (by rfl) ⟨1775708, by rfl⟩ : syracuseStep 2367611 = 3551417) B3551417
theorem B2662571 : Blo 1576486 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B2842823 : Blo 1576486 2842823 := bstep (se 1 (by rfl) ⟨2132117, by rfl⟩ : syracuseStep 2842823 = 4264235) B4264235
theorem B20218085 : Blo 1576486 20218085 := bstep (se 4 (by rfl) ⟨1895445, by rfl⟩ : syracuseStep 20218085 = 3790891) B3790891
theorem B5988599 : Blo 1576486 5988599 := bstep (se 1 (by rfl) ⟨4491449, by rfl⟩ : syracuseStep 5988599 = 8982899) B8982899
theorem B5325047 : Blo 1576486 5325047 := bstep (se 1 (by rfl) ⟨3993785, by rfl⟩ : syracuseStep 5325047 = 7987571) B7987571
theorem B20209931 : Blo 1576486 20209931 := bstep (se 1 (by rfl) ⟨15157448, by rfl⟩ : syracuseStep 20209931 = 30314897) B30314897
theorem B12140887 : Blo 1576486 12140887 := bstep (se 1 (by rfl) ⟨9105665, by rfl⟩ : syracuseStep 12140887 = 18211331) B18211331
theorem B19178009 : Blo 1576486 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B2662969 : Blo 1576486 2662969 := bstep (se 2 (by rfl) ⟨998613, by rfl⟩ : syracuseStep 2662969 = 1997227) B1997227
theorem B5325371 : Blo 1576486 5325371 := bstep (se 1 (by rfl) ⟨3994028, by rfl⟩ : syracuseStep 5325371 = 7988057) B7988057
theorem B3547745 : Blo 1576486 3547745 := bstep (se 2 (by rfl) ⟨1330404, by rfl⟩ : syracuseStep 3547745 = 2660809) B2660809
theorem B2663111 : Blo 1576486 2663111 := bstep (se 1 (by rfl) ⟨1997333, by rfl⟩ : syracuseStep 2663111 = 3994667) B3994667
theorem B3367673 : Blo 1576486 3367673 := bstep (se 2 (by rfl) ⟨1262877, by rfl⟩ : syracuseStep 3367673 = 2525755) B2525755
theorem B12149507 : Blo 1576486 12149507 := bstep (se 1 (by rfl) ⟨9112130, by rfl⟩ : syracuseStep 12149507 = 18224261) B18224261
theorem B5325641 : Blo 1576486 5325641 := bstep (se 2 (by rfl) ⟨1997115, by rfl⟩ : syracuseStep 5325641 = 3994231) B3994231
theorem B3367775 : Blo 1576486 3367775 := bstep (se 1 (by rfl) ⟨2525831, by rfl⟩ : syracuseStep 3367775 = 5051663) B5051663
theorem B2663273 : Blo 1576486 2663273 := bstep (se 2 (by rfl) ⟨998727, by rfl⟩ : syracuseStep 2663273 = 1997455) B1997455
theorem B3548087 : Blo 1576486 3548087 := bstep (se 1 (by rfl) ⟨2661065, by rfl⟩ : syracuseStep 3548087 = 5322131) B5322131
theorem B8979457 : Blo 1576486 8979457 := bstep (se 2 (by rfl) ⟨3367296, by rfl⟩ : syracuseStep 8979457 = 6734593) B6734593
theorem B3597319 : Blo 1576486 3597319 := bstep (se 1 (by rfl) ⟨2697989, by rfl⟩ : syracuseStep 3597319 = 5395979) B5395979
theorem B6398995 : Blo 1576486 6398995 := bstep (se 1 (by rfl) ⟨4799246, by rfl⟩ : syracuseStep 6398995 = 9598493) B9598493
theorem B17065025 : Blo 1576486 17065025 := bstep (se 2 (by rfl) ⟨6399384, by rfl⟩ : syracuseStep 17065025 = 12798769) B12798769
theorem B30336119 : Blo 1576486 30336119 := bstep (se 1 (by rfl) ⟨22752089, by rfl⟩ : syracuseStep 30336119 = 45504179) B45504179
theorem B5989571 : Blo 1576486 5989571 := bstep (se 1 (by rfl) ⟨4492178, by rfl⟩ : syracuseStep 5989571 = 8984357) B8984357
theorem B2663671 : Blo 1576486 2663671 := bstep (se 1 (by rfl) ⟨1997753, by rfl⟩ : syracuseStep 2663671 = 3995507) B3995507
theorem B3196255 : Blo 1576486 3196255 := bstep (se 1 (by rfl) ⟨2397191, by rfl⟩ : syracuseStep 3196255 = 4794383) B4794383
theorem B2844091 : Blo 1576486 2844091 := bstep (se 1 (by rfl) ⟨2133068, by rfl⟩ : syracuseStep 2844091 = 4266137) B4266137
theorem B3548681 : Blo 1576486 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B13477387 : Blo 1576486 13477387 := bstep (se 1 (by rfl) ⟨10108040, by rfl⟩ : syracuseStep 13477387 = 20216081) B20216081
theorem B4490777 : Blo 1576486 4490777 := bstep (se 2 (by rfl) ⟨1684041, by rfl⟩ : syracuseStep 4490777 = 3368083) B3368083
theorem B6399611 : Blo 1576486 6399611 := bstep (se 1 (by rfl) ⟨4799708, by rfl⟩ : syracuseStep 6399611 = 9599417) B9599417
theorem B3549023 : Blo 1576486 3549023 := bstep (se 1 (by rfl) ⟨2661767, by rfl⟩ : syracuseStep 3549023 = 5323535) B5323535
theorem B3991457 : Blo 1576486 3991457 := bstep (se 2 (by rfl) ⟨1496796, by rfl⟩ : syracuseStep 3991457 = 2993593) B2993593
theorem B5326775 : Blo 1576486 5326775 := bstep (se 1 (by rfl) ⟨3995081, by rfl⟩ : syracuseStep 5326775 = 7990163) B7990163
theorem B3549203 : Blo 1576486 3549203 := bstep (se 1 (by rfl) ⟨2661902, by rfl⟩ : syracuseStep 3549203 = 5323805) B5323805
theorem B1894523 : Blo 1576486 1894523 := bstep (se 1 (by rfl) ⟨1420892, by rfl⟩ : syracuseStep 1894523 = 2841785) B2841785
theorem B5990557 : Blo 1576486 5990557 := bstep (se 3 (by rfl) ⟨1123229, by rfl⟩ : syracuseStep 5990557 = 2246459) B2246459
theorem B5687491 : Blo 1576486 5687491 := bstep (se 1 (by rfl) ⟨4265618, by rfl⟩ : syracuseStep 5687491 = 8531237) B8531237
theorem B7989515 : Blo 1576486 7989515 := bstep (se 1 (by rfl) ⟨5992136, by rfl⟩ : syracuseStep 7989515 = 11984273) B11984273
theorem B62310707 : Blo 1576486 62310707 := bstep (se 1 (by rfl) ⟨46733030, by rfl⟩ : syracuseStep 62310707 = 93466061) B93466061
theorem B3991913 : Blo 1576486 3991913 := bstep (se 2 (by rfl) ⟨1496967, by rfl⟩ : syracuseStep 3991913 = 2993935) B2993935
theorem B3549545 : Blo 1576486 3549545 := bstep (se 2 (by rfl) ⟨1331079, by rfl⟩ : syracuseStep 3549545 = 2662159) B2662159
theorem B2525627 : Blo 1576486 2525627 := bstep (se 1 (by rfl) ⟨1894220, by rfl⟩ : syracuseStep 2525627 = 3788441) B3788441
theorem B7981577 : Blo 1576486 7981577 := bstep (se 2 (by rfl) ⟨2993091, by rfl⟩ : syracuseStep 7981577 = 5986183) B5986183
theorem B5327369 : Blo 1576486 5327369 := bstep (se 2 (by rfl) ⟨1997763, by rfl⟩ : syracuseStep 5327369 = 3995527) B3995527
theorem B6392459 : Blo 1576486 6392459 := bstep (se 1 (by rfl) ⟨4794344, by rfl⟩ : syracuseStep 6392459 = 9588689) B9588689
theorem B3550139 : Blo 1576486 3550139 := bstep (se 1 (by rfl) ⟨2662604, by rfl⟩ : syracuseStep 3550139 = 5325209) B5325209
theorem B3034169 : Blo 1576486 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B3550265 : Blo 1576486 3550265 := bstep (se 2 (by rfl) ⟨1331349, by rfl⟩ : syracuseStep 3550265 = 2662699) B2662699
theorem B3198313 : Blo 1576486 3198313 := bstep (se 2 (by rfl) ⟨1199367, by rfl⟩ : syracuseStep 3198313 = 2398735) B2398735
theorem B11365757 : Blo 1576486 11365757 := bstep (se 3 (by rfl) ⟨2131079, by rfl⟩ : syracuseStep 11365757 = 4262159) B4262159
theorem B4263293 : Blo 1576486 4263293 := bstep (se 3 (by rfl) ⟨799367, by rfl⟩ : syracuseStep 4263293 = 1598735) B1598735
theorem B3550607 : Blo 1576486 3550607 := bstep (se 1 (by rfl) ⟨2662955, by rfl⟩ : syracuseStep 3550607 = 5325911) B5325911
theorem B3993097 : Blo 1576486 3993097 := bstep (se 2 (by rfl) ⟨1497411, by rfl⟩ : syracuseStep 3993097 = 2994823) B2994823
theorem B1576487 : Blo 1576486 1576487 := bstep (se 1 (by rfl) ⟨1182365, by rfl⟩ : syracuseStep 1576487 = 2364731) B2364731
theorem B1576527 : Blo 1576486 1576527 := bstep (se 1 (by rfl) ⟨1182395, by rfl⟩ : syracuseStep 1576527 = 2364791) B2364791
theorem B1576543 : Blo 1576486 1576543 := bstep (se 1 (by rfl) ⟨1182407, by rfl⟩ : syracuseStep 1576543 = 2364815) B2364815
theorem B11980385 : Blo 1576486 11980385 := bstep (se 2 (by rfl) ⟨4492644, by rfl⟩ : syracuseStep 11980385 = 8985289) B8985289
theorem B1576571 : Blo 1576486 1576571 := bstep (se 1 (by rfl) ⟨1182428, by rfl⟩ : syracuseStep 1576571 = 2364857) B2364857
theorem B1707643 : Blo 1576486 1707643 := bstep (se 1 (by rfl) ⟨1280732, by rfl⟩ : syracuseStep 1707643 = 2561465) B2561465
theorem B22744709 : Blo 1576486 22744709 := bstep (se 4 (by rfl) ⟨2132316, by rfl⟩ : syracuseStep 22744709 = 4264633) B4264633
theorem B1576623 : Blo 1576486 1576623 := bstep (se 1 (by rfl) ⟨1182467, by rfl⟩ : syracuseStep 1576623 = 2364935) B2364935
theorem B7990973 : Blo 1576486 7990973 := bstep (se 3 (by rfl) ⟨1498307, by rfl⟩ : syracuseStep 7990973 = 2996615) B2996615
theorem B1576647 : Blo 1576486 1576647 := bstep (se 1 (by rfl) ⟨1182485, by rfl⟩ : syracuseStep 1576647 = 2364971) B2364971
theorem B3550931 : Blo 1576486 3550931 := bstep (se 1 (by rfl) ⟨2663198, by rfl⟩ : syracuseStep 3550931 = 5326397) B5326397
theorem B1576667 : Blo 1576486 1576667 := bstep (se 1 (by rfl) ⟨1182500, by rfl⟩ : syracuseStep 1576667 = 2365001) B2365001
theorem B1576743 : Blo 1576486 1576743 := bstep (se 1 (by rfl) ⟨1182557, by rfl⟩ : syracuseStep 1576743 = 2365115) B2365115
theorem B1576783 : Blo 1576486 1576783 := bstep (se 1 (by rfl) ⟨1182587, by rfl⟩ : syracuseStep 1576783 = 2365175) B2365175
theorem B1576799 : Blo 1576486 1576799 := bstep (se 1 (by rfl) ⟨1182599, by rfl⟩ : syracuseStep 1576799 = 2365199) B2365199
theorem B1576827 : Blo 1576486 1576827 := bstep (se 1 (by rfl) ⟨1182620, by rfl⟩ : syracuseStep 1576827 = 2365241) B2365241
theorem B1576879 : Blo 1576486 1576879 := bstep (se 1 (by rfl) ⟨1182659, by rfl⟩ : syracuseStep 1576879 = 2365319) B2365319
theorem B7983035 : Blo 1576486 7983035 := bstep (se 1 (by rfl) ⟨5987276, by rfl⟩ : syracuseStep 7983035 = 11974553) B11974553
theorem B1576903 : Blo 1576486 1576903 := bstep (se 1 (by rfl) ⟨1182677, by rfl⟩ : syracuseStep 1576903 = 2365355) B2365355
theorem B1576923 : Blo 1576486 1576923 := bstep (se 1 (by rfl) ⟨1182692, by rfl⟩ : syracuseStep 1576923 = 2365385) B2365385
theorem B2699227 : Blo 1576486 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B2994185 : Blo 1576486 2994185 := bstep (se 2 (by rfl) ⟨1122819, by rfl⟩ : syracuseStep 2994185 = 2245639) B2245639
theorem B1773607 : Blo 1576486 1773607 := bstep (se 1 (by rfl) ⟨1330205, by rfl⟩ : syracuseStep 1773607 = 2660411) B2660411
theorem B1576999 : Blo 1576486 1576999 := bstep (se 1 (by rfl) ⟨1182749, by rfl⟩ : syracuseStep 1576999 = 2365499) B2365499
theorem B1577039 : Blo 1576486 1577039 := bstep (se 1 (by rfl) ⟨1182779, by rfl⟩ : syracuseStep 1577039 = 2365559) B2365559
theorem B1577055 : Blo 1576486 1577055 := bstep (se 1 (by rfl) ⟨1182791, by rfl⟩ : syracuseStep 1577055 = 2365583) B2365583
theorem B1577083 : Blo 1576486 1577083 := bstep (se 1 (by rfl) ⟨1182812, by rfl⟩ : syracuseStep 1577083 = 2365625) B2365625
theorem B1577135 : Blo 1576486 1577135 := bstep (se 1 (by rfl) ⟨1182851, by rfl⟩ : syracuseStep 1577135 = 2365703) B2365703
theorem B1577159 : Blo 1576486 1577159 := bstep (se 1 (by rfl) ⟨1182869, by rfl⟩ : syracuseStep 1577159 = 2365739) B2365739
theorem B1577179 : Blo 1576486 1577179 := bstep (se 1 (by rfl) ⟨1182884, by rfl⟩ : syracuseStep 1577179 = 2365769) B2365769
theorem B1577255 : Blo 1576486 1577255 := bstep (se 1 (by rfl) ⟨1182941, by rfl⟩ : syracuseStep 1577255 = 2365883) B2365883
theorem B1577295 : Blo 1576486 1577295 := bstep (se 1 (by rfl) ⟨1182971, by rfl⟩ : syracuseStep 1577295 = 2365943) B2365943
theorem B1577311 : Blo 1576486 1577311 := bstep (se 1 (by rfl) ⟨1182983, by rfl⟩ : syracuseStep 1577311 = 2365967) B2365967
theorem B1577339 : Blo 1576486 1577339 := bstep (se 1 (by rfl) ⟨1183004, by rfl⟩ : syracuseStep 1577339 = 2366009) B2366009
theorem B4493693 : Blo 1576486 4493693 := bstep (se 3 (by rfl) ⟨842567, by rfl⟩ : syracuseStep 4493693 = 1685135) B1685135
theorem B1577391 : Blo 1576486 1577391 := bstep (se 1 (by rfl) ⟨1183043, by rfl⟩ : syracuseStep 1577391 = 2366087) B2366087
theorem B1577415 : Blo 1576486 1577415 := bstep (se 1 (by rfl) ⟨1183061, by rfl⟩ : syracuseStep 1577415 = 2366123) B2366123
theorem B1872347 : Blo 1576486 1872347 := bstep (se 1 (by rfl) ⟨1404260, by rfl⟩ : syracuseStep 1872347 = 2808521) B2808521
theorem B1577435 : Blo 1576486 1577435 := bstep (se 1 (by rfl) ⟨1183076, by rfl⟩ : syracuseStep 1577435 = 2366153) B2366153
theorem B1577511 : Blo 1576486 1577511 := bstep (se 1 (by rfl) ⟨1183133, by rfl⟩ : syracuseStep 1577511 = 2366267) B2366267
theorem B1577551 : Blo 1576486 1577551 := bstep (se 1 (by rfl) ⟨1183163, by rfl⟩ : syracuseStep 1577551 = 2366327) B2366327
theorem B1577567 : Blo 1576486 1577567 := bstep (se 1 (by rfl) ⟨1183175, by rfl⟩ : syracuseStep 1577567 = 2366351) B2366351
theorem B22737509 : Blo 1576486 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B1577595 : Blo 1576486 1577595 := bstep (se 1 (by rfl) ⟨1183196, by rfl⟩ : syracuseStep 1577595 = 2366393) B2366393
theorem B1577647 : Blo 1576486 1577647 := bstep (se 1 (by rfl) ⟨1183235, by rfl⟩ : syracuseStep 1577647 = 2366471) B2366471
theorem B1577671 : Blo 1576486 1577671 := bstep (se 1 (by rfl) ⟨1183253, by rfl⟩ : syracuseStep 1577671 = 2366507) B2366507
theorem B4494035 : Blo 1576486 4494035 := bstep (se 1 (by rfl) ⟨3370526, by rfl⟩ : syracuseStep 4494035 = 6741053) B6741053
theorem B6394583 : Blo 1576486 6394583 := bstep (se 1 (by rfl) ⟨4795937, by rfl⟩ : syracuseStep 6394583 = 9591875) B9591875
theorem B1577691 : Blo 1576486 1577691 := bstep (se 1 (by rfl) ⟨1183268, by rfl⟩ : syracuseStep 1577691 = 2366537) B2366537
theorem B1577767 : Blo 1576486 1577767 := bstep (se 1 (by rfl) ⟨1183325, by rfl⟩ : syracuseStep 1577767 = 2366651) B2366651
theorem B1577807 : Blo 1576486 1577807 := bstep (se 1 (by rfl) ⟨1183355, by rfl⟩ : syracuseStep 1577807 = 2366711) B2366711
theorem B1577823 : Blo 1576486 1577823 := bstep (se 1 (by rfl) ⟨1183367, by rfl⟩ : syracuseStep 1577823 = 2366735) B2366735
theorem B2995051 : Blo 1576486 2995051 := bstep (se 1 (by rfl) ⟨2246288, by rfl⟩ : syracuseStep 2995051 = 4492577) B4492577
theorem B5321591 : Blo 1576486 5321591 := bstep (se 1 (by rfl) ⟨3991193, by rfl⟩ : syracuseStep 5321591 = 7982387) B7982387
theorem B1577851 : Blo 1576486 1577851 := bstep (se 1 (by rfl) ⟨1183388, by rfl⟩ : syracuseStep 1577851 = 2366777) B2366777
theorem B1577903 : Blo 1576486 1577903 := bstep (se 1 (by rfl) ⟨1183427, by rfl⟩ : syracuseStep 1577903 = 2366855) B2366855
theorem B2995127 : Blo 1576486 2995127 := bstep (se 1 (by rfl) ⟨2246345, by rfl⟩ : syracuseStep 2995127 = 4492691) B4492691
theorem B3994555 : Blo 1576486 3994555 := bstep (se 1 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 3994555 = 5991833) B5991833
theorem B1577927 : Blo 1576486 1577927 := bstep (se 1 (by rfl) ⟨1183445, by rfl⟩ : syracuseStep 1577927 = 2366891) B2366891
theorem B1577947 : Blo 1576486 1577947 := bstep (se 1 (by rfl) ⟨1183460, by rfl⟩ : syracuseStep 1577947 = 2366921) B2366921
theorem B11981843 : Blo 1576486 11981843 := bstep (se 1 (by rfl) ⟨8986382, by rfl⟩ : syracuseStep 11981843 = 17972765) B17972765
theorem B1578023 : Blo 1576486 1578023 := bstep (se 1 (by rfl) ⟨1183517, by rfl⟩ : syracuseStep 1578023 = 2367035) B2367035
theorem B5321807 : Blo 1576486 5321807 := bstep (se 1 (by rfl) ⟨3991355, by rfl⟩ : syracuseStep 5321807 = 7982711) B7982711
theorem B1578063 : Blo 1576486 1578063 := bstep (se 1 (by rfl) ⟨1183547, by rfl⟩ : syracuseStep 1578063 = 2367095) B2367095
theorem B1578079 : Blo 1576486 1578079 := bstep (se 1 (by rfl) ⟨1183559, by rfl⟩ : syracuseStep 1578079 = 2367119) B2367119
theorem B21894263 : Blo 1576486 21894263 := bstep (se 1 (by rfl) ⟨16420697, by rfl⟩ : syracuseStep 21894263 = 32841395) B32841395
theorem B1578107 : Blo 1576486 1578107 := bstep (se 1 (by rfl) ⟨1183580, by rfl⟩ : syracuseStep 1578107 = 2367161) B2367161
theorem B1578159 : Blo 1576486 1578159 := bstep (se 1 (by rfl) ⟨1183619, by rfl⟩ : syracuseStep 1578159 = 2367239) B2367239
theorem B6739139 : Blo 1576486 6739139 := bstep (se 1 (by rfl) ⟨5054354, by rfl⟩ : syracuseStep 6739139 = 10108709) B10108709
theorem B1578183 : Blo 1576486 1578183 := bstep (se 1 (by rfl) ⟨1183637, by rfl⟩ : syracuseStep 1578183 = 2367275) B2367275
theorem B7984331 : Blo 1576486 7984331 := bstep (se 1 (by rfl) ⟨5988248, by rfl⟩ : syracuseStep 7984331 = 11976497) B11976497
theorem B1578203 : Blo 1576486 1578203 := bstep (se 1 (by rfl) ⟨1183652, by rfl⟩ : syracuseStep 1578203 = 2367305) B2367305
theorem B8983831 : Blo 1576486 8983831 := bstep (se 1 (by rfl) ⟨6737873, by rfl⟩ : syracuseStep 8983831 = 13475747) B13475747
theorem B1578279 : Blo 1576486 1578279 := bstep (se 1 (by rfl) ⟨1183709, by rfl⟩ : syracuseStep 1578279 = 2367419) B2367419
theorem B1578319 : Blo 1576486 1578319 := bstep (se 1 (by rfl) ⟨1183739, by rfl⟩ : syracuseStep 1578319 = 2367479) B2367479
theorem B2364767 : Blo 1576486 2364767 := bstep (se 1 (by rfl) ⟨1773575, by rfl⟩ : syracuseStep 2364767 = 3547151) B3547151
theorem B1578335 : Blo 1576486 1578335 := bstep (se 1 (by rfl) ⟨1183751, by rfl⟩ : syracuseStep 1578335 = 2367503) B2367503
theorem B52573541 : Blo 1576486 52573541 := bstep (se 4 (by rfl) ⟨4928769, by rfl⟩ : syracuseStep 52573541 = 9857539) B9857539
theorem B5838185 : Blo 1576486 5838185 := bstep (se 2 (by rfl) ⟨2189319, by rfl⟩ : syracuseStep 5838185 = 4378639) B4378639
theorem B2364779 : Blo 1576486 2364779 := bstep (se 1 (by rfl) ⟨1773584, by rfl⟩ : syracuseStep 2364779 = 3547169) B3547169
theorem B1578363 : Blo 1576486 1578363 := bstep (se 1 (by rfl) ⟨1183772, by rfl⟩ : syracuseStep 1578363 = 2367545) B2367545
theorem B1799599 : Blo 1576486 1799599 := bstep (se 1 (by rfl) ⟨1349699, by rfl⟩ : syracuseStep 1799599 = 2699399) B2699399
theorem B1578415 : Blo 1576486 1578415 := bstep (se 1 (by rfl) ⟨1183811, by rfl⟩ : syracuseStep 1578415 = 2367623) B2367623
theorem B2995643 : Blo 1576486 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B1578439 : Blo 1576486 1578439 := bstep (se 1 (by rfl) ⟨1183829, by rfl⟩ : syracuseStep 1578439 = 2367659) B2367659
theorem B5322185 : Blo 1576486 5322185 := bstep (se 2 (by rfl) ⟨1995819, by rfl⟩ : syracuseStep 5322185 = 3991639) B3991639
theorem B49903057 : Blo 1576486 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B19183067 : Blo 1576486 19183067 := bstep (se 1 (by rfl) ⟨14387300, by rfl⟩ : syracuseStep 19183067 = 28774601) B28774601
theorem B36435419 : Blo 1576486 36435419 := bstep (se 1 (by rfl) ⟨27326564, by rfl⟩ : syracuseStep 36435419 = 54653129) B54653129
theorem B1578459 : Blo 1576486 1578459 := bstep (se 1 (by rfl) ⟨1183844, by rfl⟩ : syracuseStep 1578459 = 2367689) B2367689
theorem B2365007 : Blo 1576486 2365007 := bstep (se 1 (by rfl) ⟨1773755, by rfl⟩ : syracuseStep 2365007 = 3547511) B3547511
theorem B1775227 : Blo 1576486 1775227 := bstep (se 1 (by rfl) ⟨1331420, by rfl⟩ : syracuseStep 1775227 = 2662841) B2662841
theorem B7583377 : Blo 1576486 7583377 := bstep (se 2 (by rfl) ⟨2843766, by rfl⟩ : syracuseStep 7583377 = 5687533) B5687533
theorem B2365127 : Blo 1576486 2365127 := bstep (se 1 (by rfl) ⟨1773845, by rfl⟩ : syracuseStep 2365127 = 3547691) B3547691
theorem B5986001 : Blo 1576486 5986001 := bstep (se 2 (by rfl) ⟨2244750, by rfl⟩ : syracuseStep 5986001 = 4489501) B4489501
theorem B5322455 : Blo 1576486 5322455 := bstep (se 1 (by rfl) ⟨3991841, by rfl⟩ : syracuseStep 5322455 = 7983683) B7983683
theorem B5052203 : Blo 1576486 5052203 := bstep (se 1 (by rfl) ⟨3789152, by rfl⟩ : syracuseStep 5052203 = 7578305) B7578305
theorem B4265801 : Blo 1576486 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B2365289 : Blo 1576486 2365289 := bstep (se 2 (by rfl) ⟨886983, by rfl⟩ : syracuseStep 2365289 = 1773967) B1773967
theorem B2996129 : Blo 1576486 2996129 := bstep (se 2 (by rfl) ⟨1123548, by rfl⟩ : syracuseStep 2996129 = 2247097) B2247097
theorem B5322671 : Blo 1576486 5322671 := bstep (se 1 (by rfl) ⟨3992003, by rfl⟩ : syracuseStep 5322671 = 7984007) B7984007
theorem B2365367 : Blo 1576486 2365367 := bstep (se 1 (by rfl) ⟨1774025, by rfl⟩ : syracuseStep 2365367 = 3548051) B3548051
theorem B10794961 : Blo 1576486 10794961 := bstep (se 2 (by rfl) ⟨4048110, by rfl⟩ : syracuseStep 10794961 = 8096221) B8096221
theorem B2365403 : Blo 1576486 2365403 := bstep (se 1 (by rfl) ⟨1774052, by rfl⟩ : syracuseStep 2365403 = 3548105) B3548105
theorem B6068225 : Blo 1576486 6068225 := bstep (se 2 (by rfl) ⟨2275584, by rfl⟩ : syracuseStep 6068225 = 4551169) B4551169
theorem B2996281 : Blo 1576486 2996281 := bstep (se 2 (by rfl) ⟨1123605, by rfl⟩ : syracuseStep 2996281 = 2247211) B2247211
theorem B2660431 : Blo 1576486 2660431 := bstep (se 1 (by rfl) ⟨1995323, by rfl⟩ : syracuseStep 2660431 = 3990647) B3990647
theorem B1775695 : Blo 1576486 1775695 := bstep (se 1 (by rfl) ⟨1331771, by rfl⟩ : syracuseStep 1775695 = 2663543) B2663543
theorem B25598051 : Blo 1576486 25598051 := bstep (se 1 (by rfl) ⟨19198538, by rfl⟩ : syracuseStep 25598051 = 38397077) B38397077
theorem B5986457 : Blo 1576486 5986457 := bstep (se 2 (by rfl) ⟨2244921, by rfl⟩ : syracuseStep 5986457 = 4489843) B4489843
theorem B136403189 : Blo 1576486 136403189 := bstep (se 5 (by rfl) ⟨6393899, by rfl⟩ : syracuseStep 136403189 = 12787799) B12787799
theorem B64739573 : Blo 1576486 64739573 := bstep (se 5 (by rfl) ⟨3034667, by rfl⟩ : syracuseStep 64739573 = 6069335) B6069335
theorem B2660681 : Blo 1576486 2660681 := bstep (se 2 (by rfl) ⟨997755, by rfl⟩ : syracuseStep 2660681 = 1995511) B1995511
theorem B2996585 : Blo 1576486 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B2365871 : Blo 1576486 2365871 := bstep (se 1 (by rfl) ⟨1774403, by rfl⟩ : syracuseStep 2365871 = 3548807) B3548807
theorem B12966347 : Blo 1576486 12966347 := bstep (se 1 (by rfl) ⟨9724760, by rfl⟩ : syracuseStep 12966347 = 19449521) B19449521
theorem B2365961 : Blo 1576486 2365961 := bstep (se 2 (by rfl) ⟨887235, by rfl⟩ : syracuseStep 2365961 = 1774471) B1774471
theorem B2365991 : Blo 1576486 2365991 := bstep (se 1 (by rfl) ⟨1774493, by rfl⟩ : syracuseStep 2365991 = 3548987) B3548987
theorem B2366075 : Blo 1576486 2366075 := bstep (se 1 (by rfl) ⟨1774556, by rfl⟩ : syracuseStep 2366075 = 3549113) B3549113
theorem B27695801 : Blo 1576486 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B2661113 : Blo 1576486 2661113 := bstep (se 2 (by rfl) ⟨997917, by rfl⟩ : syracuseStep 2661113 = 1995835) B1995835
theorem B2366201 : Blo 1576486 2366201 := bstep (se 2 (by rfl) ⟨887325, by rfl⟩ : syracuseStep 2366201 = 1774651) B1774651
theorem B2366303 : Blo 1576486 2366303 := bstep (se 1 (by rfl) ⟨1774727, by rfl⟩ : syracuseStep 2366303 = 3549455) B3549455
theorem B2366315 : Blo 1576486 2366315 := bstep (se 1 (by rfl) ⟨1774736, by rfl⟩ : syracuseStep 2366315 = 3549473) B3549473
theorem B5053303 : Blo 1576486 5053303 := bstep (se 1 (by rfl) ⟨3789977, by rfl⟩ : syracuseStep 5053303 = 7579955) B7579955
theorem B2661295 : Blo 1576486 2661295 := bstep (se 1 (by rfl) ⟨1995971, by rfl⟩ : syracuseStep 2661295 = 3991943) B3991943
theorem B4045751 : Blo 1576486 4045751 := bstep (se 1 (by rfl) ⟨3034313, by rfl⟩ : syracuseStep 4045751 = 6068627) B6068627
theorem B3414971 : Blo 1576486 3414971 := bstep (se 1 (by rfl) ⟨2561228, by rfl⟩ : syracuseStep 3414971 = 5122457) B5122457
theorem B2661383 : Blo 1576486 2661383 := bstep (se 1 (by rfl) ⟨1996037, by rfl⟩ : syracuseStep 2661383 = 3992075) B3992075
theorem B2366543 : Blo 1576486 2366543 := bstep (se 1 (by rfl) ⟨1774907, by rfl⟩ : syracuseStep 2366543 = 3549815) B3549815
theorem B2366663 : Blo 1576486 2366663 := bstep (se 1 (by rfl) ⟨1774997, by rfl⟩ : syracuseStep 2366663 = 3549995) B3549995
theorem B17530201 : Blo 1576486 17530201 := bstep (se 2 (by rfl) ⟨6573825, by rfl⟩ : syracuseStep 17530201 = 13147651) B13147651
theorem B2661727 : Blo 1576486 2661727 := bstep (se 1 (by rfl) ⟨1996295, by rfl⟩ : syracuseStep 2661727 = 3992591) B3992591
theorem B2366825 : Blo 1576486 2366825 := bstep (se 2 (by rfl) ⟨887559, by rfl⟩ : syracuseStep 2366825 = 1775119) B1775119
theorem B6397309 : Blo 1576486 6397309 := bstep (se 3 (by rfl) ⟨1199495, by rfl⟩ : syracuseStep 6397309 = 2398991) B2398991
theorem B2661815 : Blo 1576486 2661815 := bstep (se 1 (by rfl) ⟨1996361, by rfl⟩ : syracuseStep 2661815 = 3992723) B3992723
theorem B2366903 : Blo 1576486 2366903 := bstep (se 1 (by rfl) ⟨1775177, by rfl⟩ : syracuseStep 2366903 = 3550355) B3550355
theorem B11238875 : Blo 1576486 11238875 := bstep (se 1 (by rfl) ⟨8429156, by rfl⟩ : syracuseStep 11238875 = 16858313) B16858313
theorem B2366939 : Blo 1576486 2366939 := bstep (se 1 (by rfl) ⟨1775204, by rfl⟩ : syracuseStep 2366939 = 3550409) B3550409
theorem B5398139 : Blo 1576486 5398139 := bstep (se 1 (by rfl) ⟨4048604, by rfl⟩ : syracuseStep 5398139 = 8097209) B8097209
theorem B2842283 : Blo 1576486 2842283 := bstep (se 1 (by rfl) ⟨2131712, by rfl⟩ : syracuseStep 2842283 = 4263425) B4263425
theorem B11984759 : Blo 1576486 11984759 := bstep (se 1 (by rfl) ⟨8988569, by rfl⟩ : syracuseStep 11984759 = 17977139) B17977139
theorem B10796935 : Blo 1576486 10796935 := bstep (se 1 (by rfl) ⟨8097701, by rfl⟩ : syracuseStep 10796935 = 16195403) B16195403
theorem B2367407 : Blo 1576486 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B3547241 : Blo 1576486 3547241 := bstep (se 2 (by rfl) ⟨1330215, by rfl⟩ : syracuseStep 3547241 = 2660431) B2660431
theorem B2367593 : Blo 1576486 2367593 := bstep (se 2 (by rfl) ⟨887847, by rfl⟩ : syracuseStep 2367593 = 1775695) B1775695
theorem B7987409 : Blo 1576486 7987409 := bstep (se 2 (by rfl) ⟨2995278, by rfl⟩ : syracuseStep 7987409 = 5990557) B5990557
theorem B16187849 : Blo 1576486 16187849 := bstep (se 2 (by rfl) ⟨6070443, by rfl⟩ : syracuseStep 16187849 = 12140887) B12140887
theorem B2245115 : Blo 1576486 2245115 := bstep (se 1 (by rfl) ⟨1683836, by rfl⟩ : syracuseStep 2245115 = 3367673) B3367673
theorem B3547727 : Blo 1576486 3547727 := bstep (se 1 (by rfl) ⟨2660795, by rfl⟩ : syracuseStep 3547727 = 5321591) B5321591
theorem B7987895 : Blo 1576486 7987895 := bstep (se 1 (by rfl) ⟨5990921, by rfl⟩ : syracuseStep 7987895 = 11981843) B11981843
theorem B3547871 : Blo 1576486 3547871 := bstep (se 1 (by rfl) ⟨2660903, by rfl⟩ : syracuseStep 3547871 = 5321807) B5321807
theorem B3548123 : Blo 1576486 3548123 := bstep (se 1 (by rfl) ⟨2661092, by rfl⟩ : syracuseStep 3548123 = 5322185) B5322185
theorem B12788711 : Blo 1576486 12788711 := bstep (se 1 (by rfl) ⟨9591533, by rfl⟩ : syracuseStep 12788711 = 19183067) B19183067
theorem B24290279 : Blo 1576486 24290279 := bstep (se 1 (by rfl) ⟨18217709, by rfl⟩ : syracuseStep 24290279 = 36435419) B36435419
theorem B3990667 : Blo 1576486 3990667 := bstep (se 1 (by rfl) ⟨2993000, by rfl⟩ : syracuseStep 3990667 = 5986001) B5986001
theorem B3548303 : Blo 1576486 3548303 := bstep (se 1 (by rfl) ⟨2661227, by rfl⟩ : syracuseStep 3548303 = 5322455) B5322455
theorem B7988381 : Blo 1576486 7988381 := bstep (se 3 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 7988381 = 2995643) B2995643
theorem B3368135 : Blo 1576486 3368135 := bstep (se 1 (by rfl) ⟨2526101, by rfl⟩ : syracuseStep 3368135 = 5052203) B5052203
theorem B2843867 : Blo 1576486 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B3548393 : Blo 1576486 3548393 := bstep (se 2 (by rfl) ⟨1330647, by rfl⟩ : syracuseStep 3548393 = 2661295) B2661295
theorem B5326073 : Blo 1576486 5326073 := bstep (se 2 (by rfl) ⟨1997277, by rfl⟩ : syracuseStep 5326073 = 3994555) B3994555
theorem B3548447 : Blo 1576486 3548447 := bstep (se 1 (by rfl) ⟨2661335, by rfl⟩ : syracuseStep 3548447 = 5322671) B5322671
theorem B17065367 : Blo 1576486 17065367 := bstep (se 1 (by rfl) ⟨12799025, by rfl⟩ : syracuseStep 17065367 = 25598051) B25598051
theorem B3990971 : Blo 1576486 3990971 := bstep (se 1 (by rfl) ⟨2993228, by rfl⟩ : syracuseStep 3990971 = 5986457) B5986457
theorem B5326343 : Blo 1576486 5326343 := bstep (se 1 (by rfl) ⟨3994757, by rfl⟩ : syracuseStep 5326343 = 7989515) B7989515
theorem B8644231 : Blo 1576486 8644231 := bstep (se 1 (by rfl) ⟨6483173, by rfl⟩ : syracuseStep 8644231 = 12966347) B12966347
theorem B11978441 : Blo 1576486 11978441 := bstep (se 2 (by rfl) ⟨4491915, by rfl⟩ : syracuseStep 11978441 = 8983831) B8983831
theorem B4261673 : Blo 1576486 4261673 := bstep (se 2 (by rfl) ⟨1598127, by rfl⟩ : syracuseStep 4261673 = 3196255) B3196255
theorem B3548969 : Blo 1576486 3548969 := bstep (se 2 (by rfl) ⟨1330863, by rfl⟩ : syracuseStep 3548969 = 2661727) B2661727
theorem B8529745 : Blo 1576486 8529745 := bstep (se 2 (by rfl) ⟨3198654, by rfl⟩ : syracuseStep 8529745 = 6397309) B6397309
theorem B66537409 : Blo 1576486 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B2697167 : Blo 1576486 2697167 := bstep (se 1 (by rfl) ⟨2022875, by rfl⟩ : syracuseStep 2697167 = 4045751) B4045751
theorem B10111169 : Blo 1576486 10111169 := bstep (se 2 (by rfl) ⟨3791688, by rfl⟩ : syracuseStep 10111169 = 7583377) B7583377
theorem B8980733 : Blo 1576486 8980733 := bstep (se 3 (by rfl) ⟨1683887, by rfl⟩ : syracuseStep 8980733 = 3367775) B3367775
theorem B3598759 : Blo 1576486 3598759 := bstep (se 1 (by rfl) ⟨2699069, by rfl⟩ : syracuseStep 3598759 = 5398139) B5398139
theorem B7989677 : Blo 1576486 7989677 := bstep (se 3 (by rfl) ⟨1498064, by rfl⟩ : syracuseStep 7989677 = 2996129) B2996129
theorem B1894855 : Blo 1576486 1894855 := bstep (se 1 (by rfl) ⟨1421141, by rfl⟩ : syracuseStep 1894855 = 2842283) B2842283
theorem B5327315 : Blo 1576486 5327315 := bstep (se 1 (by rfl) ⟨3995486, by rfl⟩ : syracuseStep 5327315 = 7990973) B7990973
theorem B14395877 : Blo 1576486 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B14395913 : Blo 1576486 14395913 := bstep (se 2 (by rfl) ⟨5398467, by rfl⟩ : syracuseStep 14395913 = 10796935) B10796935
theorem B7989839 : Blo 1576486 7989839 := bstep (se 1 (by rfl) ⟨5992379, by rfl⟩ : syracuseStep 7989839 = 11984759) B11984759
theorem B3992287 : Blo 1576486 3992287 := bstep (se 1 (by rfl) ⟨2994215, by rfl⟩ : syracuseStep 3992287 = 5988431) B5988431
theorem B13478723 : Blo 1576486 13478723 := bstep (se 1 (by rfl) ⟨10109042, by rfl⟩ : syracuseStep 13478723 = 20218085) B20218085
theorem B3992399 : Blo 1576486 3992399 := bstep (se 1 (by rfl) ⟨2994299, by rfl⟩ : syracuseStep 3992399 = 5988599) B5988599
theorem B3550031 : Blo 1576486 3550031 := bstep (se 1 (by rfl) ⟨2662523, by rfl⟩ : syracuseStep 3550031 = 5325047) B5325047
theorem B3550247 : Blo 1576486 3550247 := bstep (se 1 (by rfl) ⟨2662685, by rfl⟩ : syracuseStep 3550247 = 5325371) B5325371
theorem B15158339 : Blo 1576486 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B7580861 : Blo 1576486 7580861 := bstep (se 3 (by rfl) ⟨1421411, by rfl⟩ : syracuseStep 7580861 = 2842823) B2842823
theorem B3550427 : Blo 1576486 3550427 := bstep (se 1 (by rfl) ⟨2662820, by rfl⟩ : syracuseStep 3550427 = 5325641) B5325641
theorem B3550625 : Blo 1576486 3550625 := bstep (se 2 (by rfl) ⟨1331484, by rfl⟩ : syracuseStep 3550625 = 2662969) B2662969
theorem B3993047 : Blo 1576486 3993047 := bstep (se 1 (by rfl) ⟨2994785, by rfl⟩ : syracuseStep 3993047 = 5989571) B5989571
theorem B4492759 : Blo 1576486 4492759 := bstep (se 1 (by rfl) ⟨3369569, by rfl⟩ : syracuseStep 4492759 = 6739139) B6739139
theorem B1576511 : Blo 1576486 1576511 := bstep (se 1 (by rfl) ⟨1182383, by rfl⟩ : syracuseStep 1576511 = 2364767) B2364767
theorem B1576519 : Blo 1576486 1576519 := bstep (se 1 (by rfl) ⟨1182389, by rfl⟩ : syracuseStep 1576519 = 2364779) B2364779
theorem B15568493 : Blo 1576486 15568493 := bstep (se 3 (by rfl) ⟨2919092, by rfl⟩ : syracuseStep 15568493 = 5838185) B5838185
theorem B2993851 : Blo 1576486 2993851 := bstep (se 1 (by rfl) ⟨2245388, by rfl⟩ : syracuseStep 2993851 = 4490777) B4490777
theorem B1576671 : Blo 1576486 1576671 := bstep (se 1 (by rfl) ⟨1182503, by rfl⟩ : syracuseStep 1576671 = 2365007) B2365007
theorem B1576751 : Blo 1576486 1576751 := bstep (se 1 (by rfl) ⟨1182563, by rfl⟩ : syracuseStep 1576751 = 2365127) B2365127
theorem B3993401 : Blo 1576486 3993401 := bstep (se 2 (by rfl) ⟨1497525, by rfl⟩ : syracuseStep 3993401 = 2995051) B2995051
theorem B6737737 : Blo 1576486 6737737 := bstep (se 2 (by rfl) ⟨2526651, by rfl⟩ : syracuseStep 6737737 = 5053303) B5053303
theorem B1576859 : Blo 1576486 1576859 := bstep (se 1 (by rfl) ⟨1182644, by rfl⟩ : syracuseStep 1576859 = 2365289) B2365289
theorem B4992925 : Blo 1576486 4992925 := bstep (se 3 (by rfl) ⟨936173, by rfl⟩ : syracuseStep 4992925 = 1872347) B1872347
theorem B1576911 : Blo 1576486 1576911 := bstep (se 1 (by rfl) ⟨1182683, by rfl⟩ : syracuseStep 1576911 = 2365367) B2365367
theorem B3551183 : Blo 1576486 3551183 := bstep (se 1 (by rfl) ⟨2663387, by rfl⟩ : syracuseStep 3551183 = 5326775) B5326775
theorem B1576935 : Blo 1576486 1576935 := bstep (se 1 (by rfl) ⟨1182701, by rfl⟩ : syracuseStep 1576935 = 2365403) B2365403
theorem B11972609 : Blo 1576486 11972609 := bstep (se 2 (by rfl) ⟨4489728, by rfl⟩ : syracuseStep 11972609 = 8979457) B8979457
theorem B4796425 : Blo 1576486 4796425 := bstep (se 2 (by rfl) ⟨1798659, by rfl⟩ : syracuseStep 4796425 = 3597319) B3597319
theorem B8531993 : Blo 1576486 8531993 := bstep (se 2 (by rfl) ⟨3199497, by rfl⟩ : syracuseStep 8531993 = 6398995) B6398995
theorem B90935459 : Blo 1576486 90935459 := bstep (se 1 (by rfl) ⟨68201594, by rfl⟩ : syracuseStep 90935459 = 136403189) B136403189
theorem B43159715 : Blo 1576486 43159715 := bstep (se 1 (by rfl) ⟨32369786, by rfl⟩ : syracuseStep 43159715 = 64739573) B64739573
theorem B1773787 : Blo 1576486 1773787 := bstep (se 1 (by rfl) ⟨1330340, by rfl⟩ : syracuseStep 1773787 = 2660681) B2660681
theorem B1577247 : Blo 1576486 1577247 := bstep (se 1 (by rfl) ⟨1182935, by rfl⟩ : syracuseStep 1577247 = 2365871) B2365871
theorem B1683751 : Blo 1576486 1683751 := bstep (se 1 (by rfl) ⟨1262813, by rfl⟩ : syracuseStep 1683751 = 2525627) B2525627
theorem B3551561 : Blo 1576486 3551561 := bstep (se 2 (by rfl) ⟨1331835, by rfl⟩ : syracuseStep 3551561 = 2663671) B2663671
theorem B5321051 : Blo 1576486 5321051 := bstep (se 1 (by rfl) ⟨3990788, by rfl⟩ : syracuseStep 5321051 = 7981577) B7981577
theorem B1577307 : Blo 1576486 1577307 := bstep (se 1 (by rfl) ⟨1182980, by rfl⟩ : syracuseStep 1577307 = 2365961) B2365961
theorem B3551579 : Blo 1576486 3551579 := bstep (se 1 (by rfl) ⟨2663684, by rfl⟩ : syracuseStep 3551579 = 5327369) B5327369
theorem B1577327 : Blo 1576486 1577327 := bstep (se 1 (by rfl) ⟨1182995, by rfl⟩ : syracuseStep 1577327 = 2365991) B2365991
theorem B1577383 : Blo 1576486 1577383 := bstep (se 1 (by rfl) ⟨1183037, by rfl⟩ : syracuseStep 1577383 = 2366075) B2366075
theorem B4264417 : Blo 1576486 4264417 := bstep (se 2 (by rfl) ⟨1599156, by rfl⟩ : syracuseStep 4264417 = 3198313) B3198313
theorem B73855469 : Blo 1576486 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B1774075 : Blo 1576486 1774075 := bstep (se 1 (by rfl) ⟨1330556, by rfl⟩ : syracuseStep 1774075 = 2661113) B2661113
theorem B1577467 : Blo 1576486 1577467 := bstep (se 1 (by rfl) ⟨1183100, by rfl⟩ : syracuseStep 1577467 = 2366201) B2366201
theorem B17052221 : Blo 1576486 17052221 := bstep (se 3 (by rfl) ⟨3197291, by rfl⟩ : syracuseStep 17052221 = 6394583) B6394583
theorem B1577535 : Blo 1576486 1577535 := bstep (se 1 (by rfl) ⟨1183151, by rfl⟩ : syracuseStep 1577535 = 2366303) B2366303
theorem B1577543 : Blo 1576486 1577543 := bstep (se 1 (by rfl) ⟨1183157, by rfl⟩ : syracuseStep 1577543 = 2366315) B2366315
theorem B1774255 : Blo 1576486 1774255 := bstep (se 1 (by rfl) ⟨1330691, by rfl⟩ : syracuseStep 1774255 = 2661383) B2661383
theorem B17969849 : Blo 1576486 17969849 := bstep (se 2 (by rfl) ⟨6738693, by rfl⟩ : syracuseStep 17969849 = 13477387) B13477387
theorem B1577695 : Blo 1576486 1577695 := bstep (se 1 (by rfl) ⟨1183271, by rfl⟩ : syracuseStep 1577695 = 2366543) B2366543
theorem B1577775 : Blo 1576486 1577775 := bstep (se 1 (by rfl) ⟨1183331, by rfl⟩ : syracuseStep 1577775 = 2366663) B2366663
theorem B1577883 : Blo 1576486 1577883 := bstep (se 1 (by rfl) ⟨1183412, by rfl⟩ : syracuseStep 1577883 = 2366825) B2366825
theorem B1774543 : Blo 1576486 1774543 := bstep (se 1 (by rfl) ⟨1330907, by rfl⟩ : syracuseStep 1774543 = 2661815) B2661815
theorem B1577935 : Blo 1576486 1577935 := bstep (se 1 (by rfl) ⟨1183451, by rfl⟩ : syracuseStep 1577935 = 2366903) B2366903
theorem B15168485 : Blo 1576486 15168485 := bstep (se 4 (by rfl) ⟨1422045, by rfl⟩ : syracuseStep 15168485 = 2844091) B2844091
theorem B7492583 : Blo 1576486 7492583 := bstep (se 1 (by rfl) ⟨5619437, by rfl⟩ : syracuseStep 7492583 = 11238875) B11238875
theorem B1577959 : Blo 1576486 1577959 := bstep (se 1 (by rfl) ⟨1183469, by rfl⟩ : syracuseStep 1577959 = 2366939) B2366939
theorem B9106589 : Blo 1576486 9106589 := bstep (se 3 (by rfl) ⟨1707485, by rfl⟩ : syracuseStep 9106589 = 3414971) B3414971
theorem B1578271 : Blo 1576486 1578271 := bstep (se 1 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 1578271 = 2367407) B2367407
theorem B5322023 : Blo 1576486 5322023 := bstep (se 1 (by rfl) ⟨3991517, by rfl⟩ : syracuseStep 5322023 = 7983035) B7983035
theorem B1774939 : Blo 1576486 1774939 := bstep (se 1 (by rfl) ⟨1331204, by rfl⟩ : syracuseStep 1774939 = 2662409) B2662409
theorem B1578331 : Blo 1576486 1578331 := bstep (se 1 (by rfl) ⟨1183748, by rfl⟩ : syracuseStep 1578331 = 2367497) B2367497
theorem B7984493 : Blo 1576486 7984493 := bstep (se 3 (by rfl) ⟨1497092, by rfl⟩ : syracuseStep 7984493 = 2994185) B2994185
theorem B1578351 : Blo 1576486 1578351 := bstep (se 1 (by rfl) ⟨1183763, by rfl⟩ : syracuseStep 1578351 = 2367527) B2367527
theorem B13653373 : Blo 1576486 13653373 := bstep (se 3 (by rfl) ⟨2560007, by rfl⟩ : syracuseStep 13653373 = 5120015) B5120015
theorem B2364809 : Blo 1576486 2364809 := bstep (se 2 (by rfl) ⟨886803, by rfl⟩ : syracuseStep 2364809 = 1773607) B1773607
theorem B3995041 : Blo 1576486 3995041 := bstep (se 2 (by rfl) ⟨1498140, by rfl⟩ : syracuseStep 3995041 = 2996281) B2996281
theorem B1578407 : Blo 1576486 1578407 := bstep (se 1 (by rfl) ⟨1183805, by rfl⟩ : syracuseStep 1578407 = 2367611) B2367611
theorem B1775047 : Blo 1576486 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B13473287 : Blo 1576486 13473287 := bstep (se 1 (by rfl) ⟨10104965, by rfl⟩ : syracuseStep 13473287 = 20209931) B20209931
theorem B2995795 : Blo 1576486 2995795 := bstep (se 1 (by rfl) ⟨2246846, by rfl⟩ : syracuseStep 2995795 = 4493693) B4493693
theorem B7583321 : Blo 1576486 7583321 := bstep (se 2 (by rfl) ⟨2843745, by rfl⟩ : syracuseStep 7583321 = 5687491) B5687491
theorem B5052061 : Blo 1576486 5052061 := bstep (se 3 (by rfl) ⟨947261, by rfl⟩ : syracuseStep 5052061 = 1894523) B1894523
theorem B12785339 : Blo 1576486 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B2365163 : Blo 1576486 2365163 := bstep (se 1 (by rfl) ⟨1773872, by rfl⟩ : syracuseStep 2365163 = 3547745) B3547745
theorem B1775407 : Blo 1576486 1775407 := bstep (se 1 (by rfl) ⟨1331555, by rfl⟩ : syracuseStep 1775407 = 2663111) B2663111
theorem B2996023 : Blo 1576486 2996023 := bstep (se 1 (by rfl) ⟨2247017, by rfl⟩ : syracuseStep 2996023 = 4494035) B4494035
theorem B8099671 : Blo 1576486 8099671 := bstep (se 1 (by rfl) ⟨6074753, by rfl⟩ : syracuseStep 8099671 = 12149507) B12149507
theorem B1775515 : Blo 1576486 1775515 := bstep (se 1 (by rfl) ⟨1331636, by rfl⟩ : syracuseStep 1775515 = 2663273) B2663273
theorem B2365391 : Blo 1576486 2365391 := bstep (se 1 (by rfl) ⟨1774043, by rfl⟩ : syracuseStep 2365391 = 3548087) B3548087
theorem B1996751 : Blo 1576486 1996751 := bstep (se 1 (by rfl) ⟨1497563, by rfl⟩ : syracuseStep 1996751 = 2995127) B2995127
theorem B11376683 : Blo 1576486 11376683 := bstep (se 1 (by rfl) ⟨8532512, by rfl⟩ : syracuseStep 11376683 = 17065025) B17065025
theorem B20224079 : Blo 1576486 20224079 := bstep (se 1 (by rfl) ⟨15168059, by rfl⟩ : syracuseStep 20224079 = 30336119) B30336119
theorem B14596175 : Blo 1576486 14596175 := bstep (se 1 (by rfl) ⟨10947131, by rfl⟩ : syracuseStep 14596175 = 21894263) B21894263
theorem B5322887 : Blo 1576486 5322887 := bstep (se 1 (by rfl) ⟨3992165, by rfl⟩ : syracuseStep 5322887 = 7984331) B7984331
theorem B140196109 : Blo 1576486 140196109 := bstep (se 3 (by rfl) ⟨26286770, by rfl⟩ : syracuseStep 140196109 = 52573541) B52573541
theorem B2365787 : Blo 1576486 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B4266407 : Blo 1576486 4266407 := bstep (se 1 (by rfl) ⟨3199805, by rfl⟩ : syracuseStep 4266407 = 6399611) B6399611
theorem B2366015 : Blo 1576486 2366015 := bstep (se 1 (by rfl) ⟨1774511, by rfl⟩ : syracuseStep 2366015 = 3549023) B3549023
theorem B2660971 : Blo 1576486 2660971 := bstep (se 1 (by rfl) ⟨1995728, by rfl⟩ : syracuseStep 2660971 = 3991457) B3991457
theorem B4045483 : Blo 1576486 4045483 := bstep (se 1 (by rfl) ⟨3034112, by rfl⟩ : syracuseStep 4045483 = 6068225) B6068225
theorem B2366135 : Blo 1576486 2366135 := bstep (se 1 (by rfl) ⟨1774601, by rfl⟩ : syracuseStep 2366135 = 3549203) B3549203
theorem B41540471 : Blo 1576486 41540471 := bstep (se 1 (by rfl) ⟨31155353, by rfl⟩ : syracuseStep 41540471 = 62310707) B62310707
theorem B2661275 : Blo 1576486 2661275 := bstep (se 1 (by rfl) ⟨1995956, by rfl⟩ : syracuseStep 2661275 = 3991913) B3991913
theorem B2366363 : Blo 1576486 2366363 := bstep (se 1 (by rfl) ⟨1774772, by rfl⟩ : syracuseStep 2366363 = 3549545) B3549545
theorem B1997723 : Blo 1576486 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B17046557 : Blo 1576486 17046557 := bstep (se 3 (by rfl) ⟨3196229, by rfl⟩ : syracuseStep 17046557 = 6392459) B6392459
theorem B93494405 : Blo 1576486 93494405 := bstep (se 4 (by rfl) ⟨8765100, by rfl⟩ : syracuseStep 93494405 = 17530201) B17530201
theorem B2399465 : Blo 1576486 2399465 := bstep (se 2 (by rfl) ⟨899799, by rfl⟩ : syracuseStep 2399465 = 1799599) B1799599
theorem B2366759 : Blo 1576486 2366759 := bstep (se 1 (by rfl) ⟨1775069, by rfl⟩ : syracuseStep 2366759 = 3550139) B3550139
theorem B5324129 : Blo 1576486 5324129 := bstep (se 2 (by rfl) ⟨1996548, by rfl⟩ : syracuseStep 5324129 = 3993097) B3993097
theorem B2022779 : Blo 1576486 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B2366843 : Blo 1576486 2366843 := bstep (se 1 (by rfl) ⟨1775132, by rfl⟩ : syracuseStep 2366843 = 3550265) B3550265
theorem B2276857 : Blo 1576486 2276857 := bstep (se 2 (by rfl) ⟨853821, by rfl⟩ : syracuseStep 2276857 = 1707643) B1707643
theorem B2366969 : Blo 1576486 2366969 := bstep (se 2 (by rfl) ⟨887613, by rfl⟩ : syracuseStep 2366969 = 1775227) B1775227
theorem B7577171 : Blo 1576486 7577171 := bstep (se 1 (by rfl) ⟨5682878, by rfl⟩ : syracuseStep 7577171 = 11365757) B11365757
theorem B2842195 : Blo 1576486 2842195 := bstep (se 1 (by rfl) ⟨2131646, by rfl⟩ : syracuseStep 2842195 = 4263293) B4263293
theorem B2367071 : Blo 1576486 2367071 := bstep (se 1 (by rfl) ⟨1775303, by rfl⟩ : syracuseStep 2367071 = 3550607) B3550607
theorem B7986923 : Blo 1576486 7986923 := bstep (se 1 (by rfl) ⟨5990192, by rfl⟩ : syracuseStep 7986923 = 11980385) B11980385
theorem B15163139 : Blo 1576486 15163139 := bstep (se 1 (by rfl) ⟨11372354, by rfl⟩ : syracuseStep 15163139 = 22744709) B22744709
theorem B57573125 : Blo 1576486 57573125 := bstep (se 4 (by rfl) ⟨5397480, by rfl⟩ : syracuseStep 57573125 = 10794961) B10794961
theorem B2367287 : Blo 1576486 2367287 := bstep (se 1 (by rfl) ⟨1775465, by rfl⟩ : syracuseStep 2367287 = 3550931) B3550931
theorem B5324939 : Blo 1576486 5324939 := bstep (se 1 (by rfl) ⟨3993704, by rfl⟩ : syracuseStep 5324939 = 7987409) B7987409
theorem B2367707 : Blo 1576486 2367707 := bstep (se 1 (by rfl) ⟨1775780, by rfl⟩ : syracuseStep 2367707 = 3551561) B3551561
theorem B3547367 : Blo 1576486 3547367 := bstep (se 1 (by rfl) ⟨2660525, by rfl⟩ : syracuseStep 3547367 = 5321051) B5321051
theorem B2367719 : Blo 1576486 2367719 := bstep (se 1 (by rfl) ⟨1775789, by rfl⟩ : syracuseStep 2367719 = 3551579) B3551579
theorem B2245001 : Blo 1576486 2245001 := bstep (se 2 (by rfl) ⟨841875, by rfl⟩ : syracuseStep 2245001 = 1683751) B1683751
theorem B5325263 : Blo 1576486 5325263 := bstep (se 1 (by rfl) ⟨3993947, by rfl⟩ : syracuseStep 5325263 = 7987895) B7987895
theorem B5685889 : Blo 1576486 5685889 := bstep (se 2 (by rfl) ⟨2132208, by rfl⟩ : syracuseStep 5685889 = 4264417) B4264417
theorem B6071059 : Blo 1576486 6071059 := bstep (se 1 (by rfl) ⟨4553294, by rfl⟩ : syracuseStep 6071059 = 9106589) B9106589
theorem B5325587 : Blo 1576486 5325587 := bstep (se 1 (by rfl) ⟨3994190, by rfl⟩ : syracuseStep 5325587 = 7988381) B7988381
theorem B2245423 : Blo 1576486 2245423 := bstep (se 1 (by rfl) ⟨1684067, by rfl⟩ : syracuseStep 2245423 = 3368135) B3368135
theorem B3547961 : Blo 1576486 3547961 := bstep (se 2 (by rfl) ⟨1330485, by rfl⟩ : syracuseStep 3547961 = 2660971) B2660971
theorem B3548015 : Blo 1576486 3548015 := bstep (se 1 (by rfl) ⟨2661011, by rfl⟩ : syracuseStep 3548015 = 5322023) B5322023
theorem B5055547 : Blo 1576486 5055547 := bstep (se 1 (by rfl) ⟨3791660, by rfl⟩ : syracuseStep 5055547 = 7583321) B7583321
theorem B3548591 : Blo 1576486 3548591 := bstep (se 1 (by rfl) ⟨2661443, by rfl⟩ : syracuseStep 3548591 = 5322887) B5322887
theorem B2844271 : Blo 1576486 2844271 := bstep (se 1 (by rfl) ⟨2133203, by rfl⟩ : syracuseStep 2844271 = 4266407) B4266407
theorem B5326451 : Blo 1576486 5326451 := bstep (se 1 (by rfl) ⟨3994838, by rfl⟩ : syracuseStep 5326451 = 7989677) B7989677
theorem B5326559 : Blo 1576486 5326559 := bstep (se 1 (by rfl) ⟨3994919, by rfl⟩ : syracuseStep 5326559 = 7989839) B7989839
theorem B18204497 : Blo 1576486 18204497 := bstep (se 2 (by rfl) ⟨6826686, by rfl⟩ : syracuseStep 18204497 = 13653373) B13653373
theorem B5326721 : Blo 1576486 5326721 := bstep (se 2 (by rfl) ⟨1997520, by rfl⟩ : syracuseStep 5326721 = 3995041) B3995041
theorem B5990345 : Blo 1576486 5990345 := bstep (se 2 (by rfl) ⟨2246379, by rfl⟩ : syracuseStep 5990345 = 4492759) B4492759
theorem B11364371 : Blo 1576486 11364371 := bstep (se 1 (by rfl) ⟨8523278, by rfl⟩ : syracuseStep 11364371 = 17046557) B17046557
theorem B1599643 : Blo 1576486 1599643 := bstep (se 1 (by rfl) ⟨1199732, by rfl⟩ : syracuseStep 1599643 = 2399465) B2399465
theorem B6736081 : Blo 1576486 6736081 := bstep (se 2 (by rfl) ⟨2526030, by rfl⟩ : syracuseStep 6736081 = 5052061) B5052061
theorem B3549419 : Blo 1576486 3549419 := bstep (se 1 (by rfl) ⟨2662064, by rfl⟩ : syracuseStep 3549419 = 5324129) B5324129
theorem B3991801 : Blo 1576486 3991801 := bstep (se 2 (by rfl) ⟨1496925, by rfl⟩ : syracuseStep 3991801 = 2993851) B2993851
theorem B5327261 : Blo 1576486 5327261 := bstep (se 3 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 5327261 = 1997723) B1997723
theorem B11372993 : Blo 1576486 11372993 := bstep (se 2 (by rfl) ⟨4264872, by rfl⟩ : syracuseStep 11372993 = 8529745) B8529745
theorem B10799561 : Blo 1576486 10799561 := bstep (se 2 (by rfl) ⟨4049835, by rfl⟩ : syracuseStep 10799561 = 8099671) B8099671
theorem B38382083 : Blo 1576486 38382083 := bstep (se 1 (by rfl) ⟨28786562, by rfl⟩ : syracuseStep 38382083 = 57573125) B57573125
theorem B7981739 : Blo 1576486 7981739 := bstep (se 1 (by rfl) ⟨5986304, by rfl⟩ : syracuseStep 7981739 = 11972609) B11972609
theorem B5687995 : Blo 1576486 5687995 := bstep (se 1 (by rfl) ⟨4265996, by rfl⟩ : syracuseStep 5687995 = 8531993) B8531993
theorem B60623639 : Blo 1576486 60623639 := bstep (se 1 (by rfl) ⟨45467729, by rfl⟩ : syracuseStep 60623639 = 90935459) B90935459
theorem B28773143 : Blo 1576486 28773143 := bstep (se 1 (by rfl) ⟨21579857, by rfl⟩ : syracuseStep 28773143 = 43159715) B43159715
theorem B10791899 : Blo 1576486 10791899 := bstep (se 1 (by rfl) ⟨8093924, by rfl⟩ : syracuseStep 10791899 = 16187849) B16187849
theorem B49236979 : Blo 1576486 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B186928145 : Blo 1576486 186928145 := bstep (se 2 (by rfl) ⟨70098054, by rfl⟩ : syracuseStep 186928145 = 140196109) B140196109
theorem B11979899 : Blo 1576486 11979899 := bstep (se 1 (by rfl) ⟨8984924, by rfl⟩ : syracuseStep 11979899 = 17969849) B17969849
theorem B2526473 : Blo 1576486 2526473 := bstep (se 2 (by rfl) ⟨947427, by rfl⟩ : syracuseStep 2526473 = 1894855) B1894855
theorem B10112323 : Blo 1576486 10112323 := bstep (se 1 (by rfl) ⟨7584242, by rfl⟩ : syracuseStep 10112323 = 15168485) B15168485
theorem B3550715 : Blo 1576486 3550715 := bstep (se 1 (by rfl) ⟨2663036, by rfl⟩ : syracuseStep 3550715 = 5326073) B5326073
theorem B1576539 : Blo 1576486 1576539 := bstep (se 1 (by rfl) ⟨1182404, by rfl⟩ : syracuseStep 1576539 = 2364809) B2364809
theorem B5394077 : Blo 1576486 5394077 := bstep (se 3 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 5394077 = 2022779) B2022779
theorem B8982191 : Blo 1576486 8982191 := bstep (se 1 (by rfl) ⟨6736643, by rfl⟩ : syracuseStep 8982191 = 13473287) B13473287
theorem B3550895 : Blo 1576486 3550895 := bstep (se 1 (by rfl) ⟨2663171, by rfl⟩ : syracuseStep 3550895 = 5326343) B5326343
theorem B8523559 : Blo 1576486 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B1576775 : Blo 1576486 1576775 := bstep (se 1 (by rfl) ⟨1182581, by rfl⟩ : syracuseStep 1576775 = 2365163) B2365163
theorem B1576927 : Blo 1576486 1576927 := bstep (se 1 (by rfl) ⟨1182695, by rfl⟩ : syracuseStep 1576927 = 2365391) B2365391
theorem B5320889 : Blo 1576486 5320889 := bstep (se 2 (by rfl) ⟨1995333, by rfl⟩ : syracuseStep 5320889 = 3990667) B3990667
theorem B1577191 : Blo 1576486 1577191 := bstep (se 1 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 1577191 = 2365787) B2365787
theorem B3551543 : Blo 1576486 3551543 := bstep (se 1 (by rfl) ⟨2663657, by rfl⟩ : syracuseStep 3551543 = 5327315) B5327315
theorem B9597251 : Blo 1576486 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B9597275 : Blo 1576486 9597275 := bstep (se 1 (by rfl) ⟨7197956, by rfl⟩ : syracuseStep 9597275 = 14395913) B14395913
theorem B1577343 : Blo 1576486 1577343 := bstep (se 1 (by rfl) ⟨1183007, by rfl⟩ : syracuseStep 1577343 = 2366015) B2366015
theorem B1577423 : Blo 1576486 1577423 := bstep (se 1 (by rfl) ⟨1183067, by rfl⟩ : syracuseStep 1577423 = 2366135) B2366135
theorem B27693647 : Blo 1576486 27693647 := bstep (se 1 (by rfl) ⟨20770235, by rfl⟩ : syracuseStep 27693647 = 41540471) B41540471
theorem B1774183 : Blo 1576486 1774183 := bstep (se 1 (by rfl) ⟨1330637, by rfl⟩ : syracuseStep 1774183 = 2661275) B2661275
theorem B1577575 : Blo 1576486 1577575 := bstep (se 1 (by rfl) ⟨1183181, by rfl⟩ : syracuseStep 1577575 = 2366363) B2366363
theorem B3035809 : Blo 1576486 3035809 := bstep (se 2 (by rfl) ⟨1138428, by rfl⟩ : syracuseStep 3035809 = 2276857) B2276857
theorem B10105559 : Blo 1576486 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B62329603 : Blo 1576486 62329603 := bstep (se 1 (by rfl) ⟨46747202, by rfl⟩ : syracuseStep 62329603 = 93494405) B93494405
theorem B3789593 : Blo 1576486 3789593 := bstep (se 2 (by rfl) ⟨1421097, by rfl⟩ : syracuseStep 3789593 = 2842195) B2842195
theorem B3994393 : Blo 1576486 3994393 := bstep (se 2 (by rfl) ⟨1497897, by rfl⟩ : syracuseStep 3994393 = 2995795) B2995795
theorem B1577839 : Blo 1576486 1577839 := bstep (se 1 (by rfl) ⟨1183379, by rfl⟩ : syracuseStep 1577839 = 2366759) B2366759
theorem B1577895 : Blo 1576486 1577895 := bstep (se 1 (by rfl) ⟨1183421, by rfl⟩ : syracuseStep 1577895 = 2366843) B2366843
theorem B1577979 : Blo 1576486 1577979 := bstep (se 1 (by rfl) ⟨1183484, by rfl⟩ : syracuseStep 1577979 = 2366969) B2366969
theorem B5051447 : Blo 1576486 5051447 := bstep (se 1 (by rfl) ⟨3788585, by rfl⟩ : syracuseStep 5051447 = 7577171) B7577171
theorem B1578047 : Blo 1576486 1578047 := bstep (se 1 (by rfl) ⟨1183535, by rfl⟩ : syracuseStep 1578047 = 2367071) B2367071
theorem B3994697 : Blo 1576486 3994697 := bstep (se 2 (by rfl) ⟨1498011, by rfl⟩ : syracuseStep 3994697 = 2996023) B2996023
theorem B8983649 : Blo 1576486 8983649 := bstep (se 2 (by rfl) ⟨3368868, by rfl⟩ : syracuseStep 8983649 = 6737737) B6737737
theorem B1578191 : Blo 1576486 1578191 := bstep (se 1 (by rfl) ⟨1183643, by rfl⟩ : syracuseStep 1578191 = 2367287) B2367287
theorem B6657233 : Blo 1576486 6657233 := bstep (se 2 (by rfl) ⟨2496462, by rfl⟩ : syracuseStep 6657233 = 4992925) B4992925
theorem B88716545 : Blo 1576486 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B6395233 : Blo 1576486 6395233 := bstep (se 2 (by rfl) ⟨2398212, by rfl⟩ : syracuseStep 6395233 = 4796425) B4796425
theorem B2364827 : Blo 1576486 2364827 := bstep (se 1 (by rfl) ⟨1773620, by rfl⟩ : syracuseStep 2364827 = 3547241) B3547241
theorem B1578395 : Blo 1576486 1578395 := bstep (se 1 (by rfl) ⟨1183796, by rfl⟩ : syracuseStep 1578395 = 2367593) B2367593
theorem B2365049 : Blo 1576486 2365049 := bstep (se 2 (by rfl) ⟨886893, by rfl⟩ : syracuseStep 2365049 = 1773787) B1773787
theorem B11368147 : Blo 1576486 11368147 := bstep (se 1 (by rfl) ⟨8526110, by rfl⟩ : syracuseStep 11368147 = 17052221) B17052221
theorem B2365151 : Blo 1576486 2365151 := bstep (se 1 (by rfl) ⟨1773863, by rfl⟩ : syracuseStep 2365151 = 3547727) B3547727
theorem B2365247 : Blo 1576486 2365247 := bstep (se 1 (by rfl) ⟨1773935, by rfl⟩ : syracuseStep 2365247 = 3547871) B3547871
theorem B4798345 : Blo 1576486 4798345 := bstep (se 2 (by rfl) ⟨1799379, by rfl⟩ : syracuseStep 4798345 = 3598759) B3598759
theorem B7583645 : Blo 1576486 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B2365415 : Blo 1576486 2365415 := bstep (se 1 (by rfl) ⟨1774061, by rfl⟩ : syracuseStep 2365415 = 3548123) B3548123
theorem B8525807 : Blo 1576486 8525807 := bstep (se 1 (by rfl) ⟨6394355, by rfl⟩ : syracuseStep 8525807 = 12788711) B12788711
theorem B4995055 : Blo 1576486 4995055 := bstep (se 1 (by rfl) ⟨3746291, by rfl⟩ : syracuseStep 4995055 = 7492583) B7492583
theorem B16193519 : Blo 1576486 16193519 := bstep (se 1 (by rfl) ⟨12145139, by rfl⟩ : syracuseStep 16193519 = 24290279) B24290279
theorem B2365433 : Blo 1576486 2365433 := bstep (se 2 (by rfl) ⟨887037, by rfl⟩ : syracuseStep 2365433 = 1774075) B1774075
theorem B46102565 : Blo 1576486 46102565 := bstep (se 4 (by rfl) ⟨4322115, by rfl⟩ : syracuseStep 46102565 = 8644231) B8644231
theorem B2365535 : Blo 1576486 2365535 := bstep (se 1 (by rfl) ⟨1774151, by rfl⟩ : syracuseStep 2365535 = 3548303) B3548303
theorem B2365595 : Blo 1576486 2365595 := bstep (se 1 (by rfl) ⟨1774196, by rfl⟩ : syracuseStep 2365595 = 3548393) B3548393
theorem B2365631 : Blo 1576486 2365631 := bstep (se 1 (by rfl) ⟨1774223, by rfl⟩ : syracuseStep 2365631 = 3548447) B3548447
theorem B21575909 : Blo 1576486 21575909 := bstep (se 4 (by rfl) ⟨2022741, by rfl⟩ : syracuseStep 21575909 = 4045483) B4045483
theorem B2365673 : Blo 1576486 2365673 := bstep (se 2 (by rfl) ⟨887127, by rfl⟩ : syracuseStep 2365673 = 1774255) B1774255
theorem B5322995 : Blo 1576486 5322995 := bstep (se 1 (by rfl) ⟨3992246, by rfl⟩ : syracuseStep 5322995 = 7984493) B7984493
theorem B11376911 : Blo 1576486 11376911 := bstep (se 1 (by rfl) ⟨8532683, by rfl⟩ : syracuseStep 11376911 = 17065367) B17065367
theorem B2660647 : Blo 1576486 2660647 := bstep (se 1 (by rfl) ⟨1995485, by rfl⟩ : syracuseStep 2660647 = 3990971) B3990971
theorem B5323049 : Blo 1576486 5323049 := bstep (se 2 (by rfl) ⟨1996143, by rfl⟩ : syracuseStep 5323049 = 3992287) B3992287
theorem B7985627 : Blo 1576486 7985627 := bstep (se 1 (by rfl) ⟨5989220, by rfl⟩ : syracuseStep 7985627 = 11978441) B11978441
theorem B2841115 : Blo 1576486 2841115 := bstep (se 1 (by rfl) ⟨2130836, by rfl⟩ : syracuseStep 2841115 = 4261673) B4261673
theorem B2365979 : Blo 1576486 2365979 := bstep (se 1 (by rfl) ⟨1774484, by rfl⟩ : syracuseStep 2365979 = 3548969) B3548969
theorem B2366057 : Blo 1576486 2366057 := bstep (se 2 (by rfl) ⟨887271, by rfl⟩ : syracuseStep 2366057 = 1774543) B1774543
theorem B5986973 : Blo 1576486 5986973 := bstep (se 3 (by rfl) ⟨1122557, by rfl⟩ : syracuseStep 5986973 = 2245115) B2245115
theorem B7584455 : Blo 1576486 7584455 := bstep (se 1 (by rfl) ⟨5688341, by rfl⟩ : syracuseStep 7584455 = 11376683) B11376683
theorem B13482719 : Blo 1576486 13482719 := bstep (se 1 (by rfl) ⟨10112039, by rfl⟩ : syracuseStep 13482719 = 20224079) B20224079
theorem B9730783 : Blo 1576486 9730783 := bstep (se 1 (by rfl) ⟨7298087, by rfl⟩ : syracuseStep 9730783 = 14596175) B14596175
theorem B6740779 : Blo 1576486 6740779 := bstep (se 1 (by rfl) ⟨5055584, by rfl⟩ : syracuseStep 6740779 = 10111169) B10111169
theorem B5987155 : Blo 1576486 5987155 := bstep (se 1 (by rfl) ⟨4490366, by rfl⟩ : syracuseStep 5987155 = 8980733) B8980733
theorem B41515981 : Blo 1576486 41515981 := bstep (se 3 (by rfl) ⟨7784246, by rfl⟩ : syracuseStep 41515981 = 15568493) B15568493
theorem B2366585 : Blo 1576486 2366585 := bstep (se 2 (by rfl) ⟨887469, by rfl⟩ : syracuseStep 2366585 = 1774939) B1774939
theorem B8985815 : Blo 1576486 8985815 := bstep (se 1 (by rfl) ⟨6739361, by rfl⟩ : syracuseStep 8985815 = 13478723) B13478723
theorem B2661599 : Blo 1576486 2661599 := bstep (se 1 (by rfl) ⟨1996199, by rfl⟩ : syracuseStep 2661599 = 3992399) B3992399
theorem B2366687 : Blo 1576486 2366687 := bstep (se 1 (by rfl) ⟨1775015, by rfl⟩ : syracuseStep 2366687 = 3550031) B3550031
theorem B2366729 : Blo 1576486 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B2366831 : Blo 1576486 2366831 := bstep (se 1 (by rfl) ⟨1775123, by rfl⟩ : syracuseStep 2366831 = 3550247) B3550247
theorem B5053907 : Blo 1576486 5053907 := bstep (se 1 (by rfl) ⟨3790430, by rfl⟩ : syracuseStep 5053907 = 7580861) B7580861
theorem B2366951 : Blo 1576486 2366951 := bstep (se 1 (by rfl) ⟨1775213, by rfl⟩ : syracuseStep 2366951 = 3550427) B3550427
theorem B2367083 : Blo 1576486 2367083 := bstep (se 1 (by rfl) ⟨1775312, by rfl⟩ : syracuseStep 2367083 = 3550625) B3550625
theorem B2662031 : Blo 1576486 2662031 := bstep (se 1 (by rfl) ⟨1996523, by rfl⟩ : syracuseStep 2662031 = 3993047) B3993047
theorem B2367209 : Blo 1576486 2367209 := bstep (se 2 (by rfl) ⟨887703, by rfl⟩ : syracuseStep 2367209 = 1775407) B1775407
theorem B5324615 : Blo 1576486 5324615 := bstep (se 1 (by rfl) ⟨3993461, by rfl⟩ : syracuseStep 5324615 = 7986923) B7986923
theorem B10108759 : Blo 1576486 10108759 := bstep (se 1 (by rfl) ⟨7581569, by rfl⟩ : syracuseStep 10108759 = 15163139) B15163139
theorem B2662267 : Blo 1576486 2662267 := bstep (se 1 (by rfl) ⟨1996700, by rfl⟩ : syracuseStep 2662267 = 3993401) B3993401
theorem B2367353 : Blo 1576486 2367353 := bstep (se 2 (by rfl) ⟨887757, by rfl⟩ : syracuseStep 2367353 = 1775515) B1775515
theorem B7192445 : Blo 1576486 7192445 := bstep (se 3 (by rfl) ⟨1348583, by rfl⟩ : syracuseStep 7192445 = 2697167) B2697167
theorem B5324669 : Blo 1576486 5324669 := bstep (se 3 (by rfl) ⟨998375, by rfl⟩ : syracuseStep 5324669 = 1996751) B1996751
theorem B2367455 : Blo 1576486 2367455 := bstep (se 1 (by rfl) ⟨1775591, by rfl⟩ : syracuseStep 2367455 = 3551183) B3551183
theorem B3547259 : Blo 1576486 3547259 := bstep (se 1 (by rfl) ⟨2660444, by rfl⟩ : syracuseStep 3547259 = 5320889) B5320889
theorem B2367695 : Blo 1576486 2367695 := bstep (se 1 (by rfl) ⟨1775771, by rfl⟩ : syracuseStep 2367695 = 3551543) B3551543
theorem B6398183 : Blo 1576486 6398183 := bstep (se 1 (by rfl) ⟨4798637, by rfl⟩ : syracuseStep 6398183 = 9597275) B9597275
theorem B3547529 : Blo 1576486 3547529 := bstep (se 2 (by rfl) ⟨1330323, by rfl⟩ : syracuseStep 3547529 = 2660647) B2660647
theorem B17752621 : Blo 1576486 17752621 := bstep (se 3 (by rfl) ⟨3328616, by rfl⟩ : syracuseStep 17752621 = 6657233) B6657233
theorem B3367631 : Blo 1576486 3367631 := bstep (se 1 (by rfl) ⟨2525723, by rfl⟩ : syracuseStep 3367631 = 5051447) B5051447
theorem B2663131 : Blo 1576486 2663131 := bstep (se 1 (by rfl) ⟨1997348, by rfl⟩ : syracuseStep 2663131 = 3994697) B3994697
theorem B5989099 : Blo 1576486 5989099 := bstep (se 1 (by rfl) ⟨4491824, by rfl⟩ : syracuseStep 5989099 = 8983649) B8983649
theorem B25592669 : Blo 1576486 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B4047745 : Blo 1576486 4047745 := bstep (se 2 (by rfl) ⟨1517904, by rfl⟩ : syracuseStep 4047745 = 3035809) B3035809
theorem B8094745 : Blo 1576486 8094745 := bstep (se 2 (by rfl) ⟨3035529, by rfl⟩ : syracuseStep 8094745 = 6071059) B6071059
theorem B5325857 : Blo 1576486 5325857 := bstep (se 2 (by rfl) ⟨1997196, by rfl⟩ : syracuseStep 5325857 = 3994393) B3994393
theorem B8987705 : Blo 1576486 8987705 := bstep (se 2 (by rfl) ⟨3370389, by rfl⟩ : syracuseStep 8987705 = 6740779) B6740779
theorem B51897509 : Blo 1576486 51897509 := bstep (se 4 (by rfl) ⟨4865391, by rfl⟩ : syracuseStep 51897509 = 9730783) B9730783
theorem B76719413 : Blo 1576486 76719413 := bstep (se 5 (by rfl) ⟨3596222, by rfl⟩ : syracuseStep 76719413 = 7192445) B7192445
theorem B3548663 : Blo 1576486 3548663 := bstep (se 1 (by rfl) ⟨2661497, by rfl⟩ : syracuseStep 3548663 = 5322995) B5322995
theorem B3548699 : Blo 1576486 3548699 := bstep (se 1 (by rfl) ⟨2661524, by rfl⟩ : syracuseStep 3548699 = 5323049) B5323049
theorem B3991315 : Blo 1576486 3991315 := bstep (se 1 (by rfl) ⟨2993486, by rfl⟩ : syracuseStep 3991315 = 5986973) B5986973
theorem B5056303 : Blo 1576486 5056303 := bstep (se 1 (by rfl) ⟨3792227, by rfl⟩ : syracuseStep 5056303 = 7584455) B7584455
theorem B8988479 : Blo 1576486 8988479 := bstep (se 1 (by rfl) ⟨6741359, by rfl⟩ : syracuseStep 8988479 = 13482719) B13482719
theorem B7194599 : Blo 1576486 7194599 := bstep (se 1 (by rfl) ⟨5395949, by rfl⟩ : syracuseStep 7194599 = 10791899) B10791899
theorem B124618763 : Blo 1576486 124618763 := bstep (se 1 (by rfl) ⟨93464072, by rfl⟩ : syracuseStep 124618763 = 186928145) B186928145
theorem B5990543 : Blo 1576486 5990543 := bstep (se 1 (by rfl) ⟨4492907, by rfl⟩ : syracuseStep 5990543 = 8985815) B8985815
theorem B15157529 : Blo 1576486 15157529 := bstep (se 2 (by rfl) ⟨5684073, by rfl⟩ : syracuseStep 15157529 = 11368147) B11368147
theorem B3369271 : Blo 1576486 3369271 := bstep (se 1 (by rfl) ⟨2526953, by rfl⟩ : syracuseStep 3369271 = 5053907) B5053907
theorem B11364745 : Blo 1576486 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B13478345 : Blo 1576486 13478345 := bstep (se 2 (by rfl) ⟨5054379, by rfl⟩ : syracuseStep 13478345 = 10108759) B10108759
theorem B3549689 : Blo 1576486 3549689 := bstep (se 2 (by rfl) ⟨1331133, by rfl⟩ : syracuseStep 3549689 = 2662267) B2662267
theorem B3549743 : Blo 1576486 3549743 := bstep (se 1 (by rfl) ⟨2662307, by rfl⟩ : syracuseStep 3549743 = 5324615) B5324615
theorem B3549779 : Blo 1576486 3549779 := bstep (se 1 (by rfl) ⟨2662334, by rfl⟩ : syracuseStep 3549779 = 5324669) B5324669
theorem B3549959 : Blo 1576486 3549959 := bstep (se 1 (by rfl) ⟨2662469, by rfl⟩ : syracuseStep 3549959 = 5324939) B5324939
theorem B122940173 : Blo 1576486 122940173 := bstep (se 3 (by rfl) ⟨23051282, by rfl⟩ : syracuseStep 122940173 = 46102565) B46102565
theorem B2132857 : Blo 1576486 2132857 := bstep (se 2 (by rfl) ⟨799821, by rfl⟩ : syracuseStep 2132857 = 1599643) B1599643
theorem B8981441 : Blo 1576486 8981441 := bstep (se 2 (by rfl) ⟨3368040, by rfl⟩ : syracuseStep 8981441 = 6736081) B6736081
theorem B3550175 : Blo 1576486 3550175 := bstep (se 1 (by rfl) ⟨2662631, by rfl⟩ : syracuseStep 3550175 = 5325263) B5325263
theorem B6737039 : Blo 1576486 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B3550391 : Blo 1576486 3550391 := bstep (se 1 (by rfl) ⟨2662793, by rfl⟩ : syracuseStep 3550391 = 5325587) B5325587
theorem B2526395 : Blo 1576486 2526395 := bstep (se 1 (by rfl) ⟨1894796, by rfl⟩ : syracuseStep 2526395 = 3789593) B3789593
theorem B57535757 : Blo 1576486 57535757 := bstep (se 3 (by rfl) ⟨10787954, by rfl⟩ : syracuseStep 57535757 = 21575909) B21575909
theorem B3788153 : Blo 1576486 3788153 := bstep (se 2 (by rfl) ⟨1420557, by rfl⟩ : syracuseStep 3788153 = 2841115) B2841115
theorem B7581185 : Blo 1576486 7581185 := bstep (se 2 (by rfl) ⟨2842944, by rfl⟩ : syracuseStep 7581185 = 5685889) B5685889
theorem B1576551 : Blo 1576486 1576551 := bstep (se 1 (by rfl) ⟨1182413, by rfl⟩ : syracuseStep 1576551 = 2364827) B2364827
theorem B2993897 : Blo 1576486 2993897 := bstep (se 2 (by rfl) ⟨1122711, by rfl⟩ : syracuseStep 2993897 = 2245423) B2245423
theorem B3550967 : Blo 1576486 3550967 := bstep (se 1 (by rfl) ⟨2663225, by rfl⟩ : syracuseStep 3550967 = 5326451) B5326451
theorem B1576699 : Blo 1576486 1576699 := bstep (se 1 (by rfl) ⟨1182524, by rfl⟩ : syracuseStep 1576699 = 2365049) B2365049
theorem B7982873 : Blo 1576486 7982873 := bstep (se 2 (by rfl) ⟨2993577, by rfl⟩ : syracuseStep 7982873 = 5987155) B5987155
theorem B1576767 : Blo 1576486 1576767 := bstep (se 1 (by rfl) ⟨1182575, by rfl⟩ : syracuseStep 1576767 = 2365151) B2365151
theorem B3551039 : Blo 1576486 3551039 := bstep (se 1 (by rfl) ⟨2663279, by rfl⟩ : syracuseStep 3551039 = 5326559) B5326559
theorem B1576831 : Blo 1576486 1576831 := bstep (se 1 (by rfl) ⟨1182623, by rfl⟩ : syracuseStep 1576831 = 2365247) B2365247
theorem B12136331 : Blo 1576486 12136331 := bstep (se 1 (by rfl) ⟨9102248, by rfl⟩ : syracuseStep 12136331 = 18204497) B18204497
theorem B3551147 : Blo 1576486 3551147 := bstep (se 1 (by rfl) ⟨2663360, by rfl⟩ : syracuseStep 3551147 = 5326721) B5326721
theorem B3993563 : Blo 1576486 3993563 := bstep (se 1 (by rfl) ⟨2995172, by rfl⟩ : syracuseStep 3993563 = 5990345) B5990345
theorem B1576943 : Blo 1576486 1576943 := bstep (se 1 (by rfl) ⟨1182707, by rfl⟩ : syracuseStep 1576943 = 2365415) B2365415
theorem B1576955 : Blo 1576486 1576955 := bstep (se 1 (by rfl) ⟨1182716, by rfl⟩ : syracuseStep 1576955 = 2365433) B2365433
theorem B1577023 : Blo 1576486 1577023 := bstep (se 1 (by rfl) ⟨1182767, by rfl⟩ : syracuseStep 1577023 = 2365535) B2365535
theorem B1577063 : Blo 1576486 1577063 := bstep (se 1 (by rfl) ⟨1182797, by rfl⟩ : syracuseStep 1577063 = 2365595) B2365595
theorem B1577087 : Blo 1576486 1577087 := bstep (se 1 (by rfl) ⟨1182815, by rfl⟩ : syracuseStep 1577087 = 2365631) B2365631
theorem B1577115 : Blo 1576486 1577115 := bstep (se 1 (by rfl) ⟨1182836, by rfl⟩ : syracuseStep 1577115 = 2365673) B2365673
theorem B3551507 : Blo 1576486 3551507 := bstep (se 1 (by rfl) ⟨2663630, by rfl⟩ : syracuseStep 3551507 = 5327261) B5327261
theorem B7581995 : Blo 1576486 7581995 := bstep (se 1 (by rfl) ⟨5686496, by rfl⟩ : syracuseStep 7581995 = 11372993) B11372993
theorem B25588055 : Blo 1576486 25588055 := bstep (se 1 (by rfl) ⟨19191041, by rfl⟩ : syracuseStep 25588055 = 38382083) B38382083
theorem B1577319 : Blo 1576486 1577319 := bstep (se 1 (by rfl) ⟨1182989, by rfl⟩ : syracuseStep 1577319 = 2365979) B2365979
theorem B1577371 : Blo 1576486 1577371 := bstep (se 1 (by rfl) ⟨1183028, by rfl⟩ : syracuseStep 1577371 = 2366057) B2366057
theorem B5321159 : Blo 1576486 5321159 := bstep (se 1 (by rfl) ⟨3990869, by rfl⟩ : syracuseStep 5321159 = 7981739) B7981739
theorem B40415759 : Blo 1576486 40415759 := bstep (se 1 (by rfl) ⟨30311819, by rfl⟩ : syracuseStep 40415759 = 60623639) B60623639
theorem B19182095 : Blo 1576486 19182095 := bstep (se 1 (by rfl) ⟨14386571, by rfl⟩ : syracuseStep 19182095 = 28773143) B28773143
theorem B1577723 : Blo 1576486 1577723 := bstep (se 1 (by rfl) ⟨1183292, by rfl⟩ : syracuseStep 1577723 = 2366585) B2366585
theorem B1774399 : Blo 1576486 1774399 := bstep (se 1 (by rfl) ⟨1330799, by rfl⟩ : syracuseStep 1774399 = 2661599) B2661599
theorem B1577791 : Blo 1576486 1577791 := bstep (se 1 (by rfl) ⟨1183343, by rfl⟩ : syracuseStep 1577791 = 2366687) B2366687
theorem B1684315 : Blo 1576486 1684315 := bstep (se 1 (by rfl) ⟨1263236, by rfl⟩ : syracuseStep 1684315 = 2526473) B2526473
theorem B1577819 : Blo 1576486 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B1577887 : Blo 1576486 1577887 := bstep (se 1 (by rfl) ⟨1183415, by rfl⟩ : syracuseStep 1577887 = 2366831) B2366831
theorem B1577967 : Blo 1576486 1577967 := bstep (se 1 (by rfl) ⟨1183475, by rfl⟩ : syracuseStep 1577967 = 2366951) B2366951
theorem B221418565 : Blo 1576486 221418565 := bstep (se 4 (by rfl) ⟨20757990, by rfl⟩ : syracuseStep 221418565 = 41515981) B41515981
theorem B1578055 : Blo 1576486 1578055 := bstep (se 1 (by rfl) ⟨1183541, by rfl⟩ : syracuseStep 1578055 = 2367083) B2367083
theorem B20223053 : Blo 1576486 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B1774687 : Blo 1576486 1774687 := bstep (se 1 (by rfl) ⟨1331015, by rfl⟩ : syracuseStep 1774687 = 2662031) B2662031
theorem B1578139 : Blo 1576486 1578139 := bstep (se 1 (by rfl) ⟨1183604, by rfl⟩ : syracuseStep 1578139 = 2367209) B2367209
theorem B1578235 : Blo 1576486 1578235 := bstep (se 1 (by rfl) ⟨1183676, by rfl⟩ : syracuseStep 1578235 = 2367353) B2367353
theorem B1578303 : Blo 1576486 1578303 := bstep (se 1 (by rfl) ⟨1183727, by rfl⟩ : syracuseStep 1578303 = 2367455) B2367455
theorem B1578471 : Blo 1576486 1578471 := bstep (se 1 (by rfl) ⟨1183853, by rfl⟩ : syracuseStep 1578471 = 2367707) B2367707
theorem B2364911 : Blo 1576486 2364911 := bstep (se 1 (by rfl) ⟨1773683, by rfl⟩ : syracuseStep 2364911 = 3547367) B3547367
theorem B1578479 : Blo 1576486 1578479 := bstep (se 1 (by rfl) ⟨1183859, by rfl⟩ : syracuseStep 1578479 = 2367719) B2367719
theorem B5322401 : Blo 1576486 5322401 := bstep (se 2 (by rfl) ⟨1995900, by rfl⟩ : syracuseStep 5322401 = 3991801) B3991801
theorem B18462431 : Blo 1576486 18462431 := bstep (se 1 (by rfl) ⟨13846823, by rfl⟩ : syracuseStep 18462431 = 27693647) B27693647
theorem B2365307 : Blo 1576486 2365307 := bstep (se 1 (by rfl) ⟨1773980, by rfl⟩ : syracuseStep 2365307 = 3547961) B3547961
theorem B2365343 : Blo 1576486 2365343 := bstep (se 1 (by rfl) ⟨1774007, by rfl⟩ : syracuseStep 2365343 = 3548015) B3548015
theorem B2365577 : Blo 1576486 2365577 := bstep (se 2 (by rfl) ⟨887091, by rfl⟩ : syracuseStep 2365577 = 1774183) B1774183
theorem B59144363 : Blo 1576486 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B7583993 : Blo 1576486 7583993 := bstep (se 2 (by rfl) ⟨2843997, by rfl⟩ : syracuseStep 7583993 = 5687995) B5687995
theorem B2365727 : Blo 1576486 2365727 := bstep (se 1 (by rfl) ⟨1774295, by rfl⟩ : syracuseStep 2365727 = 3548591) B3548591
theorem B83106137 : Blo 1576486 83106137 := bstep (se 2 (by rfl) ⟨31164801, by rfl⟩ : syracuseStep 83106137 = 62329603) B62329603
theorem B5986669 : Blo 1576486 5986669 := bstep (se 3 (by rfl) ⟨1122500, by rfl⟩ : syracuseStep 5986669 = 2245001) B2245001
theorem B65649305 : Blo 1576486 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B5683871 : Blo 1576486 5683871 := bstep (se 1 (by rfl) ⟨4262903, by rfl⟩ : syracuseStep 5683871 = 8525807) B8525807
theorem B10795679 : Blo 1576486 10795679 := bstep (se 1 (by rfl) ⟨8096759, by rfl⟩ : syracuseStep 10795679 = 16193519) B16193519
theorem B7576247 : Blo 1576486 7576247 := bstep (se 1 (by rfl) ⟨5682185, by rfl⟩ : syracuseStep 7576247 = 11364371) B11364371
theorem B6740729 : Blo 1576486 6740729 := bstep (se 2 (by rfl) ⟨2527773, by rfl⟩ : syracuseStep 6740729 = 5055547) B5055547
theorem B2366279 : Blo 1576486 2366279 := bstep (se 1 (by rfl) ⟨1774709, by rfl⟩ : syracuseStep 2366279 = 3549419) B3549419
theorem B7584607 : Blo 1576486 7584607 := bstep (se 1 (by rfl) ⟨5688455, by rfl⟩ : syracuseStep 7584607 = 11376911) B11376911
theorem B7199707 : Blo 1576486 7199707 := bstep (se 1 (by rfl) ⟨5399780, by rfl⟩ : syracuseStep 7199707 = 10799561) B10799561
theorem B5323751 : Blo 1576486 5323751 := bstep (se 1 (by rfl) ⟨3992813, by rfl⟩ : syracuseStep 5323751 = 7985627) B7985627
theorem B13483097 : Blo 1576486 13483097 := bstep (se 2 (by rfl) ⟨5056161, by rfl⟩ : syracuseStep 13483097 = 10112323) B10112323
theorem B8526977 : Blo 1576486 8526977 := bstep (se 2 (by rfl) ⟨3197616, by rfl⟩ : syracuseStep 8526977 = 6395233) B6395233
theorem B7986599 : Blo 1576486 7986599 := bstep (se 1 (by rfl) ⟨5989949, by rfl⟩ : syracuseStep 7986599 = 11979899) B11979899
theorem B3792361 : Blo 1576486 3792361 := bstep (se 2 (by rfl) ⟨1422135, by rfl⟩ : syracuseStep 3792361 = 2844271) B2844271
theorem B2367143 : Blo 1576486 2367143 := bstep (se 1 (by rfl) ⟨1775357, by rfl⟩ : syracuseStep 2367143 = 3550715) B3550715
theorem B3596051 : Blo 1576486 3596051 := bstep (se 1 (by rfl) ⟨2697038, by rfl⟩ : syracuseStep 3596051 = 5394077) B5394077
theorem B5988127 : Blo 1576486 5988127 := bstep (se 1 (by rfl) ⟨4491095, by rfl⟩ : syracuseStep 5988127 = 8982191) B8982191
theorem B2367263 : Blo 1576486 2367263 := bstep (se 1 (by rfl) ⟨1775447, by rfl⟩ : syracuseStep 2367263 = 3550895) B3550895
theorem B6397793 : Blo 1576486 6397793 := bstep (se 2 (by rfl) ⟨2399172, by rfl⟩ : syracuseStep 6397793 = 4798345) B4798345
theorem B6660073 : Blo 1576486 6660073 := bstep (se 2 (by rfl) ⟨2497527, by rfl⟩ : syracuseStep 6660073 = 4995055) B4995055
theorem B332316701 : Blo 1576486 332316701 := bstep (se 3 (by rfl) ⟨62309381, by rfl⟩ : syracuseStep 332316701 = 124618763) B124618763
theorem B43171973 : Blo 1576486 43171973 := bstep (se 4 (by rfl) ⟨4047372, by rfl⟩ : syracuseStep 43171973 = 8094745) B8094745
theorem B2367671 : Blo 1576486 2367671 := bstep (se 1 (by rfl) ⟨1775753, by rfl⟩ : syracuseStep 2367671 = 3551507) B3551507
theorem B5054663 : Blo 1576486 5054663 := bstep (se 1 (by rfl) ⟨3790997, by rfl⟩ : syracuseStep 5054663 = 7581995) B7581995
theorem B3547439 : Blo 1576486 3547439 := bstep (se 1 (by rfl) ⟨2660579, by rfl⟩ : syracuseStep 3547439 = 5321159) B5321159
theorem B26943839 : Blo 1576486 26943839 := bstep (se 1 (by rfl) ⟨20207879, by rfl⟩ : syracuseStep 26943839 = 40415759) B40415759
theorem B12788063 : Blo 1576486 12788063 := bstep (se 1 (by rfl) ⟨9591047, by rfl⟩ : syracuseStep 12788063 = 19182095) B19182095
theorem B2245087 : Blo 1576486 2245087 := bstep (se 1 (by rfl) ⟨1683815, by rfl⟩ : syracuseStep 2245087 = 3367631) B3367631
theorem B3548267 : Blo 1576486 3548267 := bstep (se 1 (by rfl) ⟨2661200, by rfl⟩ : syracuseStep 3548267 = 5322401) B5322401
theorem B2245753 : Blo 1576486 2245753 := bstep (se 2 (by rfl) ⟨842157, by rfl⟩ : syracuseStep 2245753 = 1684315) B1684315
theorem B39429575 : Blo 1576486 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B5055995 : Blo 1576486 5055995 := bstep (se 1 (by rfl) ⟨3791996, by rfl⟩ : syracuseStep 5055995 = 7583993) B7583993
theorem B55404091 : Blo 1576486 55404091 := bstep (se 1 (by rfl) ⟨41553068, by rfl⟩ : syracuseStep 55404091 = 83106137) B83106137
theorem B15156989 : Blo 1576486 15156989 := bstep (se 3 (by rfl) ⟨2841935, by rfl⟩ : syracuseStep 15156989 = 5683871) B5683871
theorem B5056481 : Blo 1576486 5056481 := bstep (se 2 (by rfl) ⟨1896180, by rfl⟩ : syracuseStep 5056481 = 3792361) B3792361
theorem B3549167 : Blo 1576486 3549167 := bstep (se 1 (by rfl) ⟨2661875, by rfl⟩ : syracuseStep 3549167 = 5323751) B5323751
theorem B8988731 : Blo 1576486 8988731 := bstep (se 1 (by rfl) ⟨6741548, by rfl⟩ : syracuseStep 8988731 = 13483097) B13483097
theorem B4491359 : Blo 1576486 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B38357171 : Blo 1576486 38357171 := bstep (se 1 (by rfl) ⟨28767878, by rfl⟩ : syracuseStep 38357171 = 57535757) B57535757
theorem B2525435 : Blo 1576486 2525435 := bstep (se 1 (by rfl) ⟨1894076, by rfl⟩ : syracuseStep 2525435 = 3788153) B3788153
theorem B17058703 : Blo 1576486 17058703 := bstep (se 1 (by rfl) ⟨12794027, by rfl⟩ : syracuseStep 17058703 = 25588055) B25588055
theorem B4492361 : Blo 1576486 4492361 := bstep (se 2 (by rfl) ⟨1684635, by rfl⟩ : syracuseStep 4492361 = 3369271) B3369271
theorem B7982225 : Blo 1576486 7982225 := bstep (se 2 (by rfl) ⟨2993334, by rfl⟩ : syracuseStep 7982225 = 5986669) B5986669
theorem B3550571 : Blo 1576486 3550571 := bstep (se 1 (by rfl) ⟨2662928, by rfl⟩ : syracuseStep 3550571 = 5325857) B5325857
theorem B5991803 : Blo 1576486 5991803 := bstep (se 1 (by rfl) ⟨4493852, by rfl⟩ : syracuseStep 5991803 = 8987705) B8987705
theorem B23670161 : Blo 1576486 23670161 := bstep (se 2 (by rfl) ⟨8876310, by rfl⟩ : syracuseStep 23670161 = 17752621) B17752621
theorem B34598339 : Blo 1576486 34598339 := bstep (se 1 (by rfl) ⟨25948754, by rfl⟩ : syracuseStep 34598339 = 51897509) B51897509
theorem B51146275 : Blo 1576486 51146275 := bstep (se 1 (by rfl) ⟨38359706, by rfl⟩ : syracuseStep 51146275 = 76719413) B76719413
theorem B3550841 : Blo 1576486 3550841 := bstep (se 2 (by rfl) ⟨1331565, by rfl⟩ : syracuseStep 3550841 = 2663131) B2663131
theorem B1576607 : Blo 1576486 1576607 := bstep (se 1 (by rfl) ⟨1182455, by rfl⟩ : syracuseStep 1576607 = 2364911) B2364911
theorem B10112809 : Blo 1576486 10112809 := bstep (se 2 (by rfl) ⟨3792303, by rfl⟩ : syracuseStep 10112809 = 7584607) B7584607
theorem B12308287 : Blo 1576486 12308287 := bstep (se 1 (by rfl) ⟨9231215, by rfl⟩ : syracuseStep 12308287 = 18462431) B18462431
theorem B5992319 : Blo 1576486 5992319 := bstep (se 1 (by rfl) ⟨4494239, by rfl⟩ : syracuseStep 5992319 = 8988479) B8988479
theorem B1576871 : Blo 1576486 1576871 := bstep (se 1 (by rfl) ⟨1182653, by rfl⟩ : syracuseStep 1576871 = 2365307) B2365307
theorem B1576895 : Blo 1576486 1576895 := bstep (se 1 (by rfl) ⟨1182671, by rfl⟩ : syracuseStep 1576895 = 2365343) B2365343
theorem B4796399 : Blo 1576486 4796399 := bstep (se 1 (by rfl) ⟨3597299, by rfl⟩ : syracuseStep 4796399 = 7194599) B7194599
theorem B1577051 : Blo 1576486 1577051 := bstep (se 1 (by rfl) ⟨1182788, by rfl⟩ : syracuseStep 1577051 = 2365577) B2365577
theorem B3993695 : Blo 1576486 3993695 := bstep (se 1 (by rfl) ⟨2995271, by rfl⟩ : syracuseStep 3993695 = 5990543) B5990543
theorem B10105019 : Blo 1576486 10105019 := bstep (se 1 (by rfl) ⟨7578764, by rfl⟩ : syracuseStep 10105019 = 15157529) B15157529
theorem B1577151 : Blo 1576486 1577151 := bstep (se 1 (by rfl) ⟨1182863, by rfl⟩ : syracuseStep 1577151 = 2365727) B2365727
theorem B43766203 : Blo 1576486 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B7197119 : Blo 1576486 7197119 := bstep (se 1 (by rfl) ⟨5397839, by rfl⟩ : syracuseStep 7197119 = 10795679) B10795679
theorem B5050831 : Blo 1576486 5050831 := bstep (se 1 (by rfl) ⟨3788123, by rfl⟩ : syracuseStep 5050831 = 7576247) B7576247
theorem B4493819 : Blo 1576486 4493819 := bstep (se 1 (by rfl) ⟨3370364, by rfl⟩ : syracuseStep 4493819 = 6740729) B6740729
theorem B1577519 : Blo 1576486 1577519 := bstep (se 1 (by rfl) ⟨1183139, by rfl⟩ : syracuseStep 1577519 = 2366279) B2366279
theorem B26948213 : Blo 1576486 26948213 := bstep (se 5 (by rfl) ⟨1263197, by rfl⟩ : syracuseStep 26948213 = 2526395) B2526395
theorem B11375237 : Blo 1576486 11375237 := bstep (se 4 (by rfl) ⟨1066428, by rfl⟩ : syracuseStep 11375237 = 2132857) B2132857
theorem B5321753 : Blo 1576486 5321753 := bstep (se 2 (by rfl) ⟨1995657, by rfl⟩ : syracuseStep 5321753 = 3991315) B3991315
theorem B7984169 : Blo 1576486 7984169 := bstep (se 2 (by rfl) ⟨2994063, by rfl⟩ : syracuseStep 7984169 = 5988127) B5988127
theorem B1578095 : Blo 1576486 1578095 := bstep (se 1 (by rfl) ⟨1183571, by rfl⟩ : syracuseStep 1578095 = 2367143) B2367143
theorem B1995931 : Blo 1576486 1995931 := bstep (se 1 (by rfl) ⟨1496948, by rfl⟩ : syracuseStep 1995931 = 2993897) B2993897
theorem B2397367 : Blo 1576486 2397367 := bstep (se 1 (by rfl) ⟨1798025, by rfl⟩ : syracuseStep 2397367 = 3596051) B3596051
theorem B5321915 : Blo 1576486 5321915 := bstep (se 1 (by rfl) ⟨3991436, by rfl⟩ : syracuseStep 5321915 = 7982873) B7982873
theorem B1578175 : Blo 1576486 1578175 := bstep (se 1 (by rfl) ⟨1183631, by rfl⟩ : syracuseStep 1578175 = 2367263) B2367263
theorem B4265195 : Blo 1576486 4265195 := bstep (se 1 (by rfl) ⟨3198896, by rfl⟩ : syracuseStep 4265195 = 6397793) B6397793
theorem B8090887 : Blo 1576486 8090887 := bstep (se 1 (by rfl) ⟨6068165, by rfl⟩ : syracuseStep 8090887 = 12136331) B12136331
theorem B2364839 : Blo 1576486 2364839 := bstep (se 1 (by rfl) ⟨1773629, by rfl⟩ : syracuseStep 2364839 = 3547259) B3547259
theorem B1578463 : Blo 1576486 1578463 := bstep (se 1 (by rfl) ⟨1183847, by rfl⟩ : syracuseStep 1578463 = 2367695) B2367695
theorem B4265455 : Blo 1576486 4265455 := bstep (se 1 (by rfl) ⟨3199091, by rfl⟩ : syracuseStep 4265455 = 6398183) B6398183
theorem B2365019 : Blo 1576486 2365019 := bstep (se 1 (by rfl) ⟨1773764, by rfl⟩ : syracuseStep 2365019 = 3547529) B3547529
theorem B1180899013 : Blo 1576486 1180899013 := bstep (se 4 (by rfl) ⟨110709282, by rfl⟩ : syracuseStep 1180899013 = 221418565) B221418565
theorem B15152993 : Blo 1576486 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B17061779 : Blo 1576486 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B13482035 : Blo 1576486 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B7985465 : Blo 1576486 7985465 := bstep (se 2 (by rfl) ⟨2994549, by rfl⟩ : syracuseStep 7985465 = 5989099) B5989099
theorem B2365775 : Blo 1576486 2365775 := bstep (se 1 (by rfl) ⟨1774331, by rfl⟩ : syracuseStep 2365775 = 3548663) B3548663
theorem B2365799 : Blo 1576486 2365799 := bstep (se 1 (by rfl) ⟨1774349, by rfl⟩ : syracuseStep 2365799 = 3548699) B3548699
theorem B2365865 : Blo 1576486 2365865 := bstep (se 2 (by rfl) ⟨887199, by rfl⟩ : syracuseStep 2365865 = 1774399) B1774399
theorem B5396993 : Blo 1576486 5396993 := bstep (se 2 (by rfl) ⟨2023872, by rfl⟩ : syracuseStep 5396993 = 4047745) B4047745
theorem B9599609 : Blo 1576486 9599609 := bstep (se 2 (by rfl) ⟨3599853, by rfl⟩ : syracuseStep 9599609 = 7199707) B7199707
theorem B2366249 : Blo 1576486 2366249 := bstep (se 2 (by rfl) ⟨887343, by rfl⟩ : syracuseStep 2366249 = 1774687) B1774687
theorem B8985563 : Blo 1576486 8985563 := bstep (se 1 (by rfl) ⟨6739172, by rfl⟩ : syracuseStep 8985563 = 13478345) B13478345
theorem B2366459 : Blo 1576486 2366459 := bstep (se 1 (by rfl) ⟨1774844, by rfl⟩ : syracuseStep 2366459 = 3549689) B3549689
theorem B2366495 : Blo 1576486 2366495 := bstep (se 1 (by rfl) ⟨1774871, by rfl⟩ : syracuseStep 2366495 = 3549743) B3549743
theorem B2366519 : Blo 1576486 2366519 := bstep (se 1 (by rfl) ⟨1774889, by rfl⟩ : syracuseStep 2366519 = 3549779) B3549779
theorem B2366639 : Blo 1576486 2366639 := bstep (se 1 (by rfl) ⟨1774979, by rfl⟩ : syracuseStep 2366639 = 3549959) B3549959
theorem B81960115 : Blo 1576486 81960115 := bstep (se 1 (by rfl) ⟨61470086, by rfl⟩ : syracuseStep 81960115 = 122940173) B122940173
theorem B5987627 : Blo 1576486 5987627 := bstep (se 1 (by rfl) ⟨4490720, by rfl⟩ : syracuseStep 5987627 = 8981441) B8981441
theorem B2366783 : Blo 1576486 2366783 := bstep (se 1 (by rfl) ⟨1775087, by rfl⟩ : syracuseStep 2366783 = 3550175) B3550175
theorem B5684651 : Blo 1576486 5684651 := bstep (se 1 (by rfl) ⟨4263488, by rfl⟩ : syracuseStep 5684651 = 8526977) B8526977
theorem B2366927 : Blo 1576486 2366927 := bstep (se 1 (by rfl) ⟨1775195, by rfl⟩ : syracuseStep 2366927 = 3550391) B3550391
theorem B5324399 : Blo 1576486 5324399 := bstep (se 1 (by rfl) ⟨3993299, by rfl⟩ : syracuseStep 5324399 = 7986599) B7986599
theorem B5054123 : Blo 1576486 5054123 := bstep (se 1 (by rfl) ⟨3790592, by rfl⟩ : syracuseStep 5054123 = 7581185) B7581185
theorem B6741737 : Blo 1576486 6741737 := bstep (se 2 (by rfl) ⟨2528151, by rfl⟩ : syracuseStep 6741737 = 5056303) B5056303
theorem B2367311 : Blo 1576486 2367311 := bstep (se 1 (by rfl) ⟨1775483, by rfl⟩ : syracuseStep 2367311 = 3550967) B3550967
theorem B2367359 : Blo 1576486 2367359 := bstep (se 1 (by rfl) ⟨1775519, by rfl⟩ : syracuseStep 2367359 = 3551039) B3551039
theorem B2367431 : Blo 1576486 2367431 := bstep (se 1 (by rfl) ⟨1775573, by rfl⟩ : syracuseStep 2367431 = 3551147) B3551147
theorem B8880097 : Blo 1576486 8880097 := bstep (se 2 (by rfl) ⟨3330036, by rfl⟩ : syracuseStep 8880097 = 6660073) B6660073
theorem B2662375 : Blo 1576486 2662375 := bstep (se 1 (by rfl) ⟨1996781, by rfl⟩ : syracuseStep 2662375 = 3993563) B3993563
theorem B221544467 : Blo 1576486 221544467 := bstep (se 1 (by rfl) ⟨166158350, by rfl⟩ : syracuseStep 221544467 = 332316701) B332316701
theorem B2662463 : Blo 1576486 2662463 := bstep (se 1 (by rfl) ⟨1996847, by rfl⟩ : syracuseStep 2662463 = 3993695) B3993695
theorem B17965475 : Blo 1576486 17965475 := bstep (se 1 (by rfl) ⟨13474106, by rfl⟩ : syracuseStep 17965475 = 26948213) B26948213
theorem B6734441 : Blo 1576486 6734441 := bstep (se 2 (by rfl) ⟨2525415, by rfl⟩ : syracuseStep 6734441 = 5050831) B5050831
theorem B3547835 : Blo 1576486 3547835 := bstep (se 1 (by rfl) ⟨2660876, by rfl⟩ : syracuseStep 3547835 = 5321753) B5321753
theorem B3547943 : Blo 1576486 3547943 := bstep (se 1 (by rfl) ⟨2660957, by rfl⟩ : syracuseStep 3547943 = 5321915) B5321915
theorem B10101995 : Blo 1576486 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B8988023 : Blo 1576486 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B3196489 : Blo 1576486 3196489 := bstep (se 2 (by rfl) ⟨1198683, by rfl⟩ : syracuseStep 3196489 = 2397367) B2397367
theorem B3597995 : Blo 1576486 3597995 := bstep (se 1 (by rfl) ⟨2698496, by rfl⟩ : syracuseStep 3597995 = 5396993) B5396993
theorem B6399739 : Blo 1576486 6399739 := bstep (se 1 (by rfl) ⟨4799804, by rfl⟩ : syracuseStep 6399739 = 9599609) B9599609
theorem B13477661 : Blo 1576486 13477661 := bstep (se 3 (by rfl) ⟨2527061, by rfl⟩ : syracuseStep 13477661 = 5054123) B5054123
theorem B5990375 : Blo 1576486 5990375 := bstep (se 1 (by rfl) ⟨4492781, by rfl⟩ : syracuseStep 5990375 = 8985563) B8985563
theorem B5687273 : Blo 1576486 5687273 := bstep (se 2 (by rfl) ⟨2132727, by rfl⟩ : syracuseStep 5687273 = 4265455) B4265455
theorem B3991751 : Blo 1576486 3991751 := bstep (se 1 (by rfl) ⟨2993813, by rfl⟩ : syracuseStep 3991751 = 5987627) B5987627
theorem B15780107 : Blo 1576486 15780107 := bstep (se 1 (by rfl) ⟨11835080, by rfl⟩ : syracuseStep 15780107 = 23670161) B23670161
theorem B3549599 : Blo 1576486 3549599 := bstep (se 1 (by rfl) ⟨2662199, by rfl⟩ : syracuseStep 3549599 = 5324399) B5324399
theorem B16411049 : Blo 1576486 16411049 := bstep (se 2 (by rfl) ⟨6154143, by rfl⟩ : syracuseStep 16411049 = 12308287) B12308287
theorem B11840129 : Blo 1576486 11840129 := bstep (se 2 (by rfl) ⟨4440048, by rfl⟩ : syracuseStep 11840129 = 8880097) B8880097
theorem B3549833 : Blo 1576486 3549833 := bstep (se 2 (by rfl) ⟨1331187, by rfl⟩ : syracuseStep 3549833 = 2662375) B2662375
theorem B3197599 : Blo 1576486 3197599 := bstep (se 1 (by rfl) ⟨2398199, by rfl⟩ : syracuseStep 3197599 = 4796399) B4796399
theorem B28781315 : Blo 1576486 28781315 := bstep (se 1 (by rfl) ⟨21585986, by rfl⟩ : syracuseStep 28781315 = 43171973) B43171973
theorem B6736679 : Blo 1576486 6736679 := bstep (se 1 (by rfl) ⟨5052509, by rfl⟩ : syracuseStep 6736679 = 10105019) B10105019
theorem B3369775 : Blo 1576486 3369775 := bstep (se 1 (by rfl) ⟨2527331, by rfl⟩ : syracuseStep 3369775 = 5054663) B5054663
theorem B58354937 : Blo 1576486 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B11373853 : Blo 1576486 11373853 := bstep (se 3 (by rfl) ⟨2132597, by rfl⟩ : syracuseStep 11373853 = 4265195) B4265195
theorem B2993449 : Blo 1576486 2993449 := bstep (se 2 (by rfl) ⟨1122543, by rfl⟩ : syracuseStep 2993449 = 2245087) B2245087
theorem B1576559 : Blo 1576486 1576559 := bstep (se 1 (by rfl) ⟨1182419, by rfl⟩ : syracuseStep 1576559 = 2364839) B2364839
theorem B3370663 : Blo 1576486 3370663 := bstep (se 1 (by rfl) ⟨2527997, by rfl⟩ : syracuseStep 3370663 = 5055995) B5055995
theorem B1576679 : Blo 1576486 1576679 := bstep (se 1 (by rfl) ⟨1182509, by rfl⟩ : syracuseStep 1576679 = 2365019) B2365019
theorem B10104659 : Blo 1576486 10104659 := bstep (se 1 (by rfl) ⟨7578494, by rfl⟩ : syracuseStep 10104659 = 15156989) B15156989
theorem B22744937 : Blo 1576486 22744937 := bstep (se 2 (by rfl) ⟨8529351, by rfl⟩ : syracuseStep 22744937 = 17058703) B17058703
theorem B11374519 : Blo 1576486 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B3370987 : Blo 1576486 3370987 := bstep (se 1 (by rfl) ⟨2528240, by rfl⟩ : syracuseStep 3370987 = 5056481) B5056481
theorem B5992487 : Blo 1576486 5992487 := bstep (se 1 (by rfl) ⟨4494365, by rfl⟩ : syracuseStep 5992487 = 8988731) B8988731
theorem B2994239 : Blo 1576486 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B25571447 : Blo 1576486 25571447 := bstep (se 1 (by rfl) ⟨19178585, by rfl⟩ : syracuseStep 25571447 = 38357171) B38357171
theorem B2994337 : Blo 1576486 2994337 := bstep (se 2 (by rfl) ⟨1122876, by rfl⟩ : syracuseStep 2994337 = 2245753) B2245753
theorem B1683623 : Blo 1576486 1683623 := bstep (se 1 (by rfl) ⟨1262717, by rfl⟩ : syracuseStep 1683623 = 2525435) B2525435
theorem B1577183 : Blo 1576486 1577183 := bstep (se 1 (by rfl) ⟨1182887, by rfl⟩ : syracuseStep 1577183 = 2365775) B2365775
theorem B1577199 : Blo 1576486 1577199 := bstep (se 1 (by rfl) ⟨1182899, by rfl⟩ : syracuseStep 1577199 = 2365799) B2365799
theorem B1577243 : Blo 1576486 1577243 := bstep (se 1 (by rfl) ⟨1182932, by rfl⟩ : syracuseStep 1577243 = 2365865) B2365865
theorem B1577499 : Blo 1576486 1577499 := bstep (se 1 (by rfl) ⟨1183124, by rfl⟩ : syracuseStep 1577499 = 2366249) B2366249
theorem B1577639 : Blo 1576486 1577639 := bstep (se 1 (by rfl) ⟨1183229, by rfl⟩ : syracuseStep 1577639 = 2366459) B2366459
theorem B1577663 : Blo 1576486 1577663 := bstep (se 1 (by rfl) ⟨1183247, by rfl⟩ : syracuseStep 1577663 = 2366495) B2366495
theorem B1577679 : Blo 1576486 1577679 := bstep (se 1 (by rfl) ⟨1183259, by rfl⟩ : syracuseStep 1577679 = 2366519) B2366519
theorem B68195033 : Blo 1576486 68195033 := bstep (se 2 (by rfl) ⟨25573137, by rfl⟩ : syracuseStep 68195033 = 51146275) B51146275
theorem B2994907 : Blo 1576486 2994907 := bstep (se 1 (by rfl) ⟨2246180, by rfl⟩ : syracuseStep 2994907 = 4492361) B4492361
theorem B73872121 : Blo 1576486 73872121 := bstep (se 2 (by rfl) ⟨27702045, by rfl⟩ : syracuseStep 73872121 = 55404091) B55404091
theorem B5321483 : Blo 1576486 5321483 := bstep (se 1 (by rfl) ⟨3991112, by rfl⟩ : syracuseStep 5321483 = 7982225) B7982225
theorem B1577759 : Blo 1576486 1577759 := bstep (se 1 (by rfl) ⟨1183319, by rfl⟩ : syracuseStep 1577759 = 2366639) B2366639
theorem B1577855 : Blo 1576486 1577855 := bstep (se 1 (by rfl) ⟨1183391, by rfl⟩ : syracuseStep 1577855 = 2366783) B2366783
theorem B3994535 : Blo 1576486 3994535 := bstep (se 1 (by rfl) ⟨2995901, by rfl⟩ : syracuseStep 3994535 = 5991803) B5991803
theorem B1574532017 : Blo 1576486 1574532017 := bstep (se 2 (by rfl) ⟨590449506, by rfl⟩ : syracuseStep 1574532017 = 1180899013) B1180899013
theorem B3789767 : Blo 1576486 3789767 := bstep (se 1 (by rfl) ⟨2842325, by rfl⟩ : syracuseStep 3789767 = 5684651) B5684651
theorem B23065559 : Blo 1576486 23065559 := bstep (se 1 (by rfl) ⟨17299169, by rfl⟩ : syracuseStep 23065559 = 34598339) B34598339
theorem B1577951 : Blo 1576486 1577951 := bstep (se 1 (by rfl) ⟨1183463, by rfl⟩ : syracuseStep 1577951 = 2366927) B2366927
theorem B4494491 : Blo 1576486 4494491 := bstep (se 1 (by rfl) ⟨3370868, by rfl⟩ : syracuseStep 4494491 = 6741737) B6741737
theorem B1578207 : Blo 1576486 1578207 := bstep (se 1 (by rfl) ⟨1183655, by rfl⟩ : syracuseStep 1578207 = 2367311) B2367311
theorem B3994879 : Blo 1576486 3994879 := bstep (se 1 (by rfl) ⟨2996159, by rfl⟩ : syracuseStep 3994879 = 5992319) B5992319
theorem B1578239 : Blo 1576486 1578239 := bstep (se 1 (by rfl) ⟨1183679, by rfl⟩ : syracuseStep 1578239 = 2367359) B2367359
theorem B1578287 : Blo 1576486 1578287 := bstep (se 1 (by rfl) ⟨1183715, by rfl⟩ : syracuseStep 1578287 = 2367431) B2367431
theorem B1578447 : Blo 1576486 1578447 := bstep (se 1 (by rfl) ⟨1183835, by rfl⟩ : syracuseStep 1578447 = 2367671) B2367671
theorem B2364959 : Blo 1576486 2364959 := bstep (se 1 (by rfl) ⟨1773719, by rfl⟩ : syracuseStep 2364959 = 3547439) B3547439
theorem B17962559 : Blo 1576486 17962559 := bstep (se 1 (by rfl) ⟨13471919, by rfl⟩ : syracuseStep 17962559 = 26943839) B26943839
theorem B8525375 : Blo 1576486 8525375 := bstep (se 1 (by rfl) ⟨6394031, by rfl⟩ : syracuseStep 8525375 = 12788063) B12788063
theorem B4798079 : Blo 1576486 4798079 := bstep (se 1 (by rfl) ⟨3598559, by rfl⟩ : syracuseStep 4798079 = 7197119) B7197119
theorem B2995879 : Blo 1576486 2995879 := bstep (se 1 (by rfl) ⟨2246909, by rfl⟩ : syracuseStep 2995879 = 4493819) B4493819
theorem B7583491 : Blo 1576486 7583491 := bstep (se 1 (by rfl) ⟨5687618, by rfl⟩ : syracuseStep 7583491 = 11375237) B11375237
theorem B5322779 : Blo 1576486 5322779 := bstep (se 1 (by rfl) ⟨3992084, by rfl⟩ : syracuseStep 5322779 = 7984169) B7984169
theorem B2365511 : Blo 1576486 2365511 := bstep (se 1 (by rfl) ⟨1774133, by rfl⟩ : syracuseStep 2365511 = 3548267) B3548267
theorem B26286383 : Blo 1576486 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B2366111 : Blo 1576486 2366111 := bstep (se 1 (by rfl) ⟨1774583, by rfl⟩ : syracuseStep 2366111 = 3549167) B3549167
theorem B2661241 : Blo 1576486 2661241 := bstep (se 2 (by rfl) ⟨997965, by rfl⟩ : syracuseStep 2661241 = 1995931) B1995931
theorem B5323643 : Blo 1576486 5323643 := bstep (se 1 (by rfl) ⟨3992732, by rfl⟩ : syracuseStep 5323643 = 7985465) B7985465
theorem B109280153 : Blo 1576486 109280153 := bstep (se 2 (by rfl) ⟨40980057, by rfl⟩ : syracuseStep 109280153 = 81960115) B81960115
theorem B10787849 : Blo 1576486 10787849 := bstep (se 2 (by rfl) ⟨4045443, by rfl⟩ : syracuseStep 10787849 = 8090887) B8090887
theorem B2367047 : Blo 1576486 2367047 := bstep (se 1 (by rfl) ⟨1775285, by rfl⟩ : syracuseStep 2367047 = 3550571) B3550571
theorem B13483745 : Blo 1576486 13483745 := bstep (se 2 (by rfl) ⟨5056404, by rfl⟩ : syracuseStep 13483745 = 10112809) B10112809
theorem B2367227 : Blo 1576486 2367227 := bstep (se 1 (by rfl) ⟨1775420, by rfl⟩ : syracuseStep 2367227 = 3550841) B3550841
theorem B17047631 : Blo 1576486 17047631 := bstep (se 1 (by rfl) ⟨12785723, by rfl⟩ : syracuseStep 17047631 = 25571447) B25571447
theorem B11976983 : Blo 1576486 11976983 := bstep (se 1 (by rfl) ⟨8982737, by rfl⟩ : syracuseStep 11976983 = 17965475) B17965475
theorem B4489627 : Blo 1576486 4489627 := bstep (se 1 (by rfl) ⟨3367220, by rfl⟩ : syracuseStep 4489627 = 6734441) B6734441
theorem B4489661 : Blo 1576486 4489661 := bstep (se 3 (by rfl) ⟨841811, by rfl⟩ : syracuseStep 4489661 = 1683623) B1683623
theorem B3547655 : Blo 1576486 3547655 := bstep (se 1 (by rfl) ⟨2660741, by rfl⟩ : syracuseStep 3547655 = 5321483) B5321483
theorem B2663023 : Blo 1576486 2663023 := bstep (se 1 (by rfl) ⟨1997267, by rfl⟩ : syracuseStep 2663023 = 3994535) B3994535
theorem B15377039 : Blo 1576486 15377039 := bstep (se 1 (by rfl) ⟨11532779, by rfl⟩ : syracuseStep 15377039 = 23065559) B23065559
theorem B6734663 : Blo 1576486 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B3548321 : Blo 1576486 3548321 := bstep (se 2 (by rfl) ⟨1330620, by rfl⟩ : syracuseStep 3548321 = 2661241) B2661241
theorem B3548519 : Blo 1576486 3548519 := bstep (se 1 (by rfl) ⟨2661389, by rfl⟩ : syracuseStep 3548519 = 5322779) B5322779
theorem B17524255 : Blo 1576486 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B5326505 : Blo 1576486 5326505 := bstep (se 2 (by rfl) ⟨1997439, by rfl⟩ : syracuseStep 5326505 = 3994879) B3994879
theorem B15165137 : Blo 1576486 15165137 := bstep (se 2 (by rfl) ⟨5686926, by rfl⟩ : syracuseStep 15165137 = 11373853) B11373853
theorem B3991265 : Blo 1576486 3991265 := bstep (se 2 (by rfl) ⟨1496724, by rfl⟩ : syracuseStep 3991265 = 2993449) B2993449
theorem B19187543 : Blo 1576486 19187543 := bstep (se 1 (by rfl) ⟨14390657, by rfl⟩ : syracuseStep 19187543 = 28781315) B28781315
theorem B4491119 : Blo 1576486 4491119 := bstep (se 1 (by rfl) ⟨3368339, by rfl⟩ : syracuseStep 4491119 = 6736679) B6736679
theorem B3549095 : Blo 1576486 3549095 := bstep (se 1 (by rfl) ⟨2661821, by rfl⟩ : syracuseStep 3549095 = 5323643) B5323643
theorem B72853435 : Blo 1576486 72853435 := bstep (se 1 (by rfl) ⟨54640076, by rfl⟩ : syracuseStep 72853435 = 109280153) B109280153
theorem B4261985 : Blo 1576486 4261985 := bstep (se 2 (by rfl) ⟨1598244, by rfl⟩ : syracuseStep 4261985 = 3196489) B3196489
theorem B10111321 : Blo 1576486 10111321 := bstep (se 2 (by rfl) ⟨3791745, by rfl⟩ : syracuseStep 10111321 = 7583491) B7583491
theorem B8989163 : Blo 1576486 8989163 := bstep (se 1 (by rfl) ⟨6741872, by rfl⟩ : syracuseStep 8989163 = 13483745) B13483745
theorem B6736439 : Blo 1576486 6736439 := bstep (se 1 (by rfl) ⟨5052329, by rfl⟩ : syracuseStep 6736439 = 10104659) B10104659
theorem B15166025 : Blo 1576486 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B15166061 : Blo 1576486 15166061 := bstep (se 3 (by rfl) ⟨2843636, by rfl⟩ : syracuseStep 15166061 = 5687273) B5687273
theorem B147696311 : Blo 1576486 147696311 := bstep (se 1 (by rfl) ⟨110772233, by rfl⟩ : syracuseStep 147696311 = 221544467) B221544467
theorem B3992449 : Blo 1576486 3992449 := bstep (se 2 (by rfl) ⟨1497168, by rfl⟩ : syracuseStep 3992449 = 2994337) B2994337
theorem B5992015 : Blo 1576486 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B3993209 : Blo 1576486 3993209 := bstep (se 2 (by rfl) ⟨1497453, by rfl⟩ : syracuseStep 3993209 = 2994907) B2994907
theorem B98496161 : Blo 1576486 98496161 := bstep (se 2 (by rfl) ⟨36936060, by rfl⟩ : syracuseStep 98496161 = 73872121) B73872121
theorem B1576639 : Blo 1576486 1576639 := bstep (se 1 (by rfl) ⟨1182479, by rfl⟩ : syracuseStep 1576639 = 2364959) B2364959
theorem B4493033 : Blo 1576486 4493033 := bstep (se 2 (by rfl) ⟨1684887, by rfl⟩ : syracuseStep 4493033 = 3369775) B3369775
theorem B3198719 : Blo 1576486 3198719 := bstep (se 1 (by rfl) ⟨2399039, by rfl⟩ : syracuseStep 3198719 = 4798079) B4798079
theorem B34131941 : Blo 1576486 34131941 := bstep (se 4 (by rfl) ⟨3199869, by rfl⟩ : syracuseStep 34131941 = 6399739) B6399739
theorem B3993583 : Blo 1576486 3993583 := bstep (se 1 (by rfl) ⟨2995187, by rfl⟩ : syracuseStep 3993583 = 5990375) B5990375
theorem B1577007 : Blo 1576486 1577007 := bstep (se 1 (by rfl) ⟨1182755, by rfl⟩ : syracuseStep 1577007 = 2365511) B2365511
theorem B10940699 : Blo 1576486 10940699 := bstep (se 1 (by rfl) ⟨8205524, by rfl⟩ : syracuseStep 10940699 = 16411049) B16411049
theorem B1577407 : Blo 1576486 1577407 := bstep (se 1 (by rfl) ⟨1183055, by rfl⟩ : syracuseStep 1577407 = 2366111) B2366111
theorem B3994505 : Blo 1576486 3994505 := bstep (se 2 (by rfl) ⟨1497939, by rfl⟩ : syracuseStep 3994505 = 2995879) B2995879
theorem B4494217 : Blo 1576486 4494217 := bstep (se 2 (by rfl) ⟨1685331, by rfl⟩ : syracuseStep 4494217 = 3370663) B3370663
theorem B1578031 : Blo 1576486 1578031 := bstep (se 1 (by rfl) ⟨1183523, by rfl⟩ : syracuseStep 1578031 = 2367047) B2367047
theorem B1578151 : Blo 1576486 1578151 := bstep (se 1 (by rfl) ⟨1183613, by rfl⟩ : syracuseStep 1578151 = 2367227) B2367227
theorem B10106045 : Blo 1576486 10106045 := bstep (se 3 (by rfl) ⟨1894883, by rfl⟩ : syracuseStep 10106045 = 3789767) B3789767
theorem B17978597 : Blo 1576486 17978597 := bstep (se 4 (by rfl) ⟨1685493, by rfl⟩ : syracuseStep 17978597 = 3370987) B3370987
theorem B3994991 : Blo 1576486 3994991 := bstep (se 1 (by rfl) ⟨2996243, by rfl⟩ : syracuseStep 3994991 = 5992487) B5992487
theorem B1996159 : Blo 1576486 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B1774975 : Blo 1576486 1774975 := bstep (se 1 (by rfl) ⟨1331231, by rfl⟩ : syracuseStep 1774975 = 2662463) B2662463
theorem B2365223 : Blo 1576486 2365223 := bstep (se 1 (by rfl) ⟨1773917, by rfl⟩ : syracuseStep 2365223 = 3547835) B3547835
theorem B45463355 : Blo 1576486 45463355 := bstep (se 1 (by rfl) ⟨34097516, by rfl⟩ : syracuseStep 45463355 = 68195033) B68195033
theorem B2365295 : Blo 1576486 2365295 := bstep (se 1 (by rfl) ⟨1773971, by rfl⟩ : syracuseStep 2365295 = 3547943) B3547943
theorem B1049688011 : Blo 1576486 1049688011 := bstep (se 1 (by rfl) ⟨787266008, by rfl⟩ : syracuseStep 1049688011 = 1574532017) B1574532017
theorem B42080285 : Blo 1576486 42080285 := bstep (se 3 (by rfl) ⟨7890053, by rfl⟩ : syracuseStep 42080285 = 15780107) B15780107
theorem B2996327 : Blo 1576486 2996327 := bstep (se 1 (by rfl) ⟨2247245, by rfl⟩ : syracuseStep 2996327 = 4494491) B4494491
theorem B17053861 : Blo 1576486 17053861 := bstep (se 4 (by rfl) ⟨1598799, by rfl⟩ : syracuseStep 17053861 = 3197599) B3197599
theorem B11975039 : Blo 1576486 11975039 := bstep (se 1 (by rfl) ⟨8981279, by rfl⟩ : syracuseStep 11975039 = 17962559) B17962559
theorem B5683583 : Blo 1576486 5683583 := bstep (se 1 (by rfl) ⟨4262687, by rfl⟩ : syracuseStep 5683583 = 8525375) B8525375
theorem B2398663 : Blo 1576486 2398663 := bstep (se 1 (by rfl) ⟨1798997, by rfl⟩ : syracuseStep 2398663 = 3597995) B3597995
theorem B8985107 : Blo 1576486 8985107 := bstep (se 1 (by rfl) ⟨6738830, by rfl⟩ : syracuseStep 8985107 = 13477661) B13477661
theorem B126294709 : Blo 1576486 126294709 := bstep (se 5 (by rfl) ⟨5920064, by rfl⟩ : syracuseStep 126294709 = 11840129) B11840129
theorem B2661167 : Blo 1576486 2661167 := bstep (se 1 (by rfl) ⟨1995875, by rfl⟩ : syracuseStep 2661167 = 3991751) B3991751
theorem B2366399 : Blo 1576486 2366399 := bstep (se 1 (by rfl) ⟨1774799, by rfl⟩ : syracuseStep 2366399 = 3549599) B3549599
theorem B2366555 : Blo 1576486 2366555 := bstep (se 1 (by rfl) ⟨1774916, by rfl⟩ : syracuseStep 2366555 = 3549833) B3549833
theorem B7191899 : Blo 1576486 7191899 := bstep (se 1 (by rfl) ⟨5393924, by rfl⟩ : syracuseStep 7191899 = 10787849) B10787849
theorem B38903291 : Blo 1576486 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B15163291 : Blo 1576486 15163291 := bstep (se 1 (by rfl) ⟨11372468, by rfl⟩ : syracuseStep 15163291 = 22744937) B22744937
theorem B4489775 : Blo 1576486 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B2663003 : Blo 1576486 2663003 := bstep (se 1 (by rfl) ⟨1997252, by rfl⟩ : syracuseStep 2663003 = 3994505) B3994505
theorem B11985731 : Blo 1576486 11985731 := bstep (se 1 (by rfl) ⟨8989298, by rfl⟩ : syracuseStep 11985731 = 17978597) B17978597
theorem B2663327 : Blo 1576486 2663327 := bstep (se 1 (by rfl) ⟨1997495, by rfl⟩ : syracuseStep 2663327 = 3994991) B3994991
theorem B10110091 : Blo 1576486 10110091 := bstep (se 1 (by rfl) ⟨7582568, by rfl⟩ : syracuseStep 10110091 = 15165137) B15165137
theorem B5990071 : Blo 1576486 5990071 := bstep (se 1 (by rfl) ⟨4492553, by rfl⟩ : syracuseStep 5990071 = 8985107) B8985107
theorem B4490959 : Blo 1576486 4490959 := bstep (se 1 (by rfl) ⟨3368219, by rfl⟩ : syracuseStep 4490959 = 6736439) B6736439
theorem B10110683 : Blo 1576486 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B10110707 : Blo 1576486 10110707 := bstep (se 1 (by rfl) ⟨7583030, by rfl⟩ : syracuseStep 10110707 = 15166061) B15166061
theorem B23365673 : Blo 1576486 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B7989353 : Blo 1576486 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B4794599 : Blo 1576486 4794599 := bstep (se 1 (by rfl) ⟨3595949, by rfl⟩ : syracuseStep 4794599 = 7191899) B7191899
theorem B2132479 : Blo 1576486 2132479 := bstep (se 1 (by rfl) ⟨1599359, by rfl⟩ : syracuseStep 2132479 = 3198719) B3198719
theorem B7293799 : Blo 1576486 7293799 := bstep (se 1 (by rfl) ⟨5470349, by rfl⟩ : syracuseStep 7293799 = 10940699) B10940699
theorem B45460349 : Blo 1576486 45460349 := bstep (se 3 (by rfl) ⟨8523815, by rfl⟩ : syracuseStep 45460349 = 17047631) B17047631
theorem B2993107 : Blo 1576486 2993107 := bstep (se 1 (by rfl) ⟨2244830, by rfl⟩ : syracuseStep 2993107 = 4489661) B4489661
theorem B10251359 : Blo 1576486 10251359 := bstep (se 1 (by rfl) ⟨7688519, by rfl⟩ : syracuseStep 10251359 = 15377039) B15377039
theorem B3198217 : Blo 1576486 3198217 := bstep (se 2 (by rfl) ⟨1199331, by rfl⟩ : syracuseStep 3198217 = 2398663) B2398663
theorem B6737363 : Blo 1576486 6737363 := bstep (se 1 (by rfl) ⟨5053022, by rfl⟩ : syracuseStep 6737363 = 10106045) B10106045
theorem B3550697 : Blo 1576486 3550697 := bstep (se 2 (by rfl) ⟨1331511, by rfl⟩ : syracuseStep 3550697 = 2663023) B2663023
theorem B3551003 : Blo 1576486 3551003 := bstep (se 1 (by rfl) ⟨2663252, by rfl⟩ : syracuseStep 3551003 = 5326505) B5326505
theorem B5992289 : Blo 1576486 5992289 := bstep (se 2 (by rfl) ⟨2247108, by rfl⟩ : syracuseStep 5992289 = 4494217) B4494217
theorem B1576815 : Blo 1576486 1576815 := bstep (se 1 (by rfl) ⟨1182611, by rfl⟩ : syracuseStep 1576815 = 2365223) B2365223
theorem B12791695 : Blo 1576486 12791695 := bstep (se 1 (by rfl) ⟨9593771, by rfl⟩ : syracuseStep 12791695 = 19187543) B19187543
theorem B1576863 : Blo 1576486 1576863 := bstep (se 1 (by rfl) ⟨1182647, by rfl⟩ : syracuseStep 1576863 = 2365295) B2365295
theorem B2994079 : Blo 1576486 2994079 := bstep (se 1 (by rfl) ⟨2245559, by rfl⟩ : syracuseStep 2994079 = 4491119) B4491119
theorem B28053523 : Blo 1576486 28053523 := bstep (se 1 (by rfl) ⟨21040142, by rfl⟩ : syracuseStep 28053523 = 42080285) B42080285
theorem B7983359 : Blo 1576486 7983359 := bstep (se 1 (by rfl) ⟨5987519, by rfl⟩ : syracuseStep 7983359 = 11975039) B11975039
theorem B3789055 : Blo 1576486 3789055 := bstep (se 1 (by rfl) ⟨2841791, by rfl⟩ : syracuseStep 3789055 = 5683583) B5683583
theorem B5992775 : Blo 1576486 5992775 := bstep (se 1 (by rfl) ⟨4494581, by rfl⟩ : syracuseStep 5992775 = 8989163) B8989163
theorem B98464207 : Blo 1576486 98464207 := bstep (se 1 (by rfl) ⟨73848155, by rfl⟩ : syracuseStep 98464207 = 147696311) B147696311
theorem B1774111 : Blo 1576486 1774111 := bstep (se 1 (by rfl) ⟨1330583, by rfl⟩ : syracuseStep 1774111 = 2661167) B2661167
theorem B1577599 : Blo 1576486 1577599 := bstep (se 1 (by rfl) ⟨1183199, by rfl⟩ : syracuseStep 1577599 = 2366399) B2366399
theorem B1577703 : Blo 1576486 1577703 := bstep (se 1 (by rfl) ⟨1183277, by rfl⟩ : syracuseStep 1577703 = 2366555) B2366555
theorem B65664107 : Blo 1576486 65664107 := bstep (se 1 (by rfl) ⟨49248080, by rfl⟩ : syracuseStep 65664107 = 98496161) B98496161
theorem B2995355 : Blo 1576486 2995355 := bstep (se 1 (by rfl) ⟨2246516, by rfl⟩ : syracuseStep 2995355 = 4493033) B4493033
theorem B97137913 : Blo 1576486 97137913 := bstep (se 2 (by rfl) ⟨36426717, by rfl⟩ : syracuseStep 97137913 = 72853435) B72853435
theorem B22754627 : Blo 1576486 22754627 := bstep (se 1 (by rfl) ⟨17065970, by rfl⟩ : syracuseStep 22754627 = 34131941) B34131941
theorem B7984655 : Blo 1576486 7984655 := bstep (se 1 (by rfl) ⟨5988491, by rfl⟩ : syracuseStep 7984655 = 11976983) B11976983
theorem B22738481 : Blo 1576486 22738481 := bstep (se 2 (by rfl) ⟨8526930, by rfl⟩ : syracuseStep 22738481 = 17053861) B17053861
theorem B2365103 : Blo 1576486 2365103 := bstep (se 1 (by rfl) ⟨1773827, by rfl⟩ : syracuseStep 2365103 = 3547655) B3547655
theorem B13481761 : Blo 1576486 13481761 := bstep (se 2 (by rfl) ⟨5055660, by rfl⟩ : syracuseStep 13481761 = 10111321) B10111321
theorem B5986169 : Blo 1576486 5986169 := bstep (se 2 (by rfl) ⟨2244813, by rfl⟩ : syracuseStep 5986169 = 4489627) B4489627
theorem B2365547 : Blo 1576486 2365547 := bstep (se 1 (by rfl) ⟨1774160, by rfl⟩ : syracuseStep 2365547 = 3548321) B3548321
theorem B2365679 : Blo 1576486 2365679 := bstep (se 1 (by rfl) ⟨1774259, by rfl⟩ : syracuseStep 2365679 = 3548519) B3548519
theorem B168392945 : Blo 1576486 168392945 := bstep (se 2 (by rfl) ⟨63147354, by rfl⟩ : syracuseStep 168392945 = 126294709) B126294709
theorem B2660843 : Blo 1576486 2660843 := bstep (se 1 (by rfl) ⟨1995632, by rfl⟩ : syracuseStep 2660843 = 3991265) B3991265
theorem B5323265 : Blo 1576486 5323265 := bstep (se 2 (by rfl) ⟨1996224, by rfl⟩ : syracuseStep 5323265 = 3992449) B3992449
theorem B30308903 : Blo 1576486 30308903 := bstep (se 1 (by rfl) ⟨22731677, by rfl⟩ : syracuseStep 30308903 = 45463355) B45463355
theorem B2366063 : Blo 1576486 2366063 := bstep (se 1 (by rfl) ⟨1774547, by rfl⟩ : syracuseStep 2366063 = 3549095) B3549095
theorem B699792007 : Blo 1576486 699792007 := bstep (se 1 (by rfl) ⟨524844005, by rfl⟩ : syracuseStep 699792007 = 1049688011) B1049688011
theorem B2841323 : Blo 1576486 2841323 := bstep (se 1 (by rfl) ⟨2130992, by rfl⟩ : syracuseStep 2841323 = 4261985) B4261985
theorem B1997551 : Blo 1576486 1997551 := bstep (se 1 (by rfl) ⟨1498163, by rfl⟩ : syracuseStep 1997551 = 2996327) B2996327
theorem B2661545 : Blo 1576486 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B2366633 : Blo 1576486 2366633 := bstep (se 2 (by rfl) ⟨887487, by rfl⟩ : syracuseStep 2366633 = 1774975) B1774975
theorem B25935527 : Blo 1576486 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B2662139 : Blo 1576486 2662139 := bstep (se 1 (by rfl) ⟨1996604, by rfl⟩ : syracuseStep 2662139 = 3993209) B3993209
theorem B20217721 : Blo 1576486 20217721 := bstep (se 2 (by rfl) ⟨7581645, by rfl⟩ : syracuseStep 20217721 = 15163291) B15163291
theorem B5324777 : Blo 1576486 5324777 := bstep (se 2 (by rfl) ⟨1996791, by rfl⟩ : syracuseStep 5324777 = 3993583) B3993583
theorem B37404697 : Blo 1576486 37404697 := bstep (se 2 (by rfl) ⟨14026761, by rfl⟩ : syracuseStep 37404697 = 28053523) B28053523
theorem B131285609 : Blo 1576486 131285609 := bstep (se 2 (by rfl) ⟨49232103, by rfl⟩ : syracuseStep 131285609 = 98464207) B98464207
theorem B2843305 : Blo 1576486 2843305 := bstep (se 2 (by rfl) ⟨1066239, by rfl⟩ : syracuseStep 2843305 = 2132479) B2132479
theorem B2663401 : Blo 1576486 2663401 := bstep (se 2 (by rfl) ⟨998775, by rfl⟩ : syracuseStep 2663401 = 1997551) B1997551
theorem B9725065 : Blo 1576486 9725065 := bstep (se 2 (by rfl) ⟨3646899, by rfl⟩ : syracuseStep 9725065 = 7293799) B7293799
theorem B3990779 : Blo 1576486 3990779 := bstep (se 1 (by rfl) ⟨2993084, by rfl⟩ : syracuseStep 3990779 = 5986169) B5986169
theorem B3990809 : Blo 1576486 3990809 := bstep (se 2 (by rfl) ⟨1496553, by rfl⟩ : syracuseStep 3990809 = 2993107) B2993107
theorem B5326235 : Blo 1576486 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B129517217 : Blo 1576486 129517217 := bstep (se 2 (by rfl) ⟨48568956, by rfl⟩ : syracuseStep 129517217 = 97137913) B97137913
theorem B3548843 : Blo 1576486 3548843 := bstep (se 1 (by rfl) ⟨2661632, by rfl⟩ : syracuseStep 3548843 = 5323265) B5323265
theorem B6834239 : Blo 1576486 6834239 := bstep (se 1 (by rfl) ⟨5125679, by rfl⟩ : syracuseStep 6834239 = 10251359) B10251359
theorem B4491575 : Blo 1576486 4491575 := bstep (se 1 (by rfl) ⟨3368681, by rfl⟩ : syracuseStep 4491575 = 6737363) B6737363
theorem B17975681 : Blo 1576486 17975681 := bstep (se 2 (by rfl) ⟨6740880, by rfl⟩ : syracuseStep 17975681 = 13481761) B13481761
theorem B3992105 : Blo 1576486 3992105 := bstep (se 2 (by rfl) ⟨1497039, by rfl⟩ : syracuseStep 3992105 = 2994079) B2994079
theorem B3549851 : Blo 1576486 3549851 := bstep (se 1 (by rfl) ⟨2662388, by rfl⟩ : syracuseStep 3549851 = 5324777) B5324777
theorem B2993183 : Blo 1576486 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B7990487 : Blo 1576486 7990487 := bstep (se 1 (by rfl) ⟨5992865, by rfl⟩ : syracuseStep 7990487 = 11985731) B11985731
theorem B933056009 : Blo 1576486 933056009 := bstep (se 2 (by rfl) ⟨349896003, by rfl⟩ : syracuseStep 933056009 = 699792007) B699792007
theorem B15158987 : Blo 1576486 15158987 := bstep (se 1 (by rfl) ⟨11369240, by rfl⟩ : syracuseStep 15158987 = 22738481) B22738481
theorem B1576735 : Blo 1576486 1576735 := bstep (se 1 (by rfl) ⟨1182551, by rfl⟩ : syracuseStep 1576735 = 2365103) B2365103
theorem B15577115 : Blo 1576486 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B1577031 : Blo 1576486 1577031 := bstep (se 1 (by rfl) ⟨1182773, by rfl⟩ : syracuseStep 1577031 = 2365547) B2365547
theorem B1577119 : Blo 1576486 1577119 := bstep (se 1 (by rfl) ⟨1182839, by rfl⟩ : syracuseStep 1577119 = 2365679) B2365679
theorem B13480121 : Blo 1576486 13480121 := bstep (se 2 (by rfl) ⟨5055045, by rfl⟩ : syracuseStep 13480121 = 10110091) B10110091
theorem B1773895 : Blo 1576486 1773895 := bstep (se 1 (by rfl) ⟨1330421, by rfl⟩ : syracuseStep 1773895 = 2660843) B2660843
theorem B4264289 : Blo 1576486 4264289 := bstep (se 2 (by rfl) ⟨1599108, by rfl⟩ : syracuseStep 4264289 = 3198217) B3198217
theorem B20205935 : Blo 1576486 20205935 := bstep (se 1 (by rfl) ⟨15154451, by rfl⟩ : syracuseStep 20205935 = 30308903) B30308903
theorem B1577375 : Blo 1576486 1577375 := bstep (se 1 (by rfl) ⟨1183031, by rfl⟩ : syracuseStep 1577375 = 2366063) B2366063
theorem B30306899 : Blo 1576486 30306899 := bstep (se 1 (by rfl) ⟨22730174, by rfl⟩ : syracuseStep 30306899 = 45460349) B45460349
theorem B1774363 : Blo 1576486 1774363 := bstep (se 1 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 1774363 = 2661545) B2661545
theorem B1577755 : Blo 1576486 1577755 := bstep (se 1 (by rfl) ⟨1183316, by rfl⟩ : syracuseStep 1577755 = 2366633) B2366633
theorem B17290351 : Blo 1576486 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B30307445 : Blo 1576486 30307445 := bstep (se 5 (by rfl) ⟨1420661, by rfl⟩ : syracuseStep 30307445 = 2841323) B2841323
theorem B26956961 : Blo 1576486 26956961 := bstep (se 2 (by rfl) ⟨10108860, by rfl⟩ : syracuseStep 26956961 = 20217721) B20217721
theorem B1774759 : Blo 1576486 1774759 := bstep (se 1 (by rfl) ⟨1331069, by rfl⟩ : syracuseStep 1774759 = 2662139) B2662139
theorem B3994859 : Blo 1576486 3994859 := bstep (se 1 (by rfl) ⟨2996144, by rfl⟩ : syracuseStep 3994859 = 5992289) B5992289
theorem B5322239 : Blo 1576486 5322239 := bstep (se 1 (by rfl) ⟨3991679, by rfl⟩ : syracuseStep 5322239 = 7983359) B7983359
theorem B3995183 : Blo 1576486 3995183 := bstep (se 1 (by rfl) ⟨2996387, by rfl⟩ : syracuseStep 3995183 = 5992775) B5992775
theorem B5052073 : Blo 1576486 5052073 := bstep (se 2 (by rfl) ⟨1894527, by rfl⟩ : syracuseStep 5052073 = 3789055) B3789055
theorem B1775335 : Blo 1576486 1775335 := bstep (se 1 (by rfl) ⟨1331501, by rfl⟩ : syracuseStep 1775335 = 2663003) B2663003
theorem B12785597 : Blo 1576486 12785597 := bstep (se 3 (by rfl) ⟨2397299, by rfl⟩ : syracuseStep 12785597 = 4794599) B4794599
theorem B1775551 : Blo 1576486 1775551 := bstep (se 1 (by rfl) ⟨1331663, by rfl⟩ : syracuseStep 1775551 = 2663327) B2663327
theorem B2365481 : Blo 1576486 2365481 := bstep (se 2 (by rfl) ⟨887055, by rfl⟩ : syracuseStep 2365481 = 1774111) B1774111
theorem B43776071 : Blo 1576486 43776071 := bstep (se 1 (by rfl) ⟨32832053, by rfl⟩ : syracuseStep 43776071 = 65664107) B65664107
theorem B1996903 : Blo 1576486 1996903 := bstep (se 1 (by rfl) ⟨1497677, by rfl⟩ : syracuseStep 1996903 = 2995355) B2995355
theorem B15169751 : Blo 1576486 15169751 := bstep (se 1 (by rfl) ⟨11377313, by rfl⟩ : syracuseStep 15169751 = 22754627) B22754627
theorem B5323103 : Blo 1576486 5323103 := bstep (se 1 (by rfl) ⟨3992327, by rfl⟩ : syracuseStep 5323103 = 7984655) B7984655
theorem B6740455 : Blo 1576486 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B6740471 : Blo 1576486 6740471 := bstep (se 1 (by rfl) ⟨5055353, by rfl⟩ : syracuseStep 6740471 = 10110707) B10110707
theorem B112261963 : Blo 1576486 112261963 := bstep (se 1 (by rfl) ⟨84196472, by rfl⟩ : syracuseStep 112261963 = 168392945) B168392945
theorem B7986761 : Blo 1576486 7986761 := bstep (se 2 (by rfl) ⟨2995035, by rfl⟩ : syracuseStep 7986761 = 5990071) B5990071
theorem B5987945 : Blo 1576486 5987945 := bstep (se 2 (by rfl) ⟨2245479, by rfl⟩ : syracuseStep 5987945 = 4490959) B4490959
theorem B2367131 : Blo 1576486 2367131 := bstep (se 1 (by rfl) ⟨1775348, by rfl⟩ : syracuseStep 2367131 = 3550697) B3550697
theorem B2367335 : Blo 1576486 2367335 := bstep (se 1 (by rfl) ⟨1775501, by rfl⟩ : syracuseStep 2367335 = 3551003) B3551003
theorem B17055593 : Blo 1576486 17055593 := bstep (se 2 (by rfl) ⟨6395847, by rfl⟩ : syracuseStep 17055593 = 12791695) B12791695
theorem B49872929 : Blo 1576486 49872929 := bstep (se 2 (by rfl) ⟨18702348, by rfl⟩ : syracuseStep 49872929 = 37404697) B37404697
theorem B8986747 : Blo 1576486 8986747 := bstep (se 1 (by rfl) ⟨6740060, by rfl⟩ : syracuseStep 8986747 = 13480121) B13480121
theorem B2662537 : Blo 1576486 2662537 := bstep (se 2 (by rfl) ⟨998451, by rfl⟩ : syracuseStep 2662537 = 1996903) B1996903
theorem B2842859 : Blo 1576486 2842859 := bstep (se 1 (by rfl) ⟨2132144, by rfl⟩ : syracuseStep 2842859 = 4264289) B4264289
theorem B87523739 : Blo 1576486 87523739 := bstep (se 1 (by rfl) ⟨65642804, by rfl⟩ : syracuseStep 87523739 = 131285609) B131285609
theorem B8987273 : Blo 1576486 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B2663239 : Blo 1576486 2663239 := bstep (se 1 (by rfl) ⟨1997429, by rfl⟩ : syracuseStep 2663239 = 3994859) B3994859
theorem B15164293 : Blo 1576486 15164293 := bstep (se 4 (by rfl) ⟨1421652, by rfl⟩ : syracuseStep 15164293 = 2843305) B2843305
theorem B3548159 : Blo 1576486 3548159 := bstep (se 1 (by rfl) ⟨2661119, by rfl⟩ : syracuseStep 3548159 = 5322239) B5322239
theorem B2663455 : Blo 1576486 2663455 := bstep (se 1 (by rfl) ⟨1997591, by rfl⟩ : syracuseStep 2663455 = 3995183) B3995183
theorem B86344811 : Blo 1576486 86344811 := bstep (se 1 (by rfl) ⟨64758608, by rfl⟩ : syracuseStep 86344811 = 129517217) B129517217
theorem B4556159 : Blo 1576486 4556159 := bstep (se 1 (by rfl) ⟨3417119, by rfl⟩ : syracuseStep 4556159 = 6834239) B6834239
theorem B3548735 : Blo 1576486 3548735 := bstep (se 1 (by rfl) ⟨2661551, by rfl⟩ : syracuseStep 3548735 = 5323103) B5323103
theorem B5326991 : Blo 1576486 5326991 := bstep (se 1 (by rfl) ⟨3995243, by rfl⟩ : syracuseStep 5326991 = 7990487) B7990487
theorem B6736097 : Blo 1576486 6736097 := bstep (se 2 (by rfl) ⟨2526036, by rfl⟩ : syracuseStep 6736097 = 5052073) B5052073
theorem B622037339 : Blo 1576486 622037339 := bstep (se 1 (by rfl) ⟨466528004, by rfl⟩ : syracuseStep 622037339 = 933056009) B933056009
theorem B3991963 : Blo 1576486 3991963 := bstep (se 1 (by rfl) ⟨2993972, by rfl⟩ : syracuseStep 3991963 = 5987945) B5987945
theorem B13470623 : Blo 1576486 13470623 := bstep (se 1 (by rfl) ⟨10102967, by rfl⟩ : syracuseStep 13470623 = 20205935) B20205935
theorem B20204599 : Blo 1576486 20204599 := bstep (se 1 (by rfl) ⟨15153449, by rfl⟩ : syracuseStep 20204599 = 30306899) B30306899
theorem B51867013 : Blo 1576486 51867013 := bstep (se 4 (by rfl) ⟨4862532, by rfl⟩ : syracuseStep 51867013 = 9725065) B9725065
theorem B20204963 : Blo 1576486 20204963 := bstep (se 1 (by rfl) ⟨15153722, by rfl⟩ : syracuseStep 20204963 = 30307445) B30307445
theorem B3550823 : Blo 1576486 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B8523731 : Blo 1576486 8523731 := bstep (se 1 (by rfl) ⟨6392798, by rfl⟩ : syracuseStep 8523731 = 12785597) B12785597
theorem B3551201 : Blo 1576486 3551201 := bstep (se 2 (by rfl) ⟨1331700, by rfl⟩ : syracuseStep 3551201 = 2663401) B2663401
theorem B1576987 : Blo 1576486 1576987 := bstep (se 1 (by rfl) ⟨1182740, by rfl⟩ : syracuseStep 1576987 = 2365481) B2365481
theorem B29184047 : Blo 1576486 29184047 := bstep (se 1 (by rfl) ⟨21888035, by rfl⟩ : syracuseStep 29184047 = 43776071) B43776071
theorem B10113167 : Blo 1576486 10113167 := bstep (se 1 (by rfl) ⟨7584875, by rfl⟩ : syracuseStep 10113167 = 15169751) B15169751
theorem B2994383 : Blo 1576486 2994383 := bstep (se 1 (by rfl) ⟨2245787, by rfl⟩ : syracuseStep 2994383 = 4491575) B4491575
theorem B4493647 : Blo 1576486 4493647 := bstep (se 1 (by rfl) ⟨3370235, by rfl⟩ : syracuseStep 4493647 = 6740471) B6740471
theorem B1995455 : Blo 1576486 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B1578087 : Blo 1576486 1578087 := bstep (se 1 (by rfl) ⟨1183565, by rfl⟩ : syracuseStep 1578087 = 2367131) B2367131
theorem B10105991 : Blo 1576486 10105991 := bstep (se 1 (by rfl) ⟨7579493, by rfl⟩ : syracuseStep 10105991 = 15158987) B15158987
theorem B1578223 : Blo 1576486 1578223 := bstep (se 1 (by rfl) ⟨1183667, by rfl⟩ : syracuseStep 1578223 = 2367335) B2367335
theorem B41538973 : Blo 1576486 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B2365193 : Blo 1576486 2365193 := bstep (se 2 (by rfl) ⟨886947, by rfl⟩ : syracuseStep 2365193 = 1773895) B1773895
theorem B92215205 : Blo 1576486 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B17971307 : Blo 1576486 17971307 := bstep (se 1 (by rfl) ⟨13478480, by rfl⟩ : syracuseStep 17971307 = 26956961) B26956961
theorem B2660519 : Blo 1576486 2660519 := bstep (se 1 (by rfl) ⟨1995389, by rfl⟩ : syracuseStep 2660519 = 3990779) B3990779
theorem B2660539 : Blo 1576486 2660539 := bstep (se 1 (by rfl) ⟨1995404, by rfl⟩ : syracuseStep 2660539 = 3990809) B3990809
theorem B2365817 : Blo 1576486 2365817 := bstep (se 2 (by rfl) ⟨887181, by rfl⟩ : syracuseStep 2365817 = 1774363) B1774363
theorem B149682617 : Blo 1576486 149682617 := bstep (se 2 (by rfl) ⟨56130981, by rfl⟩ : syracuseStep 149682617 = 112261963) B112261963
theorem B2365895 : Blo 1576486 2365895 := bstep (se 1 (by rfl) ⟨1774421, by rfl⟩ : syracuseStep 2365895 = 3548843) B3548843
theorem B2366345 : Blo 1576486 2366345 := bstep (se 2 (by rfl) ⟨887379, by rfl⟩ : syracuseStep 2366345 = 1774759) B1774759
theorem B11983787 : Blo 1576486 11983787 := bstep (se 1 (by rfl) ⟨8987840, by rfl⟩ : syracuseStep 11983787 = 17975681) B17975681
theorem B2661403 : Blo 1576486 2661403 := bstep (se 1 (by rfl) ⟨1996052, by rfl⟩ : syracuseStep 2661403 = 3992105) B3992105
theorem B2366567 : Blo 1576486 2366567 := bstep (se 1 (by rfl) ⟨1774925, by rfl⟩ : syracuseStep 2366567 = 3549851) B3549851
theorem B2367113 : Blo 1576486 2367113 := bstep (se 2 (by rfl) ⟨887667, by rfl⟩ : syracuseStep 2367113 = 1775335) B1775335
theorem B5324507 : Blo 1576486 5324507 := bstep (se 1 (by rfl) ⟨3993380, by rfl⟩ : syracuseStep 5324507 = 7986761) B7986761
theorem B11370395 : Blo 1576486 11370395 := bstep (se 1 (by rfl) ⟨8527796, by rfl⟩ : syracuseStep 11370395 = 17055593) B17055593
theorem B2367401 : Blo 1576486 2367401 := bstep (se 2 (by rfl) ⟨887775, by rfl⟩ : syracuseStep 2367401 = 1775551) B1775551
theorem B19456031 : Blo 1576486 19456031 := bstep (se 1 (by rfl) ⟨14592023, by rfl⟩ : syracuseStep 19456031 = 29184047) B29184047
theorem B6742111 : Blo 1576486 6742111 := bstep (se 1 (by rfl) ⟨5056583, by rfl⟩ : syracuseStep 6742111 = 10113167) B10113167
theorem B3547385 : Blo 1576486 3547385 := bstep (se 2 (by rfl) ⟨1330269, by rfl⟩ : syracuseStep 3547385 = 2660539) B2660539
theorem B20219057 : Blo 1576486 20219057 := bstep (se 2 (by rfl) ⟨7582146, by rfl⟩ : syracuseStep 20219057 = 15164293) B15164293
theorem B3548537 : Blo 1576486 3548537 := bstep (se 2 (by rfl) ⟨1330701, by rfl⟩ : syracuseStep 3548537 = 2661403) B2661403
theorem B4490731 : Blo 1576486 4490731 := bstep (se 1 (by rfl) ⟨3368048, by rfl⟩ : syracuseStep 4490731 = 6736097) B6736097
theorem B99788411 : Blo 1576486 99788411 := bstep (se 1 (by rfl) ⟨74841308, by rfl⟩ : syracuseStep 99788411 = 149682617) B149682617
theorem B8980415 : Blo 1576486 8980415 := bstep (se 1 (by rfl) ⟨6735311, by rfl⟩ : syracuseStep 8980415 = 13470623) B13470623
theorem B7989191 : Blo 1576486 7989191 := bstep (se 1 (by rfl) ⟨5991893, by rfl⟩ : syracuseStep 7989191 = 11983787) B11983787
theorem B13469975 : Blo 1576486 13469975 := bstep (se 1 (by rfl) ⟨10102481, by rfl⟩ : syracuseStep 13469975 = 20204963) B20204963
theorem B3549671 : Blo 1576486 3549671 := bstep (se 1 (by rfl) ⟨2662253, by rfl⟩ : syracuseStep 3549671 = 5324507) B5324507
theorem B7580263 : Blo 1576486 7580263 := bstep (se 1 (by rfl) ⟨5685197, by rfl⟩ : syracuseStep 7580263 = 11370395) B11370395
theorem B1895239 : Blo 1576486 1895239 := bstep (se 1 (by rfl) ⟨1421429, by rfl⟩ : syracuseStep 1895239 = 2842859) B2842859
theorem B3550049 : Blo 1576486 3550049 := bstep (se 2 (by rfl) ⟨1331268, by rfl⟩ : syracuseStep 3550049 = 2662537) B2662537
theorem B5991515 : Blo 1576486 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B5991529 : Blo 1576486 5991529 := bstep (se 2 (by rfl) ⟨2246823, by rfl⟩ : syracuseStep 5991529 = 4493647) B4493647
theorem B6737327 : Blo 1576486 6737327 := bstep (se 1 (by rfl) ⟨5052995, by rfl⟩ : syracuseStep 6737327 = 10105991) B10105991
theorem B3550985 : Blo 1576486 3550985 := bstep (se 2 (by rfl) ⟨1331619, by rfl⟩ : syracuseStep 3550985 = 2663239) B2663239
theorem B1576795 : Blo 1576486 1576795 := bstep (se 1 (by rfl) ⟨1182596, by rfl⟩ : syracuseStep 1576795 = 2365193) B2365193
theorem B61476803 : Blo 1576486 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B3551273 : Blo 1576486 3551273 := bstep (se 2 (by rfl) ⟨1331727, by rfl⟩ : syracuseStep 3551273 = 2663455) B2663455
theorem B11980871 : Blo 1576486 11980871 := bstep (se 1 (by rfl) ⟨8985653, by rfl⟩ : syracuseStep 11980871 = 17971307) B17971307
theorem B26939465 : Blo 1576486 26939465 := bstep (se 2 (by rfl) ⟨10102299, by rfl⟩ : syracuseStep 26939465 = 20204599) B20204599
theorem B3551327 : Blo 1576486 3551327 := bstep (se 1 (by rfl) ⟨2663495, by rfl⟩ : syracuseStep 3551327 = 5326991) B5326991
theorem B1773679 : Blo 1576486 1773679 := bstep (se 1 (by rfl) ⟨1330259, by rfl⟩ : syracuseStep 1773679 = 2660519) B2660519
theorem B414691559 : Blo 1576486 414691559 := bstep (se 1 (by rfl) ⟨311018669, by rfl⟩ : syracuseStep 414691559 = 622037339) B622037339
theorem B1577211 : Blo 1576486 1577211 := bstep (se 1 (by rfl) ⟨1182908, by rfl⟩ : syracuseStep 1577211 = 2365817) B2365817
theorem B1577263 : Blo 1576486 1577263 := bstep (se 1 (by rfl) ⟨1182947, by rfl⟩ : syracuseStep 1577263 = 2365895) B2365895
theorem B5321213 : Blo 1576486 5321213 := bstep (se 3 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 5321213 = 1995455) B1995455
theorem B1577563 : Blo 1576486 1577563 := bstep (se 1 (by rfl) ⟨1183172, by rfl⟩ : syracuseStep 1577563 = 2366345) B2366345
theorem B1577711 : Blo 1576486 1577711 := bstep (se 1 (by rfl) ⟨1183283, by rfl⟩ : syracuseStep 1577711 = 2366567) B2366567
theorem B1578075 : Blo 1576486 1578075 := bstep (se 1 (by rfl) ⟨1183556, by rfl⟩ : syracuseStep 1578075 = 2367113) B2367113
theorem B1578267 : Blo 1576486 1578267 := bstep (se 1 (by rfl) ⟨1183700, by rfl⟩ : syracuseStep 1578267 = 2367401) B2367401
theorem B5682487 : Blo 1576486 5682487 := bstep (se 1 (by rfl) ⟨4261865, by rfl⟩ : syracuseStep 5682487 = 8523731) B8523731
theorem B132994477 : Blo 1576486 132994477 := bstep (se 3 (by rfl) ⟨24936464, by rfl⟩ : syracuseStep 132994477 = 49872929) B49872929
theorem B1996255 : Blo 1576486 1996255 := bstep (se 1 (by rfl) ⟨1497191, by rfl⟩ : syracuseStep 1996255 = 2994383) B2994383
theorem B11982329 : Blo 1576486 11982329 := bstep (se 2 (by rfl) ⟨4493373, by rfl⟩ : syracuseStep 11982329 = 8986747) B8986747
theorem B58349159 : Blo 1576486 58349159 := bstep (se 1 (by rfl) ⟨43761869, by rfl⟩ : syracuseStep 58349159 = 87523739) B87523739
theorem B5322617 : Blo 1576486 5322617 := bstep (se 2 (by rfl) ⟨1995981, by rfl⟩ : syracuseStep 5322617 = 3991963) B3991963
theorem B2365439 : Blo 1576486 2365439 := bstep (se 1 (by rfl) ⟨1774079, by rfl⟩ : syracuseStep 2365439 = 3548159) B3548159
theorem B57563207 : Blo 1576486 57563207 := bstep (se 1 (by rfl) ⟨43172405, by rfl⟩ : syracuseStep 57563207 = 86344811) B86344811
theorem B3037439 : Blo 1576486 3037439 := bstep (se 1 (by rfl) ⟨2278079, by rfl⟩ : syracuseStep 3037439 = 4556159) B4556159
theorem B2365823 : Blo 1576486 2365823 := bstep (se 1 (by rfl) ⟨1774367, by rfl⟩ : syracuseStep 2365823 = 3548735) B3548735
theorem B69156017 : Blo 1576486 69156017 := bstep (se 2 (by rfl) ⟨25933506, by rfl⟩ : syracuseStep 69156017 = 51867013) B51867013
theorem B55385297 : Blo 1576486 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B2367215 : Blo 1576486 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B2367467 : Blo 1576486 2367467 := bstep (se 1 (by rfl) ⟨1775600, by rfl⟩ : syracuseStep 2367467 = 3551201) B3551201
theorem B2367515 : Blo 1576486 2367515 := bstep (se 1 (by rfl) ⟨1775636, by rfl⟩ : syracuseStep 2367515 = 3551273) B3551273
theorem B7987247 : Blo 1576486 7987247 := bstep (se 1 (by rfl) ⟨5990435, by rfl⟩ : syracuseStep 7987247 = 11980871) B11980871
theorem B2367551 : Blo 1576486 2367551 := bstep (se 1 (by rfl) ⟨1775663, by rfl⟩ : syracuseStep 2367551 = 3551327) B3551327
theorem B3547475 : Blo 1576486 3547475 := bstep (se 1 (by rfl) ⟨2660606, by rfl⟩ : syracuseStep 3547475 = 5321213) B5321213
theorem B7988219 : Blo 1576486 7988219 := bstep (se 1 (by rfl) ⟨5991164, by rfl⟩ : syracuseStep 7988219 = 11982329) B11982329
theorem B3548411 : Blo 1576486 3548411 := bstep (se 1 (by rfl) ⟨2661308, by rfl⟩ : syracuseStep 3548411 = 5322617) B5322617
theorem B5326127 : Blo 1576486 5326127 := bstep (se 1 (by rfl) ⟨3994595, by rfl⟩ : syracuseStep 5326127 = 7989191) B7989191
theorem B7988705 : Blo 1576486 7988705 := bstep (se 2 (by rfl) ⟨2995764, by rfl⟩ : syracuseStep 7988705 = 5991529) B5991529
theorem B2024959 : Blo 1576486 2024959 := bstep (se 1 (by rfl) ⟨1518719, by rfl⟩ : syracuseStep 2024959 = 3037439) B3037439
theorem B8979983 : Blo 1576486 8979983 := bstep (se 1 (by rfl) ⟨6734987, by rfl⟩ : syracuseStep 8979983 = 13469975) B13469975
theorem B177325969 : Blo 1576486 177325969 := bstep (se 2 (by rfl) ⟨66497238, by rfl⟩ : syracuseStep 177325969 = 132994477) B132994477
theorem B36923531 : Blo 1576486 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B4491551 : Blo 1576486 4491551 := bstep (se 1 (by rfl) ⟨3368663, by rfl⟩ : syracuseStep 4491551 = 6737327) B6737327
theorem B12970687 : Blo 1576486 12970687 := bstep (se 1 (by rfl) ⟨9728015, by rfl⟩ : syracuseStep 12970687 = 19456031) B19456031
theorem B17959643 : Blo 1576486 17959643 := bstep (se 1 (by rfl) ⟨13469732, by rfl⟩ : syracuseStep 17959643 = 26939465) B26939465
theorem B8989481 : Blo 1576486 8989481 := bstep (se 2 (by rfl) ⟨3371055, by rfl⟩ : syracuseStep 8989481 = 6742111) B6742111
theorem B13479371 : Blo 1576486 13479371 := bstep (se 1 (by rfl) ⟨10109528, by rfl⟩ : syracuseStep 13479371 = 20219057) B20219057
theorem B38899439 : Blo 1576486 38899439 := bstep (se 1 (by rfl) ⟨29174579, by rfl⟩ : syracuseStep 38899439 = 58349159) B58349159
theorem B2526985 : Blo 1576486 2526985 := bstep (se 2 (by rfl) ⟨947619, by rfl⟩ : syracuseStep 2526985 = 1895239) B1895239
theorem B1576959 : Blo 1576486 1576959 := bstep (se 1 (by rfl) ⟨1182719, by rfl⟩ : syracuseStep 1576959 = 2365439) B2365439
theorem B38375471 : Blo 1576486 38375471 := bstep (se 1 (by rfl) ⟨28781603, by rfl⟩ : syracuseStep 38375471 = 57563207) B57563207
theorem B1577215 : Blo 1576486 1577215 := bstep (se 1 (by rfl) ⟨1182911, by rfl⟩ : syracuseStep 1577215 = 2365823) B2365823
theorem B3994343 : Blo 1576486 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B1578143 : Blo 1576486 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B1578311 : Blo 1576486 1578311 := bstep (se 1 (by rfl) ⟨1183733, by rfl⟩ : syracuseStep 1578311 = 2367467) B2367467
theorem B2364905 : Blo 1576486 2364905 := bstep (se 2 (by rfl) ⟨886839, by rfl⟩ : syracuseStep 2364905 = 1773679) B1773679
theorem B276461039 : Blo 1576486 276461039 := bstep (se 1 (by rfl) ⟨207345779, by rfl⟩ : syracuseStep 276461039 = 414691559) B414691559
theorem B2364923 : Blo 1576486 2364923 := bstep (se 1 (by rfl) ⟨1773692, by rfl⟩ : syracuseStep 2364923 = 3547385) B3547385
theorem B10107017 : Blo 1576486 10107017 := bstep (se 2 (by rfl) ⟨3790131, by rfl⟩ : syracuseStep 10107017 = 7580263) B7580263
theorem B2365691 : Blo 1576486 2365691 := bstep (se 1 (by rfl) ⟨1774268, by rfl⟩ : syracuseStep 2365691 = 3548537) B3548537
theorem B66525607 : Blo 1576486 66525607 := bstep (se 1 (by rfl) ⟨49894205, by rfl⟩ : syracuseStep 66525607 = 99788411) B99788411
theorem B5986943 : Blo 1576486 5986943 := bstep (se 1 (by rfl) ⟨4490207, by rfl⟩ : syracuseStep 5986943 = 8980415) B8980415
theorem B2366447 : Blo 1576486 2366447 := bstep (se 1 (by rfl) ⟨1774835, by rfl⟩ : syracuseStep 2366447 = 3549671) B3549671
theorem B7576649 : Blo 1576486 7576649 := bstep (se 2 (by rfl) ⟨2841243, by rfl⟩ : syracuseStep 7576649 = 5682487) B5682487
theorem B2366699 : Blo 1576486 2366699 := bstep (se 1 (by rfl) ⟨1775024, by rfl⟩ : syracuseStep 2366699 = 3550049) B3550049
theorem B2661673 : Blo 1576486 2661673 := bstep (se 2 (by rfl) ⟨998127, by rfl⟩ : syracuseStep 2661673 = 1996255) B1996255
theorem B5987641 : Blo 1576486 5987641 := bstep (se 2 (by rfl) ⟨2245365, by rfl⟩ : syracuseStep 5987641 = 4490731) B4490731
theorem B46104011 : Blo 1576486 46104011 := bstep (se 1 (by rfl) ⟨34578008, by rfl⟩ : syracuseStep 46104011 = 69156017) B69156017
theorem B2367323 : Blo 1576486 2367323 := bstep (se 1 (by rfl) ⟨1775492, by rfl⟩ : syracuseStep 2367323 = 3550985) B3550985
theorem B40984535 : Blo 1576486 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B25583647 : Blo 1576486 25583647 := bstep (se 1 (by rfl) ⟨19187735, by rfl⟩ : syracuseStep 25583647 = 38375471) B38375471
theorem B5324831 : Blo 1576486 5324831 := bstep (se 1 (by rfl) ⟨3993623, by rfl⟩ : syracuseStep 5324831 = 7987247) B7987247
theorem B2662895 : Blo 1576486 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B5325479 : Blo 1576486 5325479 := bstep (se 1 (by rfl) ⟨3994109, by rfl⟩ : syracuseStep 5325479 = 7988219) B7988219
theorem B11977469 : Blo 1576486 11977469 := bstep (se 3 (by rfl) ⟨2245775, by rfl⟩ : syracuseStep 11977469 = 4491551) B4491551
theorem B17294249 : Blo 1576486 17294249 := bstep (se 2 (by rfl) ⟨6485343, by rfl⟩ : syracuseStep 17294249 = 12970687) B12970687
theorem B5325803 : Blo 1576486 5325803 := bstep (se 1 (by rfl) ⟨3994352, by rfl⟩ : syracuseStep 5325803 = 7988705) B7988705
theorem B3548897 : Blo 1576486 3548897 := bstep (se 2 (by rfl) ⟨1330836, by rfl⟩ : syracuseStep 3548897 = 2661673) B2661673
theorem B3991295 : Blo 1576486 3991295 := bstep (se 1 (by rfl) ⟨2993471, by rfl⟩ : syracuseStep 3991295 = 5986943) B5986943
theorem B3369313 : Blo 1576486 3369313 := bstep (se 2 (by rfl) ⟨1263492, by rfl⟩ : syracuseStep 3369313 = 2526985) B2526985
theorem B27323023 : Blo 1576486 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B98462749 : Blo 1576486 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B3550751 : Blo 1576486 3550751 := bstep (se 1 (by rfl) ⟨2663063, by rfl⟩ : syracuseStep 3550751 = 5326127) B5326127
theorem B1576603 : Blo 1576486 1576603 := bstep (se 1 (by rfl) ⟨1182452, by rfl⟩ : syracuseStep 1576603 = 2364905) B2364905
theorem B184307359 : Blo 1576486 184307359 := bstep (se 1 (by rfl) ⟨138230519, by rfl⟩ : syracuseStep 184307359 = 276461039) B276461039
theorem B1576615 : Blo 1576486 1576615 := bstep (se 1 (by rfl) ⟨1182461, by rfl⟩ : syracuseStep 1576615 = 2364923) B2364923
theorem B6738011 : Blo 1576486 6738011 := bstep (se 1 (by rfl) ⟨5053508, by rfl⟩ : syracuseStep 6738011 = 10107017) B10107017
theorem B1577127 : Blo 1576486 1577127 := bstep (se 1 (by rfl) ⟨1182845, by rfl⟩ : syracuseStep 1577127 = 2365691) B2365691
theorem B7983521 : Blo 1576486 7983521 := bstep (se 2 (by rfl) ⟨2993820, by rfl⟩ : syracuseStep 7983521 = 5987641) B5987641
theorem B11973095 : Blo 1576486 11973095 := bstep (se 1 (by rfl) ⟨8979821, by rfl⟩ : syracuseStep 11973095 = 17959643) B17959643
theorem B5992987 : Blo 1576486 5992987 := bstep (se 1 (by rfl) ⟨4494740, by rfl⟩ : syracuseStep 5992987 = 8989481) B8989481
theorem B1577631 : Blo 1576486 1577631 := bstep (se 1 (by rfl) ⟨1183223, by rfl⟩ : syracuseStep 1577631 = 2366447) B2366447
theorem B2699945 : Blo 1576486 2699945 := bstep (se 2 (by rfl) ⟨1012479, by rfl⟩ : syracuseStep 2699945 = 2024959) B2024959
theorem B5051099 : Blo 1576486 5051099 := bstep (se 1 (by rfl) ⟨3788324, by rfl⟩ : syracuseStep 5051099 = 7576649) B7576649
theorem B1577799 : Blo 1576486 1577799 := bstep (se 1 (by rfl) ⟨1183349, by rfl⟩ : syracuseStep 1577799 = 2366699) B2366699
theorem B25932959 : Blo 1576486 25932959 := bstep (se 1 (by rfl) ⟨19449719, by rfl⟩ : syracuseStep 25932959 = 38899439) B38899439
theorem B236434625 : Blo 1576486 236434625 := bstep (se 2 (by rfl) ⟨88662984, by rfl⟩ : syracuseStep 236434625 = 177325969) B177325969
theorem B1578215 : Blo 1576486 1578215 := bstep (se 1 (by rfl) ⟨1183661, by rfl⟩ : syracuseStep 1578215 = 2367323) B2367323
theorem B1578343 : Blo 1576486 1578343 := bstep (se 1 (by rfl) ⟨1183757, by rfl⟩ : syracuseStep 1578343 = 2367515) B2367515
theorem B1578367 : Blo 1576486 1578367 := bstep (se 1 (by rfl) ⟨1183775, by rfl⟩ : syracuseStep 1578367 = 2367551) B2367551
theorem B2364983 : Blo 1576486 2364983 := bstep (se 1 (by rfl) ⟨1773737, by rfl⟩ : syracuseStep 2364983 = 3547475) B3547475
theorem B2365607 : Blo 1576486 2365607 := bstep (se 1 (by rfl) ⟨1774205, by rfl⟩ : syracuseStep 2365607 = 3548411) B3548411
theorem B5986655 : Blo 1576486 5986655 := bstep (se 1 (by rfl) ⟨4489991, by rfl⟩ : syracuseStep 5986655 = 8979983) B8979983
theorem B354803237 : Blo 1576486 354803237 := bstep (se 4 (by rfl) ⟨33262803, by rfl⟩ : syracuseStep 354803237 = 66525607) B66525607
theorem B30736007 : Blo 1576486 30736007 := bstep (se 1 (by rfl) ⟨23052005, by rfl⟩ : syracuseStep 30736007 = 46104011) B46104011
theorem B8986247 : Blo 1576486 8986247 := bstep (se 1 (by rfl) ⟨6739685, by rfl⟩ : syracuseStep 8986247 = 13479371) B13479371
theorem B34111529 : Blo 1576486 34111529 := bstep (se 2 (by rfl) ⟨12791823, by rfl⟩ : syracuseStep 34111529 = 25583647) B25583647
theorem B157623083 : Blo 1576486 157623083 := bstep (se 1 (by rfl) ⟨118217312, by rfl⟩ : syracuseStep 157623083 = 236434625) B236434625
theorem B36430697 : Blo 1576486 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B3991103 : Blo 1576486 3991103 := bstep (se 1 (by rfl) ⟨2993327, by rfl⟩ : syracuseStep 3991103 = 5986655) B5986655
theorem B13469597 : Blo 1576486 13469597 := bstep (se 3 (by rfl) ⟨2525549, by rfl⟩ : syracuseStep 13469597 = 5051099) B5051099
theorem B20490671 : Blo 1576486 20490671 := bstep (se 1 (by rfl) ⟨15368003, by rfl⟩ : syracuseStep 20490671 = 30736007) B30736007
theorem B5990831 : Blo 1576486 5990831 := bstep (se 1 (by rfl) ⟨4493123, by rfl⟩ : syracuseStep 5990831 = 8986247) B8986247
theorem B3549887 : Blo 1576486 3549887 := bstep (se 1 (by rfl) ⟨2662415, by rfl⟩ : syracuseStep 3549887 = 5324831) B5324831
theorem B4492007 : Blo 1576486 4492007 := bstep (se 1 (by rfl) ⟨3369005, by rfl⟩ : syracuseStep 4492007 = 6738011) B6738011
theorem B7982063 : Blo 1576486 7982063 := bstep (se 1 (by rfl) ⟨5986547, by rfl⟩ : syracuseStep 7982063 = 11973095) B11973095
theorem B3550319 : Blo 1576486 3550319 := bstep (se 1 (by rfl) ⟨2662739, by rfl⟩ : syracuseStep 3550319 = 5325479) B5325479
theorem B4492417 : Blo 1576486 4492417 := bstep (se 2 (by rfl) ⟨1684656, by rfl⟩ : syracuseStep 4492417 = 3369313) B3369313
theorem B3550535 : Blo 1576486 3550535 := bstep (se 1 (by rfl) ⟨2662901, by rfl⟩ : syracuseStep 3550535 = 5325803) B5325803
theorem B7990649 : Blo 1576486 7990649 := bstep (se 2 (by rfl) ⟨2996493, by rfl⟩ : syracuseStep 7990649 = 5992987) B5992987
theorem B17288639 : Blo 1576486 17288639 := bstep (se 1 (by rfl) ⟨12966479, by rfl⟩ : syracuseStep 17288639 = 25932959) B25932959
theorem B1576655 : Blo 1576486 1576655 := bstep (se 1 (by rfl) ⟨1182491, by rfl⟩ : syracuseStep 1576655 = 2364983) B2364983
theorem B1577071 : Blo 1576486 1577071 := bstep (se 1 (by rfl) ⟨1182803, by rfl⟩ : syracuseStep 1577071 = 2365607) B2365607
theorem B46117997 : Blo 1576486 46117997 := bstep (se 3 (by rfl) ⟨8647124, by rfl⟩ : syracuseStep 46117997 = 17294249) B17294249
theorem B5322347 : Blo 1576486 5322347 := bstep (se 1 (by rfl) ⟨3991760, by rfl⟩ : syracuseStep 5322347 = 7983521) B7983521
theorem B1775263 : Blo 1576486 1775263 := bstep (se 1 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 1775263 = 2662895) B2662895
theorem B1799963 : Blo 1576486 1799963 := bstep (se 1 (by rfl) ⟨1349972, by rfl⟩ : syracuseStep 1799963 = 2699945) B2699945
theorem B7984979 : Blo 1576486 7984979 := bstep (se 1 (by rfl) ⟨5988734, by rfl⟩ : syracuseStep 7984979 = 11977469) B11977469
theorem B2365931 : Blo 1576486 2365931 := bstep (se 1 (by rfl) ⟨1774448, by rfl⟩ : syracuseStep 2365931 = 3548897) B3548897
theorem B2660863 : Blo 1576486 2660863 := bstep (se 1 (by rfl) ⟨1995647, by rfl⟩ : syracuseStep 2660863 = 3991295) B3991295
theorem B131283665 : Blo 1576486 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B245743145 : Blo 1576486 245743145 := bstep (se 2 (by rfl) ⟨92153679, by rfl⟩ : syracuseStep 245743145 = 184307359) B184307359
theorem B2367167 : Blo 1576486 2367167 := bstep (se 1 (by rfl) ⟨1775375, by rfl⟩ : syracuseStep 2367167 = 3550751) B3550751
theorem B236535491 : Blo 1576486 236535491 := bstep (se 1 (by rfl) ⟨177401618, by rfl⟩ : syracuseStep 236535491 = 354803237) B354803237
theorem B22741019 : Blo 1576486 22741019 := bstep (se 1 (by rfl) ⟨17055764, by rfl⟩ : syracuseStep 22741019 = 34111529) B34111529
theorem B3547817 : Blo 1576486 3547817 := bstep (se 2 (by rfl) ⟨1330431, by rfl⟩ : syracuseStep 3547817 = 2660863) B2660863
theorem B30745331 : Blo 1576486 30745331 := bstep (se 1 (by rfl) ⟨23058998, by rfl⟩ : syracuseStep 30745331 = 46117997) B46117997
theorem B3548231 : Blo 1576486 3548231 := bstep (se 1 (by rfl) ⟨2661173, by rfl⟩ : syracuseStep 3548231 = 5322347) B5322347
theorem B8979731 : Blo 1576486 8979731 := bstep (se 1 (by rfl) ⟨6734798, by rfl⟩ : syracuseStep 8979731 = 13469597) B13469597
theorem B5989889 : Blo 1576486 5989889 := bstep (se 2 (by rfl) ⟨2246208, by rfl⟩ : syracuseStep 5989889 = 4492417) B4492417
theorem B5327099 : Blo 1576486 5327099 := bstep (se 1 (by rfl) ⟨3995324, by rfl⟩ : syracuseStep 5327099 = 7990649) B7990649
theorem B157690327 : Blo 1576486 157690327 := bstep (se 1 (by rfl) ⟨118267745, by rfl⟩ : syracuseStep 157690327 = 236535491) B236535491
theorem B105082055 : Blo 1576486 105082055 := bstep (se 1 (by rfl) ⟨78811541, by rfl⟩ : syracuseStep 105082055 = 157623083) B157623083
theorem B13660447 : Blo 1576486 13660447 := bstep (se 1 (by rfl) ⟨10245335, by rfl⟩ : syracuseStep 13660447 = 20490671) B20490671
theorem B3993887 : Blo 1576486 3993887 := bstep (se 1 (by rfl) ⟨2995415, by rfl⟩ : syracuseStep 3993887 = 5990831) B5990831
theorem B1577287 : Blo 1576486 1577287 := bstep (se 1 (by rfl) ⟨1182965, by rfl⟩ : syracuseStep 1577287 = 2365931) B2365931
theorem B2994671 : Blo 1576486 2994671 := bstep (se 1 (by rfl) ⟨2246003, by rfl⟩ : syracuseStep 2994671 = 4492007) B4492007
theorem B5321375 : Blo 1576486 5321375 := bstep (se 1 (by rfl) ⟨3991031, by rfl⟩ : syracuseStep 5321375 = 7982063) B7982063
theorem B163828763 : Blo 1576486 163828763 := bstep (se 1 (by rfl) ⟨122871572, by rfl⟩ : syracuseStep 163828763 = 245743145) B245743145
theorem B1578111 : Blo 1576486 1578111 := bstep (se 1 (by rfl) ⟨1183583, by rfl⟩ : syracuseStep 1578111 = 2367167) B2367167
theorem B19199605 : Blo 1576486 19199605 := bstep (se 5 (by rfl) ⟨899981, by rfl⟩ : syracuseStep 19199605 = 1799963) B1799963
theorem B24287131 : Blo 1576486 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B2660735 : Blo 1576486 2660735 := bstep (se 1 (by rfl) ⟨1995551, by rfl⟩ : syracuseStep 2660735 = 3991103) B3991103
theorem B5323319 : Blo 1576486 5323319 := bstep (se 1 (by rfl) ⟨3992489, by rfl⟩ : syracuseStep 5323319 = 7984979) B7984979
theorem B2366591 : Blo 1576486 2366591 := bstep (se 1 (by rfl) ⟨1774943, by rfl⟩ : syracuseStep 2366591 = 3549887) B3549887
theorem B87522443 : Blo 1576486 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B2366879 : Blo 1576486 2366879 := bstep (se 1 (by rfl) ⟨1775159, by rfl⟩ : syracuseStep 2366879 = 3550319) B3550319
theorem B2367017 : Blo 1576486 2367017 := bstep (se 2 (by rfl) ⟨887631, by rfl⟩ : syracuseStep 2367017 = 1775263) B1775263
theorem B2367023 : Blo 1576486 2367023 := bstep (se 1 (by rfl) ⟨1775267, by rfl⟩ : syracuseStep 2367023 = 3550535) B3550535
theorem B11525759 : Blo 1576486 11525759 := bstep (se 1 (by rfl) ⟨8644319, by rfl⟩ : syracuseStep 11525759 = 17288639) B17288639
theorem B2662591 : Blo 1576486 2662591 := bstep (se 1 (by rfl) ⟨1996943, by rfl⟩ : syracuseStep 2662591 = 3993887) B3993887
theorem B3547583 : Blo 1576486 3547583 := bstep (se 1 (by rfl) ⟨2660687, by rfl⟩ : syracuseStep 3547583 = 5321375) B5321375
theorem B20496887 : Blo 1576486 20496887 := bstep (se 1 (by rfl) ⟨15372665, by rfl⟩ : syracuseStep 20496887 = 30745331) B30745331
theorem B3548879 : Blo 1576486 3548879 := bstep (se 1 (by rfl) ⟨2661659, by rfl⟩ : syracuseStep 3548879 = 5323319) B5323319
theorem B18213929 : Blo 1576486 18213929 := bstep (se 2 (by rfl) ⟨6830223, by rfl⟩ : syracuseStep 18213929 = 13660447) B13660447
theorem B109219175 : Blo 1576486 109219175 := bstep (se 1 (by rfl) ⟨81914381, by rfl⟩ : syracuseStep 109219175 = 163828763) B163828763
theorem B3993259 : Blo 1576486 3993259 := bstep (se 1 (by rfl) ⟨2994944, by rfl⟩ : syracuseStep 3993259 = 5989889) B5989889
theorem B3551399 : Blo 1576486 3551399 := bstep (se 1 (by rfl) ⟨2663549, by rfl⟩ : syracuseStep 3551399 = 5327099) B5327099
theorem B1773823 : Blo 1576486 1773823 := bstep (se 1 (by rfl) ⟨1330367, by rfl⟩ : syracuseStep 1773823 = 2660735) B2660735
theorem B1577727 : Blo 1576486 1577727 := bstep (se 1 (by rfl) ⟨1183295, by rfl⟩ : syracuseStep 1577727 = 2366591) B2366591
theorem B58348295 : Blo 1576486 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B70054703 : Blo 1576486 70054703 := bstep (se 1 (by rfl) ⟨52541027, by rfl⟩ : syracuseStep 70054703 = 105082055) B105082055
theorem B1577919 : Blo 1576486 1577919 := bstep (se 1 (by rfl) ⟨1183439, by rfl⟩ : syracuseStep 1577919 = 2366879) B2366879
theorem B1578011 : Blo 1576486 1578011 := bstep (se 1 (by rfl) ⟨1183508, by rfl⟩ : syracuseStep 1578011 = 2367017) B2367017
theorem B1578015 : Blo 1576486 1578015 := bstep (se 1 (by rfl) ⟨1183511, by rfl⟩ : syracuseStep 1578015 = 2367023) B2367023
theorem B15160679 : Blo 1576486 15160679 := bstep (se 1 (by rfl) ⟨11370509, by rfl⟩ : syracuseStep 15160679 = 22741019) B22741019
theorem B2365211 : Blo 1576486 2365211 := bstep (se 1 (by rfl) ⟨1773908, by rfl⟩ : syracuseStep 2365211 = 3547817) B3547817
theorem B210253769 : Blo 1576486 210253769 := bstep (se 2 (by rfl) ⟨78845163, by rfl⟩ : syracuseStep 210253769 = 157690327) B157690327
theorem B2365487 : Blo 1576486 2365487 := bstep (se 1 (by rfl) ⟨1774115, by rfl⟩ : syracuseStep 2365487 = 3548231) B3548231
theorem B5986487 : Blo 1576486 5986487 := bstep (se 1 (by rfl) ⟨4489865, by rfl⟩ : syracuseStep 5986487 = 8979731) B8979731
theorem B7985789 : Blo 1576486 7985789 := bstep (se 3 (by rfl) ⟨1497335, by rfl⟩ : syracuseStep 7985789 = 2994671) B2994671
theorem B25599473 : Blo 1576486 25599473 := bstep (se 2 (by rfl) ⟨9599802, by rfl⟩ : syracuseStep 25599473 = 19199605) B19199605
theorem B7683839 : Blo 1576486 7683839 := bstep (se 1 (by rfl) ⟨5762879, by rfl⟩ : syracuseStep 7683839 = 11525759) B11525759
theorem B32382841 : Blo 1576486 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B2367599 : Blo 1576486 2367599 := bstep (se 1 (by rfl) ⟨1775699, by rfl⟩ : syracuseStep 2367599 = 3551399) B3551399
theorem B13664591 : Blo 1576486 13664591 := bstep (se 1 (by rfl) ⟨10248443, by rfl⟩ : syracuseStep 13664591 = 20496887) B20496887
theorem B46703135 : Blo 1576486 46703135 := bstep (se 1 (by rfl) ⟨35027351, by rfl⟩ : syracuseStep 46703135 = 70054703) B70054703
theorem B3990991 : Blo 1576486 3990991 := bstep (se 1 (by rfl) ⟨2993243, by rfl⟩ : syracuseStep 3990991 = 5986487) B5986487
theorem B12142619 : Blo 1576486 12142619 := bstep (se 1 (by rfl) ⟨9106964, by rfl⟩ : syracuseStep 12142619 = 18213929) B18213929
theorem B72812783 : Blo 1576486 72812783 := bstep (se 1 (by rfl) ⟨54609587, by rfl⟩ : syracuseStep 72812783 = 109219175) B109219175
theorem B17066315 : Blo 1576486 17066315 := bstep (se 1 (by rfl) ⟨12799736, by rfl⟩ : syracuseStep 17066315 = 25599473) B25599473
theorem B5122559 : Blo 1576486 5122559 := bstep (se 1 (by rfl) ⟨3841919, by rfl⟩ : syracuseStep 5122559 = 7683839) B7683839
theorem B3550121 : Blo 1576486 3550121 := bstep (se 2 (by rfl) ⟨1331295, by rfl⟩ : syracuseStep 3550121 = 2662591) B2662591
theorem B38898863 : Blo 1576486 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B1576807 : Blo 1576486 1576807 := bstep (se 1 (by rfl) ⟨1182605, by rfl⟩ : syracuseStep 1576807 = 2365211) B2365211
theorem B140169179 : Blo 1576486 140169179 := bstep (se 1 (by rfl) ⟨105126884, by rfl⟩ : syracuseStep 140169179 = 210253769) B210253769
theorem B1576991 : Blo 1576486 1576991 := bstep (se 1 (by rfl) ⟨1182743, by rfl⟩ : syracuseStep 1576991 = 2365487) B2365487
theorem B43177121 : Blo 1576486 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B2365055 : Blo 1576486 2365055 := bstep (se 1 (by rfl) ⟨1773791, by rfl⟩ : syracuseStep 2365055 = 3547583) B3547583
theorem B2365097 : Blo 1576486 2365097 := bstep (se 2 (by rfl) ⟨886911, by rfl⟩ : syracuseStep 2365097 = 1773823) B1773823
theorem B10107119 : Blo 1576486 10107119 := bstep (se 1 (by rfl) ⟨7580339, by rfl⟩ : syracuseStep 10107119 = 15160679) B15160679
theorem B2365919 : Blo 1576486 2365919 := bstep (se 1 (by rfl) ⟨1774439, by rfl⟩ : syracuseStep 2365919 = 3548879) B3548879
theorem B5323859 : Blo 1576486 5323859 := bstep (se 1 (by rfl) ⟨3992894, by rfl⟩ : syracuseStep 5323859 = 7985789) B7985789
theorem B5324345 : Blo 1576486 5324345 := bstep (se 2 (by rfl) ⟨1996629, by rfl⟩ : syracuseStep 5324345 = 3993259) B3993259
theorem B9109727 : Blo 1576486 9109727 := bstep (se 1 (by rfl) ⟨6832295, by rfl⟩ : syracuseStep 9109727 = 13664591) B13664591
theorem B8095079 : Blo 1576486 8095079 := bstep (se 1 (by rfl) ⟨6071309, by rfl⟩ : syracuseStep 8095079 = 12142619) B12142619
theorem B3549239 : Blo 1576486 3549239 := bstep (se 1 (by rfl) ⟨2661929, by rfl⟩ : syracuseStep 3549239 = 5323859) B5323859
theorem B3549563 : Blo 1576486 3549563 := bstep (se 1 (by rfl) ⟨2662172, by rfl⟩ : syracuseStep 3549563 = 5324345) B5324345
theorem B45510173 : Blo 1576486 45510173 := bstep (se 3 (by rfl) ⟨8533157, by rfl⟩ : syracuseStep 45510173 = 17066315) B17066315
theorem B1576703 : Blo 1576486 1576703 := bstep (se 1 (by rfl) ⟨1182527, by rfl⟩ : syracuseStep 1576703 = 2365055) B2365055
theorem B1576731 : Blo 1576486 1576731 := bstep (se 1 (by rfl) ⟨1182548, by rfl⟩ : syracuseStep 1576731 = 2365097) B2365097
theorem B48541855 : Blo 1576486 48541855 := bstep (se 1 (by rfl) ⟨36406391, by rfl⟩ : syracuseStep 48541855 = 72812783) B72812783
theorem B6738079 : Blo 1576486 6738079 := bstep (se 1 (by rfl) ⟨5053559, by rfl⟩ : syracuseStep 6738079 = 10107119) B10107119
theorem B1577279 : Blo 1576486 1577279 := bstep (se 1 (by rfl) ⟨1182959, by rfl⟩ : syracuseStep 1577279 = 2365919) B2365919
theorem B5321321 : Blo 1576486 5321321 := bstep (se 2 (by rfl) ⟨1995495, by rfl⟩ : syracuseStep 5321321 = 3990991) B3990991
theorem B25932575 : Blo 1576486 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B1578399 : Blo 1576486 1578399 := bstep (se 1 (by rfl) ⟨1183799, by rfl⟩ : syracuseStep 1578399 = 2367599) B2367599
theorem B31135423 : Blo 1576486 31135423 := bstep (se 1 (by rfl) ⟨23351567, by rfl⟩ : syracuseStep 31135423 = 46703135) B46703135
theorem B28784747 : Blo 1576486 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B3415039 : Blo 1576486 3415039 := bstep (se 1 (by rfl) ⟨2561279, by rfl⟩ : syracuseStep 3415039 = 5122559) B5122559
theorem B2366747 : Blo 1576486 2366747 := bstep (se 1 (by rfl) ⟨1775060, by rfl⟩ : syracuseStep 2366747 = 3550121) B3550121
theorem B93446119 : Blo 1576486 93446119 := bstep (se 1 (by rfl) ⟨70084589, by rfl⟩ : syracuseStep 93446119 = 140169179) B140169179
theorem B76759325 : Blo 1576486 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B3547547 : Blo 1576486 3547547 := bstep (se 1 (by rfl) ⟨2660660, by rfl⟩ : syracuseStep 3547547 = 5321321) B5321321
theorem B498379301 : Blo 1576486 498379301 := bstep (se 4 (by rfl) ⟨46723059, by rfl⟩ : syracuseStep 498379301 = 93446119) B93446119
theorem B18213541 : Blo 1576486 18213541 := bstep (se 4 (by rfl) ⟨1707519, by rfl⟩ : syracuseStep 18213541 = 3415039) B3415039
theorem B6073151 : Blo 1576486 6073151 := bstep (se 1 (by rfl) ⟨4554863, by rfl⟩ : syracuseStep 6073151 = 9109727) B9109727
theorem B69153533 : Blo 1576486 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B1577831 : Blo 1576486 1577831 := bstep (se 1 (by rfl) ⟨1183373, by rfl⟩ : syracuseStep 1577831 = 2366747) B2366747
theorem B41513897 : Blo 1576486 41513897 := bstep (se 2 (by rfl) ⟨15567711, by rfl⟩ : syracuseStep 41513897 = 31135423) B31135423
theorem B30340115 : Blo 1576486 30340115 := bstep (se 1 (by rfl) ⟨22755086, by rfl⟩ : syracuseStep 30340115 = 45510173) B45510173
theorem B64722473 : Blo 1576486 64722473 := bstep (se 2 (by rfl) ⟨24270927, by rfl⟩ : syracuseStep 64722473 = 48541855) B48541855
theorem B8984105 : Blo 1576486 8984105 := bstep (se 2 (by rfl) ⟨3369039, by rfl⟩ : syracuseStep 8984105 = 6738079) B6738079
theorem B5396719 : Blo 1576486 5396719 := bstep (se 1 (by rfl) ⟨4047539, by rfl⟩ : syracuseStep 5396719 = 8095079) B8095079
theorem B2366159 : Blo 1576486 2366159 := bstep (se 1 (by rfl) ⟨1774619, by rfl⟩ : syracuseStep 2366159 = 3549239) B3549239
theorem B2366375 : Blo 1576486 2366375 := bstep (se 1 (by rfl) ⟨1774781, by rfl⟩ : syracuseStep 2366375 = 3549563) B3549563
theorem B20226743 : Blo 1576486 20226743 := bstep (se 1 (by rfl) ⟨15170057, by rfl⟩ : syracuseStep 20226743 = 30340115) B30340115
theorem B43148315 : Blo 1576486 43148315 := bstep (se 1 (by rfl) ⟨32361236, by rfl⟩ : syracuseStep 43148315 = 64722473) B64722473
theorem B5989403 : Blo 1576486 5989403 := bstep (se 1 (by rfl) ⟨4492052, by rfl⟩ : syracuseStep 5989403 = 8984105) B8984105
theorem B332252867 : Blo 1576486 332252867 := bstep (se 1 (by rfl) ⟨249189650, by rfl⟩ : syracuseStep 332252867 = 498379301) B498379301
theorem B7195625 : Blo 1576486 7195625 := bstep (se 2 (by rfl) ⟨2698359, by rfl⟩ : syracuseStep 7195625 = 5396719) B5396719
theorem B27675931 : Blo 1576486 27675931 := bstep (se 1 (by rfl) ⟨20756948, by rfl⟩ : syracuseStep 27675931 = 41513897) B41513897
theorem B1577439 : Blo 1576486 1577439 := bstep (se 1 (by rfl) ⟨1183079, by rfl⟩ : syracuseStep 1577439 = 2366159) B2366159
theorem B1577583 : Blo 1576486 1577583 := bstep (se 1 (by rfl) ⟨1183187, by rfl⟩ : syracuseStep 1577583 = 2366375) B2366375
theorem B51172883 : Blo 1576486 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B2365031 : Blo 1576486 2365031 := bstep (se 1 (by rfl) ⟨1773773, by rfl⟩ : syracuseStep 2365031 = 3547547) B3547547
theorem B46102355 : Blo 1576486 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B97138885 : Blo 1576486 97138885 := bstep (se 4 (by rfl) ⟨9106770, by rfl⟩ : syracuseStep 97138885 = 18213541) B18213541
theorem B16195069 : Blo 1576486 16195069 := bstep (se 3 (by rfl) ⟨3036575, by rfl⟩ : syracuseStep 16195069 = 6073151) B6073151
theorem B13484495 : Blo 1576486 13484495 := bstep (se 1 (by rfl) ⟨10113371, by rfl⟩ : syracuseStep 13484495 = 20226743) B20226743
theorem B886007645 : Blo 1576486 886007645 := bstep (se 3 (by rfl) ⟨166126433, by rfl⟩ : syracuseStep 886007645 = 332252867) B332252867
theorem B129518513 : Blo 1576486 129518513 := bstep (se 2 (by rfl) ⟨48569442, by rfl⟩ : syracuseStep 129518513 = 97138885) B97138885
theorem B28765543 : Blo 1576486 28765543 := bstep (se 1 (by rfl) ⟨21574157, by rfl⟩ : syracuseStep 28765543 = 43148315) B43148315
theorem B3992935 : Blo 1576486 3992935 := bstep (se 1 (by rfl) ⟨2994701, by rfl⟩ : syracuseStep 3992935 = 5989403) B5989403
theorem B34115255 : Blo 1576486 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B1576687 : Blo 1576486 1576687 := bstep (se 1 (by rfl) ⟨1182515, by rfl⟩ : syracuseStep 1576687 = 2365031) B2365031
theorem B36901241 : Blo 1576486 36901241 := bstep (se 2 (by rfl) ⟨13837965, by rfl⟩ : syracuseStep 36901241 = 27675931) B27675931
theorem B4797083 : Blo 1576486 4797083 := bstep (se 1 (by rfl) ⟨3597812, by rfl⟩ : syracuseStep 4797083 = 7195625) B7195625
theorem B30734903 : Blo 1576486 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B21593425 : Blo 1576486 21593425 := bstep (se 2 (by rfl) ⟨8097534, by rfl⟩ : syracuseStep 21593425 = 16195069) B16195069
theorem B24600827 : Blo 1576486 24600827 := bstep (se 1 (by rfl) ⟨18450620, by rfl⟩ : syracuseStep 24600827 = 36901241) B36901241
theorem B20489935 : Blo 1576486 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B86345675 : Blo 1576486 86345675 := bstep (se 1 (by rfl) ⟨64759256, by rfl⟩ : syracuseStep 86345675 = 129518513) B129518513
theorem B22743503 : Blo 1576486 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B8989663 : Blo 1576486 8989663 := bstep (se 1 (by rfl) ⟨6742247, by rfl⟩ : syracuseStep 8989663 = 13484495) B13484495
theorem B3198055 : Blo 1576486 3198055 := bstep (se 1 (by rfl) ⟨2398541, by rfl⟩ : syracuseStep 3198055 = 4797083) B4797083
theorem B590671763 : Blo 1576486 590671763 := bstep (se 1 (by rfl) ⟨443003822, by rfl⟩ : syracuseStep 590671763 = 886007645) B886007645
theorem B28791233 : Blo 1576486 28791233 := bstep (se 2 (by rfl) ⟨10796712, by rfl⟩ : syracuseStep 28791233 = 21593425) B21593425
theorem B38354057 : Blo 1576486 38354057 := bstep (se 2 (by rfl) ⟨14382771, by rfl⟩ : syracuseStep 38354057 = 28765543) B28765543
theorem B5323913 : Blo 1576486 5323913 := bstep (se 2 (by rfl) ⟨1996467, by rfl⟩ : syracuseStep 5323913 = 3992935) B3992935
theorem B16400551 : Blo 1576486 16400551 := bstep (se 1 (by rfl) ⟨12300413, by rfl⟩ : syracuseStep 16400551 = 24600827) B24600827
theorem B19194155 : Blo 1576486 19194155 := bstep (se 1 (by rfl) ⟨14395616, by rfl⟩ : syracuseStep 19194155 = 28791233) B28791233
theorem B11986217 : Blo 1576486 11986217 := bstep (se 2 (by rfl) ⟨4494831, by rfl⟩ : syracuseStep 11986217 = 8989663) B8989663
theorem B25569371 : Blo 1576486 25569371 := bstep (se 1 (by rfl) ⟨19177028, by rfl⟩ : syracuseStep 25569371 = 38354057) B38354057
theorem B3549275 : Blo 1576486 3549275 := bstep (se 1 (by rfl) ⟨2661956, by rfl⟩ : syracuseStep 3549275 = 5323913) B5323913
theorem B4264073 : Blo 1576486 4264073 := bstep (se 2 (by rfl) ⟨1599027, by rfl⟩ : syracuseStep 4264073 = 3198055) B3198055
theorem B57563783 : Blo 1576486 57563783 := bstep (se 1 (by rfl) ⟨43172837, by rfl⟩ : syracuseStep 57563783 = 86345675) B86345675
theorem B15162335 : Blo 1576486 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B27319913 : Blo 1576486 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B393781175 : Blo 1576486 393781175 := bstep (se 1 (by rfl) ⟨295335881, by rfl⟩ : syracuseStep 393781175 = 590671763) B590671763
theorem B2842715 : Blo 1576486 2842715 := bstep (se 1 (by rfl) ⟨2132036, by rfl⟩ : syracuseStep 2842715 = 4264073) B4264073
theorem B12796103 : Blo 1576486 12796103 := bstep (se 1 (by rfl) ⟨9597077, by rfl⟩ : syracuseStep 12796103 = 19194155) B19194155
theorem B18213275 : Blo 1576486 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B21867401 : Blo 1576486 21867401 := bstep (se 2 (by rfl) ⟨8200275, by rfl⟩ : syracuseStep 21867401 = 16400551) B16400551
theorem B68184989 : Blo 1576486 68184989 := bstep (se 3 (by rfl) ⟨12784685, by rfl⟩ : syracuseStep 68184989 = 25569371) B25569371
theorem B7990811 : Blo 1576486 7990811 := bstep (se 1 (by rfl) ⟨5993108, by rfl⟩ : syracuseStep 7990811 = 11986217) B11986217
theorem B38375855 : Blo 1576486 38375855 := bstep (se 1 (by rfl) ⟨28781891, by rfl⟩ : syracuseStep 38375855 = 57563783) B57563783
theorem B2366183 : Blo 1576486 2366183 := bstep (se 1 (by rfl) ⟨1774637, by rfl⟩ : syracuseStep 2366183 = 3549275) B3549275
theorem B10108223 : Blo 1576486 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B262520783 : Blo 1576486 262520783 := bstep (se 1 (by rfl) ⟨196890587, by rfl⟩ : syracuseStep 262520783 = 393781175) B393781175
theorem B25583903 : Blo 1576486 25583903 := bstep (se 1 (by rfl) ⟨19187927, by rfl⟩ : syracuseStep 25583903 = 38375855) B38375855
theorem B12142183 : Blo 1576486 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B5327207 : Blo 1576486 5327207 := bstep (se 1 (by rfl) ⟨3995405, by rfl⟩ : syracuseStep 5327207 = 7990811) B7990811
theorem B1895143 : Blo 1576486 1895143 := bstep (se 1 (by rfl) ⟨1421357, by rfl⟩ : syracuseStep 1895143 = 2842715) B2842715
theorem B34122941 : Blo 1576486 34122941 := bstep (se 3 (by rfl) ⟨6398051, by rfl⟩ : syracuseStep 34122941 = 12796103) B12796103
theorem B1577455 : Blo 1576486 1577455 := bstep (se 1 (by rfl) ⟨1183091, by rfl⟩ : syracuseStep 1577455 = 2366183) B2366183
theorem B14578267 : Blo 1576486 14578267 := bstep (se 1 (by rfl) ⟨10933700, by rfl⟩ : syracuseStep 14578267 = 21867401) B21867401
theorem B6738815 : Blo 1576486 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B45456659 : Blo 1576486 45456659 := bstep (se 1 (by rfl) ⟨34092494, by rfl⟩ : syracuseStep 45456659 = 68184989) B68184989
theorem B175013855 : Blo 1576486 175013855 := bstep (se 1 (by rfl) ⟨131260391, by rfl⟩ : syracuseStep 175013855 = 262520783) B262520783
theorem B17055935 : Blo 1576486 17055935 := bstep (se 1 (by rfl) ⟨12791951, by rfl⟩ : syracuseStep 17055935 = 25583903) B25583903
theorem B16189577 : Blo 1576486 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B30304439 : Blo 1576486 30304439 := bstep (se 1 (by rfl) ⟨22728329, by rfl⟩ : syracuseStep 30304439 = 45456659) B45456659
theorem B4492543 : Blo 1576486 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B2526857 : Blo 1576486 2526857 := bstep (se 2 (by rfl) ⟨947571, by rfl⟩ : syracuseStep 2526857 = 1895143) B1895143
theorem B3551471 : Blo 1576486 3551471 := bstep (se 1 (by rfl) ⟨2663603, by rfl⟩ : syracuseStep 3551471 = 5327207) B5327207
theorem B116675903 : Blo 1576486 116675903 := bstep (se 1 (by rfl) ⟨87506927, by rfl⟩ : syracuseStep 116675903 = 175013855) B175013855
theorem B19437689 : Blo 1576486 19437689 := bstep (se 2 (by rfl) ⟨7289133, by rfl⟩ : syracuseStep 19437689 = 14578267) B14578267
theorem B22748627 : Blo 1576486 22748627 := bstep (se 1 (by rfl) ⟨17061470, by rfl⟩ : syracuseStep 22748627 = 34122941) B34122941
theorem B11370623 : Blo 1576486 11370623 := bstep (se 1 (by rfl) ⟨8527967, by rfl⟩ : syracuseStep 11370623 = 17055935) B17055935
theorem B2367647 : Blo 1576486 2367647 := bstep (se 1 (by rfl) ⟨1775735, by rfl⟩ : syracuseStep 2367647 = 3551471) B3551471
theorem B77783935 : Blo 1576486 77783935 := bstep (se 1 (by rfl) ⟨58337951, by rfl⟩ : syracuseStep 77783935 = 116675903) B116675903
theorem B60663005 : Blo 1576486 60663005 := bstep (se 3 (by rfl) ⟨11374313, by rfl⟩ : syracuseStep 60663005 = 22748627) B22748627
theorem B20202959 : Blo 1576486 20202959 := bstep (se 1 (by rfl) ⟨15152219, by rfl⟩ : syracuseStep 20202959 = 30304439) B30304439
theorem B5990057 : Blo 1576486 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B51833837 : Blo 1576486 51833837 := bstep (se 3 (by rfl) ⟨9718844, by rfl⟩ : syracuseStep 51833837 = 19437689) B19437689
theorem B10793051 : Blo 1576486 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B1684571 : Blo 1576486 1684571 := bstep (se 1 (by rfl) ⟨1263428, by rfl⟩ : syracuseStep 1684571 = 2526857) B2526857
theorem B13468639 : Blo 1576486 13468639 := bstep (se 1 (by rfl) ⟨10101479, by rfl⟩ : syracuseStep 13468639 = 20202959) B20202959
theorem B103711913 : Blo 1576486 103711913 := bstep (se 2 (by rfl) ⟨38891967, by rfl⟩ : syracuseStep 103711913 = 77783935) B77783935
theorem B34555891 : Blo 1576486 34555891 := bstep (se 1 (by rfl) ⟨25916918, by rfl⟩ : syracuseStep 34555891 = 51833837) B51833837
theorem B7195367 : Blo 1576486 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B4492189 : Blo 1576486 4492189 := bstep (se 3 (by rfl) ⟨842285, by rfl⟩ : syracuseStep 4492189 = 1684571) B1684571
theorem B30321661 : Blo 1576486 30321661 := bstep (se 3 (by rfl) ⟨5685311, by rfl⟩ : syracuseStep 30321661 = 11370623) B11370623
theorem B3993371 : Blo 1576486 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B1578431 : Blo 1576486 1578431 := bstep (se 1 (by rfl) ⟨1183823, by rfl⟩ : syracuseStep 1578431 = 2367647) B2367647
theorem B40442003 : Blo 1576486 40442003 := bstep (se 1 (by rfl) ⟨30331502, by rfl⟩ : syracuseStep 40442003 = 60663005) B60663005
theorem B69141275 : Blo 1576486 69141275 := bstep (se 1 (by rfl) ⟨51855956, by rfl⟩ : syracuseStep 69141275 = 103711913) B103711913
theorem B5989585 : Blo 1576486 5989585 := bstep (se 2 (by rfl) ⟨2246094, by rfl⟩ : syracuseStep 5989585 = 4492189) B4492189
theorem B17958185 : Blo 1576486 17958185 := bstep (se 2 (by rfl) ⟨6734319, by rfl⟩ : syracuseStep 17958185 = 13468639) B13468639
theorem B40428881 : Blo 1576486 40428881 := bstep (se 2 (by rfl) ⟨15160830, by rfl⟩ : syracuseStep 40428881 = 30321661) B30321661
theorem B26961335 : Blo 1576486 26961335 := bstep (se 1 (by rfl) ⟨20221001, by rfl⟩ : syracuseStep 26961335 = 40442003) B40442003
theorem B46074521 : Blo 1576486 46074521 := bstep (se 2 (by rfl) ⟨17277945, by rfl⟩ : syracuseStep 46074521 = 34555891) B34555891
theorem B4796911 : Blo 1576486 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B2662247 : Blo 1576486 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B26952587 : Blo 1576486 26952587 := bstep (se 1 (by rfl) ⟨20214440, by rfl⟩ : syracuseStep 26952587 = 40428881) B40428881
theorem B17974223 : Blo 1576486 17974223 := bstep (se 1 (by rfl) ⟨13480667, by rfl⟩ : syracuseStep 17974223 = 26961335) B26961335
theorem B11972123 : Blo 1576486 11972123 := bstep (se 1 (by rfl) ⟨8979092, by rfl⟩ : syracuseStep 11972123 = 17958185) B17958185
theorem B30716347 : Blo 1576486 30716347 := bstep (se 1 (by rfl) ⟨23037260, by rfl⟩ : syracuseStep 30716347 = 46074521) B46074521
theorem B1774831 : Blo 1576486 1774831 := bstep (se 1 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 1774831 = 2662247) B2662247
theorem B46094183 : Blo 1576486 46094183 := bstep (se 1 (by rfl) ⟨34570637, by rfl⟩ : syracuseStep 46094183 = 69141275) B69141275
theorem B7986113 : Blo 1576486 7986113 := bstep (se 2 (by rfl) ⟨2994792, by rfl⟩ : syracuseStep 7986113 = 5989585) B5989585
theorem B25583525 : Blo 1576486 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B30729455 : Blo 1576486 30729455 := bstep (se 1 (by rfl) ⟨23047091, by rfl⟩ : syracuseStep 30729455 = 46094183) B46094183
theorem B7981415 : Blo 1576486 7981415 := bstep (se 1 (by rfl) ⟨5986061, by rfl⟩ : syracuseStep 7981415 = 11972123) B11972123
theorem B40955129 : Blo 1576486 40955129 := bstep (se 2 (by rfl) ⟨15358173, by rfl⟩ : syracuseStep 40955129 = 30716347) B30716347
theorem B17968391 : Blo 1576486 17968391 := bstep (se 1 (by rfl) ⟨13476293, by rfl⟩ : syracuseStep 17968391 = 26952587) B26952587
theorem B11982815 : Blo 1576486 11982815 := bstep (se 1 (by rfl) ⟨8987111, by rfl⟩ : syracuseStep 11982815 = 17974223) B17974223
theorem B2366441 : Blo 1576486 2366441 := bstep (se 2 (by rfl) ⟨887415, by rfl⟩ : syracuseStep 2366441 = 1774831) B1774831
theorem B5324075 : Blo 1576486 5324075 := bstep (se 1 (by rfl) ⟨3993056, by rfl⟩ : syracuseStep 5324075 = 7986113) B7986113
theorem B17055683 : Blo 1576486 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B7988543 : Blo 1576486 7988543 := bstep (se 1 (by rfl) ⟨5991407, by rfl⟩ : syracuseStep 7988543 = 11982815) B11982815
theorem B11978927 : Blo 1576486 11978927 := bstep (se 1 (by rfl) ⟨8984195, by rfl⟩ : syracuseStep 11978927 = 17968391) B17968391
theorem B3549383 : Blo 1576486 3549383 := bstep (se 1 (by rfl) ⟨2662037, by rfl⟩ : syracuseStep 3549383 = 5324075) B5324075
theorem B5320943 : Blo 1576486 5320943 := bstep (se 1 (by rfl) ⟨3990707, by rfl⟩ : syracuseStep 5320943 = 7981415) B7981415
theorem B1577627 : Blo 1576486 1577627 := bstep (se 1 (by rfl) ⟨1183220, by rfl⟩ : syracuseStep 1577627 = 2366441) B2366441
theorem B20486303 : Blo 1576486 20486303 := bstep (se 1 (by rfl) ⟨15364727, by rfl⟩ : syracuseStep 20486303 = 30729455) B30729455
theorem B27303419 : Blo 1576486 27303419 := bstep (se 1 (by rfl) ⟨20477564, by rfl⟩ : syracuseStep 27303419 = 40955129) B40955129
theorem B11370455 : Blo 1576486 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B3547295 : Blo 1576486 3547295 := bstep (se 1 (by rfl) ⟨2660471, by rfl⟩ : syracuseStep 3547295 = 5320943) B5320943
theorem B5325695 : Blo 1576486 5325695 := bstep (se 1 (by rfl) ⟨3994271, by rfl⟩ : syracuseStep 5325695 = 7988543) B7988543
theorem B13657535 : Blo 1576486 13657535 := bstep (se 1 (by rfl) ⟨10243151, by rfl⟩ : syracuseStep 13657535 = 20486303) B20486303
theorem B7580303 : Blo 1576486 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B7985951 : Blo 1576486 7985951 := bstep (se 1 (by rfl) ⟨5989463, by rfl⟩ : syracuseStep 7985951 = 11978927) B11978927
theorem B2366255 : Blo 1576486 2366255 := bstep (se 1 (by rfl) ⟨1774691, by rfl⟩ : syracuseStep 2366255 = 3549383) B3549383
theorem B18202279 : Blo 1576486 18202279 := bstep (se 1 (by rfl) ⟨13651709, by rfl⟩ : syracuseStep 18202279 = 27303419) B27303419
theorem B3550463 : Blo 1576486 3550463 := bstep (se 1 (by rfl) ⟨2662847, by rfl⟩ : syracuseStep 3550463 = 5325695) B5325695
theorem B9105023 : Blo 1576486 9105023 := bstep (se 1 (by rfl) ⟨6828767, by rfl⟩ : syracuseStep 9105023 = 13657535) B13657535
theorem B1577503 : Blo 1576486 1577503 := bstep (se 1 (by rfl) ⟨1183127, by rfl⟩ : syracuseStep 1577503 = 2366255) B2366255
theorem B24269705 : Blo 1576486 24269705 := bstep (se 2 (by rfl) ⟨9101139, by rfl⟩ : syracuseStep 24269705 = 18202279) B18202279
theorem B2364863 : Blo 1576486 2364863 := bstep (se 1 (by rfl) ⟨1773647, by rfl⟩ : syracuseStep 2364863 = 3547295) B3547295
theorem B5053535 : Blo 1576486 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B5323967 : Blo 1576486 5323967 := bstep (se 1 (by rfl) ⟨3992975, by rfl⟩ : syracuseStep 5323967 = 7985951) B7985951
theorem B16179803 : Blo 1576486 16179803 := bstep (se 1 (by rfl) ⟨12134852, by rfl⟩ : syracuseStep 16179803 = 24269705) B24269705
theorem B3369023 : Blo 1576486 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B3549311 : Blo 1576486 3549311 := bstep (se 1 (by rfl) ⟨2661983, by rfl⟩ : syracuseStep 3549311 = 5323967) B5323967
theorem B1576575 : Blo 1576486 1576575 := bstep (se 1 (by rfl) ⟨1182431, by rfl⟩ : syracuseStep 1576575 = 2364863) B2364863
theorem B2366975 : Blo 1576486 2366975 := bstep (se 1 (by rfl) ⟨1775231, by rfl⟩ : syracuseStep 2366975 = 3550463) B3550463
theorem B6070015 : Blo 1576486 6070015 := bstep (se 1 (by rfl) ⟨4552511, by rfl⟩ : syracuseStep 6070015 = 9105023) B9105023
theorem B2246015 : Blo 1576486 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B1577983 : Blo 1576486 1577983 := bstep (se 1 (by rfl) ⟨1183487, by rfl⟩ : syracuseStep 1577983 = 2366975) B2366975
theorem B10786535 : Blo 1576486 10786535 := bstep (se 1 (by rfl) ⟨8089901, by rfl⟩ : syracuseStep 10786535 = 16179803) B16179803
theorem B2366207 : Blo 1576486 2366207 := bstep (se 1 (by rfl) ⟨1774655, by rfl⟩ : syracuseStep 2366207 = 3549311) B3549311
theorem B8093353 : Blo 1576486 8093353 := bstep (se 2 (by rfl) ⟨3035007, by rfl⟩ : syracuseStep 8093353 = 6070015) B6070015
theorem B5989373 : Blo 1576486 5989373 := bstep (se 3 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 5989373 = 2246015) B2246015
theorem B10791137 : Blo 1576486 10791137 := bstep (se 2 (by rfl) ⟨4046676, by rfl⟩ : syracuseStep 10791137 = 8093353) B8093353
theorem B1577471 : Blo 1576486 1577471 := bstep (se 1 (by rfl) ⟨1183103, by rfl⟩ : syracuseStep 1577471 = 2366207) B2366207
theorem B7191023 : Blo 1576486 7191023 := bstep (se 1 (by rfl) ⟨5393267, by rfl⟩ : syracuseStep 7191023 = 10786535) B10786535
theorem B7194091 : Blo 1576486 7194091 := bstep (se 1 (by rfl) ⟨5395568, by rfl⟩ : syracuseStep 7194091 = 10791137) B10791137
theorem B3992915 : Blo 1576486 3992915 := bstep (se 1 (by rfl) ⟨2994686, by rfl⟩ : syracuseStep 3992915 = 5989373) B5989373
theorem B19176061 : Blo 1576486 19176061 := bstep (se 3 (by rfl) ⟨3595511, by rfl⟩ : syracuseStep 19176061 = 7191023) B7191023
theorem B25568081 : Blo 1576486 25568081 := bstep (se 2 (by rfl) ⟨9588030, by rfl⟩ : syracuseStep 25568081 = 19176061) B19176061
theorem B9592121 : Blo 1576486 9592121 := bstep (se 2 (by rfl) ⟨3597045, by rfl⟩ : syracuseStep 9592121 = 7194091) B7194091
theorem B2661943 : Blo 1576486 2661943 := bstep (se 1 (by rfl) ⟨1996457, by rfl⟩ : syracuseStep 2661943 = 3992915) B3992915
theorem B3549257 : Blo 1576486 3549257 := bstep (se 2 (by rfl) ⟨1330971, by rfl⟩ : syracuseStep 3549257 = 2661943) B2661943
theorem B6394747 : Blo 1576486 6394747 := bstep (se 1 (by rfl) ⟨4796060, by rfl⟩ : syracuseStep 6394747 = 9592121) B9592121
theorem B17045387 : Blo 1576486 17045387 := bstep (se 1 (by rfl) ⟨12784040, by rfl⟩ : syracuseStep 17045387 = 25568081) B25568081
theorem B11363591 : Blo 1576486 11363591 := bstep (se 1 (by rfl) ⟨8522693, by rfl⟩ : syracuseStep 11363591 = 17045387) B17045387
theorem B8526329 : Blo 1576486 8526329 := bstep (se 2 (by rfl) ⟨3197373, by rfl⟩ : syracuseStep 8526329 = 6394747) B6394747
theorem B2366171 : Blo 1576486 2366171 := bstep (se 1 (by rfl) ⟨1774628, by rfl⟩ : syracuseStep 2366171 = 3549257) B3549257
theorem B1577447 : Blo 1576486 1577447 := bstep (se 1 (by rfl) ⟨1183085, by rfl⟩ : syracuseStep 1577447 = 2366171) B2366171
theorem B7575727 : Blo 1576486 7575727 := bstep (se 1 (by rfl) ⟨5681795, by rfl⟩ : syracuseStep 7575727 = 11363591) B11363591
theorem B5684219 : Blo 1576486 5684219 := bstep (se 1 (by rfl) ⟨4263164, by rfl⟩ : syracuseStep 5684219 = 8526329) B8526329
theorem B10100969 : Blo 1576486 10100969 := bstep (se 2 (by rfl) ⟨3787863, by rfl⟩ : syracuseStep 10100969 = 7575727) B7575727
theorem B3789479 : Blo 1576486 3789479 := bstep (se 1 (by rfl) ⟨2842109, by rfl⟩ : syracuseStep 3789479 = 5684219) B5684219
theorem B6733979 : Blo 1576486 6733979 := bstep (se 1 (by rfl) ⟨5050484, by rfl⟩ : syracuseStep 6733979 = 10100969) B10100969
theorem B2526319 : Blo 1576486 2526319 := bstep (se 1 (by rfl) ⟨1894739, by rfl⟩ : syracuseStep 2526319 = 3789479) B3789479
theorem B4489319 : Blo 1576486 4489319 := bstep (se 1 (by rfl) ⟨3366989, by rfl⟩ : syracuseStep 4489319 = 6733979) B6733979
theorem B3368425 : Blo 1576486 3368425 := bstep (se 2 (by rfl) ⟨1263159, by rfl⟩ : syracuseStep 3368425 = 2526319) B2526319
theorem B4491233 : Blo 1576486 4491233 := bstep (se 2 (by rfl) ⟨1684212, by rfl⟩ : syracuseStep 4491233 = 3368425) B3368425
theorem B2992879 : Blo 1576486 2992879 := bstep (se 1 (by rfl) ⟨2244659, by rfl⟩ : syracuseStep 2992879 = 4489319) B4489319
theorem B3990505 : Blo 1576486 3990505 := bstep (se 2 (by rfl) ⟨1496439, by rfl⟩ : syracuseStep 3990505 = 2992879) B2992879
theorem B2994155 : Blo 1576486 2994155 := bstep (se 1 (by rfl) ⟨2245616, by rfl⟩ : syracuseStep 2994155 = 4491233) B4491233
theorem B5320673 : Blo 1576486 5320673 := bstep (se 2 (by rfl) ⟨1995252, by rfl⟩ : syracuseStep 5320673 = 3990505) B3990505
theorem B1996103 : Blo 1576486 1996103 := bstep (se 1 (by rfl) ⟨1497077, by rfl⟩ : syracuseStep 1996103 = 2994155) B2994155
theorem B5322941 : Blo 1576486 5322941 := bstep (se 3 (by rfl) ⟨998051, by rfl⟩ : syracuseStep 5322941 = 1996103) B1996103
theorem B3547115 : Blo 1576486 3547115 := bstep (se 1 (by rfl) ⟨2660336, by rfl⟩ : syracuseStep 3547115 = 5320673) B5320673
theorem B3548627 : Blo 1576486 3548627 := bstep (se 1 (by rfl) ⟨2661470, by rfl⟩ : syracuseStep 3548627 = 5322941) B5322941
theorem B2364743 : Blo 1576486 2364743 := bstep (se 1 (by rfl) ⟨1773557, by rfl⟩ : syracuseStep 2364743 = 3547115) B3547115
theorem B1576495 : Blo 1576486 1576495 := bstep (se 1 (by rfl) ⟨1182371, by rfl⟩ : syracuseStep 1576495 = 2364743) B2364743
theorem B2365751 : Blo 1576486 2365751 := bstep (se 1 (by rfl) ⟨1774313, by rfl⟩ : syracuseStep 2365751 = 3548627) B3548627
theorem B1577167 : Blo 1576486 1577167 := bstep (se 1 (by rfl) ⟨1182875, by rfl⟩ : syracuseStep 1577167 = 2365751) B2365751

theorem C0 (j : ℕ) (h1 : 394121 ≤ j) (h2 : j ≤ 394620) : Blo 1576486 (4 * j + 3) := by
  interval_cases j
  · exact B1576487
  · exact B1576491
  · exact B1576495
  · exact B1576499
  · exact B1576503
  · exact B1576507
  · exact B1576511
  · exact B1576515
  · exact B1576519
  · exact B1576523
  · exact B1576527
  · exact B1576531
  · exact B1576535
  · exact B1576539
  · exact B1576543
  · exact B1576547
  · exact B1576551
  · exact B1576555
  · exact B1576559
  · exact B1576563
  · exact B1576567
  · exact B1576571
  · exact B1576575
  · exact B1576579
  · exact B1576583
  · exact B1576587
  · exact B1576591
  · exact B1576595
  · exact B1576599
  · exact B1576603
  · exact B1576607
  · exact B1576611
  · exact B1576615
  · exact B1576619
  · exact B1576623
  · exact B1576627
  · exact B1576631
  · exact B1576635
  · exact B1576639
  · exact B1576643
  · exact B1576647
  · exact B1576651
  · exact B1576655
  · exact B1576659
  · exact B1576663
  · exact B1576667
  · exact B1576671
  · exact B1576675
  · exact B1576679
  · exact B1576683
  · exact B1576687
  · exact B1576691
  · exact B1576695
  · exact B1576699
  · exact B1576703
  · exact B1576707
  · exact B1576711
  · exact B1576715
  · exact B1576719
  · exact B1576723
  · exact B1576727
  · exact B1576731
  · exact B1576735
  · exact B1576739
  · exact B1576743
  · exact B1576747
  · exact B1576751
  · exact B1576755
  · exact B1576759
  · exact B1576763
  · exact B1576767
  · exact B1576771
  · exact B1576775
  · exact B1576779
  · exact B1576783
  · exact B1576787
  · exact B1576791
  · exact B1576795
  · exact B1576799
  · exact B1576803
  · exact B1576807
  · exact B1576811
  · exact B1576815
  · exact B1576819
  · exact B1576823
  · exact B1576827
  · exact B1576831
  · exact B1576835
  · exact B1576839
  · exact B1576843
  · exact B1576847
  · exact B1576851
  · exact B1576855
  · exact B1576859
  · exact B1576863
  · exact B1576867
  · exact B1576871
  · exact B1576875
  · exact B1576879
  · exact B1576883
  · exact B1576887
  · exact B1576891
  · exact B1576895
  · exact B1576899
  · exact B1576903
  · exact B1576907
  · exact B1576911
  · exact B1576915
  · exact B1576919
  · exact B1576923
  · exact B1576927
  · exact B1576931
  · exact B1576935
  · exact B1576939
  · exact B1576943
  · exact B1576947
  · exact B1576951
  · exact B1576955
  · exact B1576959
  · exact B1576963
  · exact B1576967
  · exact B1576971
  · exact B1576975
  · exact B1576979
  · exact B1576983
  · exact B1576987
  · exact B1576991
  · exact B1576995
  · exact B1576999
  · exact B1577003
  · exact B1577007
  · exact B1577011
  · exact B1577015
  · exact B1577019
  · exact B1577023
  · exact B1577027
  · exact B1577031
  · exact B1577035
  · exact B1577039
  · exact B1577043
  · exact B1577047
  · exact B1577051
  · exact B1577055
  · exact B1577059
  · exact B1577063
  · exact B1577067
  · exact B1577071
  · exact B1577075
  · exact B1577079
  · exact B1577083
  · exact B1577087
  · exact B1577091
  · exact B1577095
  · exact B1577099
  · exact B1577103
  · exact B1577107
  · exact B1577111
  · exact B1577115
  · exact B1577119
  · exact B1577123
  · exact B1577127
  · exact B1577131
  · exact B1577135
  · exact B1577139
  · exact B1577143
  · exact B1577147
  · exact B1577151
  · exact B1577155
  · exact B1577159
  · exact B1577163
  · exact B1577167
  · exact B1577171
  · exact B1577175
  · exact B1577179
  · exact B1577183
  · exact B1577187
  · exact B1577191
  · exact B1577195
  · exact B1577199
  · exact B1577203
  · exact B1577207
  · exact B1577211
  · exact B1577215
  · exact B1577219
  · exact B1577223
  · exact B1577227
  · exact B1577231
  · exact B1577235
  · exact B1577239
  · exact B1577243
  · exact B1577247
  · exact B1577251
  · exact B1577255
  · exact B1577259
  · exact B1577263
  · exact B1577267
  · exact B1577271
  · exact B1577275
  · exact B1577279
  · exact B1577283
  · exact B1577287
  · exact B1577291
  · exact B1577295
  · exact B1577299
  · exact B1577303
  · exact B1577307
  · exact B1577311
  · exact B1577315
  · exact B1577319
  · exact B1577323
  · exact B1577327
  · exact B1577331
  · exact B1577335
  · exact B1577339
  · exact B1577343
  · exact B1577347
  · exact B1577351
  · exact B1577355
  · exact B1577359
  · exact B1577363
  · exact B1577367
  · exact B1577371
  · exact B1577375
  · exact B1577379
  · exact B1577383
  · exact B1577387
  · exact B1577391
  · exact B1577395
  · exact B1577399
  · exact B1577403
  · exact B1577407
  · exact B1577411
  · exact B1577415
  · exact B1577419
  · exact B1577423
  · exact B1577427
  · exact B1577431
  · exact B1577435
  · exact B1577439
  · exact B1577443
  · exact B1577447
  · exact B1577451
  · exact B1577455
  · exact B1577459
  · exact B1577463
  · exact B1577467
  · exact B1577471
  · exact B1577475
  · exact B1577479
  · exact B1577483
  · exact B1577487
  · exact B1577491
  · exact B1577495
  · exact B1577499
  · exact B1577503
  · exact B1577507
  · exact B1577511
  · exact B1577515
  · exact B1577519
  · exact B1577523
  · exact B1577527
  · exact B1577531
  · exact B1577535
  · exact B1577539
  · exact B1577543
  · exact B1577547
  · exact B1577551
  · exact B1577555
  · exact B1577559
  · exact B1577563
  · exact B1577567
  · exact B1577571
  · exact B1577575
  · exact B1577579
  · exact B1577583
  · exact B1577587
  · exact B1577591
  · exact B1577595
  · exact B1577599
  · exact B1577603
  · exact B1577607
  · exact B1577611
  · exact B1577615
  · exact B1577619
  · exact B1577623
  · exact B1577627
  · exact B1577631
  · exact B1577635
  · exact B1577639
  · exact B1577643
  · exact B1577647
  · exact B1577651
  · exact B1577655
  · exact B1577659
  · exact B1577663
  · exact B1577667
  · exact B1577671
  · exact B1577675
  · exact B1577679
  · exact B1577683
  · exact B1577687
  · exact B1577691
  · exact B1577695
  · exact B1577699
  · exact B1577703
  · exact B1577707
  · exact B1577711
  · exact B1577715
  · exact B1577719
  · exact B1577723
  · exact B1577727
  · exact B1577731
  · exact B1577735
  · exact B1577739
  · exact B1577743
  · exact B1577747
  · exact B1577751
  · exact B1577755
  · exact B1577759
  · exact B1577763
  · exact B1577767
  · exact B1577771
  · exact B1577775
  · exact B1577779
  · exact B1577783
  · exact B1577787
  · exact B1577791
  · exact B1577795
  · exact B1577799
  · exact B1577803
  · exact B1577807
  · exact B1577811
  · exact B1577815
  · exact B1577819
  · exact B1577823
  · exact B1577827
  · exact B1577831
  · exact B1577835
  · exact B1577839
  · exact B1577843
  · exact B1577847
  · exact B1577851
  · exact B1577855
  · exact B1577859
  · exact B1577863
  · exact B1577867
  · exact B1577871
  · exact B1577875
  · exact B1577879
  · exact B1577883
  · exact B1577887
  · exact B1577891
  · exact B1577895
  · exact B1577899
  · exact B1577903
  · exact B1577907
  · exact B1577911
  · exact B1577915
  · exact B1577919
  · exact B1577923
  · exact B1577927
  · exact B1577931
  · exact B1577935
  · exact B1577939
  · exact B1577943
  · exact B1577947
  · exact B1577951
  · exact B1577955
  · exact B1577959
  · exact B1577963
  · exact B1577967
  · exact B1577971
  · exact B1577975
  · exact B1577979
  · exact B1577983
  · exact B1577987
  · exact B1577991
  · exact B1577995
  · exact B1577999
  · exact B1578003
  · exact B1578007
  · exact B1578011
  · exact B1578015
  · exact B1578019
  · exact B1578023
  · exact B1578027
  · exact B1578031
  · exact B1578035
  · exact B1578039
  · exact B1578043
  · exact B1578047
  · exact B1578051
  · exact B1578055
  · exact B1578059
  · exact B1578063
  · exact B1578067
  · exact B1578071
  · exact B1578075
  · exact B1578079
  · exact B1578083
  · exact B1578087
  · exact B1578091
  · exact B1578095
  · exact B1578099
  · exact B1578103
  · exact B1578107
  · exact B1578111
  · exact B1578115
  · exact B1578119
  · exact B1578123
  · exact B1578127
  · exact B1578131
  · exact B1578135
  · exact B1578139
  · exact B1578143
  · exact B1578147
  · exact B1578151
  · exact B1578155
  · exact B1578159
  · exact B1578163
  · exact B1578167
  · exact B1578171
  · exact B1578175
  · exact B1578179
  · exact B1578183
  · exact B1578187
  · exact B1578191
  · exact B1578195
  · exact B1578199
  · exact B1578203
  · exact B1578207
  · exact B1578211
  · exact B1578215
  · exact B1578219
  · exact B1578223
  · exact B1578227
  · exact B1578231
  · exact B1578235
  · exact B1578239
  · exact B1578243
  · exact B1578247
  · exact B1578251
  · exact B1578255
  · exact B1578259
  · exact B1578263
  · exact B1578267
  · exact B1578271
  · exact B1578275
  · exact B1578279
  · exact B1578283
  · exact B1578287
  · exact B1578291
  · exact B1578295
  · exact B1578299
  · exact B1578303
  · exact B1578307
  · exact B1578311
  · exact B1578315
  · exact B1578319
  · exact B1578323
  · exact B1578327
  · exact B1578331
  · exact B1578335
  · exact B1578339
  · exact B1578343
  · exact B1578347
  · exact B1578351
  · exact B1578355
  · exact B1578359
  · exact B1578363
  · exact B1578367
  · exact B1578371
  · exact B1578375
  · exact B1578379
  · exact B1578383
  · exact B1578387
  · exact B1578391
  · exact B1578395
  · exact B1578399
  · exact B1578403
  · exact B1578407
  · exact B1578411
  · exact B1578415
  · exact B1578419
  · exact B1578423
  · exact B1578427
  · exact B1578431
  · exact B1578435
  · exact B1578439
  · exact B1578443
  · exact B1578447
  · exact B1578451
  · exact B1578455
  · exact B1578459
  · exact B1578463
  · exact B1578467
  · exact B1578471
  · exact B1578475
  · exact B1578479
  · exact B1578483

theorem solution (m : ℕ) (hlo : 1576486 ≤ m) (hhi : m ≤ 1578486) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 394121 ≤ j := by omega
    have hj2 : j ≤ 394620 := by omega
    have hb : Blo 1576486 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
