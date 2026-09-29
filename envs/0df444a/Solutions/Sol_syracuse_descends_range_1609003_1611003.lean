-- Prove2me | solution 1 for syracuse_descends_range_1609003_1611003
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:11:45.104678+00:00
-- url     : https://prove2.me/submissions/d9120980-5961-4921-ba24-190d235c9ecd

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


theorem B1810453 : Blo 1609003 1810453 := bbase (se 6 (by rfl) ⟨42432, by rfl⟩ : syracuseStep 1810453 = 84865) (by norm_num)
theorem B1810489 : Blo 1609003 1810489 := bbase (se 2 (by rfl) ⟨678933, by rfl⟩ : syracuseStep 1810489 = 1357867) (by norm_num)
theorem B3620933 : Blo 1609003 3620933 := bbase (se 4 (by rfl) ⟨339462, by rfl⟩ : syracuseStep 3620933 = 678925) (by norm_num)
theorem B1810525 : Blo 1609003 1810525 := bbase (se 3 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 1810525 = 678947) (by norm_num)
theorem B3096677 : Blo 1609003 3096677 := bbase (se 4 (by rfl) ⟨290313, by rfl⟩ : syracuseStep 3096677 = 580627) (by norm_num)
theorem B6881381 : Blo 1609003 6881381 := bbase (se 4 (by rfl) ⟨645129, by rfl⟩ : syracuseStep 6881381 = 1290259) (by norm_num)
theorem B1810561 : Blo 1609003 1810561 := bbase (se 2 (by rfl) ⟨678960, by rfl⟩ : syracuseStep 1810561 = 1357921) (by norm_num)
theorem B3621005 : Blo 1609003 3621005 := bbase (se 3 (by rfl) ⟨678938, by rfl⟩ : syracuseStep 3621005 = 1357877) (by norm_num)
theorem B1810597 : Blo 1609003 1810597 := bbase (se 4 (by rfl) ⟨169743, by rfl⟩ : syracuseStep 1810597 = 339487) (by norm_num)
theorem B1810633 : Blo 1609003 1810633 := bbase (se 2 (by rfl) ⟨678987, by rfl⟩ : syracuseStep 1810633 = 1357975) (by norm_num)
theorem B3621077 : Blo 1609003 3621077 := bbase (se 7 (by rfl) ⟨42434, by rfl⟩ : syracuseStep 3621077 = 84869) (by norm_num)
theorem B1810669 : Blo 1609003 1810669 := bbase (se 3 (by rfl) ⟨339500, by rfl⟩ : syracuseStep 1810669 = 679001) (by norm_num)
theorem B3866885 : Blo 1609003 3866885 := bbase (se 4 (by rfl) ⟨362520, by rfl⟩ : syracuseStep 3866885 = 725041) (by norm_num)
theorem B3055877 : Blo 1609003 3055877 := bbase (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) (by norm_num)
theorem B1810705 : Blo 1609003 1810705 := bbase (se 2 (by rfl) ⟨679014, by rfl⟩ : syracuseStep 1810705 = 1358029) (by norm_num)
theorem B3621149 : Blo 1609003 3621149 := bbase (se 3 (by rfl) ⟨678965, by rfl⟩ : syracuseStep 3621149 = 1357931) (by norm_num)
theorem B5431589 : Blo 1609003 5431589 := bbase (se 4 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 5431589 = 1018423) (by norm_num)
theorem B1810741 : Blo 1609003 1810741 := bbase (se 5 (by rfl) ⟨84878, by rfl⟩ : syracuseStep 1810741 = 169757) (by norm_num)
theorem B3866941 : Blo 1609003 3866941 := bbase (se 3 (by rfl) ⟨725051, by rfl⟩ : syracuseStep 3866941 = 1450103) (by norm_num)
theorem B6111557 : Blo 1609003 6111557 := bbase (se 4 (by rfl) ⟨572958, by rfl⟩ : syracuseStep 6111557 = 1145917) (by norm_num)
theorem B1810777 : Blo 1609003 1810777 := bbase (se 2 (by rfl) ⟨679041, by rfl⟩ : syracuseStep 1810777 = 1358083) (by norm_num)
theorem B3621221 : Blo 1609003 3621221 := bbase (se 4 (by rfl) ⟨339489, by rfl⟩ : syracuseStep 3621221 = 678979) (by norm_num)
theorem B1810813 : Blo 1609003 1810813 := bbase (se 3 (by rfl) ⟨339527, by rfl⟩ : syracuseStep 1810813 = 679055) (by norm_num)
theorem B1810849 : Blo 1609003 1810849 := bbase (se 2 (by rfl) ⟨679068, by rfl⟩ : syracuseStep 1810849 = 1358137) (by norm_num)
theorem B3621293 : Blo 1609003 3621293 := bbase (se 3 (by rfl) ⟨678992, by rfl⟩ : syracuseStep 3621293 = 1357985) (by norm_num)
theorem B1810885 : Blo 1609003 1810885 := bbase (se 4 (by rfl) ⟨169770, by rfl⟩ : syracuseStep 1810885 = 339541) (by norm_num)
theorem B1810921 : Blo 1609003 1810921 := bbase (se 2 (by rfl) ⟨679095, by rfl⟩ : syracuseStep 1810921 = 1358191) (by norm_num)
theorem B3621365 : Blo 1609003 3621365 := bbase (se 5 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 3621365 = 339503) (by norm_num)
theorem B6873605 : Blo 1609003 6873605 := bbase (se 4 (by rfl) ⟨644400, by rfl⟩ : syracuseStep 6873605 = 1288801) (by norm_num)
theorem B8258053 : Blo 1609003 8258053 := bbase (se 4 (by rfl) ⟨774192, by rfl⟩ : syracuseStep 8258053 = 1548385) (by norm_num)
theorem B1810957 : Blo 1609003 1810957 := bbase (se 3 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 1810957 = 679109) (by norm_num)
theorem B3867173 : Blo 1609003 3867173 := bbase (se 4 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 3867173 = 725095) (by norm_num)
theorem B1810993 : Blo 1609003 1810993 := bbase (se 2 (by rfl) ⟨679122, by rfl⟩ : syracuseStep 1810993 = 1358245) (by norm_num)
theorem B13754933 : Blo 1609003 13754933 := bbase (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) (by norm_num)
theorem B3621437 : Blo 1609003 3621437 := bbase (se 3 (by rfl) ⟨679019, by rfl⟩ : syracuseStep 3621437 = 1358039) (by norm_num)
theorem B1933889 : Blo 1609003 1933889 := bbase (se 2 (by rfl) ⟨725208, by rfl⟩ : syracuseStep 1933889 = 1450417) (by norm_num)
theorem B1811029 : Blo 1609003 1811029 := bbase (se 8 (by rfl) ⟨10611, by rfl⟩ : syracuseStep 1811029 = 21223) (by norm_num)
theorem B1933913 : Blo 1609003 1933913 := bbase (se 2 (by rfl) ⟨725217, by rfl⟩ : syracuseStep 1933913 = 1450435) (by norm_num)
theorem B6111845 : Blo 1609003 6111845 := bbase (se 4 (by rfl) ⟨572985, by rfl⟩ : syracuseStep 6111845 = 1145971) (by norm_num)
theorem B1811065 : Blo 1609003 1811065 := bbase (se 2 (by rfl) ⟨679149, by rfl⟩ : syracuseStep 1811065 = 1358299) (by norm_num)
theorem B3621509 : Blo 1609003 3621509 := bbase (se 4 (by rfl) ⟨339516, by rfl⟩ : syracuseStep 3621509 = 679033) (by norm_num)
theorem B2941589 : Blo 1609003 2941589 := bbase (se 6 (by rfl) ⟨68943, by rfl⟩ : syracuseStep 2941589 = 137887) (by norm_num)
theorem B1811101 : Blo 1609003 1811101 := bbase (se 3 (by rfl) ⟨339581, by rfl⟩ : syracuseStep 1811101 = 679163) (by norm_num)
theorem B1835689 : Blo 1609003 1835689 := bbase (se 2 (by rfl) ⟨688383, by rfl⟩ : syracuseStep 1835689 = 1376767) (by norm_num)
theorem B1811137 : Blo 1609003 1811137 := bbase (se 2 (by rfl) ⟨679176, by rfl⟩ : syracuseStep 1811137 = 1358353) (by norm_num)
theorem B3621581 : Blo 1609003 3621581 := bbase (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) (by norm_num)
theorem B5432021 : Blo 1609003 5432021 := bbase (se 7 (by rfl) ⟨63656, by rfl⟩ : syracuseStep 5432021 = 127313) (by norm_num)
theorem B4129501 : Blo 1609003 4129501 := bbase (se 3 (by rfl) ⟨774281, by rfl⟩ : syracuseStep 4129501 = 1548563) (by norm_num)
theorem B3867365 : Blo 1609003 3867365 := bbase (se 4 (by rfl) ⟨362565, by rfl⟩ : syracuseStep 3867365 = 725131) (by norm_num)
theorem B1811173 : Blo 1609003 1811173 := bbase (se 4 (by rfl) ⟨169797, by rfl⟩ : syracuseStep 1811173 = 339595) (by norm_num)
theorem B10314485 : Blo 1609003 10314485 := bbase (se 5 (by rfl) ⟨483491, by rfl⟩ : syracuseStep 10314485 = 966983) (by norm_num)
theorem B3097349 : Blo 1609003 3097349 := bbase (se 4 (by rfl) ⟨290376, by rfl⟩ : syracuseStep 3097349 = 580753) (by norm_num)
theorem B1811209 : Blo 1609003 1811209 := bbase (se 2 (by rfl) ⟨679203, by rfl⟩ : syracuseStep 1811209 = 1358407) (by norm_num)
theorem B3621653 : Blo 1609003 3621653 := bbase (se 6 (by rfl) ⟨84882, by rfl⟩ : syracuseStep 3621653 = 169765) (by norm_num)
theorem B1811245 : Blo 1609003 1811245 := bbase (se 3 (by rfl) ⟨339608, by rfl⟩ : syracuseStep 1811245 = 679217) (by norm_num)
theorem B1811281 : Blo 1609003 1811281 := bbase (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) (by norm_num)
theorem B3621725 : Blo 1609003 3621725 := bbase (se 3 (by rfl) ⟨679073, by rfl⟩ : syracuseStep 3621725 = 1358147) (by norm_num)
theorem B1811317 : Blo 1609003 1811317 := bbase (se 5 (by rfl) ⟨84905, by rfl⟩ : syracuseStep 1811317 = 169811) (by norm_num)
theorem B1934221 : Blo 1609003 1934221 := bbase (se 3 (by rfl) ⟨362666, by rfl⟩ : syracuseStep 1934221 = 725333) (by norm_num)
theorem B1811353 : Blo 1609003 1811353 := bbase (se 2 (by rfl) ⟨679257, by rfl⟩ : syracuseStep 1811353 = 1358515) (by norm_num)
theorem B3621797 : Blo 1609003 3621797 := bbase (se 4 (by rfl) ⟨339543, by rfl⟩ : syracuseStep 3621797 = 679087) (by norm_num)
theorem B1811389 : Blo 1609003 1811389 := bbase (se 3 (by rfl) ⟨339635, by rfl⟩ : syracuseStep 1811389 = 679271) (by norm_num)
theorem B1811425 : Blo 1609003 1811425 := bbase (se 2 (by rfl) ⟨679284, by rfl⟩ : syracuseStep 1811425 = 1358569) (by norm_num)
theorem B3621869 : Blo 1609003 3621869 := bbase (se 3 (by rfl) ⟨679100, by rfl⟩ : syracuseStep 3621869 = 1358201) (by norm_num)
theorem B3056629 : Blo 1609003 3056629 := bbase (se 5 (by rfl) ⟨143279, by rfl⟩ : syracuseStep 3056629 = 286559) (by norm_num)
theorem B1811461 : Blo 1609003 1811461 := bbase (se 4 (by rfl) ⟨169824, by rfl⟩ : syracuseStep 1811461 = 339649) (by norm_num)
theorem B1811497 : Blo 1609003 1811497 := bbase (se 2 (by rfl) ⟨679311, by rfl⟩ : syracuseStep 1811497 = 1358623) (by norm_num)
theorem B3621941 : Blo 1609003 3621941 := bbase (se 5 (by rfl) ⟨169778, by rfl⟩ : syracuseStep 3621941 = 339557) (by norm_num)
theorem B1934393 : Blo 1609003 1934393 := bbase (se 2 (by rfl) ⟨725397, by rfl⟩ : syracuseStep 1934393 = 1450795) (by norm_num)
theorem B1811533 : Blo 1609003 1811533 := bbase (se 3 (by rfl) ⟨339662, by rfl⟩ : syracuseStep 1811533 = 679325) (by norm_num)
theorem B1811569 : Blo 1609003 1811569 := bbase (se 2 (by rfl) ⟨679338, by rfl⟩ : syracuseStep 1811569 = 1358677) (by norm_num)
theorem B3622013 : Blo 1609003 3622013 := bbase (se 3 (by rfl) ⟨679127, by rfl⟩ : syracuseStep 3622013 = 1358255) (by norm_num)
theorem B5432453 : Blo 1609003 5432453 := bbase (se 4 (by rfl) ⟨509292, by rfl⟩ : syracuseStep 5432453 = 1018585) (by norm_num)
theorem B3056773 : Blo 1609003 3056773 := bbase (se 4 (by rfl) ⟨286572, by rfl⟩ : syracuseStep 3056773 = 573145) (by norm_num)
theorem B1811605 : Blo 1609003 1811605 := bbase (se 6 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 1811605 = 84919) (by norm_num)
theorem B1934509 : Blo 1609003 1934509 := bbase (se 3 (by rfl) ⟨362720, by rfl⟩ : syracuseStep 1934509 = 725441) (by norm_num)
theorem B1811641 : Blo 1609003 1811641 := bbase (se 2 (by rfl) ⟨679365, by rfl⟩ : syracuseStep 1811641 = 1358731) (by norm_num)
theorem B3622085 : Blo 1609003 3622085 := bbase (se 4 (by rfl) ⟨339570, by rfl⟩ : syracuseStep 3622085 = 679141) (by norm_num)
theorem B1811677 : Blo 1609003 1811677 := bbase (se 3 (by rfl) ⟨339689, by rfl⟩ : syracuseStep 1811677 = 679379) (by norm_num)
theorem B1811713 : Blo 1609003 1811713 := bbase (se 2 (by rfl) ⟨679392, by rfl⟩ : syracuseStep 1811713 = 1358785) (by norm_num)
theorem B8152325 : Blo 1609003 8152325 := bbase (se 4 (by rfl) ⟨764280, by rfl⟩ : syracuseStep 8152325 = 1528561) (by norm_num)
theorem B3622157 : Blo 1609003 3622157 := bbase (se 3 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 3622157 = 1358309) (by norm_num)
theorem B1934605 : Blo 1609003 1934605 := bbase (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) (by norm_num)
theorem B3056933 : Blo 1609003 3056933 := bbase (se 4 (by rfl) ⟨286587, by rfl⟩ : syracuseStep 3056933 = 573175) (by norm_num)
theorem B1811749 : Blo 1609003 1811749 := bbase (se 4 (by rfl) ⟨169851, by rfl⟩ : syracuseStep 1811749 = 339703) (by norm_num)
theorem B1811785 : Blo 1609003 1811785 := bbase (se 2 (by rfl) ⟨679419, by rfl⟩ : syracuseStep 1811785 = 1358839) (by norm_num)
theorem B3622229 : Blo 1609003 3622229 := bbase (se 12 (by rfl) ⟨1326, by rfl⟩ : syracuseStep 3622229 = 2653) (by norm_num)
theorem B1811821 : Blo 1609003 1811821 := bbase (se 3 (by rfl) ⟨339716, by rfl⟩ : syracuseStep 1811821 = 679433) (by norm_num)
theorem B1860989 : Blo 1609003 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B1811857 : Blo 1609003 1811857 := bbase (se 2 (by rfl) ⟨679446, by rfl⟩ : syracuseStep 1811857 = 1358893) (by norm_num)
theorem B11011477 : Blo 1609003 11011477 := bbase (se 6 (by rfl) ⟨258081, by rfl⟩ : syracuseStep 11011477 = 516163) (by norm_num)
theorem B3622301 : Blo 1609003 3622301 := bbase (se 3 (by rfl) ⟨679181, by rfl⟩ : syracuseStep 3622301 = 1358363) (by norm_num)
theorem B1934749 : Blo 1609003 1934749 := bbase (se 3 (by rfl) ⟨362765, by rfl⟩ : syracuseStep 1934749 = 725531) (by norm_num)
theorem B3057077 : Blo 1609003 3057077 := bbase (se 5 (by rfl) ⟨143300, by rfl⟩ : syracuseStep 3057077 = 286601) (by norm_num)
theorem B1811893 : Blo 1609003 1811893 := bbase (se 5 (by rfl) ⟨84932, by rfl⟩ : syracuseStep 1811893 = 169865) (by norm_num)
theorem B1811929 : Blo 1609003 1811929 := bbase (se 2 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 1811929 = 1358947) (by norm_num)
theorem B3622373 : Blo 1609003 3622373 := bbase (se 4 (by rfl) ⟨339597, by rfl⟩ : syracuseStep 3622373 = 679195) (by norm_num)
theorem B4351477 : Blo 1609003 4351477 := bbase (se 5 (by rfl) ⟨203975, by rfl⟩ : syracuseStep 4351477 = 407951) (by norm_num)
theorem B1811965 : Blo 1609003 1811965 := bbase (se 3 (by rfl) ⟨339743, by rfl⟩ : syracuseStep 1811965 = 679487) (by norm_num)
theorem B3098125 : Blo 1609003 3098125 := bbase (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) (by norm_num)
theorem B1812001 : Blo 1609003 1812001 := bbase (se 2 (by rfl) ⟨679500, by rfl⟩ : syracuseStep 1812001 = 1359001) (by norm_num)
theorem B3622445 : Blo 1609003 3622445 := bbase (se 3 (by rfl) ⟨679208, by rfl⟩ : syracuseStep 3622445 = 1358417) (by norm_num)
theorem B5432885 : Blo 1609003 5432885 := bbase (se 5 (by rfl) ⟨254666, by rfl⟩ : syracuseStep 5432885 = 509333) (by norm_num)
theorem B1812037 : Blo 1609003 1812037 := bbase (se 4 (by rfl) ⟨169878, by rfl⟩ : syracuseStep 1812037 = 339757) (by norm_num)
theorem B1812073 : Blo 1609003 1812073 := bbase (se 2 (by rfl) ⟨679527, by rfl⟩ : syracuseStep 1812073 = 1359055) (by norm_num)
theorem B3671669 : Blo 1609003 3671669 := bbase (se 5 (by rfl) ⟨172109, by rfl⟩ : syracuseStep 3671669 = 344219) (by norm_num)
theorem B3622517 : Blo 1609003 3622517 := bbase (se 5 (by rfl) ⟨169805, by rfl⟩ : syracuseStep 3622517 = 339611) (by norm_num)
theorem B1812109 : Blo 1609003 1812109 := bbase (se 3 (by rfl) ⟨339770, by rfl⟩ : syracuseStep 1812109 = 679541) (by norm_num)
theorem B4073125 : Blo 1609003 4073125 := bbase (se 4 (by rfl) ⟨381855, by rfl⟩ : syracuseStep 4073125 = 763711) (by norm_num)
theorem B3868325 : Blo 1609003 3868325 := bbase (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) (by norm_num)
theorem B1812145 : Blo 1609003 1812145 := bbase (se 2 (by rfl) ⟨679554, by rfl⟩ : syracuseStep 1812145 = 1359109) (by norm_num)
theorem B3622589 : Blo 1609003 3622589 := bbase (se 3 (by rfl) ⟨679235, by rfl⟩ : syracuseStep 3622589 = 1358471) (by norm_num)
theorem B3057365 : Blo 1609003 3057365 := bbase (se 7 (by rfl) ⟨35828, by rfl⟩ : syracuseStep 3057365 = 71657) (by norm_num)
theorem B1812181 : Blo 1609003 1812181 := bbase (se 7 (by rfl) ⟨21236, by rfl⟩ : syracuseStep 1812181 = 42473) (by norm_num)
theorem B2041573 : Blo 1609003 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B1812217 : Blo 1609003 1812217 := bbase (se 2 (by rfl) ⟨679581, by rfl⟩ : syracuseStep 1812217 = 1359163) (by norm_num)
theorem B2901757 : Blo 1609003 2901757 := bbase (se 3 (by rfl) ⟨544079, by rfl⟩ : syracuseStep 2901757 = 1088159) (by norm_num)
theorem B6113029 : Blo 1609003 6113029 := bbase (se 4 (by rfl) ⟨573096, by rfl⟩ : syracuseStep 6113029 = 1146193) (by norm_num)
theorem B3622661 : Blo 1609003 3622661 := bbase (se 4 (by rfl) ⟨339624, by rfl⟩ : syracuseStep 3622661 = 679249) (by norm_num)
theorem B4073237 : Blo 1609003 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B1812253 : Blo 1609003 1812253 := bbase (se 3 (by rfl) ⟨339797, by rfl⟩ : syracuseStep 1812253 = 679595) (by norm_num)
theorem B4351781 : Blo 1609003 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B1812289 : Blo 1609003 1812289 := bbase (se 2 (by rfl) ⟨679608, by rfl⟩ : syracuseStep 1812289 = 1359217) (by norm_num)
theorem B3622733 : Blo 1609003 3622733 := bbase (se 3 (by rfl) ⟨679262, by rfl⟩ : syracuseStep 3622733 = 1358525) (by norm_num)
theorem B1812325 : Blo 1609003 1812325 := bbase (se 4 (by rfl) ⟨169905, by rfl⟩ : syracuseStep 1812325 = 339811) (by norm_num)
theorem B3057517 : Blo 1609003 3057517 := bbase (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) (by norm_num)
theorem B1812361 : Blo 1609003 1812361 := bbase (se 2 (by rfl) ⟨679635, by rfl⟩ : syracuseStep 1812361 = 1359271) (by norm_num)
theorem B3622805 : Blo 1609003 3622805 := bbase (se 6 (by rfl) ⟨84909, by rfl⟩ : syracuseStep 3622805 = 169819) (by norm_num)
theorem B1632193 : Blo 1609003 1632193 := bbase (se 2 (by rfl) ⟨612072, by rfl⟩ : syracuseStep 1632193 = 1224145) (by norm_num)
theorem B1632209 : Blo 1609003 1632209 := bbase (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) (by norm_num)
theorem B4073429 : Blo 1609003 4073429 := bbase (se 7 (by rfl) ⟨47735, by rfl⟩ : syracuseStep 4073429 = 95471) (by norm_num)
theorem B3622877 : Blo 1609003 3622877 := bbase (se 3 (by rfl) ⟨679289, by rfl⟩ : syracuseStep 3622877 = 1358579) (by norm_num)
theorem B5433317 : Blo 1609003 5433317 := bbase (se 4 (by rfl) ⟨509373, by rfl⟩ : syracuseStep 5433317 = 1018747) (by norm_num)
theorem B3483661 : Blo 1609003 3483661 := bbase (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) (by norm_num)
theorem B3622949 : Blo 1609003 3622949 := bbase (se 4 (by rfl) ⟨339651, by rfl⟩ : syracuseStep 3622949 = 679303) (by norm_num)
theorem B6113333 : Blo 1609003 6113333 := bbase (se 5 (by rfl) ⟨286562, by rfl⟩ : syracuseStep 6113333 = 573125) (by norm_num)
theorem B2066485 : Blo 1609003 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B8259653 : Blo 1609003 8259653 := bbase (se 4 (by rfl) ⟨774342, by rfl⟩ : syracuseStep 8259653 = 1548685) (by norm_num)
theorem B3623021 : Blo 1609003 3623021 := bbase (se 3 (by rfl) ⟨679316, by rfl⟩ : syracuseStep 3623021 = 1358633) (by norm_num)
theorem B3057821 : Blo 1609003 3057821 := bbase (se 3 (by rfl) ⟨573341, by rfl⟩ : syracuseStep 3057821 = 1146683) (by norm_num)
theorem B1632421 : Blo 1609003 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B3623093 : Blo 1609003 3623093 := bbase (se 5 (by rfl) ⟨169832, by rfl⟩ : syracuseStep 3623093 = 339665) (by norm_num)
theorem B2615485 : Blo 1609003 2615485 := bbase (se 3 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 2615485 = 980807) (by norm_num)
theorem B6875381 : Blo 1609003 6875381 := bbase (se 5 (by rfl) ⟨322283, by rfl⟩ : syracuseStep 6875381 = 644567) (by norm_num)
theorem B3623165 : Blo 1609003 3623165 := bbase (se 3 (by rfl) ⟨679343, by rfl⟩ : syracuseStep 3623165 = 1358687) (by norm_num)
theorem B4073773 : Blo 1609003 4073773 := bbase (se 3 (by rfl) ⟨763832, by rfl⟩ : syracuseStep 4073773 = 1527665) (by norm_num)
theorem B3262765 : Blo 1609003 3262765 := bbase (se 3 (by rfl) ⟨611768, by rfl⟩ : syracuseStep 3262765 = 1223537) (by norm_num)
theorem B3623237 : Blo 1609003 3623237 := bbase (se 4 (by rfl) ⟨339678, by rfl⟩ : syracuseStep 3623237 = 679357) (by norm_num)
theorem B8259941 : Blo 1609003 8259941 := bbase (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) (by norm_num)
theorem B2902397 : Blo 1609003 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B3262861 : Blo 1609003 3262861 := bbase (se 3 (by rfl) ⟨611786, by rfl⟩ : syracuseStep 3262861 = 1223573) (by norm_num)
theorem B3623309 : Blo 1609003 3623309 := bbase (se 3 (by rfl) ⟨679370, by rfl⟩ : syracuseStep 3623309 = 1358741) (by norm_num)
theorem B5433749 : Blo 1609003 5433749 := bbase (se 6 (by rfl) ⟨127353, by rfl⟩ : syracuseStep 5433749 = 254707) (by norm_num)
theorem B4073885 : Blo 1609003 4073885 := bbase (se 3 (by rfl) ⟨763853, by rfl⟩ : syracuseStep 4073885 = 1527707) (by norm_num)
theorem B3623381 : Blo 1609003 3623381 := bbase (se 7 (by rfl) ⟨42461, by rfl⟩ : syracuseStep 3623381 = 84923) (by norm_num)
theorem B5302741 : Blo 1609003 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B8153621 : Blo 1609003 8153621 := bbase (se 6 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 8153621 = 382201) (by norm_num)
theorem B3623453 : Blo 1609003 3623453 := bbase (se 3 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 3623453 = 1358795) (by norm_num)
theorem B5155397 : Blo 1609003 5155397 := bbase (se 4 (by rfl) ⟨483318, by rfl⟩ : syracuseStep 5155397 = 966637) (by norm_num)
theorem B4074077 : Blo 1609003 4074077 := bbase (se 3 (by rfl) ⟨763889, by rfl⟩ : syracuseStep 4074077 = 1527779) (by norm_num)
theorem B3623525 : Blo 1609003 3623525 := bbase (se 4 (by rfl) ⟨339705, by rfl⟩ : syracuseStep 3623525 = 679411) (by norm_num)
theorem B3623597 : Blo 1609003 3623597 := bbase (se 3 (by rfl) ⟨679424, by rfl⟩ : syracuseStep 3623597 = 1358849) (by norm_num)
theorem B3623669 : Blo 1609003 3623669 := bbase (se 5 (by rfl) ⟨169859, by rfl⟩ : syracuseStep 3623669 = 339719) (by norm_num)
theorem B6195973 : Blo 1609003 6195973 := bbase (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) (by norm_num)
theorem B8702741 : Blo 1609003 8702741 := bbase (se 6 (by rfl) ⟨203970, by rfl⟩ : syracuseStep 8702741 = 407941) (by norm_num)
theorem B3623741 : Blo 1609003 3623741 := bbase (se 3 (by rfl) ⟨679451, by rfl⟩ : syracuseStep 3623741 = 1358903) (by norm_num)
theorem B5434181 : Blo 1609003 5434181 := bbase (se 4 (by rfl) ⟨509454, by rfl⟩ : syracuseStep 5434181 = 1018909) (by norm_num)
theorem B3623813 : Blo 1609003 3623813 := bbase (se 4 (by rfl) ⟨339732, by rfl⟩ : syracuseStep 3623813 = 679465) (by norm_num)
theorem B8145845 : Blo 1609003 8145845 := bbase (se 5 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 8145845 = 763673) (by norm_num)
theorem B4074421 : Blo 1609003 4074421 := bbase (se 5 (by rfl) ⟨190988, by rfl⟩ : syracuseStep 4074421 = 381977) (by norm_num)
theorem B3623885 : Blo 1609003 3623885 := bbase (se 3 (by rfl) ⟨679478, by rfl⟩ : syracuseStep 3623885 = 1358957) (by norm_num)
theorem B3623957 : Blo 1609003 3623957 := bbase (se 6 (by rfl) ⟨84936, by rfl⟩ : syracuseStep 3623957 = 169873) (by norm_num)
theorem B4074533 : Blo 1609003 4074533 := bbase (se 4 (by rfl) ⟨381987, by rfl⟩ : syracuseStep 4074533 = 763975) (by norm_num)
theorem B4353077 : Blo 1609003 4353077 := bbase (se 5 (by rfl) ⟨204050, by rfl⟩ : syracuseStep 4353077 = 408101) (by norm_num)
theorem B3533885 : Blo 1609003 3533885 := bbase (se 3 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 3533885 = 1325207) (by norm_num)
theorem B3624029 : Blo 1609003 3624029 := bbase (se 3 (by rfl) ⟨679505, by rfl⟩ : syracuseStep 3624029 = 1359011) (by norm_num)
theorem B4131965 : Blo 1609003 4131965 := bbase (se 3 (by rfl) ⟨774743, by rfl⟩ : syracuseStep 4131965 = 1549487) (by norm_num)
theorem B5885077 : Blo 1609003 5885077 := bbase (se 6 (by rfl) ⟨137931, by rfl⟩ : syracuseStep 5885077 = 275863) (by norm_num)
theorem B6524069 : Blo 1609003 6524069 := bbase (se 4 (by rfl) ⟨611631, by rfl⟩ : syracuseStep 6524069 = 1223263) (by norm_num)
theorem B3624101 : Blo 1609003 3624101 := bbase (se 4 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 3624101 = 679519) (by norm_num)
theorem B6196421 : Blo 1609003 6196421 := bbase (se 4 (by rfl) ⟨580914, by rfl⟩ : syracuseStep 6196421 = 1161829) (by norm_num)
theorem B6876373 : Blo 1609003 6876373 := bbase (se 7 (by rfl) ⟨80582, by rfl⟩ : syracuseStep 6876373 = 161165) (by norm_num)
theorem B4074725 : Blo 1609003 4074725 := bbase (se 4 (by rfl) ⟨382005, by rfl⟩ : syracuseStep 4074725 = 764011) (by norm_num)
theorem B3624173 : Blo 1609003 3624173 := bbase (se 3 (by rfl) ⟨679532, by rfl⟩ : syracuseStep 3624173 = 1359065) (by norm_num)
theorem B5434613 : Blo 1609003 5434613 := bbase (se 5 (by rfl) ⟨254747, by rfl⟩ : syracuseStep 5434613 = 509495) (by norm_num)
theorem B3722525 : Blo 1609003 3722525 := bbase (se 3 (by rfl) ⟨697973, by rfl⟩ : syracuseStep 3722525 = 1395947) (by norm_num)
theorem B3624245 : Blo 1609003 3624245 := bbase (se 5 (by rfl) ⟨169886, by rfl⟩ : syracuseStep 3624245 = 339773) (by norm_num)
theorem B4582757 : Blo 1609003 4582757 := bbase (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) (by norm_num)
theorem B3624317 : Blo 1609003 3624317 := bbase (se 3 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 3624317 = 1359119) (by norm_num)
theorem B3673493 : Blo 1609003 3673493 := bbase (se 6 (by rfl) ⟨86097, by rfl⟩ : syracuseStep 3673493 = 172195) (by norm_num)
theorem B3624389 : Blo 1609003 3624389 := bbase (se 4 (by rfl) ⟨339786, by rfl⟩ : syracuseStep 3624389 = 679573) (by norm_num)
theorem B3624461 : Blo 1609003 3624461 := bbase (se 3 (by rfl) ⟨679586, by rfl⟩ : syracuseStep 3624461 = 1359173) (by norm_num)
theorem B4075069 : Blo 1609003 4075069 := bbase (se 3 (by rfl) ⟨764075, by rfl⟩ : syracuseStep 4075069 = 1528151) (by norm_num)
theorem B2715221 : Blo 1609003 2715221 := bbase (se 8 (by rfl) ⟨15909, by rfl⟩ : syracuseStep 2715221 = 31819) (by norm_num)
theorem B3624533 : Blo 1609003 3624533 := bbase (se 8 (by rfl) ⟨21237, by rfl⟩ : syracuseStep 3624533 = 42475) (by norm_num)
theorem B3624605 : Blo 1609003 3624605 := bbase (se 3 (by rfl) ⟨679613, by rfl⟩ : syracuseStep 3624605 = 1359227) (by norm_num)
theorem B5435045 : Blo 1609003 5435045 := bbase (se 4 (by rfl) ⟨509535, by rfl⟩ : syracuseStep 5435045 = 1019071) (by norm_num)
theorem B4075181 : Blo 1609003 4075181 := bbase (se 3 (by rfl) ⟨764096, by rfl⟩ : syracuseStep 4075181 = 1528193) (by norm_num)
theorem B2715349 : Blo 1609003 2715349 := bbase (se 7 (by rfl) ⟨31820, by rfl⟩ : syracuseStep 2715349 = 63641) (by norm_num)
theorem B3624677 : Blo 1609003 3624677 := bbase (se 4 (by rfl) ⟨339813, by rfl⟩ : syracuseStep 3624677 = 679627) (by norm_num)
theorem B8154917 : Blo 1609003 8154917 := bbase (se 4 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 8154917 = 1529047) (by norm_num)
theorem B2715437 : Blo 1609003 2715437 := bbase (se 3 (by rfl) ⟨509144, by rfl⟩ : syracuseStep 2715437 = 1018289) (by norm_num)
theorem B3624749 : Blo 1609003 3624749 := bbase (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) (by norm_num)
theorem B5959477 : Blo 1609003 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B4075373 : Blo 1609003 4075373 := bbase (se 3 (by rfl) ⟨764132, by rfl⟩ : syracuseStep 4075373 = 1528265) (by norm_num)
theorem B5156741 : Blo 1609003 5156741 := bbase (se 4 (by rfl) ⟨483444, by rfl⟩ : syracuseStep 5156741 = 966889) (by norm_num)
theorem B26480533 : Blo 1609003 26480533 := bbase (se 6 (by rfl) ⟨620637, by rfl⟩ : syracuseStep 26480533 = 1241275) (by norm_num)
theorem B2715565 : Blo 1609003 2715565 := bbase (se 3 (by rfl) ⟨509168, by rfl⟩ : syracuseStep 2715565 = 1018337) (by norm_num)
theorem B2715653 : Blo 1609003 2715653 := bbase (se 4 (by rfl) ⟨254592, by rfl⟩ : syracuseStep 2715653 = 509185) (by norm_num)
theorem B4583429 : Blo 1609003 4583429 := bbase (se 4 (by rfl) ⟨429696, by rfl⟩ : syracuseStep 4583429 = 859393) (by norm_num)
theorem B3436597 : Blo 1609003 3436597 := bbase (se 5 (by rfl) ⟨161090, by rfl⟩ : syracuseStep 3436597 = 322181) (by norm_num)
theorem B5435477 : Blo 1609003 5435477 := bbase (se 8 (by rfl) ⟨31848, by rfl⟩ : syracuseStep 5435477 = 63697) (by norm_num)
theorem B1986649 : Blo 1609003 1986649 := bbase (se 2 (by rfl) ⟨744993, by rfl⟩ : syracuseStep 1986649 = 1489987) (by norm_num)
theorem B6115445 : Blo 1609003 6115445 := bbase (se 5 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 6115445 = 573323) (by norm_num)
theorem B2715781 : Blo 1609003 2715781 := bbase (se 4 (by rfl) ⟨254604, by rfl⟩ : syracuseStep 2715781 = 509209) (by norm_num)
theorem B8147141 : Blo 1609003 8147141 := bbase (se 4 (by rfl) ⟨763794, by rfl⟩ : syracuseStep 8147141 = 1527589) (by norm_num)
theorem B4075717 : Blo 1609003 4075717 := bbase (se 4 (by rfl) ⟨382098, by rfl⟩ : syracuseStep 4075717 = 764197) (by norm_num)
theorem B30937301 : Blo 1609003 30937301 := bbase (se 7 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 30937301 = 725093) (by norm_num)
theorem B2715869 : Blo 1609003 2715869 := bbase (se 3 (by rfl) ⟨509225, by rfl⟩ : syracuseStep 2715869 = 1018451) (by norm_num)
theorem B4075829 : Blo 1609003 4075829 := bbase (se 5 (by rfl) ⟨191054, by rfl⟩ : syracuseStep 4075829 = 382109) (by norm_num)
theorem B2715997 : Blo 1609003 2715997 := bbase (se 3 (by rfl) ⟨509249, by rfl⟩ : syracuseStep 2715997 = 1018499) (by norm_num)
theorem B6115733 : Blo 1609003 6115733 := bbase (se 6 (by rfl) ⟨143337, by rfl⟩ : syracuseStep 6115733 = 286675) (by norm_num)
theorem B2716085 : Blo 1609003 2716085 := bbase (se 5 (by rfl) ⟨127316, by rfl⟩ : syracuseStep 2716085 = 254633) (by norm_num)
theorem B4583861 : Blo 1609003 4583861 := bbase (se 5 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 4583861 = 429737) (by norm_num)
theorem B15479221 : Blo 1609003 15479221 := bbase (se 5 (by rfl) ⟨725588, by rfl⟩ : syracuseStep 15479221 = 1451177) (by norm_num)
theorem B2421181 : Blo 1609003 2421181 := bbase (se 3 (by rfl) ⟨453971, by rfl⟩ : syracuseStep 2421181 = 907943) (by norm_num)
theorem B9171413 : Blo 1609003 9171413 := bbase (se 7 (by rfl) ⟨107477, by rfl⟩ : syracuseStep 9171413 = 214955) (by norm_num)
theorem B4076021 : Blo 1609003 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B5435909 : Blo 1609003 5435909 := bbase (se 4 (by rfl) ⟨509616, by rfl⟩ : syracuseStep 5435909 = 1019233) (by norm_num)
theorem B3437093 : Blo 1609003 3437093 := bbase (se 4 (by rfl) ⟨322227, by rfl⟩ : syracuseStep 3437093 = 644455) (by norm_num)
theorem B2716213 : Blo 1609003 2716213 := bbase (se 5 (by rfl) ⟨127322, by rfl⟩ : syracuseStep 2716213 = 254645) (by norm_num)
theorem B3265085 : Blo 1609003 3265085 := bbase (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) (by norm_num)
theorem B8704597 : Blo 1609003 8704597 := bbase (se 8 (by rfl) ⟨51003, by rfl⟩ : syracuseStep 8704597 = 102007) (by norm_num)
theorem B2716301 : Blo 1609003 2716301 := bbase (se 3 (by rfl) ⟨509306, by rfl⟩ : syracuseStep 2716301 = 1018613) (by norm_num)
theorem B2036441 : Blo 1609003 2036441 := bbase (se 2 (by rfl) ⟨763665, by rfl⟩ : syracuseStep 2036441 = 1527331) (by norm_num)
theorem B2716429 : Blo 1609003 2716429 := bbase (se 3 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 2716429 = 1018661) (by norm_num)
theorem B2036497 : Blo 1609003 2036497 := bbase (se 2 (by rfl) ⟨763686, by rfl⟩ : syracuseStep 2036497 = 1527373) (by norm_num)
theorem B6370085 : Blo 1609003 6370085 := bbase (se 4 (by rfl) ⟨597195, by rfl⟩ : syracuseStep 6370085 = 1194391) (by norm_num)
theorem B4076365 : Blo 1609003 4076365 := bbase (se 3 (by rfl) ⟨764318, by rfl⟩ : syracuseStep 4076365 = 1528637) (by norm_num)
theorem B2716517 : Blo 1609003 2716517 := bbase (se 4 (by rfl) ⟨254673, by rfl⟩ : syracuseStep 2716517 = 509347) (by norm_num)
theorem B2036593 : Blo 1609003 2036593 := bbase (se 2 (by rfl) ⟨763722, by rfl⟩ : syracuseStep 2036593 = 1527445) (by norm_num)
theorem B2175869 : Blo 1609003 2175869 := bbase (se 3 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 2175869 = 815951) (by norm_num)
theorem B5436341 : Blo 1609003 5436341 := bbase (se 5 (by rfl) ⟨254828, by rfl⟩ : syracuseStep 5436341 = 509657) (by norm_num)
theorem B4076477 : Blo 1609003 4076477 := bbase (se 3 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 4076477 = 1528679) (by norm_num)
theorem B2413517 : Blo 1609003 2413517 := bbase (se 3 (by rfl) ⟨452534, by rfl⟩ : syracuseStep 2413517 = 905069) (by norm_num)
theorem B7738325 : Blo 1609003 7738325 := bbase (se 7 (by rfl) ⟨90683, by rfl⟩ : syracuseStep 7738325 = 181367) (by norm_num)
theorem B2413541 : Blo 1609003 2413541 := bbase (se 4 (by rfl) ⟨226269, by rfl⟩ : syracuseStep 2413541 = 452539) (by norm_num)
theorem B2716645 : Blo 1609003 2716645 := bbase (se 4 (by rfl) ⟨254685, by rfl⟩ : syracuseStep 2716645 = 509371) (by norm_num)
theorem B2413565 : Blo 1609003 2413565 := bbase (se 3 (by rfl) ⟨452543, by rfl⟩ : syracuseStep 2413565 = 905087) (by norm_num)
theorem B2413589 : Blo 1609003 2413589 := bbase (se 6 (by rfl) ⟨56568, by rfl⟩ : syracuseStep 2413589 = 113137) (by norm_num)
theorem B2036765 : Blo 1609003 2036765 := bbase (se 3 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 2036765 = 763787) (by norm_num)
theorem B2413613 : Blo 1609003 2413613 := bbase (se 3 (by rfl) ⟨452552, by rfl⟩ : syracuseStep 2413613 = 905105) (by norm_num)
theorem B2716733 : Blo 1609003 2716733 := bbase (se 3 (by rfl) ⟨509387, by rfl⟩ : syracuseStep 2716733 = 1018775) (by norm_num)
theorem B2413637 : Blo 1609003 2413637 := bbase (se 4 (by rfl) ⟨226278, by rfl⟩ : syracuseStep 2413637 = 452557) (by norm_num)
theorem B2036821 : Blo 1609003 2036821 := bbase (se 8 (by rfl) ⟨11934, by rfl⟩ : syracuseStep 2036821 = 23869) (by norm_num)
theorem B2413661 : Blo 1609003 2413661 := bbase (se 3 (by rfl) ⟨452561, by rfl⟩ : syracuseStep 2413661 = 905123) (by norm_num)
theorem B2413685 : Blo 1609003 2413685 := bbase (se 5 (by rfl) ⟨113141, by rfl⟩ : syracuseStep 2413685 = 226283) (by norm_num)
theorem B4076669 : Blo 1609003 4076669 := bbase (se 3 (by rfl) ⟨764375, by rfl⟩ : syracuseStep 4076669 = 1528751) (by norm_num)
theorem B2413709 : Blo 1609003 2413709 := bbase (se 3 (by rfl) ⟨452570, by rfl⟩ : syracuseStep 2413709 = 905141) (by norm_num)
theorem B2413733 : Blo 1609003 2413733 := bbase (se 4 (by rfl) ⟨226287, by rfl⟩ : syracuseStep 2413733 = 452575) (by norm_num)
theorem B4584613 : Blo 1609003 4584613 := bbase (se 4 (by rfl) ⟨429807, by rfl⟩ : syracuseStep 4584613 = 859615) (by norm_num)
theorem B2036917 : Blo 1609003 2036917 := bbase (se 5 (by rfl) ⟨95480, by rfl⟩ : syracuseStep 2036917 = 190961) (by norm_num)
theorem B2413757 : Blo 1609003 2413757 := bbase (se 3 (by rfl) ⟨452579, by rfl⟩ : syracuseStep 2413757 = 905159) (by norm_num)
theorem B2716861 : Blo 1609003 2716861 := bbase (se 3 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 2716861 = 1018823) (by norm_num)
theorem B2413781 : Blo 1609003 2413781 := bbase (se 7 (by rfl) ⟨28286, by rfl⟩ : syracuseStep 2413781 = 56573) (by norm_num)
theorem B4412645 : Blo 1609003 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B2413805 : Blo 1609003 2413805 := bbase (se 3 (by rfl) ⟨452588, by rfl⟩ : syracuseStep 2413805 = 905177) (by norm_num)
theorem B2413829 : Blo 1609003 2413829 := bbase (se 4 (by rfl) ⟨226296, by rfl⟩ : syracuseStep 2413829 = 452593) (by norm_num)
theorem B2716949 : Blo 1609003 2716949 := bbase (se 6 (by rfl) ⟨63678, by rfl⟩ : syracuseStep 2716949 = 127357) (by norm_num)
theorem B2413853 : Blo 1609003 2413853 := bbase (se 3 (by rfl) ⟨452597, by rfl⟩ : syracuseStep 2413853 = 905195) (by norm_num)
theorem B2413877 : Blo 1609003 2413877 := bbase (se 5 (by rfl) ⟨113150, by rfl⟩ : syracuseStep 2413877 = 226301) (by norm_num)
theorem B2413901 : Blo 1609003 2413901 := bbase (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) (by norm_num)
theorem B2037089 : Blo 1609003 2037089 := bbase (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) (by norm_num)
theorem B2413925 : Blo 1609003 2413925 := bbase (se 4 (by rfl) ⟨226305, by rfl⟩ : syracuseStep 2413925 = 452611) (by norm_num)
theorem B5436773 : Blo 1609003 5436773 := bbase (se 4 (by rfl) ⟨509697, by rfl⟩ : syracuseStep 5436773 = 1019395) (by norm_num)
theorem B2413949 : Blo 1609003 2413949 := bbase (se 3 (by rfl) ⟨452615, by rfl⟩ : syracuseStep 2413949 = 905231) (by norm_num)
theorem B3437957 : Blo 1609003 3437957 := bbase (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) (by norm_num)
theorem B2446733 : Blo 1609003 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B2413973 : Blo 1609003 2413973 := bbase (se 6 (by rfl) ⟨56577, by rfl⟩ : syracuseStep 2413973 = 113155) (by norm_num)
theorem B2717077 : Blo 1609003 2717077 := bbase (se 6 (by rfl) ⟨63681, by rfl⟩ : syracuseStep 2717077 = 127363) (by norm_num)
theorem B2037145 : Blo 1609003 2037145 := bbase (se 2 (by rfl) ⟨763929, by rfl⟩ : syracuseStep 2037145 = 1527859) (by norm_num)
theorem B2413997 : Blo 1609003 2413997 := bbase (se 3 (by rfl) ⟨452624, by rfl⟩ : syracuseStep 2413997 = 905249) (by norm_num)
theorem B2414021 : Blo 1609003 2414021 := bbase (se 4 (by rfl) ⟨226314, by rfl⟩ : syracuseStep 2414021 = 452629) (by norm_num)
theorem B8148437 : Blo 1609003 8148437 := bbase (se 7 (by rfl) ⟨95489, by rfl⟩ : syracuseStep 8148437 = 190979) (by norm_num)
theorem B29382101 : Blo 1609003 29382101 := bbase (se 7 (by rfl) ⟨344321, by rfl⟩ : syracuseStep 29382101 = 688643) (by norm_num)
theorem B4077013 : Blo 1609003 4077013 := bbase (se 7 (by rfl) ⟨47777, by rfl⟩ : syracuseStep 4077013 = 95555) (by norm_num)
theorem B2414045 : Blo 1609003 2414045 := bbase (se 3 (by rfl) ⟨452633, by rfl⟩ : syracuseStep 2414045 = 905267) (by norm_num)
theorem B2717165 : Blo 1609003 2717165 := bbase (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) (by norm_num)
theorem B2414069 : Blo 1609003 2414069 := bbase (se 5 (by rfl) ⟨113159, by rfl⟩ : syracuseStep 2414069 = 226319) (by norm_num)
theorem B2037241 : Blo 1609003 2037241 := bbase (se 2 (by rfl) ⟨763965, by rfl⟩ : syracuseStep 2037241 = 1527931) (by norm_num)
theorem B2291213 : Blo 1609003 2291213 := bbase (se 3 (by rfl) ⟨429602, by rfl⟩ : syracuseStep 2291213 = 859205) (by norm_num)
theorem B2414093 : Blo 1609003 2414093 := bbase (se 3 (by rfl) ⟨452642, by rfl⟩ : syracuseStep 2414093 = 905285) (by norm_num)
theorem B3438101 : Blo 1609003 3438101 := bbase (se 6 (by rfl) ⟨80580, by rfl⟩ : syracuseStep 3438101 = 161161) (by norm_num)
theorem B5879317 : Blo 1609003 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B5805589 : Blo 1609003 5805589 := bbase (se 6 (by rfl) ⟨136068, by rfl⟩ : syracuseStep 5805589 = 272137) (by norm_num)
theorem B2414117 : Blo 1609003 2414117 := bbase (se 4 (by rfl) ⟨226323, by rfl⟩ : syracuseStep 2414117 = 452647) (by norm_num)
theorem B2414141 : Blo 1609003 2414141 := bbase (se 3 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 2414141 = 905303) (by norm_num)
theorem B4077125 : Blo 1609003 4077125 := bbase (se 4 (by rfl) ⟨382230, by rfl⟩ : syracuseStep 4077125 = 764461) (by norm_num)
theorem B2414165 : Blo 1609003 2414165 := bbase (se 8 (by rfl) ⟨14145, by rfl⟩ : syracuseStep 2414165 = 28291) (by norm_num)
theorem B2414189 : Blo 1609003 2414189 := bbase (se 3 (by rfl) ⟨452660, by rfl⟩ : syracuseStep 2414189 = 905321) (by norm_num)
theorem B2717293 : Blo 1609003 2717293 := bbase (se 3 (by rfl) ⟨509492, by rfl⟩ : syracuseStep 2717293 = 1018985) (by norm_num)
theorem B2414213 : Blo 1609003 2414213 := bbase (se 4 (by rfl) ⟨226332, by rfl⟩ : syracuseStep 2414213 = 452665) (by norm_num)
theorem B12228245 : Blo 1609003 12228245 := bbase (se 6 (by rfl) ⟨286599, by rfl⟩ : syracuseStep 12228245 = 573199) (by norm_num)
theorem B2414237 : Blo 1609003 2414237 := bbase (se 3 (by rfl) ⟨452669, by rfl⟩ : syracuseStep 2414237 = 905339) (by norm_num)
theorem B2176669 : Blo 1609003 2176669 := bbase (se 3 (by rfl) ⟨408125, by rfl⟩ : syracuseStep 2176669 = 816251) (by norm_num)
theorem B2037413 : Blo 1609003 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B2414261 : Blo 1609003 2414261 := bbase (se 5 (by rfl) ⟨113168, by rfl⟩ : syracuseStep 2414261 = 226337) (by norm_num)
theorem B2717381 : Blo 1609003 2717381 := bbase (se 4 (by rfl) ⟨254754, by rfl⟩ : syracuseStep 2717381 = 509509) (by norm_num)
theorem B2414285 : Blo 1609003 2414285 := bbase (se 3 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 2414285 = 905357) (by norm_num)
theorem B2037469 : Blo 1609003 2037469 := bbase (se 3 (by rfl) ⟨382025, by rfl⟩ : syracuseStep 2037469 = 764051) (by norm_num)
theorem B2414309 : Blo 1609003 2414309 := bbase (se 4 (by rfl) ⟨226341, by rfl⟩ : syracuseStep 2414309 = 452683) (by norm_num)
theorem B2414333 : Blo 1609003 2414333 := bbase (se 3 (by rfl) ⟨452687, by rfl⟩ : syracuseStep 2414333 = 905375) (by norm_num)
theorem B4077317 : Blo 1609003 4077317 := bbase (se 4 (by rfl) ⟨382248, by rfl⟩ : syracuseStep 4077317 = 764497) (by norm_num)
theorem B2414357 : Blo 1609003 2414357 := bbase (se 6 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 2414357 = 113173) (by norm_num)
theorem B2414381 : Blo 1609003 2414381 := bbase (se 3 (by rfl) ⟨452696, by rfl⟩ : syracuseStep 2414381 = 905393) (by norm_num)
theorem B2037565 : Blo 1609003 2037565 := bbase (se 3 (by rfl) ⟨382043, by rfl⟩ : syracuseStep 2037565 = 764087) (by norm_num)
theorem B2414405 : Blo 1609003 2414405 := bbase (se 4 (by rfl) ⟨226350, by rfl⟩ : syracuseStep 2414405 = 452701) (by norm_num)
theorem B2717509 : Blo 1609003 2717509 := bbase (se 4 (by rfl) ⟨254766, by rfl⟩ : syracuseStep 2717509 = 509533) (by norm_num)
theorem B5158741 : Blo 1609003 5158741 := bbase (se 9 (by rfl) ⟨15113, by rfl⟩ : syracuseStep 5158741 = 30227) (by norm_num)
theorem B2414429 : Blo 1609003 2414429 := bbase (se 3 (by rfl) ⟨452705, by rfl⟩ : syracuseStep 2414429 = 905411) (by norm_num)
theorem B2324333 : Blo 1609003 2324333 := bbase (se 3 (by rfl) ⟨435812, by rfl⟩ : syracuseStep 2324333 = 871625) (by norm_num)
theorem B2414453 : Blo 1609003 2414453 := bbase (se 5 (by rfl) ⟨113177, by rfl⟩ : syracuseStep 2414453 = 226355) (by norm_num)
theorem B2414477 : Blo 1609003 2414477 := bbase (se 3 (by rfl) ⟨452714, by rfl⟩ : syracuseStep 2414477 = 905429) (by norm_num)
theorem B2578333 : Blo 1609003 2578333 := bbase (se 3 (by rfl) ⟨483437, by rfl⟩ : syracuseStep 2578333 = 966875) (by norm_num)
theorem B2717597 : Blo 1609003 2717597 := bbase (se 3 (by rfl) ⟨509549, by rfl⟩ : syracuseStep 2717597 = 1019099) (by norm_num)
theorem B2414501 : Blo 1609003 2414501 := bbase (se 4 (by rfl) ⟨226359, by rfl⟩ : syracuseStep 2414501 = 452719) (by norm_num)
theorem B2414525 : Blo 1609003 2414525 := bbase (se 3 (by rfl) ⟨452723, by rfl⟩ : syracuseStep 2414525 = 905447) (by norm_num)
theorem B10311637 : Blo 1609003 10311637 := bbase (se 7 (by rfl) ⟨120839, by rfl⟩ : syracuseStep 10311637 = 241679) (by norm_num)
theorem B2414549 : Blo 1609003 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B2037737 : Blo 1609003 2037737 := bbase (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) (by norm_num)
theorem B2414573 : Blo 1609003 2414573 := bbase (se 3 (by rfl) ⟨452732, by rfl⟩ : syracuseStep 2414573 = 905465) (by norm_num)
theorem B2414597 : Blo 1609003 2414597 := bbase (se 4 (by rfl) ⟨226368, by rfl⟩ : syracuseStep 2414597 = 452737) (by norm_num)
theorem B2414621 : Blo 1609003 2414621 := bbase (se 3 (by rfl) ⟨452741, by rfl⟩ : syracuseStep 2414621 = 905483) (by norm_num)
theorem B2717725 : Blo 1609003 2717725 := bbase (se 3 (by rfl) ⟨509573, by rfl⟩ : syracuseStep 2717725 = 1019147) (by norm_num)
theorem B2037793 : Blo 1609003 2037793 := bbase (se 2 (by rfl) ⟨764172, by rfl⟩ : syracuseStep 2037793 = 1528345) (by norm_num)
theorem B12220469 : Blo 1609003 12220469 := bbase (se 5 (by rfl) ⟨572834, by rfl⟩ : syracuseStep 12220469 = 1145669) (by norm_num)
theorem B2414645 : Blo 1609003 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B1718329 : Blo 1609003 1718329 := bbase (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) (by norm_num)
theorem B2414669 : Blo 1609003 2414669 := bbase (se 3 (by rfl) ⟨452750, by rfl⟩ : syracuseStep 2414669 = 905501) (by norm_num)
theorem B4077661 : Blo 1609003 4077661 := bbase (se 3 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 4077661 = 1529123) (by norm_num)
theorem B2414693 : Blo 1609003 2414693 := bbase (se 4 (by rfl) ⟨226377, by rfl⟩ : syracuseStep 2414693 = 452755) (by norm_num)
theorem B2717813 : Blo 1609003 2717813 := bbase (se 5 (by rfl) ⟨127397, by rfl⟩ : syracuseStep 2717813 = 254795) (by norm_num)
theorem B2414717 : Blo 1609003 2414717 := bbase (se 3 (by rfl) ⟨452759, by rfl⟩ : syracuseStep 2414717 = 905519) (by norm_num)
theorem B2037889 : Blo 1609003 2037889 := bbase (se 2 (by rfl) ⟨764208, by rfl⟩ : syracuseStep 2037889 = 1528417) (by norm_num)
theorem B2414741 : Blo 1609003 2414741 := bbase (se 6 (by rfl) ⟨56595, by rfl⟩ : syracuseStep 2414741 = 113191) (by norm_num)
theorem B2414765 : Blo 1609003 2414765 := bbase (se 3 (by rfl) ⟨452768, by rfl⟩ : syracuseStep 2414765 = 905537) (by norm_num)
theorem B2414789 : Blo 1609003 2414789 := bbase (se 4 (by rfl) ⟨226386, by rfl⟩ : syracuseStep 2414789 = 452773) (by norm_num)
theorem B4077773 : Blo 1609003 4077773 := bbase (se 3 (by rfl) ⟨764582, by rfl⟩ : syracuseStep 4077773 = 1529165) (by norm_num)
theorem B2414813 : Blo 1609003 2414813 := bbase (se 3 (by rfl) ⟨452777, by rfl⟩ : syracuseStep 2414813 = 905555) (by norm_num)
theorem B2414837 : Blo 1609003 2414837 := bbase (se 5 (by rfl) ⟨113195, by rfl⟩ : syracuseStep 2414837 = 226391) (by norm_num)
theorem B2717941 : Blo 1609003 2717941 := bbase (se 5 (by rfl) ⟨127403, by rfl⟩ : syracuseStep 2717941 = 254807) (by norm_num)
theorem B3438845 : Blo 1609003 3438845 := bbase (se 3 (by rfl) ⟨644783, by rfl⟩ : syracuseStep 3438845 = 1289567) (by norm_num)
theorem B6109445 : Blo 1609003 6109445 := bbase (se 4 (by rfl) ⟨572760, by rfl⟩ : syracuseStep 6109445 = 1145521) (by norm_num)
theorem B2177285 : Blo 1609003 2177285 := bbase (se 4 (by rfl) ⟨204120, by rfl⟩ : syracuseStep 2177285 = 408241) (by norm_num)
theorem B2414861 : Blo 1609003 2414861 := bbase (se 3 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 2414861 = 905573) (by norm_num)
theorem B2414885 : Blo 1609003 2414885 := bbase (se 4 (by rfl) ⟨226395, by rfl⟩ : syracuseStep 2414885 = 452791) (by norm_num)
theorem B2038061 : Blo 1609003 2038061 := bbase (se 3 (by rfl) ⟨382136, by rfl⟩ : syracuseStep 2038061 = 764273) (by norm_num)
theorem B2414909 : Blo 1609003 2414909 := bbase (se 3 (by rfl) ⟨452795, by rfl⟩ : syracuseStep 2414909 = 905591) (by norm_num)
theorem B2718029 : Blo 1609003 2718029 := bbase (se 3 (by rfl) ⟨509630, by rfl⟩ : syracuseStep 2718029 = 1019261) (by norm_num)
theorem B2414933 : Blo 1609003 2414933 := bbase (se 10 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 2414933 = 7075) (by norm_num)
theorem B18340181 : Blo 1609003 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B2578781 : Blo 1609003 2578781 := bbase (se 3 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 2578781 = 967043) (by norm_num)
theorem B2038117 : Blo 1609003 2038117 := bbase (se 4 (by rfl) ⟨191073, by rfl⟩ : syracuseStep 2038117 = 382147) (by norm_num)
theorem B2414957 : Blo 1609003 2414957 := bbase (se 3 (by rfl) ⟨452804, by rfl⟩ : syracuseStep 2414957 = 905609) (by norm_num)
theorem B2414981 : Blo 1609003 2414981 := bbase (se 4 (by rfl) ⟨226404, by rfl⟩ : syracuseStep 2414981 = 452809) (by norm_num)
theorem B15694229 : Blo 1609003 15694229 := bbase (se 6 (by rfl) ⟨367833, by rfl⟩ : syracuseStep 15694229 = 735667) (by norm_num)
theorem B2415005 : Blo 1609003 2415005 := bbase (se 3 (by rfl) ⟨452813, by rfl⟩ : syracuseStep 2415005 = 905627) (by norm_num)
theorem B1718705 : Blo 1609003 1718705 := bbase (se 2 (by rfl) ⟨644514, by rfl⟩ : syracuseStep 1718705 = 1289029) (by norm_num)
theorem B2415029 : Blo 1609003 2415029 := bbase (se 5 (by rfl) ⟨113204, by rfl⟩ : syracuseStep 2415029 = 226409) (by norm_num)
theorem B2038213 : Blo 1609003 2038213 := bbase (se 4 (by rfl) ⟨191082, by rfl⟩ : syracuseStep 2038213 = 382165) (by norm_num)
theorem B2415053 : Blo 1609003 2415053 := bbase (se 3 (by rfl) ⟨452822, by rfl⟩ : syracuseStep 2415053 = 905645) (by norm_num)
theorem B2718157 : Blo 1609003 2718157 := bbase (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) (by norm_num)
theorem B2415077 : Blo 1609003 2415077 := bbase (se 4 (by rfl) ⟨226413, by rfl⟩ : syracuseStep 2415077 = 452827) (by norm_num)
theorem B1718777 : Blo 1609003 1718777 := bbase (se 2 (by rfl) ⟨644541, by rfl⟩ : syracuseStep 1718777 = 1289083) (by norm_num)
theorem B2415101 : Blo 1609003 2415101 := bbase (se 3 (by rfl) ⟨452831, by rfl⟩ : syracuseStep 2415101 = 905663) (by norm_num)
theorem B2415125 : Blo 1609003 2415125 := bbase (se 6 (by rfl) ⟨56604, by rfl⟩ : syracuseStep 2415125 = 113209) (by norm_num)
theorem B2718245 : Blo 1609003 2718245 := bbase (se 4 (by rfl) ⟨254835, by rfl⟩ : syracuseStep 2718245 = 509671) (by norm_num)
theorem B2415149 : Blo 1609003 2415149 := bbase (se 3 (by rfl) ⟨452840, by rfl⟩ : syracuseStep 2415149 = 905681) (by norm_num)
theorem B2415173 : Blo 1609003 2415173 := bbase (se 4 (by rfl) ⟨226422, by rfl⟩ : syracuseStep 2415173 = 452845) (by norm_num)
theorem B2415197 : Blo 1609003 2415197 := bbase (se 3 (by rfl) ⟨452849, by rfl⟩ : syracuseStep 2415197 = 905699) (by norm_num)
theorem B2038385 : Blo 1609003 2038385 := bbase (se 2 (by rfl) ⟨764394, by rfl⟩ : syracuseStep 2038385 = 1528789) (by norm_num)
theorem B13752949 : Blo 1609003 13752949 := bbase (se 5 (by rfl) ⟨644669, by rfl⟩ : syracuseStep 13752949 = 1289339) (by norm_num)
theorem B2415221 : Blo 1609003 2415221 := bbase (se 5 (by rfl) ⟨113213, by rfl⟩ : syracuseStep 2415221 = 226427) (by norm_num)
theorem B2415245 : Blo 1609003 2415245 := bbase (se 3 (by rfl) ⟨452858, by rfl⟩ : syracuseStep 2415245 = 905717) (by norm_num)
theorem B2415269 : Blo 1609003 2415269 := bbase (se 4 (by rfl) ⟨226431, by rfl⟩ : syracuseStep 2415269 = 452863) (by norm_num)
theorem B2718373 : Blo 1609003 2718373 := bbase (se 4 (by rfl) ⟨254847, by rfl⟩ : syracuseStep 2718373 = 509695) (by norm_num)
theorem B2038441 : Blo 1609003 2038441 := bbase (se 2 (by rfl) ⟨764415, by rfl⟩ : syracuseStep 2038441 = 1528831) (by norm_num)
theorem B1718965 : Blo 1609003 1718965 := bbase (se 5 (by rfl) ⟨80576, by rfl⟩ : syracuseStep 1718965 = 161153) (by norm_num)
theorem B2415293 : Blo 1609003 2415293 := bbase (se 3 (by rfl) ⟨452867, by rfl⟩ : syracuseStep 2415293 = 905735) (by norm_num)
theorem B2415317 : Blo 1609003 2415317 := bbase (se 7 (by rfl) ⟨28304, by rfl⟩ : syracuseStep 2415317 = 56609) (by norm_num)
theorem B4897493 : Blo 1609003 4897493 := bbase (se 7 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 4897493 = 114785) (by norm_num)
theorem B8149733 : Blo 1609003 8149733 := bbase (se 4 (by rfl) ⟨764037, by rfl⟩ : syracuseStep 8149733 = 1528075) (by norm_num)
theorem B2415341 : Blo 1609003 2415341 := bbase (se 3 (by rfl) ⟨452876, by rfl⟩ : syracuseStep 2415341 = 905753) (by norm_num)
theorem B2718461 : Blo 1609003 2718461 := bbase (se 3 (by rfl) ⟨509711, by rfl⟩ : syracuseStep 2718461 = 1019423) (by norm_num)
theorem B2415365 : Blo 1609003 2415365 := bbase (se 4 (by rfl) ⟨226440, by rfl⟩ : syracuseStep 2415365 = 452881) (by norm_num)
theorem B2038537 : Blo 1609003 2038537 := bbase (se 2 (by rfl) ⟨764451, by rfl⟩ : syracuseStep 2038537 = 1528903) (by norm_num)
theorem B2415389 : Blo 1609003 2415389 := bbase (se 3 (by rfl) ⟨452885, by rfl⟩ : syracuseStep 2415389 = 905771) (by norm_num)
theorem B2415413 : Blo 1609003 2415413 := bbase (se 5 (by rfl) ⟨113222, by rfl⟩ : syracuseStep 2415413 = 226445) (by norm_num)
theorem B7732037 : Blo 1609003 7732037 := bbase (se 4 (by rfl) ⟨724878, by rfl⟩ : syracuseStep 7732037 = 1449757) (by norm_num)
theorem B2415437 : Blo 1609003 2415437 := bbase (se 3 (by rfl) ⟨452894, by rfl⟩ : syracuseStep 2415437 = 905789) (by norm_num)
theorem B2415461 : Blo 1609003 2415461 := bbase (se 4 (by rfl) ⟨226449, by rfl⟩ : syracuseStep 2415461 = 452899) (by norm_num)
theorem B1719149 : Blo 1609003 1719149 := bbase (se 3 (by rfl) ⟨322340, by rfl⟩ : syracuseStep 1719149 = 644681) (by norm_num)
theorem B2415485 : Blo 1609003 2415485 := bbase (se 3 (by rfl) ⟨452903, by rfl⟩ : syracuseStep 2415485 = 905807) (by norm_num)
theorem B2415509 : Blo 1609003 2415509 := bbase (se 6 (by rfl) ⟨56613, by rfl⟩ : syracuseStep 2415509 = 113227) (by norm_num)
theorem B2292637 : Blo 1609003 2292637 := bbase (se 3 (by rfl) ⟨429869, by rfl⟩ : syracuseStep 2292637 = 859739) (by norm_num)
theorem B2415533 : Blo 1609003 2415533 := bbase (se 3 (by rfl) ⟨452912, by rfl⟩ : syracuseStep 2415533 = 905825) (by norm_num)
theorem B2038709 : Blo 1609003 2038709 := bbase (se 5 (by rfl) ⟨95564, by rfl⟩ : syracuseStep 2038709 = 191129) (by norm_num)
theorem B2415557 : Blo 1609003 2415557 := bbase (se 4 (by rfl) ⟨226458, by rfl⟩ : syracuseStep 2415557 = 452917) (by norm_num)
theorem B27884501 : Blo 1609003 27884501 := bbase (se 7 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 27884501 = 653543) (by norm_num)
theorem B9796565 : Blo 1609003 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B2415581 : Blo 1609003 2415581 := bbase (se 3 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 2415581 = 905843) (by norm_num)
theorem B3439597 : Blo 1609003 3439597 := bbase (se 3 (by rfl) ⟨644924, by rfl⟩ : syracuseStep 3439597 = 1289849) (by norm_num)
theorem B2038765 : Blo 1609003 2038765 := bbase (se 3 (by rfl) ⟨382268, by rfl⟩ : syracuseStep 2038765 = 764537) (by norm_num)
theorem B2415605 : Blo 1609003 2415605 := bbase (se 5 (by rfl) ⟨113231, by rfl⟩ : syracuseStep 2415605 = 226463) (by norm_num)
theorem B2415629 : Blo 1609003 2415629 := bbase (se 3 (by rfl) ⟨452930, by rfl⟩ : syracuseStep 2415629 = 905861) (by norm_num)
theorem B3308581 : Blo 1609003 3308581 := bbase (se 4 (by rfl) ⟨310179, by rfl⟩ : syracuseStep 3308581 = 620359) (by norm_num)
theorem B2415653 : Blo 1609003 2415653 := bbase (se 4 (by rfl) ⟨226467, by rfl⟩ : syracuseStep 2415653 = 452935) (by norm_num)
theorem B2415677 : Blo 1609003 2415677 := bbase (se 3 (by rfl) ⟨452939, by rfl⟩ : syracuseStep 2415677 = 905879) (by norm_num)
theorem B2038861 : Blo 1609003 2038861 := bbase (se 3 (by rfl) ⟨382286, by rfl⟩ : syracuseStep 2038861 = 764573) (by norm_num)
theorem B2415701 : Blo 1609003 2415701 := bbase (se 8 (by rfl) ⟨14154, by rfl⟩ : syracuseStep 2415701 = 28309) (by norm_num)
theorem B3054685 : Blo 1609003 3054685 := bbase (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) (by norm_num)
theorem B2415725 : Blo 1609003 2415725 := bbase (se 3 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 2415725 = 905897) (by norm_num)
theorem B3439741 : Blo 1609003 3439741 := bbase (se 3 (by rfl) ⟨644951, by rfl⟩ : syracuseStep 3439741 = 1289903) (by norm_num)
theorem B2415749 : Blo 1609003 2415749 := bbase (se 4 (by rfl) ⟨226476, by rfl⟩ : syracuseStep 2415749 = 452953) (by norm_num)
theorem B2415773 : Blo 1609003 2415773 := bbase (se 3 (by rfl) ⟨452957, by rfl⟩ : syracuseStep 2415773 = 905915) (by norm_num)
theorem B2415797 : Blo 1609003 2415797 := bbase (se 5 (by rfl) ⟨113240, by rfl⟩ : syracuseStep 2415797 = 226481) (by norm_num)
theorem B2415821 : Blo 1609003 2415821 := bbase (se 3 (by rfl) ⟨452966, by rfl⟩ : syracuseStep 2415821 = 905933) (by norm_num)
theorem B2415845 : Blo 1609003 2415845 := bbase (se 4 (by rfl) ⟨226485, by rfl⟩ : syracuseStep 2415845 = 452971) (by norm_num)
theorem B3054829 : Blo 1609003 3054829 := bbase (se 3 (by rfl) ⟨572780, by rfl⟩ : syracuseStep 3054829 = 1145561) (by norm_num)
theorem B2415869 : Blo 1609003 2415869 := bbase (se 3 (by rfl) ⟨452975, by rfl⟩ : syracuseStep 2415869 = 905951) (by norm_num)
theorem B2415893 : Blo 1609003 2415893 := bbase (se 6 (by rfl) ⟨56622, by rfl⟩ : syracuseStep 2415893 = 113245) (by norm_num)
theorem B2415917 : Blo 1609003 2415917 := bbase (se 3 (by rfl) ⟨452984, by rfl⟩ : syracuseStep 2415917 = 905969) (by norm_num)
theorem B2415941 : Blo 1609003 2415941 := bbase (se 4 (by rfl) ⟨226494, by rfl⟩ : syracuseStep 2415941 = 452989) (by norm_num)
theorem B2415965 : Blo 1609003 2415965 := bbase (se 3 (by rfl) ⟨452993, by rfl⟩ : syracuseStep 2415965 = 905987) (by norm_num)
theorem B2415989 : Blo 1609003 2415989 := bbase (se 5 (by rfl) ⟨113249, by rfl⟩ : syracuseStep 2415989 = 226499) (by norm_num)
theorem B3865981 : Blo 1609003 3865981 := bbase (se 3 (by rfl) ⟨724871, by rfl⟩ : syracuseStep 3865981 = 1449743) (by norm_num)
theorem B3054989 : Blo 1609003 3054989 := bbase (se 3 (by rfl) ⟨572810, by rfl⟩ : syracuseStep 3054989 = 1145621) (by norm_num)
theorem B2416013 : Blo 1609003 2416013 := bbase (se 3 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 2416013 = 906005) (by norm_num)
theorem B2416037 : Blo 1609003 2416037 := bbase (se 4 (by rfl) ⟨226503, by rfl⟩ : syracuseStep 2416037 = 453007) (by norm_num)
theorem B3620285 : Blo 1609003 3620285 := bbase (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) (by norm_num)
theorem B2416061 : Blo 1609003 2416061 := bbase (se 3 (by rfl) ⟨453011, by rfl⟩ : syracuseStep 2416061 = 906023) (by norm_num)
theorem B5430725 : Blo 1609003 5430725 := bbase (se 4 (by rfl) ⟨509130, by rfl⟩ : syracuseStep 5430725 = 1018261) (by norm_num)
theorem B2416085 : Blo 1609003 2416085 := bbase (se 7 (by rfl) ⟨28313, by rfl⟩ : syracuseStep 2416085 = 56627) (by norm_num)
theorem B2293229 : Blo 1609003 2293229 := bbase (se 3 (by rfl) ⟨429980, by rfl⟩ : syracuseStep 2293229 = 859961) (by norm_num)
theorem B2416109 : Blo 1609003 2416109 := bbase (se 3 (by rfl) ⟨453020, by rfl⟩ : syracuseStep 2416109 = 906041) (by norm_num)
theorem B3440117 : Blo 1609003 3440117 := bbase (se 5 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 3440117 = 322511) (by norm_num)
theorem B3620357 : Blo 1609003 3620357 := bbase (se 4 (by rfl) ⟨339408, by rfl⟩ : syracuseStep 3620357 = 678817) (by norm_num)
theorem B2416133 : Blo 1609003 2416133 := bbase (se 4 (by rfl) ⟨226512, by rfl⟩ : syracuseStep 2416133 = 453025) (by norm_num)
theorem B3055133 : Blo 1609003 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B2416157 : Blo 1609003 2416157 := bbase (se 3 (by rfl) ⟨453029, by rfl⟩ : syracuseStep 2416157 = 906059) (by norm_num)
theorem B2416181 : Blo 1609003 2416181 := bbase (se 5 (by rfl) ⟨113258, by rfl⟩ : syracuseStep 2416181 = 226517) (by norm_num)
theorem B2293309 : Blo 1609003 2293309 := bbase (se 3 (by rfl) ⟨429995, by rfl⟩ : syracuseStep 2293309 = 859991) (by norm_num)
theorem B3620429 : Blo 1609003 3620429 := bbase (se 3 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 3620429 = 1357661) (by norm_num)
theorem B2416205 : Blo 1609003 2416205 := bbase (se 3 (by rfl) ⟨453038, by rfl⟩ : syracuseStep 2416205 = 906077) (by norm_num)
theorem B1719901 : Blo 1609003 1719901 := bbase (se 3 (by rfl) ⟨322481, by rfl⟩ : syracuseStep 1719901 = 644963) (by norm_num)
theorem B2416229 : Blo 1609003 2416229 := bbase (se 4 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 2416229 = 453043) (by norm_num)
theorem B2416253 : Blo 1609003 2416253 := bbase (se 3 (by rfl) ⟨453047, by rfl⟩ : syracuseStep 2416253 = 906095) (by norm_num)
theorem B3620501 : Blo 1609003 3620501 := bbase (se 6 (by rfl) ⟨84855, by rfl⟩ : syracuseStep 3620501 = 169711) (by norm_num)
theorem B2449045 : Blo 1609003 2449045 := bbase (se 6 (by rfl) ⟨57399, by rfl⟩ : syracuseStep 2449045 = 114799) (by norm_num)
theorem B2416277 : Blo 1609003 2416277 := bbase (se 6 (by rfl) ⟨56631, by rfl⟩ : syracuseStep 2416277 = 113263) (by norm_num)
theorem B1719973 : Blo 1609003 1719973 := bbase (se 4 (by rfl) ⟨161247, by rfl⟩ : syracuseStep 1719973 = 322495) (by norm_num)
theorem B2416301 : Blo 1609003 2416301 := bbase (se 3 (by rfl) ⟨453056, by rfl⟩ : syracuseStep 2416301 = 906113) (by norm_num)
theorem B12385973 : Blo 1609003 12385973 := bbase (se 5 (by rfl) ⟨580592, by rfl⟩ : syracuseStep 12385973 = 1161185) (by norm_num)
theorem B2293429 : Blo 1609003 2293429 := bbase (se 5 (by rfl) ⟨107504, by rfl⟩ : syracuseStep 2293429 = 215009) (by norm_num)
theorem B7741109 : Blo 1609003 7741109 := bbase (se 5 (by rfl) ⟨362864, by rfl⟩ : syracuseStep 7741109 = 725729) (by norm_num)
theorem B2416325 : Blo 1609003 2416325 := bbase (se 4 (by rfl) ⟨226530, by rfl⟩ : syracuseStep 2416325 = 453061) (by norm_num)
theorem B1810129 : Blo 1609003 1810129 := bbase (se 2 (by rfl) ⟨678798, by rfl⟩ : syracuseStep 1810129 = 1357597) (by norm_num)
theorem B3620573 : Blo 1609003 3620573 := bbase (se 3 (by rfl) ⟨678857, by rfl⟩ : syracuseStep 3620573 = 1357715) (by norm_num)
theorem B2416349 : Blo 1609003 2416349 := bbase (se 3 (by rfl) ⟨453065, by rfl⟩ : syracuseStep 2416349 = 906131) (by norm_num)
theorem B1810165 : Blo 1609003 1810165 := bbase (se 5 (by rfl) ⟨84851, by rfl⟩ : syracuseStep 1810165 = 169703) (by norm_num)
theorem B2416373 : Blo 1609003 2416373 := bbase (se 5 (by rfl) ⟨113267, by rfl⟩ : syracuseStep 2416373 = 226535) (by norm_num)
theorem B2416397 : Blo 1609003 2416397 := bbase (se 3 (by rfl) ⟨453074, by rfl⟩ : syracuseStep 2416397 = 906149) (by norm_num)
theorem B2293525 : Blo 1609003 2293525 := bbase (se 6 (by rfl) ⟨53754, by rfl⟩ : syracuseStep 2293525 = 107509) (by norm_num)
theorem B1810201 : Blo 1609003 1810201 := bbase (se 2 (by rfl) ⟨678825, by rfl⟩ : syracuseStep 1810201 = 1357651) (by norm_num)
theorem B3620645 : Blo 1609003 3620645 := bbase (se 4 (by rfl) ⟨339435, by rfl⟩ : syracuseStep 3620645 = 678871) (by norm_num)
theorem B2416421 : Blo 1609003 2416421 := bbase (se 4 (by rfl) ⟨226539, by rfl⟩ : syracuseStep 2416421 = 453079) (by norm_num)
theorem B1810237 : Blo 1609003 1810237 := bbase (se 3 (by rfl) ⟨339419, by rfl⟩ : syracuseStep 1810237 = 678839) (by norm_num)
theorem B3055421 : Blo 1609003 3055421 := bbase (se 3 (by rfl) ⟨572891, by rfl⟩ : syracuseStep 3055421 = 1145783) (by norm_num)
theorem B2416445 : Blo 1609003 2416445 := bbase (se 3 (by rfl) ⟨453083, by rfl⟩ : syracuseStep 2416445 = 906167) (by norm_num)
theorem B2580293 : Blo 1609003 2580293 := bbase (se 4 (by rfl) ⟨241902, by rfl⟩ : syracuseStep 2580293 = 483805) (by norm_num)
theorem B88137557 : Blo 1609003 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B2416469 : Blo 1609003 2416469 := bbase (se 9 (by rfl) ⟨7079, by rfl⟩ : syracuseStep 2416469 = 14159) (by norm_num)
theorem B2064217 : Blo 1609003 2064217 := bbase (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) (by norm_num)
theorem B1720153 : Blo 1609003 1720153 := bbase (se 2 (by rfl) ⟨645057, by rfl⟩ : syracuseStep 1720153 = 1290115) (by norm_num)
theorem B1810273 : Blo 1609003 1810273 := bbase (se 2 (by rfl) ⟨678852, by rfl⟩ : syracuseStep 1810273 = 1357705) (by norm_num)
theorem B3440485 : Blo 1609003 3440485 := bbase (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) (by norm_num)
theorem B3620717 : Blo 1609003 3620717 := bbase (se 3 (by rfl) ⟨678884, by rfl⟩ : syracuseStep 3620717 = 1357769) (by norm_num)
theorem B2416493 : Blo 1609003 2416493 := bbase (se 3 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 2416493 = 906185) (by norm_num)
theorem B5431157 : Blo 1609003 5431157 := bbase (se 5 (by rfl) ⟨254585, by rfl⟩ : syracuseStep 5431157 = 509171) (by norm_num)
theorem B1810309 : Blo 1609003 1810309 := bbase (se 4 (by rfl) ⟨169716, by rfl⟩ : syracuseStep 1810309 = 339433) (by norm_num)
theorem B1810345 : Blo 1609003 1810345 := bbase (se 2 (by rfl) ⟨678879, by rfl⟩ : syracuseStep 1810345 = 1357759) (by norm_num)
theorem B3620789 : Blo 1609003 3620789 := bbase (se 5 (by rfl) ⟨169724, by rfl⟩ : syracuseStep 3620789 = 339449) (by norm_num)
theorem B3866557 : Blo 1609003 3866557 := bbase (se 3 (by rfl) ⟨724979, by rfl⟩ : syracuseStep 3866557 = 1449959) (by norm_num)
theorem B8257477 : Blo 1609003 8257477 := bbase (se 4 (by rfl) ⟨774138, by rfl⟩ : syracuseStep 8257477 = 1548277) (by norm_num)
theorem B2580421 : Blo 1609003 2580421 := bbase (se 4 (by rfl) ⟨241914, by rfl⟩ : syracuseStep 2580421 = 483829) (by norm_num)
theorem B4587461 : Blo 1609003 4587461 := bbase (se 4 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 4587461 = 860149) (by norm_num)
theorem B1810381 : Blo 1609003 1810381 := bbase (se 3 (by rfl) ⟨339446, by rfl⟩ : syracuseStep 1810381 = 678893) (by norm_num)
theorem B3055573 : Blo 1609003 3055573 := bbase (se 7 (by rfl) ⟨35807, by rfl⟩ : syracuseStep 3055573 = 71615) (by norm_num)
theorem B1810417 : Blo 1609003 1810417 := bbase (se 2 (by rfl) ⟨678906, by rfl⟩ : syracuseStep 1810417 = 1357813) (by norm_num)
theorem B8151029 : Blo 1609003 8151029 := bbase (se 5 (by rfl) ⟨382079, by rfl⟩ : syracuseStep 8151029 = 764159) (by norm_num)
theorem B3620861 : Blo 1609003 3620861 := bbase (se 3 (by rfl) ⟨678911, by rfl⟩ : syracuseStep 3620861 = 1357823) (by norm_num)
theorem B1810435 : Blo 1609003 1810435 := bstep (se 1 (by rfl) ⟨1357826, by rfl⟩ : syracuseStep 1810435 = 2715653) B2715653
theorem B3055619 : Blo 1609003 3055619 := bstep (se 1 (by rfl) ⟨2291714, by rfl⟩ : syracuseStep 3055619 = 4583429) B4583429
theorem B4644881 : Blo 1609003 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B4587587 : Blo 1609003 4587587 := bstep (se 1 (by rfl) ⟨3440690, by rfl⟩ : syracuseStep 4587587 = 6881381) B6881381
theorem B5431373 : Blo 1609003 5431373 := bstep (se 3 (by rfl) ⟨1018382, by rfl⟩ : syracuseStep 5431373 = 2036765) B2036765
theorem B5431427 : Blo 1609003 5431427 := bstep (se 1 (by rfl) ⟨4073570, by rfl⟩ : syracuseStep 5431427 = 8147141) B8147141
theorem B1810579 : Blo 1609003 1810579 := bstep (se 1 (by rfl) ⟨1357934, by rfl⟩ : syracuseStep 1810579 = 2715869) B2715869
theorem B3621041 : Blo 1609003 3621041 := bstep (se 2 (by rfl) ⟨1357890, by rfl⟩ : syracuseStep 3621041 = 2715781) B2715781
theorem B3621059 : Blo 1609003 3621059 := bstep (se 1 (by rfl) ⟨2715794, by rfl⟩ : syracuseStep 3621059 = 5431589) B5431589
theorem B8257805 : Blo 1609003 8257805 := bstep (se 3 (by rfl) ⟨1548338, by rfl⟩ : syracuseStep 8257805 = 3096677) B3096677
theorem B1810723 : Blo 1609003 1810723 := bstep (se 1 (by rfl) ⟨1358042, by rfl⟩ : syracuseStep 1810723 = 2716085) B2716085
theorem B3055907 : Blo 1609003 3055907 := bstep (se 1 (by rfl) ⟨2291930, by rfl⟩ : syracuseStep 3055907 = 4583861) B4583861
theorem B5431697 : Blo 1609003 5431697 := bstep (se 2 (by rfl) ⟨2036886, by rfl⟩ : syracuseStep 5431697 = 4073773) B4073773
theorem B4350353 : Blo 1609003 4350353 := bstep (se 2 (by rfl) ⟨1631382, by rfl⟩ : syracuseStep 4350353 = 3262765) B3262765
theorem B1810867 : Blo 1609003 1810867 := bstep (se 1 (by rfl) ⟨1358150, by rfl⟩ : syracuseStep 1810867 = 2716301) B2716301
theorem B3621329 : Blo 1609003 3621329 := bstep (se 2 (by rfl) ⟨1357998, by rfl⟩ : syracuseStep 3621329 = 2715997) B2715997
theorem B3621347 : Blo 1609003 3621347 := bstep (se 1 (by rfl) ⟨2716010, by rfl⟩ : syracuseStep 3621347 = 5432021) B5432021
theorem B2064899 : Blo 1609003 2064899 := bstep (se 1 (by rfl) ⟨1548674, by rfl⟩ : syracuseStep 2064899 = 3097349) B3097349
theorem B1811011 : Blo 1609003 1811011 := bstep (se 1 (by rfl) ⟨1358258, by rfl⟩ : syracuseStep 1811011 = 2716517) B2716517
theorem B7070321 : Blo 1609003 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B18334349 : Blo 1609003 18334349 := bstep (se 3 (by rfl) ⟨3437690, by rfl⟩ : syracuseStep 18334349 = 6875381) B6875381
theorem B11010737 : Blo 1609003 11010737 := bstep (se 2 (by rfl) ⟨4129026, by rfl⟩ : syracuseStep 11010737 = 8258053) B8258053
theorem B1811155 : Blo 1609003 1811155 := bstep (se 1 (by rfl) ⟨1358366, by rfl⟩ : syracuseStep 1811155 = 2716733) B2716733
theorem B3621617 : Blo 1609003 3621617 := bstep (se 2 (by rfl) ⟨1358106, by rfl⟩ : syracuseStep 3621617 = 2716213) B2716213
theorem B3621635 : Blo 1609003 3621635 := bstep (se 1 (by rfl) ⟨2716226, by rfl⟩ : syracuseStep 3621635 = 5432453) B5432453
theorem B2941763 : Blo 1609003 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B1811299 : Blo 1609003 1811299 := bstep (se 1 (by rfl) ⟨1358474, by rfl⟩ : syracuseStep 1811299 = 2716949) B2716949
theorem B5432237 : Blo 1609003 5432237 := bstep (se 3 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 5432237 = 2037089) B2037089
theorem B9167813 : Blo 1609003 9167813 := bstep (se 4 (by rfl) ⟨859482, by rfl⟩ : syracuseStep 9167813 = 1718965) B1718965
theorem B5506001 : Blo 1609003 5506001 := bstep (se 2 (by rfl) ⟨2064750, by rfl⟩ : syracuseStep 5506001 = 4129501) B4129501
theorem B5432291 : Blo 1609003 5432291 := bstep (se 1 (by rfl) ⟨4074218, by rfl⟩ : syracuseStep 5432291 = 8148437) B8148437
theorem B19588067 : Blo 1609003 19588067 := bstep (se 1 (by rfl) ⟨14691050, by rfl⟩ : syracuseStep 19588067 = 29382101) B29382101
theorem B1811443 : Blo 1609003 1811443 := bstep (se 1 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 1811443 = 2717165) B2717165
theorem B3621905 : Blo 1609003 3621905 := bstep (se 2 (by rfl) ⟨1358214, by rfl⟩ : syracuseStep 3621905 = 2716429) B2716429
theorem B3621923 : Blo 1609003 3621923 := bstep (se 1 (by rfl) ⟨2716442, by rfl⟩ : syracuseStep 3621923 = 5432885) B5432885
theorem B8152163 : Blo 1609003 8152163 := bstep (se 1 (by rfl) ⟨6114122, by rfl⟩ : syracuseStep 8152163 = 12228245) B12228245
theorem B1811587 : Blo 1609003 1811587 := bstep (se 1 (by rfl) ⟨1358690, by rfl⟩ : syracuseStep 1811587 = 2717381) B2717381
theorem B2901187 : Blo 1609003 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B3056849 : Blo 1609003 3056849 := bstep (se 2 (by rfl) ⟨1146318, by rfl⟩ : syracuseStep 3056849 = 2292637) B2292637
theorem B5432561 : Blo 1609003 5432561 := bstep (se 2 (by rfl) ⟨2037210, by rfl⟩ : syracuseStep 5432561 = 4074421) B4074421
theorem B1811731 : Blo 1609003 1811731 := bstep (se 1 (by rfl) ⟨1358798, by rfl⟩ : syracuseStep 1811731 = 2717597) B2717597
theorem B3622193 : Blo 1609003 3622193 := bstep (se 2 (by rfl) ⟨1358322, by rfl⟩ : syracuseStep 3622193 = 2716645) B2716645
theorem B3622211 : Blo 1609003 3622211 := bstep (se 1 (by rfl) ⟨2716658, by rfl⟩ : syracuseStep 3622211 = 5433317) B5433317
theorem B5506435 : Blo 1609003 5506435 := bstep (se 1 (by rfl) ⟨4129826, by rfl⟩ : syracuseStep 5506435 = 8259653) B8259653
theorem B1811875 : Blo 1609003 1811875 := bstep (se 1 (by rfl) ⟨1358906, by rfl⟩ : syracuseStep 1811875 = 2717813) B2717813
theorem B12232133 : Blo 1609003 12232133 := bstep (se 4 (by rfl) ⟨1146762, by rfl⟩ : syracuseStep 12232133 = 2293525) B2293525
theorem B4072913 : Blo 1609003 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B4072963 : Blo 1609003 4072963 := bstep (se 1 (by rfl) ⟨3054722, by rfl⟩ : syracuseStep 4072963 = 6109445) B6109445
theorem B6112817 : Blo 1609003 6112817 := bstep (se 2 (by rfl) ⟨2292306, by rfl⟩ : syracuseStep 6112817 = 4584613) B4584613
theorem B1812019 : Blo 1609003 1812019 := bstep (se 1 (by rfl) ⟨1359014, by rfl⟩ : syracuseStep 1812019 = 2718029) B2718029
theorem B5506627 : Blo 1609003 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B3622481 : Blo 1609003 3622481 := bstep (se 2 (by rfl) ⟨1358430, by rfl⟩ : syracuseStep 3622481 = 2716861) B2716861
theorem B3622499 : Blo 1609003 3622499 := bstep (se 1 (by rfl) ⟨2716874, by rfl⟩ : syracuseStep 3622499 = 5433749) B5433749
theorem B10462819 : Blo 1609003 10462819 := bstep (se 1 (by rfl) ⟨7847114, by rfl⟩ : syracuseStep 10462819 = 15694229) B15694229
theorem B9168497 : Blo 1609003 9168497 := bstep (se 2 (by rfl) ⟨3438186, by rfl⟩ : syracuseStep 9168497 = 6876373) B6876373
theorem B4073105 : Blo 1609003 4073105 := bstep (se 2 (by rfl) ⟨1527414, by rfl⟩ : syracuseStep 4073105 = 3054829) B3054829
theorem B1812163 : Blo 1609003 1812163 := bstep (se 1 (by rfl) ⟨1359122, by rfl⟩ : syracuseStep 1812163 = 2718245) B2718245
theorem B5433101 : Blo 1609003 5433101 := bstep (se 3 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 5433101 = 2037413) B2037413
theorem B5433155 : Blo 1609003 5433155 := bstep (se 1 (by rfl) ⟨4074866, by rfl⟩ : syracuseStep 5433155 = 8149733) B8149733
theorem B5154641 : Blo 1609003 5154641 := bstep (se 2 (by rfl) ⟨1932990, by rfl⟩ : syracuseStep 5154641 = 3865981) B3865981
theorem B1812307 : Blo 1609003 1812307 := bstep (se 1 (by rfl) ⟨1359230, by rfl⟩ : syracuseStep 1812307 = 2718461) B2718461
theorem B5801827 : Blo 1609003 5801827 := bstep (se 1 (by rfl) ⟨4351370, by rfl⟩ : syracuseStep 5801827 = 8702741) B8702741
theorem B14681969 : Blo 1609003 14681969 := bstep (se 2 (by rfl) ⟨5505738, by rfl⟩ : syracuseStep 14681969 = 11011477) B11011477
theorem B3622769 : Blo 1609003 3622769 := bstep (se 2 (by rfl) ⟨1358538, by rfl⟩ : syracuseStep 3622769 = 2717077) B2717077
theorem B5154691 : Blo 1609003 5154691 := bstep (se 1 (by rfl) ⟨3866018, by rfl⟩ : syracuseStep 5154691 = 7732037) B7732037
theorem B3622787 : Blo 1609003 3622787 := bstep (se 1 (by rfl) ⟨2717090, by rfl⟩ : syracuseStep 3622787 = 5434181) B5434181
theorem B8152973 : Blo 1609003 8152973 := bstep (se 3 (by rfl) ⟨1528682, by rfl⟩ : syracuseStep 8152973 = 3057365) B3057365
theorem B18589667 : Blo 1609003 18589667 := bstep (se 1 (by rfl) ⟨13942250, by rfl⟩ : syracuseStep 18589667 = 27884501) B27884501
theorem B6531043 : Blo 1609003 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B5801969 : Blo 1609003 5801969 := bstep (se 2 (by rfl) ⟨2175738, by rfl⟩ : syracuseStep 5801969 = 4351477) B4351477
theorem B4130833 : Blo 1609003 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B2902051 : Blo 1609003 2902051 := bstep (se 1 (by rfl) ⟨2176538, by rfl⟩ : syracuseStep 2902051 = 4353077) B4353077
theorem B17401925 : Blo 1609003 17401925 := bstep (se 4 (by rfl) ⟨1631430, by rfl⟩ : syracuseStep 17401925 = 3262861) B3262861
theorem B5433425 : Blo 1609003 5433425 := bstep (se 2 (by rfl) ⟨2037534, by rfl⟩ : syracuseStep 5433425 = 4075069) B4075069
theorem B3057745 : Blo 1609003 3057745 := bstep (se 2 (by rfl) ⟨1146654, by rfl⟩ : syracuseStep 3057745 = 2293309) B2293309
theorem B2754643 : Blo 1609003 2754643 := bstep (se 1 (by rfl) ⟨2065982, by rfl⟩ : syracuseStep 2754643 = 4131965) B4131965
theorem B4130947 : Blo 1609003 4130947 := bstep (se 1 (by rfl) ⟨3098210, by rfl⟩ : syracuseStep 4130947 = 6196421) B6196421
theorem B3623057 : Blo 1609003 3623057 := bstep (se 2 (by rfl) ⟨1358646, by rfl⟩ : syracuseStep 3623057 = 2717293) B2717293
theorem B3623075 : Blo 1609003 3623075 := bstep (se 1 (by rfl) ⟨2717306, by rfl⟩ : syracuseStep 3623075 = 5434613) B5434613
theorem B17410229 : Blo 1609003 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B2902225 : Blo 1609003 2902225 := bstep (se 2 (by rfl) ⟨1088334, by rfl⟩ : syracuseStep 2902225 = 2176669) B2176669
theorem B3057905 : Blo 1609003 3057905 := bstep (se 2 (by rfl) ⟨1146714, by rfl⟩ : syracuseStep 3057905 = 2293429) B2293429
theorem B2722097 : Blo 1609003 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B12912965 : Blo 1609003 12912965 := bstep (se 4 (by rfl) ⟨1210590, by rfl⟩ : syracuseStep 12912965 = 2421181) B2421181
theorem B5802317 : Blo 1609003 5802317 := bstep (se 3 (by rfl) ⟨1087934, by rfl⟩ : syracuseStep 5802317 = 2175869) B2175869
theorem B3869009 : Blo 1609003 3869009 := bstep (se 2 (by rfl) ⟨1450878, by rfl⟩ : syracuseStep 3869009 = 2901757) B2901757
theorem B3623345 : Blo 1609003 3623345 := bstep (se 2 (by rfl) ⟨1358754, by rfl⟩ : syracuseStep 3623345 = 2717509) B2717509
theorem B3623363 : Blo 1609003 3623363 := bstep (se 1 (by rfl) ⟨2717522, by rfl⟩ : syracuseStep 3623363 = 5435045) B5435045
theorem B5155409 : Blo 1609003 5155409 := bstep (se 2 (by rfl) ⟨1933278, by rfl⟩ : syracuseStep 5155409 = 3866557) B3866557
theorem B5433965 : Blo 1609003 5433965 := bstep (se 3 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 5433965 = 2037737) B2037737
theorem B13748849 : Blo 1609003 13748849 := bstep (se 2 (by rfl) ⟨5155818, by rfl⟩ : syracuseStep 13748849 = 10311637) B10311637
theorem B4074097 : Blo 1609003 4074097 := bstep (se 2 (by rfl) ⟨1527786, by rfl⟩ : syracuseStep 4074097 = 3055573) B3055573
theorem B3058307 : Blo 1609003 3058307 := bstep (se 1 (by rfl) ⟨2293730, by rfl⟩ : syracuseStep 3058307 = 4587461) B4587461
theorem B5434019 : Blo 1609003 5434019 := bstep (se 1 (by rfl) ⟨4075514, by rfl⟩ : syracuseStep 5434019 = 8151029) B8151029
theorem B3623633 : Blo 1609003 3623633 := bstep (se 2 (by rfl) ⟨1358862, by rfl⟩ : syracuseStep 3623633 = 2717725) B2717725
theorem B3623651 : Blo 1609003 3623651 := bstep (se 1 (by rfl) ⟨2717738, by rfl⟩ : syracuseStep 3623651 = 5435477) B5435477
theorem B2755313 : Blo 1609003 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B4074371 : Blo 1609003 4074371 := bstep (se 1 (by rfl) ⟨3055778, by rfl⟩ : syracuseStep 4074371 = 6111557) B6111557
theorem B5434289 : Blo 1609003 5434289 := bstep (se 2 (by rfl) ⟨2037858, by rfl⟩ : syracuseStep 5434289 = 4075717) B4075717
theorem B18328517 : Blo 1609003 18328517 := bstep (se 4 (by rfl) ⟨1718298, by rfl⟩ : syracuseStep 18328517 = 3436597) B3436597
theorem B6114275 : Blo 1609003 6114275 := bstep (se 1 (by rfl) ⟨4585706, by rfl⟩ : syracuseStep 6114275 = 9171413) B9171413
theorem B3623921 : Blo 1609003 3623921 := bstep (se 2 (by rfl) ⟨1358970, by rfl⟩ : syracuseStep 3623921 = 2717941) B2717941
theorem B4582403 : Blo 1609003 4582403 := bstep (se 1 (by rfl) ⟨3436802, by rfl⟩ : syracuseStep 4582403 = 6873605) B6873605
theorem B3623939 : Blo 1609003 3623939 := bstep (se 1 (by rfl) ⟨2717954, by rfl⟩ : syracuseStep 3623939 = 5435909) B5435909
theorem B9169955 : Blo 1609003 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B4074563 : Blo 1609003 4074563 := bstep (se 1 (by rfl) ⟨3055922, by rfl⟩ : syracuseStep 4074563 = 6111845) B6111845
theorem B5155921 : Blo 1609003 5155921 := bstep (se 2 (by rfl) ⟨1933470, by rfl⟩ : syracuseStep 5155921 = 3866941) B3866941
theorem B1961059 : Blo 1609003 1961059 := bstep (se 1 (by rfl) ⟨1470794, by rfl⟩ : syracuseStep 1961059 = 2941589) B2941589
theorem B10595461 : Blo 1609003 10595461 := bstep (se 4 (by rfl) ⟨993324, by rfl⟩ : syracuseStep 10595461 = 1986649) B1986649
theorem B6876323 : Blo 1609003 6876323 := bstep (se 1 (by rfl) ⟨5157242, by rfl⟩ : syracuseStep 6876323 = 10314485) B10314485
theorem B4246723 : Blo 1609003 4246723 := bstep (se 1 (by rfl) ⟨3185042, by rfl⟩ : syracuseStep 4246723 = 6370085) B6370085
theorem B20638961 : Blo 1609003 20638961 := bstep (se 2 (by rfl) ⟨7739610, by rfl⟩ : syracuseStep 20638961 = 15479221) B15479221
theorem B3624209 : Blo 1609003 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B3624227 : Blo 1609003 3624227 := bstep (se 1 (by rfl) ⟨2718170, by rfl⟩ : syracuseStep 3624227 = 5436341) B5436341
theorem B1609011 : Blo 1609003 1609011 := bstep (se 1 (by rfl) ⟨1206758, by rfl⟩ : syracuseStep 1609011 = 2413517) B2413517
theorem B1609027 : Blo 1609003 1609027 := bstep (se 1 (by rfl) ⟨1206770, by rfl⟩ : syracuseStep 1609027 = 2413541) B2413541
theorem B1609043 : Blo 1609003 1609043 := bstep (se 1 (by rfl) ⟨1206782, by rfl⟩ : syracuseStep 1609043 = 2413565) B2413565
theorem B1609059 : Blo 1609003 1609059 := bstep (se 1 (by rfl) ⟨1206794, by rfl⟩ : syracuseStep 1609059 = 2413589) B2413589
theorem B1609075 : Blo 1609003 1609075 := bstep (se 1 (by rfl) ⟨1206806, by rfl⟩ : syracuseStep 1609075 = 2413613) B2413613
theorem B1609091 : Blo 1609003 1609091 := bstep (se 1 (by rfl) ⟨1206818, by rfl⟩ : syracuseStep 1609091 = 2413637) B2413637
theorem B1609107 : Blo 1609003 1609107 := bstep (se 1 (by rfl) ⟨1206830, by rfl⟩ : syracuseStep 1609107 = 2413661) B2413661
theorem B1609123 : Blo 1609003 1609123 := bstep (se 1 (by rfl) ⟨1206842, by rfl⟩ : syracuseStep 1609123 = 2413685) B2413685
theorem B1609139 : Blo 1609003 1609139 := bstep (se 1 (by rfl) ⟨1206854, by rfl⟩ : syracuseStep 1609139 = 2413709) B2413709
theorem B1609155 : Blo 1609003 1609155 := bstep (se 1 (by rfl) ⟨1206866, by rfl⟩ : syracuseStep 1609155 = 2413733) B2413733
theorem B5434829 : Blo 1609003 5434829 := bstep (se 3 (by rfl) ⟨1019030, by rfl⟩ : syracuseStep 5434829 = 2038061) B2038061
theorem B1609171 : Blo 1609003 1609171 := bstep (se 1 (by rfl) ⟨1206878, by rfl⟩ : syracuseStep 1609171 = 2413757) B2413757
theorem B1609187 : Blo 1609003 1609187 := bstep (se 1 (by rfl) ⟨1206890, by rfl⟩ : syracuseStep 1609187 = 2413781) B2413781
theorem B18337265 : Blo 1609003 18337265 := bstep (se 2 (by rfl) ⟨6876474, by rfl⟩ : syracuseStep 18337265 = 13752949) B13752949
theorem B1609203 : Blo 1609003 1609203 := bstep (se 1 (by rfl) ⟨1206902, by rfl⟩ : syracuseStep 1609203 = 2413805) B2413805
theorem B1609219 : Blo 1609003 1609219 := bstep (se 1 (by rfl) ⟨1206914, by rfl⟩ : syracuseStep 1609219 = 2413829) B2413829
theorem B5434883 : Blo 1609003 5434883 := bstep (se 1 (by rfl) ⟨4076162, by rfl⟩ : syracuseStep 5434883 = 8152325) B8152325
theorem B1609235 : Blo 1609003 1609235 := bstep (se 1 (by rfl) ⟨1206926, by rfl⟩ : syracuseStep 1609235 = 2413853) B2413853
theorem B1609251 : Blo 1609003 1609251 := bstep (se 1 (by rfl) ⟨1206938, by rfl⟩ : syracuseStep 1609251 = 2413877) B2413877
theorem B3624497 : Blo 1609003 3624497 := bstep (se 2 (by rfl) ⟨1359186, by rfl⟩ : syracuseStep 3624497 = 2718373) B2718373
theorem B1609267 : Blo 1609003 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B1609283 : Blo 1609003 1609283 := bstep (se 1 (by rfl) ⟨1206962, by rfl⟩ : syracuseStep 1609283 = 2413925) B2413925
theorem B3624515 : Blo 1609003 3624515 := bstep (se 1 (by rfl) ⟨2718386, by rfl⟩ : syracuseStep 3624515 = 5436773) B5436773
theorem B1609299 : Blo 1609003 1609299 := bstep (se 1 (by rfl) ⟨1206974, by rfl⟩ : syracuseStep 1609299 = 2413949) B2413949
theorem B1609315 : Blo 1609003 1609315 := bstep (se 1 (by rfl) ⟨1206986, by rfl⟩ : syracuseStep 1609315 = 2413973) B2413973
theorem B1609331 : Blo 1609003 1609331 := bstep (se 1 (by rfl) ⟨1206998, by rfl⟩ : syracuseStep 1609331 = 2413997) B2413997
theorem B1609347 : Blo 1609003 1609347 := bstep (se 1 (by rfl) ⟨1207010, by rfl⟩ : syracuseStep 1609347 = 2414021) B2414021
theorem B1609363 : Blo 1609003 1609363 := bstep (se 1 (by rfl) ⟨1207022, by rfl⟩ : syracuseStep 1609363 = 2414045) B2414045
theorem B1609379 : Blo 1609003 1609379 := bstep (se 1 (by rfl) ⟨1207034, by rfl⟩ : syracuseStep 1609379 = 2414069) B2414069
theorem B8261297 : Blo 1609003 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B1609395 : Blo 1609003 1609395 := bstep (se 1 (by rfl) ⟨1207046, by rfl⟩ : syracuseStep 1609395 = 2414093) B2414093
theorem B2715329 : Blo 1609003 2715329 := bstep (se 2 (by rfl) ⟨1018248, by rfl⟩ : syracuseStep 2715329 = 2036497) B2036497
theorem B1609411 : Blo 1609003 1609411 := bstep (se 1 (by rfl) ⟨1207058, by rfl⟩ : syracuseStep 1609411 = 2414117) B2414117
theorem B6524621 : Blo 1609003 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B1609427 : Blo 1609003 1609427 := bstep (se 1 (by rfl) ⟨1207070, by rfl⟩ : syracuseStep 1609427 = 2414141) B2414141
theorem B1609443 : Blo 1609003 1609443 := bstep (se 1 (by rfl) ⟨1207082, by rfl⟩ : syracuseStep 1609443 = 2414165) B2414165
theorem B1609459 : Blo 1609003 1609459 := bstep (se 1 (by rfl) ⟨1207094, by rfl⟩ : syracuseStep 1609459 = 2414189) B2414189
theorem B1609475 : Blo 1609003 1609475 := bstep (se 1 (by rfl) ⟨1207106, by rfl⟩ : syracuseStep 1609475 = 2414213) B2414213
theorem B5435153 : Blo 1609003 5435153 := bstep (se 2 (by rfl) ⟨2038182, by rfl⟩ : syracuseStep 5435153 = 4076365) B4076365
theorem B1609491 : Blo 1609003 1609491 := bstep (se 1 (by rfl) ⟨1207118, by rfl⟩ : syracuseStep 1609491 = 2414237) B2414237
theorem B1609507 : Blo 1609003 1609507 := bstep (se 1 (by rfl) ⟨1207130, by rfl⟩ : syracuseStep 1609507 = 2414261) B2414261
theorem B4583213 : Blo 1609003 4583213 := bstep (se 3 (by rfl) ⟨859352, by rfl⟩ : syracuseStep 4583213 = 1718705) B1718705
theorem B1609523 : Blo 1609003 1609523 := bstep (se 1 (by rfl) ⟨1207142, by rfl⟩ : syracuseStep 1609523 = 2414285) B2414285
theorem B2715457 : Blo 1609003 2715457 := bstep (se 2 (by rfl) ⟨1018296, by rfl⟩ : syracuseStep 2715457 = 2036593) B2036593
theorem B1609539 : Blo 1609003 1609539 := bstep (se 1 (by rfl) ⟨1207154, by rfl⟩ : syracuseStep 1609539 = 2414309) B2414309
theorem B1609555 : Blo 1609003 1609555 := bstep (se 1 (by rfl) ⟨1207166, by rfl⟩ : syracuseStep 1609555 = 2414333) B2414333
theorem B2715491 : Blo 1609003 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B1609571 : Blo 1609003 1609571 := bstep (se 1 (by rfl) ⟨1207178, by rfl⟩ : syracuseStep 1609571 = 2414357) B2414357
theorem B1609587 : Blo 1609003 1609587 := bstep (se 1 (by rfl) ⟨1207190, by rfl⟩ : syracuseStep 1609587 = 2414381) B2414381
theorem B1609603 : Blo 1609003 1609603 := bstep (se 1 (by rfl) ⟨1207202, by rfl⟩ : syracuseStep 1609603 = 2414405) B2414405
theorem B1609619 : Blo 1609003 1609619 := bstep (se 1 (by rfl) ⟨1207214, by rfl⟩ : syracuseStep 1609619 = 2414429) B2414429
theorem B1609635 : Blo 1609003 1609635 := bstep (se 1 (by rfl) ⟨1207226, by rfl⟩ : syracuseStep 1609635 = 2414453) B2414453
theorem B1609651 : Blo 1609003 1609651 := bstep (se 1 (by rfl) ⟨1207238, by rfl⟩ : syracuseStep 1609651 = 2414477) B2414477
theorem B1609667 : Blo 1609003 1609667 := bstep (se 1 (by rfl) ⟨1207250, by rfl⟩ : syracuseStep 1609667 = 2414501) B2414501
theorem B6115277 : Blo 1609003 6115277 := bstep (se 3 (by rfl) ⟨1146614, by rfl⟩ : syracuseStep 6115277 = 2293229) B2293229
theorem B1609683 : Blo 1609003 1609683 := bstep (se 1 (by rfl) ⟨1207262, by rfl⟩ : syracuseStep 1609683 = 2414525) B2414525
theorem B2715619 : Blo 1609003 2715619 := bstep (se 1 (by rfl) ⟨2036714, by rfl⟩ : syracuseStep 2715619 = 4073429) B4073429
theorem B1609699 : Blo 1609003 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B4583405 : Blo 1609003 4583405 := bstep (se 3 (by rfl) ⟨859388, by rfl⟩ : syracuseStep 4583405 = 1718777) B1718777
theorem B4075505 : Blo 1609003 4075505 := bstep (se 2 (by rfl) ⟨1528314, by rfl⟩ : syracuseStep 4075505 = 3056629) B3056629
theorem B1609715 : Blo 1609003 1609715 := bstep (se 1 (by rfl) ⟨1207286, by rfl⟩ : syracuseStep 1609715 = 2414573) B2414573
theorem B1609731 : Blo 1609003 1609731 := bstep (se 1 (by rfl) ⟨1207298, by rfl⟩ : syracuseStep 1609731 = 2414597) B2414597
theorem B1609747 : Blo 1609003 1609747 := bstep (se 1 (by rfl) ⟨1207310, by rfl⟩ : syracuseStep 1609747 = 2414621) B2414621
theorem B34820117 : Blo 1609003 34820117 := bstep (se 6 (by rfl) ⟨816096, by rfl⟩ : syracuseStep 34820117 = 1632193) B1632193
theorem B8146979 : Blo 1609003 8146979 := bstep (se 1 (by rfl) ⟨6110234, by rfl⟩ : syracuseStep 8146979 = 12220469) B12220469
theorem B1609763 : Blo 1609003 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B4075555 : Blo 1609003 4075555 := bstep (se 1 (by rfl) ⟨3056666, by rfl⟩ : syracuseStep 4075555 = 6113333) B6113333
theorem B4411441 : Blo 1609003 4411441 := bstep (se 2 (by rfl) ⟨1654290, by rfl⟩ : syracuseStep 4411441 = 3308581) B3308581
theorem B1609779 : Blo 1609003 1609779 := bstep (se 1 (by rfl) ⟨1207334, by rfl⟩ : syracuseStep 1609779 = 2414669) B2414669
theorem B1609795 : Blo 1609003 1609795 := bstep (se 1 (by rfl) ⟨1207346, by rfl⟩ : syracuseStep 1609795 = 2414693) B2414693
theorem B1609811 : Blo 1609003 1609811 := bstep (se 1 (by rfl) ⟨1207358, by rfl⟩ : syracuseStep 1609811 = 2414717) B2414717
theorem B1609827 : Blo 1609003 1609827 := bstep (se 1 (by rfl) ⟨1207370, by rfl⟩ : syracuseStep 1609827 = 2414741) B2414741
theorem B2715761 : Blo 1609003 2715761 := bstep (se 2 (by rfl) ⟨1018410, by rfl⟩ : syracuseStep 2715761 = 2036821) B2036821
theorem B1609843 : Blo 1609003 1609843 := bstep (se 1 (by rfl) ⟨1207382, by rfl⟩ : syracuseStep 1609843 = 2414765) B2414765
theorem B1609859 : Blo 1609003 1609859 := bstep (se 1 (by rfl) ⟨1207394, by rfl⟩ : syracuseStep 1609859 = 2414789) B2414789
theorem B1609875 : Blo 1609003 1609875 := bstep (se 1 (by rfl) ⟨1207406, by rfl⟩ : syracuseStep 1609875 = 2414813) B2414813
theorem B1609891 : Blo 1609003 1609891 := bstep (se 1 (by rfl) ⟨1207418, by rfl⟩ : syracuseStep 1609891 = 2414837) B2414837
theorem B5157037 : Blo 1609003 5157037 := bstep (se 3 (by rfl) ⟨966944, by rfl⟩ : syracuseStep 5157037 = 1933889) B1933889
theorem B4075697 : Blo 1609003 4075697 := bstep (se 2 (by rfl) ⟨1528386, by rfl⟩ : syracuseStep 4075697 = 3056773) B3056773
theorem B1609907 : Blo 1609003 1609907 := bstep (se 1 (by rfl) ⟨1207430, by rfl⟩ : syracuseStep 1609907 = 2414861) B2414861
theorem B1609923 : Blo 1609003 1609923 := bstep (se 1 (by rfl) ⟨1207442, by rfl⟩ : syracuseStep 1609923 = 2414885) B2414885
theorem B1609939 : Blo 1609003 1609939 := bstep (se 1 (by rfl) ⟨1207454, by rfl⟩ : syracuseStep 1609939 = 2414909) B2414909
theorem B1609955 : Blo 1609003 1609955 := bstep (se 1 (by rfl) ⟨1207466, by rfl⟩ : syracuseStep 1609955 = 2414933) B2414933
theorem B12226787 : Blo 1609003 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B5157101 : Blo 1609003 5157101 := bstep (se 3 (by rfl) ⟨966956, by rfl⟩ : syracuseStep 5157101 = 1933913) B1933913
theorem B2715889 : Blo 1609003 2715889 := bstep (se 2 (by rfl) ⟨1018458, by rfl⟩ : syracuseStep 2715889 = 2036917) B2036917
theorem B1609971 : Blo 1609003 1609971 := bstep (se 1 (by rfl) ⟨1207478, by rfl⟩ : syracuseStep 1609971 = 2414957) B2414957
theorem B1609987 : Blo 1609003 1609987 := bstep (se 1 (by rfl) ⟨1207490, by rfl⟩ : syracuseStep 1609987 = 2414981) B2414981
theorem B2715923 : Blo 1609003 2715923 := bstep (se 1 (by rfl) ⟨2036942, by rfl⟩ : syracuseStep 2715923 = 4073885) B4073885
theorem B1610003 : Blo 1609003 1610003 := bstep (se 1 (by rfl) ⟨1207502, by rfl⟩ : syracuseStep 1610003 = 2415005) B2415005
theorem B1610019 : Blo 1609003 1610019 := bstep (se 1 (by rfl) ⟨1207514, by rfl⟩ : syracuseStep 1610019 = 2415029) B2415029
theorem B5435693 : Blo 1609003 5435693 := bstep (se 3 (by rfl) ⟨1019192, by rfl⟩ : syracuseStep 5435693 = 2038385) B2038385
theorem B1610035 : Blo 1609003 1610035 := bstep (se 1 (by rfl) ⟨1207526, by rfl⟩ : syracuseStep 1610035 = 2415053) B2415053
theorem B1610051 : Blo 1609003 1610051 := bstep (se 1 (by rfl) ⟨1207538, by rfl⟩ : syracuseStep 1610051 = 2415077) B2415077
theorem B1610067 : Blo 1609003 1610067 := bstep (se 1 (by rfl) ⟨1207550, by rfl⟩ : syracuseStep 1610067 = 2415101) B2415101
theorem B1610083 : Blo 1609003 1610083 := bstep (se 1 (by rfl) ⟨1207562, by rfl⟩ : syracuseStep 1610083 = 2415125) B2415125
theorem B5435747 : Blo 1609003 5435747 := bstep (se 1 (by rfl) ⟨4076810, by rfl⟩ : syracuseStep 5435747 = 8153621) B8153621
theorem B1610099 : Blo 1609003 1610099 := bstep (se 1 (by rfl) ⟨1207574, by rfl⟩ : syracuseStep 1610099 = 2415149) B2415149
theorem B3436931 : Blo 1609003 3436931 := bstep (se 1 (by rfl) ⟨2577698, by rfl⟩ : syracuseStep 3436931 = 5155397) B5155397
theorem B1610115 : Blo 1609003 1610115 := bstep (se 1 (by rfl) ⟨1207586, by rfl⟩ : syracuseStep 1610115 = 2415173) B2415173
theorem B2716051 : Blo 1609003 2716051 := bstep (se 1 (by rfl) ⟨2037038, by rfl⟩ : syracuseStep 2716051 = 4074077) B4074077
theorem B1610131 : Blo 1609003 1610131 := bstep (se 1 (by rfl) ⟨1207598, by rfl⟩ : syracuseStep 1610131 = 2415197) B2415197
theorem B1610147 : Blo 1609003 1610147 := bstep (se 1 (by rfl) ⟨1207610, by rfl⟩ : syracuseStep 1610147 = 2415221) B2415221
theorem B1610163 : Blo 1609003 1610163 := bstep (se 1 (by rfl) ⟨1207622, by rfl⟩ : syracuseStep 1610163 = 2415245) B2415245
theorem B1610179 : Blo 1609003 1610179 := bstep (se 1 (by rfl) ⟨1207634, by rfl⟩ : syracuseStep 1610179 = 2415269) B2415269
theorem B1610195 : Blo 1609003 1610195 := bstep (se 1 (by rfl) ⟨1207646, by rfl⟩ : syracuseStep 1610195 = 2415293) B2415293
theorem B1610211 : Blo 1609003 1610211 := bstep (se 1 (by rfl) ⟨1207658, by rfl⟩ : syracuseStep 1610211 = 2415317) B2415317
theorem B3264995 : Blo 1609003 3264995 := bstep (se 1 (by rfl) ⟨2448746, by rfl⟩ : syracuseStep 3264995 = 4897493) B4897493
theorem B1610227 : Blo 1609003 1610227 := bstep (se 1 (by rfl) ⟨1207670, by rfl⟩ : syracuseStep 1610227 = 2415341) B2415341
theorem B1610243 : Blo 1609003 1610243 := bstep (se 1 (by rfl) ⟨1207682, by rfl⟩ : syracuseStep 1610243 = 2415365) B2415365
theorem B1610259 : Blo 1609003 1610259 := bstep (se 1 (by rfl) ⟨1207694, by rfl⟩ : syracuseStep 1610259 = 2415389) B2415389
theorem B2716193 : Blo 1609003 2716193 := bstep (se 2 (by rfl) ⟨1018572, by rfl⟩ : syracuseStep 2716193 = 2037145) B2037145
theorem B1610275 : Blo 1609003 1610275 := bstep (se 1 (by rfl) ⟨1207706, by rfl⟩ : syracuseStep 1610275 = 2415413) B2415413
theorem B1610291 : Blo 1609003 1610291 := bstep (se 1 (by rfl) ⟨1207718, by rfl⟩ : syracuseStep 1610291 = 2415437) B2415437
theorem B1610307 : Blo 1609003 1610307 := bstep (se 1 (by rfl) ⟨1207730, by rfl⟩ : syracuseStep 1610307 = 2415461) B2415461
theorem B1610323 : Blo 1609003 1610323 := bstep (se 1 (by rfl) ⟨1207742, by rfl⟩ : syracuseStep 1610323 = 2415485) B2415485
theorem B1610339 : Blo 1609003 1610339 := bstep (se 1 (by rfl) ⟨1207754, by rfl⟩ : syracuseStep 1610339 = 2415509) B2415509
theorem B5436017 : Blo 1609003 5436017 := bstep (se 2 (by rfl) ⟨2038506, by rfl⟩ : syracuseStep 5436017 = 4077013) B4077013
theorem B1610355 : Blo 1609003 1610355 := bstep (se 1 (by rfl) ⟨1207766, by rfl⟩ : syracuseStep 1610355 = 2415533) B2415533
theorem B1610371 : Blo 1609003 1610371 := bstep (se 1 (by rfl) ⟨1207778, by rfl⟩ : syracuseStep 1610371 = 2415557) B2415557
theorem B1610387 : Blo 1609003 1610387 := bstep (se 1 (by rfl) ⟨1207790, by rfl⟩ : syracuseStep 1610387 = 2415581) B2415581
theorem B2716321 : Blo 1609003 2716321 := bstep (se 2 (by rfl) ⟨1018620, by rfl⟩ : syracuseStep 2716321 = 2037241) B2037241
theorem B1610403 : Blo 1609003 1610403 := bstep (se 1 (by rfl) ⟨1207802, by rfl⟩ : syracuseStep 1610403 = 2415605) B2415605
theorem B1610419 : Blo 1609003 1610419 := bstep (se 1 (by rfl) ⟨1207814, by rfl⟩ : syracuseStep 1610419 = 2415629) B2415629
theorem B2716355 : Blo 1609003 2716355 := bstep (se 1 (by rfl) ⟨2037266, by rfl⟩ : syracuseStep 2716355 = 4074533) B4074533
theorem B1610435 : Blo 1609003 1610435 := bstep (se 1 (by rfl) ⟨1207826, by rfl⟩ : syracuseStep 1610435 = 2415653) B2415653
theorem B2355923 : Blo 1609003 2355923 := bstep (se 1 (by rfl) ⟨1766942, by rfl⟩ : syracuseStep 2355923 = 3533885) B3533885
theorem B1610451 : Blo 1609003 1610451 := bstep (se 1 (by rfl) ⟨1207838, by rfl⟩ : syracuseStep 1610451 = 2415677) B2415677
theorem B1610467 : Blo 1609003 1610467 := bstep (se 1 (by rfl) ⟨1207850, by rfl⟩ : syracuseStep 1610467 = 2415701) B2415701
theorem B1610483 : Blo 1609003 1610483 := bstep (se 1 (by rfl) ⟨1207862, by rfl⟩ : syracuseStep 1610483 = 2415725) B2415725
theorem B1610499 : Blo 1609003 1610499 := bstep (se 1 (by rfl) ⟨1207874, by rfl⟩ : syracuseStep 1610499 = 2415749) B2415749
theorem B1610515 : Blo 1609003 1610515 := bstep (se 1 (by rfl) ⟨1207886, by rfl⟩ : syracuseStep 1610515 = 2415773) B2415773
theorem B1610531 : Blo 1609003 1610531 := bstep (se 1 (by rfl) ⟨1207898, by rfl⟩ : syracuseStep 1610531 = 2415797) B2415797
theorem B1610547 : Blo 1609003 1610547 := bstep (se 1 (by rfl) ⟨1207910, by rfl⟩ : syracuseStep 1610547 = 2415821) B2415821
theorem B2716483 : Blo 1609003 2716483 := bstep (se 1 (by rfl) ⟨2037362, by rfl⟩ : syracuseStep 2716483 = 4074725) B4074725
theorem B1610563 : Blo 1609003 1610563 := bstep (se 1 (by rfl) ⟨1207922, by rfl⟩ : syracuseStep 1610563 = 2415845) B2415845
theorem B10318661 : Blo 1609003 10318661 := bstep (se 4 (by rfl) ⟨967374, by rfl⟩ : syracuseStep 10318661 = 1934749) B1934749
theorem B8147789 : Blo 1609003 8147789 := bstep (se 3 (by rfl) ⟨1527710, by rfl⟩ : syracuseStep 8147789 = 3055421) B3055421
theorem B1610579 : Blo 1609003 1610579 := bstep (se 1 (by rfl) ⟨1207934, by rfl⟩ : syracuseStep 1610579 = 2415869) B2415869
theorem B1610595 : Blo 1609003 1610595 := bstep (se 1 (by rfl) ⟨1207946, by rfl⟩ : syracuseStep 1610595 = 2415893) B2415893
theorem B3265393 : Blo 1609003 3265393 := bstep (se 2 (by rfl) ⟨1224522, by rfl⟩ : syracuseStep 3265393 = 2449045) B2449045
theorem B1610611 : Blo 1609003 1610611 := bstep (se 1 (by rfl) ⟨1207958, by rfl⟩ : syracuseStep 1610611 = 2415917) B2415917
theorem B1610627 : Blo 1609003 1610627 := bstep (se 1 (by rfl) ⟨1207970, by rfl⟩ : syracuseStep 1610627 = 2415941) B2415941
theorem B1610643 : Blo 1609003 1610643 := bstep (se 1 (by rfl) ⟨1207982, by rfl⟩ : syracuseStep 1610643 = 2415965) B2415965
theorem B1610659 : Blo 1609003 1610659 := bstep (se 1 (by rfl) ⟨1207994, by rfl⟩ : syracuseStep 1610659 = 2415989) B2415989
theorem B2036659 : Blo 1609003 2036659 := bstep (se 1 (by rfl) ⟨1527494, by rfl⟩ : syracuseStep 2036659 = 3054989) B3054989
theorem B1610675 : Blo 1609003 1610675 := bstep (se 1 (by rfl) ⟨1208006, by rfl⟩ : syracuseStep 1610675 = 2416013) B2416013
theorem B2413505 : Blo 1609003 2413505 := bstep (se 2 (by rfl) ⟨905064, by rfl⟩ : syracuseStep 2413505 = 1810129) B1810129
theorem B1610691 : Blo 1609003 1610691 := bstep (se 1 (by rfl) ⟨1208018, by rfl⟩ : syracuseStep 1610691 = 2416037) B2416037
theorem B4584397 : Blo 1609003 4584397 := bstep (se 3 (by rfl) ⟨859574, by rfl⟩ : syracuseStep 4584397 = 1719149) B1719149
theorem B6198221 : Blo 1609003 6198221 := bstep (se 3 (by rfl) ⟨1162166, by rfl⟩ : syracuseStep 6198221 = 2324333) B2324333
theorem B2716625 : Blo 1609003 2716625 := bstep (se 2 (by rfl) ⟨1018734, by rfl⟩ : syracuseStep 2716625 = 2037469) B2037469
theorem B2413523 : Blo 1609003 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B1610707 : Blo 1609003 1610707 := bstep (se 1 (by rfl) ⟨1208030, by rfl⟩ : syracuseStep 1610707 = 2416061) B2416061
theorem B1610723 : Blo 1609003 1610723 := bstep (se 1 (by rfl) ⟨1208042, by rfl⟩ : syracuseStep 1610723 = 2416085) B2416085
theorem B2413553 : Blo 1609003 2413553 := bstep (se 2 (by rfl) ⟨905082, by rfl⟩ : syracuseStep 2413553 = 1810165) B1810165
theorem B1610739 : Blo 1609003 1610739 := bstep (se 1 (by rfl) ⟨1208054, by rfl⟩ : syracuseStep 1610739 = 2416109) B2416109
theorem B2413571 : Blo 1609003 2413571 := bstep (se 1 (by rfl) ⟨1810178, by rfl⟩ : syracuseStep 2413571 = 3620357) B3620357
theorem B1610755 : Blo 1609003 1610755 := bstep (se 1 (by rfl) ⟨1208066, by rfl⟩ : syracuseStep 1610755 = 2416133) B2416133
theorem B13751309 : Blo 1609003 13751309 := bstep (se 3 (by rfl) ⟨2578370, by rfl⟩ : syracuseStep 13751309 = 5156741) B5156741
theorem B2036755 : Blo 1609003 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B1610771 : Blo 1609003 1610771 := bstep (se 1 (by rfl) ⟨1208078, by rfl⟩ : syracuseStep 1610771 = 2416157) B2416157
theorem B2413601 : Blo 1609003 2413601 := bstep (se 2 (by rfl) ⟨905100, by rfl⟩ : syracuseStep 2413601 = 1810201) B1810201
theorem B1610787 : Blo 1609003 1610787 := bstep (se 1 (by rfl) ⟨1208090, by rfl⟩ : syracuseStep 1610787 = 2416181) B2416181
theorem B2413619 : Blo 1609003 2413619 := bstep (se 1 (by rfl) ⟨1810214, by rfl⟩ : syracuseStep 2413619 = 3620429) B3620429
theorem B1610803 : Blo 1609003 1610803 := bstep (se 1 (by rfl) ⟨1208102, by rfl⟩ : syracuseStep 1610803 = 2416205) B2416205
theorem B1610819 : Blo 1609003 1610819 := bstep (se 1 (by rfl) ⟨1208114, by rfl⟩ : syracuseStep 1610819 = 2416229) B2416229
theorem B2413649 : Blo 1609003 2413649 := bstep (se 2 (by rfl) ⟨905118, by rfl⟩ : syracuseStep 2413649 = 1810237) B1810237
theorem B2716753 : Blo 1609003 2716753 := bstep (se 2 (by rfl) ⟨1018782, by rfl⟩ : syracuseStep 2716753 = 2037565) B2037565
theorem B1610835 : Blo 1609003 1610835 := bstep (se 1 (by rfl) ⟨1208126, by rfl⟩ : syracuseStep 1610835 = 2416253) B2416253
theorem B2413667 : Blo 1609003 2413667 := bstep (se 1 (by rfl) ⟨1810250, by rfl⟩ : syracuseStep 2413667 = 3620501) B3620501
theorem B1610851 : Blo 1609003 1610851 := bstep (se 1 (by rfl) ⟨1208138, by rfl⟩ : syracuseStep 1610851 = 2416277) B2416277
theorem B6878321 : Blo 1609003 6878321 := bstep (se 2 (by rfl) ⟨2579370, by rfl⟩ : syracuseStep 6878321 = 5158741) B5158741
theorem B2716787 : Blo 1609003 2716787 := bstep (se 1 (by rfl) ⟨2037590, by rfl⟩ : syracuseStep 2716787 = 4075181) B4075181
theorem B1610867 : Blo 1609003 1610867 := bstep (se 1 (by rfl) ⟨1208150, by rfl⟩ : syracuseStep 1610867 = 2416301) B2416301
theorem B2413697 : Blo 1609003 2413697 := bstep (se 2 (by rfl) ⟨905136, by rfl⟩ : syracuseStep 2413697 = 1810273) B1810273
theorem B1610883 : Blo 1609003 1610883 := bstep (se 1 (by rfl) ⟨1208162, by rfl⟩ : syracuseStep 1610883 = 2416325) B2416325
theorem B5436557 : Blo 1609003 5436557 := bstep (se 3 (by rfl) ⟨1019354, by rfl⟩ : syracuseStep 5436557 = 2038709) B2038709
theorem B4076689 : Blo 1609003 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B2413715 : Blo 1609003 2413715 := bstep (se 1 (by rfl) ⟨1810286, by rfl⟩ : syracuseStep 2413715 = 3620573) B3620573
theorem B1610899 : Blo 1609003 1610899 := bstep (se 1 (by rfl) ⟨1208174, by rfl⟩ : syracuseStep 1610899 = 2416349) B2416349
theorem B1610915 : Blo 1609003 1610915 := bstep (se 1 (by rfl) ⟨1208186, by rfl⟩ : syracuseStep 1610915 = 2416373) B2416373
theorem B2413745 : Blo 1609003 2413745 := bstep (se 2 (by rfl) ⟨905154, by rfl⟩ : syracuseStep 2413745 = 1810309) B1810309
theorem B1610931 : Blo 1609003 1610931 := bstep (se 1 (by rfl) ⟨1208198, by rfl⟩ : syracuseStep 1610931 = 2416397) B2416397
theorem B2413763 : Blo 1609003 2413763 := bstep (se 1 (by rfl) ⟨1810322, by rfl⟩ : syracuseStep 2413763 = 3620645) B3620645
theorem B5436611 : Blo 1609003 5436611 := bstep (se 1 (by rfl) ⟨4077458, by rfl⟩ : syracuseStep 5436611 = 8154917) B8154917
theorem B1610947 : Blo 1609003 1610947 := bstep (se 1 (by rfl) ⟨1208210, by rfl⟩ : syracuseStep 1610947 = 2416421) B2416421
theorem B3437777 : Blo 1609003 3437777 := bstep (se 2 (by rfl) ⟨1289166, by rfl⟩ : syracuseStep 3437777 = 2578333) B2578333
theorem B1610963 : Blo 1609003 1610963 := bstep (se 1 (by rfl) ⟨1208222, by rfl⟩ : syracuseStep 1610963 = 2416445) B2416445
theorem B2413793 : Blo 1609003 2413793 := bstep (se 2 (by rfl) ⟨905172, by rfl⟩ : syracuseStep 2413793 = 1810345) B1810345
theorem B58758371 : Blo 1609003 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B1610979 : Blo 1609003 1610979 := bstep (se 1 (by rfl) ⟨1208234, by rfl⟩ : syracuseStep 1610979 = 2416469) B2416469
theorem B2413811 : Blo 1609003 2413811 := bstep (se 1 (by rfl) ⟨1810358, by rfl⟩ : syracuseStep 2413811 = 3620717) B3620717
theorem B2716915 : Blo 1609003 2716915 := bstep (se 1 (by rfl) ⟨2037686, by rfl⟩ : syracuseStep 2716915 = 4075373) B4075373
theorem B1610995 : Blo 1609003 1610995 := bstep (se 1 (by rfl) ⟨1208246, by rfl⟩ : syracuseStep 1610995 = 2416493) B2416493
theorem B2413841 : Blo 1609003 2413841 := bstep (se 2 (by rfl) ⟨905190, by rfl⟩ : syracuseStep 2413841 = 1810381) B1810381
theorem B2413859 : Blo 1609003 2413859 := bstep (se 1 (by rfl) ⟨1810394, by rfl⟩ : syracuseStep 2413859 = 3620789) B3620789
theorem B2413889 : Blo 1609003 2413889 := bstep (se 2 (by rfl) ⟨905208, by rfl⟩ : syracuseStep 2413889 = 1810417) B1810417
theorem B2413907 : Blo 1609003 2413907 := bstep (se 1 (by rfl) ⟨1810430, by rfl⟩ : syracuseStep 2413907 = 3620861) B3620861
theorem B2413937 : Blo 1609003 2413937 := bstep (se 2 (by rfl) ⟨905226, by rfl⟩ : syracuseStep 2413937 = 1810453) B1810453
theorem B2717057 : Blo 1609003 2717057 := bstep (se 2 (by rfl) ⟨1018896, by rfl⟩ : syracuseStep 2717057 = 2037793) B2037793
theorem B2413955 : Blo 1609003 2413955 := bstep (se 1 (by rfl) ⟨1810466, by rfl⟩ : syracuseStep 2413955 = 3620933) B3620933
theorem B2291105 : Blo 1609003 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B2413985 : Blo 1609003 2413985 := bstep (se 2 (by rfl) ⟨905244, by rfl⟩ : syracuseStep 2413985 = 1810489) B1810489
theorem B4076963 : Blo 1609003 4076963 := bstep (se 1 (by rfl) ⟨3057722, by rfl⟩ : syracuseStep 4076963 = 6115445) B6115445
theorem B2414003 : Blo 1609003 2414003 := bstep (se 1 (by rfl) ⟨1810502, by rfl⟩ : syracuseStep 2414003 = 3621005) B3621005
theorem B2414033 : Blo 1609003 2414033 := bstep (se 2 (by rfl) ⟨905262, by rfl⟩ : syracuseStep 2414033 = 1810525) B1810525
theorem B5436881 : Blo 1609003 5436881 := bstep (se 2 (by rfl) ⟨2038830, by rfl⟩ : syracuseStep 5436881 = 4077661) B4077661
theorem B2414051 : Blo 1609003 2414051 := bstep (se 1 (by rfl) ⟨1810538, by rfl⟩ : syracuseStep 2414051 = 3621077) B3621077
theorem B20624867 : Blo 1609003 20624867 := bstep (se 1 (by rfl) ⟨15468650, by rfl⟩ : syracuseStep 20624867 = 30937301) B30937301
theorem B2414081 : Blo 1609003 2414081 := bstep (se 2 (by rfl) ⟨905280, by rfl⟩ : syracuseStep 2414081 = 1810561) B1810561
theorem B2717185 : Blo 1609003 2717185 := bstep (se 2 (by rfl) ⟨1018944, by rfl⟩ : syracuseStep 2717185 = 2037889) B2037889
theorem B2577923 : Blo 1609003 2577923 := bstep (se 1 (by rfl) ⟨1933442, by rfl⟩ : syracuseStep 2577923 = 3866885) B3866885
theorem B2037251 : Blo 1609003 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B2414099 : Blo 1609003 2414099 := bstep (se 1 (by rfl) ⟨1810574, by rfl⟩ : syracuseStep 2414099 = 3621149) B3621149
theorem B2717219 : Blo 1609003 2717219 := bstep (se 1 (by rfl) ⟨2037914, by rfl⟩ : syracuseStep 2717219 = 4075829) B4075829
theorem B2414129 : Blo 1609003 2414129 := bstep (se 2 (by rfl) ⟨905298, by rfl⟩ : syracuseStep 2414129 = 1810597) B1810597
theorem B2176561 : Blo 1609003 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B2414147 : Blo 1609003 2414147 := bstep (se 1 (by rfl) ⟨1810610, by rfl⟩ : syracuseStep 2414147 = 3621221) B3621221
theorem B3487313 : Blo 1609003 3487313 := bstep (se 2 (by rfl) ⟨1307742, by rfl⟩ : syracuseStep 3487313 = 2615485) B2615485
theorem B2414177 : Blo 1609003 2414177 := bstep (se 2 (by rfl) ⟨905316, by rfl⟩ : syracuseStep 2414177 = 1810633) B1810633
theorem B4077155 : Blo 1609003 4077155 := bstep (se 1 (by rfl) ⟨3057866, by rfl⟩ : syracuseStep 4077155 = 6115733) B6115733
theorem B2414195 : Blo 1609003 2414195 := bstep (se 1 (by rfl) ⟨1810646, by rfl⟩ : syracuseStep 2414195 = 3621293) B3621293
theorem B2414225 : Blo 1609003 2414225 := bstep (se 2 (by rfl) ⟨905334, by rfl⟩ : syracuseStep 2414225 = 1810669) B1810669
theorem B2414243 : Blo 1609003 2414243 := bstep (se 1 (by rfl) ⟨1810682, by rfl⟩ : syracuseStep 2414243 = 3621365) B3621365
theorem B2717347 : Blo 1609003 2717347 := bstep (se 1 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 2717347 = 4076021) B4076021
theorem B2414273 : Blo 1609003 2414273 := bstep (se 2 (by rfl) ⟨905352, by rfl⟩ : syracuseStep 2414273 = 1810705) B1810705
theorem B2578115 : Blo 1609003 2578115 := bstep (se 1 (by rfl) ⟨1933586, by rfl⟩ : syracuseStep 2578115 = 3867173) B3867173
theorem B2414291 : Blo 1609003 2414291 := bstep (se 1 (by rfl) ⟨1810718, by rfl⟩ : syracuseStep 2414291 = 3621437) B3621437
theorem B2176723 : Blo 1609003 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B2414321 : Blo 1609003 2414321 := bstep (se 2 (by rfl) ⟨905370, by rfl⟩ : syracuseStep 2414321 = 1810741) B1810741
theorem B2414339 : Blo 1609003 2414339 := bstep (se 1 (by rfl) ⟨1810754, by rfl⟩ : syracuseStep 2414339 = 3621509) B3621509
theorem B17397517 : Blo 1609003 17397517 := bstep (se 3 (by rfl) ⟨3262034, by rfl⟩ : syracuseStep 17397517 = 6524069) B6524069
theorem B2414369 : Blo 1609003 2414369 := bstep (se 2 (by rfl) ⟨905388, by rfl⟩ : syracuseStep 2414369 = 1810777) B1810777
theorem B2717489 : Blo 1609003 2717489 := bstep (se 2 (by rfl) ⟨1019058, by rfl⟩ : syracuseStep 2717489 = 2038117) B2038117
theorem B2414387 : Blo 1609003 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B2578243 : Blo 1609003 2578243 := bstep (se 1 (by rfl) ⟨1933682, by rfl⟩ : syracuseStep 2578243 = 3867365) B3867365
theorem B2414417 : Blo 1609003 2414417 := bstep (se 2 (by rfl) ⟨905406, by rfl⟩ : syracuseStep 2414417 = 1810813) B1810813
theorem B2414435 : Blo 1609003 2414435 := bstep (se 1 (by rfl) ⟨1810826, by rfl⟩ : syracuseStep 2414435 = 3621653) B3621653
theorem B2414465 : Blo 1609003 2414465 := bstep (se 2 (by rfl) ⟨905424, by rfl⟩ : syracuseStep 2414465 = 1810849) B1810849
theorem B2414483 : Blo 1609003 2414483 := bstep (se 1 (by rfl) ⟨1810862, by rfl⟩ : syracuseStep 2414483 = 3621725) B3621725
theorem B2414513 : Blo 1609003 2414513 := bstep (se 2 (by rfl) ⟨905442, by rfl⟩ : syracuseStep 2414513 = 1810885) B1810885
theorem B2717617 : Blo 1609003 2717617 := bstep (se 2 (by rfl) ⟨1019106, by rfl⟩ : syracuseStep 2717617 = 2038213) B2038213
theorem B20633525 : Blo 1609003 20633525 := bstep (se 5 (by rfl) ⟨967196, by rfl⟩ : syracuseStep 20633525 = 1934393) B1934393
theorem B2414531 : Blo 1609003 2414531 := bstep (se 1 (by rfl) ⟨1810898, by rfl⟩ : syracuseStep 2414531 = 3621797) B3621797
theorem B2717651 : Blo 1609003 2717651 := bstep (se 1 (by rfl) ⟨2038238, by rfl⟩ : syracuseStep 2717651 = 4076477) B4076477
theorem B2414561 : Blo 1609003 2414561 := bstep (se 2 (by rfl) ⟨905460, by rfl⟩ : syracuseStep 2414561 = 1810921) B1810921
theorem B5158883 : Blo 1609003 5158883 := bstep (se 1 (by rfl) ⟨3869162, by rfl⟩ : syracuseStep 5158883 = 7738325) B7738325
theorem B2414579 : Blo 1609003 2414579 := bstep (se 1 (by rfl) ⟨1810934, by rfl⟩ : syracuseStep 2414579 = 3621869) B3621869
theorem B5806093 : Blo 1609003 5806093 := bstep (se 3 (by rfl) ⟨1088642, by rfl⟩ : syracuseStep 5806093 = 2177285) B2177285
theorem B2414609 : Blo 1609003 2414609 := bstep (se 2 (by rfl) ⟨905478, by rfl⟩ : syracuseStep 2414609 = 1810957) B1810957
theorem B2414627 : Blo 1609003 2414627 := bstep (se 1 (by rfl) ⟨1810970, by rfl⟩ : syracuseStep 2414627 = 3621941) B3621941
theorem B2414657 : Blo 1609003 2414657 := bstep (se 2 (by rfl) ⟨905496, by rfl⟩ : syracuseStep 2414657 = 1810993) B1810993
theorem B2414675 : Blo 1609003 2414675 := bstep (se 1 (by rfl) ⟨1811006, by rfl⟩ : syracuseStep 2414675 = 3622013) B3622013
theorem B2717779 : Blo 1609003 2717779 := bstep (se 1 (by rfl) ⟨2038334, by rfl⟩ : syracuseStep 2717779 = 4076669) B4076669
theorem B2414705 : Blo 1609003 2414705 := bstep (se 2 (by rfl) ⟨905514, by rfl⟩ : syracuseStep 2414705 = 1811029) B1811029
theorem B11606129 : Blo 1609003 11606129 := bstep (se 2 (by rfl) ⟨4352298, by rfl⟩ : syracuseStep 11606129 = 8704597) B8704597
theorem B2414723 : Blo 1609003 2414723 := bstep (se 1 (by rfl) ⟨1811042, by rfl⟩ : syracuseStep 2414723 = 3622085) B3622085
theorem B2414753 : Blo 1609003 2414753 := bstep (se 2 (by rfl) ⟨905532, by rfl⟩ : syracuseStep 2414753 = 1811065) B1811065
theorem B2414771 : Blo 1609003 2414771 := bstep (se 1 (by rfl) ⟨1811078, by rfl⟩ : syracuseStep 2414771 = 3622157) B3622157
theorem B2037955 : Blo 1609003 2037955 := bstep (se 1 (by rfl) ⟨1528466, by rfl⟩ : syracuseStep 2037955 = 3056933) B3056933
theorem B9173189 : Blo 1609003 9173189 := bstep (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) B1719973
theorem B2414801 : Blo 1609003 2414801 := bstep (se 2 (by rfl) ⟨905550, by rfl⟩ : syracuseStep 2414801 = 1811101) B1811101
theorem B2447585 : Blo 1609003 2447585 := bstep (se 2 (by rfl) ⟨917844, by rfl⟩ : syracuseStep 2447585 = 1835689) B1835689
theorem B2717921 : Blo 1609003 2717921 := bstep (se 2 (by rfl) ⟨1019220, by rfl⟩ : syracuseStep 2717921 = 2038441) B2038441
theorem B2414819 : Blo 1609003 2414819 := bstep (se 1 (by rfl) ⟨1811114, by rfl⟩ : syracuseStep 2414819 = 3622229) B3622229
theorem B2414849 : Blo 1609003 2414849 := bstep (se 2 (by rfl) ⟨905568, by rfl⟩ : syracuseStep 2414849 = 1811137) B1811137
theorem B2291971 : Blo 1609003 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B2414867 : Blo 1609003 2414867 := bstep (se 1 (by rfl) ⟨1811150, by rfl⟩ : syracuseStep 2414867 = 3622301) B3622301
theorem B2038051 : Blo 1609003 2038051 := bstep (se 1 (by rfl) ⟨1528538, by rfl⟩ : syracuseStep 2038051 = 3057077) B3057077
theorem B2414897 : Blo 1609003 2414897 := bstep (se 2 (by rfl) ⟨905586, by rfl⟩ : syracuseStep 2414897 = 1811173) B1811173
theorem B2414915 : Blo 1609003 2414915 := bstep (se 1 (by rfl) ⟨1811186, by rfl⟩ : syracuseStep 2414915 = 3622373) B3622373
theorem B4962637 : Blo 1609003 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B7739725 : Blo 1609003 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B2414945 : Blo 1609003 2414945 := bstep (se 2 (by rfl) ⟨905604, by rfl⟩ : syracuseStep 2414945 = 1811209) B1811209
theorem B2718049 : Blo 1609003 2718049 := bstep (se 2 (by rfl) ⟨1019268, by rfl⟩ : syracuseStep 2718049 = 2038537) B2038537
theorem B2292067 : Blo 1609003 2292067 := bstep (se 1 (by rfl) ⟨1719050, by rfl⟩ : syracuseStep 2292067 = 3438101) B3438101
theorem B2414963 : Blo 1609003 2414963 := bstep (se 1 (by rfl) ⟨1811222, by rfl⟩ : syracuseStep 2414963 = 3622445) B3622445
theorem B2718083 : Blo 1609003 2718083 := bstep (se 1 (by rfl) ⟨2038562, by rfl⟩ : syracuseStep 2718083 = 4077125) B4077125
theorem B2414993 : Blo 1609003 2414993 := bstep (se 2 (by rfl) ⟨905622, by rfl⟩ : syracuseStep 2414993 = 1811245) B1811245
theorem B2447779 : Blo 1609003 2447779 := bstep (se 1 (by rfl) ⟨1835834, by rfl⟩ : syracuseStep 2447779 = 3671669) B3671669
theorem B2415011 : Blo 1609003 2415011 := bstep (se 1 (by rfl) ⟨1811258, by rfl⟩ : syracuseStep 2415011 = 3622517) B3622517
theorem B2415041 : Blo 1609003 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B2578883 : Blo 1609003 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B2415059 : Blo 1609003 2415059 := bstep (se 1 (by rfl) ⟨1811294, by rfl⟩ : syracuseStep 2415059 = 3622589) B3622589
theorem B2415089 : Blo 1609003 2415089 := bstep (se 2 (by rfl) ⟨905658, by rfl⟩ : syracuseStep 2415089 = 1811317) B1811317
theorem B2415107 : Blo 1609003 2415107 := bstep (se 1 (by rfl) ⟨1811330, by rfl⟩ : syracuseStep 2415107 = 3622661) B3622661
theorem B2718211 : Blo 1609003 2718211 := bstep (se 1 (by rfl) ⟨2038658, by rfl⟩ : syracuseStep 2718211 = 4077317) B4077317
theorem B2578961 : Blo 1609003 2578961 := bstep (se 2 (by rfl) ⟨967110, by rfl⟩ : syracuseStep 2578961 = 1934221) B1934221
theorem B2415137 : Blo 1609003 2415137 := bstep (se 2 (by rfl) ⟨905676, by rfl⟩ : syracuseStep 2415137 = 1811353) B1811353
theorem B2415155 : Blo 1609003 2415155 := bstep (se 1 (by rfl) ⟨1811366, by rfl⟩ : syracuseStep 2415155 = 3622733) B3622733
theorem B2415185 : Blo 1609003 2415185 := bstep (se 2 (by rfl) ⟨905694, by rfl⟩ : syracuseStep 2415185 = 1811389) B1811389
theorem B2415203 : Blo 1609003 2415203 := bstep (se 1 (by rfl) ⟨1811402, by rfl⟩ : syracuseStep 2415203 = 3622805) B3622805
theorem B2415233 : Blo 1609003 2415233 := bstep (se 2 (by rfl) ⟨905712, by rfl⟩ : syracuseStep 2415233 = 1811425) B1811425
theorem B9173645 : Blo 1609003 9173645 := bstep (se 3 (by rfl) ⟨1720058, by rfl⟩ : syracuseStep 9173645 = 3440117) B3440117
theorem B4586129 : Blo 1609003 4586129 := bstep (se 2 (by rfl) ⟨1719798, by rfl⟩ : syracuseStep 4586129 = 3439597) B3439597
theorem B2718353 : Blo 1609003 2718353 := bstep (se 2 (by rfl) ⟨1019382, by rfl⟩ : syracuseStep 2718353 = 2038765) B2038765
theorem B2415251 : Blo 1609003 2415251 := bstep (se 1 (by rfl) ⟨1811438, by rfl⟩ : syracuseStep 2415251 = 3622877) B3622877
theorem B2415281 : Blo 1609003 2415281 := bstep (se 2 (by rfl) ⟨905730, by rfl⟩ : syracuseStep 2415281 = 1811461) B1811461
theorem B2415299 : Blo 1609003 2415299 := bstep (se 1 (by rfl) ⟨1811474, by rfl⟩ : syracuseStep 2415299 = 3622949) B3622949
theorem B6109901 : Blo 1609003 6109901 := bstep (se 3 (by rfl) ⟨1145606, by rfl⟩ : syracuseStep 6109901 = 2291213) B2291213
theorem B2415329 : Blo 1609003 2415329 := bstep (se 2 (by rfl) ⟨905748, by rfl⟩ : syracuseStep 2415329 = 1811497) B1811497
theorem B2415347 : Blo 1609003 2415347 := bstep (se 1 (by rfl) ⟨1811510, by rfl⟩ : syracuseStep 2415347 = 3623021) B3623021
theorem B9165581 : Blo 1609003 9165581 := bstep (se 3 (by rfl) ⟨1718546, by rfl⟩ : syracuseStep 9165581 = 3437093) B3437093
theorem B2415377 : Blo 1609003 2415377 := bstep (se 2 (by rfl) ⟨905766, by rfl⟩ : syracuseStep 2415377 = 1811533) B1811533
theorem B2718481 : Blo 1609003 2718481 := bstep (se 2 (by rfl) ⟨1019430, by rfl⟩ : syracuseStep 2718481 = 2038861) B2038861
theorem B2038547 : Blo 1609003 2038547 := bstep (se 1 (by rfl) ⟨1528910, by rfl⟩ : syracuseStep 2038547 = 3057821) B3057821
theorem B2415395 : Blo 1609003 2415395 := bstep (se 1 (by rfl) ⟨1811546, by rfl⟩ : syracuseStep 2415395 = 3623093) B3623093
theorem B2718515 : Blo 1609003 2718515 := bstep (se 1 (by rfl) ⟨2038886, by rfl⟩ : syracuseStep 2718515 = 4077773) B4077773
theorem B2415425 : Blo 1609003 2415425 := bstep (se 2 (by rfl) ⟨905784, by rfl⟩ : syracuseStep 2415425 = 1811569) B1811569
theorem B4586321 : Blo 1609003 4586321 := bstep (se 2 (by rfl) ⟨1719870, by rfl⟩ : syracuseStep 4586321 = 3439741) B3439741
theorem B2292563 : Blo 1609003 2292563 := bstep (se 1 (by rfl) ⟨1719422, by rfl⟩ : syracuseStep 2292563 = 3438845) B3438845
theorem B2415443 : Blo 1609003 2415443 := bstep (se 1 (by rfl) ⟨1811582, by rfl⟩ : syracuseStep 2415443 = 3623165) B3623165
theorem B2415473 : Blo 1609003 2415473 := bstep (se 2 (by rfl) ⟨905802, by rfl⟩ : syracuseStep 2415473 = 1811605) B1811605
theorem B7846769 : Blo 1609003 7846769 := bstep (se 2 (by rfl) ⟨2942538, by rfl⟩ : syracuseStep 7846769 = 5885077) B5885077
theorem B2415491 : Blo 1609003 2415491 := bstep (se 1 (by rfl) ⟨1811618, by rfl⟩ : syracuseStep 2415491 = 3623237) B3623237
theorem B2579345 : Blo 1609003 2579345 := bstep (se 2 (by rfl) ⟨967254, by rfl⟩ : syracuseStep 2579345 = 1934509) B1934509
theorem B1719187 : Blo 1609003 1719187 := bstep (se 1 (by rfl) ⟨1289390, by rfl⟩ : syracuseStep 1719187 = 2578781) B2578781
theorem B2415521 : Blo 1609003 2415521 := bstep (se 2 (by rfl) ⟨905820, by rfl⟩ : syracuseStep 2415521 = 1811641) B1811641
theorem B2415539 : Blo 1609003 2415539 := bstep (se 1 (by rfl) ⟨1811654, by rfl⟩ : syracuseStep 2415539 = 3623309) B3623309
theorem B31783877 : Blo 1609003 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B2415569 : Blo 1609003 2415569 := bstep (se 2 (by rfl) ⟨905838, by rfl⟩ : syracuseStep 2415569 = 1811677) B1811677
theorem B2415587 : Blo 1609003 2415587 := bstep (se 1 (by rfl) ⟨1811690, by rfl⟩ : syracuseStep 2415587 = 3623381) B3623381
theorem B2415617 : Blo 1609003 2415617 := bstep (se 2 (by rfl) ⟨905856, by rfl⟩ : syracuseStep 2415617 = 1811713) B1811713
theorem B2579473 : Blo 1609003 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B2415635 : Blo 1609003 2415635 := bstep (se 1 (by rfl) ⟨1811726, by rfl⟩ : syracuseStep 2415635 = 3623453) B3623453
theorem B2415665 : Blo 1609003 2415665 := bstep (se 2 (by rfl) ⟨905874, by rfl⟩ : syracuseStep 2415665 = 1811749) B1811749
theorem B2415683 : Blo 1609003 2415683 := bstep (se 1 (by rfl) ⟨1811762, by rfl⟩ : syracuseStep 2415683 = 3623525) B3623525
theorem B2415713 : Blo 1609003 2415713 := bstep (se 2 (by rfl) ⟨905892, by rfl⟩ : syracuseStep 2415713 = 1811785) B1811785
theorem B2415731 : Blo 1609003 2415731 := bstep (se 1 (by rfl) ⟨1811798, by rfl⟩ : syracuseStep 2415731 = 3623597) B3623597
theorem B20642957 : Blo 1609003 20642957 := bstep (se 3 (by rfl) ⟨3870554, by rfl⟩ : syracuseStep 20642957 = 7741109) B7741109
theorem B2415761 : Blo 1609003 2415761 := bstep (se 2 (by rfl) ⟨905910, by rfl⟩ : syracuseStep 2415761 = 1811821) B1811821
theorem B2415779 : Blo 1609003 2415779 := bstep (se 1 (by rfl) ⟨1811834, by rfl⟩ : syracuseStep 2415779 = 3623669) B3623669
theorem B2415809 : Blo 1609003 2415809 := bstep (se 2 (by rfl) ⟨905928, by rfl⟩ : syracuseStep 2415809 = 1811857) B1811857
theorem B2415827 : Blo 1609003 2415827 := bstep (se 1 (by rfl) ⟨1811870, by rfl⟩ : syracuseStep 2415827 = 3623741) B3623741
theorem B5430509 : Blo 1609003 5430509 := bstep (se 3 (by rfl) ⟨1018220, by rfl⟩ : syracuseStep 5430509 = 2036441) B2036441
theorem B2415857 : Blo 1609003 2415857 := bstep (se 2 (by rfl) ⟨905946, by rfl⟩ : syracuseStep 2415857 = 1811893) B1811893
theorem B2415875 : Blo 1609003 2415875 := bstep (se 1 (by rfl) ⟨1811906, by rfl⟩ : syracuseStep 2415875 = 3623813) B3623813
theorem B2415905 : Blo 1609003 2415905 := bstep (se 2 (by rfl) ⟨905964, by rfl⟩ : syracuseStep 2415905 = 1811929) B1811929
theorem B5430563 : Blo 1609003 5430563 := bstep (se 1 (by rfl) ⟨4072922, by rfl⟩ : syracuseStep 5430563 = 8145845) B8145845
theorem B2415923 : Blo 1609003 2415923 := bstep (se 1 (by rfl) ⟨1811942, by rfl⟩ : syracuseStep 2415923 = 3623885) B3623885
theorem B2415953 : Blo 1609003 2415953 := bstep (se 2 (by rfl) ⟨905982, by rfl⟩ : syracuseStep 2415953 = 1811965) B1811965
theorem B2415971 : Blo 1609003 2415971 := bstep (se 1 (by rfl) ⟨1811978, by rfl⟩ : syracuseStep 2415971 = 3623957) B3623957
theorem B7839089 : Blo 1609003 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B7740785 : Blo 1609003 7740785 := bstep (se 2 (by rfl) ⟨2902794, by rfl⟩ : syracuseStep 7740785 = 5805589) B5805589
theorem B2416001 : Blo 1609003 2416001 := bstep (se 2 (by rfl) ⟨906000, by rfl⟩ : syracuseStep 2416001 = 1812001) B1812001
theorem B2416019 : Blo 1609003 2416019 := bstep (se 1 (by rfl) ⟨1812014, by rfl⟩ : syracuseStep 2416019 = 3624029) B3624029
theorem B2416049 : Blo 1609003 2416049 := bstep (se 2 (by rfl) ⟨906018, by rfl⟩ : syracuseStep 2416049 = 1812037) B1812037
theorem B2416067 : Blo 1609003 2416067 := bstep (se 1 (by rfl) ⟨1812050, by rfl⟩ : syracuseStep 2416067 = 3624101) B3624101
theorem B2293201 : Blo 1609003 2293201 := bstep (se 2 (by rfl) ⟨859950, by rfl⟩ : syracuseStep 2293201 = 1719901) B1719901
theorem B2416097 : Blo 1609003 2416097 := bstep (se 2 (by rfl) ⟨906036, by rfl⟩ : syracuseStep 2416097 = 1812073) B1812073
theorem B2416115 : Blo 1609003 2416115 := bstep (se 1 (by rfl) ⟨1812086, by rfl⟩ : syracuseStep 2416115 = 3624173) B3624173
theorem B6880781 : Blo 1609003 6880781 := bstep (se 3 (by rfl) ⟨1290146, by rfl⟩ : syracuseStep 6880781 = 2580293) B2580293
theorem B2416145 : Blo 1609003 2416145 := bstep (se 2 (by rfl) ⟨906054, by rfl⟩ : syracuseStep 2416145 = 1812109) B1812109
theorem B2481683 : Blo 1609003 2481683 := bstep (se 1 (by rfl) ⟨1861262, by rfl⟩ : syracuseStep 2481683 = 3722525) B3722525
theorem B2416163 : Blo 1609003 2416163 := bstep (se 1 (by rfl) ⟨1812122, by rfl⟩ : syracuseStep 2416163 = 3624245) B3624245
theorem B5430833 : Blo 1609003 5430833 := bstep (se 2 (by rfl) ⟨2036562, by rfl⟩ : syracuseStep 5430833 = 4073125) B4073125
theorem B2416193 : Blo 1609003 2416193 := bstep (se 2 (by rfl) ⟨906072, by rfl⟩ : syracuseStep 2416193 = 1812145) B1812145
theorem B3055171 : Blo 1609003 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B2416211 : Blo 1609003 2416211 := bstep (se 1 (by rfl) ⟨1812158, by rfl⟩ : syracuseStep 2416211 = 3624317) B3624317
theorem B2448995 : Blo 1609003 2448995 := bstep (se 1 (by rfl) ⟨1836746, by rfl⟩ : syracuseStep 2448995 = 3673493) B3673493
theorem B3620465 : Blo 1609003 3620465 := bstep (se 2 (by rfl) ⟨1357674, by rfl⟩ : syracuseStep 3620465 = 2715349) B2715349
theorem B2416241 : Blo 1609003 2416241 := bstep (se 2 (by rfl) ⟨906090, by rfl⟩ : syracuseStep 2416241 = 1812181) B1812181
theorem B3620483 : Blo 1609003 3620483 := bstep (se 1 (by rfl) ⟨2715362, by rfl⟩ : syracuseStep 3620483 = 5430725) B5430725
theorem B2416259 : Blo 1609003 2416259 := bstep (se 1 (by rfl) ⟨1812194, by rfl⟩ : syracuseStep 2416259 = 3624389) B3624389
theorem B2416289 : Blo 1609003 2416289 := bstep (se 2 (by rfl) ⟨906108, by rfl⟩ : syracuseStep 2416289 = 1812217) B1812217
theorem B8150705 : Blo 1609003 8150705 := bstep (se 2 (by rfl) ⟨3056514, by rfl⟩ : syracuseStep 8150705 = 6113029) B6113029
theorem B2416307 : Blo 1609003 2416307 := bstep (se 1 (by rfl) ⟨1812230, by rfl⟩ : syracuseStep 2416307 = 3624461) B3624461
theorem B2416337 : Blo 1609003 2416337 := bstep (se 2 (by rfl) ⟨906126, by rfl⟩ : syracuseStep 2416337 = 1812253) B1812253
theorem B1810147 : Blo 1609003 1810147 := bstep (se 1 (by rfl) ⟨1357610, by rfl⟩ : syracuseStep 1810147 = 2715221) B2715221
theorem B2416355 : Blo 1609003 2416355 := bstep (se 1 (by rfl) ⟨1812266, by rfl⟩ : syracuseStep 2416355 = 3624533) B3624533
theorem B2416385 : Blo 1609003 2416385 := bstep (se 2 (by rfl) ⟨906144, by rfl⟩ : syracuseStep 2416385 = 1812289) B1812289
theorem B2416403 : Blo 1609003 2416403 := bstep (se 1 (by rfl) ⟨1812302, by rfl⟩ : syracuseStep 2416403 = 3624605) B3624605
theorem B2752289 : Blo 1609003 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B8257315 : Blo 1609003 8257315 := bstep (se 1 (by rfl) ⟨6192986, by rfl⟩ : syracuseStep 8257315 = 12385973) B12385973
theorem B2293537 : Blo 1609003 2293537 := bstep (se 2 (by rfl) ⟨860076, by rfl⟩ : syracuseStep 2293537 = 1720153) B1720153
theorem B4587313 : Blo 1609003 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B2416433 : Blo 1609003 2416433 := bstep (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) B1812325
theorem B2416451 : Blo 1609003 2416451 := bstep (se 1 (by rfl) ⟨1812338, by rfl⟩ : syracuseStep 2416451 = 3624677) B3624677
theorem B2416481 : Blo 1609003 2416481 := bstep (se 2 (by rfl) ⟨906180, by rfl⟩ : syracuseStep 2416481 = 1812361) B1812361
theorem B35307377 : Blo 1609003 35307377 := bstep (se 2 (by rfl) ⟨13240266, by rfl⟩ : syracuseStep 35307377 = 26480533) B26480533
theorem B1810291 : Blo 1609003 1810291 := bstep (se 1 (by rfl) ⟨1357718, by rfl⟩ : syracuseStep 1810291 = 2715437) B2715437
theorem B2416499 : Blo 1609003 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B3620753 : Blo 1609003 3620753 := bstep (se 2 (by rfl) ⟨1357782, by rfl⟩ : syracuseStep 3620753 = 2715565) B2715565
theorem B3620771 : Blo 1609003 3620771 := bstep (se 1 (by rfl) ⟨2715578, by rfl⟩ : syracuseStep 3620771 = 5431157) B5431157
theorem B11009969 : Blo 1609003 11009969 := bstep (se 2 (by rfl) ⟨4128738, by rfl⟩ : syracuseStep 11009969 = 8257477) B8257477
theorem B3440561 : Blo 1609003 3440561 := bstep (se 2 (by rfl) ⟨1290210, by rfl⟩ : syracuseStep 3440561 = 2580421) B2580421
theorem B3096587 : Blo 1609003 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B7741457 : Blo 1609003 7741457 := bstep (se 2 (by rfl) ⟨2903046, by rfl⟩ : syracuseStep 7741457 = 5806093) B5806093
theorem B5431319 : Blo 1609003 5431319 := bstep (se 1 (by rfl) ⟨4073489, by rfl⟩ : syracuseStep 5431319 = 8146979) B8146979
theorem B3620915 : Blo 1609003 3620915 := bstep (se 1 (by rfl) ⟨2715686, by rfl⟩ : syracuseStep 3620915 = 5431373) B5431373
theorem B1810507 : Blo 1609003 1810507 := bstep (se 1 (by rfl) ⟨1357880, by rfl⟩ : syracuseStep 1810507 = 2715761) B2715761
theorem B3620951 : Blo 1609003 3620951 := bstep (se 1 (by rfl) ⟨2715713, by rfl⟩ : syracuseStep 3620951 = 5431427) B5431427
theorem B8151191 : Blo 1609003 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B5505203 : Blo 1609003 5505203 := bstep (se 1 (by rfl) ⟨4128902, by rfl⟩ : syracuseStep 5505203 = 8257805) B8257805
theorem B1810615 : Blo 1609003 1810615 := bstep (se 1 (by rfl) ⟨1357961, by rfl⟩ : syracuseStep 1810615 = 2715923) B2715923
theorem B23527685 : Blo 1609003 23527685 := bstep (se 4 (by rfl) ⟨2205720, by rfl⟩ : syracuseStep 23527685 = 4411441) B4411441
theorem B3621131 : Blo 1609003 3621131 := bstep (se 1 (by rfl) ⟨2715848, by rfl⟩ : syracuseStep 3621131 = 5431697) B5431697
theorem B3621185 : Blo 1609003 3621185 := bstep (se 2 (by rfl) ⟨1357944, by rfl⟩ : syracuseStep 3621185 = 2715889) B2715889
theorem B3055961 : Blo 1609003 3055961 := bstep (se 2 (by rfl) ⟨1145985, by rfl⟩ : syracuseStep 3055961 = 2291971) B2291971
theorem B1810795 : Blo 1609003 1810795 := bstep (se 1 (by rfl) ⟨1358096, by rfl⟩ : syracuseStep 1810795 = 2716193) B2716193
theorem B12222899 : Blo 1609003 12222899 := bstep (se 1 (by rfl) ⟨9167174, by rfl⟩ : syracuseStep 12222899 = 18334349) B18334349
theorem B7340491 : Blo 1609003 7340491 := bstep (se 1 (by rfl) ⟨5505368, by rfl⟩ : syracuseStep 7340491 = 11010737) B11010737
theorem B1810903 : Blo 1609003 1810903 := bstep (se 1 (by rfl) ⟨1358177, by rfl⟩ : syracuseStep 1810903 = 2716355) B2716355
theorem B3621401 : Blo 1609003 3621401 := bstep (se 2 (by rfl) ⟨1358025, by rfl⟩ : syracuseStep 3621401 = 2716051) B2716051
theorem B5431859 : Blo 1609003 5431859 := bstep (se 1 (by rfl) ⟨4073894, by rfl⟩ : syracuseStep 5431859 = 8147789) B8147789
theorem B3621491 : Blo 1609003 3621491 := bstep (se 1 (by rfl) ⟨2716118, by rfl⟩ : syracuseStep 3621491 = 5432237) B5432237
theorem B6111875 : Blo 1609003 6111875 := bstep (se 1 (by rfl) ⟨4583906, by rfl⟩ : syracuseStep 6111875 = 9167813) B9167813
theorem B3670667 : Blo 1609003 3670667 := bstep (se 1 (by rfl) ⟨2753000, by rfl⟩ : syracuseStep 3670667 = 5506001) B5506001
theorem B1811083 : Blo 1609003 1811083 := bstep (se 1 (by rfl) ⟨1358312, by rfl⟩ : syracuseStep 1811083 = 2716625) B2716625
theorem B3621527 : Blo 1609003 3621527 := bstep (se 1 (by rfl) ⟨2716145, by rfl⟩ : syracuseStep 3621527 = 5432291) B5432291
theorem B13058711 : Blo 1609003 13058711 := bstep (se 1 (by rfl) ⟨9794033, by rfl⟩ : syracuseStep 13058711 = 19588067) B19588067
theorem B9167539 : Blo 1609003 9167539 := bstep (se 1 (by rfl) ⟨6875654, by rfl⟩ : syracuseStep 9167539 = 13751309) B13751309
theorem B1811191 : Blo 1609003 1811191 := bstep (se 1 (by rfl) ⟨1358393, by rfl⟩ : syracuseStep 1811191 = 2716787) B2716787
theorem B5432129 : Blo 1609003 5432129 := bstep (se 2 (by rfl) ⟨2037048, by rfl⟩ : syracuseStep 5432129 = 4074097) B4074097
theorem B3621707 : Blo 1609003 3621707 := bstep (se 1 (by rfl) ⟨2716280, by rfl⟩ : syracuseStep 3621707 = 5432561) B5432561
theorem B3621761 : Blo 1609003 3621761 := bstep (se 2 (by rfl) ⟨1358160, by rfl⟩ : syracuseStep 3621761 = 2716321) B2716321
theorem B1811371 : Blo 1609003 1811371 := bstep (se 1 (by rfl) ⟨1358528, by rfl⟩ : syracuseStep 1811371 = 2717057) B2717057
theorem B1811479 : Blo 1609003 1811479 := bstep (se 1 (by rfl) ⟨1358609, by rfl⟩ : syracuseStep 1811479 = 2717219) B2717219
theorem B11600941 : Blo 1609003 11600941 := bstep (se 3 (by rfl) ⟨2175176, by rfl⟩ : syracuseStep 11600941 = 4350353) B4350353
theorem B6112331 : Blo 1609003 6112331 := bstep (se 1 (by rfl) ⟨4584248, by rfl⟩ : syracuseStep 6112331 = 9168497) B9168497
theorem B3621977 : Blo 1609003 3621977 := bstep (se 2 (by rfl) ⟨1358241, by rfl⟩ : syracuseStep 3621977 = 2716483) B2716483
theorem B11609189 : Blo 1609003 11609189 := bstep (se 4 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 11609189 = 2176723) B2176723
theorem B3622067 : Blo 1609003 3622067 := bstep (se 1 (by rfl) ⟨2716550, by rfl⟩ : syracuseStep 3622067 = 5433101) B5433101
theorem B1811659 : Blo 1609003 1811659 := bstep (se 1 (by rfl) ⟨1358744, by rfl⟩ : syracuseStep 1811659 = 2717489) B2717489
theorem B3622103 : Blo 1609003 3622103 := bstep (se 1 (by rfl) ⟨2716577, by rfl⟩ : syracuseStep 3622103 = 5433155) B5433155
theorem B6112529 : Blo 1609003 6112529 := bstep (se 2 (by rfl) ⟨2292198, by rfl⟩ : syracuseStep 6112529 = 4584397) B4584397
theorem B13755683 : Blo 1609003 13755683 := bstep (se 1 (by rfl) ⟨10316762, by rfl⟩ : syracuseStep 13755683 = 20633525) B20633525
theorem B1811767 : Blo 1609003 1811767 := bstep (se 1 (by rfl) ⟨1358825, by rfl⟩ : syracuseStep 1811767 = 2717651) B2717651
theorem B5432669 : Blo 1609003 5432669 := bstep (se 3 (by rfl) ⟨1018625, by rfl⟩ : syracuseStep 5432669 = 2037251) B2037251
theorem B5506397 : Blo 1609003 5506397 := bstep (se 3 (by rfl) ⟨1032449, by rfl⟩ : syracuseStep 5506397 = 2064899) B2064899
theorem B3622283 : Blo 1609003 3622283 := bstep (se 1 (by rfl) ⟨2716712, by rfl⟩ : syracuseStep 3622283 = 5433425) B5433425
theorem B6874561 : Blo 1609003 6874561 := bstep (se 2 (by rfl) ⟨2577960, by rfl⟩ : syracuseStep 6874561 = 5155921) B5155921
theorem B3622337 : Blo 1609003 3622337 := bstep (se 2 (by rfl) ⟨1358376, by rfl⟩ : syracuseStep 3622337 = 2716753) B2716753
theorem B2614745 : Blo 1609003 2614745 := bstep (se 2 (by rfl) ⟨980529, by rfl⟩ : syracuseStep 2614745 = 1961059) B1961059
theorem B1631723 : Blo 1609003 1631723 := bstep (se 1 (by rfl) ⟨1223792, by rfl⟩ : syracuseStep 1631723 = 2447585) B2447585
theorem B1811947 : Blo 1609003 1811947 := bstep (se 1 (by rfl) ⟨1358960, by rfl⟩ : syracuseStep 1811947 = 2717921) B2717921
theorem B9299501 : Blo 1609003 9299501 := bstep (se 3 (by rfl) ⟨1743656, by rfl⟩ : syracuseStep 9299501 = 3487313) B3487313
theorem B3868211 : Blo 1609003 3868211 := bstep (se 1 (by rfl) ⟨2901158, by rfl⟩ : syracuseStep 3868211 = 5802317) B5802317
theorem B1812055 : Blo 1609003 1812055 := bstep (se 1 (by rfl) ⟨1359041, by rfl⟩ : syracuseStep 1812055 = 2718083) B2718083
theorem B3868249 : Blo 1609003 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B5662297 : Blo 1609003 5662297 := bstep (se 2 (by rfl) ⟨2123361, by rfl⟩ : syracuseStep 5662297 = 4246723) B4246723
theorem B6530653 : Blo 1609003 6530653 := bstep (se 3 (by rfl) ⟨1224497, by rfl⟩ : syracuseStep 6530653 = 2448995) B2448995
theorem B3622553 : Blo 1609003 3622553 := bstep (se 2 (by rfl) ⟨1358457, by rfl⟩ : syracuseStep 3622553 = 2716915) B2716915
theorem B3622643 : Blo 1609003 3622643 := bstep (se 1 (by rfl) ⟨2716982, by rfl⟩ : syracuseStep 3622643 = 5433965) B5433965
theorem B3057419 : Blo 1609003 3057419 := bstep (se 1 (by rfl) ⟨2293064, by rfl⟩ : syracuseStep 3057419 = 4586129) B4586129
theorem B1812235 : Blo 1609003 1812235 := bstep (se 1 (by rfl) ⟨1359176, by rfl⟩ : syracuseStep 1812235 = 2718353) B2718353
theorem B3622679 : Blo 1609003 3622679 := bstep (se 1 (by rfl) ⟨2717009, by rfl⟩ : syracuseStep 3622679 = 5434019) B5434019
theorem B4073267 : Blo 1609003 4073267 := bstep (se 1 (by rfl) ⟨3054950, by rfl⟩ : syracuseStep 4073267 = 6109901) B6109901
theorem B1836875 : Blo 1609003 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B7341913 : Blo 1609003 7341913 := bstep (se 2 (by rfl) ⟨2753217, by rfl⟩ : syracuseStep 7341913 = 5506435) B5506435
theorem B12224357 : Blo 1609003 12224357 := bstep (se 4 (by rfl) ⟨1146033, by rfl⟩ : syracuseStep 12224357 = 2292067) B2292067
theorem B1812343 : Blo 1609003 1812343 := bstep (se 1 (by rfl) ⟨1359257, by rfl⟩ : syracuseStep 1812343 = 2718515) B2718515
theorem B3057601 : Blo 1609003 3057601 := bstep (se 2 (by rfl) ⟨1146600, by rfl⟩ : syracuseStep 3057601 = 2293201) B2293201
theorem B3622859 : Blo 1609003 3622859 := bstep (se 1 (by rfl) ⟨2717144, by rfl⟩ : syracuseStep 3622859 = 5434289) B5434289
theorem B3622913 : Blo 1609003 3622913 := bstep (se 2 (by rfl) ⟨1358592, by rfl⟩ : syracuseStep 3622913 = 2717185) B2717185
theorem B6113303 : Blo 1609003 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B2902081 : Blo 1609003 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B4073561 : Blo 1609003 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B7342169 : Blo 1609003 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B9168997 : Blo 1609003 9168997 := bstep (se 4 (by rfl) ⟨859593, by rfl⟩ : syracuseStep 9168997 = 1719187) B1719187
theorem B3623129 : Blo 1609003 3623129 := bstep (se 2 (by rfl) ⟨1358673, by rfl⟩ : syracuseStep 3623129 = 2717347) B2717347
theorem B6113501 : Blo 1609003 6113501 := bstep (se 3 (by rfl) ⟨1146281, by rfl⟩ : syracuseStep 6113501 = 2292563) B2292563
theorem B3623219 : Blo 1609003 3623219 := bstep (se 1 (by rfl) ⟨2717414, by rfl⟩ : syracuseStep 3623219 = 5434829) B5434829
theorem B12224843 : Blo 1609003 12224843 := bstep (se 1 (by rfl) ⟨9168632, by rfl⟩ : syracuseStep 12224843 = 18337265) B18337265
theorem B3623255 : Blo 1609003 3623255 := bstep (se 1 (by rfl) ⟨2717441, by rfl⟩ : syracuseStep 3623255 = 5434883) B5434883
theorem B3058049 : Blo 1609003 3058049 := bstep (se 2 (by rfl) ⟨1146768, by rfl⟩ : syracuseStep 3058049 = 2293537) B2293537
theorem B5507531 : Blo 1609003 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B5433803 : Blo 1609003 5433803 := bstep (se 1 (by rfl) ⟨4075352, by rfl⟩ : syracuseStep 5433803 = 8150705) B8150705
theorem B7735769 : Blo 1609003 7735769 := bstep (se 2 (by rfl) ⟨2900913, by rfl⟩ : syracuseStep 7735769 = 5801827) B5801827
theorem B3623435 : Blo 1609003 3623435 := bstep (se 1 (by rfl) ⟨2717576, by rfl⟩ : syracuseStep 3623435 = 5435153) B5435153
theorem B3623489 : Blo 1609003 3623489 := bstep (se 2 (by rfl) ⟨1358808, by rfl⟩ : syracuseStep 3623489 = 2717617) B2717617
theorem B23538251 : Blo 1609003 23538251 := bstep (se 1 (by rfl) ⟨17653688, by rfl⟩ : syracuseStep 23538251 = 35307377) B35307377
theorem B49572445 : Blo 1609003 49572445 := bstep (se 3 (by rfl) ⟨9294833, by rfl⟩ : syracuseStep 49572445 = 18589667) B18589667
theorem B5507777 : Blo 1609003 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B3058391 : Blo 1609003 3058391 := bstep (se 1 (by rfl) ⟨2293793, by rfl⟩ : syracuseStep 3058391 = 4587587) B4587587
theorem B5434073 : Blo 1609003 5434073 := bstep (se 2 (by rfl) ⟨2037777, by rfl⟩ : syracuseStep 5434073 = 4075555) B4075555
theorem B3672857 : Blo 1609003 3672857 := bstep (se 2 (by rfl) ⟨1377321, by rfl⟩ : syracuseStep 3672857 = 2754643) B2754643
theorem B3623705 : Blo 1609003 3623705 := bstep (se 2 (by rfl) ⟨1358889, by rfl⟩ : syracuseStep 3623705 = 2717779) B2717779
theorem B5507929 : Blo 1609003 5507929 := bstep (se 2 (by rfl) ⟨2065473, by rfl⟩ : syracuseStep 5507929 = 4130947) B4130947
theorem B15477605 : Blo 1609003 15477605 := bstep (se 4 (by rfl) ⟨1451025, by rfl⟩ : syracuseStep 15477605 = 2902051) B2902051
theorem B3623795 : Blo 1609003 3623795 := bstep (se 1 (by rfl) ⟨2717846, by rfl⟩ : syracuseStep 3623795 = 5435693) B5435693
theorem B6876049 : Blo 1609003 6876049 := bstep (se 2 (by rfl) ⟨2578518, by rfl⟩ : syracuseStep 6876049 = 5157037) B5157037
theorem B3623831 : Blo 1609003 3623831 := bstep (se 1 (by rfl) ⟨2717873, by rfl⟩ : syracuseStep 3623831 = 5435747) B5435747
theorem B3869633 : Blo 1609003 3869633 := bstep (se 2 (by rfl) ⟨1451112, by rfl⟩ : syracuseStep 3869633 = 2902225) B2902225
theorem B3624011 : Blo 1609003 3624011 := bstep (se 1 (by rfl) ⟨2718008, by rfl⟩ : syracuseStep 3624011 = 5436017) B5436017
theorem B4713547 : Blo 1609003 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B3624065 : Blo 1609003 3624065 := bstep (se 2 (by rfl) ⟨1359024, by rfl⟩ : syracuseStep 3624065 = 2718049) B2718049
theorem B3263705 : Blo 1609003 3263705 := bstep (se 2 (by rfl) ⟨1223889, by rfl⟩ : syracuseStep 3263705 = 2447779) B2447779
theorem B1609003 : Blo 1609003 1609003 := bstep (se 1 (by rfl) ⟨1206752, by rfl⟩ : syracuseStep 1609003 = 2413505) B2413505
theorem B4132147 : Blo 1609003 4132147 := bstep (se 1 (by rfl) ⟨3099110, by rfl⟩ : syracuseStep 4132147 = 6198221) B6198221
theorem B1609015 : Blo 1609003 1609015 := bstep (se 1 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 1609015 = 2413523) B2413523
theorem B1609035 : Blo 1609003 1609035 := bstep (se 1 (by rfl) ⟨1206776, by rfl⟩ : syracuseStep 1609035 = 2413553) B2413553
theorem B1609047 : Blo 1609003 1609047 := bstep (se 1 (by rfl) ⟨1206785, by rfl⟩ : syracuseStep 1609047 = 2413571) B2413571
theorem B3624281 : Blo 1609003 3624281 := bstep (se 2 (by rfl) ⟨1359105, by rfl⟩ : syracuseStep 3624281 = 2718211) B2718211
theorem B1609067 : Blo 1609003 1609067 := bstep (se 1 (by rfl) ⟨1206800, by rfl⟩ : syracuseStep 1609067 = 2413601) B2413601
theorem B1609079 : Blo 1609003 1609079 := bstep (se 1 (by rfl) ⟨1206809, by rfl⟩ : syracuseStep 1609079 = 2413619) B2413619
theorem B1609099 : Blo 1609003 1609099 := bstep (se 1 (by rfl) ⟨1206824, by rfl⟩ : syracuseStep 1609099 = 2413649) B2413649
theorem B1609111 : Blo 1609003 1609111 := bstep (se 1 (by rfl) ⟨1206833, by rfl⟩ : syracuseStep 1609111 = 2413667) B2413667
theorem B5434775 : Blo 1609003 5434775 := bstep (se 1 (by rfl) ⟨4076081, by rfl⟩ : syracuseStep 5434775 = 8152163) B8152163
theorem B1609131 : Blo 1609003 1609131 := bstep (se 1 (by rfl) ⟨1206848, by rfl⟩ : syracuseStep 1609131 = 2413697) B2413697
theorem B3624371 : Blo 1609003 3624371 := bstep (se 1 (by rfl) ⟨2718278, by rfl⟩ : syracuseStep 3624371 = 5436557) B5436557
theorem B1609143 : Blo 1609003 1609143 := bstep (se 1 (by rfl) ⟨1206857, by rfl⟩ : syracuseStep 1609143 = 2413715) B2413715
theorem B1609163 : Blo 1609003 1609163 := bstep (se 1 (by rfl) ⟨1206872, by rfl⟩ : syracuseStep 1609163 = 2413745) B2413745
theorem B1609175 : Blo 1609003 1609175 := bstep (se 1 (by rfl) ⟨1206881, by rfl⟩ : syracuseStep 1609175 = 2413763) B2413763
theorem B3624407 : Blo 1609003 3624407 := bstep (se 1 (by rfl) ⟨2718305, by rfl⟩ : syracuseStep 3624407 = 5436611) B5436611
theorem B1609195 : Blo 1609003 1609195 := bstep (se 1 (by rfl) ⟨1206896, by rfl⟩ : syracuseStep 1609195 = 2413793) B2413793
theorem B1609207 : Blo 1609003 1609207 := bstep (se 1 (by rfl) ⟨1206905, by rfl⟩ : syracuseStep 1609207 = 2413811) B2413811
theorem B1609227 : Blo 1609003 1609227 := bstep (se 1 (by rfl) ⟨1206920, by rfl⟩ : syracuseStep 1609227 = 2413841) B2413841
theorem B1609239 : Blo 1609003 1609239 := bstep (se 1 (by rfl) ⟨1206929, by rfl⟩ : syracuseStep 1609239 = 2413859) B2413859
theorem B1609259 : Blo 1609003 1609259 := bstep (se 1 (by rfl) ⟨1206944, by rfl⟩ : syracuseStep 1609259 = 2413889) B2413889
theorem B1609271 : Blo 1609003 1609271 := bstep (se 1 (by rfl) ⟨1206953, by rfl⟩ : syracuseStep 1609271 = 2413907) B2413907
theorem B1609291 : Blo 1609003 1609291 := bstep (se 1 (by rfl) ⟨1206968, by rfl⟩ : syracuseStep 1609291 = 2413937) B2413937
theorem B1609303 : Blo 1609003 1609303 := bstep (se 1 (by rfl) ⟨1206977, by rfl⟩ : syracuseStep 1609303 = 2413955) B2413955
theorem B1609323 : Blo 1609003 1609323 := bstep (se 1 (by rfl) ⟨1206992, by rfl⟩ : syracuseStep 1609323 = 2413985) B2413985
theorem B1609335 : Blo 1609003 1609335 := bstep (se 1 (by rfl) ⟨1207001, by rfl⟩ : syracuseStep 1609335 = 2414003) B2414003
theorem B8154755 : Blo 1609003 8154755 := bstep (se 1 (by rfl) ⟨6116066, by rfl⟩ : syracuseStep 8154755 = 12232133) B12232133
theorem B2715275 : Blo 1609003 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B1609355 : Blo 1609003 1609355 := bstep (se 1 (by rfl) ⟨1207016, by rfl⟩ : syracuseStep 1609355 = 2414033) B2414033
theorem B3624587 : Blo 1609003 3624587 := bstep (se 1 (by rfl) ⟨2718440, by rfl⟩ : syracuseStep 3624587 = 5436881) B5436881
theorem B1609367 : Blo 1609003 1609367 := bstep (se 1 (by rfl) ⟨1207025, by rfl⟩ : syracuseStep 1609367 = 2414051) B2414051
theorem B13749911 : Blo 1609003 13749911 := bstep (se 1 (by rfl) ⟨10312433, by rfl⟩ : syracuseStep 13749911 = 20624867) B20624867
theorem B1609387 : Blo 1609003 1609387 := bstep (se 1 (by rfl) ⟨1207040, by rfl⟩ : syracuseStep 1609387 = 2414081) B2414081
theorem B1609399 : Blo 1609003 1609399 := bstep (se 1 (by rfl) ⟨1207049, by rfl⟩ : syracuseStep 1609399 = 2414099) B2414099
theorem B3624641 : Blo 1609003 3624641 := bstep (se 2 (by rfl) ⟨1359240, by rfl⟩ : syracuseStep 3624641 = 2718481) B2718481
theorem B1609419 : Blo 1609003 1609419 := bstep (se 1 (by rfl) ⟨1207064, by rfl⟩ : syracuseStep 1609419 = 2414129) B2414129
theorem B4075211 : Blo 1609003 4075211 := bstep (se 1 (by rfl) ⟨3056408, by rfl⟩ : syracuseStep 4075211 = 6112817) B6112817
theorem B1609431 : Blo 1609003 1609431 := bstep (se 1 (by rfl) ⟨1207073, by rfl⟩ : syracuseStep 1609431 = 2414147) B2414147
theorem B1609451 : Blo 1609003 1609451 := bstep (se 1 (by rfl) ⟨1207088, by rfl⟩ : syracuseStep 1609451 = 2414177) B2414177
theorem B1609463 : Blo 1609003 1609463 := bstep (se 1 (by rfl) ⟨1207097, by rfl⟩ : syracuseStep 1609463 = 2414195) B2414195
theorem B2715403 : Blo 1609003 2715403 := bstep (se 1 (by rfl) ⟨2036552, by rfl⟩ : syracuseStep 2715403 = 4073105) B4073105
theorem B1609483 : Blo 1609003 1609483 := bstep (se 1 (by rfl) ⟨1207112, by rfl⟩ : syracuseStep 1609483 = 2414225) B2414225
theorem B1609495 : Blo 1609003 1609495 := bstep (se 1 (by rfl) ⟨1207121, by rfl⟩ : syracuseStep 1609495 = 2414243) B2414243
theorem B1609515 : Blo 1609003 1609515 := bstep (se 1 (by rfl) ⟨1207136, by rfl⟩ : syracuseStep 1609515 = 2414273) B2414273
theorem B1609527 : Blo 1609003 1609527 := bstep (se 1 (by rfl) ⟨1207145, by rfl⟩ : syracuseStep 1609527 = 2414291) B2414291
theorem B4353857 : Blo 1609003 4353857 := bstep (se 2 (by rfl) ⟨1632696, by rfl⟩ : syracuseStep 4353857 = 3265393) B3265393
theorem B1609547 : Blo 1609003 1609547 := bstep (se 1 (by rfl) ⟨1207160, by rfl⟩ : syracuseStep 1609547 = 2414321) B2414321
theorem B1609559 : Blo 1609003 1609559 := bstep (se 1 (by rfl) ⟨1207169, by rfl⟩ : syracuseStep 1609559 = 2414339) B2414339
theorem B1609579 : Blo 1609003 1609579 := bstep (se 1 (by rfl) ⟨1207184, by rfl⟩ : syracuseStep 1609579 = 2414369) B2414369
theorem B1609591 : Blo 1609003 1609591 := bstep (se 1 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 1609591 = 2414387) B2414387
theorem B3436427 : Blo 1609003 3436427 := bstep (se 1 (by rfl) ⟨2577320, by rfl⟩ : syracuseStep 3436427 = 5154641) B5154641
theorem B1609611 : Blo 1609003 1609611 := bstep (se 1 (by rfl) ⟨1207208, by rfl⟩ : syracuseStep 1609611 = 2414417) B2414417
theorem B1609623 : Blo 1609003 1609623 := bstep (se 1 (by rfl) ⟨1207217, by rfl⟩ : syracuseStep 1609623 = 2414435) B2414435
theorem B2715545 : Blo 1609003 2715545 := bstep (se 2 (by rfl) ⟨1018329, by rfl⟩ : syracuseStep 2715545 = 2036659) B2036659
theorem B1609643 : Blo 1609003 1609643 := bstep (se 1 (by rfl) ⟨1207232, by rfl⟩ : syracuseStep 1609643 = 2414465) B2414465
theorem B5435315 : Blo 1609003 5435315 := bstep (se 1 (by rfl) ⟨4076486, by rfl⟩ : syracuseStep 5435315 = 8152973) B8152973
theorem B1609655 : Blo 1609003 1609655 := bstep (se 1 (by rfl) ⟨1207241, by rfl⟩ : syracuseStep 1609655 = 2414483) B2414483
theorem B1609675 : Blo 1609003 1609675 := bstep (se 1 (by rfl) ⟨1207256, by rfl⟩ : syracuseStep 1609675 = 2414513) B2414513
theorem B1609687 : Blo 1609003 1609687 := bstep (se 1 (by rfl) ⟨1207265, by rfl⟩ : syracuseStep 1609687 = 2414531) B2414531
theorem B1609707 : Blo 1609003 1609707 := bstep (se 1 (by rfl) ⟨1207280, by rfl⟩ : syracuseStep 1609707 = 2414561) B2414561
theorem B1609719 : Blo 1609003 1609719 := bstep (se 1 (by rfl) ⟨1207289, by rfl⟩ : syracuseStep 1609719 = 2414579) B2414579
theorem B1609739 : Blo 1609003 1609739 := bstep (se 1 (by rfl) ⟨1207304, by rfl⟩ : syracuseStep 1609739 = 2414609) B2414609
theorem B1609751 : Blo 1609003 1609751 := bstep (se 1 (by rfl) ⟨1207313, by rfl⟩ : syracuseStep 1609751 = 2414627) B2414627
theorem B2715673 : Blo 1609003 2715673 := bstep (se 2 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 2715673 = 2036755) B2036755
theorem B1609771 : Blo 1609003 1609771 := bstep (se 1 (by rfl) ⟨1207328, by rfl⟩ : syracuseStep 1609771 = 2414657) B2414657
theorem B1609783 : Blo 1609003 1609783 := bstep (se 1 (by rfl) ⟨1207337, by rfl⟩ : syracuseStep 1609783 = 2414675) B2414675
theorem B1609803 : Blo 1609003 1609803 := bstep (se 1 (by rfl) ⟨1207352, by rfl⟩ : syracuseStep 1609803 = 2414705) B2414705
theorem B7737419 : Blo 1609003 7737419 := bstep (se 1 (by rfl) ⟨5803064, by rfl⟩ : syracuseStep 7737419 = 11606129) B11606129
theorem B1609815 : Blo 1609003 1609815 := bstep (se 1 (by rfl) ⟨1207361, by rfl⟩ : syracuseStep 1609815 = 2414723) B2414723
theorem B1609835 : Blo 1609003 1609835 := bstep (se 1 (by rfl) ⟨1207376, by rfl⟩ : syracuseStep 1609835 = 2414753) B2414753
theorem B1609847 : Blo 1609003 1609847 := bstep (se 1 (by rfl) ⟨1207385, by rfl⟩ : syracuseStep 1609847 = 2414771) B2414771
theorem B6115459 : Blo 1609003 6115459 := bstep (se 1 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 6115459 = 9173189) B9173189
theorem B1609867 : Blo 1609003 1609867 := bstep (se 1 (by rfl) ⟨1207400, by rfl⟩ : syracuseStep 1609867 = 2414801) B2414801
theorem B1609879 : Blo 1609003 1609879 := bstep (se 1 (by rfl) ⟨1207409, by rfl⟩ : syracuseStep 1609879 = 2414819) B2414819
theorem B1609899 : Blo 1609003 1609899 := bstep (se 1 (by rfl) ⟨1207424, by rfl⟩ : syracuseStep 1609899 = 2414849) B2414849
theorem B14127281 : Blo 1609003 14127281 := bstep (se 2 (by rfl) ⟨5297730, by rfl⟩ : syracuseStep 14127281 = 10595461) B10595461
theorem B1609911 : Blo 1609003 1609911 := bstep (se 1 (by rfl) ⟨1207433, by rfl⟩ : syracuseStep 1609911 = 2414867) B2414867
theorem B5435585 : Blo 1609003 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B1814731 : Blo 1609003 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B1609931 : Blo 1609003 1609931 := bstep (se 1 (by rfl) ⟨1207448, by rfl⟩ : syracuseStep 1609931 = 2414897) B2414897
theorem B1609943 : Blo 1609003 1609943 := bstep (se 1 (by rfl) ⟨1207457, by rfl⟩ : syracuseStep 1609943 = 2414915) B2414915
theorem B1609963 : Blo 1609003 1609963 := bstep (se 1 (by rfl) ⟨1207472, by rfl⟩ : syracuseStep 1609963 = 2414945) B2414945
theorem B1609975 : Blo 1609003 1609975 := bstep (se 1 (by rfl) ⟨1207481, by rfl⟩ : syracuseStep 1609975 = 2414963) B2414963
theorem B1609995 : Blo 1609003 1609995 := bstep (se 1 (by rfl) ⟨1207496, by rfl⟩ : syracuseStep 1609995 = 2414993) B2414993
theorem B1610007 : Blo 1609003 1610007 := bstep (se 1 (by rfl) ⟨1207505, by rfl⟩ : syracuseStep 1610007 = 2415011) B2415011
theorem B1610027 : Blo 1609003 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B1610039 : Blo 1609003 1610039 := bstep (se 1 (by rfl) ⟨1207529, by rfl⟩ : syracuseStep 1610039 = 2415059) B2415059
theorem B1610059 : Blo 1609003 1610059 := bstep (se 1 (by rfl) ⟨1207544, by rfl⟩ : syracuseStep 1610059 = 2415089) B2415089
theorem B1610071 : Blo 1609003 1610071 := bstep (se 1 (by rfl) ⟨1207553, by rfl⟩ : syracuseStep 1610071 = 2415107) B2415107
theorem B1610091 : Blo 1609003 1610091 := bstep (se 1 (by rfl) ⟨1207568, by rfl⟩ : syracuseStep 1610091 = 2415137) B2415137
theorem B1610103 : Blo 1609003 1610103 := bstep (se 1 (by rfl) ⟨1207577, by rfl⟩ : syracuseStep 1610103 = 2415155) B2415155
theorem B3436939 : Blo 1609003 3436939 := bstep (se 1 (by rfl) ⟨2577704, by rfl⟩ : syracuseStep 3436939 = 5155409) B5155409
theorem B1610123 : Blo 1609003 1610123 := bstep (se 1 (by rfl) ⟨1207592, by rfl⟩ : syracuseStep 1610123 = 2415185) B2415185
theorem B1610135 : Blo 1609003 1610135 := bstep (se 1 (by rfl) ⟨1207601, by rfl⟩ : syracuseStep 1610135 = 2415203) B2415203
theorem B1610155 : Blo 1609003 1610155 := bstep (se 1 (by rfl) ⟨1207616, by rfl⟩ : syracuseStep 1610155 = 2415233) B2415233
theorem B6115763 : Blo 1609003 6115763 := bstep (se 1 (by rfl) ⟨4586822, by rfl⟩ : syracuseStep 6115763 = 9173645) B9173645
theorem B1610167 : Blo 1609003 1610167 := bstep (se 1 (by rfl) ⟨1207625, by rfl⟩ : syracuseStep 1610167 = 2415251) B2415251
theorem B1610187 : Blo 1609003 1610187 := bstep (se 1 (by rfl) ⟨1207640, by rfl⟩ : syracuseStep 1610187 = 2415281) B2415281
theorem B1610199 : Blo 1609003 1610199 := bstep (se 1 (by rfl) ⟨1207649, by rfl⟩ : syracuseStep 1610199 = 2415299) B2415299
theorem B1610219 : Blo 1609003 1610219 := bstep (se 1 (by rfl) ⟨1207664, by rfl⟩ : syracuseStep 1610219 = 2415329) B2415329
theorem B1610231 : Blo 1609003 1610231 := bstep (se 1 (by rfl) ⟨1207673, by rfl⟩ : syracuseStep 1610231 = 2415347) B2415347
theorem B1610251 : Blo 1609003 1610251 := bstep (se 1 (by rfl) ⟨1207688, by rfl⟩ : syracuseStep 1610251 = 2415377) B2415377
theorem B1610263 : Blo 1609003 1610263 := bstep (se 1 (by rfl) ⟨1207697, by rfl⟩ : syracuseStep 1610263 = 2415395) B2415395
theorem B1610283 : Blo 1609003 1610283 := bstep (se 1 (by rfl) ⟨1207712, by rfl⟩ : syracuseStep 1610283 = 2415425) B2415425
theorem B1610295 : Blo 1609003 1610295 := bstep (se 1 (by rfl) ⟨1207721, by rfl⟩ : syracuseStep 1610295 = 2415443) B2415443
theorem B1610315 : Blo 1609003 1610315 := bstep (se 1 (by rfl) ⟨1207736, by rfl⟩ : syracuseStep 1610315 = 2415473) B2415473
theorem B5231179 : Blo 1609003 5231179 := bstep (se 1 (by rfl) ⟨3923384, by rfl⟩ : syracuseStep 5231179 = 7846769) B7846769
theorem B2716247 : Blo 1609003 2716247 := bstep (se 1 (by rfl) ⟨2037185, by rfl⟩ : syracuseStep 2716247 = 4074371) B4074371
theorem B1610327 : Blo 1609003 1610327 := bstep (se 1 (by rfl) ⟨1207745, by rfl⟩ : syracuseStep 1610327 = 2415491) B2415491
theorem B1610347 : Blo 1609003 1610347 := bstep (se 1 (by rfl) ⟨1207760, by rfl⟩ : syracuseStep 1610347 = 2415521) B2415521
theorem B1610359 : Blo 1609003 1610359 := bstep (se 1 (by rfl) ⟨1207769, by rfl⟩ : syracuseStep 1610359 = 2415539) B2415539
theorem B12219011 : Blo 1609003 12219011 := bstep (se 1 (by rfl) ⟨9164258, by rfl⟩ : syracuseStep 12219011 = 18328517) B18328517
theorem B21189251 : Blo 1609003 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B1610379 : Blo 1609003 1610379 := bstep (se 1 (by rfl) ⟨1207784, by rfl⟩ : syracuseStep 1610379 = 2415569) B2415569
theorem B4076183 : Blo 1609003 4076183 := bstep (se 1 (by rfl) ⟨3057137, by rfl⟩ : syracuseStep 4076183 = 6114275) B6114275
theorem B1610391 : Blo 1609003 1610391 := bstep (se 1 (by rfl) ⟨1207793, by rfl⟩ : syracuseStep 1610391 = 2415587) B2415587
theorem B1610411 : Blo 1609003 1610411 := bstep (se 1 (by rfl) ⟨1207808, by rfl⟩ : syracuseStep 1610411 = 2415617) B2415617
theorem B1610423 : Blo 1609003 1610423 := bstep (se 1 (by rfl) ⟨1207817, by rfl⟩ : syracuseStep 1610423 = 2415635) B2415635
theorem B1610443 : Blo 1609003 1610443 := bstep (se 1 (by rfl) ⟨1207832, by rfl⟩ : syracuseStep 1610443 = 2415665) B2415665
theorem B2716375 : Blo 1609003 2716375 := bstep (se 1 (by rfl) ⟨2037281, by rfl⟩ : syracuseStep 2716375 = 4074563) B4074563
theorem B1610455 : Blo 1609003 1610455 := bstep (se 1 (by rfl) ⟨1207841, by rfl⟩ : syracuseStep 1610455 = 2415683) B2415683
theorem B5436125 : Blo 1609003 5436125 := bstep (se 3 (by rfl) ⟨1019273, by rfl⟩ : syracuseStep 5436125 = 2038547) B2038547
theorem B1610475 : Blo 1609003 1610475 := bstep (se 1 (by rfl) ⟨1207856, by rfl⟩ : syracuseStep 1610475 = 2415713) B2415713
theorem B1610487 : Blo 1609003 1610487 := bstep (se 1 (by rfl) ⟨1207865, by rfl⟩ : syracuseStep 1610487 = 2415731) B2415731
theorem B1610507 : Blo 1609003 1610507 := bstep (se 1 (by rfl) ⟨1207880, by rfl⟩ : syracuseStep 1610507 = 2415761) B2415761
theorem B4584215 : Blo 1609003 4584215 := bstep (se 1 (by rfl) ⟨3438161, by rfl⟩ : syracuseStep 4584215 = 6876323) B6876323
theorem B1610519 : Blo 1609003 1610519 := bstep (se 1 (by rfl) ⟨1207889, by rfl⟩ : syracuseStep 1610519 = 2415779) B2415779
theorem B1610539 : Blo 1609003 1610539 := bstep (se 1 (by rfl) ⟨1207904, by rfl⟩ : syracuseStep 1610539 = 2415809) B2415809
theorem B1610551 : Blo 1609003 1610551 := bstep (se 1 (by rfl) ⟨1207913, by rfl⟩ : syracuseStep 1610551 = 2415827) B2415827
theorem B1610571 : Blo 1609003 1610571 := bstep (se 1 (by rfl) ⟨1207928, by rfl⟩ : syracuseStep 1610571 = 2415857) B2415857
theorem B13759307 : Blo 1609003 13759307 := bstep (se 1 (by rfl) ⟨10319480, by rfl⟩ : syracuseStep 13759307 = 20638961) B20638961
theorem B1610583 : Blo 1609003 1610583 := bstep (se 1 (by rfl) ⟨1207937, by rfl⟩ : syracuseStep 1610583 = 2415875) B2415875
theorem B7844701 : Blo 1609003 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B1610603 : Blo 1609003 1610603 := bstep (se 1 (by rfl) ⟨1207952, by rfl⟩ : syracuseStep 1610603 = 2415905) B2415905
theorem B1610615 : Blo 1609003 1610615 := bstep (se 1 (by rfl) ⟨1207961, by rfl⟩ : syracuseStep 1610615 = 2415923) B2415923
theorem B1610635 : Blo 1609003 1610635 := bstep (se 1 (by rfl) ⟨1207976, by rfl⟩ : syracuseStep 1610635 = 2415953) B2415953
theorem B1610647 : Blo 1609003 1610647 := bstep (se 1 (by rfl) ⟨1207985, by rfl⟩ : syracuseStep 1610647 = 2415971) B2415971
theorem B1610667 : Blo 1609003 1610667 := bstep (se 1 (by rfl) ⟨1208000, by rfl⟩ : syracuseStep 1610667 = 2416001) B2416001
theorem B1610679 : Blo 1609003 1610679 := bstep (se 1 (by rfl) ⟨1208009, by rfl⟩ : syracuseStep 1610679 = 2416019) B2416019
theorem B1610699 : Blo 1609003 1610699 := bstep (se 1 (by rfl) ⟨1208024, by rfl⟩ : syracuseStep 1610699 = 2416049) B2416049
theorem B1610711 : Blo 1609003 1610711 := bstep (se 1 (by rfl) ⟨1208033, by rfl⟩ : syracuseStep 1610711 = 2416067) B2416067
theorem B2413529 : Blo 1609003 2413529 := bstep (se 2 (by rfl) ⟨905073, by rfl⟩ : syracuseStep 2413529 = 1810147) B1810147
theorem B1610731 : Blo 1609003 1610731 := bstep (se 1 (by rfl) ⟨1208048, by rfl⟩ : syracuseStep 1610731 = 2416097) B2416097
theorem B1610743 : Blo 1609003 1610743 := bstep (se 1 (by rfl) ⟨1208057, by rfl⟩ : syracuseStep 1610743 = 2416115) B2416115
theorem B1610763 : Blo 1609003 1610763 := bstep (se 1 (by rfl) ⟨1208072, by rfl⟩ : syracuseStep 1610763 = 2416145) B2416145
theorem B23196689 : Blo 1609003 23196689 := bstep (se 2 (by rfl) ⟨8698758, by rfl⟩ : syracuseStep 23196689 = 17397517) B17397517
theorem B1610775 : Blo 1609003 1610775 := bstep (se 1 (by rfl) ⟨1208081, by rfl⟩ : syracuseStep 1610775 = 2416163) B2416163
theorem B1610795 : Blo 1609003 1610795 := bstep (se 1 (by rfl) ⟨1208096, by rfl⟩ : syracuseStep 1610795 = 2416193) B2416193
theorem B1610807 : Blo 1609003 1610807 := bstep (se 1 (by rfl) ⟨1208105, by rfl⟩ : syracuseStep 1610807 = 2416211) B2416211
theorem B6116417 : Blo 1609003 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B2413643 : Blo 1609003 2413643 := bstep (se 1 (by rfl) ⟨1810232, by rfl⟩ : syracuseStep 2413643 = 3620465) B3620465
theorem B1610827 : Blo 1609003 1610827 := bstep (se 1 (by rfl) ⟨1208120, by rfl⟩ : syracuseStep 1610827 = 2416241) B2416241
theorem B2413655 : Blo 1609003 2413655 := bstep (se 1 (by rfl) ⟨1810241, by rfl⟩ : syracuseStep 2413655 = 3620483) B3620483
theorem B3437657 : Blo 1609003 3437657 := bstep (se 2 (by rfl) ⟨1289121, by rfl⟩ : syracuseStep 3437657 = 2578243) B2578243
theorem B1610839 : Blo 1609003 1610839 := bstep (se 1 (by rfl) ⟨1208129, by rfl⟩ : syracuseStep 1610839 = 2416259) B2416259
theorem B1610859 : Blo 1609003 1610859 := bstep (se 1 (by rfl) ⟨1208144, by rfl⟩ : syracuseStep 1610859 = 2416289) B2416289
theorem B1610871 : Blo 1609003 1610871 := bstep (se 1 (by rfl) ⟨1208153, by rfl⟩ : syracuseStep 1610871 = 2416307) B2416307
theorem B1610891 : Blo 1609003 1610891 := bstep (se 1 (by rfl) ⟨1208168, by rfl⟩ : syracuseStep 1610891 = 2416337) B2416337
theorem B1610903 : Blo 1609003 1610903 := bstep (se 1 (by rfl) ⟨1208177, by rfl⟩ : syracuseStep 1610903 = 2416355) B2416355
theorem B2413721 : Blo 1609003 2413721 := bstep (se 2 (by rfl) ⟨905145, by rfl⟩ : syracuseStep 2413721 = 1810291) B1810291
theorem B1610923 : Blo 1609003 1610923 := bstep (se 1 (by rfl) ⟨1208192, by rfl⟩ : syracuseStep 1610923 = 2416385) B2416385
theorem B1610935 : Blo 1609003 1610935 := bstep (se 1 (by rfl) ⟨1208201, by rfl⟩ : syracuseStep 1610935 = 2416403) B2416403
theorem B1610955 : Blo 1609003 1610955 := bstep (se 1 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 1610955 = 2416433) B2416433
theorem B1610967 : Blo 1609003 1610967 := bstep (se 1 (by rfl) ⟨1208225, by rfl⟩ : syracuseStep 1610967 = 2416451) B2416451
theorem B1610987 : Blo 1609003 1610987 := bstep (se 1 (by rfl) ⟨1208240, by rfl⟩ : syracuseStep 1610987 = 2416481) B2416481
theorem B1610999 : Blo 1609003 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B2413835 : Blo 1609003 2413835 := bstep (se 1 (by rfl) ⟨1810376, by rfl⟩ : syracuseStep 2413835 = 3620753) B3620753
theorem B2413847 : Blo 1609003 2413847 := bstep (se 1 (by rfl) ⟨1810385, by rfl⟩ : syracuseStep 2413847 = 3620771) B3620771
theorem B15471917 : Blo 1609003 15471917 := bstep (se 3 (by rfl) ⟨2900984, by rfl⟩ : syracuseStep 15471917 = 5801969) B5801969
theorem B4076851 : Blo 1609003 4076851 := bstep (se 1 (by rfl) ⟨3057638, by rfl⟩ : syracuseStep 4076851 = 6115277) B6115277
theorem B2717003 : Blo 1609003 2717003 := bstep (se 1 (by rfl) ⟨2037752, by rfl⟩ : syracuseStep 2717003 = 4075505) B4075505
theorem B2037079 : Blo 1609003 2037079 := bstep (se 1 (by rfl) ⟨1527809, by rfl⟩ : syracuseStep 2037079 = 3055619) B3055619
theorem B2413913 : Blo 1609003 2413913 := bstep (se 2 (by rfl) ⟨905217, by rfl⟩ : syracuseStep 2413913 = 1810435) B1810435
theorem B23213411 : Blo 1609003 23213411 := bstep (se 1 (by rfl) ⟨17410058, by rfl⟩ : syracuseStep 23213411 = 34820117) B34820117
theorem B4076993 : Blo 1609003 4076993 := bstep (se 2 (by rfl) ⟨1528872, by rfl⟩ : syracuseStep 4076993 = 3057745) B3057745
theorem B2414027 : Blo 1609003 2414027 := bstep (se 1 (by rfl) ⟨1810520, by rfl⟩ : syracuseStep 2414027 = 3621041) B3621041
theorem B2717131 : Blo 1609003 2717131 := bstep (se 1 (by rfl) ⟨2037848, by rfl⟩ : syracuseStep 2717131 = 4075697) B4075697
theorem B2414039 : Blo 1609003 2414039 := bstep (se 1 (by rfl) ⟨1810529, by rfl⟩ : syracuseStep 2414039 = 3621059) B3621059
theorem B3438067 : Blo 1609003 3438067 := bstep (se 1 (by rfl) ⟨2578550, by rfl⟩ : syracuseStep 3438067 = 5157101) B5157101
theorem B46405133 : Blo 1609003 46405133 := bstep (se 3 (by rfl) ⟨8700962, by rfl⟩ : syracuseStep 46405133 = 17401925) B17401925
theorem B2414105 : Blo 1609003 2414105 := bstep (se 2 (by rfl) ⟨905289, by rfl⟩ : syracuseStep 2414105 = 1810579) B1810579
theorem B2717273 : Blo 1609003 2717273 := bstep (se 2 (by rfl) ⟨1018977, by rfl⟩ : syracuseStep 2717273 = 2037955) B2037955
theorem B2414219 : Blo 1609003 2414219 := bstep (se 1 (by rfl) ⟨1810664, by rfl⟩ : syracuseStep 2414219 = 3621329) B3621329
theorem B2414231 : Blo 1609003 2414231 := bstep (se 1 (by rfl) ⟨1810673, by rfl⟩ : syracuseStep 2414231 = 3621347) B3621347
theorem B2414297 : Blo 1609003 2414297 := bstep (se 2 (by rfl) ⟨905361, by rfl⟩ : syracuseStep 2414297 = 1810723) B1810723
theorem B2717401 : Blo 1609003 2717401 := bstep (se 2 (by rfl) ⟨1019025, by rfl⟩ : syracuseStep 2717401 = 2038051) B2038051
theorem B6616849 : Blo 1609003 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B10319633 : Blo 1609003 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B2414411 : Blo 1609003 2414411 := bstep (se 1 (by rfl) ⟨1810808, by rfl⟩ : syracuseStep 2414411 = 3621617) B3621617
theorem B2414423 : Blo 1609003 2414423 := bstep (se 1 (by rfl) ⟨1810817, by rfl⟩ : syracuseStep 2414423 = 3621635) B3621635
theorem B6879107 : Blo 1609003 6879107 := bstep (se 1 (by rfl) ⟨5159330, by rfl⟩ : syracuseStep 6879107 = 10318661) B10318661
theorem B2414489 : Blo 1609003 2414489 := bstep (se 2 (by rfl) ⟨905433, by rfl⟩ : syracuseStep 2414489 = 1810867) B1810867
theorem B2414603 : Blo 1609003 2414603 := bstep (se 1 (by rfl) ⟨1810952, by rfl⟩ : syracuseStep 2414603 = 3621905) B3621905
theorem B2414615 : Blo 1609003 2414615 := bstep (se 1 (by rfl) ⟨1810961, by rfl⟩ : syracuseStep 2414615 = 3621923) B3621923
theorem B4585547 : Blo 1609003 4585547 := bstep (se 1 (by rfl) ⟨3439160, by rfl⟩ : syracuseStep 4585547 = 6878321) B6878321
theorem B2414681 : Blo 1609003 2414681 := bstep (se 2 (by rfl) ⟨905505, by rfl⟩ : syracuseStep 2414681 = 1811011) B1811011
theorem B8149085 : Blo 1609003 8149085 := bstep (se 3 (by rfl) ⟨1527953, by rfl⟩ : syracuseStep 8149085 = 3055907) B3055907
theorem B2291851 : Blo 1609003 2291851 := bstep (se 1 (by rfl) ⟨1718888, by rfl⟩ : syracuseStep 2291851 = 3437777) B3437777
theorem B2037899 : Blo 1609003 2037899 := bstep (se 1 (by rfl) ⟨1528424, by rfl⟩ : syracuseStep 2037899 = 3056849) B3056849
theorem B39172247 : Blo 1609003 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B2414795 : Blo 1609003 2414795 := bstep (se 1 (by rfl) ⟨1811096, by rfl⟩ : syracuseStep 2414795 = 3622193) B3622193
theorem B2414807 : Blo 1609003 2414807 := bstep (se 1 (by rfl) ⟨1811105, by rfl⟩ : syracuseStep 2414807 = 3622211) B3622211
theorem B2717975 : Blo 1609003 2717975 := bstep (se 1 (by rfl) ⟨2038481, by rfl⟩ : syracuseStep 2717975 = 4076963) B4076963
theorem B2414873 : Blo 1609003 2414873 := bstep (se 2 (by rfl) ⟨905577, by rfl⟩ : syracuseStep 2414873 = 1811155) B1811155
theorem B1718615 : Blo 1609003 1718615 := bstep (se 1 (by rfl) ⟨1288961, by rfl⟩ : syracuseStep 1718615 = 2577923) B2577923
theorem B9165149 : Blo 1609003 9165149 := bstep (se 3 (by rfl) ⟨1718465, by rfl⟩ : syracuseStep 9165149 = 3436931) B3436931
theorem B2414987 : Blo 1609003 2414987 := bstep (se 1 (by rfl) ⟨1811240, by rfl⟩ : syracuseStep 2414987 = 3622481) B3622481
theorem B2414999 : Blo 1609003 2414999 := bstep (se 1 (by rfl) ⟨1811249, by rfl⟩ : syracuseStep 2414999 = 3622499) B3622499
theorem B2718103 : Blo 1609003 2718103 := bstep (se 1 (by rfl) ⟨2038577, by rfl⟩ : syracuseStep 2718103 = 4077155) B4077155
theorem B6109613 : Blo 1609003 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B1718743 : Blo 1609003 1718743 := bstep (se 1 (by rfl) ⟨1289057, by rfl⟩ : syracuseStep 1718743 = 2578115) B2578115
theorem B2415065 : Blo 1609003 2415065 := bstep (se 2 (by rfl) ⟨905649, by rfl⟩ : syracuseStep 2415065 = 1811299) B1811299
theorem B9787979 : Blo 1609003 9787979 := bstep (se 1 (by rfl) ⟨7340984, by rfl⟩ : syracuseStep 9787979 = 14681969) B14681969
theorem B2415179 : Blo 1609003 2415179 := bstep (se 1 (by rfl) ⟨1811384, by rfl⟩ : syracuseStep 2415179 = 3622769) B3622769
theorem B2415191 : Blo 1609003 2415191 := bstep (se 1 (by rfl) ⟨1811393, by rfl⟩ : syracuseStep 2415191 = 3622787) B3622787
theorem B8706653 : Blo 1609003 8706653 := bstep (se 3 (by rfl) ⟨1632497, by rfl⟩ : syracuseStep 8706653 = 3264995) B3264995
theorem B3439255 : Blo 1609003 3439255 := bstep (se 1 (by rfl) ⟨2579441, by rfl⟩ : syracuseStep 3439255 = 5158883) B5158883
theorem B2415257 : Blo 1609003 2415257 := bstep (se 2 (by rfl) ⟨905721, by rfl⟩ : syracuseStep 2415257 = 1811443) B1811443
theorem B3439297 : Blo 1609003 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B6617821 : Blo 1609003 6617821 := bstep (se 3 (by rfl) ⟨1240841, by rfl⟩ : syracuseStep 6617821 = 2481683) B2481683
theorem B2415371 : Blo 1609003 2415371 := bstep (se 1 (by rfl) ⟨1811528, by rfl⟩ : syracuseStep 2415371 = 3623057) B3623057
theorem B2415383 : Blo 1609003 2415383 := bstep (se 1 (by rfl) ⟨1811537, by rfl⟩ : syracuseStep 2415383 = 3623075) B3623075
theorem B11606819 : Blo 1609003 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B2038603 : Blo 1609003 2038603 := bstep (se 1 (by rfl) ⟨1528952, by rfl⟩ : syracuseStep 2038603 = 3057905) B3057905
theorem B2415449 : Blo 1609003 2415449 := bstep (se 2 (by rfl) ⟨905793, by rfl⟩ : syracuseStep 2415449 = 1811587) B1811587
theorem B8608643 : Blo 1609003 8608643 := bstep (se 1 (by rfl) ⟨6456482, by rfl⟩ : syracuseStep 8608643 = 12912965) B12912965
theorem B2579339 : Blo 1609003 2579339 := bstep (se 1 (by rfl) ⟨1934504, by rfl⟩ : syracuseStep 2579339 = 3869009) B3869009
theorem B2415563 : Blo 1609003 2415563 := bstep (se 1 (by rfl) ⟨1811672, by rfl⟩ : syracuseStep 2415563 = 3623345) B3623345
theorem B2415575 : Blo 1609003 2415575 := bstep (se 1 (by rfl) ⟨1811681, by rfl⟩ : syracuseStep 2415575 = 3623363) B3623363
theorem B1719307 : Blo 1609003 1719307 := bstep (se 1 (by rfl) ⟨1289480, by rfl⟩ : syracuseStep 1719307 = 2578961) B2578961
theorem B2415641 : Blo 1609003 2415641 := bstep (se 2 (by rfl) ⟨905865, by rfl⟩ : syracuseStep 2415641 = 1811731) B1811731
theorem B9165899 : Blo 1609003 9165899 := bstep (se 1 (by rfl) ⟨6874424, by rfl⟩ : syracuseStep 9165899 = 13748849) B13748849
theorem B2038871 : Blo 1609003 2038871 := bstep (se 1 (by rfl) ⟨1529153, by rfl⟩ : syracuseStep 2038871 = 3058307) B3058307
theorem B2415755 : Blo 1609003 2415755 := bstep (se 1 (by rfl) ⟨1811816, by rfl⟩ : syracuseStep 2415755 = 3623633) B3623633
theorem B2415767 : Blo 1609003 2415767 := bstep (se 1 (by rfl) ⟨1811825, by rfl⟩ : syracuseStep 2415767 = 3623651) B3623651
theorem B6110387 : Blo 1609003 6110387 := bstep (se 1 (by rfl) ⟨4582790, by rfl⟩ : syracuseStep 6110387 = 9165581) B9165581
theorem B2415833 : Blo 1609003 2415833 := bstep (se 2 (by rfl) ⟨905937, by rfl⟩ : syracuseStep 2415833 = 1811875) B1811875
theorem B6282461 : Blo 1609003 6282461 := bstep (se 3 (by rfl) ⟨1177961, by rfl⟩ : syracuseStep 6282461 = 2355923) B2355923
theorem B1719563 : Blo 1609003 1719563 := bstep (se 1 (by rfl) ⟨1289672, by rfl⟩ : syracuseStep 1719563 = 2579345) B2579345
theorem B2415947 : Blo 1609003 2415947 := bstep (se 1 (by rfl) ⟨1811960, by rfl⟩ : syracuseStep 2415947 = 3623921) B3623921
theorem B3054935 : Blo 1609003 3054935 := bstep (se 1 (by rfl) ⟨2291201, by rfl⟩ : syracuseStep 3054935 = 4582403) B4582403
theorem B2415959 : Blo 1609003 2415959 := bstep (se 1 (by rfl) ⟨1811969, by rfl⟩ : syracuseStep 2415959 = 3623939) B3623939
theorem B5430617 : Blo 1609003 5430617 := bstep (se 2 (by rfl) ⟨2036481, by rfl⟩ : syracuseStep 5430617 = 4072963) B4072963
theorem B27508085 : Blo 1609003 27508085 := bstep (se 5 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 27508085 = 2578883) B2578883
theorem B2416025 : Blo 1609003 2416025 := bstep (se 2 (by rfl) ⟨906009, by rfl⟩ : syracuseStep 2416025 = 1812019) B1812019
theorem B13761971 : Blo 1609003 13761971 := bstep (se 1 (by rfl) ⟨10321478, by rfl⟩ : syracuseStep 13761971 = 20642957) B20642957
theorem B13950425 : Blo 1609003 13950425 := bstep (se 2 (by rfl) ⟨5231409, by rfl⟩ : syracuseStep 13950425 = 10462819) B10462819
theorem B3620339 : Blo 1609003 3620339 := bstep (se 1 (by rfl) ⟨2715254, by rfl⟩ : syracuseStep 3620339 = 5430509) B5430509
theorem B2416139 : Blo 1609003 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B3620375 : Blo 1609003 3620375 := bstep (se 1 (by rfl) ⟨2715281, by rfl⟩ : syracuseStep 3620375 = 5430563) B5430563
theorem B2416151 : Blo 1609003 2416151 := bstep (se 1 (by rfl) ⟨1812113, by rfl⟩ : syracuseStep 2416151 = 3624227) B3624227
theorem B12230189 : Blo 1609003 12230189 := bstep (se 3 (by rfl) ⟨2293160, by rfl⟩ : syracuseStep 12230189 = 4586321) B4586321
theorem B5226059 : Blo 1609003 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B5160523 : Blo 1609003 5160523 := bstep (se 1 (by rfl) ⟨3870392, by rfl⟩ : syracuseStep 5160523 = 7740785) B7740785
theorem B2416217 : Blo 1609003 2416217 := bstep (se 2 (by rfl) ⟨906081, by rfl⟩ : syracuseStep 2416217 = 1812163) B1812163
theorem B4587187 : Blo 1609003 4587187 := bstep (se 1 (by rfl) ⟨3440390, by rfl⟩ : syracuseStep 4587187 = 6880781) B6880781
theorem B3620555 : Blo 1609003 3620555 := bstep (se 1 (by rfl) ⟨2715416, by rfl⟩ : syracuseStep 3620555 = 5430833) B5430833
theorem B2416331 : Blo 1609003 2416331 := bstep (se 1 (by rfl) ⟨1812248, by rfl⟩ : syracuseStep 2416331 = 3624497) B3624497
theorem B2416343 : Blo 1609003 2416343 := bstep (se 1 (by rfl) ⟨1812257, by rfl⟩ : syracuseStep 2416343 = 3624515) B3624515
theorem B11009753 : Blo 1609003 11009753 := bstep (se 2 (by rfl) ⟨4128657, by rfl⟩ : syracuseStep 11009753 = 8257315) B8257315
theorem B3620609 : Blo 1609003 3620609 := bstep (se 2 (by rfl) ⟨1357728, by rfl⟩ : syracuseStep 3620609 = 2715457) B2715457
theorem B2416409 : Blo 1609003 2416409 := bstep (se 2 (by rfl) ⟨906153, by rfl⟩ : syracuseStep 2416409 = 1812307) B1812307
theorem B1810219 : Blo 1609003 1810219 := bstep (se 1 (by rfl) ⟨1357664, by rfl⟩ : syracuseStep 1810219 = 2715329) B2715329
theorem B9174829 : Blo 1609003 9174829 := bstep (se 3 (by rfl) ⟨1720280, by rfl⟩ : syracuseStep 9174829 = 3440561) B3440561
theorem B4349747 : Blo 1609003 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B6872921 : Blo 1609003 6872921 := bstep (se 2 (by rfl) ⟨2577345, by rfl⟩ : syracuseStep 6872921 = 5154691) B5154691
theorem B1834859 : Blo 1609003 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B3055475 : Blo 1609003 3055475 := bstep (se 1 (by rfl) ⟨2291606, by rfl⟩ : syracuseStep 3055475 = 4583213) B4583213
theorem B1810327 : Blo 1609003 1810327 := bstep (se 1 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 1810327 = 2715491) B2715491
theorem B7339979 : Blo 1609003 7339979 := bstep (se 1 (by rfl) ⟨5504984, by rfl⟩ : syracuseStep 7339979 = 11009969) B11009969
theorem B12222413 : Blo 1609003 12222413 := bstep (se 3 (by rfl) ⟨2291702, by rfl⟩ : syracuseStep 12222413 = 4583405) B4583405
theorem B3620825 : Blo 1609003 3620825 := bstep (se 2 (by rfl) ⟨1357809, by rfl⟩ : syracuseStep 3620825 = 2715619) B2715619
theorem B8708057 : Blo 1609003 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B5160971 : Blo 1609003 5160971 := bstep (se 1 (by rfl) ⟨3870728, by rfl⟩ : syracuseStep 5160971 = 7741457) B7741457
theorem B3620879 : Blo 1609003 3620879 := bstep (se 1 (by rfl) ⟨2715659, by rfl⟩ : syracuseStep 3620879 = 5431319) B5431319
theorem B8257565 : Blo 1609003 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B3620897 : Blo 1609003 3620897 := bstep (se 2 (by rfl) ⟨1357836, by rfl⟩ : syracuseStep 3620897 = 2715673) B2715673
theorem B3055801 : Blo 1609003 3055801 := bstep (se 2 (by rfl) ⟨1145925, by rfl⟩ : syracuseStep 3055801 = 2291851) B2291851
theorem B19579117 : Blo 1609003 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B3621239 : Blo 1609003 3621239 := bstep (se 1 (by rfl) ⟨2715929, by rfl⟩ : syracuseStep 3621239 = 5431859) B5431859
theorem B1810831 : Blo 1609003 1810831 := bstep (se 1 (by rfl) ⟨1358123, by rfl⟩ : syracuseStep 1810831 = 2716247) B2716247
theorem B14680541 : Blo 1609003 14680541 := bstep (se 3 (by rfl) ⟨2752601, by rfl⟩ : syracuseStep 14680541 = 5505203) B5505203
theorem B3056143 : Blo 1609003 3056143 := bstep (se 1 (by rfl) ⟨2292107, by rfl⟩ : syracuseStep 3056143 = 4584215) B4584215
theorem B3621419 : Blo 1609003 3621419 := bstep (se 1 (by rfl) ⟨2716064, by rfl⟩ : syracuseStep 3621419 = 5432129) B5432129
theorem B10314611 : Blo 1609003 10314611 := bstep (se 1 (by rfl) ⟨7735958, by rfl⟩ : syracuseStep 10314611 = 15471917) B15471917
theorem B1811335 : Blo 1609003 1811335 := bstep (se 1 (by rfl) ⟨1358501, by rfl⟩ : syracuseStep 1811335 = 2717003) B2717003
theorem B3670931 : Blo 1609003 3670931 := bstep (se 1 (by rfl) ⟨2753198, by rfl⟩ : syracuseStep 3670931 = 5506397) B5506397
theorem B3621779 : Blo 1609003 3621779 := bstep (se 1 (by rfl) ⟨2716334, by rfl⟩ : syracuseStep 3621779 = 5432669) B5432669
theorem B15475607 : Blo 1609003 15475607 := bstep (se 1 (by rfl) ⟨11606705, by rfl⟩ : syracuseStep 15475607 = 23213411) B23213411
theorem B12223385 : Blo 1609003 12223385 := bstep (se 2 (by rfl) ⟨4583769, by rfl⟩ : syracuseStep 12223385 = 9167539) B9167539
theorem B3621833 : Blo 1609003 3621833 := bstep (se 2 (by rfl) ⟨1358187, by rfl⟩ : syracuseStep 3621833 = 2716375) B2716375
theorem B8823761 : Blo 1609003 8823761 := bstep (se 2 (by rfl) ⟨3308910, by rfl⟩ : syracuseStep 8823761 = 6617821) B6617821
theorem B1811515 : Blo 1609003 1811515 := bstep (se 1 (by rfl) ⟨1358636, by rfl⟩ : syracuseStep 1811515 = 2717273) B2717273
theorem B9168065 : Blo 1609003 9168065 := bstep (se 2 (by rfl) ⟨3438024, by rfl⟩ : syracuseStep 9168065 = 6876049) B6876049
theorem B37201133 : Blo 1609003 37201133 := bstep (se 3 (by rfl) ⟨6975212, by rfl⟩ : syracuseStep 37201133 = 13950425) B13950425
theorem B4351261 : Blo 1609003 4351261 := bstep (se 3 (by rfl) ⟨815861, by rfl⟩ : syracuseStep 4351261 = 1631723) B1631723
theorem B3057031 : Blo 1609003 3057031 := bstep (se 1 (by rfl) ⟨2292773, by rfl⟩ : syracuseStep 3057031 = 4585547) B4585547
theorem B15467921 : Blo 1609003 15467921 := bstep (se 2 (by rfl) ⟨5800470, by rfl⟩ : syracuseStep 15467921 = 11600941) B11600941
theorem B5432723 : Blo 1609003 5432723 := bstep (se 1 (by rfl) ⟨4074542, by rfl⟩ : syracuseStep 5432723 = 8149085) B8149085
theorem B6284729 : Blo 1609003 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B1811983 : Blo 1609003 1811983 := bstep (se 1 (by rfl) ⟨1358987, by rfl⟩ : syracuseStep 1811983 = 2717975) B2717975
theorem B13936157 : Blo 1609003 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B26101277 : Blo 1609003 26101277 := bstep (se 3 (by rfl) ⟨4893989, by rfl⟩ : syracuseStep 26101277 = 9787979) B9787979
theorem B4073075 : Blo 1609003 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B3671687 : Blo 1609003 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B3622535 : Blo 1609003 3622535 := bstep (se 1 (by rfl) ⟨2716901, by rfl⟩ : syracuseStep 3622535 = 5433803) B5433803
theorem B3622715 : Blo 1609003 3622715 := bstep (se 1 (by rfl) ⟨2717036, by rfl⟩ : syracuseStep 3622715 = 5434073) B5434073
theorem B3622841 : Blo 1609003 3622841 := bstep (se 2 (by rfl) ⟨1358565, by rfl⟩ : syracuseStep 3622841 = 2717131) B2717131
theorem B30951517 : Blo 1609003 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B4073591 : Blo 1609003 4073591 := bstep (se 1 (by rfl) ⟨3055193, by rfl⟩ : syracuseStep 4073591 = 6110387) B6110387
theorem B4188307 : Blo 1609003 4188307 := bstep (se 1 (by rfl) ⟨3141230, by rfl⟩ : syracuseStep 4188307 = 6282461) B6282461
theorem B3623183 : Blo 1609003 3623183 := bstep (se 1 (by rfl) ⟨2717387, by rfl⟩ : syracuseStep 3623183 = 5434775) B5434775
theorem B4892957 : Blo 1609003 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B3623201 : Blo 1609003 3623201 := bstep (se 2 (by rfl) ⟨1358700, by rfl⟩ : syracuseStep 3623201 = 2717401) B2717401
theorem B8153459 : Blo 1609003 8153459 := bstep (se 1 (by rfl) ⟨6115094, by rfl⟩ : syracuseStep 8153459 = 12230189) B12230189
theorem B12233105 : Blo 1609003 12233105 := bstep (se 2 (by rfl) ⟨4587414, by rfl⟩ : syracuseStep 12233105 = 9174829) B9174829
theorem B2902571 : Blo 1609003 2902571 := bstep (se 1 (by rfl) ⟨2176928, by rfl⟩ : syracuseStep 2902571 = 4353857) B4353857
theorem B4581947 : Blo 1609003 4581947 := bstep (se 1 (by rfl) ⟨3436460, by rfl⟩ : syracuseStep 4581947 = 6872921) B6872921
theorem B3623543 : Blo 1609003 3623543 := bstep (se 1 (by rfl) ⟨2717657, by rfl⟩ : syracuseStep 3623543 = 5435315) B5435315
theorem B4893319 : Blo 1609003 4893319 := bstep (se 1 (by rfl) ⟨3669989, by rfl⟩ : syracuseStep 4893319 = 7339979) B7339979
theorem B3869441 : Blo 1609003 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B5434127 : Blo 1609003 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B3623723 : Blo 1609003 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B12225329 : Blo 1609003 12225329 := bstep (se 2 (by rfl) ⟨4584498, by rfl⟩ : syracuseStep 12225329 = 9168997) B9168997
theorem B8153945 : Blo 1609003 8153945 := bstep (se 2 (by rfl) ⟨3057729, by rfl⟩ : syracuseStep 8153945 = 6115459) B6115459
theorem B5434397 : Blo 1609003 5434397 := bstep (se 3 (by rfl) ⟨1018949, by rfl⟩ : syracuseStep 5434397 = 2037899) B2037899
theorem B8146007 : Blo 1609003 8146007 := bstep (se 1 (by rfl) ⟨6109505, by rfl⟩ : syracuseStep 8146007 = 12219011) B12219011
theorem B14126167 : Blo 1609003 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B4074583 : Blo 1609003 4074583 := bstep (se 1 (by rfl) ⟨3055937, by rfl⟩ : syracuseStep 4074583 = 6111875) B6111875
theorem B3624083 : Blo 1609003 3624083 := bstep (se 1 (by rfl) ⟨2718062, by rfl⟩ : syracuseStep 3624083 = 5436125) B5436125
theorem B4582585 : Blo 1609003 4582585 := bstep (se 2 (by rfl) ⟨1718469, by rfl⟩ : syracuseStep 4582585 = 3436939) B3436939
theorem B3624137 : Blo 1609003 3624137 := bstep (se 2 (by rfl) ⟨1359051, by rfl⟩ : syracuseStep 3624137 = 2718103) B2718103
theorem B1609019 : Blo 1609003 1609019 := bstep (se 1 (by rfl) ⟨1206764, by rfl⟩ : syracuseStep 1609019 = 2413529) B2413529
theorem B4074887 : Blo 1609003 4074887 := bstep (se 1 (by rfl) ⟨3056165, by rfl⟩ : syracuseStep 4074887 = 6112331) B6112331
theorem B1609095 : Blo 1609003 1609095 := bstep (se 1 (by rfl) ⟨1206821, by rfl⟩ : syracuseStep 1609095 = 2413643) B2413643
theorem B1609103 : Blo 1609003 1609103 := bstep (se 1 (by rfl) ⟨1206827, by rfl⟩ : syracuseStep 1609103 = 2413655) B2413655
theorem B6974905 : Blo 1609003 6974905 := bstep (se 2 (by rfl) ⟨2615589, by rfl⟩ : syracuseStep 6974905 = 5231179) B5231179
theorem B1609147 : Blo 1609003 1609147 := bstep (se 1 (by rfl) ⟨1206860, by rfl⟩ : syracuseStep 1609147 = 2413721) B2413721
theorem B66096593 : Blo 1609003 66096593 := bstep (se 2 (by rfl) ⟨24786222, by rfl⟩ : syracuseStep 66096593 = 49572445) B49572445
theorem B1609223 : Blo 1609003 1609223 := bstep (se 1 (by rfl) ⟨1206917, by rfl⟩ : syracuseStep 1609223 = 2413835) B2413835
theorem B4075019 : Blo 1609003 4075019 := bstep (se 1 (by rfl) ⟨3056264, by rfl⟩ : syracuseStep 4075019 = 6112529) B6112529
theorem B1609231 : Blo 1609003 1609231 := bstep (se 1 (by rfl) ⟨1206923, by rfl⟩ : syracuseStep 1609231 = 2413847) B2413847
theorem B9170455 : Blo 1609003 9170455 := bstep (se 1 (by rfl) ⟨6877841, by rfl⟩ : syracuseStep 9170455 = 13755683) B13755683
theorem B1609275 : Blo 1609003 1609275 := bstep (se 1 (by rfl) ⟨1206956, by rfl⟩ : syracuseStep 1609275 = 2413913) B2413913
theorem B8146493 : Blo 1609003 8146493 := bstep (se 3 (by rfl) ⟨1527467, by rfl⟩ : syracuseStep 8146493 = 3054935) B3054935
theorem B4582973 : Blo 1609003 4582973 := bstep (se 3 (by rfl) ⟨859307, by rfl⟩ : syracuseStep 4582973 = 1718615) B1718615
theorem B1609351 : Blo 1609003 1609351 := bstep (se 1 (by rfl) ⟨1207013, by rfl⟩ : syracuseStep 1609351 = 2414027) B2414027
theorem B1609359 : Blo 1609003 1609359 := bstep (se 1 (by rfl) ⟨1207019, by rfl⟩ : syracuseStep 1609359 = 2414039) B2414039
theorem B30936755 : Blo 1609003 30936755 := bstep (se 1 (by rfl) ⟨23202566, by rfl⟩ : syracuseStep 30936755 = 46405133) B46405133
theorem B1609403 : Blo 1609003 1609403 := bstep (se 1 (by rfl) ⟨1207052, by rfl⟩ : syracuseStep 1609403 = 2414105) B2414105
theorem B9678565 : Blo 1609003 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B1609479 : Blo 1609003 1609479 := bstep (se 1 (by rfl) ⟨1207109, by rfl⟩ : syracuseStep 1609479 = 2414219) B2414219
theorem B1609487 : Blo 1609003 1609487 := bstep (se 1 (by rfl) ⟨1207115, by rfl⟩ : syracuseStep 1609487 = 2414231) B2414231
theorem B7343905 : Blo 1609003 7343905 := bstep (se 2 (by rfl) ⟨2753964, by rfl⟩ : syracuseStep 7343905 = 5507929) B5507929
theorem B1609531 : Blo 1609003 1609531 := bstep (se 1 (by rfl) ⟨1207148, by rfl⟩ : syracuseStep 1609531 = 2414297) B2414297
theorem B2715511 : Blo 1609003 2715511 := bstep (se 1 (by rfl) ⟨2036633, by rfl⟩ : syracuseStep 2715511 = 4073267) B4073267
theorem B1609607 : Blo 1609003 1609607 := bstep (se 1 (by rfl) ⟨1207205, by rfl⟩ : syracuseStep 1609607 = 2414411) B2414411
theorem B1609615 : Blo 1609003 1609615 := bstep (se 1 (by rfl) ⟨1207211, by rfl⟩ : syracuseStep 1609615 = 2414423) B2414423
theorem B1609659 : Blo 1609003 1609659 := bstep (se 1 (by rfl) ⟨1207244, by rfl⟩ : syracuseStep 1609659 = 2414489) B2414489
theorem B1609735 : Blo 1609003 1609735 := bstep (se 1 (by rfl) ⟨1207301, by rfl⟩ : syracuseStep 1609735 = 2414603) B2414603
theorem B1609743 : Blo 1609003 1609743 := bstep (se 1 (by rfl) ⟨1207307, by rfl⟩ : syracuseStep 1609743 = 2414615) B2414615
theorem B4075535 : Blo 1609003 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B2715707 : Blo 1609003 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B1609787 : Blo 1609003 1609787 := bstep (se 1 (by rfl) ⟨1207340, by rfl⟩ : syracuseStep 1609787 = 2414681) B2414681
theorem B1609863 : Blo 1609003 1609863 := bstep (se 1 (by rfl) ⟨1207397, by rfl⟩ : syracuseStep 1609863 = 2414795) B2414795
theorem B1609871 : Blo 1609003 1609871 := bstep (se 1 (by rfl) ⟨1207403, by rfl⟩ : syracuseStep 1609871 = 2414807) B2414807
theorem B4075667 : Blo 1609003 4075667 := bstep (se 1 (by rfl) ⟨3056750, by rfl⟩ : syracuseStep 4075667 = 6113501) B6113501
theorem B1609915 : Blo 1609003 1609915 := bstep (se 1 (by rfl) ⟨1207436, by rfl⟩ : syracuseStep 1609915 = 2414873) B2414873
theorem B1609991 : Blo 1609003 1609991 := bstep (se 1 (by rfl) ⟨1207493, by rfl⟩ : syracuseStep 1609991 = 2414987) B2414987
theorem B1609999 : Blo 1609003 1609999 := bstep (se 1 (by rfl) ⟨1207499, by rfl⟩ : syracuseStep 1609999 = 2414999) B2414999
theorem B5157179 : Blo 1609003 5157179 := bstep (se 1 (by rfl) ⟨3867884, by rfl⟩ : syracuseStep 5157179 = 7735769) B7735769
theorem B1610043 : Blo 1609003 1610043 := bstep (se 1 (by rfl) ⟨1207532, by rfl⟩ : syracuseStep 1610043 = 2415065) B2415065
theorem B1610119 : Blo 1609003 1610119 := bstep (se 1 (by rfl) ⟨1207589, by rfl⟩ : syracuseStep 1610119 = 2415179) B2415179
theorem B15692167 : Blo 1609003 15692167 := bstep (se 1 (by rfl) ⟨11769125, by rfl⟩ : syracuseStep 15692167 = 23538251) B23538251
theorem B1610127 : Blo 1609003 1610127 := bstep (se 1 (by rfl) ⟨1207595, by rfl⟩ : syracuseStep 1610127 = 2415191) B2415191
theorem B5804435 : Blo 1609003 5804435 := bstep (se 1 (by rfl) ⟨4353326, by rfl⟩ : syracuseStep 5804435 = 8706653) B8706653
theorem B5509529 : Blo 1609003 5509529 := bstep (se 2 (by rfl) ⟨2066073, by rfl⟩ : syracuseStep 5509529 = 4132147) B4132147
theorem B5435801 : Blo 1609003 5435801 := bstep (se 2 (by rfl) ⟨2038425, by rfl⟩ : syracuseStep 5435801 = 4076851) B4076851
theorem B1610171 : Blo 1609003 1610171 := bstep (se 1 (by rfl) ⟨1207628, by rfl⟩ : syracuseStep 1610171 = 2415257) B2415257
theorem B2716105 : Blo 1609003 2716105 := bstep (se 2 (by rfl) ⟨1018539, by rfl⟩ : syracuseStep 2716105 = 2037079) B2037079
theorem B1610247 : Blo 1609003 1610247 := bstep (se 1 (by rfl) ⟨1207685, by rfl⟩ : syracuseStep 1610247 = 2415371) B2415371
theorem B1610255 : Blo 1609003 1610255 := bstep (se 1 (by rfl) ⟨1207691, by rfl⟩ : syracuseStep 1610255 = 2415383) B2415383
theorem B1610299 : Blo 1609003 1610299 := bstep (se 1 (by rfl) ⟨1207724, by rfl⟩ : syracuseStep 1610299 = 2415449) B2415449
theorem B10318403 : Blo 1609003 10318403 := bstep (se 1 (by rfl) ⟨7738802, by rfl⟩ : syracuseStep 10318403 = 15477605) B15477605
theorem B5739095 : Blo 1609003 5739095 := bstep (se 1 (by rfl) ⟨4304321, by rfl⟩ : syracuseStep 5739095 = 8608643) B8608643
theorem B1610375 : Blo 1609003 1610375 := bstep (se 1 (by rfl) ⟨1207781, by rfl⟩ : syracuseStep 1610375 = 2415563) B2415563
theorem B1610383 : Blo 1609003 1610383 := bstep (se 1 (by rfl) ⟨1207787, by rfl⟩ : syracuseStep 1610383 = 2415575) B2415575
theorem B4584089 : Blo 1609003 4584089 := bstep (se 2 (by rfl) ⟨1719033, by rfl⟩ : syracuseStep 4584089 = 3438067) B3438067
theorem B1610427 : Blo 1609003 1610427 := bstep (se 1 (by rfl) ⟨1207820, by rfl⟩ : syracuseStep 1610427 = 2415641) B2415641
theorem B1610503 : Blo 1609003 1610503 := bstep (se 1 (by rfl) ⟨1207877, by rfl⟩ : syracuseStep 1610503 = 2415755) B2415755
theorem B1610511 : Blo 1609003 1610511 := bstep (se 1 (by rfl) ⟨1207883, by rfl⟩ : syracuseStep 1610511 = 2415767) B2415767
theorem B5157665 : Blo 1609003 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B7549729 : Blo 1609003 7549729 := bstep (se 2 (by rfl) ⟨2831148, by rfl⟩ : syracuseStep 7549729 = 5662297) B5662297
theorem B2175803 : Blo 1609003 2175803 := bstep (se 1 (by rfl) ⟨1631852, by rfl⟩ : syracuseStep 2175803 = 3263705) B3263705
theorem B1610555 : Blo 1609003 1610555 := bstep (se 1 (by rfl) ⟨1207916, by rfl⟩ : syracuseStep 1610555 = 2415833) B2415833
theorem B1610631 : Blo 1609003 1610631 := bstep (se 1 (by rfl) ⟨1207973, by rfl⟩ : syracuseStep 1610631 = 2415947) B2415947
theorem B1610639 : Blo 1609003 1610639 := bstep (se 1 (by rfl) ⟨1207979, by rfl⟩ : syracuseStep 1610639 = 2415959) B2415959
theorem B6116249 : Blo 1609003 6116249 := bstep (se 2 (by rfl) ⟨2293593, by rfl⟩ : syracuseStep 6116249 = 4587187) B4587187
theorem B18338723 : Blo 1609003 18338723 := bstep (se 1 (by rfl) ⟨13754042, by rfl⟩ : syracuseStep 18338723 = 27508085) B27508085
theorem B1610683 : Blo 1609003 1610683 := bstep (se 1 (by rfl) ⟨1208012, by rfl⟩ : syracuseStep 1610683 = 2416025) B2416025
theorem B2413559 : Blo 1609003 2413559 := bstep (se 1 (by rfl) ⟨1810169, by rfl⟩ : syracuseStep 2413559 = 3620339) B3620339
theorem B1610759 : Blo 1609003 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B2413583 : Blo 1609003 2413583 := bstep (se 1 (by rfl) ⟨1810187, by rfl⟩ : syracuseStep 2413583 = 3620375) B3620375
theorem B1610767 : Blo 1609003 1610767 := bstep (se 1 (by rfl) ⟨1208075, by rfl⟩ : syracuseStep 1610767 = 2416151) B2416151
theorem B2413625 : Blo 1609003 2413625 := bstep (se 2 (by rfl) ⟨905109, by rfl⟩ : syracuseStep 2413625 = 1810219) B1810219
theorem B1610811 : Blo 1609003 1610811 := bstep (se 1 (by rfl) ⟨1208108, by rfl⟩ : syracuseStep 1610811 = 2416217) B2416217
theorem B5436503 : Blo 1609003 5436503 := bstep (se 1 (by rfl) ⟨4077377, by rfl⟩ : syracuseStep 5436503 = 8154755) B8154755
theorem B2413703 : Blo 1609003 2413703 := bstep (se 1 (by rfl) ⟨1810277, by rfl⟩ : syracuseStep 2413703 = 3620555) B3620555
theorem B2716807 : Blo 1609003 2716807 := bstep (se 1 (by rfl) ⟨2037605, by rfl⟩ : syracuseStep 2716807 = 4075211) B4075211
theorem B1610887 : Blo 1609003 1610887 := bstep (se 1 (by rfl) ⟨1208165, by rfl⟩ : syracuseStep 1610887 = 2416331) B2416331
theorem B1610895 : Blo 1609003 1610895 := bstep (se 1 (by rfl) ⟨1208171, by rfl⟩ : syracuseStep 1610895 = 2416343) B2416343
theorem B2413739 : Blo 1609003 2413739 := bstep (se 1 (by rfl) ⟨1810304, by rfl⟩ : syracuseStep 2413739 = 3620609) B3620609
theorem B1610939 : Blo 1609003 1610939 := bstep (se 1 (by rfl) ⟨1208204, by rfl⟩ : syracuseStep 1610939 = 2416409) B2416409
theorem B2413769 : Blo 1609003 2413769 := bstep (se 2 (by rfl) ⟨905163, by rfl⟩ : syracuseStep 2413769 = 1810327) B1810327
theorem B2036983 : Blo 1609003 2036983 := bstep (se 1 (by rfl) ⟨1527737, by rfl⟩ : syracuseStep 2036983 = 3055475) B3055475
theorem B4076801 : Blo 1609003 4076801 := bstep (se 2 (by rfl) ⟨1528800, by rfl⟩ : syracuseStep 4076801 = 3057601) B3057601
theorem B2290951 : Blo 1609003 2290951 := bstep (se 1 (by rfl) ⟨1718213, by rfl⟩ : syracuseStep 2290951 = 3436427) B3436427
theorem B8148275 : Blo 1609003 8148275 := bstep (se 1 (by rfl) ⟨6111206, by rfl⟩ : syracuseStep 8148275 = 12222413) B12222413
theorem B2413883 : Blo 1609003 2413883 := bstep (se 1 (by rfl) ⟨1810412, by rfl⟩ : syracuseStep 2413883 = 3620825) B3620825
theorem B5805371 : Blo 1609003 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B2413943 : Blo 1609003 2413943 := bstep (se 1 (by rfl) ⟨1810457, by rfl⟩ : syracuseStep 2413943 = 3620915) B3620915
theorem B5158279 : Blo 1609003 5158279 := bstep (se 1 (by rfl) ⟨3868709, by rfl⟩ : syracuseStep 5158279 = 7737419) B7737419
theorem B2413967 : Blo 1609003 2413967 := bstep (se 1 (by rfl) ⟨1810475, by rfl⟩ : syracuseStep 2413967 = 3620951) B3620951
theorem B2414009 : Blo 1609003 2414009 := bstep (se 2 (by rfl) ⟨905253, by rfl⟩ : syracuseStep 2414009 = 1810507) B1810507
theorem B9418187 : Blo 1609003 9418187 := bstep (se 1 (by rfl) ⟨7063640, by rfl⟩ : syracuseStep 9418187 = 14127281) B14127281
theorem B15685123 : Blo 1609003 15685123 := bstep (se 1 (by rfl) ⟨11763842, by rfl⟩ : syracuseStep 15685123 = 23527685) B23527685
theorem B2414087 : Blo 1609003 2414087 := bstep (se 1 (by rfl) ⟨1810565, by rfl⟩ : syracuseStep 2414087 = 3621131) B3621131
theorem B2414123 : Blo 1609003 2414123 := bstep (se 1 (by rfl) ⟨1810592, by rfl⟩ : syracuseStep 2414123 = 3621185) B3621185
theorem B2037307 : Blo 1609003 2037307 := bstep (se 1 (by rfl) ⟨1527980, by rfl⟩ : syracuseStep 2037307 = 3055961) B3055961
theorem B5436989 : Blo 1609003 5436989 := bstep (se 3 (by rfl) ⟨1019435, by rfl⟩ : syracuseStep 5436989 = 2038871) B2038871
theorem B2414153 : Blo 1609003 2414153 := bstep (se 2 (by rfl) ⟨905307, by rfl⟩ : syracuseStep 2414153 = 1810615) B1810615
theorem B8148599 : Blo 1609003 8148599 := bstep (se 1 (by rfl) ⟨6111449, by rfl⟩ : syracuseStep 8148599 = 12222899) B12222899
theorem B4077175 : Blo 1609003 4077175 := bstep (se 1 (by rfl) ⟨3057881, by rfl⟩ : syracuseStep 4077175 = 6115763) B6115763
theorem B2414267 : Blo 1609003 2414267 := bstep (se 1 (by rfl) ⟨1810700, by rfl⟩ : syracuseStep 2414267 = 3621401) B3621401
theorem B2414327 : Blo 1609003 2414327 := bstep (se 1 (by rfl) ⟨1810745, by rfl⟩ : syracuseStep 2414327 = 3621491) B3621491
theorem B2447111 : Blo 1609003 2447111 := bstep (se 1 (by rfl) ⟨1835333, by rfl⟩ : syracuseStep 2447111 = 3670667) B3670667
theorem B2414351 : Blo 1609003 2414351 := bstep (se 1 (by rfl) ⟨1810763, by rfl⟩ : syracuseStep 2414351 = 3621527) B3621527
theorem B2717455 : Blo 1609003 2717455 := bstep (se 1 (by rfl) ⟨2038091, by rfl⟩ : syracuseStep 2717455 = 4076183) B4076183
theorem B8705807 : Blo 1609003 8705807 := bstep (se 1 (by rfl) ⟨6529355, by rfl⟩ : syracuseStep 8705807 = 13058711) B13058711
theorem B2414393 : Blo 1609003 2414393 := bstep (se 2 (by rfl) ⟨905397, by rfl⟩ : syracuseStep 2414393 = 1810795) B1810795
theorem B2414471 : Blo 1609003 2414471 := bstep (se 1 (by rfl) ⟨1810853, by rfl⟩ : syracuseStep 2414471 = 3621707) B3621707
theorem B9172871 : Blo 1609003 9172871 := bstep (se 1 (by rfl) ⟨6879653, by rfl⟩ : syracuseStep 9172871 = 13759307) B13759307
theorem B2414507 : Blo 1609003 2414507 := bstep (se 1 (by rfl) ⟨1810880, by rfl⟩ : syracuseStep 2414507 = 3621761) B3621761
theorem B9787321 : Blo 1609003 9787321 := bstep (se 2 (by rfl) ⟨3670245, by rfl⟩ : syracuseStep 9787321 = 7340491) B7340491
theorem B2291657 : Blo 1609003 2291657 := bstep (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) B1718743
theorem B2414537 : Blo 1609003 2414537 := bstep (se 2 (by rfl) ⟨905451, by rfl⟩ : syracuseStep 2414537 = 1810903) B1810903
theorem B15464459 : Blo 1609003 15464459 := bstep (se 1 (by rfl) ⟨11598344, by rfl⟩ : syracuseStep 15464459 = 23196689) B23196689
theorem B4585501 : Blo 1609003 4585501 := bstep (se 3 (by rfl) ⟨859781, by rfl⟩ : syracuseStep 4585501 = 1719563) B1719563
theorem B4077611 : Blo 1609003 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B2291771 : Blo 1609003 2291771 := bstep (se 1 (by rfl) ⟨1718828, by rfl⟩ : syracuseStep 2291771 = 3437657) B3437657
theorem B2414651 : Blo 1609003 2414651 := bstep (se 1 (by rfl) ⟨1810988, by rfl⟩ : syracuseStep 2414651 = 3621977) B3621977
theorem B7739459 : Blo 1609003 7739459 := bstep (se 1 (by rfl) ⟨5804594, by rfl⟩ : syracuseStep 7739459 = 11609189) B11609189
theorem B2414711 : Blo 1609003 2414711 := bstep (se 1 (by rfl) ⟨1811033, by rfl⟩ : syracuseStep 2414711 = 3622067) B3622067
theorem B2414735 : Blo 1609003 2414735 := bstep (se 1 (by rfl) ⟨1811051, by rfl⟩ : syracuseStep 2414735 = 3622103) B3622103
theorem B2414777 : Blo 1609003 2414777 := bstep (se 2 (by rfl) ⟨905541, by rfl⟩ : syracuseStep 2414777 = 1811083) B1811083
theorem B4585673 : Blo 1609003 4585673 := bstep (se 2 (by rfl) ⟨1719627, by rfl⟩ : syracuseStep 4585673 = 3439255) B3439255
theorem B4585729 : Blo 1609003 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B2414855 : Blo 1609003 2414855 := bstep (se 1 (by rfl) ⟨1811141, by rfl⟩ : syracuseStep 2414855 = 3622283) B3622283
theorem B2414891 : Blo 1609003 2414891 := bstep (se 1 (by rfl) ⟨1811168, by rfl⟩ : syracuseStep 2414891 = 3622337) B3622337
theorem B2717995 : Blo 1609003 2717995 := bstep (se 1 (by rfl) ⟨2038496, by rfl⟩ : syracuseStep 2717995 = 4076993) B4076993
theorem B1743163 : Blo 1609003 1743163 := bstep (se 1 (by rfl) ⟨1307372, by rfl⟩ : syracuseStep 1743163 = 2614745) B2614745
theorem B2414921 : Blo 1609003 2414921 := bstep (se 2 (by rfl) ⟨905595, by rfl⟩ : syracuseStep 2414921 = 1811191) B1811191
theorem B6199667 : Blo 1609003 6199667 := bstep (se 1 (by rfl) ⟨4649750, by rfl⟩ : syracuseStep 6199667 = 9299501) B9299501
theorem B2578807 : Blo 1609003 2578807 := bstep (se 1 (by rfl) ⟨1934105, by rfl⟩ : syracuseStep 2578807 = 3868211) B3868211
theorem B2718137 : Blo 1609003 2718137 := bstep (se 2 (by rfl) ⟨1019301, by rfl⟩ : syracuseStep 2718137 = 2038603) B2038603
theorem B2415035 : Blo 1609003 2415035 := bstep (se 1 (by rfl) ⟨1811276, by rfl⟩ : syracuseStep 2415035 = 3622553) B3622553
theorem B10459601 : Blo 1609003 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B2415095 : Blo 1609003 2415095 := bstep (se 1 (by rfl) ⟨1811321, by rfl⟩ : syracuseStep 2415095 = 3622643) B3622643
theorem B2038279 : Blo 1609003 2038279 := bstep (se 1 (by rfl) ⟨1528709, by rfl⟩ : syracuseStep 2038279 = 3057419) B3057419
theorem B6879755 : Blo 1609003 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B2415119 : Blo 1609003 2415119 := bstep (se 1 (by rfl) ⟨1811339, by rfl⟩ : syracuseStep 2415119 = 3622679) B3622679
theorem B2415161 : Blo 1609003 2415161 := bstep (se 2 (by rfl) ⟨905685, by rfl⟩ : syracuseStep 2415161 = 1811371) B1811371
theorem B8149571 : Blo 1609003 8149571 := bstep (se 1 (by rfl) ⟨6112178, by rfl⟩ : syracuseStep 8149571 = 12224357) B12224357
theorem B4586071 : Blo 1609003 4586071 := bstep (se 1 (by rfl) ⟨3439553, by rfl⟩ : syracuseStep 4586071 = 6879107) B6879107
theorem B2415239 : Blo 1609003 2415239 := bstep (se 1 (by rfl) ⟨1811429, by rfl⟩ : syracuseStep 2415239 = 3622859) B3622859
theorem B2415275 : Blo 1609003 2415275 := bstep (se 1 (by rfl) ⟨1811456, by rfl⟩ : syracuseStep 2415275 = 3622913) B3622913
theorem B2292409 : Blo 1609003 2292409 := bstep (se 2 (by rfl) ⟨859653, by rfl⟩ : syracuseStep 2292409 = 1719307) B1719307
theorem B2415305 : Blo 1609003 2415305 := bstep (se 2 (by rfl) ⟨905739, by rfl⟩ : syracuseStep 2415305 = 1811479) B1811479
theorem B26114831 : Blo 1609003 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B2415419 : Blo 1609003 2415419 := bstep (se 1 (by rfl) ⟨1811564, by rfl⟩ : syracuseStep 2415419 = 3623129) B3623129
theorem B2415479 : Blo 1609003 2415479 := bstep (se 1 (by rfl) ⟨1811609, by rfl⟩ : syracuseStep 2415479 = 3623219) B3623219
theorem B8149895 : Blo 1609003 8149895 := bstep (se 1 (by rfl) ⟨6112421, by rfl⟩ : syracuseStep 8149895 = 12224843) B12224843
theorem B2415503 : Blo 1609003 2415503 := bstep (se 1 (by rfl) ⟨1811627, by rfl⟩ : syracuseStep 2415503 = 3623255) B3623255
theorem B6110099 : Blo 1609003 6110099 := bstep (se 1 (by rfl) ⟨4582574, by rfl⟩ : syracuseStep 6110099 = 9165149) B9165149
theorem B2038699 : Blo 1609003 2038699 := bstep (se 1 (by rfl) ⟨1529024, by rfl⟩ : syracuseStep 2038699 = 3058049) B3058049
theorem B2415545 : Blo 1609003 2415545 := bstep (se 2 (by rfl) ⟨905829, by rfl⟩ : syracuseStep 2415545 = 1811659) B1811659
theorem B2415623 : Blo 1609003 2415623 := bstep (se 1 (by rfl) ⟨1811717, by rfl⟩ : syracuseStep 2415623 = 3623435) B3623435
theorem B2415659 : Blo 1609003 2415659 := bstep (se 1 (by rfl) ⟨1811744, by rfl⟩ : syracuseStep 2415659 = 3623489) B3623489
theorem B2415689 : Blo 1609003 2415689 := bstep (se 2 (by rfl) ⟨905883, by rfl⟩ : syracuseStep 2415689 = 1811767) B1811767
theorem B2038927 : Blo 1609003 2038927 := bstep (se 1 (by rfl) ⟨1529195, by rfl⟩ : syracuseStep 2038927 = 3058391) B3058391
theorem B14687405 : Blo 1609003 14687405 := bstep (se 3 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 14687405 = 5507777) B5507777
theorem B2448571 : Blo 1609003 2448571 := bstep (se 1 (by rfl) ⟨1836428, by rfl⟩ : syracuseStep 2448571 = 3672857) B3672857
theorem B2415803 : Blo 1609003 2415803 := bstep (se 1 (by rfl) ⟨1811852, by rfl⟩ : syracuseStep 2415803 = 3623705) B3623705
theorem B2415863 : Blo 1609003 2415863 := bstep (se 1 (by rfl) ⟨1811897, by rfl⟩ : syracuseStep 2415863 = 3623795) B3623795
theorem B9166081 : Blo 1609003 9166081 := bstep (se 2 (by rfl) ⟨3437280, by rfl⟩ : syracuseStep 9166081 = 6874561) B6874561
theorem B1719559 : Blo 1609003 1719559 := bstep (se 1 (by rfl) ⟨1289669, by rfl⟩ : syracuseStep 1719559 = 2579339) B2579339
theorem B2415887 : Blo 1609003 2415887 := bstep (se 1 (by rfl) ⟨1811915, by rfl⟩ : syracuseStep 2415887 = 3623831) B3623831
theorem B2579755 : Blo 1609003 2579755 := bstep (se 1 (by rfl) ⟨1934816, by rfl⟩ : syracuseStep 2579755 = 3869633) B3869633
theorem B2415929 : Blo 1609003 2415929 := bstep (se 2 (by rfl) ⟨905973, by rfl⟩ : syracuseStep 2415929 = 1811947) B1811947
theorem B6110599 : Blo 1609003 6110599 := bstep (se 1 (by rfl) ⟨4582949, by rfl⟩ : syracuseStep 6110599 = 9165899) B9165899
theorem B2416007 : Blo 1609003 2416007 := bstep (se 1 (by rfl) ⟨1812005, by rfl⟩ : syracuseStep 2416007 = 3624011) B3624011
theorem B2416043 : Blo 1609003 2416043 := bstep (se 1 (by rfl) ⟨1812032, by rfl⟩ : syracuseStep 2416043 = 3624065) B3624065
theorem B6880697 : Blo 1609003 6880697 := bstep (se 2 (by rfl) ⟨2580261, by rfl⟩ : syracuseStep 6880697 = 5160523) B5160523
theorem B2416073 : Blo 1609003 2416073 := bstep (se 2 (by rfl) ⟨906027, by rfl⟩ : syracuseStep 2416073 = 1812055) B1812055
theorem B8707537 : Blo 1609003 8707537 := bstep (se 2 (by rfl) ⟨3265326, by rfl⟩ : syracuseStep 8707537 = 6530653) B6530653
theorem B11599325 : Blo 1609003 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B4898333 : Blo 1609003 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B3620411 : Blo 1609003 3620411 := bstep (se 1 (by rfl) ⟨2715308, by rfl⟩ : syracuseStep 3620411 = 5430617) B5430617
theorem B2416187 : Blo 1609003 2416187 := bstep (se 1 (by rfl) ⟨1812140, by rfl⟩ : syracuseStep 2416187 = 3624281) B3624281
theorem B2416247 : Blo 1609003 2416247 := bstep (se 1 (by rfl) ⟨1812185, by rfl⟩ : syracuseStep 2416247 = 3624371) B3624371
theorem B9174647 : Blo 1609003 9174647 := bstep (se 1 (by rfl) ⟨6880985, by rfl⟩ : syracuseStep 9174647 = 13761971) B13761971
theorem B2416271 : Blo 1609003 2416271 := bstep (se 1 (by rfl) ⟨1812203, by rfl⟩ : syracuseStep 2416271 = 3624407) B3624407
theorem B3620537 : Blo 1609003 3620537 := bstep (se 2 (by rfl) ⟨1357701, by rfl⟩ : syracuseStep 3620537 = 2715403) B2715403
theorem B2416313 : Blo 1609003 2416313 := bstep (se 2 (by rfl) ⟨906117, by rfl⟩ : syracuseStep 2416313 = 1812235) B1812235
theorem B8822465 : Blo 1609003 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1810183 : Blo 1609003 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B2416391 : Blo 1609003 2416391 := bstep (se 1 (by rfl) ⟨1812293, by rfl⟩ : syracuseStep 2416391 = 3624587) B3624587
theorem B9166607 : Blo 1609003 9166607 := bstep (se 1 (by rfl) ⟨6874955, by rfl⟩ : syracuseStep 9166607 = 13749911) B13749911
theorem B9789217 : Blo 1609003 9789217 := bstep (se 2 (by rfl) ⟨3670956, by rfl⟩ : syracuseStep 9789217 = 7341913) B7341913
theorem B2416427 : Blo 1609003 2416427 := bstep (se 1 (by rfl) ⟨1812320, by rfl⟩ : syracuseStep 2416427 = 3624641) B3624641
theorem B7339835 : Blo 1609003 7339835 := bstep (se 1 (by rfl) ⟨5504876, by rfl⟩ : syracuseStep 7339835 = 11009753) B11009753
theorem B2416457 : Blo 1609003 2416457 := bstep (se 2 (by rfl) ⟨906171, by rfl⟩ : syracuseStep 2416457 = 1812343) B1812343
theorem B1810363 : Blo 1609003 1810363 := bstep (se 1 (by rfl) ⟨1357772, by rfl⟩ : syracuseStep 1810363 = 2715545) B2715545
theorem B3440647 : Blo 1609003 3440647 := bstep (se 1 (by rfl) ⟨2580485, by rfl⟩ : syracuseStep 3440647 = 5160971) B5160971
theorem B1810471 : Blo 1609003 1810471 := bstep (se 1 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 1810471 = 2715707) B2715707
theorem B22020173 : Blo 1609003 22020173 := bstep (se 3 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 22020173 = 8257565) B8257565
theorem B6111389 : Blo 1609003 6111389 := bstep (se 3 (by rfl) ⟨1145885, by rfl⟩ : syracuseStep 6111389 = 2291771) B2291771
theorem B3826063 : Blo 1609003 3826063 := bstep (se 1 (by rfl) ⟨2869547, by rfl⟩ : syracuseStep 3826063 = 5739095) B5739095
theorem B3056059 : Blo 1609003 3056059 := bstep (se 1 (by rfl) ⟨2292044, by rfl⟩ : syracuseStep 3056059 = 4584089) B4584089
theorem B20922889 : Blo 1609003 20922889 := bstep (se 2 (by rfl) ⟨7846083, by rfl⟩ : syracuseStep 20922889 = 15692167) B15692167
theorem B3621473 : Blo 1609003 3621473 := bstep (se 2 (by rfl) ⟨1358052, by rfl⟩ : syracuseStep 3621473 = 2716105) B2716105
theorem B23208565 : Blo 1609003 23208565 := bstep (se 5 (by rfl) ⟨1087901, by rfl⟩ : syracuseStep 23208565 = 2175803) B2175803
theorem B5882507 : Blo 1609003 5882507 := bstep (se 1 (by rfl) ⟨4411880, by rfl⟩ : syracuseStep 5882507 = 8823761) B8823761
theorem B6112043 : Blo 1609003 6112043 := bstep (se 1 (by rfl) ⟨4584032, by rfl⟩ : syracuseStep 6112043 = 9168065) B9168065
theorem B5432183 : Blo 1609003 5432183 := bstep (se 1 (by rfl) ⟨4074137, by rfl⟩ : syracuseStep 5432183 = 8148275) B8148275
theorem B3056545 : Blo 1609003 3056545 := bstep (se 2 (by rfl) ⟨1146204, by rfl⟩ : syracuseStep 3056545 = 2292409) B2292409
theorem B3621815 : Blo 1609003 3621815 := bstep (se 1 (by rfl) ⟨2716361, by rfl⟩ : syracuseStep 3621815 = 5432723) B5432723
theorem B9290771 : Blo 1609003 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B17400851 : Blo 1609003 17400851 := bstep (se 1 (by rfl) ⟨13050638, by rfl⟩ : syracuseStep 17400851 = 26101277) B26101277
theorem B5432399 : Blo 1609003 5432399 := bstep (se 1 (by rfl) ⟨4074299, by rfl⟩ : syracuseStep 5432399 = 8148599) B8148599
theorem B18834889 : Blo 1609003 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B5432777 : Blo 1609003 5432777 := bstep (se 2 (by rfl) ⟨2037291, by rfl⟩ : syracuseStep 5432777 = 4074583) B4074583
theorem B3057115 : Blo 1609003 3057115 := bstep (se 1 (by rfl) ⟨2292836, by rfl⟩ : syracuseStep 3057115 = 4585673) B4585673
theorem B52209157 : Blo 1609003 52209157 := bstep (se 4 (by rfl) ⟨4894608, by rfl⟩ : syracuseStep 52209157 = 9789217) B9789217
theorem B3622409 : Blo 1609003 3622409 := bstep (se 2 (by rfl) ⟨1358403, by rfl⟩ : syracuseStep 3622409 = 2716807) B2716807
theorem B3261971 : Blo 1609003 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B1812091 : Blo 1609003 1812091 := bstep (se 1 (by rfl) ⟨1359068, by rfl⟩ : syracuseStep 1812091 = 2718137) B2718137
theorem B6973067 : Blo 1609003 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B9791165 : Blo 1609003 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1935047 : Blo 1609003 1935047 := bstep (se 1 (by rfl) ⟨1451285, by rfl⟩ : syracuseStep 1935047 = 2902571) B2902571
theorem B5801681 : Blo 1609003 5801681 := bstep (se 2 (by rfl) ⟨2175630, by rfl⟩ : syracuseStep 5801681 = 4351261) B4351261
theorem B5433047 : Blo 1609003 5433047 := bstep (se 1 (by rfl) ⟨4074785, by rfl⟩ : syracuseStep 5433047 = 8149571) B8149571
theorem B3622751 : Blo 1609003 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B17409887 : Blo 1609003 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B9299873 : Blo 1609003 9299873 := bstep (se 2 (by rfl) ⟨3487452, by rfl⟩ : syracuseStep 9299873 = 6974905) B6974905
theorem B5433263 : Blo 1609003 5433263 := bstep (se 1 (by rfl) ⟨4074947, by rfl⟩ : syracuseStep 5433263 = 8149895) B8149895
theorem B4073399 : Blo 1609003 4073399 := bstep (se 1 (by rfl) ⟨3055049, by rfl⟩ : syracuseStep 4073399 = 6110099) B6110099
theorem B11610049 : Blo 1609003 11610049 := bstep (se 2 (by rfl) ⟨4353768, by rfl⟩ : syracuseStep 11610049 = 8707537) B8707537
theorem B3622931 : Blo 1609003 3622931 := bstep (se 1 (by rfl) ⟨2717198, by rfl⟩ : syracuseStep 3622931 = 5434397) B5434397
theorem B9791603 : Blo 1609003 9791603 := bstep (se 1 (by rfl) ⟨7343702, by rfl⟩ : syracuseStep 9791603 = 14687405) B14687405
theorem B12904753 : Blo 1609003 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B3623273 : Blo 1609003 3623273 := bstep (se 2 (by rfl) ⟨1358727, by rfl⟩ : syracuseStep 3623273 = 2717455) B2717455
theorem B9791873 : Blo 1609003 9791873 := bstep (se 2 (by rfl) ⟨3671952, by rfl⟩ : syracuseStep 9791873 = 7343905) B7343905
theorem B4893223 : Blo 1609003 4893223 := bstep (se 1 (by rfl) ⟨3669917, by rfl⟩ : syracuseStep 4893223 = 7339835) B7339835
theorem B6114001 : Blo 1609003 6114001 := bstep (se 2 (by rfl) ⟨2292750, by rfl⟩ : syracuseStep 6114001 = 4585501) B4585501
theorem B4074401 : Blo 1609003 4074401 := bstep (se 2 (by rfl) ⟨1527900, by rfl⟩ : syracuseStep 4074401 = 3055801) B3055801
theorem B3869623 : Blo 1609003 3869623 := bstep (se 1 (by rfl) ⟨2902217, by rfl⟩ : syracuseStep 3869623 = 5804435) B5804435
theorem B3673019 : Blo 1609003 3673019 := bstep (se 1 (by rfl) ⟨2754764, by rfl⟩ : syracuseStep 3673019 = 5509529) B5509529
theorem B3623867 : Blo 1609003 3623867 := bstep (se 1 (by rfl) ⟨2717900, by rfl⟩ : syracuseStep 3623867 = 5435801) B5435801
theorem B6114305 : Blo 1609003 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B3623993 : Blo 1609003 3623993 := bstep (se 2 (by rfl) ⟨1358997, by rfl⟩ : syracuseStep 3623993 = 2717995) B2717995
theorem B6876407 : Blo 1609003 6876407 := bstep (se 1 (by rfl) ⟨5157305, by rfl⟩ : syracuseStep 6876407 = 10314611) B10314611
theorem B10317071 : Blo 1609003 10317071 := bstep (se 1 (by rfl) ⟨7737803, by rfl⟩ : syracuseStep 10317071 = 15475607) B15475607
theorem B12225815 : Blo 1609003 12225815 := bstep (se 1 (by rfl) ⟨9169361, by rfl⟩ : syracuseStep 12225815 = 18338723) B18338723
theorem B1609039 : Blo 1609003 1609039 := bstep (se 1 (by rfl) ⟨1206779, by rfl⟩ : syracuseStep 1609039 = 2413559) B2413559
theorem B1609055 : Blo 1609003 1609055 := bstep (se 1 (by rfl) ⟨1206791, by rfl⟩ : syracuseStep 1609055 = 2413583) B2413583
theorem B4074857 : Blo 1609003 4074857 := bstep (se 2 (by rfl) ⟨1528071, by rfl⟩ : syracuseStep 4074857 = 3056143) B3056143
theorem B1609083 : Blo 1609003 1609083 := bstep (se 1 (by rfl) ⟨1206812, by rfl⟩ : syracuseStep 1609083 = 2413625) B2413625
theorem B3624335 : Blo 1609003 3624335 := bstep (se 1 (by rfl) ⟨2718251, by rfl⟩ : syracuseStep 3624335 = 5436503) B5436503
theorem B1609135 : Blo 1609003 1609135 := bstep (se 1 (by rfl) ⟨1206851, by rfl⟩ : syracuseStep 1609135 = 2413703) B2413703
theorem B1609159 : Blo 1609003 1609159 := bstep (se 1 (by rfl) ⟨1206869, by rfl⟩ : syracuseStep 1609159 = 2413739) B2413739
theorem B6114761 : Blo 1609003 6114761 := bstep (se 2 (by rfl) ⟨2293035, by rfl⟩ : syracuseStep 6114761 = 4586071) B4586071
theorem B1609179 : Blo 1609003 1609179 := bstep (se 1 (by rfl) ⟨1206884, by rfl⟩ : syracuseStep 1609179 = 2413769) B2413769
theorem B24800755 : Blo 1609003 24800755 := bstep (se 1 (by rfl) ⟨18600566, by rfl⟩ : syracuseStep 24800755 = 37201133) B37201133
theorem B6524425 : Blo 1609003 6524425 := bstep (se 2 (by rfl) ⟨2446659, by rfl⟩ : syracuseStep 6524425 = 4893319) B4893319
theorem B1609255 : Blo 1609003 1609255 := bstep (se 1 (by rfl) ⟨1206941, by rfl⟩ : syracuseStep 1609255 = 2413883) B2413883
theorem B1609295 : Blo 1609003 1609295 := bstep (se 1 (by rfl) ⟨1206971, by rfl⟩ : syracuseStep 1609295 = 2413943) B2413943
theorem B1609311 : Blo 1609003 1609311 := bstep (se 1 (by rfl) ⟨1206983, by rfl⟩ : syracuseStep 1609311 = 2413967) B2413967
theorem B1609339 : Blo 1609003 1609339 := bstep (se 1 (by rfl) ⟨1207004, by rfl⟩ : syracuseStep 1609339 = 2414009) B2414009
theorem B4189819 : Blo 1609003 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B6278791 : Blo 1609003 6278791 := bstep (se 1 (by rfl) ⟨4709093, by rfl⟩ : syracuseStep 6278791 = 9418187) B9418187
theorem B1609391 : Blo 1609003 1609391 := bstep (se 1 (by rfl) ⟨1207043, by rfl⟩ : syracuseStep 1609391 = 2414087) B2414087
theorem B1609415 : Blo 1609003 1609415 := bstep (se 1 (by rfl) ⟨1207061, by rfl⟩ : syracuseStep 1609415 = 2414123) B2414123
theorem B3624659 : Blo 1609003 3624659 := bstep (se 1 (by rfl) ⟨2718494, by rfl⟩ : syracuseStep 3624659 = 5436989) B5436989
theorem B1609435 : Blo 1609003 1609435 := bstep (se 1 (by rfl) ⟨1207076, by rfl⟩ : syracuseStep 1609435 = 2414153) B2414153
theorem B2715383 : Blo 1609003 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B1609511 : Blo 1609003 1609511 := bstep (se 1 (by rfl) ⟨1207133, by rfl⟩ : syracuseStep 1609511 = 2414267) B2414267
theorem B1609551 : Blo 1609003 1609551 := bstep (se 1 (by rfl) ⟨1207163, by rfl⟩ : syracuseStep 1609551 = 2414327) B2414327
theorem B1609567 : Blo 1609003 1609567 := bstep (se 1 (by rfl) ⟨1207175, by rfl⟩ : syracuseStep 1609567 = 2414351) B2414351
theorem B5803871 : Blo 1609003 5803871 := bstep (se 1 (by rfl) ⟨4352903, by rfl⟩ : syracuseStep 5803871 = 8705807) B8705807
theorem B1609595 : Blo 1609003 1609595 := bstep (se 1 (by rfl) ⟨1207196, by rfl⟩ : syracuseStep 1609595 = 2414393) B2414393
theorem B1609647 : Blo 1609003 1609647 := bstep (se 1 (by rfl) ⟨1207235, by rfl⟩ : syracuseStep 1609647 = 2414471) B2414471
theorem B6115247 : Blo 1609003 6115247 := bstep (se 1 (by rfl) ⟨4586435, by rfl⟩ : syracuseStep 6115247 = 9172871) B9172871
theorem B1609671 : Blo 1609003 1609671 := bstep (se 1 (by rfl) ⟨1207253, by rfl⟩ : syracuseStep 1609671 = 2414507) B2414507
theorem B1609691 : Blo 1609003 1609691 := bstep (se 1 (by rfl) ⟨1207268, by rfl⟩ : syracuseStep 1609691 = 2414537) B2414537
theorem B10309639 : Blo 1609003 10309639 := bstep (se 1 (by rfl) ⟨7732229, by rfl⟩ : syracuseStep 10309639 = 15464459) B15464459
theorem B18346013 : Blo 1609003 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B1609767 : Blo 1609003 1609767 := bstep (se 1 (by rfl) ⟨1207325, by rfl⟩ : syracuseStep 1609767 = 2414651) B2414651
theorem B9170981 : Blo 1609003 9170981 := bstep (se 4 (by rfl) ⟨859779, by rfl⟩ : syracuseStep 9170981 = 1719559) B1719559
theorem B13062221 : Blo 1609003 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B2715727 : Blo 1609003 2715727 := bstep (se 1 (by rfl) ⟨2036795, by rfl⟩ : syracuseStep 2715727 = 4073591) B4073591
theorem B1609807 : Blo 1609003 1609807 := bstep (se 1 (by rfl) ⟨1207355, by rfl⟩ : syracuseStep 1609807 = 2414711) B2414711
theorem B1609823 : Blo 1609003 1609823 := bstep (se 1 (by rfl) ⟨1207367, by rfl⟩ : syracuseStep 1609823 = 2414735) B2414735
theorem B1609851 : Blo 1609003 1609851 := bstep (se 1 (by rfl) ⟨1207388, by rfl⟩ : syracuseStep 1609851 = 2414777) B2414777
theorem B12218525 : Blo 1609003 12218525 := bstep (se 3 (by rfl) ⟨2290973, by rfl⟩ : syracuseStep 12218525 = 4581947) B4581947
theorem B1609903 : Blo 1609003 1609903 := bstep (se 1 (by rfl) ⟨1207427, by rfl⟩ : syracuseStep 1609903 = 2414855) B2414855
theorem B1609927 : Blo 1609003 1609927 := bstep (se 1 (by rfl) ⟨1207445, by rfl⟩ : syracuseStep 1609927 = 2414891) B2414891
theorem B1609947 : Blo 1609003 1609947 := bstep (se 1 (by rfl) ⟨1207460, by rfl⟩ : syracuseStep 1609947 = 2414921) B2414921
theorem B5435639 : Blo 1609003 5435639 := bstep (se 1 (by rfl) ⟨4076729, by rfl⟩ : syracuseStep 5435639 = 8153459) B8153459
theorem B3264761 : Blo 1609003 3264761 := bstep (se 2 (by rfl) ⟨1224285, by rfl⟩ : syracuseStep 3264761 = 2448571) B2448571
theorem B4133111 : Blo 1609003 4133111 := bstep (se 1 (by rfl) ⟨3099833, by rfl⟩ : syracuseStep 4133111 = 6199667) B6199667
theorem B8155403 : Blo 1609003 8155403 := bstep (se 1 (by rfl) ⟨6116552, by rfl⟩ : syracuseStep 8155403 = 12233105) B12233105
theorem B1610023 : Blo 1609003 1610023 := bstep (se 1 (by rfl) ⟨1207517, by rfl⟩ : syracuseStep 1610023 = 2415035) B2415035
theorem B2715977 : Blo 1609003 2715977 := bstep (se 2 (by rfl) ⟨1018491, by rfl⟩ : syracuseStep 2715977 = 2036983) B2036983
theorem B1610063 : Blo 1609003 1610063 := bstep (se 1 (by rfl) ⟨1207547, by rfl⟩ : syracuseStep 1610063 = 2415095) B2415095
theorem B1610079 : Blo 1609003 1610079 := bstep (se 1 (by rfl) ⟨1207559, by rfl⟩ : syracuseStep 1610079 = 2415119) B2415119
theorem B1610107 : Blo 1609003 1610107 := bstep (se 1 (by rfl) ⟨1207580, by rfl⟩ : syracuseStep 1610107 = 2415161) B2415161
theorem B1610159 : Blo 1609003 1610159 := bstep (se 1 (by rfl) ⟨1207619, by rfl⟩ : syracuseStep 1610159 = 2415239) B2415239
theorem B1610183 : Blo 1609003 1610183 := bstep (se 1 (by rfl) ⟨1207637, by rfl⟩ : syracuseStep 1610183 = 2415275) B2415275
theorem B1610203 : Blo 1609003 1610203 := bstep (se 1 (by rfl) ⟨1207652, by rfl⟩ : syracuseStep 1610203 = 2415305) B2415305
theorem B8147465 : Blo 1609003 8147465 := bstep (se 2 (by rfl) ⟨3055299, by rfl⟩ : syracuseStep 8147465 = 6110599) B6110599
theorem B6877705 : Blo 1609003 6877705 := bstep (se 2 (by rfl) ⟨2579139, by rfl⟩ : syracuseStep 6877705 = 5158279) B5158279
theorem B4076041 : Blo 1609003 4076041 := bstep (se 2 (by rfl) ⟨1528515, by rfl⟩ : syracuseStep 4076041 = 3057031) B3057031
theorem B1610279 : Blo 1609003 1610279 := bstep (se 1 (by rfl) ⟨1207709, by rfl⟩ : syracuseStep 1610279 = 2415419) B2415419
theorem B5435963 : Blo 1609003 5435963 := bstep (se 1 (by rfl) ⟨4076972, by rfl⟩ : syracuseStep 5435963 = 8153945) B8153945
theorem B1610319 : Blo 1609003 1610319 := bstep (se 1 (by rfl) ⟨1207739, by rfl⟩ : syracuseStep 1610319 = 2415479) B2415479
theorem B1610335 : Blo 1609003 1610335 := bstep (se 1 (by rfl) ⟨1207751, by rfl⟩ : syracuseStep 1610335 = 2415503) B2415503
theorem B1610363 : Blo 1609003 1610363 := bstep (se 1 (by rfl) ⟨1207772, by rfl⟩ : syracuseStep 1610363 = 2415545) B2415545
theorem B1610415 : Blo 1609003 1610415 := bstep (se 1 (by rfl) ⟨1207811, by rfl⟩ : syracuseStep 1610415 = 2415623) B2415623
theorem B6525629 : Blo 1609003 6525629 := bstep (se 3 (by rfl) ⟨1223555, by rfl⟩ : syracuseStep 6525629 = 2447111) B2447111
theorem B1610439 : Blo 1609003 1610439 := bstep (se 1 (by rfl) ⟨1207829, by rfl⟩ : syracuseStep 1610439 = 2415659) B2415659
theorem B12227273 : Blo 1609003 12227273 := bstep (se 2 (by rfl) ⟨4585227, by rfl⟩ : syracuseStep 12227273 = 9170455) B9170455
theorem B1610459 : Blo 1609003 1610459 := bstep (se 1 (by rfl) ⟨1207844, by rfl⟩ : syracuseStep 1610459 = 2415689) B2415689
theorem B2716409 : Blo 1609003 2716409 := bstep (se 2 (by rfl) ⟨1018653, by rfl⟩ : syracuseStep 2716409 = 2037307) B2037307
theorem B1610535 : Blo 1609003 1610535 := bstep (se 1 (by rfl) ⟨1207901, by rfl⟩ : syracuseStep 1610535 = 2415803) B2415803
theorem B5436233 : Blo 1609003 5436233 := bstep (se 2 (by rfl) ⟨2038587, by rfl⟩ : syracuseStep 5436233 = 4077175) B4077175
theorem B1610575 : Blo 1609003 1610575 := bstep (se 1 (by rfl) ⟨1207931, by rfl⟩ : syracuseStep 1610575 = 2415863) B2415863
theorem B1610591 : Blo 1609003 1610591 := bstep (se 1 (by rfl) ⟨1207943, by rfl⟩ : syracuseStep 1610591 = 2415887) B2415887
theorem B1610619 : Blo 1609003 1610619 := bstep (se 1 (by rfl) ⟨1207964, by rfl⟩ : syracuseStep 1610619 = 2415929) B2415929
theorem B2716591 : Blo 1609003 2716591 := bstep (se 1 (by rfl) ⟨2037443, by rfl⟩ : syracuseStep 2716591 = 4074887) B4074887
theorem B1610671 : Blo 1609003 1610671 := bstep (se 1 (by rfl) ⟨1208003, by rfl⟩ : syracuseStep 1610671 = 2416007) B2416007
theorem B1610695 : Blo 1609003 1610695 := bstep (se 1 (by rfl) ⟨1208021, by rfl⟩ : syracuseStep 1610695 = 2416043) B2416043
theorem B1610715 : Blo 1609003 1610715 := bstep (se 1 (by rfl) ⟨1208036, by rfl⟩ : syracuseStep 1610715 = 2416073) B2416073
theorem B2716679 : Blo 1609003 2716679 := bstep (se 1 (by rfl) ⟨2037509, by rfl⟩ : syracuseStep 2716679 = 4075019) B4075019
theorem B2413577 : Blo 1609003 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B2413607 : Blo 1609003 2413607 := bstep (se 1 (by rfl) ⟨1810205, by rfl⟩ : syracuseStep 2413607 = 3620411) B3620411
theorem B1610791 : Blo 1609003 1610791 := bstep (se 1 (by rfl) ⟨1208093, by rfl⟩ : syracuseStep 1610791 = 2416187) B2416187
theorem B1610831 : Blo 1609003 1610831 := bstep (se 1 (by rfl) ⟨1208123, by rfl⟩ : syracuseStep 1610831 = 2416247) B2416247
theorem B6116431 : Blo 1609003 6116431 := bstep (se 1 (by rfl) ⟨4587323, by rfl⟩ : syracuseStep 6116431 = 9174647) B9174647
theorem B1610847 : Blo 1609003 1610847 := bstep (se 1 (by rfl) ⟨1208135, by rfl⟩ : syracuseStep 1610847 = 2416271) B2416271
theorem B20624503 : Blo 1609003 20624503 := bstep (se 1 (by rfl) ⟨15468377, by rfl⟩ : syracuseStep 20624503 = 30936755) B30936755
theorem B2413691 : Blo 1609003 2413691 := bstep (se 1 (by rfl) ⟨1810268, by rfl⟩ : syracuseStep 2413691 = 3620537) B3620537
theorem B1610875 : Blo 1609003 1610875 := bstep (se 1 (by rfl) ⟨1208156, by rfl⟩ : syracuseStep 1610875 = 2416313) B2416313
theorem B1610927 : Blo 1609003 1610927 := bstep (se 1 (by rfl) ⟨1208195, by rfl⟩ : syracuseStep 1610927 = 2416391) B2416391
theorem B1610951 : Blo 1609003 1610951 := bstep (se 1 (by rfl) ⟨1208213, by rfl⟩ : syracuseStep 1610951 = 2416427) B2416427
theorem B1610971 : Blo 1609003 1610971 := bstep (se 1 (by rfl) ⟨1208228, by rfl⟩ : syracuseStep 1610971 = 2416457) B2416457
theorem B2413817 : Blo 1609003 2413817 := bstep (se 2 (by rfl) ⟨905181, by rfl⟩ : syracuseStep 2413817 = 1810363) B1810363
theorem B2413919 : Blo 1609003 2413919 := bstep (se 1 (by rfl) ⟨1810439, by rfl⟩ : syracuseStep 2413919 = 3620879) B3620879
theorem B2717023 : Blo 1609003 2717023 := bstep (se 1 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 2717023 = 4075535) B4075535
theorem B2413931 : Blo 1609003 2413931 := bstep (se 1 (by rfl) ⟨1810448, by rfl⟩ : syracuseStep 2413931 = 3620897) B3620897
theorem B2717111 : Blo 1609003 2717111 := bstep (se 1 (by rfl) ⟨2037833, by rfl⟩ : syracuseStep 2717111 = 4075667) B4075667
theorem B41268689 : Blo 1609003 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B5584409 : Blo 1609003 5584409 := bstep (se 2 (by rfl) ⟨2094153, by rfl⟩ : syracuseStep 5584409 = 4188307) B4188307
theorem B3438119 : Blo 1609003 3438119 := bstep (se 1 (by rfl) ⟨2578589, by rfl⟩ : syracuseStep 3438119 = 5157179) B5157179
theorem B2414159 : Blo 1609003 2414159 := bstep (se 1 (by rfl) ⟨1810619, by rfl⟩ : syracuseStep 2414159 = 3621239) B3621239
theorem B26105489 : Blo 1609003 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B9787027 : Blo 1609003 9787027 := bstep (se 1 (by rfl) ⟨7340270, by rfl⟩ : syracuseStep 9787027 = 14680541) B14680541
theorem B2414279 : Blo 1609003 2414279 := bstep (se 1 (by rfl) ⟨1810709, by rfl⟩ : syracuseStep 2414279 = 3621419) B3621419
theorem B6878935 : Blo 1609003 6878935 := bstep (se 1 (by rfl) ⟨5159201, by rfl⟩ : syracuseStep 6878935 = 10318403) B10318403
theorem B3438409 : Blo 1609003 3438409 := bstep (se 2 (by rfl) ⟨1289403, by rfl⟩ : syracuseStep 3438409 = 2578807) B2578807
theorem B2414441 : Blo 1609003 2414441 := bstep (se 2 (by rfl) ⟨905415, by rfl⟩ : syracuseStep 2414441 = 1810831) B1810831
theorem B3438443 : Blo 1609003 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B2414519 : Blo 1609003 2414519 := bstep (se 1 (by rfl) ⟨1810889, by rfl⟩ : syracuseStep 2414519 = 3621779) B3621779
theorem B8148923 : Blo 1609003 8148923 := bstep (se 1 (by rfl) ⟨6111692, by rfl⟩ : syracuseStep 8148923 = 12223385) B12223385
theorem B4077499 : Blo 1609003 4077499 := bstep (se 1 (by rfl) ⟨3058124, by rfl⟩ : syracuseStep 4077499 = 6116249) B6116249
theorem B2414555 : Blo 1609003 2414555 := bstep (se 1 (by rfl) ⟨1810916, by rfl⟩ : syracuseStep 2414555 = 3621833) B3621833
theorem B2717705 : Blo 1609003 2717705 := bstep (se 2 (by rfl) ⟨1019139, by rfl⟩ : syracuseStep 2717705 = 2038279) B2038279
theorem B161060885 : Blo 1609003 161060885 := bstep (se 6 (by rfl) ⟨3774864, by rfl⟩ : syracuseStep 161060885 = 7549729) B7549729
theorem B15480989 : Blo 1609003 15480989 := bstep (se 3 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 15480989 = 5805371) B5805371
theorem B2717867 : Blo 1609003 2717867 := bstep (se 1 (by rfl) ⟨2038400, by rfl⟩ : syracuseStep 2717867 = 4076801) B4076801
theorem B10311947 : Blo 1609003 10311947 := bstep (se 1 (by rfl) ⟨7733960, by rfl⟩ : syracuseStep 10311947 = 15467921) B15467921
theorem B2415023 : Blo 1609003 2415023 := bstep (se 1 (by rfl) ⟨1811267, by rfl⟩ : syracuseStep 2415023 = 3622535) B3622535
theorem B2415113 : Blo 1609003 2415113 := bstep (se 2 (by rfl) ⟨905667, by rfl⟩ : syracuseStep 2415113 = 1811335) B1811335
theorem B2415143 : Blo 1609003 2415143 := bstep (se 1 (by rfl) ⟨1811357, by rfl⟩ : syracuseStep 2415143 = 3622715) B3622715
theorem B2718265 : Blo 1609003 2718265 := bstep (se 2 (by rfl) ⟨1019349, by rfl⟩ : syracuseStep 2718265 = 2038699) B2038699
theorem B2415227 : Blo 1609003 2415227 := bstep (se 1 (by rfl) ⟨1811420, by rfl⟩ : syracuseStep 2415227 = 3622841) B3622841
theorem B2718407 : Blo 1609003 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B5159639 : Blo 1609003 5159639 := bstep (se 1 (by rfl) ⟨3869729, by rfl⟩ : syracuseStep 5159639 = 7739459) B7739459
theorem B2415353 : Blo 1609003 2415353 := bstep (se 2 (by rfl) ⟨905757, by rfl⟩ : syracuseStep 2415353 = 1811515) B1811515
theorem B2415455 : Blo 1609003 2415455 := bstep (se 1 (by rfl) ⟨1811591, by rfl⟩ : syracuseStep 2415455 = 3623183) B3623183
theorem B2718569 : Blo 1609003 2718569 := bstep (se 2 (by rfl) ⟨1019463, by rfl⟩ : syracuseStep 2718569 = 2038927) B2038927
theorem B2415467 : Blo 1609003 2415467 := bstep (se 1 (by rfl) ⟨1811600, by rfl⟩ : syracuseStep 2415467 = 3623201) B3623201
theorem B6110113 : Blo 1609003 6110113 := bstep (se 2 (by rfl) ⟨2291292, by rfl⟩ : syracuseStep 6110113 = 4582585) B4582585
theorem B9296869 : Blo 1609003 9296869 := bstep (se 4 (by rfl) ⟨871581, by rfl⟩ : syracuseStep 9296869 = 1743163) B1743163
theorem B12221441 : Blo 1609003 12221441 := bstep (se 2 (by rfl) ⟨4583040, by rfl⟩ : syracuseStep 12221441 = 9166081) B9166081
theorem B3054601 : Blo 1609003 3054601 := bstep (se 2 (by rfl) ⟨1145475, by rfl⟩ : syracuseStep 3054601 = 2290951) B2290951
theorem B3439673 : Blo 1609003 3439673 := bstep (se 2 (by rfl) ⟨1289877, by rfl⟩ : syracuseStep 3439673 = 2579755) B2579755
theorem B2415695 : Blo 1609003 2415695 := bstep (se 1 (by rfl) ⟨1811771, by rfl⟩ : syracuseStep 2415695 = 3623543) B3623543
theorem B2579627 : Blo 1609003 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B2415815 : Blo 1609003 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B8150219 : Blo 1609003 8150219 := bstep (se 1 (by rfl) ⟨6112664, by rfl⟩ : syracuseStep 8150219 = 12225329) B12225329
theorem B20913497 : Blo 1609003 20913497 := bstep (se 2 (by rfl) ⟨7842561, by rfl⟩ : syracuseStep 20913497 = 15685123) B15685123
theorem B2415977 : Blo 1609003 2415977 := bstep (se 2 (by rfl) ⟨905991, by rfl⟩ : syracuseStep 2415977 = 1811983) B1811983
theorem B5430671 : Blo 1609003 5430671 := bstep (se 1 (by rfl) ⟨4073003, by rfl⟩ : syracuseStep 5430671 = 8146007) B8146007
theorem B2416055 : Blo 1609003 2416055 := bstep (se 1 (by rfl) ⟨1812041, by rfl⟩ : syracuseStep 2416055 = 3624083) B3624083
theorem B2416091 : Blo 1609003 2416091 := bstep (se 1 (by rfl) ⟨1812068, by rfl⟩ : syracuseStep 2416091 = 3624137) B3624137
theorem B4587131 : Blo 1609003 4587131 := bstep (se 1 (by rfl) ⟨3440348, by rfl⟩ : syracuseStep 4587131 = 6880697) B6880697
theorem B44064395 : Blo 1609003 44064395 := bstep (se 1 (by rfl) ⟨33048296, by rfl⟩ : syracuseStep 44064395 = 66096593) B66096593
theorem B7732883 : Blo 1609003 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B5430995 : Blo 1609003 5430995 := bstep (se 1 (by rfl) ⟨4073246, by rfl⟩ : syracuseStep 5430995 = 8146493) B8146493
theorem B3055315 : Blo 1609003 3055315 := bstep (se 1 (by rfl) ⟨2291486, by rfl⟩ : syracuseStep 3055315 = 4582973) B4582973
theorem B9789149 : Blo 1609003 9789149 := bstep (se 3 (by rfl) ⟨1835465, by rfl⟩ : syracuseStep 9789149 = 3670931) B3670931
theorem B5881643 : Blo 1609003 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3620681 : Blo 1609003 3620681 := bstep (se 2 (by rfl) ⟨1357755, by rfl⟩ : syracuseStep 3620681 = 2715511) B2715511
theorem B6111071 : Blo 1609003 6111071 := bstep (se 1 (by rfl) ⟨4583303, by rfl⟩ : syracuseStep 6111071 = 9166607) B9166607
theorem B6111085 : Blo 1609003 6111085 := bstep (se 3 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 6111085 = 2291657) B2291657
theorem B13049761 : Blo 1609003 13049761 := bstep (se 2 (by rfl) ⟨4893660, by rfl⟩ : syracuseStep 13049761 = 9787321) B9787321
theorem B13746185 : Blo 1609003 13746185 := bstep (se 2 (by rfl) ⟨5154819, by rfl⟩ : syracuseStep 13746185 = 10309639) B10309639
theorem B4587529 : Blo 1609003 4587529 := bstep (se 2 (by rfl) ⟨1720323, by rfl⟩ : syracuseStep 4587529 = 3440647) B3440647
theorem B12230675 : Blo 1609003 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B14680115 : Blo 1609003 14680115 := bstep (se 1 (by rfl) ⟨11010086, by rfl⟩ : syracuseStep 14680115 = 22020173) B22020173
theorem B8708147 : Blo 1609003 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B3620969 : Blo 1609003 3620969 := bstep (se 2 (by rfl) ⟨1357863, by rfl⟩ : syracuseStep 3620969 = 2715727) B2715727
theorem B1810651 : Blo 1609003 1810651 := bstep (se 1 (by rfl) ⟨1357988, by rfl⟩ : syracuseStep 1810651 = 2715977) B2715977
theorem B5431643 : Blo 1609003 5431643 := bstep (se 1 (by rfl) ⟨4073732, by rfl⟩ : syracuseStep 5431643 = 8147465) B8147465
theorem B4350419 : Blo 1609003 4350419 := bstep (se 1 (by rfl) ⟨3262814, by rfl⟩ : syracuseStep 4350419 = 6525629) B6525629
theorem B8151515 : Blo 1609003 8151515 := bstep (se 1 (by rfl) ⟨6113636, by rfl⟩ : syracuseStep 8151515 = 12227273) B12227273
theorem B1810939 : Blo 1609003 1810939 := bstep (se 1 (by rfl) ⟨1358204, by rfl⟩ : syracuseStep 1810939 = 2716409) B2716409
theorem B3621455 : Blo 1609003 3621455 := bstep (se 1 (by rfl) ⟨2716091, by rfl⟩ : syracuseStep 3621455 = 5432183) B5432183
theorem B1811119 : Blo 1609003 1811119 := bstep (se 1 (by rfl) ⟨1358339, by rfl⟩ : syracuseStep 1811119 = 2716679) B2716679
theorem B6193847 : Blo 1609003 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B11600567 : Blo 1609003 11600567 := bstep (se 1 (by rfl) ⟨8700425, by rfl⟩ : syracuseStep 11600567 = 17400851) B17400851
theorem B3621599 : Blo 1609003 3621599 := bstep (se 1 (by rfl) ⟨2716199, by rfl⟩ : syracuseStep 3621599 = 5432399) B5432399
theorem B8152001 : Blo 1609003 8152001 := bstep (se 2 (by rfl) ⟨3057000, by rfl⟩ : syracuseStep 8152001 = 6114001) B6114001
theorem B1811407 : Blo 1609003 1811407 := bstep (se 1 (by rfl) ⟨1358555, by rfl⟩ : syracuseStep 1811407 = 2717111) B2717111
theorem B3621851 : Blo 1609003 3621851 := bstep (se 1 (by rfl) ⟨2716388, by rfl⟩ : syracuseStep 3621851 = 5432777) B5432777
theorem B3867787 : Blo 1609003 3867787 := bstep (se 1 (by rfl) ⟨2900840, by rfl⟩ : syracuseStep 3867787 = 5801681) B5801681
theorem B3622031 : Blo 1609003 3622031 := bstep (se 1 (by rfl) ⟨2716523, by rfl⟩ : syracuseStep 3622031 = 5433047) B5433047
theorem B3622121 : Blo 1609003 3622121 := bstep (se 2 (by rfl) ⟨1358295, by rfl⟩ : syracuseStep 3622121 = 2716591) B2716591
theorem B3622175 : Blo 1609003 3622175 := bstep (se 1 (by rfl) ⟨2716631, by rfl⟩ : syracuseStep 3622175 = 5433263) B5433263
theorem B5432615 : Blo 1609003 5432615 := bstep (se 1 (by rfl) ⟨4074461, by rfl⟩ : syracuseStep 5432615 = 8148923) B8148923
theorem B12395825 : Blo 1609003 12395825 := bstep (se 2 (by rfl) ⟨4648434, by rfl⟩ : syracuseStep 12395825 = 9296869) B9296869
theorem B1811803 : Blo 1609003 1811803 := bstep (se 1 (by rfl) ⟨1358852, by rfl⟩ : syracuseStep 1811803 = 2717705) B2717705
theorem B4072801 : Blo 1609003 4072801 := bstep (se 2 (by rfl) ⟨1527300, by rfl⟩ : syracuseStep 4072801 = 3054601) B3054601
theorem B107373923 : Blo 1609003 107373923 := bstep (se 1 (by rfl) ⟨80530442, by rfl⟩ : syracuseStep 107373923 = 161060885) B161060885
theorem B1811911 : Blo 1609003 1811911 := bstep (se 1 (by rfl) ⟨1358933, by rfl⟩ : syracuseStep 1811911 = 2717867) B2717867
theorem B6874631 : Blo 1609003 6874631 := bstep (se 1 (by rfl) ⟨5155973, by rfl⟩ : syracuseStep 6874631 = 10311947) B10311947
theorem B3622697 : Blo 1609003 3622697 := bstep (se 2 (by rfl) ⟨1358511, by rfl⟩ : syracuseStep 3622697 = 2717023) B2717023
theorem B1812271 : Blo 1609003 1812271 := bstep (se 1 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 1812271 = 2718407) B2718407
theorem B26109773 : Blo 1609003 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B1812379 : Blo 1609003 1812379 := bstep (se 1 (by rfl) ⟨1359284, by rfl⟩ : syracuseStep 1812379 = 2718569) B2718569
theorem B5433479 : Blo 1609003 5433479 := bstep (se 1 (by rfl) ⟨4075109, by rfl⟩ : syracuseStep 5433479 = 8150219) B8150219
theorem B15476989 : Blo 1609003 15476989 := bstep (se 3 (by rfl) ⟨2901935, by rfl⟩ : syracuseStep 15476989 = 5803871) B5803871
theorem B4073753 : Blo 1609003 4073753 := bstep (se 2 (by rfl) ⟨1527657, by rfl⟩ : syracuseStep 4073753 = 3055315) B3055315
theorem B20637989 : Blo 1609003 20637989 := bstep (se 4 (by rfl) ⟨1934811, by rfl⟩ : syracuseStep 20637989 = 3869623) B3869623
theorem B3058087 : Blo 1609003 3058087 := bstep (se 1 (by rfl) ⟨2293565, by rfl⟩ : syracuseStep 3058087 = 4587131) B4587131
theorem B5155255 : Blo 1609003 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B4074047 : Blo 1609003 4074047 := bstep (se 1 (by rfl) ⟨3055535, by rfl⟩ : syracuseStep 4074047 = 6111071) B6111071
theorem B6113987 : Blo 1609003 6113987 := bstep (se 1 (by rfl) ⟨4585490, by rfl⟩ : syracuseStep 6113987 = 9170981) B9170981
theorem B8145683 : Blo 1609003 8145683 := bstep (se 1 (by rfl) ⟨6109262, by rfl⟩ : syracuseStep 8145683 = 12218525) B12218525
theorem B4074259 : Blo 1609003 4074259 := bstep (se 1 (by rfl) ⟨3055694, by rfl⟩ : syracuseStep 4074259 = 6111389) B6111389
theorem B3623759 : Blo 1609003 3623759 := bstep (se 1 (by rfl) ⟨2717819, by rfl⟩ : syracuseStep 3623759 = 5435639) B5435639
theorem B3623975 : Blo 1609003 3623975 := bstep (se 1 (by rfl) ⟨2717981, by rfl⟩ : syracuseStep 3623975 = 5435963) B5435963
theorem B17206337 : Blo 1609003 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B4074695 : Blo 1609003 4074695 := bstep (se 1 (by rfl) ⟨3056021, by rfl⟩ : syracuseStep 4074695 = 6112043) B6112043
theorem B3624155 : Blo 1609003 3624155 := bstep (se 1 (by rfl) ⟨2718116, by rfl⟩ : syracuseStep 3624155 = 5436233) B5436233
theorem B4074745 : Blo 1609003 4074745 := bstep (se 2 (by rfl) ⟨1528029, by rfl⟩ : syracuseStep 4074745 = 3056059) B3056059
theorem B1609051 : Blo 1609003 1609051 := bstep (se 1 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 1609051 = 2413577) B2413577
theorem B9170273 : Blo 1609003 9170273 := bstep (se 2 (by rfl) ⟨3438852, by rfl⟩ : syracuseStep 9170273 = 6877705) B6877705
theorem B5434721 : Blo 1609003 5434721 := bstep (se 2 (by rfl) ⟨2038020, by rfl⟩ : syracuseStep 5434721 = 4076041) B4076041
theorem B27897185 : Blo 1609003 27897185 := bstep (se 2 (by rfl) ⟨10461444, by rfl⟩ : syracuseStep 27897185 = 20922889) B20922889
theorem B1609071 : Blo 1609003 1609071 := bstep (se 1 (by rfl) ⟨1206803, by rfl⟩ : syracuseStep 1609071 = 2413607) B2413607
theorem B6524297 : Blo 1609003 6524297 := bstep (se 2 (by rfl) ⟨2446611, by rfl⟩ : syracuseStep 6524297 = 4893223) B4893223
theorem B3624353 : Blo 1609003 3624353 := bstep (se 2 (by rfl) ⟨1359132, by rfl⟩ : syracuseStep 3624353 = 2718265) B2718265
theorem B1609127 : Blo 1609003 1609127 := bstep (se 1 (by rfl) ⟨1206845, by rfl⟩ : syracuseStep 1609127 = 2413691) B2413691
theorem B30944753 : Blo 1609003 30944753 := bstep (se 2 (by rfl) ⟨11604282, by rfl⟩ : syracuseStep 30944753 = 23208565) B23208565
theorem B1609211 : Blo 1609003 1609211 := bstep (se 1 (by rfl) ⟨1206908, by rfl⟩ : syracuseStep 1609211 = 2413817) B2413817
theorem B1609279 : Blo 1609003 1609279 := bstep (se 1 (by rfl) ⟨1206959, by rfl⟩ : syracuseStep 1609279 = 2413919) B2413919
theorem B1609287 : Blo 1609003 1609287 := bstep (se 1 (by rfl) ⟨1206965, by rfl⟩ : syracuseStep 1609287 = 2413931) B2413931
theorem B27512459 : Blo 1609003 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B3722939 : Blo 1609003 3722939 := bstep (se 1 (by rfl) ⟨2792204, by rfl⟩ : syracuseStep 3722939 = 5584409) B5584409
theorem B1609439 : Blo 1609003 1609439 := bstep (se 1 (by rfl) ⟨1207079, by rfl⟩ : syracuseStep 1609439 = 2414159) B2414159
theorem B17403659 : Blo 1609003 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B1609519 : Blo 1609003 1609519 := bstep (se 1 (by rfl) ⟨1207139, by rfl⟩ : syracuseStep 1609519 = 2414279) B2414279
theorem B8146817 : Blo 1609003 8146817 := bstep (se 2 (by rfl) ⟨3055056, by rfl⟩ : syracuseStep 8146817 = 6110113) B6110113
theorem B4075393 : Blo 1609003 4075393 := bstep (se 2 (by rfl) ⟨1528272, by rfl⟩ : syracuseStep 4075393 = 3056545) B3056545
theorem B1609627 : Blo 1609003 1609627 := bstep (se 1 (by rfl) ⟨1207220, by rfl⟩ : syracuseStep 1609627 = 2414441) B2414441
theorem B2715599 : Blo 1609003 2715599 := bstep (se 1 (by rfl) ⟨2036699, by rfl⟩ : syracuseStep 2715599 = 4073399) B4073399
theorem B1609679 : Blo 1609003 1609679 := bstep (se 1 (by rfl) ⟨1207259, by rfl⟩ : syracuseStep 1609679 = 2414519) B2414519
theorem B1609703 : Blo 1609003 1609703 := bstep (se 1 (by rfl) ⟨1207277, by rfl⟩ : syracuseStep 1609703 = 2414555) B2414555
theorem B8155241 : Blo 1609003 8155241 := bstep (se 2 (by rfl) ⟨3058215, by rfl⟩ : syracuseStep 8155241 = 6116431) B6116431
theorem B1610015 : Blo 1609003 1610015 := bstep (se 1 (by rfl) ⟨1207511, by rfl⟩ : syracuseStep 1610015 = 2415023) B2415023
theorem B1610075 : Blo 1609003 1610075 := bstep (se 1 (by rfl) ⟨1207556, by rfl⟩ : syracuseStep 1610075 = 2415113) B2415113
theorem B1610095 : Blo 1609003 1610095 := bstep (se 1 (by rfl) ⟨1207571, by rfl⟩ : syracuseStep 1610095 = 2415143) B2415143
theorem B1610151 : Blo 1609003 1610151 := bstep (se 1 (by rfl) ⟨1207613, by rfl⟩ : syracuseStep 1610151 = 2415227) B2415227
theorem B1610235 : Blo 1609003 1610235 := bstep (se 1 (by rfl) ⟨1207676, by rfl⟩ : syracuseStep 1610235 = 2415353) B2415353
theorem B1610303 : Blo 1609003 1610303 := bstep (se 1 (by rfl) ⟨1207727, by rfl⟩ : syracuseStep 1610303 = 2415455) B2415455
theorem B1610311 : Blo 1609003 1610311 := bstep (se 1 (by rfl) ⟨1207733, by rfl⟩ : syracuseStep 1610311 = 2415467) B2415467
theorem B25113185 : Blo 1609003 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B2716267 : Blo 1609003 2716267 := bstep (se 1 (by rfl) ⟨2037200, by rfl⟩ : syracuseStep 2716267 = 4074401) B4074401
theorem B4076153 : Blo 1609003 4076153 := bstep (se 2 (by rfl) ⟨1528557, by rfl⟩ : syracuseStep 4076153 = 3057115) B3057115
theorem B33067673 : Blo 1609003 33067673 := bstep (se 2 (by rfl) ⟨12400377, by rfl⟩ : syracuseStep 33067673 = 24800755) B24800755
theorem B8147627 : Blo 1609003 8147627 := bstep (se 1 (by rfl) ⟨6110720, by rfl⟩ : syracuseStep 8147627 = 12221441) B12221441
theorem B4076203 : Blo 1609003 4076203 := bstep (se 1 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 4076203 = 6114305) B6114305
theorem B69612209 : Blo 1609003 69612209 := bstep (se 2 (by rfl) ⟨26104578, by rfl⟩ : syracuseStep 69612209 = 52209157) B52209157
theorem B1610463 : Blo 1609003 1610463 := bstep (se 1 (by rfl) ⟨1207847, by rfl⟩ : syracuseStep 1610463 = 2415695) B2415695
theorem B1610543 : Blo 1609003 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B4584271 : Blo 1609003 4584271 := bstep (se 1 (by rfl) ⟨3438203, by rfl⟩ : syracuseStep 4584271 = 6876407) B6876407
theorem B6878047 : Blo 1609003 6878047 := bstep (se 1 (by rfl) ⟨5158535, by rfl⟩ : syracuseStep 6878047 = 10317071) B10317071
theorem B2716571 : Blo 1609003 2716571 := bstep (se 1 (by rfl) ⟨2037428, by rfl⟩ : syracuseStep 2716571 = 4074857) B4074857
theorem B1610651 : Blo 1609003 1610651 := bstep (se 1 (by rfl) ⟨1207988, by rfl⟩ : syracuseStep 1610651 = 2415977) B2415977
theorem B9171913 : Blo 1609003 9171913 := bstep (se 2 (by rfl) ⟨3439467, by rfl⟩ : syracuseStep 9171913 = 6878935) B6878935
theorem B1610703 : Blo 1609003 1610703 := bstep (se 1 (by rfl) ⟨1208027, by rfl⟩ : syracuseStep 1610703 = 2416055) B2416055
theorem B4076507 : Blo 1609003 4076507 := bstep (se 1 (by rfl) ⟨3057380, by rfl⟩ : syracuseStep 4076507 = 6114761) B6114761
theorem B1610727 : Blo 1609003 1610727 := bstep (se 1 (by rfl) ⟨1208045, by rfl⟩ : syracuseStep 1610727 = 2416091) B2416091
theorem B4584545 : Blo 1609003 4584545 := bstep (se 2 (by rfl) ⟨1719204, by rfl⟩ : syracuseStep 4584545 = 3438409) B3438409
theorem B8148113 : Blo 1609003 8148113 := bstep (se 2 (by rfl) ⟨3055542, by rfl⟩ : syracuseStep 8148113 = 6111085) B6111085
theorem B6526099 : Blo 1609003 6526099 := bstep (se 1 (by rfl) ⟨4894574, by rfl⟩ : syracuseStep 6526099 = 9789149) B9789149
theorem B3921095 : Blo 1609003 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2413787 : Blo 1609003 2413787 := bstep (se 1 (by rfl) ⟨1810340, by rfl⟩ : syracuseStep 2413787 = 3620681) B3620681
theorem B44086517 : Blo 1609003 44086517 := bstep (se 5 (by rfl) ⟨2066555, by rfl⟩ : syracuseStep 44086517 = 4133111) B4133111
theorem B5436665 : Blo 1609003 5436665 := bstep (se 2 (by rfl) ⟨2038749, by rfl⟩ : syracuseStep 5436665 = 4077499) B4077499
theorem B15480065 : Blo 1609003 15480065 := bstep (se 2 (by rfl) ⟨5805024, by rfl⟩ : syracuseStep 15480065 = 11610049) B11610049
theorem B4076831 : Blo 1609003 4076831 := bstep (se 1 (by rfl) ⟨3057623, by rfl⟩ : syracuseStep 4076831 = 6115247) B6115247
theorem B2413961 : Blo 1609003 2413961 := bstep (se 2 (by rfl) ⟨905235, by rfl⟩ : syracuseStep 2413961 = 1810471) B1810471
theorem B2176507 : Blo 1609003 2176507 := bstep (se 1 (by rfl) ⟨1632380, by rfl⟩ : syracuseStep 2176507 = 3264761) B3264761
theorem B5436935 : Blo 1609003 5436935 := bstep (se 1 (by rfl) ⟨4077701, by rfl⟩ : syracuseStep 5436935 = 8155403) B8155403
theorem B2414315 : Blo 1609003 2414315 := bstep (se 1 (by rfl) ⟨1810736, by rfl⟩ : syracuseStep 2414315 = 3621473) B3621473
theorem B3921671 : Blo 1609003 3921671 := bstep (se 1 (by rfl) ⟨2941253, by rfl⟩ : syracuseStep 3921671 = 5882507) B5882507
theorem B6879005 : Blo 1609003 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B5101417 : Blo 1609003 5101417 := bstep (se 2 (by rfl) ⟨1913031, by rfl⟩ : syracuseStep 5101417 = 3826063) B3826063
theorem B2414543 : Blo 1609003 2414543 := bstep (se 1 (by rfl) ⟨1810907, by rfl⟩ : syracuseStep 2414543 = 3621815) B3621815
theorem B2414939 : Blo 1609003 2414939 := bstep (se 1 (by rfl) ⟨1811204, by rfl⟩ : syracuseStep 2414939 = 3622409) B3622409
theorem B2292079 : Blo 1609003 2292079 := bstep (se 1 (by rfl) ⟨1719059, by rfl⟩ : syracuseStep 2292079 = 3438119) B3438119
theorem B2415167 : Blo 1609003 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B11606591 : Blo 1609003 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B2292295 : Blo 1609003 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B6199915 : Blo 1609003 6199915 := bstep (se 1 (by rfl) ⟨4649936, by rfl⟩ : syracuseStep 6199915 = 9299873) B9299873
theorem B2415287 : Blo 1609003 2415287 := bstep (se 1 (by rfl) ⟨1811465, by rfl⟩ : syracuseStep 2415287 = 3622931) B3622931
theorem B8698589 : Blo 1609003 8698589 := bstep (se 3 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 8698589 = 3261971) B3261971
theorem B6527735 : Blo 1609003 6527735 := bstep (se 1 (by rfl) ⟨4895801, by rfl⟩ : syracuseStep 6527735 = 9791603) B9791603
theorem B10320659 : Blo 1609003 10320659 := bstep (se 1 (by rfl) ⟨7740494, by rfl⟩ : syracuseStep 10320659 = 15480989) B15480989
theorem B27499337 : Blo 1609003 27499337 := bstep (se 2 (by rfl) ⟨10312251, by rfl⟩ : syracuseStep 27499337 = 20624503) B20624503
theorem B2415515 : Blo 1609003 2415515 := bstep (se 1 (by rfl) ⟨1811636, by rfl⟩ : syracuseStep 2415515 = 3623273) B3623273
theorem B6527915 : Blo 1609003 6527915 := bstep (se 1 (by rfl) ⟨4895936, by rfl⟩ : syracuseStep 6527915 = 9791873) B9791873
theorem B18594845 : Blo 1609003 18594845 := bstep (se 3 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 18594845 = 6973067) B6973067
theorem B3439759 : Blo 1609003 3439759 := bstep (se 1 (by rfl) ⟨2579819, by rfl⟩ : syracuseStep 3439759 = 5159639) B5159639
theorem B5160125 : Blo 1609003 5160125 := bstep (se 3 (by rfl) ⟨967523, by rfl⟩ : syracuseStep 5160125 = 1935047) B1935047
theorem B2448679 : Blo 1609003 2448679 := bstep (se 1 (by rfl) ⟨1836509, by rfl⟩ : syracuseStep 2448679 = 3673019) B3673019
theorem B2415911 : Blo 1609003 2415911 := bstep (se 1 (by rfl) ⟨1811933, by rfl⟩ : syracuseStep 2415911 = 3623867) B3623867
theorem B8699233 : Blo 1609003 8699233 := bstep (se 2 (by rfl) ⟨3262212, by rfl⟩ : syracuseStep 8699233 = 6524425) B6524425
theorem B2293115 : Blo 1609003 2293115 := bstep (se 1 (by rfl) ⟨1719836, by rfl⟩ : syracuseStep 2293115 = 3439673) B3439673
theorem B2415995 : Blo 1609003 2415995 := bstep (se 1 (by rfl) ⟨1811996, by rfl⟩ : syracuseStep 2415995 = 3623993) B3623993
theorem B2416121 : Blo 1609003 2416121 := bstep (se 2 (by rfl) ⟨906045, by rfl⟩ : syracuseStep 2416121 = 1812091) B1812091
theorem B5586425 : Blo 1609003 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B8371721 : Blo 1609003 8371721 := bstep (se 2 (by rfl) ⟨3139395, by rfl⟩ : syracuseStep 8371721 = 6278791) B6278791
theorem B8150543 : Blo 1609003 8150543 := bstep (se 1 (by rfl) ⟨6112907, by rfl⟩ : syracuseStep 8150543 = 12225815) B12225815
theorem B13049369 : Blo 1609003 13049369 := bstep (se 2 (by rfl) ⟨4893513, by rfl⟩ : syracuseStep 13049369 = 9787027) B9787027
theorem B13942331 : Blo 1609003 13942331 := bstep (se 1 (by rfl) ⟨10456748, by rfl⟩ : syracuseStep 13942331 = 20913497) B20913497
theorem B3620447 : Blo 1609003 3620447 := bstep (se 1 (by rfl) ⟨2715335, by rfl⟩ : syracuseStep 3620447 = 5430671) B5430671
theorem B2416223 : Blo 1609003 2416223 := bstep (se 1 (by rfl) ⟨1812167, by rfl⟩ : syracuseStep 2416223 = 3624335) B3624335
theorem B29376263 : Blo 1609003 29376263 := bstep (se 1 (by rfl) ⟨22032197, by rfl⟩ : syracuseStep 29376263 = 44064395) B44064395
theorem B3620663 : Blo 1609003 3620663 := bstep (se 1 (by rfl) ⟨2715497, by rfl⟩ : syracuseStep 3620663 = 5430995) B5430995
theorem B2416439 : Blo 1609003 2416439 := bstep (se 1 (by rfl) ⟨1812329, by rfl⟩ : syracuseStep 2416439 = 3624659) B3624659
theorem B1810255 : Blo 1609003 1810255 := bstep (se 1 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 1810255 = 2715383) B2715383
theorem B17399681 : Blo 1609003 17399681 := bstep (se 2 (by rfl) ⟨6524880, by rfl⟩ : syracuseStep 17399681 = 13049761) B13049761
theorem B3621095 : Blo 1609003 3621095 := bstep (se 1 (by rfl) ⟨2715821, by rfl⟩ : syracuseStep 3621095 = 5431643) B5431643
theorem B2900279 : Blo 1609003 2900279 := bstep (se 1 (by rfl) ⟨2175209, by rfl⟩ : syracuseStep 2900279 = 4350419) B4350419
theorem B20635985 : Blo 1609003 20635985 := bstep (se 2 (by rfl) ⟨7738494, by rfl⟩ : syracuseStep 20635985 = 15476989) B15476989
theorem B22045115 : Blo 1609003 22045115 := bstep (se 1 (by rfl) ⟨16533836, by rfl⟩ : syracuseStep 22045115 = 33067673) B33067673
theorem B5431751 : Blo 1609003 5431751 := bstep (se 1 (by rfl) ⟨4073813, by rfl⟩ : syracuseStep 5431751 = 8147627) B8147627
theorem B46408139 : Blo 1609003 46408139 := bstep (se 1 (by rfl) ⟨34806104, by rfl⟩ : syracuseStep 46408139 = 69612209) B69612209
theorem B4129231 : Blo 1609003 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B7733711 : Blo 1609003 7733711 := bstep (se 1 (by rfl) ⟨5800283, by rfl⟩ : syracuseStep 7733711 = 11600567) B11600567
theorem B3056105 : Blo 1609003 3056105 := bstep (se 2 (by rfl) ⟨1146039, by rfl⟩ : syracuseStep 3056105 = 2292079) B2292079
theorem B6873673 : Blo 1609003 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B1811047 : Blo 1609003 1811047 := bstep (se 1 (by rfl) ⟨1358285, by rfl⟩ : syracuseStep 1811047 = 2716571) B2716571
theorem B3056363 : Blo 1609003 3056363 := bstep (se 1 (by rfl) ⟨2292272, by rfl⟩ : syracuseStep 3056363 = 4584545) B4584545
theorem B3056393 : Blo 1609003 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B5432075 : Blo 1609003 5432075 := bstep (se 1 (by rfl) ⟨4074056, by rfl⟩ : syracuseStep 5432075 = 8148113) B8148113
theorem B3621689 : Blo 1609003 3621689 := bstep (se 2 (by rfl) ⟨1358133, by rfl⟩ : syracuseStep 3621689 = 2716267) B2716267
theorem B8266553 : Blo 1609003 8266553 := bstep (se 2 (by rfl) ⟨3099957, by rfl⟩ : syracuseStep 8266553 = 6199915) B6199915
theorem B3621743 : Blo 1609003 3621743 := bstep (se 1 (by rfl) ⟨2716307, by rfl⟩ : syracuseStep 3621743 = 5432615) B5432615
theorem B71582615 : Blo 1609003 71582615 := bstep (se 1 (by rfl) ⟨53686961, by rfl⟩ : syracuseStep 71582615 = 107373923) B107373923
theorem B5432345 : Blo 1609003 5432345 := bstep (se 2 (by rfl) ⟨2037129, by rfl⟩ : syracuseStep 5432345 = 4074259) B4074259
theorem B6112361 : Blo 1609003 6112361 := bstep (se 2 (by rfl) ⟨2292135, by rfl⟩ : syracuseStep 6112361 = 4584271) B4584271
theorem B2614447 : Blo 1609003 2614447 := bstep (se 1 (by rfl) ⟨1960835, by rfl⟩ : syracuseStep 2614447 = 3921671) B3921671
theorem B22324589 : Blo 1609003 22324589 := bstep (se 3 (by rfl) ⟨4185860, by rfl⟩ : syracuseStep 22324589 = 8371721) B8371721
theorem B3622319 : Blo 1609003 3622319 := bstep (se 1 (by rfl) ⟨2716739, by rfl⟩ : syracuseStep 3622319 = 5433479) B5433479
theorem B8701465 : Blo 1609003 8701465 := bstep (se 2 (by rfl) ⟨3263049, by rfl⟩ : syracuseStep 8701465 = 6526099) B6526099
theorem B5432993 : Blo 1609003 5432993 := bstep (se 2 (by rfl) ⟨2037372, by rfl⟩ : syracuseStep 5432993 = 4074745) B4074745
theorem B4351823 : Blo 1609003 4351823 := bstep (se 1 (by rfl) ⟨3263867, by rfl⟩ : syracuseStep 4351823 = 6527735) B6527735
theorem B4351943 : Blo 1609003 4351943 := bstep (se 1 (by rfl) ⟨3263957, by rfl⟩ : syracuseStep 4351943 = 6527915) B6527915
theorem B2902009 : Blo 1609003 2902009 := bstep (se 2 (by rfl) ⟨1088253, by rfl⟩ : syracuseStep 2902009 = 2176507) B2176507
theorem B12396563 : Blo 1609003 12396563 := bstep (se 1 (by rfl) ⟨9297422, by rfl⟩ : syracuseStep 12396563 = 18594845) B18594845
theorem B11470891 : Blo 1609003 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B6113515 : Blo 1609003 6113515 := bstep (se 1 (by rfl) ⟨4585136, by rfl⟩ : syracuseStep 6113515 = 9170273) B9170273
theorem B3623147 : Blo 1609003 3623147 := bstep (se 1 (by rfl) ⟨2717360, by rfl⟩ : syracuseStep 3623147 = 5434721) B5434721
theorem B18598123 : Blo 1609003 18598123 := bstep (se 1 (by rfl) ⟨13948592, by rfl⟩ : syracuseStep 18598123 = 27897185) B27897185
theorem B20629835 : Blo 1609003 20629835 := bstep (se 1 (by rfl) ⟨15472376, by rfl⟩ : syracuseStep 20629835 = 30944753) B30944753
theorem B5433695 : Blo 1609003 5433695 := bstep (se 1 (by rfl) ⟨4075271, by rfl⟩ : syracuseStep 5433695 = 8150543) B8150543
theorem B6801889 : Blo 1609003 6801889 := bstep (se 2 (by rfl) ⟨2550708, by rfl⟩ : syracuseStep 6801889 = 5101417) B5101417
theorem B5433857 : Blo 1609003 5433857 := bstep (se 2 (by rfl) ⟨2037696, by rfl⟩ : syracuseStep 5433857 = 4075393) B4075393
theorem B11602439 : Blo 1609003 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B8153783 : Blo 1609003 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B5434343 : Blo 1609003 5434343 := bstep (se 1 (by rfl) ⟨4075757, by rfl⟩ : syracuseStep 5434343 = 8151515) B8151515
theorem B10456253 : Blo 1609003 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B5434667 : Blo 1609003 5434667 := bstep (se 1 (by rfl) ⟨4076000, by rfl⟩ : syracuseStep 5434667 = 8152001) B8152001
theorem B1609191 : Blo 1609003 1609191 := bstep (se 1 (by rfl) ⟨1206893, by rfl⟩ : syracuseStep 1609191 = 2413787) B2413787
theorem B3624443 : Blo 1609003 3624443 := bstep (se 1 (by rfl) ⟨2718332, by rfl⟩ : syracuseStep 3624443 = 5436665) B5436665
theorem B5434937 : Blo 1609003 5434937 := bstep (se 2 (by rfl) ⟨2038101, by rfl⟩ : syracuseStep 5434937 = 4076203) B4076203
theorem B1609307 : Blo 1609003 1609307 := bstep (se 1 (by rfl) ⟨1206980, by rfl⟩ : syracuseStep 1609307 = 2413961) B2413961
theorem B6114973 : Blo 1609003 6114973 := bstep (se 3 (by rfl) ⟨1146557, by rfl⟩ : syracuseStep 6114973 = 2293115) B2293115
theorem B4583087 : Blo 1609003 4583087 := bstep (se 1 (by rfl) ⟨3437315, by rfl⟩ : syracuseStep 4583087 = 6874631) B6874631
theorem B3624623 : Blo 1609003 3624623 := bstep (se 1 (by rfl) ⟨2718467, by rfl⟩ : syracuseStep 3624623 = 5436935) B5436935
theorem B9170729 : Blo 1609003 9170729 := bstep (se 2 (by rfl) ⟨3439023, by rfl⟩ : syracuseStep 9170729 = 6878047) B6878047
theorem B1609543 : Blo 1609003 1609543 := bstep (se 1 (by rfl) ⟨1207157, by rfl⟩ : syracuseStep 1609543 = 2414315) B2414315
theorem B1609695 : Blo 1609003 1609695 := bstep (se 1 (by rfl) ⟨1207271, by rfl⟩ : syracuseStep 1609695 = 2414543) B2414543
theorem B5157049 : Blo 1609003 5157049 := bstep (se 2 (by rfl) ⟨1933893, by rfl⟩ : syracuseStep 5157049 = 3867787) B3867787
theorem B2715835 : Blo 1609003 2715835 := bstep (se 1 (by rfl) ⟨2036876, by rfl⟩ : syracuseStep 2715835 = 4073753) B4073753
theorem B13758659 : Blo 1609003 13758659 := bstep (se 1 (by rfl) ⟨10318994, by rfl⟩ : syracuseStep 13758659 = 20637989) B20637989
theorem B1609959 : Blo 1609003 1609959 := bstep (se 1 (by rfl) ⟨1207469, by rfl⟩ : syracuseStep 1609959 = 2414939) B2414939
theorem B2716031 : Blo 1609003 2716031 := bstep (se 1 (by rfl) ⟨2037023, by rfl⟩ : syracuseStep 2716031 = 4074047) B4074047
theorem B1610111 : Blo 1609003 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B7737727 : Blo 1609003 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B3264905 : Blo 1609003 3264905 := bstep (se 2 (by rfl) ⟨1224339, by rfl⟩ : syracuseStep 3264905 = 2448679) B2448679
theorem B1610191 : Blo 1609003 1610191 := bstep (se 1 (by rfl) ⟨1207643, by rfl⟩ : syracuseStep 1610191 = 2415287) B2415287
theorem B4075991 : Blo 1609003 4075991 := bstep (se 1 (by rfl) ⟨3056993, by rfl⟩ : syracuseStep 4075991 = 6113987) B6113987
theorem B1610343 : Blo 1609003 1610343 := bstep (se 1 (by rfl) ⟨1207757, by rfl⟩ : syracuseStep 1610343 = 2415515) B2415515
theorem B2716463 : Blo 1609003 2716463 := bstep (se 1 (by rfl) ⟨2037347, by rfl⟩ : syracuseStep 2716463 = 4074695) B4074695
theorem B1610607 : Blo 1609003 1610607 := bstep (se 1 (by rfl) ⟨1207955, by rfl⟩ : syracuseStep 1610607 = 2415911) B2415911
theorem B1610663 : Blo 1609003 1610663 := bstep (se 1 (by rfl) ⟨1207997, by rfl⟩ : syracuseStep 1610663 = 2415995) B2415995
theorem B1610747 : Blo 1609003 1610747 := bstep (se 1 (by rfl) ⟨1208060, by rfl⟩ : syracuseStep 1610747 = 2416121) B2416121
theorem B3724283 : Blo 1609003 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B9294887 : Blo 1609003 9294887 := bstep (se 1 (by rfl) ⟨6971165, by rfl⟩ : syracuseStep 9294887 = 13942331) B13942331
theorem B2413631 : Blo 1609003 2413631 := bstep (se 1 (by rfl) ⟨1810223, by rfl⟩ : syracuseStep 2413631 = 3620447) B3620447
theorem B1610815 : Blo 1609003 1610815 := bstep (se 1 (by rfl) ⟨1208111, by rfl⟩ : syracuseStep 1610815 = 2416223) B2416223
theorem B2413673 : Blo 1609003 2413673 := bstep (se 2 (by rfl) ⟨905127, by rfl⟩ : syracuseStep 2413673 = 1810255) B1810255
theorem B19584175 : Blo 1609003 19584175 := bstep (se 1 (by rfl) ⟨14688131, by rfl⟩ : syracuseStep 19584175 = 29376263) B29376263
theorem B2413775 : Blo 1609003 2413775 := bstep (se 1 (by rfl) ⟨1810331, by rfl⟩ : syracuseStep 2413775 = 3620663) B3620663
theorem B1610959 : Blo 1609003 1610959 := bstep (se 1 (by rfl) ⟨1208219, by rfl⟩ : syracuseStep 1610959 = 2416439) B2416439
theorem B9164123 : Blo 1609003 9164123 := bstep (se 1 (by rfl) ⟨6873092, by rfl⟩ : syracuseStep 9164123 = 13746185) B13746185
theorem B6116705 : Blo 1609003 6116705 := bstep (se 2 (by rfl) ⟨2293764, by rfl⟩ : syracuseStep 6116705 = 4587529) B4587529
theorem B9786743 : Blo 1609003 9786743 := bstep (se 1 (by rfl) ⟨7340057, by rfl⟩ : syracuseStep 9786743 = 14680115) B14680115
theorem B5805431 : Blo 1609003 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B2413979 : Blo 1609003 2413979 := bstep (se 1 (by rfl) ⟨1810484, by rfl⟩ : syracuseStep 2413979 = 3620969) B3620969
theorem B5436827 : Blo 1609003 5436827 := bstep (se 1 (by rfl) ⟨4077620, by rfl⟩ : syracuseStep 5436827 = 8155241) B8155241
theorem B2414201 : Blo 1609003 2414201 := bstep (se 2 (by rfl) ⟨905325, by rfl⟩ : syracuseStep 2414201 = 1810651) B1810651
theorem B2414303 : Blo 1609003 2414303 := bstep (se 1 (by rfl) ⟨1810727, by rfl⟩ : syracuseStep 2414303 = 3621455) B3621455
theorem B16742123 : Blo 1609003 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B2717435 : Blo 1609003 2717435 := bstep (se 1 (by rfl) ⟨2038076, by rfl⟩ : syracuseStep 2717435 = 4076153) B4076153
theorem B2414399 : Blo 1609003 2414399 := bstep (se 1 (by rfl) ⟨1810799, by rfl⟩ : syracuseStep 2414399 = 3621599) B3621599
theorem B4077449 : Blo 1609003 4077449 := bstep (se 2 (by rfl) ⟨1529043, by rfl⟩ : syracuseStep 4077449 = 3058087) B3058087
theorem B2414567 : Blo 1609003 2414567 := bstep (se 1 (by rfl) ⟨1810925, by rfl⟩ : syracuseStep 2414567 = 3621851) B3621851
theorem B2717671 : Blo 1609003 2717671 := bstep (se 1 (by rfl) ⟨2038253, by rfl⟩ : syracuseStep 2717671 = 4076507) B4076507
theorem B2414585 : Blo 1609003 2414585 := bstep (se 2 (by rfl) ⟨905469, by rfl⟩ : syracuseStep 2414585 = 1810939) B1810939
theorem B2414687 : Blo 1609003 2414687 := bstep (se 1 (by rfl) ⟨1811015, by rfl⟩ : syracuseStep 2414687 = 3622031) B3622031
theorem B2414747 : Blo 1609003 2414747 := bstep (se 1 (by rfl) ⟨1811060, by rfl⟩ : syracuseStep 2414747 = 3622121) B3622121
theorem B29391011 : Blo 1609003 29391011 := bstep (se 1 (by rfl) ⟨22043258, by rfl⟩ : syracuseStep 29391011 = 44086517) B44086517
theorem B10320043 : Blo 1609003 10320043 := bstep (se 1 (by rfl) ⟨7740032, by rfl⟩ : syracuseStep 10320043 = 15480065) B15480065
theorem B2414783 : Blo 1609003 2414783 := bstep (se 1 (by rfl) ⟨1811087, by rfl⟩ : syracuseStep 2414783 = 3622175) B3622175
theorem B2717887 : Blo 1609003 2717887 := bstep (se 1 (by rfl) ⟨2038415, by rfl⟩ : syracuseStep 2717887 = 4076831) B4076831
theorem B8263883 : Blo 1609003 8263883 := bstep (se 1 (by rfl) ⟨6197912, by rfl⟩ : syracuseStep 8263883 = 12395825) B12395825
theorem B2414825 : Blo 1609003 2414825 := bstep (se 2 (by rfl) ⟨905559, by rfl⟩ : syracuseStep 2414825 = 1811119) B1811119
theorem B4586003 : Blo 1609003 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B2415131 : Blo 1609003 2415131 := bstep (se 1 (by rfl) ⟨1811348, by rfl⟩ : syracuseStep 2415131 = 3622697) B3622697
theorem B17406515 : Blo 1609003 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B12229217 : Blo 1609003 12229217 := bstep (se 2 (by rfl) ⟨4585956, by rfl⟩ : syracuseStep 12229217 = 9171913) B9171913
theorem B2415209 : Blo 1609003 2415209 := bstep (se 2 (by rfl) ⟨905703, by rfl⟩ : syracuseStep 2415209 = 1811407) B1811407
theorem B4586345 : Blo 1609003 4586345 := bstep (se 2 (by rfl) ⟨1719879, by rfl⟩ : syracuseStep 4586345 = 3439759) B3439759
theorem B2415737 : Blo 1609003 2415737 := bstep (se 2 (by rfl) ⟨905901, by rfl⟩ : syracuseStep 2415737 = 1811803) B1811803
theorem B5430401 : Blo 1609003 5430401 := bstep (se 2 (by rfl) ⟨2036400, by rfl⟩ : syracuseStep 5430401 = 4072801) B4072801
theorem B11598977 : Blo 1609003 11598977 := bstep (se 2 (by rfl) ⟨4349616, by rfl⟩ : syracuseStep 11598977 = 8699233) B8699233
theorem B5799059 : Blo 1609003 5799059 := bstep (se 1 (by rfl) ⟨4349294, by rfl⟩ : syracuseStep 5799059 = 8698589) B8698589
theorem B5430455 : Blo 1609003 5430455 := bstep (se 1 (by rfl) ⟨4072841, by rfl⟩ : syracuseStep 5430455 = 8145683) B8145683
theorem B6880439 : Blo 1609003 6880439 := bstep (se 1 (by rfl) ⟨5160329, by rfl⟩ : syracuseStep 6880439 = 10320659) B10320659
theorem B18332891 : Blo 1609003 18332891 := bstep (se 1 (by rfl) ⟨13749668, by rfl⟩ : syracuseStep 18332891 = 27499337) B27499337
theorem B2415839 : Blo 1609003 2415839 := bstep (se 1 (by rfl) ⟨1811879, by rfl⟩ : syracuseStep 2415839 = 3623759) B3623759
theorem B2415881 : Blo 1609003 2415881 := bstep (se 2 (by rfl) ⟨905955, by rfl⟩ : syracuseStep 2415881 = 1811911) B1811911
theorem B2415983 : Blo 1609003 2415983 := bstep (se 1 (by rfl) ⟨1811987, by rfl⟩ : syracuseStep 2415983 = 3623975) B3623975
theorem B3440083 : Blo 1609003 3440083 := bstep (se 1 (by rfl) ⟨2580062, by rfl⟩ : syracuseStep 3440083 = 5160125) B5160125
theorem B2416103 : Blo 1609003 2416103 := bstep (se 1 (by rfl) ⟨1812077, by rfl⟩ : syracuseStep 2416103 = 3624155) B3624155
theorem B4349531 : Blo 1609003 4349531 := bstep (se 1 (by rfl) ⟨3262148, by rfl⟩ : syracuseStep 4349531 = 6524297) B6524297
theorem B2416235 : Blo 1609003 2416235 := bstep (se 1 (by rfl) ⟨1812176, by rfl⟩ : syracuseStep 2416235 = 3624353) B3624353
theorem B8699579 : Blo 1609003 8699579 := bstep (se 1 (by rfl) ⟨6524684, by rfl⟩ : syracuseStep 8699579 = 13049369) B13049369
theorem B2416361 : Blo 1609003 2416361 := bstep (se 2 (by rfl) ⟨906135, by rfl⟩ : syracuseStep 2416361 = 1812271) B1812271
theorem B18341639 : Blo 1609003 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B2481959 : Blo 1609003 2481959 := bstep (se 1 (by rfl) ⟨1861469, by rfl⟩ : syracuseStep 2481959 = 3722939) B3722939
theorem B2416505 : Blo 1609003 2416505 := bstep (se 2 (by rfl) ⟨906189, by rfl⟩ : syracuseStep 2416505 = 1812379) B1812379
theorem B5431211 : Blo 1609003 5431211 := bstep (se 1 (by rfl) ⟨4073408, by rfl⟩ : syracuseStep 5431211 = 8146817) B8146817
theorem B11599787 : Blo 1609003 11599787 := bstep (se 1 (by rfl) ⟨8699840, by rfl⟩ : syracuseStep 11599787 = 17399681) B17399681
theorem B1810399 : Blo 1609003 1810399 := bstep (se 1 (by rfl) ⟨1357799, by rfl⟩ : syracuseStep 1810399 = 2715599) B2715599
theorem B15294521 : Blo 1609003 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B1933519 : Blo 1609003 1933519 := bstep (se 1 (by rfl) ⟨1450139, by rfl⟩ : syracuseStep 1933519 = 2900279) B2900279
theorem B3621113 : Blo 1609003 3621113 := bstep (se 2 (by rfl) ⟨1357917, by rfl⟩ : syracuseStep 3621113 = 2715835) B2715835
theorem B1810687 : Blo 1609003 1810687 := bstep (se 1 (by rfl) ⟨1358015, by rfl⟩ : syracuseStep 1810687 = 2716031) B2716031
theorem B14696743 : Blo 1609003 14696743 := bstep (se 1 (by rfl) ⟨11022557, by rfl⟩ : syracuseStep 14696743 = 22045115) B22045115
theorem B3621167 : Blo 1609003 3621167 := bstep (se 1 (by rfl) ⟨2715875, by rfl⟩ : syracuseStep 3621167 = 5431751) B5431751
theorem B8151353 : Blo 1609003 8151353 := bstep (se 2 (by rfl) ⟨3056757, by rfl⟩ : syracuseStep 8151353 = 6113515) B6113515
theorem B24797497 : Blo 1609003 24797497 := bstep (se 2 (by rfl) ⟨9299061, by rfl⟩ : syracuseStep 24797497 = 18598123) B18598123
theorem B3621383 : Blo 1609003 3621383 := bstep (se 1 (by rfl) ⟨2716037, by rfl⟩ : syracuseStep 3621383 = 5432075) B5432075
theorem B1810975 : Blo 1609003 1810975 := bstep (se 1 (by rfl) ⟨1358231, by rfl⟩ : syracuseStep 1810975 = 2716463) B2716463
theorem B5505641 : Blo 1609003 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B9069185 : Blo 1609003 9069185 := bstep (se 2 (by rfl) ⟨3400944, by rfl⟩ : syracuseStep 9069185 = 6801889) B6801889
theorem B2482855 : Blo 1609003 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B3621563 : Blo 1609003 3621563 := bstep (se 1 (by rfl) ⟨2716172, by rfl⟩ : syracuseStep 3621563 = 5432345) B5432345
theorem B3621995 : Blo 1609003 3621995 := bstep (se 1 (by rfl) ⟨2716496, by rfl⟩ : syracuseStep 3621995 = 5432993) B5432993
theorem B1811623 : Blo 1609003 1811623 := bstep (se 1 (by rfl) ⟨1358717, by rfl⟩ : syracuseStep 1811623 = 2717435) B2717435
theorem B2901215 : Blo 1609003 2901215 := bstep (se 1 (by rfl) ⟨2175911, by rfl⟩ : syracuseStep 2901215 = 4351823) B4351823
theorem B2901295 : Blo 1609003 2901295 := bstep (se 1 (by rfl) ⟨2175971, by rfl⟩ : syracuseStep 2901295 = 4351943) B4351943
theorem B3622463 : Blo 1609003 3622463 := bstep (se 1 (by rfl) ⟨2716847, by rfl⟩ : syracuseStep 3622463 = 5433695) B5433695
theorem B3622571 : Blo 1609003 3622571 := bstep (se 1 (by rfl) ⟨2716928, by rfl⟩ : syracuseStep 3622571 = 5433857) B5433857
theorem B7734959 : Blo 1609003 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B3057335 : Blo 1609003 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B8152811 : Blo 1609003 8152811 := bstep (se 1 (by rfl) ⟨6114608, by rfl⟩ : syracuseStep 8152811 = 12229217) B12229217
theorem B3057563 : Blo 1609003 3057563 := bstep (se 1 (by rfl) ⟨2293172, by rfl⟩ : syracuseStep 3057563 = 4586345) B4586345
theorem B3622895 : Blo 1609003 3622895 := bstep (se 1 (by rfl) ⟨2717171, by rfl⟩ : syracuseStep 3622895 = 5434343) B5434343
theorem B11601953 : Blo 1609003 11601953 := bstep (se 2 (by rfl) ⟨4350732, by rfl⟩ : syracuseStep 11601953 = 8701465) B8701465
theorem B3623111 : Blo 1609003 3623111 := bstep (se 1 (by rfl) ⟨2717333, by rfl⟩ : syracuseStep 3623111 = 5434667) B5434667
theorem B8153297 : Blo 1609003 8153297 := bstep (se 2 (by rfl) ⟨3057486, by rfl⟩ : syracuseStep 8153297 = 6114973) B6114973
theorem B3623291 : Blo 1609003 3623291 := bstep (se 1 (by rfl) ⟨2717468, by rfl⟩ : syracuseStep 3623291 = 5434937) B5434937
theorem B6113819 : Blo 1609003 6113819 := bstep (se 1 (by rfl) ⟨4585364, by rfl⟩ : syracuseStep 6113819 = 9170729) B9170729
theorem B3623561 : Blo 1609003 3623561 := bstep (se 2 (by rfl) ⟨1358835, by rfl⟩ : syracuseStep 3623561 = 2717671) B2717671
theorem B3869345 : Blo 1609003 3869345 := bstep (se 2 (by rfl) ⟨1451004, by rfl⟩ : syracuseStep 3869345 = 2902009) B2902009
theorem B13757323 : Blo 1609003 13757323 := bstep (se 1 (by rfl) ⟨10317992, by rfl⟩ : syracuseStep 13757323 = 20635985) B20635985
theorem B6876065 : Blo 1609003 6876065 := bstep (se 2 (by rfl) ⟨2578524, by rfl⟩ : syracuseStep 6876065 = 5157049) B5157049
theorem B3623849 : Blo 1609003 3623849 := bstep (se 2 (by rfl) ⟨1358943, by rfl⟩ : syracuseStep 3623849 = 2717887) B2717887
theorem B5155807 : Blo 1609003 5155807 := bstep (se 1 (by rfl) ⟨3866855, by rfl⟩ : syracuseStep 5155807 = 7733711) B7733711
theorem B10316969 : Blo 1609003 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B47721743 : Blo 1609003 47721743 := bstep (se 1 (by rfl) ⟨35791307, by rfl⟩ : syracuseStep 47721743 = 71582615) B71582615
theorem B6196591 : Blo 1609003 6196591 := bstep (se 1 (by rfl) ⟨4647443, by rfl⟩ : syracuseStep 6196591 = 9294887) B9294887
theorem B1609087 : Blo 1609003 1609087 := bstep (se 1 (by rfl) ⟨1206815, by rfl⟩ : syracuseStep 1609087 = 2413631) B2413631
theorem B1609115 : Blo 1609003 1609115 := bstep (se 1 (by rfl) ⟨1206836, by rfl⟩ : syracuseStep 1609115 = 2413673) B2413673
theorem B4074907 : Blo 1609003 4074907 := bstep (se 1 (by rfl) ⟨3056180, by rfl⟩ : syracuseStep 4074907 = 6112361) B6112361
theorem B1609183 : Blo 1609003 1609183 := bstep (se 1 (by rfl) ⟨1206887, by rfl⟩ : syracuseStep 1609183 = 2413775) B2413775
theorem B6524495 : Blo 1609003 6524495 := bstep (se 1 (by rfl) ⟨4893371, by rfl⟩ : syracuseStep 6524495 = 9786743) B9786743
theorem B3870287 : Blo 1609003 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B1609319 : Blo 1609003 1609319 := bstep (se 1 (by rfl) ⟨1206989, by rfl⟩ : syracuseStep 1609319 = 2413979) B2413979
theorem B3624551 : Blo 1609003 3624551 := bstep (se 1 (by rfl) ⟨2718413, by rfl⟩ : syracuseStep 3624551 = 5436827) B5436827
theorem B1609467 : Blo 1609003 1609467 := bstep (se 1 (by rfl) ⟨1207100, by rfl⟩ : syracuseStep 1609467 = 2414201) B2414201
theorem B1609535 : Blo 1609003 1609535 := bstep (se 1 (by rfl) ⟨1207151, by rfl⟩ : syracuseStep 1609535 = 2414303) B2414303
theorem B11161415 : Blo 1609003 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B1609599 : Blo 1609003 1609599 := bstep (se 1 (by rfl) ⟨1207199, by rfl⟩ : syracuseStep 1609599 = 2414399) B2414399
theorem B1609711 : Blo 1609003 1609711 := bstep (se 1 (by rfl) ⟨1207283, by rfl⟩ : syracuseStep 1609711 = 2414567) B2414567
theorem B1609723 : Blo 1609003 1609723 := bstep (se 1 (by rfl) ⟨1207292, by rfl⟩ : syracuseStep 1609723 = 2414585) B2414585
theorem B1609791 : Blo 1609003 1609791 := bstep (se 1 (by rfl) ⟨1207343, by rfl⟩ : syracuseStep 1609791 = 2414687) B2414687
theorem B1609831 : Blo 1609003 1609831 := bstep (se 1 (by rfl) ⟨1207373, by rfl⟩ : syracuseStep 1609831 = 2414747) B2414747
theorem B1609855 : Blo 1609003 1609855 := bstep (se 1 (by rfl) ⟨1207391, by rfl⟩ : syracuseStep 1609855 = 2414783) B2414783
theorem B5509255 : Blo 1609003 5509255 := bstep (se 1 (by rfl) ⟨4131941, by rfl⟩ : syracuseStep 5509255 = 8263883) B8263883
theorem B1609883 : Blo 1609003 1609883 := bstep (se 1 (by rfl) ⟨1207412, by rfl⟩ : syracuseStep 1609883 = 2414825) B2414825
theorem B26112233 : Blo 1609003 26112233 := bstep (se 2 (by rfl) ⟨9792087, by rfl⟩ : syracuseStep 26112233 = 19584175) B19584175
theorem B3485929 : Blo 1609003 3485929 := bstep (se 2 (by rfl) ⟨1307223, by rfl⟩ : syracuseStep 3485929 = 2614447) B2614447
theorem B1610087 : Blo 1609003 1610087 := bstep (se 1 (by rfl) ⟨1207565, by rfl⟩ : syracuseStep 1610087 = 2415131) B2415131
theorem B11604343 : Blo 1609003 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B1610139 : Blo 1609003 1610139 := bstep (se 1 (by rfl) ⟨1207604, by rfl⟩ : syracuseStep 1610139 = 2415209) B2415209
theorem B5435855 : Blo 1609003 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B1610491 : Blo 1609003 1610491 := bstep (se 1 (by rfl) ⟨1207868, by rfl⟩ : syracuseStep 1610491 = 2415737) B2415737
theorem B1610559 : Blo 1609003 1610559 := bstep (se 1 (by rfl) ⟨1207919, by rfl⟩ : syracuseStep 1610559 = 2415839) B2415839
theorem B1610587 : Blo 1609003 1610587 := bstep (se 1 (by rfl) ⟨1207940, by rfl⟩ : syracuseStep 1610587 = 2415881) B2415881
theorem B1610655 : Blo 1609003 1610655 := bstep (se 1 (by rfl) ⟨1207991, by rfl⟩ : syracuseStep 1610655 = 2415983) B2415983
theorem B1610735 : Blo 1609003 1610735 := bstep (se 1 (by rfl) ⟨1208051, by rfl⟩ : syracuseStep 1610735 = 2416103) B2416103
theorem B1610823 : Blo 1609003 1610823 := bstep (se 1 (by rfl) ⟨1208117, by rfl⟩ : syracuseStep 1610823 = 2416235) B2416235
theorem B1610907 : Blo 1609003 1610907 := bstep (se 1 (by rfl) ⟨1208180, by rfl⟩ : syracuseStep 1610907 = 2416361) B2416361
theorem B12227759 : Blo 1609003 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B1611003 : Blo 1609003 1611003 := bstep (se 1 (by rfl) ⟨1208252, by rfl⟩ : syracuseStep 1611003 = 2416505) B2416505
theorem B2413865 : Blo 1609003 2413865 := bstep (se 2 (by rfl) ⟨905199, by rfl⟩ : syracuseStep 2413865 = 1810399) B1810399
theorem B9172439 : Blo 1609003 9172439 := bstep (se 1 (by rfl) ⟨6879329, by rfl⟩ : syracuseStep 9172439 = 13758659) B13758659
theorem B2414063 : Blo 1609003 2414063 := bstep (se 1 (by rfl) ⟨1810547, by rfl⟩ : syracuseStep 2414063 = 3621095) B3621095
theorem B13760057 : Blo 1609003 13760057 := bstep (se 2 (by rfl) ⟨5160021, by rfl⟩ : syracuseStep 13760057 = 10320043) B10320043
theorem B30938759 : Blo 1609003 30938759 := bstep (se 1 (by rfl) ⟨23204069, by rfl⟩ : syracuseStep 30938759 = 46408139) B46408139
theorem B2717327 : Blo 1609003 2717327 := bstep (se 1 (by rfl) ⟨2037995, by rfl⟩ : syracuseStep 2717327 = 4075991) B4075991
theorem B2037403 : Blo 1609003 2037403 := bstep (se 1 (by rfl) ⟨1528052, by rfl⟩ : syracuseStep 2037403 = 3056105) B3056105
theorem B30930605 : Blo 1609003 30930605 := bstep (se 3 (by rfl) ⟨5799488, by rfl⟩ : syracuseStep 30930605 = 11598977) B11598977
theorem B2037575 : Blo 1609003 2037575 := bstep (se 1 (by rfl) ⟨1528181, by rfl⟩ : syracuseStep 2037575 = 3056363) B3056363
theorem B2414459 : Blo 1609003 2414459 := bstep (se 1 (by rfl) ⟨1810844, by rfl⟩ : syracuseStep 2414459 = 3621689) B3621689
theorem B5511035 : Blo 1609003 5511035 := bstep (se 1 (by rfl) ⟨4133276, by rfl⟩ : syracuseStep 5511035 = 8266553) B8266553
theorem B2414495 : Blo 1609003 2414495 := bstep (se 1 (by rfl) ⟨1810871, by rfl⟩ : syracuseStep 2414495 = 3621743) B3621743
theorem B9164897 : Blo 1609003 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B2414729 : Blo 1609003 2414729 := bstep (se 2 (by rfl) ⟨905523, by rfl⟩ : syracuseStep 2414729 = 1811047) B1811047
theorem B6109415 : Blo 1609003 6109415 := bstep (se 1 (by rfl) ⟨4582061, by rfl⟩ : syracuseStep 6109415 = 9164123) B9164123
theorem B4077803 : Blo 1609003 4077803 := bstep (se 1 (by rfl) ⟨3058352, by rfl⟩ : syracuseStep 4077803 = 6116705) B6116705
theorem B14883059 : Blo 1609003 14883059 := bstep (se 1 (by rfl) ⟨11162294, by rfl⟩ : syracuseStep 14883059 = 22324589) B22324589
theorem B2414879 : Blo 1609003 2414879 := bstep (se 1 (by rfl) ⟨1811159, by rfl⟩ : syracuseStep 2414879 = 3622319) B3622319
theorem B8706413 : Blo 1609003 8706413 := bstep (se 3 (by rfl) ⟨1632452, by rfl⟩ : syracuseStep 8706413 = 3264905) B3264905
theorem B2718299 : Blo 1609003 2718299 := bstep (se 1 (by rfl) ⟨2038724, by rfl⟩ : syracuseStep 2718299 = 4077449) B4077449
theorem B8264375 : Blo 1609003 8264375 := bstep (se 1 (by rfl) ⟨6198281, by rfl⟩ : syracuseStep 8264375 = 12396563) B12396563
theorem B19594007 : Blo 1609003 19594007 := bstep (se 1 (by rfl) ⟨14695505, by rfl⟩ : syracuseStep 19594007 = 29391011) B29391011
theorem B2415431 : Blo 1609003 2415431 := bstep (se 1 (by rfl) ⟨1811573, by rfl⟩ : syracuseStep 2415431 = 3623147) B3623147
theorem B13753223 : Blo 1609003 13753223 := bstep (se 1 (by rfl) ⟨10314917, by rfl⟩ : syracuseStep 13753223 = 20629835) B20629835
theorem B4586777 : Blo 1609003 4586777 := bstep (se 2 (by rfl) ⟨1720041, by rfl⟩ : syracuseStep 4586777 = 3440083) B3440083
theorem B8150381 : Blo 1609003 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B3620267 : Blo 1609003 3620267 := bstep (se 1 (by rfl) ⟨2715200, by rfl⟩ : syracuseStep 3620267 = 5430401) B5430401
theorem B3866039 : Blo 1609003 3866039 := bstep (se 1 (by rfl) ⟨2899529, by rfl⟩ : syracuseStep 3866039 = 5799059) B5799059
theorem B6618557 : Blo 1609003 6618557 := bstep (se 3 (by rfl) ⟨1240979, by rfl⟩ : syracuseStep 6618557 = 2481959) B2481959
theorem B3620303 : Blo 1609003 3620303 := bstep (se 1 (by rfl) ⟨2715227, by rfl⟩ : syracuseStep 3620303 = 5430455) B5430455
theorem B6970835 : Blo 1609003 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4586959 : Blo 1609003 4586959 := bstep (se 1 (by rfl) ⟨3440219, by rfl⟩ : syracuseStep 4586959 = 6880439) B6880439
theorem B12221927 : Blo 1609003 12221927 := bstep (se 1 (by rfl) ⟨9166445, by rfl⟩ : syracuseStep 12221927 = 18332891) B18332891
theorem B2416295 : Blo 1609003 2416295 := bstep (se 1 (by rfl) ⟨1812221, by rfl⟩ : syracuseStep 2416295 = 3624443) B3624443
theorem B2899687 : Blo 1609003 2899687 := bstep (se 1 (by rfl) ⟨2174765, by rfl⟩ : syracuseStep 2899687 = 4349531) B4349531
theorem B3055391 : Blo 1609003 3055391 := bstep (se 1 (by rfl) ⟨2291543, by rfl⟩ : syracuseStep 3055391 = 4583087) B4583087
theorem B2416415 : Blo 1609003 2416415 := bstep (se 1 (by rfl) ⟨1812311, by rfl⟩ : syracuseStep 2416415 = 3624623) B3624623
theorem B5799719 : Blo 1609003 5799719 := bstep (se 1 (by rfl) ⟨4349789, by rfl⟩ : syracuseStep 5799719 = 8699579) B8699579
theorem B3620807 : Blo 1609003 3620807 := bstep (se 1 (by rfl) ⟨2715605, by rfl⟩ : syracuseStep 3620807 = 5431211) B5431211
theorem B7733191 : Blo 1609003 7733191 := bstep (se 1 (by rfl) ⟨5799893, by rfl⟩ : syracuseStep 7733191 = 11599787) B11599787
theorem B17408155 : Blo 1609003 17408155 := bstep (se 1 (by rfl) ⟨13056116, by rfl⟩ : syracuseStep 17408155 = 26112233) B26112233
theorem B19595657 : Blo 1609003 19595657 := bstep (se 2 (by rfl) ⟨7348371, by rfl⟩ : syracuseStep 19595657 = 14696743) B14696743
theorem B3670427 : Blo 1609003 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B33063329 : Blo 1609003 33063329 := bstep (se 2 (by rfl) ⟨12398748, by rfl⟩ : syracuseStep 33063329 = 24797497) B24797497
theorem B6046123 : Blo 1609003 6046123 := bstep (se 1 (by rfl) ⟨4534592, by rfl⟩ : syracuseStep 6046123 = 9069185) B9069185
theorem B8151839 : Blo 1609003 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B23217101 : Blo 1609003 23217101 := bstep (se 3 (by rfl) ⟨4353206, by rfl⟩ : syracuseStep 23217101 = 8706413) B8706413
theorem B1811551 : Blo 1609003 1811551 := bstep (se 1 (by rfl) ⟨1358663, by rfl⟩ : syracuseStep 1811551 = 2717327) B2717327
theorem B20620403 : Blo 1609003 20620403 := bstep (se 1 (by rfl) ⟨15465302, by rfl⟩ : syracuseStep 20620403 = 30930605) B30930605
theorem B18343097 : Blo 1609003 18343097 := bstep (se 2 (by rfl) ⟨6878661, by rfl⟩ : syracuseStep 18343097 = 13757323) B13757323
theorem B6874409 : Blo 1609003 6874409 := bstep (se 2 (by rfl) ⟨2577903, by rfl⟩ : syracuseStep 6874409 = 5155807) B5155807
theorem B7734635 : Blo 1609003 7734635 := bstep (se 1 (by rfl) ⟨5800976, by rfl⟩ : syracuseStep 7734635 = 11601953) B11601953
theorem B4072943 : Blo 1609003 4072943 := bstep (se 1 (by rfl) ⟨3054707, by rfl⟩ : syracuseStep 4072943 = 6109415) B6109415
theorem B1812199 : Blo 1609003 1812199 := bstep (se 1 (by rfl) ⟨1359149, by rfl⟩ : syracuseStep 1812199 = 2718299) B2718299
theorem B3868393 : Blo 1609003 3868393 := bstep (se 2 (by rfl) ⟨1450647, by rfl⟩ : syracuseStep 3868393 = 2901295) B2901295
theorem B5433209 : Blo 1609003 5433209 := bstep (se 2 (by rfl) ⟨2037453, by rfl⟩ : syracuseStep 5433209 = 4074907) B4074907
theorem B9168815 : Blo 1609003 9168815 := bstep (se 1 (by rfl) ⟨6876611, by rfl⟩ : syracuseStep 9168815 = 13753223) B13753223
theorem B3057851 : Blo 1609003 3057851 := bstep (se 1 (by rfl) ⟨2293388, by rfl⟩ : syracuseStep 3057851 = 4586777) B4586777
theorem B29763773 : Blo 1609003 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B5433533 : Blo 1609003 5433533 := bstep (se 3 (by rfl) ⟨1018787, by rfl⟩ : syracuseStep 5433533 = 2037575) B2037575
theorem B5433587 : Blo 1609003 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B4647223 : Blo 1609003 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B5434235 : Blo 1609003 5434235 := bstep (se 1 (by rfl) ⟨4075676, by rfl⟩ : syracuseStep 5434235 = 8151353) B8151353
theorem B4647905 : Blo 1609003 4647905 := bstep (se 2 (by rfl) ⟨1742964, by rfl⟩ : syracuseStep 4647905 = 3485929) B3485929
theorem B3623903 : Blo 1609003 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B7736573 : Blo 1609003 7736573 := bstep (se 3 (by rfl) ⟨1450607, by rfl⟩ : syracuseStep 7736573 = 2901215) B2901215
theorem B1609243 : Blo 1609003 1609243 := bstep (se 1 (by rfl) ⟨1206932, by rfl⟩ : syracuseStep 1609243 = 2413865) B2413865
theorem B13241893 : Blo 1609003 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B6114959 : Blo 1609003 6114959 := bstep (se 1 (by rfl) ⟨4586219, by rfl⟩ : syracuseStep 6114959 = 9172439) B9172439
theorem B1609375 : Blo 1609003 1609375 := bstep (se 1 (by rfl) ⟨1207031, by rfl⟩ : syracuseStep 1609375 = 2414063) B2414063
theorem B5156639 : Blo 1609003 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B5435207 : Blo 1609003 5435207 := bstep (se 1 (by rfl) ⟨4076405, by rfl⟩ : syracuseStep 5435207 = 8152811) B8152811
theorem B17649485 : Blo 1609003 17649485 := bstep (se 3 (by rfl) ⟨3309278, by rfl⟩ : syracuseStep 17649485 = 6618557) B6618557
theorem B1609639 : Blo 1609003 1609639 := bstep (se 1 (by rfl) ⟨1207229, by rfl⟩ : syracuseStep 1609639 = 2414459) B2414459
theorem B1609663 : Blo 1609003 1609663 := bstep (se 1 (by rfl) ⟨1207247, by rfl⟩ : syracuseStep 1609663 = 2414495) B2414495
theorem B1609819 : Blo 1609003 1609819 := bstep (se 1 (by rfl) ⟨1207364, by rfl⟩ : syracuseStep 1609819 = 2414729) B2414729
theorem B5435531 : Blo 1609003 5435531 := bstep (se 1 (by rfl) ⟨4076648, by rfl⟩ : syracuseStep 5435531 = 8153297) B8153297
theorem B1609919 : Blo 1609003 1609919 := bstep (se 1 (by rfl) ⟨1207439, by rfl⟩ : syracuseStep 1609919 = 2414879) B2414879
theorem B4075879 : Blo 1609003 4075879 := bstep (se 1 (by rfl) ⟨3056909, by rfl⟩ : syracuseStep 4075879 = 6113819) B6113819
theorem B5509583 : Blo 1609003 5509583 := bstep (se 1 (by rfl) ⟨4132187, by rfl⟩ : syracuseStep 5509583 = 8264375) B8264375
theorem B8262121 : Blo 1609003 8262121 := bstep (se 2 (by rfl) ⟨3098295, by rfl⟩ : syracuseStep 8262121 = 6196591) B6196591
theorem B13062671 : Blo 1609003 13062671 := bstep (se 1 (by rfl) ⟨9797003, by rfl⟩ : syracuseStep 13062671 = 19594007) B19594007
theorem B1610287 : Blo 1609003 1610287 := bstep (se 1 (by rfl) ⟨1207715, by rfl⟩ : syracuseStep 1610287 = 2415431) B2415431
theorem B6115945 : Blo 1609003 6115945 := bstep (se 2 (by rfl) ⟨2293479, by rfl⟩ : syracuseStep 6115945 = 4586959) B4586959
theorem B4584043 : Blo 1609003 4584043 := bstep (se 1 (by rfl) ⟨3438032, by rfl⟩ : syracuseStep 4584043 = 6876065) B6876065
theorem B6877979 : Blo 1609003 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B31814495 : Blo 1609003 31814495 := bstep (se 1 (by rfl) ⟨23860871, by rfl⟩ : syracuseStep 31814495 = 47721743) B47721743
theorem B2716537 : Blo 1609003 2716537 := bstep (se 2 (by rfl) ⟨1018701, by rfl⟩ : syracuseStep 2716537 = 2037403) B2037403
theorem B2413511 : Blo 1609003 2413511 := bstep (se 1 (by rfl) ⟨1810133, by rfl⟩ : syracuseStep 2413511 = 3620267) B3620267
theorem B2577359 : Blo 1609003 2577359 := bstep (se 1 (by rfl) ⟨1933019, by rfl⟩ : syracuseStep 2577359 = 3866039) B3866039
theorem B2413535 : Blo 1609003 2413535 := bstep (se 1 (by rfl) ⟨1810151, by rfl⟩ : syracuseStep 2413535 = 3620303) B3620303
theorem B8147951 : Blo 1609003 8147951 := bstep (se 1 (by rfl) ⟨6110963, by rfl⟩ : syracuseStep 8147951 = 12221927) B12221927
theorem B1610863 : Blo 1609003 1610863 := bstep (se 1 (by rfl) ⟨1208147, by rfl⟩ : syracuseStep 1610863 = 2416295) B2416295
theorem B2036927 : Blo 1609003 2036927 := bstep (se 1 (by rfl) ⟨1527695, by rfl⟩ : syracuseStep 2036927 = 3055391) B3055391
theorem B1610943 : Blo 1609003 1610943 := bstep (se 1 (by rfl) ⟨1208207, by rfl⟩ : syracuseStep 1610943 = 2416415) B2416415
theorem B10310921 : Blo 1609003 10310921 := bstep (se 2 (by rfl) ⟨3866595, by rfl⟩ : syracuseStep 10310921 = 7733191) B7733191
theorem B2413871 : Blo 1609003 2413871 := bstep (se 1 (by rfl) ⟨1810403, by rfl⟩ : syracuseStep 2413871 = 3620807) B3620807
theorem B10196347 : Blo 1609003 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B2414075 : Blo 1609003 2414075 := bstep (se 1 (by rfl) ⟨1810556, by rfl⟩ : syracuseStep 2414075 = 3621113) B3621113
theorem B7345673 : Blo 1609003 7345673 := bstep (se 2 (by rfl) ⟨2754627, by rfl⟩ : syracuseStep 7345673 = 5509255) B5509255
theorem B2414111 : Blo 1609003 2414111 := bstep (se 1 (by rfl) ⟨1810583, by rfl⟩ : syracuseStep 2414111 = 3621167) B3621167
theorem B2578025 : Blo 1609003 2578025 := bstep (se 2 (by rfl) ⟨966759, by rfl⟩ : syracuseStep 2578025 = 1933519) B1933519
theorem B2414249 : Blo 1609003 2414249 := bstep (se 2 (by rfl) ⟨905343, by rfl⟩ : syracuseStep 2414249 = 1810687) B1810687
theorem B2414255 : Blo 1609003 2414255 := bstep (se 1 (by rfl) ⟨1810691, by rfl⟩ : syracuseStep 2414255 = 3621383) B3621383
theorem B2414375 : Blo 1609003 2414375 := bstep (se 1 (by rfl) ⟨1810781, by rfl⟩ : syracuseStep 2414375 = 3621563) B3621563
theorem B15472457 : Blo 1609003 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B39688157 : Blo 1609003 39688157 := bstep (se 3 (by rfl) ⟨7441529, by rfl⟩ : syracuseStep 39688157 = 14883059) B14883059
theorem B2414633 : Blo 1609003 2414633 := bstep (se 2 (by rfl) ⟨905487, by rfl⟩ : syracuseStep 2414633 = 1810975) B1810975
theorem B2414663 : Blo 1609003 2414663 := bstep (se 1 (by rfl) ⟨1810997, by rfl⟩ : syracuseStep 2414663 = 3621995) B3621995
theorem B9173371 : Blo 1609003 9173371 := bstep (se 1 (by rfl) ⟨6880028, by rfl⟩ : syracuseStep 9173371 = 13760057) B13760057
theorem B2414975 : Blo 1609003 2414975 := bstep (se 1 (by rfl) ⟨1811231, by rfl⟩ : syracuseStep 2414975 = 3622463) B3622463
theorem B20625839 : Blo 1609003 20625839 := bstep (se 1 (by rfl) ⟨15469379, by rfl⟩ : syracuseStep 20625839 = 30938759) B30938759
theorem B2415047 : Blo 1609003 2415047 := bstep (se 1 (by rfl) ⟨1811285, by rfl⟩ : syracuseStep 2415047 = 3622571) B3622571
theorem B2038223 : Blo 1609003 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B2038375 : Blo 1609003 2038375 := bstep (se 1 (by rfl) ⟨1528781, by rfl⟩ : syracuseStep 2038375 = 3057563) B3057563
theorem B2415263 : Blo 1609003 2415263 := bstep (se 1 (by rfl) ⟨1811447, by rfl⟩ : syracuseStep 2415263 = 3622895) B3622895
theorem B6109931 : Blo 1609003 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B2415407 : Blo 1609003 2415407 := bstep (se 1 (by rfl) ⟨1811555, by rfl⟩ : syracuseStep 2415407 = 3623111) B3623111
theorem B2718535 : Blo 1609003 2718535 := bstep (se 1 (by rfl) ⟨2038901, by rfl⟩ : syracuseStep 2718535 = 4077803) B4077803
theorem B2415497 : Blo 1609003 2415497 := bstep (se 2 (by rfl) ⟨905811, by rfl⟩ : syracuseStep 2415497 = 1811623) B1811623
theorem B2415527 : Blo 1609003 2415527 := bstep (se 1 (by rfl) ⟨1811645, by rfl⟩ : syracuseStep 2415527 = 3623291) B3623291
theorem B2415707 : Blo 1609003 2415707 := bstep (se 1 (by rfl) ⟨1811780, by rfl⟩ : syracuseStep 2415707 = 3623561) B3623561
theorem B2579563 : Blo 1609003 2579563 := bstep (se 1 (by rfl) ⟨1934672, by rfl⟩ : syracuseStep 2579563 = 3869345) B3869345
theorem B2415899 : Blo 1609003 2415899 := bstep (se 1 (by rfl) ⟨1811924, by rfl⟩ : syracuseStep 2415899 = 3623849) B3623849
theorem B15465917 : Blo 1609003 15465917 := bstep (se 3 (by rfl) ⟨2899859, by rfl⟩ : syracuseStep 15465917 = 5799719) B5799719
theorem B3866249 : Blo 1609003 3866249 := bstep (se 2 (by rfl) ⟨1449843, by rfl⟩ : syracuseStep 3866249 = 2899687) B2899687
theorem B14696093 : Blo 1609003 14696093 := bstep (se 3 (by rfl) ⟨2755517, by rfl⟩ : syracuseStep 14696093 = 5511035) B5511035
theorem B4349663 : Blo 1609003 4349663 := bstep (se 1 (by rfl) ⟨3262247, by rfl⟩ : syracuseStep 4349663 = 6524495) B6524495
theorem B2580191 : Blo 1609003 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B2416367 : Blo 1609003 2416367 := bstep (se 1 (by rfl) ⟨1812275, by rfl⟩ : syracuseStep 2416367 = 3624551) B3624551
theorem B8708447 : Blo 1609003 8708447 := bstep (se 1 (by rfl) ⟨6531335, by rfl⟩ : syracuseStep 8708447 = 13062671) B13062671
theorem B12231161 : Blo 1609003 12231161 := bstep (se 2 (by rfl) ⟨4586685, by rfl⟩ : syracuseStep 12231161 = 9173371) B9173371
theorem B5431805 : Blo 1609003 5431805 := bstep (se 3 (by rfl) ⟨1018463, by rfl⟩ : syracuseStep 5431805 = 2036927) B2036927
theorem B8061497 : Blo 1609003 8061497 := bstep (se 2 (by rfl) ⟨3023061, by rfl⟩ : syracuseStep 8061497 = 6046123) B6046123
theorem B21209663 : Blo 1609003 21209663 := bstep (se 1 (by rfl) ⟨15907247, by rfl⟩ : syracuseStep 21209663 = 31814495) B31814495
theorem B5431967 : Blo 1609003 5431967 := bstep (se 1 (by rfl) ⟨4073975, by rfl⟩ : syracuseStep 5431967 = 8147951) B8147951
theorem B13746935 : Blo 1609003 13746935 := bstep (se 1 (by rfl) ⟨10310201, by rfl⟩ : syracuseStep 13746935 = 20620403) B20620403
theorem B6112057 : Blo 1609003 6112057 := bstep (se 2 (by rfl) ⟨2292021, by rfl⟩ : syracuseStep 6112057 = 4584043) B4584043
theorem B6873947 : Blo 1609003 6873947 := bstep (se 1 (by rfl) ⟨5155460, by rfl⟩ : syracuseStep 6873947 = 10310921) B10310921
theorem B3622049 : Blo 1609003 3622049 := bstep (se 2 (by rfl) ⟨1358268, by rfl⟩ : syracuseStep 3622049 = 2716537) B2716537
theorem B10314971 : Blo 1609003 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B3622139 : Blo 1609003 3622139 := bstep (se 1 (by rfl) ⟨2716604, by rfl⟩ : syracuseStep 3622139 = 5433209) B5433209
theorem B6112543 : Blo 1609003 6112543 := bstep (se 1 (by rfl) ⟨4584407, by rfl⟩ : syracuseStep 6112543 = 9168815) B9168815
theorem B19842515 : Blo 1609003 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B3622355 : Blo 1609003 3622355 := bstep (se 1 (by rfl) ⟨2716766, by rfl⟩ : syracuseStep 3622355 = 5433533) B5433533
theorem B3622391 : Blo 1609003 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B6874733 : Blo 1609003 6874733 := bstep (se 3 (by rfl) ⟨1289012, by rfl⟩ : syracuseStep 6874733 = 2578025) B2578025
theorem B4073287 : Blo 1609003 4073287 := bstep (se 1 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 4073287 = 6109931) B6109931
theorem B3622823 : Blo 1609003 3622823 := bstep (se 1 (by rfl) ⟨2717117, by rfl⟩ : syracuseStep 3622823 = 5434235) B5434235
theorem B3098603 : Blo 1609003 3098603 := bstep (se 1 (by rfl) ⟨2323952, by rfl⟩ : syracuseStep 3098603 = 4647905) B4647905
theorem B17655857 : Blo 1609003 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B3623471 : Blo 1609003 3623471 := bstep (se 1 (by rfl) ⟨2717603, by rfl⟩ : syracuseStep 3623471 = 5435207) B5435207
theorem B11766323 : Blo 1609003 11766323 := bstep (se 1 (by rfl) ⟨8824742, by rfl⟩ : syracuseStep 11766323 = 17649485) B17649485
theorem B3623687 : Blo 1609003 3623687 := bstep (se 1 (by rfl) ⟨2717765, by rfl⟩ : syracuseStep 3623687 = 5435531) B5435531
theorem B23210873 : Blo 1609003 23210873 := bstep (se 2 (by rfl) ⟨8704077, by rfl⟩ : syracuseStep 23210873 = 17408155) B17408155
theorem B3673055 : Blo 1609003 3673055 := bstep (se 1 (by rfl) ⟨2754791, by rfl⟩ : syracuseStep 3673055 = 5509583) B5509583
theorem B5434505 : Blo 1609003 5434505 := bstep (se 2 (by rfl) ⟨2037939, by rfl⟩ : syracuseStep 5434505 = 4075879) B4075879
theorem B8154269 : Blo 1609003 8154269 := bstep (se 3 (by rfl) ⟨1528925, by rfl⟩ : syracuseStep 8154269 = 3057851) B3057851
theorem B5434559 : Blo 1609003 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B1609007 : Blo 1609003 1609007 := bstep (se 1 (by rfl) ⟨1206755, by rfl⟩ : syracuseStep 1609007 = 2413511) B2413511
theorem B15478067 : Blo 1609003 15478067 := bstep (se 1 (by rfl) ⟨11608550, by rfl⟩ : syracuseStep 15478067 = 23217101) B23217101
theorem B1609023 : Blo 1609003 1609023 := bstep (se 1 (by rfl) ⟨1206767, by rfl⟩ : syracuseStep 1609023 = 2413535) B2413535
theorem B20630861 : Blo 1609003 20630861 := bstep (se 3 (by rfl) ⟨3868286, by rfl⟩ : syracuseStep 20630861 = 7736573) B7736573
theorem B8154593 : Blo 1609003 8154593 := bstep (se 2 (by rfl) ⟨3057972, by rfl⟩ : syracuseStep 8154593 = 6115945) B6115945
theorem B4582939 : Blo 1609003 4582939 := bstep (se 1 (by rfl) ⟨3437204, by rfl⟩ : syracuseStep 4582939 = 6874409) B6874409
theorem B1609247 : Blo 1609003 1609247 := bstep (se 1 (by rfl) ⟨1206935, by rfl⟩ : syracuseStep 1609247 = 2413871) B2413871
theorem B5156423 : Blo 1609003 5156423 := bstep (se 1 (by rfl) ⟨3867317, by rfl⟩ : syracuseStep 5156423 = 7734635) B7734635
theorem B2715295 : Blo 1609003 2715295 := bstep (se 1 (by rfl) ⟨2036471, by rfl⟩ : syracuseStep 2715295 = 4072943) B4072943
theorem B1609383 : Blo 1609003 1609383 := bstep (se 1 (by rfl) ⟨1207037, by rfl⟩ : syracuseStep 1609383 = 2414075) B2414075
theorem B1609407 : Blo 1609003 1609407 := bstep (se 1 (by rfl) ⟨1207055, by rfl⟩ : syracuseStep 1609407 = 2414111) B2414111
theorem B3624713 : Blo 1609003 3624713 := bstep (se 2 (by rfl) ⟨1359267, by rfl⟩ : syracuseStep 3624713 = 2718535) B2718535
theorem B1609499 : Blo 1609003 1609499 := bstep (se 1 (by rfl) ⟨1207124, by rfl⟩ : syracuseStep 1609499 = 2414249) B2414249
theorem B1609503 : Blo 1609003 1609503 := bstep (se 1 (by rfl) ⟨1207127, by rfl⟩ : syracuseStep 1609503 = 2414255) B2414255
theorem B41242445 : Blo 1609003 41242445 := bstep (se 3 (by rfl) ⟨7732958, by rfl⟩ : syracuseStep 41242445 = 15465917) B15465917
theorem B1609583 : Blo 1609003 1609583 := bstep (se 1 (by rfl) ⟨1207187, by rfl⟩ : syracuseStep 1609583 = 2414375) B2414375
theorem B5435261 : Blo 1609003 5435261 := bstep (se 3 (by rfl) ⟨1019111, by rfl⟩ : syracuseStep 5435261 = 2038223) B2038223
theorem B1609755 : Blo 1609003 1609755 := bstep (se 1 (by rfl) ⟨1207316, by rfl⟩ : syracuseStep 1609755 = 2414633) B2414633
theorem B1609775 : Blo 1609003 1609775 := bstep (se 1 (by rfl) ⟨1207331, by rfl⟩ : syracuseStep 1609775 = 2414663) B2414663
theorem B1609983 : Blo 1609003 1609983 := bstep (se 1 (by rfl) ⟨1207487, by rfl⟩ : syracuseStep 1609983 = 2414975) B2414975
theorem B13750559 : Blo 1609003 13750559 := bstep (se 1 (by rfl) ⟨10312919, by rfl⟩ : syracuseStep 13750559 = 20625839) B20625839
theorem B24785189 : Blo 1609003 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B1610031 : Blo 1609003 1610031 := bstep (se 1 (by rfl) ⟨1207523, by rfl⟩ : syracuseStep 1610031 = 2415047) B2415047
theorem B10309997 : Blo 1609003 10309997 := bstep (se 3 (by rfl) ⟨1933124, by rfl⟩ : syracuseStep 10309997 = 3866249) B3866249
theorem B1610175 : Blo 1609003 1610175 := bstep (se 1 (by rfl) ⟨1207631, by rfl⟩ : syracuseStep 1610175 = 2415263) B2415263
theorem B13595129 : Blo 1609003 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B1610271 : Blo 1609003 1610271 := bstep (se 1 (by rfl) ⟨1207703, by rfl⟩ : syracuseStep 1610271 = 2415407) B2415407
theorem B1610331 : Blo 1609003 1610331 := bstep (se 1 (by rfl) ⟨1207748, by rfl⟩ : syracuseStep 1610331 = 2415497) B2415497
theorem B1610351 : Blo 1609003 1610351 := bstep (se 1 (by rfl) ⟨1207763, by rfl⟩ : syracuseStep 1610351 = 2415527) B2415527
theorem B1610471 : Blo 1609003 1610471 := bstep (se 1 (by rfl) ⟨1207853, by rfl⟩ : syracuseStep 1610471 = 2415707) B2415707
theorem B1610599 : Blo 1609003 1610599 := bstep (se 1 (by rfl) ⟨1207949, by rfl⟩ : syracuseStep 1610599 = 2415899) B2415899
theorem B5157857 : Blo 1609003 5157857 := bstep (se 2 (by rfl) ⟨1934196, by rfl⟩ : syracuseStep 5157857 = 3868393) B3868393
theorem B4076639 : Blo 1609003 4076639 := bstep (se 1 (by rfl) ⟨3057479, by rfl⟩ : syracuseStep 4076639 = 6114959) B6114959
theorem B1610911 : Blo 1609003 1610911 := bstep (se 1 (by rfl) ⟨1208183, by rfl⟩ : syracuseStep 1610911 = 2416367) B2416367
theorem B3437759 : Blo 1609003 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B13063771 : Blo 1609003 13063771 := bstep (se 1 (by rfl) ⟨9797828, by rfl⟩ : syracuseStep 13063771 = 19595657) B19595657
theorem B22042219 : Blo 1609003 22042219 := bstep (se 1 (by rfl) ⟨16531664, by rfl⟩ : syracuseStep 22042219 = 33063329) B33063329
theorem B4585319 : Blo 1609003 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B11016161 : Blo 1609003 11016161 := bstep (se 2 (by rfl) ⟨4131060, by rfl⟩ : syracuseStep 11016161 = 8262121) B8262121
theorem B12228731 : Blo 1609003 12228731 := bstep (se 1 (by rfl) ⟨9171548, by rfl⟩ : syracuseStep 12228731 = 18343097) B18343097
theorem B2717833 : Blo 1609003 2717833 := bstep (se 2 (by rfl) ⟨1019187, by rfl⟩ : syracuseStep 2717833 = 2038375) B2038375
theorem B4897115 : Blo 1609003 4897115 := bstep (se 1 (by rfl) ⟨3672836, by rfl⟩ : syracuseStep 4897115 = 7345673) B7345673
theorem B9787805 : Blo 1609003 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B26458771 : Blo 1609003 26458771 := bstep (se 1 (by rfl) ⟨19844078, by rfl⟩ : syracuseStep 26458771 = 39688157) B39688157
theorem B2415401 : Blo 1609003 2415401 := bstep (se 2 (by rfl) ⟨905775, by rfl⟩ : syracuseStep 2415401 = 1811551) B1811551
theorem B3439417 : Blo 1609003 3439417 := bstep (se 2 (by rfl) ⟨1289781, by rfl⟩ : syracuseStep 3439417 = 2579563) B2579563
theorem B2415935 : Blo 1609003 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B2416265 : Blo 1609003 2416265 := bstep (se 2 (by rfl) ⟨906099, by rfl⟩ : syracuseStep 2416265 = 1812199) B1812199
theorem B9797395 : Blo 1609003 9797395 := bstep (se 1 (by rfl) ⟨7348046, by rfl⟩ : syracuseStep 9797395 = 14696093) B14696093
theorem B2899775 : Blo 1609003 2899775 := bstep (se 1 (by rfl) ⟨2174831, by rfl⟩ : syracuseStep 2899775 = 4349663) B4349663
theorem B1720127 : Blo 1609003 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B6872957 : Blo 1609003 6872957 := bstep (se 3 (by rfl) ⟨1288679, by rfl⟩ : syracuseStep 6872957 = 2577359) B2577359
theorem B9167039 : Blo 1609003 9167039 := bstep (se 1 (by rfl) ⟨6875279, by rfl⟩ : syracuseStep 9167039 = 13750559) B13750559
theorem B16523459 : Blo 1609003 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B6873331 : Blo 1609003 6873331 := bstep (se 1 (by rfl) ⟨5154998, by rfl⟩ : syracuseStep 6873331 = 10309997) B10309997
theorem B3621203 : Blo 1609003 3621203 := bstep (se 1 (by rfl) ⟨2715902, by rfl⟩ : syracuseStep 3621203 = 5431805) B5431805
theorem B5374331 : Blo 1609003 5374331 := bstep (se 1 (by rfl) ⟨4030748, by rfl⟩ : syracuseStep 5374331 = 8061497) B8061497
theorem B14139775 : Blo 1609003 14139775 := bstep (se 1 (by rfl) ⟨10604831, by rfl⟩ : syracuseStep 14139775 = 21209663) B21209663
theorem B3621311 : Blo 1609003 3621311 := bstep (se 1 (by rfl) ⟨2715983, by rfl⟩ : syracuseStep 3621311 = 5431967) B5431967
theorem B69673445 : Blo 1609003 69673445 := bstep (se 4 (by rfl) ⟨6531885, by rfl⟩ : syracuseStep 69673445 = 13063771) B13063771
theorem B9167357 : Blo 1609003 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B3056879 : Blo 1609003 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B2065735 : Blo 1609003 2065735 := bstep (se 1 (by rfl) ⟨1549301, by rfl⟩ : syracuseStep 2065735 = 3098603) B3098603
theorem B8152487 : Blo 1609003 8152487 := bstep (se 1 (by rfl) ⟨6114365, by rfl⟩ : syracuseStep 8152487 = 12228731) B12228731
theorem B3623003 : Blo 1609003 3623003 := bstep (se 1 (by rfl) ⟨2717252, by rfl⟩ : syracuseStep 3623003 = 5434505) B5434505
theorem B3623039 : Blo 1609003 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B27494963 : Blo 1609003 27494963 := bstep (se 1 (by rfl) ⟨20621222, by rfl⟩ : syracuseStep 27494963 = 41242445) B41242445
theorem B4581971 : Blo 1609003 4581971 := bstep (se 1 (by rfl) ⟨3436478, by rfl⟩ : syracuseStep 4581971 = 6872957) B6872957
theorem B3623507 : Blo 1609003 3623507 := bstep (se 1 (by rfl) ⟨2717630, by rfl⟩ : syracuseStep 3623507 = 5435261) B5435261
theorem B3623777 : Blo 1609003 3623777 := bstep (se 2 (by rfl) ⟨1358916, by rfl⟩ : syracuseStep 3623777 = 2717833) B2717833
theorem B9063419 : Blo 1609003 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B8154107 : Blo 1609003 8154107 := bstep (se 1 (by rfl) ⟨6115580, by rfl⟩ : syracuseStep 8154107 = 12231161) B12231161
theorem B4582631 : Blo 1609003 4582631 := bstep (se 1 (by rfl) ⟨3436973, by rfl⟩ : syracuseStep 4582631 = 6873947) B6873947
theorem B6876647 : Blo 1609003 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B35278361 : Blo 1609003 35278361 := bstep (se 2 (by rfl) ⟨13229385, by rfl⟩ : syracuseStep 35278361 = 26458771) B26458771
theorem B4583155 : Blo 1609003 4583155 := bstep (se 1 (by rfl) ⟨3437366, by rfl⟩ : syracuseStep 4583155 = 6874733) B6874733
theorem B7344107 : Blo 1609003 7344107 := bstep (se 1 (by rfl) ⟨5508080, by rfl⟩ : syracuseStep 7344107 = 11016161) B11016161
theorem B3264743 : Blo 1609003 3264743 := bstep (se 1 (by rfl) ⟨2448557, by rfl⟩ : syracuseStep 3264743 = 4897115) B4897115
theorem B6525203 : Blo 1609003 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B7844215 : Blo 1609003 7844215 := bstep (se 1 (by rfl) ⟨5883161, by rfl⟩ : syracuseStep 7844215 = 11766323) B11766323
theorem B1610267 : Blo 1609003 1610267 := bstep (se 1 (by rfl) ⟨1207700, by rfl⟩ : syracuseStep 1610267 = 2415401) B2415401
theorem B5436179 : Blo 1609003 5436179 := bstep (se 1 (by rfl) ⟨4077134, by rfl⟩ : syracuseStep 5436179 = 8154269) B8154269
theorem B29389625 : Blo 1609003 29389625 := bstep (se 2 (by rfl) ⟨11021109, by rfl⟩ : syracuseStep 29389625 = 22042219) B22042219
theorem B10318711 : Blo 1609003 10318711 := bstep (se 1 (by rfl) ⟨7739033, by rfl⟩ : syracuseStep 10318711 = 15478067) B15478067
theorem B1610623 : Blo 1609003 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B5436395 : Blo 1609003 5436395 := bstep (se 1 (by rfl) ⟨4077296, by rfl⟩ : syracuseStep 5436395 = 8154593) B8154593
theorem B13063193 : Blo 1609003 13063193 := bstep (se 2 (by rfl) ⟨4898697, by rfl⟩ : syracuseStep 13063193 = 9797395) B9797395
theorem B3437615 : Blo 1609003 3437615 := bstep (se 1 (by rfl) ⟨2578211, by rfl⟩ : syracuseStep 3437615 = 5156423) B5156423
theorem B1610843 : Blo 1609003 1610843 := bstep (se 1 (by rfl) ⟨1208132, by rfl⟩ : syracuseStep 1610843 = 2416265) B2416265
theorem B5805631 : Blo 1609003 5805631 := bstep (se 1 (by rfl) ⟨4354223, by rfl⟩ : syracuseStep 5805631 = 8708447) B8708447
theorem B9164623 : Blo 1609003 9164623 := bstep (se 1 (by rfl) ⟨6873467, by rfl⟩ : syracuseStep 9164623 = 13746935) B13746935
theorem B2717759 : Blo 1609003 2717759 := bstep (se 1 (by rfl) ⟨2038319, by rfl⟩ : syracuseStep 2717759 = 4076639) B4076639
theorem B2414699 : Blo 1609003 2414699 := bstep (se 1 (by rfl) ⟨1811024, by rfl⟩ : syracuseStep 2414699 = 3622049) B3622049
theorem B2414759 : Blo 1609003 2414759 := bstep (se 1 (by rfl) ⟨1811069, by rfl⟩ : syracuseStep 2414759 = 3622139) B3622139
theorem B13228343 : Blo 1609003 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B2414903 : Blo 1609003 2414903 := bstep (se 1 (by rfl) ⟨1811177, by rfl⟩ : syracuseStep 2414903 = 3622355) B3622355
theorem B2414927 : Blo 1609003 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B8149409 : Blo 1609003 8149409 := bstep (se 2 (by rfl) ⟨3056028, by rfl⟩ : syracuseStep 8149409 = 6112057) B6112057
theorem B4585889 : Blo 1609003 4585889 := bstep (se 2 (by rfl) ⟨1719708, by rfl⟩ : syracuseStep 4585889 = 3439417) B3439417
theorem B2415215 : Blo 1609003 2415215 := bstep (se 1 (by rfl) ⟨1811411, by rfl⟩ : syracuseStep 2415215 = 3622823) B3622823
theorem B11770571 : Blo 1609003 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B2415647 : Blo 1609003 2415647 := bstep (se 1 (by rfl) ⟨1811735, by rfl⟩ : syracuseStep 2415647 = 3623471) B3623471
theorem B8150057 : Blo 1609003 8150057 := bstep (se 2 (by rfl) ⟨3056271, by rfl⟩ : syracuseStep 8150057 = 6112543) B6112543
theorem B2415791 : Blo 1609003 2415791 := bstep (se 1 (by rfl) ⟨1811843, by rfl⟩ : syracuseStep 2415791 = 3623687) B3623687
theorem B15473915 : Blo 1609003 15473915 := bstep (se 1 (by rfl) ⟨11605436, by rfl⟩ : syracuseStep 15473915 = 23210873) B23210873
theorem B2448703 : Blo 1609003 2448703 := bstep (se 1 (by rfl) ⟨1836527, by rfl⟩ : syracuseStep 2448703 = 3673055) B3673055
theorem B6110585 : Blo 1609003 6110585 := bstep (se 2 (by rfl) ⟨2291469, by rfl⟩ : syracuseStep 6110585 = 4582939) B4582939
theorem B4587005 : Blo 1609003 4587005 := bstep (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) B1720127
theorem B3620393 : Blo 1609003 3620393 := bstep (se 2 (by rfl) ⟨1357647, by rfl⟩ : syracuseStep 3620393 = 2715295) B2715295
theorem B13753907 : Blo 1609003 13753907 := bstep (se 1 (by rfl) ⟨10315430, by rfl⟩ : syracuseStep 13753907 = 20630861) B20630861
theorem B5431049 : Blo 1609003 5431049 := bstep (se 2 (by rfl) ⟨2036643, by rfl⟩ : syracuseStep 5431049 = 4073287) B4073287
theorem B2416475 : Blo 1609003 2416475 := bstep (se 1 (by rfl) ⟨1812356, by rfl⟩ : syracuseStep 2416475 = 3624713) B3624713
theorem B1933183 : Blo 1609003 1933183 := bstep (se 1 (by rfl) ⟨1449887, by rfl⟩ : syracuseStep 1933183 = 2899775) B2899775
theorem B13754285 : Blo 1609003 13754285 := bstep (se 3 (by rfl) ⟨2578928, by rfl⟩ : syracuseStep 13754285 = 5157857) B5157857
theorem B6111359 : Blo 1609003 6111359 := bstep (se 1 (by rfl) ⟨4583519, by rfl⟩ : syracuseStep 6111359 = 9167039) B9167039
theorem B46448963 : Blo 1609003 46448963 := bstep (se 1 (by rfl) ⟨34836722, by rfl⟩ : syracuseStep 46448963 = 69673445) B69673445
theorem B6111571 : Blo 1609003 6111571 := bstep (se 1 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 6111571 = 9167357) B9167357
theorem B8151677 : Blo 1609003 8151677 := bstep (se 3 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 8151677 = 3056879) B3056879
theorem B8708795 : Blo 1609003 8708795 := bstep (se 1 (by rfl) ⟨6531596, by rfl⟩ : syracuseStep 8708795 = 13063193) B13063193
theorem B1811839 : Blo 1609003 1811839 := bstep (se 1 (by rfl) ⟨1358879, by rfl⟩ : syracuseStep 1811839 = 2717759) B2717759
theorem B5432939 : Blo 1609003 5432939 := bstep (se 1 (by rfl) ⟨4074704, by rfl⟩ : syracuseStep 5432939 = 8149409) B8149409
theorem B3057259 : Blo 1609003 3057259 := bstep (se 1 (by rfl) ⟨2292944, by rfl⟩ : syracuseStep 3057259 = 4585889) B4585889
theorem B2754313 : Blo 1609003 2754313 := bstep (se 2 (by rfl) ⟨1032867, by rfl⟩ : syracuseStep 2754313 = 2065735) B2065735
theorem B5433371 : Blo 1609003 5433371 := bstep (se 1 (by rfl) ⟨4075028, by rfl⟩ : syracuseStep 5433371 = 8150057) B8150057
theorem B10315943 : Blo 1609003 10315943 := bstep (se 1 (by rfl) ⟨7736957, by rfl⟩ : syracuseStep 10315943 = 15473915) B15473915
theorem B4073723 : Blo 1609003 4073723 := bstep (se 1 (by rfl) ⟨3055292, by rfl⟩ : syracuseStep 4073723 = 6110585) B6110585
theorem B3058003 : Blo 1609003 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B9169271 : Blo 1609003 9169271 := bstep (se 1 (by rfl) ⟨6876953, by rfl⟩ : syracuseStep 9169271 = 13753907) B13753907
theorem B9169523 : Blo 1609003 9169523 := bstep (se 1 (by rfl) ⟨6877142, by rfl⟩ : syracuseStep 9169523 = 13754285) B13754285
theorem B24169117 : Blo 1609003 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B69602165 : Blo 1609003 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B3582887 : Blo 1609003 3582887 := bstep (se 1 (by rfl) ⟨2687165, by rfl⟩ : syracuseStep 3582887 = 5374331) B5374331
theorem B3624119 : Blo 1609003 3624119 := bstep (se 1 (by rfl) ⟨2718089, by rfl⟩ : syracuseStep 3624119 = 5436179) B5436179
theorem B3624263 : Blo 1609003 3624263 := bstep (se 1 (by rfl) ⟨2718197, by rfl⟩ : syracuseStep 3624263 = 5436395) B5436395
theorem B5434991 : Blo 1609003 5434991 := bstep (se 1 (by rfl) ⟨4076243, by rfl⟩ : syracuseStep 5434991 = 8152487) B8152487
theorem B13758281 : Blo 1609003 13758281 := bstep (se 2 (by rfl) ⟨5159355, by rfl⟩ : syracuseStep 13758281 = 10318711) B10318711
theorem B1609799 : Blo 1609003 1609799 := bstep (se 1 (by rfl) ⟨1207349, by rfl⟩ : syracuseStep 1609799 = 2414699) B2414699
theorem B1609839 : Blo 1609003 1609839 := bstep (se 1 (by rfl) ⟨1207379, by rfl⟩ : syracuseStep 1609839 = 2414759) B2414759
theorem B8818895 : Blo 1609003 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B1609935 : Blo 1609003 1609935 := bstep (se 1 (by rfl) ⟨1207451, by rfl⟩ : syracuseStep 1609935 = 2414903) B2414903
theorem B1609951 : Blo 1609003 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B18329975 : Blo 1609003 18329975 := bstep (se 1 (by rfl) ⟨13747481, by rfl⟩ : syracuseStep 18329975 = 27494963) B27494963
theorem B1610143 : Blo 1609003 1610143 := bstep (se 1 (by rfl) ⟨1207607, by rfl⟩ : syracuseStep 1610143 = 2415215) B2415215
theorem B3264937 : Blo 1609003 3264937 := bstep (se 2 (by rfl) ⟨1224351, by rfl⟩ : syracuseStep 3264937 = 2448703) B2448703
theorem B75412133 : Blo 1609003 75412133 := bstep (se 4 (by rfl) ⟨7069887, by rfl⟩ : syracuseStep 75412133 = 14139775) B14139775
theorem B5436071 : Blo 1609003 5436071 := bstep (se 1 (by rfl) ⟨4077053, by rfl⟩ : syracuseStep 5436071 = 8154107) B8154107
theorem B1610431 : Blo 1609003 1610431 := bstep (se 1 (by rfl) ⟨1207823, by rfl⟩ : syracuseStep 1610431 = 2415647) B2415647
theorem B1610527 : Blo 1609003 1610527 := bstep (se 1 (by rfl) ⟨1207895, by rfl⟩ : syracuseStep 1610527 = 2415791) B2415791
theorem B4584431 : Blo 1609003 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B2413595 : Blo 1609003 2413595 := bstep (se 1 (by rfl) ⟨1810196, by rfl⟩ : syracuseStep 2413595 = 3620393) B3620393
theorem B12219497 : Blo 1609003 12219497 := bstep (se 2 (by rfl) ⟨4582311, by rfl⟩ : syracuseStep 12219497 = 9164623) B9164623
theorem B2577577 : Blo 1609003 2577577 := bstep (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) B1933183
theorem B1610983 : Blo 1609003 1610983 := bstep (se 1 (by rfl) ⟨1208237, by rfl⟩ : syracuseStep 1610983 = 2416475) B2416475
theorem B4896071 : Blo 1609003 4896071 := bstep (se 1 (by rfl) ⟨3672053, by rfl⟩ : syracuseStep 4896071 = 7344107) B7344107
theorem B11015639 : Blo 1609003 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B2414135 : Blo 1609003 2414135 := bstep (se 1 (by rfl) ⟨1810601, by rfl⟩ : syracuseStep 2414135 = 3621203) B3621203
theorem B2414207 : Blo 1609003 2414207 := bstep (se 1 (by rfl) ⟨1810655, by rfl⟩ : syracuseStep 2414207 = 3621311) B3621311
theorem B9164441 : Blo 1609003 9164441 := bstep (se 2 (by rfl) ⟨3436665, by rfl⟩ : syracuseStep 9164441 = 6873331) B6873331
theorem B10458953 : Blo 1609003 10458953 := bstep (se 2 (by rfl) ⟨3922107, by rfl⟩ : syracuseStep 10458953 = 7844215) B7844215
theorem B19593083 : Blo 1609003 19593083 := bstep (se 1 (by rfl) ⟨14694812, by rfl⟩ : syracuseStep 19593083 = 29389625) B29389625
theorem B8705981 : Blo 1609003 8705981 := bstep (se 3 (by rfl) ⟨1632371, by rfl⟩ : syracuseStep 8705981 = 3264743) B3264743
theorem B2291743 : Blo 1609003 2291743 := bstep (se 1 (by rfl) ⟨1718807, by rfl⟩ : syracuseStep 2291743 = 3437615) B3437615
theorem B2415335 : Blo 1609003 2415335 := bstep (se 1 (by rfl) ⟨1811501, by rfl⟩ : syracuseStep 2415335 = 3623003) B3623003
theorem B2415359 : Blo 1609003 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B3054647 : Blo 1609003 3054647 := bstep (se 1 (by rfl) ⟨2290985, by rfl⟩ : syracuseStep 3054647 = 4581971) B4581971
theorem B2415671 : Blo 1609003 2415671 := bstep (se 1 (by rfl) ⟨1811753, by rfl⟩ : syracuseStep 2415671 = 3623507) B3623507
theorem B7847047 : Blo 1609003 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B2415851 : Blo 1609003 2415851 := bstep (se 1 (by rfl) ⟨1811888, by rfl⟩ : syracuseStep 2415851 = 3623777) B3623777
theorem B7740841 : Blo 1609003 7740841 := bstep (se 2 (by rfl) ⟨2902815, by rfl⟩ : syracuseStep 7740841 = 5805631) B5805631
theorem B3055087 : Blo 1609003 3055087 := bstep (se 1 (by rfl) ⟨2291315, by rfl⟩ : syracuseStep 3055087 = 4582631) B4582631
theorem B6110873 : Blo 1609003 6110873 := bstep (se 2 (by rfl) ⟨2291577, by rfl⟩ : syracuseStep 6110873 = 4583155) B4583155
theorem B23518907 : Blo 1609003 23518907 := bstep (se 1 (by rfl) ⟨17639180, by rfl⟩ : syracuseStep 23518907 = 35278361) B35278361
theorem B3620699 : Blo 1609003 3620699 := bstep (se 1 (by rfl) ⟨2715524, by rfl⟩ : syracuseStep 3620699 = 5431049) B5431049
theorem B3055657 : Blo 1609003 3055657 := bstep (se 2 (by rfl) ⟨1145871, by rfl⟩ : syracuseStep 3055657 = 2291743) B2291743
theorem B30965975 : Blo 1609003 30965975 := bstep (se 1 (by rfl) ⟨23224481, by rfl⟩ : syracuseStep 30965975 = 46448963) B46448963
theorem B50274755 : Blo 1609003 50274755 := bstep (se 1 (by rfl) ⟨37706066, by rfl⟩ : syracuseStep 50274755 = 75412133) B75412133
theorem B3056287 : Blo 1609003 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B3621959 : Blo 1609003 3621959 := bstep (se 1 (by rfl) ⟨2716469, by rfl⟩ : syracuseStep 3621959 = 5432939) B5432939
theorem B6972635 : Blo 1609003 6972635 := bstep (se 1 (by rfl) ⟨5229476, by rfl⟩ : syracuseStep 6972635 = 10458953) B10458953
theorem B3622247 : Blo 1609003 3622247 := bstep (se 1 (by rfl) ⟨2716685, by rfl⟩ : syracuseStep 3622247 = 5433371) B5433371
theorem B14689669 : Blo 1609003 14689669 := bstep (se 4 (by rfl) ⟨1377156, by rfl⟩ : syracuseStep 14689669 = 2754313) B2754313
theorem B10462729 : Blo 1609003 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B6112847 : Blo 1609003 6112847 := bstep (se 1 (by rfl) ⟨4584635, by rfl⟩ : syracuseStep 6112847 = 9169271) B9169271
theorem B6113015 : Blo 1609003 6113015 := bstep (se 1 (by rfl) ⟨4584761, by rfl⟩ : syracuseStep 6113015 = 9169523) B9169523
theorem B46401443 : Blo 1609003 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B4073449 : Blo 1609003 4073449 := bstep (se 2 (by rfl) ⟨1527543, by rfl⟩ : syracuseStep 4073449 = 3055087) B3055087
theorem B3623327 : Blo 1609003 3623327 := bstep (se 1 (by rfl) ⟨2717495, by rfl⟩ : syracuseStep 3623327 = 5434991) B5434991
theorem B4073915 : Blo 1609003 4073915 := bstep (se 1 (by rfl) ⟨3055436, by rfl⟩ : syracuseStep 4073915 = 6110873) B6110873
theorem B9554365 : Blo 1609003 9554365 := bstep (se 3 (by rfl) ⟨1791443, by rfl⟩ : syracuseStep 9554365 = 3582887) B3582887
theorem B4074239 : Blo 1609003 4074239 := bstep (se 1 (by rfl) ⟨3055679, by rfl⟩ : syracuseStep 4074239 = 6111359) B6111359
theorem B5434451 : Blo 1609003 5434451 := bstep (se 1 (by rfl) ⟨4075838, by rfl⟩ : syracuseStep 5434451 = 8151677) B8151677
theorem B3624047 : Blo 1609003 3624047 := bstep (se 1 (by rfl) ⟨2718035, by rfl⟩ : syracuseStep 3624047 = 5436071) B5436071
theorem B1609063 : Blo 1609003 1609063 := bstep (se 1 (by rfl) ⟨1206797, by rfl⟩ : syracuseStep 1609063 = 2413595) B2413595
theorem B8146331 : Blo 1609003 8146331 := bstep (se 1 (by rfl) ⟨6109748, by rfl⟩ : syracuseStep 8146331 = 12219497) B12219497
theorem B3264047 : Blo 1609003 3264047 := bstep (se 1 (by rfl) ⟨2448035, by rfl⟩ : syracuseStep 3264047 = 4896071) B4896071
theorem B7343759 : Blo 1609003 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B1609423 : Blo 1609003 1609423 := bstep (se 1 (by rfl) ⟨1207067, by rfl⟩ : syracuseStep 1609423 = 2414135) B2414135
theorem B1609471 : Blo 1609003 1609471 := bstep (se 1 (by rfl) ⟨1207103, by rfl⟩ : syracuseStep 1609471 = 2414207) B2414207
theorem B13062055 : Blo 1609003 13062055 := bstep (se 1 (by rfl) ⟨9796541, by rfl⟩ : syracuseStep 13062055 = 19593083) B19593083
theorem B5803987 : Blo 1609003 5803987 := bstep (se 1 (by rfl) ⟨4352990, by rfl⟩ : syracuseStep 5803987 = 8705981) B8705981
theorem B6877295 : Blo 1609003 6877295 := bstep (se 1 (by rfl) ⟨5157971, by rfl⟩ : syracuseStep 6877295 = 10315943) B10315943
theorem B2715815 : Blo 1609003 2715815 := bstep (se 1 (by rfl) ⟨2036861, by rfl⟩ : syracuseStep 2715815 = 4073723) B4073723
theorem B3436769 : Blo 1609003 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B1610223 : Blo 1609003 1610223 := bstep (se 1 (by rfl) ⟨1207667, by rfl⟩ : syracuseStep 1610223 = 2415335) B2415335
theorem B1610239 : Blo 1609003 1610239 := bstep (se 1 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 1610239 = 2415359) B2415359
theorem B2036431 : Blo 1609003 2036431 := bstep (se 1 (by rfl) ⟨1527323, by rfl⟩ : syracuseStep 2036431 = 3054647) B3054647
theorem B1610447 : Blo 1609003 1610447 := bstep (se 1 (by rfl) ⟨1207835, by rfl⟩ : syracuseStep 1610447 = 2415671) B2415671
theorem B4076345 : Blo 1609003 4076345 := bstep (se 2 (by rfl) ⟨1528629, by rfl⟩ : syracuseStep 4076345 = 3057259) B3057259
theorem B1610567 : Blo 1609003 1610567 := bstep (se 1 (by rfl) ⟨1207925, by rfl⟩ : syracuseStep 1610567 = 2415851) B2415851
theorem B17412997 : Blo 1609003 17412997 := bstep (se 4 (by rfl) ⟨1632468, by rfl⟩ : syracuseStep 17412997 = 3264937) B3264937
theorem B9172187 : Blo 1609003 9172187 := bstep (se 1 (by rfl) ⟨6879140, by rfl⟩ : syracuseStep 9172187 = 13758281) B13758281
theorem B2413799 : Blo 1609003 2413799 := bstep (se 1 (by rfl) ⟨1810349, by rfl⟩ : syracuseStep 2413799 = 3620699) B3620699
theorem B12219983 : Blo 1609003 12219983 := bstep (se 1 (by rfl) ⟨9164987, by rfl⟩ : syracuseStep 12219983 = 18329975) B18329975
theorem B8148761 : Blo 1609003 8148761 := bstep (se 2 (by rfl) ⟨3055785, by rfl⟩ : syracuseStep 8148761 = 6111571) B6111571
theorem B4077337 : Blo 1609003 4077337 := bstep (se 2 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 4077337 = 3058003) B3058003
theorem B5805863 : Blo 1609003 5805863 := bstep (se 1 (by rfl) ⟨4354397, by rfl⟩ : syracuseStep 5805863 = 8708795) B8708795
theorem B23517053 : Blo 1609003 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B32225489 : Blo 1609003 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B6109627 : Blo 1609003 6109627 := bstep (se 1 (by rfl) ⟨4582220, by rfl⟩ : syracuseStep 6109627 = 9164441) B9164441
theorem B2415785 : Blo 1609003 2415785 := bstep (se 2 (by rfl) ⟨905919, by rfl⟩ : syracuseStep 2415785 = 1811839) B1811839
theorem B10321121 : Blo 1609003 10321121 := bstep (se 2 (by rfl) ⟨3870420, by rfl⟩ : syracuseStep 10321121 = 7740841) B7740841
theorem B2416079 : Blo 1609003 2416079 := bstep (se 1 (by rfl) ⟨1812059, by rfl⟩ : syracuseStep 2416079 = 3624119) B3624119
theorem B2416175 : Blo 1609003 2416175 := bstep (se 1 (by rfl) ⟨1812131, by rfl⟩ : syracuseStep 2416175 = 3624263) B3624263
theorem B15679271 : Blo 1609003 15679271 := bstep (se 1 (by rfl) ⟨11759453, by rfl⟩ : syracuseStep 15679271 = 23518907) B23518907
theorem B1810543 : Blo 1609003 1810543 := bstep (se 1 (by rfl) ⟨1357907, by rfl⟩ : syracuseStep 1810543 = 2715815) B2715815
theorem B20643983 : Blo 1609003 20643983 := bstep (se 1 (by rfl) ⟨15482987, by rfl⟩ : syracuseStep 20643983 = 30965975) B30965975
theorem B12739153 : Blo 1609003 12739153 := bstep (se 2 (by rfl) ⟨4777182, by rfl⟩ : syracuseStep 12739153 = 9554365) B9554365
theorem B23217329 : Blo 1609003 23217329 := bstep (se 2 (by rfl) ⟨8706498, by rfl⟩ : syracuseStep 23217329 = 17412997) B17412997
theorem B5432507 : Blo 1609003 5432507 := bstep (se 1 (by rfl) ⟨4074380, by rfl⟩ : syracuseStep 5432507 = 8148761) B8148761
theorem B30934295 : Blo 1609003 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B3622967 : Blo 1609003 3622967 := bstep (se 1 (by rfl) ⟨2717225, by rfl⟩ : syracuseStep 3622967 = 5434451) B5434451
theorem B4074209 : Blo 1609003 4074209 := bstep (se 2 (by rfl) ⟨1527828, by rfl⟩ : syracuseStep 4074209 = 3055657) B3055657
theorem B33516503 : Blo 1609003 33516503 := bstep (se 1 (by rfl) ⟨25137377, by rfl⟩ : syracuseStep 33516503 = 50274755) B50274755
theorem B8146169 : Blo 1609003 8146169 := bstep (se 2 (by rfl) ⟨3054813, by rfl⟩ : syracuseStep 8146169 = 6109627) B6109627
theorem B4648423 : Blo 1609003 4648423 := bstep (se 1 (by rfl) ⟨3486317, by rfl⟩ : syracuseStep 4648423 = 6972635) B6972635
theorem B6114791 : Blo 1609003 6114791 := bstep (se 1 (by rfl) ⟨4586093, by rfl⟩ : syracuseStep 6114791 = 9172187) B9172187
theorem B1609199 : Blo 1609003 1609199 := bstep (se 1 (by rfl) ⟨1206899, by rfl⟩ : syracuseStep 1609199 = 2413799) B2413799
theorem B4075049 : Blo 1609003 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B2715241 : Blo 1609003 2715241 := bstep (se 2 (by rfl) ⟨1018215, by rfl⟩ : syracuseStep 2715241 = 2036431) B2036431
theorem B8146655 : Blo 1609003 8146655 := bstep (se 1 (by rfl) ⟨6109991, by rfl⟩ : syracuseStep 8146655 = 12219983) B12219983
theorem B4075231 : Blo 1609003 4075231 := bstep (se 1 (by rfl) ⟨3056423, by rfl⟩ : syracuseStep 4075231 = 6112847) B6112847
theorem B4075343 : Blo 1609003 4075343 := bstep (se 1 (by rfl) ⟨3056507, by rfl⟩ : syracuseStep 4075343 = 6113015) B6113015
theorem B3870575 : Blo 1609003 3870575 := bstep (se 1 (by rfl) ⟨2902931, by rfl⟩ : syracuseStep 3870575 = 5805863) B5805863
theorem B21483659 : Blo 1609003 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B2715943 : Blo 1609003 2715943 := bstep (se 1 (by rfl) ⟨2036957, by rfl⟩ : syracuseStep 2715943 = 4073915) B4073915
theorem B2716159 : Blo 1609003 2716159 := bstep (se 1 (by rfl) ⟨2037119, by rfl⟩ : syracuseStep 2716159 = 4074239) B4074239
theorem B1610523 : Blo 1609003 1610523 := bstep (se 1 (by rfl) ⟨1207892, by rfl⟩ : syracuseStep 1610523 = 2415785) B2415785
theorem B1610719 : Blo 1609003 1610719 := bstep (se 1 (by rfl) ⟨1208039, by rfl⟩ : syracuseStep 1610719 = 2416079) B2416079
theorem B2176031 : Blo 1609003 2176031 := bstep (se 1 (by rfl) ⟨1632023, by rfl⟩ : syracuseStep 2176031 = 3264047) B3264047
theorem B1610783 : Blo 1609003 1610783 := bstep (se 1 (by rfl) ⟨1208087, by rfl⟩ : syracuseStep 1610783 = 2416175) B2416175
theorem B5436449 : Blo 1609003 5436449 := bstep (se 2 (by rfl) ⟨2038668, by rfl⟩ : syracuseStep 5436449 = 4077337) B4077337
theorem B4895839 : Blo 1609003 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B7738649 : Blo 1609003 7738649 := bstep (se 2 (by rfl) ⟨2901993, by rfl⟩ : syracuseStep 7738649 = 5803987) B5803987
theorem B4584863 : Blo 1609003 4584863 := bstep (se 1 (by rfl) ⟨3438647, by rfl⟩ : syracuseStep 4584863 = 6877295) B6877295
theorem B2291179 : Blo 1609003 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B2717563 : Blo 1609003 2717563 := bstep (se 1 (by rfl) ⟨2038172, by rfl⟩ : syracuseStep 2717563 = 4076345) B4076345
theorem B2414639 : Blo 1609003 2414639 := bstep (se 1 (by rfl) ⟨1810979, by rfl⟩ : syracuseStep 2414639 = 3621959) B3621959
theorem B2414831 : Blo 1609003 2414831 := bstep (se 1 (by rfl) ⟨1811123, by rfl⟩ : syracuseStep 2414831 = 3622247) B3622247
theorem B15678035 : Blo 1609003 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B2415551 : Blo 1609003 2415551 := bstep (se 1 (by rfl) ⟨1811663, by rfl⟩ : syracuseStep 2415551 = 3623327) B3623327
theorem B19586225 : Blo 1609003 19586225 := bstep (se 2 (by rfl) ⟨7344834, by rfl⟩ : syracuseStep 19586225 = 14689669) B14689669
theorem B13950305 : Blo 1609003 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B2416031 : Blo 1609003 2416031 := bstep (se 1 (by rfl) ⟨1812023, by rfl⟩ : syracuseStep 2416031 = 3624047) B3624047
theorem B6880747 : Blo 1609003 6880747 := bstep (se 1 (by rfl) ⟨5160560, by rfl⟩ : syracuseStep 6880747 = 10321121) B10321121
theorem B5430887 : Blo 1609003 5430887 := bstep (se 1 (by rfl) ⟨4073165, by rfl⟩ : syracuseStep 5430887 = 8146331) B8146331
theorem B10452847 : Blo 1609003 10452847 := bstep (se 1 (by rfl) ⟨7839635, by rfl⟩ : syracuseStep 10452847 = 15679271) B15679271
theorem B17416073 : Blo 1609003 17416073 := bstep (se 2 (by rfl) ⟨6531027, by rfl⟩ : syracuseStep 17416073 = 13062055) B13062055
theorem B5431265 : Blo 1609003 5431265 := bstep (se 2 (by rfl) ⟨2036724, by rfl⟩ : syracuseStep 5431265 = 4073449) B4073449
theorem B13762655 : Blo 1609003 13762655 := bstep (se 1 (by rfl) ⟨10321991, by rfl⟩ : syracuseStep 13762655 = 20643983) B20643983
theorem B3621257 : Blo 1609003 3621257 := bstep (se 2 (by rfl) ⟨1357971, by rfl⟩ : syracuseStep 3621257 = 2715943) B2715943
theorem B3621545 : Blo 1609003 3621545 := bstep (se 2 (by rfl) ⟨1358079, by rfl⟩ : syracuseStep 3621545 = 2716159) B2716159
theorem B3621671 : Blo 1609003 3621671 := bstep (se 1 (by rfl) ⟨2716253, by rfl⟩ : syracuseStep 3621671 = 5432507) B5432507
theorem B9300203 : Blo 1609003 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B5433641 : Blo 1609003 5433641 := bstep (se 2 (by rfl) ⟨2037615, by rfl⟩ : syracuseStep 5433641 = 4075231) B4075231
theorem B13937129 : Blo 1609003 13937129 := bstep (se 2 (by rfl) ⟨5226423, by rfl⟩ : syracuseStep 13937129 = 10452847) B10452847
theorem B3623417 : Blo 1609003 3623417 := bstep (se 2 (by rfl) ⟨1358781, by rfl⟩ : syracuseStep 3623417 = 2717563) B2717563
theorem B11610715 : Blo 1609003 11610715 := bstep (se 1 (by rfl) ⟨8708036, by rfl⟩ : syracuseStep 11610715 = 17416073) B17416073
theorem B5802749 : Blo 1609003 5802749 := bstep (se 3 (by rfl) ⟨1088015, by rfl⟩ : syracuseStep 5802749 = 2176031) B2176031
theorem B14322439 : Blo 1609003 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B3624299 : Blo 1609003 3624299 := bstep (se 1 (by rfl) ⟨2718224, by rfl⟩ : syracuseStep 3624299 = 5436449) B5436449
theorem B16985537 : Blo 1609003 16985537 := bstep (se 2 (by rfl) ⟨6369576, by rfl⟩ : syracuseStep 16985537 = 12739153) B12739153
theorem B15478219 : Blo 1609003 15478219 := bstep (se 1 (by rfl) ⟨11608664, by rfl⟩ : syracuseStep 15478219 = 23217329) B23217329
theorem B20622863 : Blo 1609003 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B12226301 : Blo 1609003 12226301 := bstep (se 3 (by rfl) ⟨2292431, by rfl⟩ : syracuseStep 12226301 = 4584863) B4584863
theorem B1609759 : Blo 1609003 1609759 := bstep (se 1 (by rfl) ⟨1207319, by rfl⟩ : syracuseStep 1609759 = 2414639) B2414639
theorem B1609887 : Blo 1609003 1609887 := bstep (se 1 (by rfl) ⟨1207415, by rfl⟩ : syracuseStep 1609887 = 2414831) B2414831
theorem B2716139 : Blo 1609003 2716139 := bstep (se 1 (by rfl) ⟨2037104, by rfl⟩ : syracuseStep 2716139 = 4074209) B4074209
theorem B1610367 : Blo 1609003 1610367 := bstep (se 1 (by rfl) ⟨1207775, by rfl⟩ : syracuseStep 1610367 = 2415551) B2415551
theorem B6197897 : Blo 1609003 6197897 := bstep (se 2 (by rfl) ⟨2324211, by rfl⟩ : syracuseStep 6197897 = 4648423) B4648423
theorem B22344335 : Blo 1609003 22344335 := bstep (se 1 (by rfl) ⟨16758251, by rfl⟩ : syracuseStep 22344335 = 33516503) B33516503
theorem B1610687 : Blo 1609003 1610687 := bstep (se 1 (by rfl) ⟨1208015, by rfl⟩ : syracuseStep 1610687 = 2416031) B2416031
theorem B4076527 : Blo 1609003 4076527 := bstep (se 1 (by rfl) ⟨3057395, by rfl⟩ : syracuseStep 4076527 = 6114791) B6114791
theorem B2716699 : Blo 1609003 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B2716895 : Blo 1609003 2716895 := bstep (se 1 (by rfl) ⟨2037671, by rfl⟩ : syracuseStep 2716895 = 4075343) B4075343
theorem B2414057 : Blo 1609003 2414057 := bstep (se 2 (by rfl) ⟨905271, by rfl⟩ : syracuseStep 2414057 = 1810543) B1810543
theorem B5159099 : Blo 1609003 5159099 := bstep (se 1 (by rfl) ⟨3869324, by rfl⟩ : syracuseStep 5159099 = 7738649) B7738649
theorem B2415311 : Blo 1609003 2415311 := bstep (se 1 (by rfl) ⟨1811483, by rfl⟩ : syracuseStep 2415311 = 3622967) B3622967
theorem B6527785 : Blo 1609003 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B10452023 : Blo 1609003 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B3054905 : Blo 1609003 3054905 := bstep (se 2 (by rfl) ⟨1145589, by rfl⟩ : syracuseStep 3054905 = 2291179) B2291179
theorem B9174329 : Blo 1609003 9174329 := bstep (se 2 (by rfl) ⟨3440373, by rfl⟩ : syracuseStep 9174329 = 6880747) B6880747
theorem B13057483 : Blo 1609003 13057483 := bstep (se 1 (by rfl) ⟨9793112, by rfl⟩ : syracuseStep 13057483 = 19586225) B19586225
theorem B3620321 : Blo 1609003 3620321 := bstep (se 2 (by rfl) ⟨1357620, by rfl⟩ : syracuseStep 3620321 = 2715241) B2715241
theorem B5430779 : Blo 1609003 5430779 := bstep (se 1 (by rfl) ⟨4073084, by rfl⟩ : syracuseStep 5430779 = 8146169) B8146169
theorem B3620591 : Blo 1609003 3620591 := bstep (se 1 (by rfl) ⟨2715443, by rfl⟩ : syracuseStep 3620591 = 5430887) B5430887
theorem B5431103 : Blo 1609003 5431103 := bstep (se 1 (by rfl) ⟨4073327, by rfl⟩ : syracuseStep 5431103 = 8146655) B8146655
theorem B2580383 : Blo 1609003 2580383 := bstep (se 1 (by rfl) ⟨1935287, by rfl⟩ : syracuseStep 2580383 = 3870575) B3870575
theorem B3620843 : Blo 1609003 3620843 := bstep (se 1 (by rfl) ⟨2715632, by rfl⟩ : syracuseStep 3620843 = 5431265) B5431265
theorem B9175103 : Blo 1609003 9175103 := bstep (se 1 (by rfl) ⟨6881327, by rfl⟩ : syracuseStep 9175103 = 13762655) B13762655
theorem B1810759 : Blo 1609003 1810759 := bstep (se 1 (by rfl) ⟨1358069, by rfl⟩ : syracuseStep 1810759 = 2716139) B2716139
theorem B1811263 : Blo 1609003 1811263 := bstep (se 1 (by rfl) ⟨1358447, by rfl⟩ : syracuseStep 1811263 = 2716895) B2716895
theorem B3622265 : Blo 1609003 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B3622427 : Blo 1609003 3622427 := bstep (se 1 (by rfl) ⟨2716820, by rfl⟩ : syracuseStep 3622427 = 5433641) B5433641
theorem B9291419 : Blo 1609003 9291419 := bstep (se 1 (by rfl) ⟨6968564, by rfl⟩ : syracuseStep 9291419 = 13937129) B13937129
theorem B3868499 : Blo 1609003 3868499 := bstep (se 1 (by rfl) ⟨2901374, by rfl⟩ : syracuseStep 3868499 = 5802749) B5802749
theorem B17409977 : Blo 1609003 17409977 := bstep (se 2 (by rfl) ⟨6528741, by rfl⟩ : syracuseStep 17409977 = 13057483) B13057483
theorem B20637625 : Blo 1609003 20637625 := bstep (se 2 (by rfl) ⟨7739109, by rfl⟩ : syracuseStep 20637625 = 15478219) B15478219
theorem B11323691 : Blo 1609003 11323691 := bstep (se 1 (by rfl) ⟨8492768, by rfl⟩ : syracuseStep 11323691 = 16985537) B16985537
theorem B13748575 : Blo 1609003 13748575 := bstep (se 1 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 13748575 = 20622863) B20622863
theorem B14896223 : Blo 1609003 14896223 := bstep (se 1 (by rfl) ⟨11172167, by rfl⟩ : syracuseStep 14896223 = 22344335) B22344335
theorem B13757597 : Blo 1609003 13757597 := bstep (se 3 (by rfl) ⟨2579549, by rfl⟩ : syracuseStep 13757597 = 5159099) B5159099
theorem B1609371 : Blo 1609003 1609371 := bstep (se 1 (by rfl) ⟨1207028, by rfl⟩ : syracuseStep 1609371 = 2414057) B2414057
theorem B8703713 : Blo 1609003 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B5435369 : Blo 1609003 5435369 := bstep (se 2 (by rfl) ⟨2038263, by rfl⟩ : syracuseStep 5435369 = 4076527) B4076527
theorem B76386341 : Blo 1609003 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B16527725 : Blo 1609003 16527725 := bstep (se 3 (by rfl) ⟨3098948, by rfl⟩ : syracuseStep 16527725 = 6197897) B6197897
theorem B1610207 : Blo 1609003 1610207 := bstep (se 1 (by rfl) ⟨1207655, by rfl⟩ : syracuseStep 1610207 = 2415311) B2415311
theorem B6968015 : Blo 1609003 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B2036603 : Blo 1609003 2036603 := bstep (se 1 (by rfl) ⟨1527452, by rfl⟩ : syracuseStep 2036603 = 3054905) B3054905
theorem B6116219 : Blo 1609003 6116219 := bstep (se 1 (by rfl) ⟨4587164, by rfl⟩ : syracuseStep 6116219 = 9174329) B9174329
theorem B2413547 : Blo 1609003 2413547 := bstep (se 1 (by rfl) ⟨1810160, by rfl⟩ : syracuseStep 2413547 = 3620321) B3620321
theorem B2413727 : Blo 1609003 2413727 := bstep (se 1 (by rfl) ⟨1810295, by rfl⟩ : syracuseStep 2413727 = 3620591) B3620591
theorem B2413895 : Blo 1609003 2413895 := bstep (se 1 (by rfl) ⟨1810421, by rfl⟩ : syracuseStep 2413895 = 3620843) B3620843
theorem B2414171 : Blo 1609003 2414171 := bstep (se 1 (by rfl) ⟨1810628, by rfl⟩ : syracuseStep 2414171 = 3621257) B3621257
theorem B2414363 : Blo 1609003 2414363 := bstep (se 1 (by rfl) ⟨1810772, by rfl⟩ : syracuseStep 2414363 = 3621545) B3621545
theorem B2414447 : Blo 1609003 2414447 := bstep (se 1 (by rfl) ⟨1810835, by rfl⟩ : syracuseStep 2414447 = 3621671) B3621671
theorem B15480953 : Blo 1609003 15480953 := bstep (se 2 (by rfl) ⟨5805357, by rfl⟩ : syracuseStep 15480953 = 11610715) B11610715
theorem B6200135 : Blo 1609003 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B2415611 : Blo 1609003 2415611 := bstep (se 1 (by rfl) ⟨1811708, by rfl⟩ : syracuseStep 2415611 = 3623417) B3623417
theorem B2416199 : Blo 1609003 2416199 := bstep (se 1 (by rfl) ⟨1812149, by rfl⟩ : syracuseStep 2416199 = 3624299) B3624299
theorem B3620519 : Blo 1609003 3620519 := bstep (se 1 (by rfl) ⟨2715389, by rfl⟩ : syracuseStep 3620519 = 5430779) B5430779
theorem B6881021 : Blo 1609003 6881021 := bstep (se 3 (by rfl) ⟨1290191, by rfl⟩ : syracuseStep 6881021 = 2580383) B2580383
theorem B8150867 : Blo 1609003 8150867 := bstep (se 1 (by rfl) ⟨6113150, by rfl⟩ : syracuseStep 8150867 = 12226301) B12226301
theorem B3620735 : Blo 1609003 3620735 := bstep (se 1 (by rfl) ⟨2715551, by rfl⟩ : syracuseStep 3620735 = 5431103) B5431103
theorem B11018483 : Blo 1609003 11018483 := bstep (se 1 (by rfl) ⟨8263862, by rfl⟩ : syracuseStep 11018483 = 16527725) B16527725
theorem B4645343 : Blo 1609003 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B6194279 : Blo 1609003 6194279 := bstep (se 1 (by rfl) ⟨4645709, by rfl⟩ : syracuseStep 6194279 = 9291419) B9291419
theorem B23209901 : Blo 1609003 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B9930815 : Blo 1609003 9930815 := bstep (se 1 (by rfl) ⟨7448111, by rfl⟩ : syracuseStep 9930815 = 14896223) B14896223
theorem B10315997 : Blo 1609003 10315997 := bstep (se 3 (by rfl) ⟨1934249, by rfl⟩ : syracuseStep 10315997 = 3868499) B3868499
theorem B5433911 : Blo 1609003 5433911 := bstep (se 1 (by rfl) ⟨4075433, by rfl⟩ : syracuseStep 5433911 = 8150867) B8150867
theorem B3623579 : Blo 1609003 3623579 := bstep (se 1 (by rfl) ⟨2717684, by rfl⟩ : syracuseStep 3623579 = 5435369) B5435369
theorem B50924227 : Blo 1609003 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B1609031 : Blo 1609003 1609031 := bstep (se 1 (by rfl) ⟨1206773, by rfl⟩ : syracuseStep 1609031 = 2413547) B2413547
theorem B1609151 : Blo 1609003 1609151 := bstep (se 1 (by rfl) ⟨1206863, by rfl⟩ : syracuseStep 1609151 = 2413727) B2413727
theorem B1609263 : Blo 1609003 1609263 := bstep (se 1 (by rfl) ⟨1206947, by rfl⟩ : syracuseStep 1609263 = 2413895) B2413895
theorem B1609447 : Blo 1609003 1609447 := bstep (se 1 (by rfl) ⟨1207085, by rfl⟩ : syracuseStep 1609447 = 2414171) B2414171
theorem B1609575 : Blo 1609003 1609575 := bstep (se 1 (by rfl) ⟨1207181, by rfl⟩ : syracuseStep 1609575 = 2414363) B2414363
theorem B1609631 : Blo 1609003 1609631 := bstep (se 1 (by rfl) ⟨1207223, by rfl⟩ : syracuseStep 1609631 = 2414447) B2414447
theorem B7549127 : Blo 1609003 7549127 := bstep (se 1 (by rfl) ⟨5661845, by rfl⟩ : syracuseStep 7549127 = 11323691) B11323691
theorem B4133423 : Blo 1609003 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B1610407 : Blo 1609003 1610407 := bstep (se 1 (by rfl) ⟨1207805, by rfl⟩ : syracuseStep 1610407 = 2415611) B2415611
theorem B9171731 : Blo 1609003 9171731 := bstep (se 1 (by rfl) ⟨6878798, by rfl⟩ : syracuseStep 9171731 = 13757597) B13757597
theorem B1610799 : Blo 1609003 1610799 := bstep (se 1 (by rfl) ⟨1208099, by rfl⟩ : syracuseStep 1610799 = 2416199) B2416199
theorem B2413679 : Blo 1609003 2413679 := bstep (se 1 (by rfl) ⟨1810259, by rfl⟩ : syracuseStep 2413679 = 3620519) B3620519
theorem B2413823 : Blo 1609003 2413823 := bstep (se 1 (by rfl) ⟨1810367, by rfl⟩ : syracuseStep 2413823 = 3620735) B3620735
theorem B6116735 : Blo 1609003 6116735 := bstep (se 1 (by rfl) ⟨4587551, by rfl⟩ : syracuseStep 6116735 = 9175103) B9175103
theorem B2414345 : Blo 1609003 2414345 := bstep (se 2 (by rfl) ⟨905379, by rfl⟩ : syracuseStep 2414345 = 1810759) B1810759
theorem B18331433 : Blo 1609003 18331433 := bstep (se 2 (by rfl) ⟨6874287, by rfl⟩ : syracuseStep 18331433 = 13748575) B13748575
theorem B4077479 : Blo 1609003 4077479 := bstep (se 1 (by rfl) ⟨3058109, by rfl⟩ : syracuseStep 4077479 = 6116219) B6116219
theorem B2414843 : Blo 1609003 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B2414951 : Blo 1609003 2414951 := bstep (se 1 (by rfl) ⟨1811213, by rfl⟩ : syracuseStep 2414951 = 3622427) B3622427
theorem B2415017 : Blo 1609003 2415017 := bstep (se 2 (by rfl) ⟨905631, by rfl⟩ : syracuseStep 2415017 = 1811263) B1811263
theorem B11606651 : Blo 1609003 11606651 := bstep (se 1 (by rfl) ⟨8704988, by rfl⟩ : syracuseStep 11606651 = 17409977) B17409977
theorem B10320635 : Blo 1609003 10320635 := bstep (se 1 (by rfl) ⟨7740476, by rfl⟩ : syracuseStep 10320635 = 15480953) B15480953
theorem B5430941 : Blo 1609003 5430941 := bstep (se 3 (by rfl) ⟨1018301, by rfl⟩ : syracuseStep 5430941 = 2036603) B2036603
theorem B4587347 : Blo 1609003 4587347 := bstep (se 1 (by rfl) ⟨3440510, by rfl⟩ : syracuseStep 4587347 = 6881021) B6881021
theorem B27516833 : Blo 1609003 27516833 := bstep (se 2 (by rfl) ⟨10318812, by rfl⟩ : syracuseStep 27516833 = 20637625) B20637625
theorem B3096895 : Blo 1609003 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B6620543 : Blo 1609003 6620543 := bstep (se 1 (by rfl) ⟨4965407, by rfl⟩ : syracuseStep 6620543 = 9930815) B9930815
theorem B3622607 : Blo 1609003 3622607 := bstep (se 1 (by rfl) ⟨2716955, by rfl⟩ : syracuseStep 3622607 = 5433911) B5433911
theorem B3058231 : Blo 1609003 3058231 := bstep (se 1 (by rfl) ⟨2293673, by rfl⟩ : syracuseStep 3058231 = 4587347) B4587347
theorem B18344555 : Blo 1609003 18344555 := bstep (se 1 (by rfl) ⟨13758416, by rfl⟩ : syracuseStep 18344555 = 27516833) B27516833
theorem B5032751 : Blo 1609003 5032751 := bstep (se 1 (by rfl) ⟨3774563, by rfl⟩ : syracuseStep 5032751 = 7549127) B7549127
theorem B16518077 : Blo 1609003 16518077 := bstep (se 3 (by rfl) ⟨3097139, by rfl⟩ : syracuseStep 16518077 = 6194279) B6194279
theorem B2755615 : Blo 1609003 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B6114487 : Blo 1609003 6114487 := bstep (se 1 (by rfl) ⟨4585865, by rfl⟩ : syracuseStep 6114487 = 9171731) B9171731
theorem B1609119 : Blo 1609003 1609119 := bstep (se 1 (by rfl) ⟨1206839, by rfl⟩ : syracuseStep 1609119 = 2413679) B2413679
theorem B1609215 : Blo 1609003 1609215 := bstep (se 1 (by rfl) ⟨1206911, by rfl⟩ : syracuseStep 1609215 = 2413823) B2413823
theorem B67898969 : Blo 1609003 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B1609563 : Blo 1609003 1609563 := bstep (se 1 (by rfl) ⟨1207172, by rfl⟩ : syracuseStep 1609563 = 2414345) B2414345
theorem B6877331 : Blo 1609003 6877331 := bstep (se 1 (by rfl) ⟨5157998, by rfl⟩ : syracuseStep 6877331 = 10315997) B10315997
theorem B1609895 : Blo 1609003 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B1609967 : Blo 1609003 1609967 := bstep (se 1 (by rfl) ⟨1207475, by rfl⟩ : syracuseStep 1609967 = 2414951) B2414951
theorem B1610011 : Blo 1609003 1610011 := bstep (se 1 (by rfl) ⟨1207508, by rfl⟩ : syracuseStep 1610011 = 2415017) B2415017
theorem B7737767 : Blo 1609003 7737767 := bstep (se 1 (by rfl) ⟨5803325, by rfl⟩ : syracuseStep 7737767 = 11606651) B11606651
theorem B7345655 : Blo 1609003 7345655 := bstep (se 1 (by rfl) ⟨5509241, by rfl⟩ : syracuseStep 7345655 = 11018483) B11018483
theorem B4077823 : Blo 1609003 4077823 := bstep (se 1 (by rfl) ⟨3058367, by rfl⟩ : syracuseStep 4077823 = 6116735) B6116735
theorem B12220955 : Blo 1609003 12220955 := bstep (se 1 (by rfl) ⟨9165716, by rfl⟩ : syracuseStep 12220955 = 18331433) B18331433
theorem B2718319 : Blo 1609003 2718319 := bstep (se 1 (by rfl) ⟨2038739, by rfl⟩ : syracuseStep 2718319 = 4077479) B4077479
theorem B15473267 : Blo 1609003 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B2415719 : Blo 1609003 2415719 := bstep (se 1 (by rfl) ⟨1811789, by rfl⟩ : syracuseStep 2415719 = 3623579) B3623579
theorem B6880423 : Blo 1609003 6880423 := bstep (se 1 (by rfl) ⟨5160317, by rfl⟩ : syracuseStep 6880423 = 10320635) B10320635
theorem B3620627 : Blo 1609003 3620627 := bstep (se 1 (by rfl) ⟨2715470, by rfl⟩ : syracuseStep 3620627 = 5430941) B5430941
theorem B4129193 : Blo 1609003 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B8152649 : Blo 1609003 8152649 := bstep (se 2 (by rfl) ⟨3057243, by rfl⟩ : syracuseStep 8152649 = 6114487) B6114487
theorem B10315511 : Blo 1609003 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B11012051 : Blo 1609003 11012051 := bstep (se 1 (by rfl) ⟨8259038, by rfl⟩ : syracuseStep 11012051 = 16518077) B16518077
theorem B13420669 : Blo 1609003 13420669 := bstep (se 3 (by rfl) ⟨2516375, by rfl⟩ : syracuseStep 13420669 = 5032751) B5032751
theorem B3624425 : Blo 1609003 3624425 := bstep (se 2 (by rfl) ⟨1359159, by rfl⟩ : syracuseStep 3624425 = 2718319) B2718319
theorem B3674153 : Blo 1609003 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B8147303 : Blo 1609003 8147303 := bstep (se 1 (by rfl) ⟨6110477, by rfl⟩ : syracuseStep 8147303 = 12220955) B12220955
theorem B1610479 : Blo 1609003 1610479 := bstep (se 1 (by rfl) ⟨1207859, by rfl⟩ : syracuseStep 1610479 = 2415719) B2415719
theorem B45265979 : Blo 1609003 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B2413751 : Blo 1609003 2413751 := bstep (se 1 (by rfl) ⟨1810313, by rfl⟩ : syracuseStep 2413751 = 3620627) B3620627
theorem B4584887 : Blo 1609003 4584887 := bstep (se 1 (by rfl) ⟨3438665, by rfl⟩ : syracuseStep 4584887 = 6877331) B6877331
theorem B5158511 : Blo 1609003 5158511 := bstep (se 1 (by rfl) ⟨3868883, by rfl⟩ : syracuseStep 5158511 = 7737767) B7737767
theorem B5437097 : Blo 1609003 5437097 := bstep (se 2 (by rfl) ⟨2038911, by rfl⟩ : syracuseStep 5437097 = 4077823) B4077823
theorem B4077641 : Blo 1609003 4077641 := bstep (se 2 (by rfl) ⟨1529115, by rfl⟩ : syracuseStep 4077641 = 3058231) B3058231
theorem B4413695 : Blo 1609003 4413695 := bstep (se 1 (by rfl) ⟨3310271, by rfl⟩ : syracuseStep 4413695 = 6620543) B6620543
theorem B4897103 : Blo 1609003 4897103 := bstep (se 1 (by rfl) ⟨3672827, by rfl⟩ : syracuseStep 4897103 = 7345655) B7345655
theorem B2415071 : Blo 1609003 2415071 := bstep (se 1 (by rfl) ⟨1811303, by rfl⟩ : syracuseStep 2415071 = 3622607) B3622607
theorem B9173897 : Blo 1609003 9173897 := bstep (se 2 (by rfl) ⟨3440211, by rfl⟩ : syracuseStep 9173897 = 6880423) B6880423
theorem B12229703 : Blo 1609003 12229703 := bstep (se 1 (by rfl) ⟨9172277, by rfl⟩ : syracuseStep 12229703 = 18344555) B18344555
theorem B2449435 : Blo 1609003 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B5431535 : Blo 1609003 5431535 := bstep (se 1 (by rfl) ⟨4073651, by rfl⟩ : syracuseStep 5431535 = 8147303) B8147303
theorem B2752795 : Blo 1609003 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B3056591 : Blo 1609003 3056591 := bstep (se 1 (by rfl) ⟨2292443, by rfl⟩ : syracuseStep 3056591 = 4584887) B4584887
theorem B7341367 : Blo 1609003 7341367 := bstep (se 1 (by rfl) ⟨5506025, by rfl⟩ : syracuseStep 7341367 = 11012051) B11012051
theorem B8153135 : Blo 1609003 8153135 := bstep (se 1 (by rfl) ⟨6114851, by rfl⟩ : syracuseStep 8153135 = 12229703) B12229703
theorem B17894225 : Blo 1609003 17894225 := bstep (se 2 (by rfl) ⟨6710334, by rfl⟩ : syracuseStep 17894225 = 13420669) B13420669
theorem B1609167 : Blo 1609003 1609167 := bstep (se 1 (by rfl) ⟨1206875, by rfl⟩ : syracuseStep 1609167 = 2413751) B2413751
theorem B52235765 : Blo 1609003 52235765 := bstep (se 5 (by rfl) ⟨2448551, by rfl⟩ : syracuseStep 52235765 = 4897103) B4897103
theorem B5435099 : Blo 1609003 5435099 := bstep (se 1 (by rfl) ⟨4076324, by rfl⟩ : syracuseStep 5435099 = 8152649) B8152649
theorem B3624731 : Blo 1609003 3624731 := bstep (se 1 (by rfl) ⟨2718548, by rfl⟩ : syracuseStep 3624731 = 5437097) B5437097
theorem B6877007 : Blo 1609003 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B1610047 : Blo 1609003 1610047 := bstep (se 1 (by rfl) ⟨1207535, by rfl⟩ : syracuseStep 1610047 = 2415071) B2415071
theorem B6115931 : Blo 1609003 6115931 := bstep (se 1 (by rfl) ⟨4586948, by rfl⟩ : syracuseStep 6115931 = 9173897) B9173897
theorem B30177319 : Blo 1609003 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B3439007 : Blo 1609003 3439007 := bstep (se 1 (by rfl) ⟨2579255, by rfl⟩ : syracuseStep 3439007 = 5158511) B5158511
theorem B2718427 : Blo 1609003 2718427 := bstep (se 1 (by rfl) ⟨2038820, by rfl⟩ : syracuseStep 2718427 = 4077641) B4077641
theorem B2416283 : Blo 1609003 2416283 := bstep (se 1 (by rfl) ⟨1812212, by rfl⟩ : syracuseStep 2416283 = 3624425) B3624425
theorem B47079413 : Blo 1609003 47079413 := bstep (se 5 (by rfl) ⟨2206847, by rfl⟩ : syracuseStep 47079413 = 4413695) B4413695
theorem B3621023 : Blo 1609003 3621023 := bstep (se 1 (by rfl) ⟨2715767, by rfl⟩ : syracuseStep 3621023 = 5431535) B5431535
theorem B14681573 : Blo 1609003 14681573 := bstep (se 4 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 14681573 = 2752795) B2752795
theorem B11929483 : Blo 1609003 11929483 := bstep (se 1 (by rfl) ⟨8947112, by rfl⟩ : syracuseStep 11929483 = 17894225) B17894225
theorem B3623399 : Blo 1609003 3623399 := bstep (se 1 (by rfl) ⟨2717549, by rfl⟩ : syracuseStep 3623399 = 5435099) B5435099
theorem B31386275 : Blo 1609003 31386275 := bstep (se 1 (by rfl) ⟨23539706, by rfl⟩ : syracuseStep 31386275 = 47079413) B47079413
theorem B3624569 : Blo 1609003 3624569 := bstep (se 2 (by rfl) ⟨1359213, by rfl⟩ : syracuseStep 3624569 = 2718427) B2718427
theorem B5435423 : Blo 1609003 5435423 := bstep (se 1 (by rfl) ⟨4076567, by rfl⟩ : syracuseStep 5435423 = 8153135) B8153135
theorem B1610855 : Blo 1609003 1610855 := bstep (se 1 (by rfl) ⟨1208141, by rfl⟩ : syracuseStep 1610855 = 2416283) B2416283
theorem B4584671 : Blo 1609003 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B3265913 : Blo 1609003 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B40236425 : Blo 1609003 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B4077287 : Blo 1609003 4077287 := bstep (se 1 (by rfl) ⟨3057965, by rfl⟩ : syracuseStep 4077287 = 6115931) B6115931
theorem B2037727 : Blo 1609003 2037727 := bstep (se 1 (by rfl) ⟨1528295, by rfl⟩ : syracuseStep 2037727 = 3056591) B3056591
theorem B2292671 : Blo 1609003 2292671 := bstep (se 1 (by rfl) ⟨1719503, by rfl⟩ : syracuseStep 2292671 = 3439007) B3439007
theorem B9788489 : Blo 1609003 9788489 := bstep (se 2 (by rfl) ⟨3670683, by rfl⟩ : syracuseStep 9788489 = 7341367) B7341367
theorem B34823843 : Blo 1609003 34823843 := bstep (se 1 (by rfl) ⟨26117882, by rfl⟩ : syracuseStep 34823843 = 52235765) B52235765
theorem B2416487 : Blo 1609003 2416487 := bstep (se 1 (by rfl) ⟨1812365, by rfl⟩ : syracuseStep 2416487 = 3624731) B3624731
theorem B3056447 : Blo 1609003 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B20924183 : Blo 1609003 20924183 := bstep (se 1 (by rfl) ⟨15693137, by rfl⟩ : syracuseStep 20924183 = 31386275) B31386275
theorem B6113789 : Blo 1609003 6113789 := bstep (se 3 (by rfl) ⟨1146335, by rfl⟩ : syracuseStep 6113789 = 2292671) B2292671
theorem B3623615 : Blo 1609003 3623615 := bstep (se 1 (by rfl) ⟨2717711, by rfl⟩ : syracuseStep 3623615 = 5435423) B5435423
theorem B26824283 : Blo 1609003 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B6525659 : Blo 1609003 6525659 := bstep (se 1 (by rfl) ⟨4894244, by rfl⟩ : syracuseStep 6525659 = 9788489) B9788489
theorem B15905977 : Blo 1609003 15905977 := bstep (se 2 (by rfl) ⟨5964741, by rfl⟩ : syracuseStep 15905977 = 11929483) B11929483
theorem B1610991 : Blo 1609003 1610991 := bstep (se 1 (by rfl) ⟨1208243, by rfl⟩ : syracuseStep 1610991 = 2416487) B2416487
theorem B2716969 : Blo 1609003 2716969 := bstep (se 2 (by rfl) ⟨1018863, by rfl⟩ : syracuseStep 2716969 = 2037727) B2037727
theorem B2414015 : Blo 1609003 2414015 := bstep (se 1 (by rfl) ⟨1810511, by rfl⟩ : syracuseStep 2414015 = 3621023) B3621023
theorem B2177275 : Blo 1609003 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B9787715 : Blo 1609003 9787715 := bstep (se 1 (by rfl) ⟨7340786, by rfl⟩ : syracuseStep 9787715 = 14681573) B14681573
theorem B2718191 : Blo 1609003 2718191 := bstep (se 1 (by rfl) ⟨2038643, by rfl⟩ : syracuseStep 2718191 = 4077287) B4077287
theorem B2415599 : Blo 1609003 2415599 := bstep (se 1 (by rfl) ⟨1811699, by rfl⟩ : syracuseStep 2415599 = 3623399) B3623399
theorem B2416379 : Blo 1609003 2416379 := bstep (se 1 (by rfl) ⟨1812284, by rfl⟩ : syracuseStep 2416379 = 3624569) B3624569
theorem B23215895 : Blo 1609003 23215895 := bstep (se 1 (by rfl) ⟨17411921, by rfl⟩ : syracuseStep 23215895 = 34823843) B34823843
theorem B4350439 : Blo 1609003 4350439 := bstep (se 1 (by rfl) ⟨3262829, by rfl⟩ : syracuseStep 4350439 = 6525659) B6525659
theorem B1812127 : Blo 1609003 1812127 := bstep (se 1 (by rfl) ⟨1359095, by rfl⟩ : syracuseStep 1812127 = 2718191) B2718191
theorem B3622625 : Blo 1609003 3622625 := bstep (se 2 (by rfl) ⟨1358484, by rfl⟩ : syracuseStep 3622625 = 2716969) B2716969
theorem B55797821 : Blo 1609003 55797821 := bstep (se 3 (by rfl) ⟨10462091, by rfl⟩ : syracuseStep 55797821 = 20924183) B20924183
theorem B15477263 : Blo 1609003 15477263 := bstep (se 1 (by rfl) ⟨11607947, by rfl⟩ : syracuseStep 15477263 = 23215895) B23215895
theorem B2903033 : Blo 1609003 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B1609343 : Blo 1609003 1609343 := bstep (se 1 (by rfl) ⟨1207007, by rfl⟩ : syracuseStep 1609343 = 2414015) B2414015
theorem B84831877 : Blo 1609003 84831877 := bstep (se 4 (by rfl) ⟨7952988, by rfl⟩ : syracuseStep 84831877 = 15905977) B15905977
theorem B6525143 : Blo 1609003 6525143 := bstep (se 1 (by rfl) ⟨4893857, by rfl⟩ : syracuseStep 6525143 = 9787715) B9787715
theorem B4075859 : Blo 1609003 4075859 := bstep (se 1 (by rfl) ⟨3056894, by rfl⟩ : syracuseStep 4075859 = 6113789) B6113789
theorem B1610399 : Blo 1609003 1610399 := bstep (se 1 (by rfl) ⟨1207799, by rfl⟩ : syracuseStep 1610399 = 2415599) B2415599
theorem B1610919 : Blo 1609003 1610919 := bstep (se 1 (by rfl) ⟨1208189, by rfl⟩ : syracuseStep 1610919 = 2416379) B2416379
theorem B2037631 : Blo 1609003 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B2415743 : Blo 1609003 2415743 := bstep (se 1 (by rfl) ⟨1811807, by rfl⟩ : syracuseStep 2415743 = 3623615) B3623615
theorem B17882855 : Blo 1609003 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B4350095 : Blo 1609003 4350095 := bstep (se 1 (by rfl) ⟨3262571, by rfl⟩ : syracuseStep 4350095 = 6525143) B6525143
theorem B5800585 : Blo 1609003 5800585 := bstep (se 2 (by rfl) ⟨2175219, by rfl⟩ : syracuseStep 5800585 = 4350439) B4350439
theorem B1935355 : Blo 1609003 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B113109169 : Blo 1609003 113109169 := bstep (se 2 (by rfl) ⟨42415938, by rfl⟩ : syracuseStep 113109169 = 84831877) B84831877
theorem B11921903 : Blo 1609003 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B10318175 : Blo 1609003 10318175 := bstep (se 1 (by rfl) ⟨7738631, by rfl⟩ : syracuseStep 10318175 = 15477263) B15477263
theorem B1610495 : Blo 1609003 1610495 := bstep (se 1 (by rfl) ⟨1207871, by rfl⟩ : syracuseStep 1610495 = 2415743) B2415743
theorem B2716841 : Blo 1609003 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B2717239 : Blo 1609003 2717239 := bstep (se 1 (by rfl) ⟨2037929, by rfl⟩ : syracuseStep 2717239 = 4075859) B4075859
theorem B2415083 : Blo 1609003 2415083 := bstep (se 1 (by rfl) ⟨1811312, by rfl⟩ : syracuseStep 2415083 = 3622625) B3622625
theorem B37198547 : Blo 1609003 37198547 := bstep (se 1 (by rfl) ⟨27898910, by rfl⟩ : syracuseStep 37198547 = 55797821) B55797821
theorem B2416169 : Blo 1609003 2416169 := bstep (se 2 (by rfl) ⟨906063, by rfl⟩ : syracuseStep 2416169 = 1812127) B1812127
theorem B2900063 : Blo 1609003 2900063 := bstep (se 1 (by rfl) ⟨2175047, by rfl⟩ : syracuseStep 2900063 = 4350095) B4350095
theorem B1811227 : Blo 1609003 1811227 := bstep (se 1 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 1811227 = 2716841) B2716841
theorem B7734113 : Blo 1609003 7734113 := bstep (se 2 (by rfl) ⟨2900292, by rfl⟩ : syracuseStep 7734113 = 5800585) B5800585
theorem B7947935 : Blo 1609003 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B24799031 : Blo 1609003 24799031 := bstep (se 1 (by rfl) ⟨18599273, by rfl⟩ : syracuseStep 24799031 = 37198547) B37198547
theorem B3622985 : Blo 1609003 3622985 := bstep (se 2 (by rfl) ⟨1358619, by rfl⟩ : syracuseStep 3622985 = 2717239) B2717239
theorem B1610055 : Blo 1609003 1610055 := bstep (se 1 (by rfl) ⟨1207541, by rfl⟩ : syracuseStep 1610055 = 2415083) B2415083
theorem B1610779 : Blo 1609003 1610779 := bstep (se 1 (by rfl) ⟨1208084, by rfl⟩ : syracuseStep 1610779 = 2416169) B2416169
theorem B6878783 : Blo 1609003 6878783 := bstep (se 1 (by rfl) ⟨5159087, by rfl⟩ : syracuseStep 6878783 = 10318175) B10318175
theorem B150812225 : Blo 1609003 150812225 := bstep (se 2 (by rfl) ⟨56554584, by rfl⟩ : syracuseStep 150812225 = 113109169) B113109169
theorem B2580473 : Blo 1609003 2580473 := bstep (se 2 (by rfl) ⟨967677, by rfl⟩ : syracuseStep 2580473 = 1935355) B1935355
theorem B1933375 : Blo 1609003 1933375 := bstep (se 1 (by rfl) ⟨1450031, by rfl⟩ : syracuseStep 1933375 = 2900063) B2900063
theorem B100541483 : Blo 1609003 100541483 := bstep (se 1 (by rfl) ⟨75406112, by rfl⟩ : syracuseStep 100541483 = 150812225) B150812225
theorem B16532687 : Blo 1609003 16532687 := bstep (se 1 (by rfl) ⟨12399515, by rfl⟩ : syracuseStep 16532687 = 24799031) B24799031
theorem B5156075 : Blo 1609003 5156075 := bstep (se 1 (by rfl) ⟨3867056, by rfl⟩ : syracuseStep 5156075 = 7734113) B7734113
theorem B2414969 : Blo 1609003 2414969 := bstep (se 2 (by rfl) ⟨905613, by rfl⟩ : syracuseStep 2414969 = 1811227) B1811227
theorem B4585855 : Blo 1609003 4585855 := bstep (se 1 (by rfl) ⟨3439391, by rfl⟩ : syracuseStep 4585855 = 6878783) B6878783
theorem B5298623 : Blo 1609003 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B2415323 : Blo 1609003 2415323 := bstep (se 1 (by rfl) ⟨1811492, by rfl⟩ : syracuseStep 2415323 = 3622985) B3622985
theorem B1720315 : Blo 1609003 1720315 := bstep (se 1 (by rfl) ⟨1290236, by rfl⟩ : syracuseStep 1720315 = 2580473) B2580473
theorem B67027655 : Blo 1609003 67027655 := bstep (se 1 (by rfl) ⟨50270741, by rfl⟩ : syracuseStep 67027655 = 100541483) B100541483
theorem B3532415 : Blo 1609003 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B6114473 : Blo 1609003 6114473 := bstep (se 2 (by rfl) ⟨2292927, by rfl⟩ : syracuseStep 6114473 = 4585855) B4585855
theorem B13749533 : Blo 1609003 13749533 := bstep (se 3 (by rfl) ⟨2578037, by rfl⟩ : syracuseStep 13749533 = 5156075) B5156075
theorem B1609979 : Blo 1609003 1609979 := bstep (se 1 (by rfl) ⟨1207484, by rfl⟩ : syracuseStep 1609979 = 2414969) B2414969
theorem B1610215 : Blo 1609003 1610215 := bstep (se 1 (by rfl) ⟨1207661, by rfl⟩ : syracuseStep 1610215 = 2415323) B2415323
theorem B2577833 : Blo 1609003 2577833 := bstep (se 2 (by rfl) ⟨966687, by rfl⟩ : syracuseStep 2577833 = 1933375) B1933375
theorem B44087165 : Blo 1609003 44087165 := bstep (se 3 (by rfl) ⟨8266343, by rfl⟩ : syracuseStep 44087165 = 16532687) B16532687
theorem B2293753 : Blo 1609003 2293753 := bstep (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) B1720315
theorem B3058337 : Blo 1609003 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B37679093 : Blo 1609003 37679093 := bstep (se 5 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 37679093 = 3532415) B3532415
theorem B4076315 : Blo 1609003 4076315 := bstep (se 1 (by rfl) ⟨3057236, by rfl⟩ : syracuseStep 4076315 = 6114473) B6114473
theorem B44685103 : Blo 1609003 44685103 := bstep (se 1 (by rfl) ⟨33513827, by rfl⟩ : syracuseStep 44685103 = 67027655) B67027655
theorem B1718555 : Blo 1609003 1718555 := bstep (se 1 (by rfl) ⟨1288916, by rfl⟩ : syracuseStep 1718555 = 2577833) B2577833
theorem B29391443 : Blo 1609003 29391443 := bstep (se 1 (by rfl) ⟨22043582, by rfl⟩ : syracuseStep 29391443 = 44087165) B44087165
theorem B9166355 : Blo 1609003 9166355 := bstep (se 1 (by rfl) ⟨6874766, by rfl⟩ : syracuseStep 9166355 = 13749533) B13749533
theorem B25119395 : Blo 1609003 25119395 := bstep (se 1 (by rfl) ⟨18839546, by rfl⟩ : syracuseStep 25119395 = 37679093) B37679093
theorem B4582813 : Blo 1609003 4582813 := bstep (se 3 (by rfl) ⟨859277, by rfl⟩ : syracuseStep 4582813 = 1718555) B1718555
theorem B8155565 : Blo 1609003 8155565 := bstep (se 3 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 8155565 = 3058337) B3058337
theorem B2717543 : Blo 1609003 2717543 := bstep (se 1 (by rfl) ⟨2038157, by rfl⟩ : syracuseStep 2717543 = 4076315) B4076315
theorem B19594295 : Blo 1609003 19594295 := bstep (se 1 (by rfl) ⟨14695721, by rfl⟩ : syracuseStep 19594295 = 29391443) B29391443
theorem B6110903 : Blo 1609003 6110903 := bstep (se 1 (by rfl) ⟨4583177, by rfl⟩ : syracuseStep 6110903 = 9166355) B9166355
theorem B59580137 : Blo 1609003 59580137 := bstep (se 2 (by rfl) ⟨22342551, by rfl⟩ : syracuseStep 59580137 = 44685103) B44685103
theorem B1811695 : Blo 1609003 1811695 := bstep (se 1 (by rfl) ⟨1358771, by rfl⟩ : syracuseStep 1811695 = 2717543) B2717543
theorem B16746263 : Blo 1609003 16746263 := bstep (se 1 (by rfl) ⟨12559697, by rfl⟩ : syracuseStep 16746263 = 25119395) B25119395
theorem B4073935 : Blo 1609003 4073935 := bstep (se 1 (by rfl) ⟨3055451, by rfl⟩ : syracuseStep 4073935 = 6110903) B6110903
theorem B158880365 : Blo 1609003 158880365 := bstep (se 3 (by rfl) ⟨29790068, by rfl⟩ : syracuseStep 158880365 = 59580137) B59580137
theorem B13062863 : Blo 1609003 13062863 := bstep (se 1 (by rfl) ⟨9797147, by rfl⟩ : syracuseStep 13062863 = 19594295) B19594295
theorem B5437043 : Blo 1609003 5437043 := bstep (se 1 (by rfl) ⟨4077782, by rfl⟩ : syracuseStep 5437043 = 8155565) B8155565
theorem B6110417 : Blo 1609003 6110417 := bstep (se 2 (by rfl) ⟨2291406, by rfl⟩ : syracuseStep 6110417 = 4582813) B4582813
theorem B8708575 : Blo 1609003 8708575 := bstep (se 1 (by rfl) ⟨6531431, by rfl⟩ : syracuseStep 8708575 = 13062863) B13062863
theorem B5431913 : Blo 1609003 5431913 := bstep (se 2 (by rfl) ⟨2036967, by rfl⟩ : syracuseStep 5431913 = 4073935) B4073935
theorem B4073611 : Blo 1609003 4073611 := bstep (se 1 (by rfl) ⟨3055208, by rfl⟩ : syracuseStep 4073611 = 6110417) B6110417
theorem B3624695 : Blo 1609003 3624695 := bstep (se 1 (by rfl) ⟨2718521, by rfl⟩ : syracuseStep 3624695 = 5437043) B5437043
theorem B105920243 : Blo 1609003 105920243 := bstep (se 1 (by rfl) ⟨79440182, by rfl⟩ : syracuseStep 105920243 = 158880365) B158880365
theorem B11164175 : Blo 1609003 11164175 := bstep (se 1 (by rfl) ⟨8373131, by rfl⟩ : syracuseStep 11164175 = 16746263) B16746263
theorem B2415593 : Blo 1609003 2415593 := bstep (se 2 (by rfl) ⟨905847, by rfl⟩ : syracuseStep 2415593 = 1811695) B1811695
theorem B5431481 : Blo 1609003 5431481 := bstep (se 2 (by rfl) ⟨2036805, by rfl⟩ : syracuseStep 5431481 = 4073611) B4073611
theorem B3621275 : Blo 1609003 3621275 := bstep (se 1 (by rfl) ⟨2715956, by rfl⟩ : syracuseStep 3621275 = 5431913) B5431913
theorem B11611433 : Blo 1609003 11611433 := bstep (se 2 (by rfl) ⟨4354287, by rfl⟩ : syracuseStep 11611433 = 8708575) B8708575
theorem B7442783 : Blo 1609003 7442783 := bstep (se 1 (by rfl) ⟨5582087, by rfl⟩ : syracuseStep 7442783 = 11164175) B11164175
theorem B1610395 : Blo 1609003 1610395 := bstep (se 1 (by rfl) ⟨1207796, by rfl⟩ : syracuseStep 1610395 = 2415593) B2415593
theorem B70613495 : Blo 1609003 70613495 := bstep (se 1 (by rfl) ⟨52960121, by rfl⟩ : syracuseStep 70613495 = 105920243) B105920243
theorem B2416463 : Blo 1609003 2416463 := bstep (se 1 (by rfl) ⟨1812347, by rfl⟩ : syracuseStep 2416463 = 3624695) B3624695
theorem B3620987 : Blo 1609003 3620987 := bstep (se 1 (by rfl) ⟨2715740, by rfl⟩ : syracuseStep 3620987 = 5431481) B5431481
theorem B47075663 : Blo 1609003 47075663 := bstep (se 1 (by rfl) ⟨35306747, by rfl⟩ : syracuseStep 47075663 = 70613495) B70613495
theorem B1610975 : Blo 1609003 1610975 := bstep (se 1 (by rfl) ⟨1208231, by rfl⟩ : syracuseStep 1610975 = 2416463) B2416463
theorem B4961855 : Blo 1609003 4961855 := bstep (se 1 (by rfl) ⟨3721391, by rfl⟩ : syracuseStep 4961855 = 7442783) B7442783
theorem B2414183 : Blo 1609003 2414183 := bstep (se 1 (by rfl) ⟨1810637, by rfl⟩ : syracuseStep 2414183 = 3621275) B3621275
theorem B7740955 : Blo 1609003 7740955 := bstep (se 1 (by rfl) ⟨5805716, by rfl⟩ : syracuseStep 7740955 = 11611433) B11611433
theorem B31383775 : Blo 1609003 31383775 := bstep (se 1 (by rfl) ⟨23537831, by rfl⟩ : syracuseStep 31383775 = 47075663) B47075663
theorem B13231613 : Blo 1609003 13231613 := bstep (se 3 (by rfl) ⟨2480927, by rfl⟩ : syracuseStep 13231613 = 4961855) B4961855
theorem B1609455 : Blo 1609003 1609455 := bstep (se 1 (by rfl) ⟨1207091, by rfl⟩ : syracuseStep 1609455 = 2414183) B2414183
theorem B2413991 : Blo 1609003 2413991 := bstep (se 1 (by rfl) ⟨1810493, by rfl⟩ : syracuseStep 2413991 = 3620987) B3620987
theorem B10321273 : Blo 1609003 10321273 := bstep (se 2 (by rfl) ⟨3870477, by rfl⟩ : syracuseStep 10321273 = 7740955) B7740955
theorem B41845033 : Blo 1609003 41845033 := bstep (se 2 (by rfl) ⟨15691887, by rfl⟩ : syracuseStep 41845033 = 31383775) B31383775
theorem B35284301 : Blo 1609003 35284301 := bstep (se 3 (by rfl) ⟨6615806, by rfl⟩ : syracuseStep 35284301 = 13231613) B13231613
theorem B1609327 : Blo 1609003 1609327 := bstep (se 1 (by rfl) ⟨1206995, by rfl⟩ : syracuseStep 1609327 = 2413991) B2413991
theorem B13761697 : Blo 1609003 13761697 := bstep (se 2 (by rfl) ⟨5160636, by rfl⟩ : syracuseStep 13761697 = 10321273) B10321273
theorem B23522867 : Blo 1609003 23522867 := bstep (se 1 (by rfl) ⟨17642150, by rfl⟩ : syracuseStep 23522867 = 35284301) B35284301
theorem B55793377 : Blo 1609003 55793377 := bstep (se 2 (by rfl) ⟨20922516, by rfl⟩ : syracuseStep 55793377 = 41845033) B41845033
theorem B18348929 : Blo 1609003 18348929 := bstep (se 2 (by rfl) ⟨6880848, by rfl⟩ : syracuseStep 18348929 = 13761697) B13761697
theorem B12232619 : Blo 1609003 12232619 := bstep (se 1 (by rfl) ⟨9174464, by rfl⟩ : syracuseStep 12232619 = 18348929) B18348929
theorem B250910581 : Blo 1609003 250910581 := bstep (se 5 (by rfl) ⟨11761433, by rfl⟩ : syracuseStep 250910581 = 23522867) B23522867
theorem B297564677 : Blo 1609003 297564677 := bstep (se 4 (by rfl) ⟨27896688, by rfl⟩ : syracuseStep 297564677 = 55793377) B55793377
theorem B334547441 : Blo 1609003 334547441 := bstep (se 2 (by rfl) ⟨125455290, by rfl⟩ : syracuseStep 334547441 = 250910581) B250910581
theorem B8155079 : Blo 1609003 8155079 := bstep (se 1 (by rfl) ⟨6116309, by rfl⟩ : syracuseStep 8155079 = 12232619) B12232619
theorem B198376451 : Blo 1609003 198376451 := bstep (se 1 (by rfl) ⟨148782338, by rfl⟩ : syracuseStep 198376451 = 297564677) B297564677
theorem B223031627 : Blo 1609003 223031627 := bstep (se 1 (by rfl) ⟨167273720, by rfl⟩ : syracuseStep 223031627 = 334547441) B334547441
theorem B5436719 : Blo 1609003 5436719 := bstep (se 1 (by rfl) ⟨4077539, by rfl⟩ : syracuseStep 5436719 = 8155079) B8155079
theorem B132250967 : Blo 1609003 132250967 := bstep (se 1 (by rfl) ⟨99188225, by rfl⟩ : syracuseStep 132250967 = 198376451) B198376451
theorem B148687751 : Blo 1609003 148687751 := bstep (se 1 (by rfl) ⟨111515813, by rfl⟩ : syracuseStep 148687751 = 223031627) B223031627
theorem B3624479 : Blo 1609003 3624479 := bstep (se 1 (by rfl) ⟨2718359, by rfl⟩ : syracuseStep 3624479 = 5436719) B5436719
theorem B88167311 : Blo 1609003 88167311 := bstep (se 1 (by rfl) ⟨66125483, by rfl⟩ : syracuseStep 88167311 = 132250967) B132250967
theorem B58778207 : Blo 1609003 58778207 := bstep (se 1 (by rfl) ⟨44083655, by rfl⟩ : syracuseStep 58778207 = 88167311) B88167311
theorem B99125167 : Blo 1609003 99125167 := bstep (se 1 (by rfl) ⟨74343875, by rfl⟩ : syracuseStep 99125167 = 148687751) B148687751
theorem B2416319 : Blo 1609003 2416319 := bstep (se 1 (by rfl) ⟨1812239, by rfl⟩ : syracuseStep 2416319 = 3624479) B3624479
theorem B39185471 : Blo 1609003 39185471 := bstep (se 1 (by rfl) ⟨29389103, by rfl⟩ : syracuseStep 39185471 = 58778207) B58778207
theorem B1610879 : Blo 1609003 1610879 := bstep (se 1 (by rfl) ⟨1208159, by rfl⟩ : syracuseStep 1610879 = 2416319) B2416319
theorem B132166889 : Blo 1609003 132166889 := bstep (se 2 (by rfl) ⟨49562583, by rfl⟩ : syracuseStep 132166889 = 99125167) B99125167
theorem B88111259 : Blo 1609003 88111259 := bstep (se 1 (by rfl) ⟨66083444, by rfl⟩ : syracuseStep 88111259 = 132166889) B132166889
theorem B26123647 : Blo 1609003 26123647 := bstep (se 1 (by rfl) ⟨19592735, by rfl⟩ : syracuseStep 26123647 = 39185471) B39185471
theorem B58740839 : Blo 1609003 58740839 := bstep (se 1 (by rfl) ⟨44055629, by rfl⟩ : syracuseStep 58740839 = 88111259) B88111259
theorem B34831529 : Blo 1609003 34831529 := bstep (se 2 (by rfl) ⟨13061823, by rfl⟩ : syracuseStep 34831529 = 26123647) B26123647
theorem B39160559 : Blo 1609003 39160559 := bstep (se 1 (by rfl) ⟨29370419, by rfl⟩ : syracuseStep 39160559 = 58740839) B58740839
theorem B23221019 : Blo 1609003 23221019 := bstep (se 1 (by rfl) ⟨17415764, by rfl⟩ : syracuseStep 23221019 = 34831529) B34831529
theorem B26107039 : Blo 1609003 26107039 := bstep (se 1 (by rfl) ⟨19580279, by rfl⟩ : syracuseStep 26107039 = 39160559) B39160559
theorem B61922717 : Blo 1609003 61922717 := bstep (se 3 (by rfl) ⟨11610509, by rfl⟩ : syracuseStep 61922717 = 23221019) B23221019
theorem B41281811 : Blo 1609003 41281811 := bstep (se 1 (by rfl) ⟨30961358, by rfl⟩ : syracuseStep 41281811 = 61922717) B61922717
theorem B139237541 : Blo 1609003 139237541 := bstep (se 4 (by rfl) ⟨13053519, by rfl⟩ : syracuseStep 139237541 = 26107039) B26107039
theorem B92825027 : Blo 1609003 92825027 := bstep (se 1 (by rfl) ⟨69618770, by rfl⟩ : syracuseStep 92825027 = 139237541) B139237541
theorem B27521207 : Blo 1609003 27521207 := bstep (se 1 (by rfl) ⟨20640905, by rfl⟩ : syracuseStep 27521207 = 41281811) B41281811
theorem B61883351 : Blo 1609003 61883351 := bstep (se 1 (by rfl) ⟨46412513, by rfl⟩ : syracuseStep 61883351 = 92825027) B92825027
theorem B18347471 : Blo 1609003 18347471 := bstep (se 1 (by rfl) ⟨13760603, by rfl⟩ : syracuseStep 18347471 = 27521207) B27521207
theorem B41255567 : Blo 1609003 41255567 := bstep (se 1 (by rfl) ⟨30941675, by rfl⟩ : syracuseStep 41255567 = 61883351) B61883351
theorem B12231647 : Blo 1609003 12231647 := bstep (se 1 (by rfl) ⟨9173735, by rfl⟩ : syracuseStep 12231647 = 18347471) B18347471
theorem B27503711 : Blo 1609003 27503711 := bstep (se 1 (by rfl) ⟨20627783, by rfl⟩ : syracuseStep 27503711 = 41255567) B41255567
theorem B8154431 : Blo 1609003 8154431 := bstep (se 1 (by rfl) ⟨6115823, by rfl⟩ : syracuseStep 8154431 = 12231647) B12231647
theorem B18335807 : Blo 1609003 18335807 := bstep (se 1 (by rfl) ⟨13751855, by rfl⟩ : syracuseStep 18335807 = 27503711) B27503711
theorem B5436287 : Blo 1609003 5436287 := bstep (se 1 (by rfl) ⟨4077215, by rfl⟩ : syracuseStep 5436287 = 8154431) B8154431
theorem B12223871 : Blo 1609003 12223871 := bstep (se 1 (by rfl) ⟨9167903, by rfl⟩ : syracuseStep 12223871 = 18335807) B18335807
theorem B3624191 : Blo 1609003 3624191 := bstep (se 1 (by rfl) ⟨2718143, by rfl⟩ : syracuseStep 3624191 = 5436287) B5436287
theorem B8149247 : Blo 1609003 8149247 := bstep (se 1 (by rfl) ⟨6111935, by rfl⟩ : syracuseStep 8149247 = 12223871) B12223871
theorem B2416127 : Blo 1609003 2416127 := bstep (se 1 (by rfl) ⟨1812095, by rfl⟩ : syracuseStep 2416127 = 3624191) B3624191
theorem B5432831 : Blo 1609003 5432831 := bstep (se 1 (by rfl) ⟨4074623, by rfl⟩ : syracuseStep 5432831 = 8149247) B8149247
theorem B1610751 : Blo 1609003 1610751 := bstep (se 1 (by rfl) ⟨1208063, by rfl⟩ : syracuseStep 1610751 = 2416127) B2416127
theorem B3621887 : Blo 1609003 3621887 := bstep (se 1 (by rfl) ⟨2716415, by rfl⟩ : syracuseStep 3621887 = 5432831) B5432831
theorem B2414591 : Blo 1609003 2414591 := bstep (se 1 (by rfl) ⟨1810943, by rfl⟩ : syracuseStep 2414591 = 3621887) B3621887
theorem B1609727 : Blo 1609003 1609727 := bstep (se 1 (by rfl) ⟨1207295, by rfl⟩ : syracuseStep 1609727 = 2414591) B2414591

theorem C0 (j : ℕ) (h1 : 402250 ≤ j) (h2 : j ≤ 402750) : Blo 1609003 (4 * j + 3) := by
  interval_cases j
  · exact B1609003
  · exact B1609007
  · exact B1609011
  · exact B1609015
  · exact B1609019
  · exact B1609023
  · exact B1609027
  · exact B1609031
  · exact B1609035
  · exact B1609039
  · exact B1609043
  · exact B1609047
  · exact B1609051
  · exact B1609055
  · exact B1609059
  · exact B1609063
  · exact B1609067
  · exact B1609071
  · exact B1609075
  · exact B1609079
  · exact B1609083
  · exact B1609087
  · exact B1609091
  · exact B1609095
  · exact B1609099
  · exact B1609103
  · exact B1609107
  · exact B1609111
  · exact B1609115
  · exact B1609119
  · exact B1609123
  · exact B1609127
  · exact B1609131
  · exact B1609135
  · exact B1609139
  · exact B1609143
  · exact B1609147
  · exact B1609151
  · exact B1609155
  · exact B1609159
  · exact B1609163
  · exact B1609167
  · exact B1609171
  · exact B1609175
  · exact B1609179
  · exact B1609183
  · exact B1609187
  · exact B1609191
  · exact B1609195
  · exact B1609199
  · exact B1609203
  · exact B1609207
  · exact B1609211
  · exact B1609215
  · exact B1609219
  · exact B1609223
  · exact B1609227
  · exact B1609231
  · exact B1609235
  · exact B1609239
  · exact B1609243
  · exact B1609247
  · exact B1609251
  · exact B1609255
  · exact B1609259
  · exact B1609263
  · exact B1609267
  · exact B1609271
  · exact B1609275
  · exact B1609279
  · exact B1609283
  · exact B1609287
  · exact B1609291
  · exact B1609295
  · exact B1609299
  · exact B1609303
  · exact B1609307
  · exact B1609311
  · exact B1609315
  · exact B1609319
  · exact B1609323
  · exact B1609327
  · exact B1609331
  · exact B1609335
  · exact B1609339
  · exact B1609343
  · exact B1609347
  · exact B1609351
  · exact B1609355
  · exact B1609359
  · exact B1609363
  · exact B1609367
  · exact B1609371
  · exact B1609375
  · exact B1609379
  · exact B1609383
  · exact B1609387
  · exact B1609391
  · exact B1609395
  · exact B1609399
  · exact B1609403
  · exact B1609407
  · exact B1609411
  · exact B1609415
  · exact B1609419
  · exact B1609423
  · exact B1609427
  · exact B1609431
  · exact B1609435
  · exact B1609439
  · exact B1609443
  · exact B1609447
  · exact B1609451
  · exact B1609455
  · exact B1609459
  · exact B1609463
  · exact B1609467
  · exact B1609471
  · exact B1609475
  · exact B1609479
  · exact B1609483
  · exact B1609487
  · exact B1609491
  · exact B1609495
  · exact B1609499
  · exact B1609503
  · exact B1609507
  · exact B1609511
  · exact B1609515
  · exact B1609519
  · exact B1609523
  · exact B1609527
  · exact B1609531
  · exact B1609535
  · exact B1609539
  · exact B1609543
  · exact B1609547
  · exact B1609551
  · exact B1609555
  · exact B1609559
  · exact B1609563
  · exact B1609567
  · exact B1609571
  · exact B1609575
  · exact B1609579
  · exact B1609583
  · exact B1609587
  · exact B1609591
  · exact B1609595
  · exact B1609599
  · exact B1609603
  · exact B1609607
  · exact B1609611
  · exact B1609615
  · exact B1609619
  · exact B1609623
  · exact B1609627
  · exact B1609631
  · exact B1609635
  · exact B1609639
  · exact B1609643
  · exact B1609647
  · exact B1609651
  · exact B1609655
  · exact B1609659
  · exact B1609663
  · exact B1609667
  · exact B1609671
  · exact B1609675
  · exact B1609679
  · exact B1609683
  · exact B1609687
  · exact B1609691
  · exact B1609695
  · exact B1609699
  · exact B1609703
  · exact B1609707
  · exact B1609711
  · exact B1609715
  · exact B1609719
  · exact B1609723
  · exact B1609727
  · exact B1609731
  · exact B1609735
  · exact B1609739
  · exact B1609743
  · exact B1609747
  · exact B1609751
  · exact B1609755
  · exact B1609759
  · exact B1609763
  · exact B1609767
  · exact B1609771
  · exact B1609775
  · exact B1609779
  · exact B1609783
  · exact B1609787
  · exact B1609791
  · exact B1609795
  · exact B1609799
  · exact B1609803
  · exact B1609807
  · exact B1609811
  · exact B1609815
  · exact B1609819
  · exact B1609823
  · exact B1609827
  · exact B1609831
  · exact B1609835
  · exact B1609839
  · exact B1609843
  · exact B1609847
  · exact B1609851
  · exact B1609855
  · exact B1609859
  · exact B1609863
  · exact B1609867
  · exact B1609871
  · exact B1609875
  · exact B1609879
  · exact B1609883
  · exact B1609887
  · exact B1609891
  · exact B1609895
  · exact B1609899
  · exact B1609903
  · exact B1609907
  · exact B1609911
  · exact B1609915
  · exact B1609919
  · exact B1609923
  · exact B1609927
  · exact B1609931
  · exact B1609935
  · exact B1609939
  · exact B1609943
  · exact B1609947
  · exact B1609951
  · exact B1609955
  · exact B1609959
  · exact B1609963
  · exact B1609967
  · exact B1609971
  · exact B1609975
  · exact B1609979
  · exact B1609983
  · exact B1609987
  · exact B1609991
  · exact B1609995
  · exact B1609999
  · exact B1610003
  · exact B1610007
  · exact B1610011
  · exact B1610015
  · exact B1610019
  · exact B1610023
  · exact B1610027
  · exact B1610031
  · exact B1610035
  · exact B1610039
  · exact B1610043
  · exact B1610047
  · exact B1610051
  · exact B1610055
  · exact B1610059
  · exact B1610063
  · exact B1610067
  · exact B1610071
  · exact B1610075
  · exact B1610079
  · exact B1610083
  · exact B1610087
  · exact B1610091
  · exact B1610095
  · exact B1610099
  · exact B1610103
  · exact B1610107
  · exact B1610111
  · exact B1610115
  · exact B1610119
  · exact B1610123
  · exact B1610127
  · exact B1610131
  · exact B1610135
  · exact B1610139
  · exact B1610143
  · exact B1610147
  · exact B1610151
  · exact B1610155
  · exact B1610159
  · exact B1610163
  · exact B1610167
  · exact B1610171
  · exact B1610175
  · exact B1610179
  · exact B1610183
  · exact B1610187
  · exact B1610191
  · exact B1610195
  · exact B1610199
  · exact B1610203
  · exact B1610207
  · exact B1610211
  · exact B1610215
  · exact B1610219
  · exact B1610223
  · exact B1610227
  · exact B1610231
  · exact B1610235
  · exact B1610239
  · exact B1610243
  · exact B1610247
  · exact B1610251
  · exact B1610255
  · exact B1610259
  · exact B1610263
  · exact B1610267
  · exact B1610271
  · exact B1610275
  · exact B1610279
  · exact B1610283
  · exact B1610287
  · exact B1610291
  · exact B1610295
  · exact B1610299
  · exact B1610303
  · exact B1610307
  · exact B1610311
  · exact B1610315
  · exact B1610319
  · exact B1610323
  · exact B1610327
  · exact B1610331
  · exact B1610335
  · exact B1610339
  · exact B1610343
  · exact B1610347
  · exact B1610351
  · exact B1610355
  · exact B1610359
  · exact B1610363
  · exact B1610367
  · exact B1610371
  · exact B1610375
  · exact B1610379
  · exact B1610383
  · exact B1610387
  · exact B1610391
  · exact B1610395
  · exact B1610399
  · exact B1610403
  · exact B1610407
  · exact B1610411
  · exact B1610415
  · exact B1610419
  · exact B1610423
  · exact B1610427
  · exact B1610431
  · exact B1610435
  · exact B1610439
  · exact B1610443
  · exact B1610447
  · exact B1610451
  · exact B1610455
  · exact B1610459
  · exact B1610463
  · exact B1610467
  · exact B1610471
  · exact B1610475
  · exact B1610479
  · exact B1610483
  · exact B1610487
  · exact B1610491
  · exact B1610495
  · exact B1610499
  · exact B1610503
  · exact B1610507
  · exact B1610511
  · exact B1610515
  · exact B1610519
  · exact B1610523
  · exact B1610527
  · exact B1610531
  · exact B1610535
  · exact B1610539
  · exact B1610543
  · exact B1610547
  · exact B1610551
  · exact B1610555
  · exact B1610559
  · exact B1610563
  · exact B1610567
  · exact B1610571
  · exact B1610575
  · exact B1610579
  · exact B1610583
  · exact B1610587
  · exact B1610591
  · exact B1610595
  · exact B1610599
  · exact B1610603
  · exact B1610607
  · exact B1610611
  · exact B1610615
  · exact B1610619
  · exact B1610623
  · exact B1610627
  · exact B1610631
  · exact B1610635
  · exact B1610639
  · exact B1610643
  · exact B1610647
  · exact B1610651
  · exact B1610655
  · exact B1610659
  · exact B1610663
  · exact B1610667
  · exact B1610671
  · exact B1610675
  · exact B1610679
  · exact B1610683
  · exact B1610687
  · exact B1610691
  · exact B1610695
  · exact B1610699
  · exact B1610703
  · exact B1610707
  · exact B1610711
  · exact B1610715
  · exact B1610719
  · exact B1610723
  · exact B1610727
  · exact B1610731
  · exact B1610735
  · exact B1610739
  · exact B1610743
  · exact B1610747
  · exact B1610751
  · exact B1610755
  · exact B1610759
  · exact B1610763
  · exact B1610767
  · exact B1610771
  · exact B1610775
  · exact B1610779
  · exact B1610783
  · exact B1610787
  · exact B1610791
  · exact B1610795
  · exact B1610799
  · exact B1610803
  · exact B1610807
  · exact B1610811
  · exact B1610815
  · exact B1610819
  · exact B1610823
  · exact B1610827
  · exact B1610831
  · exact B1610835
  · exact B1610839
  · exact B1610843
  · exact B1610847
  · exact B1610851
  · exact B1610855
  · exact B1610859
  · exact B1610863
  · exact B1610867
  · exact B1610871
  · exact B1610875
  · exact B1610879
  · exact B1610883
  · exact B1610887
  · exact B1610891
  · exact B1610895
  · exact B1610899
  · exact B1610903
  · exact B1610907
  · exact B1610911
  · exact B1610915
  · exact B1610919
  · exact B1610923
  · exact B1610927
  · exact B1610931
  · exact B1610935
  · exact B1610939
  · exact B1610943
  · exact B1610947
  · exact B1610951
  · exact B1610955
  · exact B1610959
  · exact B1610963
  · exact B1610967
  · exact B1610971
  · exact B1610975
  · exact B1610979
  · exact B1610983
  · exact B1610987
  · exact B1610991
  · exact B1610995
  · exact B1610999
  · exact B1611003

theorem solution (m : ℕ) (hlo : 1609003 ≤ m) (hhi : m ≤ 1611003) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 402250 ≤ j := by omega
    have hj2 : j ≤ 402750 := by omega
    have hb : Blo 1609003 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
