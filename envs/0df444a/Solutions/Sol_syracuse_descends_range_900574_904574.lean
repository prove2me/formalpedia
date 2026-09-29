-- Prove2me | solution 1 for syracuse_descends_range_900574_904574
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:48.706796+00:00
-- url     : https://prove2.me/submissions/f5e17d73-49fc-456c-af56-11aa3e01dac4

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


theorem B1015825 : Blo 900574 1015825 := bbase (se 2 (by rfl) ⟨380934, by rfl⟩ : syracuseStep 1015825 = 761869) (by norm_num)
theorem B1015861 : Blo 900574 1015861 := bbase (se 5 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 1015861 = 95237) (by norm_num)
theorem B2031677 : Blo 900574 2031677 := bbase (se 3 (by rfl) ⟨380939, by rfl⟩ : syracuseStep 2031677 = 761879) (by norm_num)
theorem B1015897 : Blo 900574 1015897 := bbase (se 2 (by rfl) ⟨380961, by rfl⟩ : syracuseStep 1015897 = 761923) (by norm_num)
theorem B1015933 : Blo 900574 1015933 := bbase (se 3 (by rfl) ⟨190487, by rfl⟩ : syracuseStep 1015933 = 380975) (by norm_num)
theorem B2031749 : Blo 900574 2031749 := bbase (se 4 (by rfl) ⟨190476, by rfl⟩ : syracuseStep 2031749 = 380953) (by norm_num)
theorem B1015969 : Blo 900574 1015969 := bbase (se 2 (by rfl) ⟨380988, by rfl⟩ : syracuseStep 1015969 = 761977) (by norm_num)
theorem B1736893 : Blo 900574 1736893 := bbase (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) (by norm_num)
theorem B1016005 : Blo 900574 1016005 := bbase (se 4 (by rfl) ⟨95250, by rfl⟩ : syracuseStep 1016005 = 190501) (by norm_num)
theorem B2031821 : Blo 900574 2031821 := bbase (se 3 (by rfl) ⟨380966, by rfl⟩ : syracuseStep 2031821 = 761933) (by norm_num)
theorem B1016041 : Blo 900574 1016041 := bbase (se 2 (by rfl) ⟨381015, by rfl⟩ : syracuseStep 1016041 = 762031) (by norm_num)
theorem B1736957 : Blo 900574 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1016077 : Blo 900574 1016077 := bbase (se 3 (by rfl) ⟨190514, by rfl⟩ : syracuseStep 1016077 = 381029) (by norm_num)
theorem B2031893 : Blo 900574 2031893 := bbase (se 6 (by rfl) ⟨47622, by rfl⟩ : syracuseStep 2031893 = 95245) (by norm_num)
theorem B1016113 : Blo 900574 1016113 := bbase (se 2 (by rfl) ⟨381042, by rfl⟩ : syracuseStep 1016113 = 762085) (by norm_num)
theorem B1016149 : Blo 900574 1016149 := bbase (se 10 (by rfl) ⟨1488, by rfl⟩ : syracuseStep 1016149 = 2977) (by norm_num)
theorem B5144917 : Blo 900574 5144917 := bbase (se 10 (by rfl) ⟨7536, by rfl⟩ : syracuseStep 5144917 = 15073) (by norm_num)
theorem B2031965 : Blo 900574 2031965 := bbase (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) (by norm_num)
theorem B1016185 : Blo 900574 1016185 := bbase (se 2 (by rfl) ⟨381069, by rfl⟩ : syracuseStep 1016185 = 762139) (by norm_num)
theorem B3047813 : Blo 900574 3047813 := bbase (se 4 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 3047813 = 571465) (by norm_num)
theorem B1016221 : Blo 900574 1016221 := bbase (se 3 (by rfl) ⟨190541, by rfl⟩ : syracuseStep 1016221 = 381083) (by norm_num)
theorem B2032037 : Blo 900574 2032037 := bbase (se 4 (by rfl) ⟨190503, by rfl⟩ : syracuseStep 2032037 = 381007) (by norm_num)
theorem B1016257 : Blo 900574 1016257 := bbase (se 2 (by rfl) ⟨381096, by rfl⟩ : syracuseStep 1016257 = 762193) (by norm_num)
theorem B1016293 : Blo 900574 1016293 := bbase (se 4 (by rfl) ⟨95277, by rfl⟩ : syracuseStep 1016293 = 190555) (by norm_num)
theorem B2032109 : Blo 900574 2032109 := bbase (se 3 (by rfl) ⟨381020, by rfl⟩ : syracuseStep 2032109 = 762041) (by norm_num)
theorem B1016329 : Blo 900574 1016329 := bbase (se 2 (by rfl) ⟨381123, by rfl⟩ : syracuseStep 1016329 = 762247) (by norm_num)
theorem B1016365 : Blo 900574 1016365 := bbase (se 3 (by rfl) ⟨190568, by rfl⟩ : syracuseStep 1016365 = 381137) (by norm_num)
theorem B2032181 : Blo 900574 2032181 := bbase (se 5 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 2032181 = 190517) (by norm_num)
theorem B1016401 : Blo 900574 1016401 := bbase (se 2 (by rfl) ⟨381150, by rfl⟩ : syracuseStep 1016401 = 762301) (by norm_num)
theorem B1016437 : Blo 900574 1016437 := bbase (se 5 (by rfl) ⟨47645, by rfl⟩ : syracuseStep 1016437 = 95291) (by norm_num)
theorem B2032253 : Blo 900574 2032253 := bbase (se 3 (by rfl) ⟨381047, by rfl⟩ : syracuseStep 2032253 = 762095) (by norm_num)
theorem B1016473 : Blo 900574 1016473 := bbase (se 2 (by rfl) ⟨381177, by rfl⟩ : syracuseStep 1016473 = 762355) (by norm_num)
theorem B1016509 : Blo 900574 1016509 := bbase (se 3 (by rfl) ⟨190595, by rfl⟩ : syracuseStep 1016509 = 381191) (by norm_num)
theorem B2032325 : Blo 900574 2032325 := bbase (se 4 (by rfl) ⟨190530, by rfl⟩ : syracuseStep 2032325 = 381061) (by norm_num)
theorem B1016545 : Blo 900574 1016545 := bbase (se 2 (by rfl) ⟨381204, by rfl⟩ : syracuseStep 1016545 = 762409) (by norm_num)
theorem B1442549 : Blo 900574 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B2196229 : Blo 900574 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B1016581 : Blo 900574 1016581 := bbase (se 4 (by rfl) ⟨95304, by rfl⟩ : syracuseStep 1016581 = 190609) (by norm_num)
theorem B2032397 : Blo 900574 2032397 := bbase (se 3 (by rfl) ⟨381074, by rfl⟩ : syracuseStep 2032397 = 762149) (by norm_num)
theorem B1737509 : Blo 900574 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B1016617 : Blo 900574 1016617 := bbase (se 2 (by rfl) ⟨381231, by rfl⟩ : syracuseStep 1016617 = 762463) (by norm_num)
theorem B3048245 : Blo 900574 3048245 := bbase (se 5 (by rfl) ⟨142886, by rfl⟩ : syracuseStep 3048245 = 285773) (by norm_num)
theorem B1016653 : Blo 900574 1016653 := bbase (se 3 (by rfl) ⟨190622, by rfl⟩ : syracuseStep 1016653 = 381245) (by norm_num)
theorem B1540949 : Blo 900574 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B2032469 : Blo 900574 2032469 := bbase (se 9 (by rfl) ⟨5954, by rfl⟩ : syracuseStep 2032469 = 11909) (by norm_num)
theorem B1016689 : Blo 900574 1016689 := bbase (se 2 (by rfl) ⟨381258, by rfl⟩ : syracuseStep 1016689 = 762517) (by norm_num)
theorem B1016725 : Blo 900574 1016725 := bbase (se 6 (by rfl) ⟨23829, by rfl⟩ : syracuseStep 1016725 = 47659) (by norm_num)
theorem B2032541 : Blo 900574 2032541 := bbase (se 3 (by rfl) ⟨381101, by rfl⟩ : syracuseStep 2032541 = 762203) (by norm_num)
theorem B1016761 : Blo 900574 1016761 := bbase (se 2 (by rfl) ⟨381285, by rfl⟩ : syracuseStep 1016761 = 762571) (by norm_num)
theorem B1016797 : Blo 900574 1016797 := bbase (se 3 (by rfl) ⟨190649, by rfl⟩ : syracuseStep 1016797 = 381299) (by norm_num)
theorem B2032613 : Blo 900574 2032613 := bbase (se 4 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 2032613 = 381115) (by norm_num)
theorem B1082369 : Blo 900574 1082369 := bbase (se 2 (by rfl) ⟨405888, by rfl⟩ : syracuseStep 1082369 = 811777) (by norm_num)
theorem B1016833 : Blo 900574 1016833 := bbase (se 2 (by rfl) ⟨381312, by rfl⟩ : syracuseStep 1016833 = 762625) (by norm_num)
theorem B1016869 : Blo 900574 1016869 := bbase (se 4 (by rfl) ⟨95331, by rfl⟩ : syracuseStep 1016869 = 190663) (by norm_num)
theorem B2032685 : Blo 900574 2032685 := bbase (se 3 (by rfl) ⟨381128, by rfl⟩ : syracuseStep 2032685 = 762257) (by norm_num)
theorem B1016905 : Blo 900574 1016905 := bbase (se 2 (by rfl) ⟨381339, by rfl⟩ : syracuseStep 1016905 = 762679) (by norm_num)
theorem B1016941 : Blo 900574 1016941 := bbase (se 3 (by rfl) ⟨190676, by rfl⟩ : syracuseStep 1016941 = 381353) (by norm_num)
theorem B2032757 : Blo 900574 2032757 := bbase (se 5 (by rfl) ⟨95285, by rfl⟩ : syracuseStep 2032757 = 190571) (by norm_num)
theorem B1016977 : Blo 900574 1016977 := bbase (se 2 (by rfl) ⟨381366, by rfl⟩ : syracuseStep 1016977 = 762733) (by norm_num)
theorem B1017013 : Blo 900574 1017013 := bbase (se 5 (by rfl) ⟨47672, by rfl⟩ : syracuseStep 1017013 = 95345) (by norm_num)
theorem B1443005 : Blo 900574 1443005 := bbase (se 3 (by rfl) ⟨270563, by rfl⟩ : syracuseStep 1443005 = 541127) (by norm_num)
theorem B2032829 : Blo 900574 2032829 := bbase (se 3 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 2032829 = 762311) (by norm_num)
theorem B1017049 : Blo 900574 1017049 := bbase (se 2 (by rfl) ⟨381393, by rfl⟩ : syracuseStep 1017049 = 762787) (by norm_num)
theorem B3048677 : Blo 900574 3048677 := bbase (se 4 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 3048677 = 571627) (by norm_num)
theorem B1017085 : Blo 900574 1017085 := bbase (se 3 (by rfl) ⟨190703, by rfl⟩ : syracuseStep 1017085 = 381407) (by norm_num)
theorem B2032901 : Blo 900574 2032901 := bbase (se 4 (by rfl) ⟨190584, by rfl⟩ : syracuseStep 2032901 = 381169) (by norm_num)
theorem B1017121 : Blo 900574 1017121 := bbase (se 2 (by rfl) ⟨381420, by rfl⟩ : syracuseStep 1017121 = 762841) (by norm_num)
theorem B1017157 : Blo 900574 1017157 := bbase (se 4 (by rfl) ⟨95358, by rfl⟩ : syracuseStep 1017157 = 190717) (by norm_num)
theorem B2032973 : Blo 900574 2032973 := bbase (se 3 (by rfl) ⟨381182, by rfl⟩ : syracuseStep 2032973 = 762365) (by norm_num)
theorem B1017193 : Blo 900574 1017193 := bbase (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) (by norm_num)
theorem B1017229 : Blo 900574 1017229 := bbase (se 3 (by rfl) ⟨190730, by rfl⟩ : syracuseStep 1017229 = 381461) (by norm_num)
theorem B2033045 : Blo 900574 2033045 := bbase (se 6 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 2033045 = 95299) (by norm_num)
theorem B1017265 : Blo 900574 1017265 := bbase (se 2 (by rfl) ⟨381474, by rfl⟩ : syracuseStep 1017265 = 762949) (by norm_num)
theorem B1017301 : Blo 900574 1017301 := bbase (se 7 (by rfl) ⟨11921, by rfl⟩ : syracuseStep 1017301 = 23843) (by norm_num)
theorem B2033117 : Blo 900574 2033117 := bbase (se 3 (by rfl) ⟨381209, by rfl⟩ : syracuseStep 2033117 = 762419) (by norm_num)
theorem B1017337 : Blo 900574 1017337 := bbase (se 2 (by rfl) ⟨381501, by rfl⟩ : syracuseStep 1017337 = 763003) (by norm_num)
theorem B1017373 : Blo 900574 1017373 := bbase (se 3 (by rfl) ⟨190757, by rfl⟩ : syracuseStep 1017373 = 381515) (by norm_num)
theorem B2033189 : Blo 900574 2033189 := bbase (se 4 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 2033189 = 381223) (by norm_num)
theorem B1017409 : Blo 900574 1017409 := bbase (se 2 (by rfl) ⟨381528, by rfl⟩ : syracuseStep 1017409 = 763057) (by norm_num)
theorem B1017445 : Blo 900574 1017445 := bbase (se 4 (by rfl) ⟨95385, by rfl⟩ : syracuseStep 1017445 = 190771) (by norm_num)
theorem B2033261 : Blo 900574 2033261 := bbase (se 3 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 2033261 = 762473) (by norm_num)
theorem B1017481 : Blo 900574 1017481 := bbase (se 2 (by rfl) ⟨381555, by rfl⟩ : syracuseStep 1017481 = 763111) (by norm_num)
theorem B3049109 : Blo 900574 3049109 := bbase (se 6 (by rfl) ⟨71463, by rfl⟩ : syracuseStep 3049109 = 142927) (by norm_num)
theorem B1017517 : Blo 900574 1017517 := bbase (se 3 (by rfl) ⟨190784, by rfl⟩ : syracuseStep 1017517 = 381569) (by norm_num)
theorem B1083061 : Blo 900574 1083061 := bbase (se 5 (by rfl) ⟨50768, by rfl⟩ : syracuseStep 1083061 = 101537) (by norm_num)
theorem B2033333 : Blo 900574 2033333 := bbase (se 5 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 2033333 = 190625) (by norm_num)
theorem B1083065 : Blo 900574 1083065 := bbase (se 2 (by rfl) ⟨406149, by rfl⟩ : syracuseStep 1083065 = 812299) (by norm_num)
theorem B1017553 : Blo 900574 1017553 := bbase (se 2 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 1017553 = 763165) (by norm_num)
theorem B1017589 : Blo 900574 1017589 := bbase (se 5 (by rfl) ⟨47699, by rfl⟩ : syracuseStep 1017589 = 95399) (by norm_num)
theorem B2164477 : Blo 900574 2164477 := bbase (se 3 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 2164477 = 811679) (by norm_num)
theorem B2033405 : Blo 900574 2033405 := bbase (se 3 (by rfl) ⟨381263, by rfl⟩ : syracuseStep 2033405 = 762527) (by norm_num)
theorem B1017625 : Blo 900574 1017625 := bbase (se 2 (by rfl) ⟨381609, by rfl⟩ : syracuseStep 1017625 = 763219) (by norm_num)
theorem B2033477 : Blo 900574 2033477 := bbase (se 4 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 2033477 = 381277) (by norm_num)
theorem B2033549 : Blo 900574 2033549 := bbase (se 3 (by rfl) ⟨381290, by rfl⟩ : syracuseStep 2033549 = 762581) (by norm_num)
theorem B2033621 : Blo 900574 2033621 := bbase (se 7 (by rfl) ⟨23831, by rfl⟩ : syracuseStep 2033621 = 47663) (by norm_num)
theorem B2033693 : Blo 900574 2033693 := bbase (se 3 (by rfl) ⟨381317, by rfl⟩ : syracuseStep 2033693 = 762635) (by norm_num)
theorem B2885701 : Blo 900574 2885701 := bbase (se 4 (by rfl) ⟨270534, by rfl⟩ : syracuseStep 2885701 = 541069) (by norm_num)
theorem B3049541 : Blo 900574 3049541 := bbase (se 4 (by rfl) ⟨285894, by rfl⟩ : syracuseStep 3049541 = 571789) (by norm_num)
theorem B2033765 : Blo 900574 2033765 := bbase (se 4 (by rfl) ⟨190665, by rfl⟩ : syracuseStep 2033765 = 381331) (by norm_num)
theorem B1443997 : Blo 900574 1443997 := bbase (se 3 (by rfl) ⟨270749, by rfl⟩ : syracuseStep 1443997 = 541499) (by norm_num)
theorem B1083565 : Blo 900574 1083565 := bbase (se 3 (by rfl) ⟨203168, by rfl⟩ : syracuseStep 1083565 = 406337) (by norm_num)
theorem B2033837 : Blo 900574 2033837 := bbase (se 3 (by rfl) ⟨381344, by rfl⟩ : syracuseStep 2033837 = 762689) (by norm_num)
theorem B2033909 : Blo 900574 2033909 := bbase (se 5 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 2033909 = 190679) (by norm_num)
theorem B5146901 : Blo 900574 5146901 := bbase (se 6 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 5146901 = 241261) (by norm_num)
theorem B2033981 : Blo 900574 2033981 := bbase (se 3 (by rfl) ⟨381371, by rfl⟩ : syracuseStep 2033981 = 762743) (by norm_num)
theorem B2165093 : Blo 900574 2165093 := bbase (se 4 (by rfl) ⟨202977, by rfl⟩ : syracuseStep 2165093 = 405955) (by norm_num)
theorem B2034053 : Blo 900574 2034053 := bbase (se 4 (by rfl) ⟨190692, by rfl⟩ : syracuseStep 2034053 = 381385) (by norm_num)
theorem B2034125 : Blo 900574 2034125 := bbase (se 3 (by rfl) ⟨381398, by rfl⟩ : syracuseStep 2034125 = 762797) (by norm_num)
theorem B3049973 : Blo 900574 3049973 := bbase (se 5 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 3049973 = 285935) (by norm_num)
theorem B2034197 : Blo 900574 2034197 := bbase (se 6 (by rfl) ⟨47676, by rfl⟩ : syracuseStep 2034197 = 95353) (by norm_num)
theorem B2165285 : Blo 900574 2165285 := bbase (se 4 (by rfl) ⟨202995, by rfl⟩ : syracuseStep 2165285 = 405991) (by norm_num)
theorem B1083949 : Blo 900574 1083949 := bbase (se 3 (by rfl) ⟨203240, by rfl⟩ : syracuseStep 1083949 = 406481) (by norm_num)
theorem B2034269 : Blo 900574 2034269 := bbase (se 3 (by rfl) ⟨381425, by rfl⟩ : syracuseStep 2034269 = 762851) (by norm_num)
theorem B2165381 : Blo 900574 2165381 := bbase (se 4 (by rfl) ⟨203004, by rfl⟩ : syracuseStep 2165381 = 406009) (by norm_num)
theorem B2034341 : Blo 900574 2034341 := bbase (se 4 (by rfl) ⟨190719, by rfl⟩ : syracuseStep 2034341 = 381439) (by norm_num)
theorem B2034413 : Blo 900574 2034413 := bbase (se 3 (by rfl) ⟨381452, by rfl⟩ : syracuseStep 2034413 = 762905) (by norm_num)
theorem B1444645 : Blo 900574 1444645 := bbase (se 4 (by rfl) ⟨135435, by rfl⟩ : syracuseStep 1444645 = 270871) (by norm_num)
theorem B2034485 : Blo 900574 2034485 := bbase (se 5 (by rfl) ⟨95366, by rfl⟩ : syracuseStep 2034485 = 190733) (by norm_num)
theorem B3083093 : Blo 900574 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B2034557 : Blo 900574 2034557 := bbase (se 3 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 2034557 = 762959) (by norm_num)
theorem B2886533 : Blo 900574 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B3050405 : Blo 900574 3050405 := bbase (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) (by norm_num)
theorem B3476405 : Blo 900574 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B2034629 : Blo 900574 2034629 := bbase (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) (by norm_num)
theorem B2034701 : Blo 900574 2034701 := bbase (se 3 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 2034701 = 763013) (by norm_num)
theorem B2034773 : Blo 900574 2034773 := bbase (se 8 (by rfl) ⟨11922, by rfl⟩ : syracuseStep 2034773 = 23845) (by norm_num)
theorem B2034845 : Blo 900574 2034845 := bbase (se 3 (by rfl) ⟨381533, by rfl⟩ : syracuseStep 2034845 = 763067) (by norm_num)
theorem B2034917 : Blo 900574 2034917 := bbase (se 4 (by rfl) ⟨190773, by rfl⟩ : syracuseStep 2034917 = 381547) (by norm_num)
theorem B2034989 : Blo 900574 2034989 := bbase (se 3 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 2034989 = 763121) (by norm_num)
theorem B3050837 : Blo 900574 3050837 := bbase (se 11 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 3050837 = 4469) (by norm_num)
theorem B2035061 : Blo 900574 2035061 := bbase (se 5 (by rfl) ⟨95393, by rfl⟩ : syracuseStep 2035061 = 190787) (by norm_num)
theorem B1084853 : Blo 900574 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B2035133 : Blo 900574 2035133 := bbase (se 3 (by rfl) ⟨381587, by rfl⟩ : syracuseStep 2035133 = 763175) (by norm_num)
theorem B5770709 : Blo 900574 5770709 := bbase (se 7 (by rfl) ⟨67625, by rfl⟩ : syracuseStep 5770709 = 135251) (by norm_num)
theorem B2035205 : Blo 900574 2035205 := bbase (se 4 (by rfl) ⟨190800, by rfl⟩ : syracuseStep 2035205 = 381601) (by norm_num)
theorem B3247685 : Blo 900574 3247685 := bbase (se 4 (by rfl) ⟨304470, by rfl⟩ : syracuseStep 3247685 = 608941) (by norm_num)
theorem B2035277 : Blo 900574 2035277 := bbase (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) (by norm_num)
theorem B1412725 : Blo 900574 1412725 := bbase (se 5 (by rfl) ⟨66221, by rfl⟩ : syracuseStep 1412725 = 132443) (by norm_num)
theorem B1085113 : Blo 900574 1085113 := bbase (se 2 (by rfl) ⟨406917, by rfl⟩ : syracuseStep 1085113 = 813835) (by norm_num)
theorem B1445573 : Blo 900574 1445573 := bbase (se 4 (by rfl) ⟨135522, by rfl⟩ : syracuseStep 1445573 = 271045) (by norm_num)
theorem B1412813 : Blo 900574 1412813 := bbase (se 3 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 1412813 = 529805) (by norm_num)
theorem B3051269 : Blo 900574 3051269 := bbase (se 4 (by rfl) ⟨286056, by rfl⟩ : syracuseStep 3051269 = 572113) (by norm_num)
theorem B1085305 : Blo 900574 1085305 := bbase (se 2 (by rfl) ⟨406989, by rfl⟩ : syracuseStep 1085305 = 813979) (by norm_num)
theorem B1085329 : Blo 900574 1085329 := bbase (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) (by norm_num)
theorem B1085333 : Blo 900574 1085333 := bbase (se 6 (by rfl) ⟨25437, by rfl⟩ : syracuseStep 1085333 = 50875) (by norm_num)
theorem B2199653 : Blo 900574 2199653 := bbase (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) (by norm_num)
theorem B3248261 : Blo 900574 3248261 := bbase (se 4 (by rfl) ⟨304524, by rfl⟩ : syracuseStep 3248261 = 609049) (by norm_num)
theorem B1446029 : Blo 900574 1446029 := bbase (se 3 (by rfl) ⟨271130, by rfl⟩ : syracuseStep 1446029 = 542261) (by norm_num)
theorem B3051701 : Blo 900574 3051701 := bbase (se 5 (by rfl) ⟨143048, by rfl⟩ : syracuseStep 3051701 = 286097) (by norm_num)
theorem B1282277 : Blo 900574 1282277 := bbase (se 4 (by rfl) ⟨120213, by rfl⟩ : syracuseStep 1282277 = 240427) (by norm_num)
theorem B19501397 : Blo 900574 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B1085833 : Blo 900574 1085833 := bbase (se 2 (by rfl) ⟨407187, by rfl⟩ : syracuseStep 1085833 = 814375) (by norm_num)
theorem B5149109 : Blo 900574 5149109 := bbase (se 5 (by rfl) ⟨241364, by rfl⟩ : syracuseStep 5149109 = 482729) (by norm_num)
theorem B3477973 : Blo 900574 3477973 := bbase (se 7 (by rfl) ⟨40757, by rfl⟩ : syracuseStep 3477973 = 81515) (by norm_num)
theorem B1085929 : Blo 900574 1085929 := bbase (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) (by norm_num)
theorem B2200069 : Blo 900574 2200069 := bbase (se 4 (by rfl) ⟨206256, by rfl⟩ : syracuseStep 2200069 = 412513) (by norm_num)
theorem B9277973 : Blo 900574 9277973 := bbase (se 6 (by rfl) ⟨217452, by rfl⟩ : syracuseStep 9277973 = 434905) (by norm_num)
theorem B3052133 : Blo 900574 3052133 := bbase (se 4 (by rfl) ⟨286137, by rfl⟩ : syracuseStep 3052133 = 572275) (by norm_num)
theorem B1217173 : Blo 900574 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B2888405 : Blo 900574 2888405 := bbase (se 7 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 2888405 = 67697) (by norm_num)
theorem B4559813 : Blo 900574 4559813 := bbase (se 4 (by rfl) ⟨427482, by rfl⟩ : syracuseStep 4559813 = 854965) (by norm_num)
theorem B2167813 : Blo 900574 2167813 := bbase (se 4 (by rfl) ⟨203232, by rfl⟩ : syracuseStep 2167813 = 406465) (by norm_num)
theorem B3052565 : Blo 900574 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B1545301 : Blo 900574 1545301 := bbase (se 8 (by rfl) ⟨9054, by rfl⟩ : syracuseStep 1545301 = 18109) (by norm_num)
theorem B2168149 : Blo 900574 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B1447445 : Blo 900574 1447445 := bbase (se 6 (by rfl) ⟨33924, by rfl⟩ : syracuseStep 1447445 = 67849) (by norm_num)
theorem B1283701 : Blo 900574 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B1709741 : Blo 900574 1709741 := bbase (se 3 (by rfl) ⟨320576, by rfl⟩ : syracuseStep 1709741 = 641153) (by norm_num)
theorem B1447669 : Blo 900574 1447669 := bbase (se 5 (by rfl) ⟨67859, by rfl⟩ : syracuseStep 1447669 = 135719) (by norm_num)
theorem B1709885 : Blo 900574 1709885 := bbase (se 3 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 1709885 = 641207) (by norm_num)
theorem B2168765 : Blo 900574 2168765 := bbase (se 3 (by rfl) ⟨406643, by rfl⟩ : syracuseStep 2168765 = 813287) (by norm_num)
theorem B1710173 : Blo 900574 1710173 := bbase (se 3 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 1710173 = 641315) (by norm_num)
theorem B1284293 : Blo 900574 1284293 := bbase (se 4 (by rfl) ⟨120402, by rfl⟩ : syracuseStep 1284293 = 240805) (by norm_num)
theorem B4561109 : Blo 900574 4561109 := bbase (se 7 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 4561109 = 106901) (by norm_num)
theorem B1710325 : Blo 900574 1710325 := bbase (se 5 (by rfl) ⟨80171, by rfl⟩ : syracuseStep 1710325 = 160343) (by norm_num)
theorem B1284373 : Blo 900574 1284373 := bbase (se 6 (by rfl) ⟨30102, by rfl⟩ : syracuseStep 1284373 = 60205) (by norm_num)
theorem B2169197 : Blo 900574 2169197 := bbase (se 3 (by rfl) ⟨406724, by rfl⟩ : syracuseStep 2169197 = 813449) (by norm_num)
theorem B6855029 : Blo 900574 6855029 := bbase (se 5 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 6855029 = 642659) (by norm_num)
theorem B1284493 : Blo 900574 1284493 := bbase (se 3 (by rfl) ⟨240842, by rfl⟩ : syracuseStep 1284493 = 481685) (by norm_num)
theorem B1284589 : Blo 900574 1284589 := bbase (se 3 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 1284589 = 481721) (by norm_num)
theorem B1710629 : Blo 900574 1710629 := bbase (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) (by norm_num)
theorem B1219141 : Blo 900574 1219141 := bbase (se 4 (by rfl) ⟨114294, by rfl⟩ : syracuseStep 1219141 = 228589) (by norm_num)
theorem B1317541 : Blo 900574 1317541 := bbase (se 4 (by rfl) ⟨123519, by rfl⟩ : syracuseStep 1317541 = 247039) (by norm_num)
theorem B11901653 : Blo 900574 11901653 := bbase (se 7 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 11901653 = 278945) (by norm_num)
theorem B1285085 : Blo 900574 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B2169821 : Blo 900574 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B17603669 : Blo 900574 17603669 := bbase (se 8 (by rfl) ⟨103146, by rfl⟩ : syracuseStep 17603669 = 206293) (by norm_num)
theorem B1219789 : Blo 900574 1219789 := bbase (se 3 (by rfl) ⟨228710, by rfl⟩ : syracuseStep 1219789 = 457421) (by norm_num)
theorem B1350869 : Blo 900574 1350869 := bbase (se 7 (by rfl) ⟨15830, by rfl⟩ : syracuseStep 1350869 = 31661) (by norm_num)
theorem B1350893 : Blo 900574 1350893 := bbase (se 3 (by rfl) ⟨253292, by rfl⟩ : syracuseStep 1350893 = 506585) (by norm_num)
theorem B1350917 : Blo 900574 1350917 := bbase (se 4 (by rfl) ⟨126648, by rfl⟩ : syracuseStep 1350917 = 253297) (by norm_num)
theorem B1711381 : Blo 900574 1711381 := bbase (se 6 (by rfl) ⟨40110, by rfl⟩ : syracuseStep 1711381 = 80221) (by norm_num)
theorem B1350941 : Blo 900574 1350941 := bbase (se 3 (by rfl) ⟨253301, by rfl⟩ : syracuseStep 1350941 = 506603) (by norm_num)
theorem B3480869 : Blo 900574 3480869 := bbase (se 4 (by rfl) ⟨326331, by rfl⟩ : syracuseStep 3480869 = 652663) (by norm_num)
theorem B1350965 : Blo 900574 1350965 := bbase (se 5 (by rfl) ⟨63326, by rfl⟩ : syracuseStep 1350965 = 126653) (by norm_num)
theorem B1350989 : Blo 900574 1350989 := bbase (se 3 (by rfl) ⟨253310, by rfl⟩ : syracuseStep 1350989 = 506621) (by norm_num)
theorem B3087701 : Blo 900574 3087701 := bbase (se 11 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 3087701 = 4523) (by norm_num)
theorem B1351013 : Blo 900574 1351013 := bbase (se 4 (by rfl) ⟨126657, by rfl⟩ : syracuseStep 1351013 = 253315) (by norm_num)
theorem B1351037 : Blo 900574 1351037 := bbase (se 3 (by rfl) ⟨253319, by rfl⟩ : syracuseStep 1351037 = 506639) (by norm_num)
theorem B1351061 : Blo 900574 1351061 := bbase (se 6 (by rfl) ⟨31665, by rfl⟩ : syracuseStep 1351061 = 63331) (by norm_num)
theorem B1711525 : Blo 900574 1711525 := bbase (se 4 (by rfl) ⟨160455, by rfl⟩ : syracuseStep 1711525 = 320911) (by norm_num)
theorem B2891173 : Blo 900574 2891173 := bbase (se 4 (by rfl) ⟨271047, by rfl⟩ : syracuseStep 2891173 = 542095) (by norm_num)
theorem B1351085 : Blo 900574 1351085 := bbase (se 3 (by rfl) ⟨253328, by rfl⟩ : syracuseStep 1351085 = 506657) (by norm_num)
theorem B1351109 : Blo 900574 1351109 := bbase (se 4 (by rfl) ⟨126666, by rfl⟩ : syracuseStep 1351109 = 253333) (by norm_num)
theorem B1351133 : Blo 900574 1351133 := bbase (se 3 (by rfl) ⟨253337, by rfl⟩ : syracuseStep 1351133 = 506675) (by norm_num)
theorem B4562405 : Blo 900574 4562405 := bbase (se 4 (by rfl) ⟨427725, by rfl⟩ : syracuseStep 4562405 = 855451) (by norm_num)
theorem B1351157 : Blo 900574 1351157 := bbase (se 5 (by rfl) ⟨63335, by rfl⟩ : syracuseStep 1351157 = 126671) (by norm_num)
theorem B1285637 : Blo 900574 1285637 := bbase (se 4 (by rfl) ⟨120528, by rfl⟩ : syracuseStep 1285637 = 241057) (by norm_num)
theorem B1351181 : Blo 900574 1351181 := bbase (se 3 (by rfl) ⟨253346, by rfl⟩ : syracuseStep 1351181 = 506693) (by norm_num)
theorem B1351205 : Blo 900574 1351205 := bbase (se 4 (by rfl) ⟨126675, by rfl⟩ : syracuseStep 1351205 = 253351) (by norm_num)
theorem B1351229 : Blo 900574 1351229 := bbase (se 3 (by rfl) ⟨253355, by rfl⟩ : syracuseStep 1351229 = 506711) (by norm_num)
theorem B1711685 : Blo 900574 1711685 := bbase (se 4 (by rfl) ⟨160470, by rfl⟩ : syracuseStep 1711685 = 320941) (by norm_num)
theorem B1351253 : Blo 900574 1351253 := bbase (se 8 (by rfl) ⟨7917, by rfl⟩ : syracuseStep 1351253 = 15835) (by norm_num)
theorem B1351277 : Blo 900574 1351277 := bbase (se 3 (by rfl) ⟨253364, by rfl⟩ : syracuseStep 1351277 = 506729) (by norm_num)
theorem B1351301 : Blo 900574 1351301 := bbase (se 4 (by rfl) ⟨126684, by rfl⟩ : syracuseStep 1351301 = 253369) (by norm_num)
theorem B1351325 : Blo 900574 1351325 := bbase (se 3 (by rfl) ⟨253373, by rfl⟩ : syracuseStep 1351325 = 506747) (by norm_num)
theorem B1351349 : Blo 900574 1351349 := bbase (se 5 (by rfl) ⟨63344, by rfl⟩ : syracuseStep 1351349 = 126689) (by norm_num)
theorem B1351373 : Blo 900574 1351373 := bbase (se 3 (by rfl) ⟨253382, by rfl⟩ : syracuseStep 1351373 = 506765) (by norm_num)
theorem B1711829 : Blo 900574 1711829 := bbase (se 7 (by rfl) ⟨20060, by rfl⟩ : syracuseStep 1711829 = 40121) (by norm_num)
theorem B1351397 : Blo 900574 1351397 := bbase (se 4 (by rfl) ⟨126693, by rfl⟩ : syracuseStep 1351397 = 253387) (by norm_num)
theorem B1351421 : Blo 900574 1351421 := bbase (se 3 (by rfl) ⟨253391, by rfl⟩ : syracuseStep 1351421 = 506783) (by norm_num)
theorem B1351445 : Blo 900574 1351445 := bbase (se 6 (by rfl) ⟨31674, by rfl⟩ : syracuseStep 1351445 = 63349) (by norm_num)
theorem B1351469 : Blo 900574 1351469 := bbase (se 3 (by rfl) ⟨253400, by rfl⟩ : syracuseStep 1351469 = 506801) (by norm_num)
theorem B1351493 : Blo 900574 1351493 := bbase (se 4 (by rfl) ⟨126702, by rfl⟩ : syracuseStep 1351493 = 253405) (by norm_num)
theorem B1351517 : Blo 900574 1351517 := bbase (se 3 (by rfl) ⟨253409, by rfl⟩ : syracuseStep 1351517 = 506819) (by norm_num)
theorem B1351541 : Blo 900574 1351541 := bbase (se 5 (by rfl) ⟨63353, by rfl⟩ : syracuseStep 1351541 = 126707) (by norm_num)
theorem B1351565 : Blo 900574 1351565 := bbase (se 3 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 1351565 = 506837) (by norm_num)
theorem B1351589 : Blo 900574 1351589 := bbase (se 4 (by rfl) ⟨126711, by rfl⟩ : syracuseStep 1351589 = 253423) (by norm_num)
theorem B1351613 : Blo 900574 1351613 := bbase (se 3 (by rfl) ⟨253427, by rfl⟩ : syracuseStep 1351613 = 506855) (by norm_num)
theorem B1351637 : Blo 900574 1351637 := bbase (se 7 (by rfl) ⟨15839, by rfl⟩ : syracuseStep 1351637 = 31679) (by norm_num)
theorem B14622677 : Blo 900574 14622677 := bbase (se 7 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 14622677 = 342719) (by norm_num)
theorem B1351661 : Blo 900574 1351661 := bbase (se 3 (by rfl) ⟨253436, by rfl⟩ : syracuseStep 1351661 = 506873) (by norm_num)
theorem B1712117 : Blo 900574 1712117 := bbase (se 5 (by rfl) ⟨80255, by rfl⟩ : syracuseStep 1712117 = 160511) (by norm_num)
theorem B1351685 : Blo 900574 1351685 := bbase (se 4 (by rfl) ⟨126720, by rfl⟩ : syracuseStep 1351685 = 253441) (by norm_num)
theorem B1351709 : Blo 900574 1351709 := bbase (se 3 (by rfl) ⟨253445, by rfl⟩ : syracuseStep 1351709 = 506891) (by norm_num)
theorem B1351733 : Blo 900574 1351733 := bbase (se 5 (by rfl) ⟨63362, by rfl⟩ : syracuseStep 1351733 = 126725) (by norm_num)
theorem B1351757 : Blo 900574 1351757 := bbase (se 3 (by rfl) ⟨253454, by rfl⟩ : syracuseStep 1351757 = 506909) (by norm_num)
theorem B1351781 : Blo 900574 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B1351805 : Blo 900574 1351805 := bbase (se 3 (by rfl) ⟨253463, by rfl⟩ : syracuseStep 1351805 = 506927) (by norm_num)
theorem B1712269 : Blo 900574 1712269 := bbase (se 3 (by rfl) ⟨321050, by rfl⟩ : syracuseStep 1712269 = 642101) (by norm_num)
theorem B1351829 : Blo 900574 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B1351853 : Blo 900574 1351853 := bbase (se 3 (by rfl) ⟨253472, by rfl⟩ : syracuseStep 1351853 = 506945) (by norm_num)
theorem B1351877 : Blo 900574 1351877 := bbase (se 4 (by rfl) ⟨126738, by rfl⟩ : syracuseStep 1351877 = 253477) (by norm_num)
theorem B1351901 : Blo 900574 1351901 := bbase (se 3 (by rfl) ⟨253481, by rfl⟩ : syracuseStep 1351901 = 506963) (by norm_num)
theorem B1351925 : Blo 900574 1351925 := bbase (se 5 (by rfl) ⟨63371, by rfl⟩ : syracuseStep 1351925 = 126743) (by norm_num)
theorem B1286389 : Blo 900574 1286389 := bbase (se 5 (by rfl) ⟨60299, by rfl⟩ : syracuseStep 1286389 = 120599) (by norm_num)
theorem B1351949 : Blo 900574 1351949 := bbase (se 3 (by rfl) ⟨253490, by rfl⟩ : syracuseStep 1351949 = 506981) (by norm_num)
theorem B1351973 : Blo 900574 1351973 := bbase (se 4 (by rfl) ⟨126747, by rfl⟩ : syracuseStep 1351973 = 253495) (by norm_num)
theorem B1351997 : Blo 900574 1351997 := bbase (se 3 (by rfl) ⟨253499, by rfl⟩ : syracuseStep 1351997 = 506999) (by norm_num)
theorem B1352021 : Blo 900574 1352021 := bbase (se 10 (by rfl) ⟨1980, by rfl⟩ : syracuseStep 1352021 = 3961) (by norm_num)
theorem B1155421 : Blo 900574 1155421 := bbase (se 3 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 1155421 = 433283) (by norm_num)
theorem B1352045 : Blo 900574 1352045 := bbase (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) (by norm_num)
theorem B1352069 : Blo 900574 1352069 := bbase (se 4 (by rfl) ⟨126756, by rfl⟩ : syracuseStep 1352069 = 253513) (by norm_num)
theorem B1483157 : Blo 900574 1483157 := bbase (se 6 (by rfl) ⟨34761, by rfl⟩ : syracuseStep 1483157 = 69523) (by norm_num)
theorem B1352093 : Blo 900574 1352093 := bbase (se 3 (by rfl) ⟨253517, by rfl⟩ : syracuseStep 1352093 = 507035) (by norm_num)
theorem B1352117 : Blo 900574 1352117 := bbase (se 5 (by rfl) ⟨63380, by rfl⟩ : syracuseStep 1352117 = 126761) (by norm_num)
theorem B1712573 : Blo 900574 1712573 := bbase (se 3 (by rfl) ⟨321107, by rfl⟩ : syracuseStep 1712573 = 642215) (by norm_num)
theorem B1352141 : Blo 900574 1352141 := bbase (se 3 (by rfl) ⟨253526, by rfl⟩ : syracuseStep 1352141 = 507053) (by norm_num)
theorem B1352165 : Blo 900574 1352165 := bbase (se 4 (by rfl) ⟨126765, by rfl⟩ : syracuseStep 1352165 = 253531) (by norm_num)
theorem B1352189 : Blo 900574 1352189 := bbase (se 3 (by rfl) ⟨253535, by rfl⟩ : syracuseStep 1352189 = 507071) (by norm_num)
theorem B1155589 : Blo 900574 1155589 := bbase (se 4 (by rfl) ⟨108336, by rfl⟩ : syracuseStep 1155589 = 216673) (by norm_num)
theorem B1352213 : Blo 900574 1352213 := bbase (se 6 (by rfl) ⟨31692, by rfl⟩ : syracuseStep 1352213 = 63385) (by norm_num)
theorem B1352237 : Blo 900574 1352237 := bbase (se 3 (by rfl) ⟨253544, by rfl⟩ : syracuseStep 1352237 = 507089) (by norm_num)
theorem B1352261 : Blo 900574 1352261 := bbase (se 4 (by rfl) ⟨126774, by rfl⟩ : syracuseStep 1352261 = 253549) (by norm_num)
theorem B1352285 : Blo 900574 1352285 := bbase (se 3 (by rfl) ⟨253553, by rfl⟩ : syracuseStep 1352285 = 507107) (by norm_num)
theorem B1352309 : Blo 900574 1352309 := bbase (se 5 (by rfl) ⟨63389, by rfl⟩ : syracuseStep 1352309 = 126779) (by norm_num)
theorem B1352333 : Blo 900574 1352333 := bbase (se 3 (by rfl) ⟨253562, by rfl⟩ : syracuseStep 1352333 = 507125) (by norm_num)
theorem B1352357 : Blo 900574 1352357 := bbase (se 4 (by rfl) ⟨126783, by rfl⟩ : syracuseStep 1352357 = 253567) (by norm_num)
theorem B1352381 : Blo 900574 1352381 := bbase (se 3 (by rfl) ⟨253571, by rfl⟩ : syracuseStep 1352381 = 507143) (by norm_num)
theorem B1352405 : Blo 900574 1352405 := bbase (se 7 (by rfl) ⟨15848, by rfl⟩ : syracuseStep 1352405 = 31697) (by norm_num)
theorem B1352429 : Blo 900574 1352429 := bbase (se 3 (by rfl) ⟨253580, by rfl⟩ : syracuseStep 1352429 = 507161) (by norm_num)
theorem B4563701 : Blo 900574 4563701 := bbase (se 5 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 4563701 = 427847) (by norm_num)
theorem B1352453 : Blo 900574 1352453 := bbase (se 4 (by rfl) ⟨126792, by rfl⟩ : syracuseStep 1352453 = 253585) (by norm_num)
theorem B2564885 : Blo 900574 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B5219093 : Blo 900574 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B1352477 : Blo 900574 1352477 := bbase (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) (by norm_num)
theorem B5481269 : Blo 900574 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B1352501 : Blo 900574 1352501 := bbase (se 5 (by rfl) ⟨63398, by rfl⟩ : syracuseStep 1352501 = 126797) (by norm_num)
theorem B3253061 : Blo 900574 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B1352525 : Blo 900574 1352525 := bbase (se 3 (by rfl) ⟨253598, by rfl⟩ : syracuseStep 1352525 = 507197) (by norm_num)
theorem B1352549 : Blo 900574 1352549 := bbase (se 4 (by rfl) ⟨126801, by rfl⟩ : syracuseStep 1352549 = 253603) (by norm_num)
theorem B1352573 : Blo 900574 1352573 := bbase (se 3 (by rfl) ⟨253607, by rfl⟩ : syracuseStep 1352573 = 507215) (by norm_num)
theorem B1352597 : Blo 900574 1352597 := bbase (se 6 (by rfl) ⟨31701, by rfl⟩ : syracuseStep 1352597 = 63403) (by norm_num)
theorem B1352621 : Blo 900574 1352621 := bbase (se 3 (by rfl) ⟨253616, by rfl⟩ : syracuseStep 1352621 = 507233) (by norm_num)
theorem B1352645 : Blo 900574 1352645 := bbase (se 4 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 1352645 = 253621) (by norm_num)
theorem B1352669 : Blo 900574 1352669 := bbase (se 3 (by rfl) ⟨253625, by rfl⟩ : syracuseStep 1352669 = 507251) (by norm_num)
theorem B1352693 : Blo 900574 1352693 := bbase (se 5 (by rfl) ⟨63407, by rfl⟩ : syracuseStep 1352693 = 126815) (by norm_num)
theorem B1352717 : Blo 900574 1352717 := bbase (se 3 (by rfl) ⟨253634, by rfl⟩ : syracuseStep 1352717 = 507269) (by norm_num)
theorem B1287181 : Blo 900574 1287181 := bbase (se 3 (by rfl) ⟨241346, by rfl⟩ : syracuseStep 1287181 = 482693) (by norm_num)
theorem B1352741 : Blo 900574 1352741 := bbase (se 4 (by rfl) ⟨126819, by rfl⟩ : syracuseStep 1352741 = 253639) (by norm_num)
theorem B1352765 : Blo 900574 1352765 := bbase (se 3 (by rfl) ⟨253643, by rfl⟩ : syracuseStep 1352765 = 507287) (by norm_num)
theorem B1352789 : Blo 900574 1352789 := bbase (se 8 (by rfl) ⟨7926, by rfl⟩ : syracuseStep 1352789 = 15853) (by norm_num)
theorem B1352813 : Blo 900574 1352813 := bbase (se 3 (by rfl) ⟨253652, by rfl⟩ : syracuseStep 1352813 = 507305) (by norm_num)
theorem B1352837 : Blo 900574 1352837 := bbase (se 4 (by rfl) ⟨126828, by rfl⟩ : syracuseStep 1352837 = 253657) (by norm_num)
theorem B1352861 : Blo 900574 1352861 := bbase (se 3 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 1352861 = 507323) (by norm_num)
theorem B3515557 : Blo 900574 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B1713325 : Blo 900574 1713325 := bbase (se 3 (by rfl) ⟨321248, by rfl⟩ : syracuseStep 1713325 = 642497) (by norm_num)
theorem B1352885 : Blo 900574 1352885 := bbase (se 5 (by rfl) ⟨63416, by rfl⟩ : syracuseStep 1352885 = 126833) (by norm_num)
theorem B1352909 : Blo 900574 1352909 := bbase (se 3 (by rfl) ⟨253670, by rfl⟩ : syracuseStep 1352909 = 507341) (by norm_num)
theorem B1352933 : Blo 900574 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B1352957 : Blo 900574 1352957 := bbase (se 3 (by rfl) ⟨253679, by rfl⟩ : syracuseStep 1352957 = 507359) (by norm_num)
theorem B1352981 : Blo 900574 1352981 := bbase (se 6 (by rfl) ⟨31710, by rfl⟩ : syracuseStep 1352981 = 63421) (by norm_num)
theorem B4629797 : Blo 900574 4629797 := bbase (se 4 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 4629797 = 868087) (by norm_num)
theorem B1353005 : Blo 900574 1353005 := bbase (se 3 (by rfl) ⟨253688, by rfl⟩ : syracuseStep 1353005 = 507377) (by norm_num)
theorem B1713469 : Blo 900574 1713469 := bbase (se 3 (by rfl) ⟨321275, by rfl⟩ : syracuseStep 1713469 = 642551) (by norm_num)
theorem B1353029 : Blo 900574 1353029 := bbase (se 4 (by rfl) ⟨126846, by rfl⟩ : syracuseStep 1353029 = 253693) (by norm_num)
theorem B1353053 : Blo 900574 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B1287517 : Blo 900574 1287517 := bbase (se 3 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 1287517 = 482819) (by norm_num)
theorem B5776757 : Blo 900574 5776757 := bbase (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) (by norm_num)
theorem B1353077 : Blo 900574 1353077 := bbase (se 5 (by rfl) ⟨63425, by rfl⟩ : syracuseStep 1353077 = 126851) (by norm_num)
theorem B1353101 : Blo 900574 1353101 := bbase (se 3 (by rfl) ⟨253706, by rfl⟩ : syracuseStep 1353101 = 507413) (by norm_num)
theorem B1353125 : Blo 900574 1353125 := bbase (se 4 (by rfl) ⟨126855, by rfl⟩ : syracuseStep 1353125 = 253711) (by norm_num)
theorem B2565557 : Blo 900574 2565557 := bbase (se 5 (by rfl) ⟨120260, by rfl⟩ : syracuseStep 2565557 = 240521) (by norm_num)
theorem B4335029 : Blo 900574 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B1353149 : Blo 900574 1353149 := bbase (se 3 (by rfl) ⟨253715, by rfl⟩ : syracuseStep 1353149 = 507431) (by norm_num)
theorem B1353173 : Blo 900574 1353173 := bbase (se 7 (by rfl) ⟨15857, by rfl⟩ : syracuseStep 1353173 = 31715) (by norm_num)
theorem B1713629 : Blo 900574 1713629 := bbase (se 3 (by rfl) ⟨321305, by rfl⟩ : syracuseStep 1713629 = 642611) (by norm_num)
theorem B1353197 : Blo 900574 1353197 := bbase (se 3 (by rfl) ⟨253724, by rfl⟩ : syracuseStep 1353197 = 507449) (by norm_num)
theorem B1353221 : Blo 900574 1353221 := bbase (se 4 (by rfl) ⟨126864, by rfl⟩ : syracuseStep 1353221 = 253729) (by norm_num)
theorem B1353245 : Blo 900574 1353245 := bbase (se 3 (by rfl) ⟨253733, by rfl⟩ : syracuseStep 1353245 = 507467) (by norm_num)
theorem B1353269 : Blo 900574 1353269 := bbase (se 5 (by rfl) ⟨63434, by rfl⟩ : syracuseStep 1353269 = 126869) (by norm_num)
theorem B1287733 : Blo 900574 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B1353293 : Blo 900574 1353293 := bbase (se 3 (by rfl) ⟨253742, by rfl⟩ : syracuseStep 1353293 = 507485) (by norm_num)
theorem B1353317 : Blo 900574 1353317 := bbase (se 4 (by rfl) ⟨126873, by rfl⟩ : syracuseStep 1353317 = 253747) (by norm_num)
theorem B1713773 : Blo 900574 1713773 := bbase (se 3 (by rfl) ⟨321332, by rfl⟩ : syracuseStep 1713773 = 642665) (by norm_num)
theorem B1353341 : Blo 900574 1353341 := bbase (se 3 (by rfl) ⟨253751, by rfl⟩ : syracuseStep 1353341 = 507503) (by norm_num)
theorem B1353365 : Blo 900574 1353365 := bbase (se 6 (by rfl) ⟨31719, by rfl⟩ : syracuseStep 1353365 = 63439) (by norm_num)
theorem B1353389 : Blo 900574 1353389 := bbase (se 3 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 1353389 = 507521) (by norm_num)
theorem B1353413 : Blo 900574 1353413 := bbase (se 4 (by rfl) ⟨126882, by rfl⟩ : syracuseStep 1353413 = 253765) (by norm_num)
theorem B1353437 : Blo 900574 1353437 := bbase (se 3 (by rfl) ⟨253769, by rfl⟩ : syracuseStep 1353437 = 507539) (by norm_num)
theorem B1353461 : Blo 900574 1353461 := bbase (se 5 (by rfl) ⟨63443, by rfl⟩ : syracuseStep 1353461 = 126887) (by norm_num)
theorem B1353485 : Blo 900574 1353485 := bbase (se 3 (by rfl) ⟨253778, by rfl⟩ : syracuseStep 1353485 = 507557) (by norm_num)
theorem B1353509 : Blo 900574 1353509 := bbase (se 4 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 1353509 = 253783) (by norm_num)
theorem B3254069 : Blo 900574 3254069 := bbase (se 5 (by rfl) ⟨152534, by rfl⟩ : syracuseStep 3254069 = 305069) (by norm_num)
theorem B1353533 : Blo 900574 1353533 := bbase (se 3 (by rfl) ⟨253787, by rfl⟩ : syracuseStep 1353533 = 507575) (by norm_num)
theorem B1353557 : Blo 900574 1353557 := bbase (se 9 (by rfl) ⟨3965, by rfl⟩ : syracuseStep 1353557 = 7931) (by norm_num)
theorem B2565989 : Blo 900574 2565989 := bbase (se 4 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 2565989 = 481123) (by norm_num)
theorem B1353581 : Blo 900574 1353581 := bbase (se 3 (by rfl) ⟨253796, by rfl⟩ : syracuseStep 1353581 = 507593) (by norm_num)
theorem B2172781 : Blo 900574 2172781 := bbase (se 3 (by rfl) ⟨407396, by rfl⟩ : syracuseStep 2172781 = 814793) (by norm_num)
theorem B2926469 : Blo 900574 2926469 := bbase (se 4 (by rfl) ⟨274356, by rfl⟩ : syracuseStep 2926469 = 548713) (by norm_num)
theorem B1353605 : Blo 900574 1353605 := bbase (se 4 (by rfl) ⟨126900, by rfl⟩ : syracuseStep 1353605 = 253801) (by norm_num)
theorem B1714061 : Blo 900574 1714061 := bbase (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) (by norm_num)
theorem B1353629 : Blo 900574 1353629 := bbase (se 3 (by rfl) ⟨253805, by rfl⟩ : syracuseStep 1353629 = 507611) (by norm_num)
theorem B1353653 : Blo 900574 1353653 := bbase (se 5 (by rfl) ⟨63452, by rfl⟩ : syracuseStep 1353653 = 126905) (by norm_num)
theorem B1353677 : Blo 900574 1353677 := bbase (se 3 (by rfl) ⟨253814, by rfl⟩ : syracuseStep 1353677 = 507629) (by norm_num)
theorem B1353701 : Blo 900574 1353701 := bbase (se 4 (by rfl) ⟨126909, by rfl⟩ : syracuseStep 1353701 = 253819) (by norm_num)
theorem B1353725 : Blo 900574 1353725 := bbase (se 3 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 1353725 = 507647) (by norm_num)
theorem B4564997 : Blo 900574 4564997 := bbase (se 4 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 4564997 = 855937) (by norm_num)
theorem B1353749 : Blo 900574 1353749 := bbase (se 6 (by rfl) ⟨31728, by rfl⟩ : syracuseStep 1353749 = 63457) (by norm_num)
theorem B1714213 : Blo 900574 1714213 := bbase (se 4 (by rfl) ⟨160707, by rfl⟩ : syracuseStep 1714213 = 321415) (by norm_num)
theorem B1353773 : Blo 900574 1353773 := bbase (se 3 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 1353773 = 507665) (by norm_num)
theorem B2172973 : Blo 900574 2172973 := bbase (se 3 (by rfl) ⟨407432, by rfl⟩ : syracuseStep 2172973 = 814865) (by norm_num)
theorem B1353797 : Blo 900574 1353797 := bbase (se 4 (by rfl) ⟨126918, by rfl⟩ : syracuseStep 1353797 = 253837) (by norm_num)
theorem B2173013 : Blo 900574 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B1353821 : Blo 900574 1353821 := bbase (se 3 (by rfl) ⟨253841, by rfl⟩ : syracuseStep 1353821 = 507683) (by norm_num)
theorem B1353845 : Blo 900574 1353845 := bbase (se 5 (by rfl) ⟨63461, by rfl⟩ : syracuseStep 1353845 = 126923) (by norm_num)
theorem B1353869 : Blo 900574 1353869 := bbase (se 3 (by rfl) ⟨253850, by rfl⟩ : syracuseStep 1353869 = 507701) (by norm_num)
theorem B1353893 : Blo 900574 1353893 := bbase (se 4 (by rfl) ⟨126927, by rfl⟩ : syracuseStep 1353893 = 253855) (by norm_num)
theorem B1353917 : Blo 900574 1353917 := bbase (se 3 (by rfl) ⟨253859, by rfl⟩ : syracuseStep 1353917 = 507719) (by norm_num)
theorem B1353941 : Blo 900574 1353941 := bbase (se 7 (by rfl) ⟨15866, by rfl⟩ : syracuseStep 1353941 = 31733) (by norm_num)
theorem B1353965 : Blo 900574 1353965 := bbase (se 3 (by rfl) ⟨253868, by rfl⟩ : syracuseStep 1353965 = 507737) (by norm_num)
theorem B2894069 : Blo 900574 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B1353989 : Blo 900574 1353989 := bbase (se 4 (by rfl) ⟨126936, by rfl⟩ : syracuseStep 1353989 = 253873) (by norm_num)
theorem B1354013 : Blo 900574 1354013 := bbase (se 3 (by rfl) ⟨253877, by rfl⟩ : syracuseStep 1354013 = 507755) (by norm_num)
theorem B1354037 : Blo 900574 1354037 := bbase (se 5 (by rfl) ⟨63470, by rfl⟩ : syracuseStep 1354037 = 126941) (by norm_num)
theorem B1354061 : Blo 900574 1354061 := bbase (se 3 (by rfl) ⟨253886, by rfl⟩ : syracuseStep 1354061 = 507773) (by norm_num)
theorem B1714517 : Blo 900574 1714517 := bbase (se 10 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 1714517 = 5023) (by norm_num)
theorem B1354085 : Blo 900574 1354085 := bbase (se 4 (by rfl) ⟨126945, by rfl⟩ : syracuseStep 1354085 = 253891) (by norm_num)
theorem B2173301 : Blo 900574 2173301 := bbase (se 5 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 2173301 = 203747) (by norm_num)
theorem B1354109 : Blo 900574 1354109 := bbase (se 3 (by rfl) ⟨253895, by rfl⟩ : syracuseStep 1354109 = 507791) (by norm_num)
theorem B1354133 : Blo 900574 1354133 := bbase (se 6 (by rfl) ⟨31737, by rfl⟩ : syracuseStep 1354133 = 63475) (by norm_num)
theorem B1354157 : Blo 900574 1354157 := bbase (se 3 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 1354157 = 507809) (by norm_num)
theorem B1354181 : Blo 900574 1354181 := bbase (se 4 (by rfl) ⟨126954, by rfl⟩ : syracuseStep 1354181 = 253909) (by norm_num)
theorem B1354205 : Blo 900574 1354205 := bbase (se 3 (by rfl) ⟨253913, by rfl⟩ : syracuseStep 1354205 = 507827) (by norm_num)
theorem B1354229 : Blo 900574 1354229 := bbase (se 5 (by rfl) ⟨63479, by rfl⟩ : syracuseStep 1354229 = 126959) (by norm_num)
theorem B1354253 : Blo 900574 1354253 := bbase (se 3 (by rfl) ⟨253922, by rfl⟩ : syracuseStep 1354253 = 507845) (by norm_num)
theorem B1354277 : Blo 900574 1354277 := bbase (se 4 (by rfl) ⟨126963, by rfl⟩ : syracuseStep 1354277 = 253927) (by norm_num)
theorem B1354301 : Blo 900574 1354301 := bbase (se 3 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 1354301 = 507863) (by norm_num)
theorem B2566741 : Blo 900574 2566741 := bbase (se 8 (by rfl) ⟨15039, by rfl⟩ : syracuseStep 2566741 = 30079) (by norm_num)
theorem B10693205 : Blo 900574 10693205 := bbase (se 8 (by rfl) ⟨62655, by rfl⟩ : syracuseStep 10693205 = 125311) (by norm_num)
theorem B1354325 : Blo 900574 1354325 := bbase (se 8 (by rfl) ⟨7935, by rfl⟩ : syracuseStep 1354325 = 15871) (by norm_num)
theorem B1354349 : Blo 900574 1354349 := bbase (se 3 (by rfl) ⟨253940, by rfl⟩ : syracuseStep 1354349 = 507881) (by norm_num)
theorem B1354373 : Blo 900574 1354373 := bbase (se 4 (by rfl) ⟨126972, by rfl⟩ : syracuseStep 1354373 = 253945) (by norm_num)
theorem B1354397 : Blo 900574 1354397 := bbase (se 3 (by rfl) ⟨253949, by rfl⟩ : syracuseStep 1354397 = 507899) (by norm_num)
theorem B1354421 : Blo 900574 1354421 := bbase (se 5 (by rfl) ⟨63488, by rfl⟩ : syracuseStep 1354421 = 126977) (by norm_num)
theorem B1354445 : Blo 900574 1354445 := bbase (se 3 (by rfl) ⟨253958, by rfl⟩ : syracuseStep 1354445 = 507917) (by norm_num)
theorem B1354469 : Blo 900574 1354469 := bbase (se 4 (by rfl) ⟨126981, by rfl⟩ : syracuseStep 1354469 = 253963) (by norm_num)
theorem B1354493 : Blo 900574 1354493 := bbase (se 3 (by rfl) ⟨253967, by rfl⟩ : syracuseStep 1354493 = 507935) (by norm_num)
theorem B1354517 : Blo 900574 1354517 := bbase (se 6 (by rfl) ⟨31746, by rfl⟩ : syracuseStep 1354517 = 63493) (by norm_num)
theorem B1354541 : Blo 900574 1354541 := bbase (se 3 (by rfl) ⟨253976, by rfl⟩ : syracuseStep 1354541 = 507953) (by norm_num)
theorem B1354565 : Blo 900574 1354565 := bbase (se 4 (by rfl) ⟨126990, by rfl⟩ : syracuseStep 1354565 = 253981) (by norm_num)
theorem B1354589 : Blo 900574 1354589 := bbase (se 3 (by rfl) ⟨253985, by rfl⟩ : syracuseStep 1354589 = 507971) (by norm_num)
theorem B1354613 : Blo 900574 1354613 := bbase (se 5 (by rfl) ⟨63497, by rfl⟩ : syracuseStep 1354613 = 126995) (by norm_num)
theorem B1354637 : Blo 900574 1354637 := bbase (se 3 (by rfl) ⟨253994, by rfl⟩ : syracuseStep 1354637 = 507989) (by norm_num)
theorem B1354661 : Blo 900574 1354661 := bbase (se 4 (by rfl) ⟨126999, by rfl⟩ : syracuseStep 1354661 = 253999) (by norm_num)
theorem B1354685 : Blo 900574 1354685 := bbase (se 3 (by rfl) ⟨254003, by rfl⟩ : syracuseStep 1354685 = 508007) (by norm_num)
theorem B1354709 : Blo 900574 1354709 := bbase (se 7 (by rfl) ⟨15875, by rfl⟩ : syracuseStep 1354709 = 31751) (by norm_num)
theorem B1354733 : Blo 900574 1354733 := bbase (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) (by norm_num)
theorem B1354757 : Blo 900574 1354757 := bbase (se 4 (by rfl) ⟨127008, by rfl⟩ : syracuseStep 1354757 = 254017) (by norm_num)
theorem B1354781 : Blo 900574 1354781 := bbase (se 3 (by rfl) ⟨254021, by rfl⟩ : syracuseStep 1354781 = 508043) (by norm_num)
theorem B1354805 : Blo 900574 1354805 := bbase (se 5 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 1354805 = 127013) (by norm_num)
theorem B1715269 : Blo 900574 1715269 := bbase (se 4 (by rfl) ⟨160806, by rfl⟩ : syracuseStep 1715269 = 321613) (by norm_num)
theorem B1354829 : Blo 900574 1354829 := bbase (se 3 (by rfl) ⟨254030, by rfl⟩ : syracuseStep 1354829 = 508061) (by norm_num)
theorem B2174045 : Blo 900574 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B1354853 : Blo 900574 1354853 := bbase (se 4 (by rfl) ⟨127017, by rfl⟩ : syracuseStep 1354853 = 254035) (by norm_num)
theorem B1354877 : Blo 900574 1354877 := bbase (se 3 (by rfl) ⟨254039, by rfl⟩ : syracuseStep 1354877 = 508079) (by norm_num)
theorem B1354901 : Blo 900574 1354901 := bbase (se 6 (by rfl) ⟨31755, by rfl⟩ : syracuseStep 1354901 = 63511) (by norm_num)
theorem B1354925 : Blo 900574 1354925 := bbase (se 3 (by rfl) ⟨254048, by rfl⟩ : syracuseStep 1354925 = 508097) (by norm_num)
theorem B1354949 : Blo 900574 1354949 := bbase (se 4 (by rfl) ⟨127026, by rfl⟩ : syracuseStep 1354949 = 254053) (by norm_num)
theorem B1715413 : Blo 900574 1715413 := bbase (se 7 (by rfl) ⟨20102, by rfl⟩ : syracuseStep 1715413 = 40205) (by norm_num)
theorem B1354973 : Blo 900574 1354973 := bbase (se 3 (by rfl) ⟨254057, by rfl⟩ : syracuseStep 1354973 = 508115) (by norm_num)
theorem B1354997 : Blo 900574 1354997 := bbase (se 5 (by rfl) ⟨63515, by rfl⟩ : syracuseStep 1354997 = 127031) (by norm_num)
theorem B1355021 : Blo 900574 1355021 := bbase (se 3 (by rfl) ⟨254066, by rfl⟩ : syracuseStep 1355021 = 508133) (by norm_num)
theorem B4566293 : Blo 900574 4566293 := bbase (se 6 (by rfl) ⟨107022, by rfl⟩ : syracuseStep 4566293 = 214045) (by norm_num)
theorem B1355045 : Blo 900574 1355045 := bbase (se 4 (by rfl) ⟨127035, by rfl⟩ : syracuseStep 1355045 = 254071) (by norm_num)
theorem B961853 : Blo 900574 961853 := bbase (se 3 (by rfl) ⟨180347, by rfl⟩ : syracuseStep 961853 = 360695) (by norm_num)
theorem B1355069 : Blo 900574 1355069 := bbase (se 3 (by rfl) ⟨254075, by rfl⟩ : syracuseStep 1355069 = 508151) (by norm_num)
theorem B2436421 : Blo 900574 2436421 := bbase (se 4 (by rfl) ⟨228414, by rfl⟩ : syracuseStep 2436421 = 456829) (by norm_num)
theorem B1355093 : Blo 900574 1355093 := bbase (se 11 (by rfl) ⟨992, by rfl⟩ : syracuseStep 1355093 = 1985) (by norm_num)
theorem B1355117 : Blo 900574 1355117 := bbase (se 3 (by rfl) ⟨254084, by rfl⟩ : syracuseStep 1355117 = 508169) (by norm_num)
theorem B1715573 : Blo 900574 1715573 := bbase (se 5 (by rfl) ⟨80417, by rfl⟩ : syracuseStep 1715573 = 160835) (by norm_num)
theorem B961913 : Blo 900574 961913 := bbase (se 2 (by rfl) ⟨360717, by rfl⟩ : syracuseStep 961913 = 721435) (by norm_num)
theorem B1355141 : Blo 900574 1355141 := bbase (se 4 (by rfl) ⟨127044, by rfl⟩ : syracuseStep 1355141 = 254089) (by norm_num)
theorem B1486237 : Blo 900574 1486237 := bbase (se 3 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 1486237 = 557339) (by norm_num)
theorem B1355165 : Blo 900574 1355165 := bbase (se 3 (by rfl) ⟨254093, by rfl⟩ : syracuseStep 1355165 = 508187) (by norm_num)
theorem B1355189 : Blo 900574 1355189 := bbase (se 5 (by rfl) ⟨63524, by rfl⟩ : syracuseStep 1355189 = 127049) (by norm_num)
theorem B1355213 : Blo 900574 1355213 := bbase (se 3 (by rfl) ⟨254102, by rfl⟩ : syracuseStep 1355213 = 508205) (by norm_num)
theorem B1355237 : Blo 900574 1355237 := bbase (se 4 (by rfl) ⟨127053, by rfl⟩ : syracuseStep 1355237 = 254107) (by norm_num)
theorem B962041 : Blo 900574 962041 := bbase (se 2 (by rfl) ⟨360765, by rfl⟩ : syracuseStep 962041 = 721531) (by norm_num)
theorem B1355261 : Blo 900574 1355261 := bbase (se 3 (by rfl) ⟨254111, by rfl⟩ : syracuseStep 1355261 = 508223) (by norm_num)
theorem B1715717 : Blo 900574 1715717 := bbase (se 4 (by rfl) ⟨160848, by rfl⟩ : syracuseStep 1715717 = 321697) (by norm_num)
theorem B1355285 : Blo 900574 1355285 := bbase (se 6 (by rfl) ⟨31764, by rfl⟩ : syracuseStep 1355285 = 63529) (by norm_num)
theorem B1355309 : Blo 900574 1355309 := bbase (se 3 (by rfl) ⟨254120, by rfl⟩ : syracuseStep 1355309 = 508241) (by norm_num)
theorem B1355333 : Blo 900574 1355333 := bbase (se 4 (by rfl) ⟨127062, by rfl⟩ : syracuseStep 1355333 = 254125) (by norm_num)
theorem B1355357 : Blo 900574 1355357 := bbase (se 3 (by rfl) ⟨254129, by rfl⟩ : syracuseStep 1355357 = 508259) (by norm_num)
theorem B3092069 : Blo 900574 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B1355381 : Blo 900574 1355381 := bbase (se 5 (by rfl) ⟨63533, by rfl⟩ : syracuseStep 1355381 = 127067) (by norm_num)
theorem B1355405 : Blo 900574 1355405 := bbase (se 3 (by rfl) ⟨254138, by rfl⟩ : syracuseStep 1355405 = 508277) (by norm_num)
theorem B1355429 : Blo 900574 1355429 := bbase (se 4 (by rfl) ⟨127071, by rfl⟩ : syracuseStep 1355429 = 254143) (by norm_num)
theorem B1158833 : Blo 900574 1158833 := bbase (se 2 (by rfl) ⟨434562, by rfl⟩ : syracuseStep 1158833 = 869125) (by norm_num)
theorem B1355453 : Blo 900574 1355453 := bbase (se 3 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 1355453 = 508295) (by norm_num)
theorem B1355477 : Blo 900574 1355477 := bbase (se 7 (by rfl) ⟨15884, by rfl⟩ : syracuseStep 1355477 = 31769) (by norm_num)
theorem B1355501 : Blo 900574 1355501 := bbase (se 3 (by rfl) ⟨254156, by rfl⟩ : syracuseStep 1355501 = 508313) (by norm_num)
theorem B1355525 : Blo 900574 1355525 := bbase (se 4 (by rfl) ⟨127080, by rfl⟩ : syracuseStep 1355525 = 254161) (by norm_num)
theorem B1355549 : Blo 900574 1355549 := bbase (se 3 (by rfl) ⟨254165, by rfl⟩ : syracuseStep 1355549 = 508331) (by norm_num)
theorem B1716005 : Blo 900574 1716005 := bbase (se 4 (by rfl) ⟨160875, by rfl⟩ : syracuseStep 1716005 = 321751) (by norm_num)
theorem B1978157 : Blo 900574 1978157 := bbase (se 3 (by rfl) ⟨370904, by rfl⟩ : syracuseStep 1978157 = 741809) (by norm_num)
theorem B1355573 : Blo 900574 1355573 := bbase (se 5 (by rfl) ⟨63542, by rfl⟩ : syracuseStep 1355573 = 127085) (by norm_num)
theorem B1355597 : Blo 900574 1355597 := bbase (se 3 (by rfl) ⟨254174, by rfl⟩ : syracuseStep 1355597 = 508349) (by norm_num)
theorem B1355621 : Blo 900574 1355621 := bbase (se 4 (by rfl) ⟨127089, by rfl⟩ : syracuseStep 1355621 = 254179) (by norm_num)
theorem B1027957 : Blo 900574 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B1355645 : Blo 900574 1355645 := bbase (se 3 (by rfl) ⟨254183, by rfl⟩ : syracuseStep 1355645 = 508367) (by norm_num)
theorem B1355669 : Blo 900574 1355669 := bbase (se 6 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 1355669 = 63547) (by norm_num)
theorem B1355693 : Blo 900574 1355693 := bbase (se 3 (by rfl) ⟨254192, by rfl⟩ : syracuseStep 1355693 = 508385) (by norm_num)
theorem B962485 : Blo 900574 962485 := bbase (se 5 (by rfl) ⟨45116, by rfl⟩ : syracuseStep 962485 = 90233) (by norm_num)
theorem B1716157 : Blo 900574 1716157 := bbase (se 3 (by rfl) ⟨321779, by rfl⟩ : syracuseStep 1716157 = 643559) (by norm_num)
theorem B1355717 : Blo 900574 1355717 := bbase (se 4 (by rfl) ⟨127098, by rfl⟩ : syracuseStep 1355717 = 254197) (by norm_num)
theorem B1355741 : Blo 900574 1355741 := bbase (se 3 (by rfl) ⟨254201, by rfl⟩ : syracuseStep 1355741 = 508403) (by norm_num)
theorem B1355765 : Blo 900574 1355765 := bbase (se 5 (by rfl) ⟨63551, by rfl⟩ : syracuseStep 1355765 = 127103) (by norm_num)
theorem B1355789 : Blo 900574 1355789 := bbase (se 3 (by rfl) ⟨254210, by rfl⟩ : syracuseStep 1355789 = 508421) (by norm_num)
theorem B10268693 : Blo 900574 10268693 := bbase (se 6 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 10268693 = 481345) (by norm_num)
theorem B1355813 : Blo 900574 1355813 := bbase (se 4 (by rfl) ⟨127107, by rfl⟩ : syracuseStep 1355813 = 254215) (by norm_num)
theorem B962605 : Blo 900574 962605 := bbase (se 3 (by rfl) ⟨180488, by rfl⟩ : syracuseStep 962605 = 360977) (by norm_num)
theorem B1355837 : Blo 900574 1355837 := bbase (se 3 (by rfl) ⟨254219, by rfl⟩ : syracuseStep 1355837 = 508439) (by norm_num)
theorem B18493525 : Blo 900574 18493525 := bbase (se 8 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 18493525 = 216721) (by norm_num)
theorem B3518549 : Blo 900574 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B1355861 : Blo 900574 1355861 := bbase (se 8 (by rfl) ⟨7944, by rfl⟩ : syracuseStep 1355861 = 15889) (by norm_num)
theorem B1355885 : Blo 900574 1355885 := bbase (se 3 (by rfl) ⟨254228, by rfl⟩ : syracuseStep 1355885 = 508457) (by norm_num)
theorem B1355909 : Blo 900574 1355909 := bbase (se 4 (by rfl) ⟨127116, by rfl⟩ : syracuseStep 1355909 = 254233) (by norm_num)
theorem B1355933 : Blo 900574 1355933 := bbase (se 3 (by rfl) ⟨254237, by rfl⟩ : syracuseStep 1355933 = 508475) (by norm_num)
theorem B1519789 : Blo 900574 1519789 := bbase (se 3 (by rfl) ⟨284960, by rfl⟩ : syracuseStep 1519789 = 569921) (by norm_num)
theorem B1355957 : Blo 900574 1355957 := bbase (se 5 (by rfl) ⟨63560, by rfl⟩ : syracuseStep 1355957 = 127121) (by norm_num)
theorem B1355981 : Blo 900574 1355981 := bbase (se 3 (by rfl) ⟨254246, by rfl⟩ : syracuseStep 1355981 = 508493) (by norm_num)
theorem B1356005 : Blo 900574 1356005 := bbase (se 4 (by rfl) ⟨127125, by rfl⟩ : syracuseStep 1356005 = 254251) (by norm_num)
theorem B1716461 : Blo 900574 1716461 := bbase (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) (by norm_num)
theorem B1356029 : Blo 900574 1356029 := bbase (se 3 (by rfl) ⟨254255, by rfl⟩ : syracuseStep 1356029 = 508511) (by norm_num)
theorem B1519877 : Blo 900574 1519877 := bbase (se 4 (by rfl) ⟨142488, by rfl⟩ : syracuseStep 1519877 = 284977) (by norm_num)
theorem B1356053 : Blo 900574 1356053 := bbase (se 6 (by rfl) ⟨31782, by rfl⟩ : syracuseStep 1356053 = 63565) (by norm_num)
theorem B962857 : Blo 900574 962857 := bbase (se 2 (by rfl) ⟨361071, by rfl⟩ : syracuseStep 962857 = 722143) (by norm_num)
theorem B962861 : Blo 900574 962861 := bbase (se 3 (by rfl) ⟨180536, by rfl⟩ : syracuseStep 962861 = 361073) (by norm_num)
theorem B1356077 : Blo 900574 1356077 := bbase (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) (by norm_num)
theorem B1159489 : Blo 900574 1159489 := bbase (se 2 (by rfl) ⟨434808, by rfl⟩ : syracuseStep 1159489 = 869617) (by norm_num)
theorem B1356101 : Blo 900574 1356101 := bbase (se 4 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 1356101 = 254269) (by norm_num)
theorem B1356125 : Blo 900574 1356125 := bbase (se 3 (by rfl) ⟨254273, by rfl⟩ : syracuseStep 1356125 = 508547) (by norm_num)
theorem B1356149 : Blo 900574 1356149 := bbase (se 5 (by rfl) ⟨63569, by rfl⟩ : syracuseStep 1356149 = 127139) (by norm_num)
theorem B1520005 : Blo 900574 1520005 := bbase (se 4 (by rfl) ⟨142500, by rfl⟩ : syracuseStep 1520005 = 285001) (by norm_num)
theorem B1356173 : Blo 900574 1356173 := bbase (se 3 (by rfl) ⟨254282, by rfl⟩ : syracuseStep 1356173 = 508565) (by norm_num)
theorem B1356197 : Blo 900574 1356197 := bbase (se 4 (by rfl) ⟨127143, by rfl⟩ : syracuseStep 1356197 = 254287) (by norm_num)
theorem B1356221 : Blo 900574 1356221 := bbase (se 3 (by rfl) ⟨254291, by rfl⟩ : syracuseStep 1356221 = 508583) (by norm_num)
theorem B2437589 : Blo 900574 2437589 := bbase (se 7 (by rfl) ⟨28565, by rfl⟩ : syracuseStep 2437589 = 57131) (by norm_num)
theorem B1356245 : Blo 900574 1356245 := bbase (se 7 (by rfl) ⟨15893, by rfl⟩ : syracuseStep 1356245 = 31787) (by norm_num)
theorem B1520093 : Blo 900574 1520093 := bbase (se 3 (by rfl) ⟨285017, by rfl⟩ : syracuseStep 1520093 = 570035) (by norm_num)
theorem B1356269 : Blo 900574 1356269 := bbase (se 3 (by rfl) ⟨254300, by rfl⟩ : syracuseStep 1356269 = 508601) (by norm_num)
theorem B1356293 : Blo 900574 1356293 := bbase (se 4 (by rfl) ⟨127152, by rfl⟩ : syracuseStep 1356293 = 254305) (by norm_num)
theorem B9777685 : Blo 900574 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B1356317 : Blo 900574 1356317 := bbase (se 3 (by rfl) ⟨254309, by rfl⟩ : syracuseStep 1356317 = 508619) (by norm_num)
theorem B4567589 : Blo 900574 4567589 := bbase (se 4 (by rfl) ⟨428211, by rfl⟩ : syracuseStep 4567589 = 856423) (by norm_num)
theorem B1356341 : Blo 900574 1356341 := bbase (se 5 (by rfl) ⟨63578, by rfl⟩ : syracuseStep 1356341 = 127157) (by norm_num)
theorem B1356365 : Blo 900574 1356365 := bbase (se 3 (by rfl) ⟨254318, by rfl⟩ : syracuseStep 1356365 = 508637) (by norm_num)
theorem B1520221 : Blo 900574 1520221 := bbase (se 3 (by rfl) ⟨285041, by rfl⟩ : syracuseStep 1520221 = 570083) (by norm_num)
theorem B1356389 : Blo 900574 1356389 := bbase (se 4 (by rfl) ⟨127161, by rfl⟩ : syracuseStep 1356389 = 254323) (by norm_num)
theorem B1356413 : Blo 900574 1356413 := bbase (se 3 (by rfl) ⟨254327, by rfl⟩ : syracuseStep 1356413 = 508655) (by norm_num)
theorem B1159817 : Blo 900574 1159817 := bbase (se 2 (by rfl) ⟨434931, by rfl⟩ : syracuseStep 1159817 = 869863) (by norm_num)
theorem B1356437 : Blo 900574 1356437 := bbase (se 6 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 1356437 = 63583) (by norm_num)
theorem B1356461 : Blo 900574 1356461 := bbase (se 3 (by rfl) ⟨254336, by rfl⟩ : syracuseStep 1356461 = 508673) (by norm_num)
theorem B4108981 : Blo 900574 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B1520309 : Blo 900574 1520309 := bbase (se 5 (by rfl) ⟨71264, by rfl⟩ : syracuseStep 1520309 = 142529) (by norm_num)
theorem B1356485 : Blo 900574 1356485 := bbase (se 4 (by rfl) ⟨127170, by rfl⟩ : syracuseStep 1356485 = 254341) (by norm_num)
theorem B1356509 : Blo 900574 1356509 := bbase (se 3 (by rfl) ⟨254345, by rfl⟩ : syracuseStep 1356509 = 508691) (by norm_num)
theorem B1356533 : Blo 900574 1356533 := bbase (se 5 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 1356533 = 127175) (by norm_num)
theorem B1356557 : Blo 900574 1356557 := bbase (se 3 (by rfl) ⟨254354, by rfl⟩ : syracuseStep 1356557 = 508709) (by norm_num)
theorem B1356581 : Blo 900574 1356581 := bbase (se 4 (by rfl) ⟨127179, by rfl⟩ : syracuseStep 1356581 = 254359) (by norm_num)
theorem B1520437 : Blo 900574 1520437 := bbase (se 5 (by rfl) ⟨71270, by rfl⟩ : syracuseStep 1520437 = 142541) (by norm_num)
theorem B1356605 : Blo 900574 1356605 := bbase (se 3 (by rfl) ⟨254363, by rfl⟩ : syracuseStep 1356605 = 508727) (by norm_num)
theorem B1356629 : Blo 900574 1356629 := bbase (se 9 (by rfl) ⟨3974, by rfl⟩ : syracuseStep 1356629 = 7949) (by norm_num)
theorem B963425 : Blo 900574 963425 := bbase (se 2 (by rfl) ⟨361284, by rfl⟩ : syracuseStep 963425 = 722569) (by norm_num)
theorem B1356653 : Blo 900574 1356653 := bbase (se 3 (by rfl) ⟨254372, by rfl⟩ : syracuseStep 1356653 = 508745) (by norm_num)
theorem B3421061 : Blo 900574 3421061 := bbase (se 4 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 3421061 = 641449) (by norm_num)
theorem B1356677 : Blo 900574 1356677 := bbase (se 4 (by rfl) ⟨127188, by rfl⟩ : syracuseStep 1356677 = 254377) (by norm_num)
theorem B1520525 : Blo 900574 1520525 := bbase (se 3 (by rfl) ⟨285098, by rfl⟩ : syracuseStep 1520525 = 570197) (by norm_num)
theorem B1356701 : Blo 900574 1356701 := bbase (se 3 (by rfl) ⟨254381, by rfl⟩ : syracuseStep 1356701 = 508763) (by norm_num)
theorem B1160101 : Blo 900574 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B1356725 : Blo 900574 1356725 := bbase (se 5 (by rfl) ⟨63596, by rfl⟩ : syracuseStep 1356725 = 127193) (by norm_num)
theorem B1356749 : Blo 900574 1356749 := bbase (se 3 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 1356749 = 508781) (by norm_num)
theorem B1717213 : Blo 900574 1717213 := bbase (se 3 (by rfl) ⟨321977, by rfl⟩ : syracuseStep 1717213 = 643955) (by norm_num)
theorem B1356773 : Blo 900574 1356773 := bbase (se 4 (by rfl) ⟨127197, by rfl⟩ : syracuseStep 1356773 = 254395) (by norm_num)
theorem B1356797 : Blo 900574 1356797 := bbase (se 3 (by rfl) ⟨254399, by rfl⟩ : syracuseStep 1356797 = 508799) (by norm_num)
theorem B1520653 : Blo 900574 1520653 := bbase (se 3 (by rfl) ⟨285122, by rfl⟩ : syracuseStep 1520653 = 570245) (by norm_num)
theorem B1356821 : Blo 900574 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B963613 : Blo 900574 963613 := bbase (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) (by norm_num)
theorem B1356845 : Blo 900574 1356845 := bbase (se 3 (by rfl) ⟨254408, by rfl⟩ : syracuseStep 1356845 = 508817) (by norm_num)
theorem B1160281 : Blo 900574 1160281 := bbase (se 2 (by rfl) ⟨435105, by rfl⟩ : syracuseStep 1160281 = 870211) (by norm_num)
theorem B1520741 : Blo 900574 1520741 := bbase (se 4 (by rfl) ⟨142569, by rfl⟩ : syracuseStep 1520741 = 285139) (by norm_num)
theorem B3421349 : Blo 900574 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B1520869 : Blo 900574 1520869 := bbase (se 4 (by rfl) ⟨142581, by rfl⟩ : syracuseStep 1520869 = 285163) (by norm_num)
theorem B1520957 : Blo 900574 1520957 := bbase (se 3 (by rfl) ⟨285179, by rfl⟩ : syracuseStep 1520957 = 570359) (by norm_num)
theorem B2897221 : Blo 900574 2897221 := bbase (se 4 (by rfl) ⟨271614, by rfl⟩ : syracuseStep 2897221 = 543229) (by norm_num)
theorem B2569589 : Blo 900574 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B1521085 : Blo 900574 1521085 := bbase (se 3 (by rfl) ⟨285203, by rfl⟩ : syracuseStep 1521085 = 570407) (by norm_num)
theorem B6174197 : Blo 900574 6174197 := bbase (se 5 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 6174197 = 578831) (by norm_num)
theorem B1521173 : Blo 900574 1521173 := bbase (se 6 (by rfl) ⟨35652, by rfl⟩ : syracuseStep 1521173 = 71305) (by norm_num)
theorem B1521301 : Blo 900574 1521301 := bbase (se 6 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 1521301 = 71311) (by norm_num)
theorem B1521389 : Blo 900574 1521389 := bbase (se 3 (by rfl) ⟨285260, by rfl⟩ : syracuseStep 1521389 = 570521) (by norm_num)
theorem B3847925 : Blo 900574 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B4568885 : Blo 900574 4568885 := bbase (se 5 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 4568885 = 428333) (by norm_num)
theorem B964433 : Blo 900574 964433 := bbase (se 2 (by rfl) ⟨361662, by rfl⟩ : syracuseStep 964433 = 723325) (by norm_num)
theorem B1521517 : Blo 900574 1521517 := bbase (se 3 (by rfl) ⟨285284, by rfl⟩ : syracuseStep 1521517 = 570569) (by norm_num)
theorem B1030033 : Blo 900574 1030033 := bbase (se 2 (by rfl) ⟨386262, by rfl⟩ : syracuseStep 1030033 = 772525) (by norm_num)
theorem B1521605 : Blo 900574 1521605 := bbase (se 4 (by rfl) ⟨142650, by rfl⟩ : syracuseStep 1521605 = 285301) (by norm_num)
theorem B6862805 : Blo 900574 6862805 := bbase (se 7 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 6862805 = 160847) (by norm_num)
theorem B3094517 : Blo 900574 3094517 := bbase (se 5 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 3094517 = 290111) (by norm_num)
theorem B1521733 : Blo 900574 1521733 := bbase (se 4 (by rfl) ⟨142662, by rfl⟩ : syracuseStep 1521733 = 285325) (by norm_num)
theorem B1521821 : Blo 900574 1521821 := bbase (se 3 (by rfl) ⟨285341, by rfl⟩ : syracuseStep 1521821 = 570683) (by norm_num)
theorem B964877 : Blo 900574 964877 := bbase (se 3 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 964877 = 361829) (by norm_num)
theorem B1521949 : Blo 900574 1521949 := bbase (se 3 (by rfl) ⟨285365, by rfl⟩ : syracuseStep 1521949 = 570731) (by norm_num)
theorem B3422533 : Blo 900574 3422533 := bbase (se 4 (by rfl) ⟨320862, by rfl⟩ : syracuseStep 3422533 = 641725) (by norm_num)
theorem B1030493 : Blo 900574 1030493 := bbase (se 3 (by rfl) ⟨193217, by rfl⟩ : syracuseStep 1030493 = 386435) (by norm_num)
theorem B1522037 : Blo 900574 1522037 := bbase (se 5 (by rfl) ⟨71345, by rfl⟩ : syracuseStep 1522037 = 142691) (by norm_num)
theorem B7715189 : Blo 900574 7715189 := bbase (se 5 (by rfl) ⟨361649, by rfl⟩ : syracuseStep 7715189 = 723299) (by norm_num)
theorem B1980805 : Blo 900574 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B1522165 : Blo 900574 1522165 := bbase (se 5 (by rfl) ⟨71351, by rfl⟩ : syracuseStep 1522165 = 142703) (by norm_num)
theorem B965125 : Blo 900574 965125 := bbase (se 4 (by rfl) ⟨90480, by rfl⟩ : syracuseStep 965125 = 180961) (by norm_num)
theorem B2570773 : Blo 900574 2570773 := bbase (se 6 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 2570773 = 120505) (by norm_num)
theorem B1522253 : Blo 900574 1522253 := bbase (se 3 (by rfl) ⟨285422, by rfl⟩ : syracuseStep 1522253 = 570845) (by norm_num)
theorem B3422837 : Blo 900574 3422837 := bbase (se 5 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 3422837 = 320891) (by norm_num)
theorem B2570933 : Blo 900574 2570933 := bbase (se 5 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 2570933 = 241025) (by norm_num)
theorem B1522381 : Blo 900574 1522381 := bbase (se 3 (by rfl) ⟨285446, by rfl⟩ : syracuseStep 1522381 = 570893) (by norm_num)
theorem B1522469 : Blo 900574 1522469 := bbase (se 4 (by rfl) ⟨142731, by rfl⟩ : syracuseStep 1522469 = 285463) (by norm_num)
theorem B1522597 : Blo 900574 1522597 := bbase (se 4 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 1522597 = 285487) (by norm_num)
theorem B2571173 : Blo 900574 2571173 := bbase (se 4 (by rfl) ⟨241047, by rfl⟩ : syracuseStep 2571173 = 482095) (by norm_num)
theorem B1031077 : Blo 900574 1031077 := bbase (se 4 (by rfl) ⟨96663, by rfl⟩ : syracuseStep 1031077 = 193327) (by norm_num)
theorem B965557 : Blo 900574 965557 := bbase (se 5 (by rfl) ⟨45260, by rfl⟩ : syracuseStep 965557 = 90521) (by norm_num)
theorem B1522685 : Blo 900574 1522685 := bbase (se 3 (by rfl) ⟨285503, by rfl⟩ : syracuseStep 1522685 = 571007) (by norm_num)
theorem B965629 : Blo 900574 965629 := bbase (se 3 (by rfl) ⟨181055, by rfl⟩ : syracuseStep 965629 = 362111) (by norm_num)
theorem B5782549 : Blo 900574 5782549 := bbase (se 6 (by rfl) ⟨135528, by rfl⟩ : syracuseStep 5782549 = 271057) (by norm_num)
theorem B4570181 : Blo 900574 4570181 := bbase (se 4 (by rfl) ⟨428454, by rfl⟩ : syracuseStep 4570181 = 856909) (by norm_num)
theorem B2571365 : Blo 900574 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B1031273 : Blo 900574 1031273 := bbase (se 2 (by rfl) ⟨386727, by rfl⟩ : syracuseStep 1031273 = 773455) (by norm_num)
theorem B1522813 : Blo 900574 1522813 := bbase (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) (by norm_num)
theorem B1522901 : Blo 900574 1522901 := bbase (se 7 (by rfl) ⟨17846, by rfl⟩ : syracuseStep 1522901 = 35693) (by norm_num)
theorem B1523029 : Blo 900574 1523029 := bbase (se 11 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 1523029 = 2231) (by norm_num)
theorem B1523117 : Blo 900574 1523117 := bbase (se 3 (by rfl) ⟨285584, by rfl⟩ : syracuseStep 1523117 = 571169) (by norm_num)
theorem B1523245 : Blo 900574 1523245 := bbase (se 3 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 1523245 = 571217) (by norm_num)
theorem B2637413 : Blo 900574 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B1523333 : Blo 900574 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B6602485 : Blo 900574 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B1523461 : Blo 900574 1523461 := bbase (se 4 (by rfl) ⟨142824, by rfl⟩ : syracuseStep 1523461 = 285649) (by norm_num)
theorem B1523549 : Blo 900574 1523549 := bbase (se 3 (by rfl) ⟨285665, by rfl⟩ : syracuseStep 1523549 = 571331) (by norm_num)
theorem B11583445 : Blo 900574 11583445 := bbase (se 7 (by rfl) ⟨135743, by rfl⟩ : syracuseStep 11583445 = 271487) (by norm_num)
theorem B1523677 : Blo 900574 1523677 := bbase (se 3 (by rfl) ⟨285689, by rfl⟩ : syracuseStep 1523677 = 571379) (by norm_num)
theorem B1523765 : Blo 900574 1523765 := bbase (se 5 (by rfl) ⟨71426, by rfl⟩ : syracuseStep 1523765 = 142853) (by norm_num)
theorem B2572357 : Blo 900574 2572357 := bbase (se 4 (by rfl) ⟨241158, by rfl⟩ : syracuseStep 2572357 = 482317) (by norm_num)
theorem B1523893 : Blo 900574 1523893 := bbase (se 5 (by rfl) ⟨71432, by rfl⟩ : syracuseStep 1523893 = 142865) (by norm_num)
theorem B1523981 : Blo 900574 1523981 := bbase (se 3 (by rfl) ⟨285746, by rfl⟩ : syracuseStep 1523981 = 571493) (by norm_num)
theorem B4342085 : Blo 900574 4342085 := bbase (se 4 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 4342085 = 814141) (by norm_num)
theorem B4571477 : Blo 900574 4571477 := bbase (se 10 (by rfl) ⟨6696, by rfl⟩ : syracuseStep 4571477 = 13393) (by norm_num)
theorem B1524109 : Blo 900574 1524109 := bbase (se 3 (by rfl) ⟨285770, by rfl⟩ : syracuseStep 1524109 = 571541) (by norm_num)
theorem B10961365 : Blo 900574 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B1524197 : Blo 900574 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B1524325 : Blo 900574 1524325 := bbase (se 4 (by rfl) ⟨142905, by rfl⟩ : syracuseStep 1524325 = 285811) (by norm_num)
theorem B1950325 : Blo 900574 1950325 := bbase (se 5 (by rfl) ⟨91421, by rfl⟩ : syracuseStep 1950325 = 182843) (by norm_num)
theorem B3424949 : Blo 900574 3424949 := bbase (se 5 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 3424949 = 321089) (by norm_num)
theorem B1524413 : Blo 900574 1524413 := bbase (se 3 (by rfl) ⟨285827, by rfl⟩ : syracuseStep 1524413 = 571655) (by norm_num)
theorem B4113125 : Blo 900574 4113125 := bbase (se 4 (by rfl) ⟨385605, by rfl⟩ : syracuseStep 4113125 = 771211) (by norm_num)
theorem B1098505 : Blo 900574 1098505 := bbase (se 2 (by rfl) ⟨411939, by rfl⟩ : syracuseStep 1098505 = 823879) (by norm_num)
theorem B1393453 : Blo 900574 1393453 := bbase (se 3 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 1393453 = 522545) (by norm_num)
theorem B1524541 : Blo 900574 1524541 := bbase (se 3 (by rfl) ⟨285851, by rfl⟩ : syracuseStep 1524541 = 571703) (by norm_num)
theorem B1098617 : Blo 900574 1098617 := bbase (se 2 (by rfl) ⟨411981, by rfl⟩ : syracuseStep 1098617 = 823963) (by norm_num)
theorem B2311037 : Blo 900574 2311037 := bbase (se 3 (by rfl) ⟨433319, by rfl⟩ : syracuseStep 2311037 = 866639) (by norm_num)
theorem B1524629 : Blo 900574 1524629 := bbase (se 6 (by rfl) ⟨35733, by rfl⟩ : syracuseStep 1524629 = 71467) (by norm_num)
theorem B3425237 : Blo 900574 3425237 := bbase (se 7 (by rfl) ⟨40139, by rfl⟩ : syracuseStep 3425237 = 80279) (by norm_num)
theorem B1524757 : Blo 900574 1524757 := bbase (se 6 (by rfl) ⟨35736, by rfl⟩ : syracuseStep 1524757 = 71473) (by norm_num)
theorem B1524845 : Blo 900574 1524845 := bbase (se 3 (by rfl) ⟨285908, by rfl⟩ : syracuseStep 1524845 = 571817) (by norm_num)
theorem B2573461 : Blo 900574 2573461 := bbase (se 6 (by rfl) ⟨60315, by rfl⟩ : syracuseStep 2573461 = 120631) (by norm_num)
theorem B1524973 : Blo 900574 1524973 := bbase (se 3 (by rfl) ⟨285932, by rfl⟩ : syracuseStep 1524973 = 571865) (by norm_num)
theorem B7718165 : Blo 900574 7718165 := bbase (se 6 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 7718165 = 361789) (by norm_num)
theorem B1525061 : Blo 900574 1525061 := bbase (se 4 (by rfl) ⟨142974, by rfl⟩ : syracuseStep 1525061 = 285949) (by norm_num)
theorem B1951061 : Blo 900574 1951061 := bbase (se 12 (by rfl) ⟨714, by rfl⟩ : syracuseStep 1951061 = 1429) (by norm_num)
theorem B2442629 : Blo 900574 2442629 := bbase (se 4 (by rfl) ⟨228996, by rfl⟩ : syracuseStep 2442629 = 457993) (by norm_num)
theorem B1525189 : Blo 900574 1525189 := bbase (se 4 (by rfl) ⟨142986, by rfl⟩ : syracuseStep 1525189 = 285973) (by norm_num)
theorem B1525277 : Blo 900574 1525277 := bbase (se 3 (by rfl) ⟨285989, by rfl⟩ : syracuseStep 1525277 = 571979) (by norm_num)
theorem B1099333 : Blo 900574 1099333 := bbase (se 4 (by rfl) ⟨103062, by rfl⟩ : syracuseStep 1099333 = 206125) (by norm_num)
theorem B2475605 : Blo 900574 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B4572773 : Blo 900574 4572773 := bbase (se 4 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 4572773 = 857395) (by norm_num)
theorem B1525405 : Blo 900574 1525405 := bbase (se 3 (by rfl) ⟨286013, by rfl⟩ : syracuseStep 1525405 = 572027) (by norm_num)
theorem B1525493 : Blo 900574 1525493 := bbase (se 5 (by rfl) ⟨71507, by rfl⟩ : syracuseStep 1525493 = 143015) (by norm_num)
theorem B1525621 : Blo 900574 1525621 := bbase (se 5 (by rfl) ⟨71513, by rfl⟩ : syracuseStep 1525621 = 143027) (by norm_num)
theorem B3852197 : Blo 900574 3852197 := bbase (se 4 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 3852197 = 722287) (by norm_num)
theorem B1525709 : Blo 900574 1525709 := bbase (se 3 (by rfl) ⟨286070, by rfl⟩ : syracuseStep 1525709 = 572141) (by norm_num)
theorem B3655733 : Blo 900574 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B1525837 : Blo 900574 1525837 := bbase (se 3 (by rfl) ⟨286094, by rfl⟩ : syracuseStep 1525837 = 572189) (by norm_num)
theorem B3426421 : Blo 900574 3426421 := bbase (se 5 (by rfl) ⟨160613, by rfl⟩ : syracuseStep 3426421 = 321227) (by norm_num)
theorem B1525925 : Blo 900574 1525925 := bbase (se 4 (by rfl) ⟨143055, by rfl⟩ : syracuseStep 1525925 = 286111) (by norm_num)
theorem B4344101 : Blo 900574 4344101 := bbase (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) (by norm_num)
theorem B1526053 : Blo 900574 1526053 := bbase (se 4 (by rfl) ⟨143067, by rfl⟩ : syracuseStep 1526053 = 286135) (by norm_num)
theorem B2279765 : Blo 900574 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B1526141 : Blo 900574 1526141 := bbase (se 3 (by rfl) ⟨286151, by rfl⟩ : syracuseStep 1526141 = 572303) (by norm_num)
theorem B3426725 : Blo 900574 3426725 := bbase (se 4 (by rfl) ⟨321255, by rfl⟩ : syracuseStep 3426725 = 642511) (by norm_num)
theorem B4344293 : Blo 900574 4344293 := bbase (se 4 (by rfl) ⟨407277, by rfl⟩ : syracuseStep 4344293 = 814555) (by norm_num)
theorem B1526269 : Blo 900574 1526269 := bbase (se 3 (by rfl) ⟨286175, by rfl⟩ : syracuseStep 1526269 = 572351) (by norm_num)
theorem B2476565 : Blo 900574 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B1526357 : Blo 900574 1526357 := bbase (se 8 (by rfl) ⟨8943, by rfl⟩ : syracuseStep 1526357 = 17887) (by norm_num)
theorem B2574965 : Blo 900574 2574965 := bbase (se 5 (by rfl) ⟨120701, by rfl⟩ : syracuseStep 2574965 = 241403) (by norm_num)
theorem B2280109 : Blo 900574 2280109 := bbase (se 3 (by rfl) ⟨427520, by rfl⟩ : syracuseStep 2280109 = 855041) (by norm_num)
theorem B1854181 : Blo 900574 1854181 := bbase (se 4 (by rfl) ⟨173829, by rfl⟩ : syracuseStep 1854181 = 347659) (by norm_num)
theorem B2280221 : Blo 900574 2280221 := bbase (se 3 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 2280221 = 855083) (by norm_num)
theorem B4574069 : Blo 900574 4574069 := bbase (se 5 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 4574069 = 428819) (by norm_num)
theorem B2280413 : Blo 900574 2280413 := bbase (se 3 (by rfl) ⟨427577, by rfl⟩ : syracuseStep 2280413 = 855155) (by norm_num)
theorem B1625189 : Blo 900574 1625189 := bbase (se 4 (by rfl) ⟨152361, by rfl⟩ : syracuseStep 1625189 = 304723) (by norm_num)
theorem B2280757 : Blo 900574 2280757 := bbase (se 5 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 2280757 = 213821) (by norm_num)
theorem B2280869 : Blo 900574 2280869 := bbase (se 4 (by rfl) ⟨213831, by rfl⟩ : syracuseStep 2280869 = 427663) (by norm_num)
theorem B2281061 : Blo 900574 2281061 := bbase (se 4 (by rfl) ⟨213849, by rfl⟩ : syracuseStep 2281061 = 427699) (by norm_num)
theorem B3853973 : Blo 900574 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B2608805 : Blo 900574 2608805 := bbase (se 4 (by rfl) ⟨244575, by rfl⟩ : syracuseStep 2608805 = 489151) (by norm_num)
theorem B1953589 : Blo 900574 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B3854213 : Blo 900574 3854213 := bbase (se 4 (by rfl) ⟨361332, by rfl⟩ : syracuseStep 3854213 = 722665) (by norm_num)
theorem B2281405 : Blo 900574 2281405 := bbase (se 3 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 2281405 = 855527) (by norm_num)
theorem B1626149 : Blo 900574 1626149 := bbase (se 4 (by rfl) ⟨152451, by rfl⟩ : syracuseStep 1626149 = 304903) (by norm_num)
theorem B2281517 : Blo 900574 2281517 := bbase (se 3 (by rfl) ⟨427784, by rfl⟩ : syracuseStep 2281517 = 855569) (by norm_num)
theorem B4575365 : Blo 900574 4575365 := bbase (se 4 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 4575365 = 857881) (by norm_num)
theorem B2281709 : Blo 900574 2281709 := bbase (se 3 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 2281709 = 855641) (by norm_num)
theorem B2314709 : Blo 900574 2314709 := bbase (se 7 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 2314709 = 54251) (by norm_num)
theorem B3428837 : Blo 900574 3428837 := bbase (se 4 (by rfl) ⟨321453, by rfl⟩ : syracuseStep 3428837 = 642907) (by norm_num)
theorem B4346389 : Blo 900574 4346389 := bbase (se 6 (by rfl) ⟨101868, by rfl⟩ : syracuseStep 4346389 = 203737) (by norm_num)
theorem B2282053 : Blo 900574 2282053 := bbase (se 4 (by rfl) ⟨213942, by rfl⟩ : syracuseStep 2282053 = 427885) (by norm_num)
theorem B2282165 : Blo 900574 2282165 := bbase (se 5 (by rfl) ⟨106976, by rfl⟩ : syracuseStep 2282165 = 213953) (by norm_num)
theorem B9261749 : Blo 900574 9261749 := bbase (se 5 (by rfl) ⟨434144, by rfl⟩ : syracuseStep 9261749 = 868289) (by norm_num)
theorem B3429125 : Blo 900574 3429125 := bbase (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) (by norm_num)
theorem B4117301 : Blo 900574 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B2282357 : Blo 900574 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B5788853 : Blo 900574 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B2282701 : Blo 900574 2282701 := bbase (se 3 (by rfl) ⟨428006, by rfl⟩ : syracuseStep 2282701 = 856013) (by norm_num)
theorem B1627381 : Blo 900574 1627381 := bbase (se 5 (by rfl) ⟨76283, by rfl⟩ : syracuseStep 1627381 = 152567) (by norm_num)
theorem B2282813 : Blo 900574 2282813 := bbase (se 3 (by rfl) ⟨428027, by rfl⟩ : syracuseStep 2282813 = 856055) (by norm_num)
theorem B4576661 : Blo 900574 4576661 := bbase (se 6 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 4576661 = 214531) (by norm_num)
theorem B2283005 : Blo 900574 2283005 := bbase (se 3 (by rfl) ⟨428063, by rfl⟩ : syracuseStep 2283005 = 856127) (by norm_num)
theorem B2283349 : Blo 900574 2283349 := bbase (se 9 (by rfl) ⟨6689, by rfl⟩ : syracuseStep 2283349 = 13379) (by norm_num)
theorem B3430309 : Blo 900574 3430309 := bbase (se 4 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 3430309 = 643183) (by norm_num)
theorem B2283461 : Blo 900574 2283461 := bbase (se 4 (by rfl) ⟨214074, by rfl⟩ : syracuseStep 2283461 = 428149) (by norm_num)
theorem B17324117 : Blo 900574 17324117 := bbase (se 8 (by rfl) ⟨101508, by rfl⟩ : syracuseStep 17324117 = 203017) (by norm_num)
theorem B3856501 : Blo 900574 3856501 := bbase (se 5 (by rfl) ⟨180773, by rfl⟩ : syracuseStep 3856501 = 361547) (by norm_num)
theorem B2283653 : Blo 900574 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B1267877 : Blo 900574 1267877 := bbase (se 4 (by rfl) ⟨118863, by rfl⟩ : syracuseStep 1267877 = 237727) (by norm_num)
theorem B3430613 : Blo 900574 3430613 := bbase (se 7 (by rfl) ⟨40202, by rfl⟩ : syracuseStep 3430613 = 80405) (by norm_num)
theorem B2316557 : Blo 900574 2316557 := bbase (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) (by norm_num)
theorem B1300789 : Blo 900574 1300789 := bbase (se 5 (by rfl) ⟨60974, by rfl⟩ : syracuseStep 1300789 = 121949) (by norm_num)
theorem B2087333 : Blo 900574 2087333 := bbase (se 4 (by rfl) ⟨195687, by rfl⟩ : syracuseStep 2087333 = 391375) (by norm_num)
theorem B2283997 : Blo 900574 2283997 := bbase (se 3 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 2283997 = 856499) (by norm_num)
theorem B1759781 : Blo 900574 1759781 := bbase (se 4 (by rfl) ⟨164979, by rfl⟩ : syracuseStep 1759781 = 329959) (by norm_num)
theorem B4872757 : Blo 900574 4872757 := bbase (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) (by norm_num)
theorem B2284109 : Blo 900574 2284109 := bbase (se 3 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 2284109 = 856541) (by norm_num)
theorem B1628765 : Blo 900574 1628765 := bbase (se 3 (by rfl) ⟨305393, by rfl⟩ : syracuseStep 1628765 = 610787) (by norm_num)
theorem B1628837 : Blo 900574 1628837 := bbase (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) (by norm_num)
theorem B4577957 : Blo 900574 4577957 := bbase (se 4 (by rfl) ⟨429183, by rfl⟩ : syracuseStep 4577957 = 858367) (by norm_num)
theorem B2284301 : Blo 900574 2284301 := bbase (se 3 (by rfl) ⟨428306, by rfl⟩ : syracuseStep 2284301 = 856613) (by norm_num)
theorem B1628981 : Blo 900574 1628981 := bbase (se 5 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 1628981 = 152717) (by norm_num)
theorem B2284645 : Blo 900574 2284645 := bbase (se 4 (by rfl) ⟨214185, by rfl⟩ : syracuseStep 2284645 = 428371) (by norm_num)
theorem B1924253 : Blo 900574 1924253 := bbase (se 3 (by rfl) ⟨360797, by rfl⟩ : syracuseStep 1924253 = 721595) (by norm_num)
theorem B1236125 : Blo 900574 1236125 := bbase (se 3 (by rfl) ⟨231773, by rfl⟩ : syracuseStep 1236125 = 463547) (by norm_num)
theorem B6839477 : Blo 900574 6839477 := bbase (se 5 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 6839477 = 641201) (by norm_num)
theorem B2317501 : Blo 900574 2317501 := bbase (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) (by norm_num)
theorem B2284757 : Blo 900574 2284757 := bbase (se 7 (by rfl) ⟨26774, by rfl⟩ : syracuseStep 2284757 = 53549) (by norm_num)
theorem B1924373 : Blo 900574 1924373 := bbase (se 6 (by rfl) ⟨45102, by rfl⟩ : syracuseStep 1924373 = 90205) (by norm_num)
theorem B5135669 : Blo 900574 5135669 := bbase (se 5 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 5135669 = 481469) (by norm_num)
theorem B15621461 : Blo 900574 15621461 := bbase (se 11 (by rfl) ⟨11441, by rfl⟩ : syracuseStep 15621461 = 22883) (by norm_num)
theorem B25058645 : Blo 900574 25058645 := bbase (se 11 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 25058645 = 36707) (by norm_num)
theorem B941417 : Blo 900574 941417 := bbase (se 2 (by rfl) ⟨353031, by rfl⟩ : syracuseStep 941417 = 706063) (by norm_num)
theorem B2284949 : Blo 900574 2284949 := bbase (se 6 (by rfl) ⟨53553, by rfl⟩ : syracuseStep 2284949 = 107107) (by norm_num)
theorem B3661301 : Blo 900574 3661301 := bbase (se 5 (by rfl) ⟨171623, by rfl⟩ : syracuseStep 3661301 = 343247) (by norm_num)
theorem B3857989 : Blo 900574 3857989 := bbase (se 4 (by rfl) ⟨361686, by rfl⟩ : syracuseStep 3857989 = 723373) (by norm_num)
theorem B3858005 : Blo 900574 3858005 := bbase (se 8 (by rfl) ⟨22605, by rfl⟩ : syracuseStep 3858005 = 45211) (by norm_num)
theorem B2285293 : Blo 900574 2285293 := bbase (se 3 (by rfl) ⟨428492, by rfl⟩ : syracuseStep 2285293 = 856985) (by norm_num)
theorem B2285405 : Blo 900574 2285405 := bbase (se 3 (by rfl) ⟨428513, by rfl⟩ : syracuseStep 2285405 = 857027) (by norm_num)
theorem B1925005 : Blo 900574 1925005 := bbase (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) (by norm_num)
theorem B4579253 : Blo 900574 4579253 := bbase (se 5 (by rfl) ⟨214652, by rfl⟩ : syracuseStep 4579253 = 429305) (by norm_num)
theorem B2056205 : Blo 900574 2056205 := bbase (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) (by norm_num)
theorem B2285597 : Blo 900574 2285597 := bbase (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) (by norm_num)
theorem B3432725 : Blo 900574 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B3039605 : Blo 900574 3039605 := bbase (se 5 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 3039605 = 284963) (by norm_num)
theorem B2285941 : Blo 900574 2285941 := bbase (se 5 (by rfl) ⟨107153, by rfl⟩ : syracuseStep 2285941 = 214307) (by norm_num)
theorem B2286053 : Blo 900574 2286053 := bbase (se 4 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 2286053 = 428635) (by norm_num)
theorem B3433013 : Blo 900574 3433013 := bbase (se 5 (by rfl) ⟨160922, by rfl⟩ : syracuseStep 3433013 = 321845) (by norm_num)
theorem B2286245 : Blo 900574 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B1925893 : Blo 900574 1925893 := bbase (se 4 (by rfl) ⟨180552, by rfl⟩ : syracuseStep 1925893 = 361105) (by norm_num)
theorem B3040037 : Blo 900574 3040037 := bbase (se 4 (by rfl) ⟨285003, by rfl⟩ : syracuseStep 3040037 = 570007) (by norm_num)
theorem B1926013 : Blo 900574 1926013 := bbase (se 3 (by rfl) ⟨361127, by rfl⟩ : syracuseStep 1926013 = 722255) (by norm_num)
theorem B4875157 : Blo 900574 4875157 := bbase (se 6 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 4875157 = 228523) (by norm_num)
theorem B2286589 : Blo 900574 2286589 := bbase (se 3 (by rfl) ⟨428735, by rfl⟩ : syracuseStep 2286589 = 857471) (by norm_num)
theorem B3466277 : Blo 900574 3466277 := bbase (se 4 (by rfl) ⟨324963, by rfl⟩ : syracuseStep 3466277 = 649927) (by norm_num)
theorem B2286701 : Blo 900574 2286701 := bbase (se 3 (by rfl) ⟨428756, by rfl⟩ : syracuseStep 2286701 = 857513) (by norm_num)
theorem B1827965 : Blo 900574 1827965 := bbase (se 3 (by rfl) ⟨342743, by rfl⟩ : syracuseStep 1827965 = 685487) (by norm_num)
theorem B1926269 : Blo 900574 1926269 := bbase (se 3 (by rfl) ⟨361175, by rfl⟩ : syracuseStep 1926269 = 722351) (by norm_num)
theorem B3040469 : Blo 900574 3040469 := bbase (se 7 (by rfl) ⟨35630, by rfl⟩ : syracuseStep 3040469 = 71261) (by norm_num)
theorem B1139933 : Blo 900574 1139933 := bbase (se 3 (by rfl) ⟨213737, by rfl⟩ : syracuseStep 1139933 = 427475) (by norm_num)
theorem B1139989 : Blo 900574 1139989 := bbase (se 6 (by rfl) ⟨26718, by rfl⟩ : syracuseStep 1139989 = 53437) (by norm_num)
theorem B2286893 : Blo 900574 2286893 := bbase (se 3 (by rfl) ⟨428792, by rfl⟩ : syracuseStep 2286893 = 857585) (by norm_num)
theorem B1140085 : Blo 900574 1140085 := bbase (se 5 (by rfl) ⟨53441, by rfl⟩ : syracuseStep 1140085 = 106883) (by norm_num)
theorem B976321 : Blo 900574 976321 := bbase (se 2 (by rfl) ⟨366120, by rfl⟩ : syracuseStep 976321 = 732241) (by norm_num)
theorem B8676821 : Blo 900574 8676821 := bbase (se 7 (by rfl) ⟨101681, by rfl⟩ : syracuseStep 8676821 = 203363) (by norm_num)
theorem B1140257 : Blo 900574 1140257 := bbase (se 2 (by rfl) ⟨427596, by rfl⟩ : syracuseStep 1140257 = 855193) (by norm_num)
theorem B1140313 : Blo 900574 1140313 := bbase (se 2 (by rfl) ⟨427617, by rfl⟩ : syracuseStep 1140313 = 855235) (by norm_num)
theorem B3040901 : Blo 900574 3040901 := bbase (se 4 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 3040901 = 570169) (by norm_num)
theorem B2287237 : Blo 900574 2287237 := bbase (se 4 (by rfl) ⟨214428, by rfl⟩ : syracuseStep 2287237 = 428857) (by norm_num)
theorem B1140409 : Blo 900574 1140409 := bbase (se 2 (by rfl) ⟨427653, by rfl⟩ : syracuseStep 1140409 = 855307) (by norm_num)
theorem B3434197 : Blo 900574 3434197 := bbase (se 7 (by rfl) ⟨40244, by rfl⟩ : syracuseStep 3434197 = 80489) (by norm_num)
theorem B2287349 : Blo 900574 2287349 := bbase (se 5 (by rfl) ⟨107219, by rfl⟩ : syracuseStep 2287349 = 214439) (by norm_num)
theorem B3860261 : Blo 900574 3860261 := bbase (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) (by norm_num)
theorem B1140581 : Blo 900574 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B1140637 : Blo 900574 1140637 := bbase (se 3 (by rfl) ⟨213869, by rfl⟩ : syracuseStep 1140637 = 427739) (by norm_num)
theorem B2287541 : Blo 900574 2287541 := bbase (se 5 (by rfl) ⟨107228, by rfl⟩ : syracuseStep 2287541 = 214457) (by norm_num)
theorem B1927157 : Blo 900574 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B1140733 : Blo 900574 1140733 := bbase (se 3 (by rfl) ⟨213887, by rfl⟩ : syracuseStep 1140733 = 427775) (by norm_num)
theorem B3434501 : Blo 900574 3434501 := bbase (se 4 (by rfl) ⟨321984, by rfl⟩ : syracuseStep 3434501 = 643969) (by norm_num)
theorem B3041333 : Blo 900574 3041333 := bbase (se 5 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 3041333 = 285125) (by norm_num)
theorem B1140905 : Blo 900574 1140905 := bbase (se 2 (by rfl) ⟨427839, by rfl⟩ : syracuseStep 1140905 = 855679) (by norm_num)
theorem B1140961 : Blo 900574 1140961 := bbase (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) (by norm_num)
theorem B1927397 : Blo 900574 1927397 := bbase (se 4 (by rfl) ⟨180693, by rfl⟩ : syracuseStep 1927397 = 361387) (by norm_num)
theorem B2320613 : Blo 900574 2320613 := bbase (se 4 (by rfl) ⟨217557, by rfl⟩ : syracuseStep 2320613 = 435115) (by norm_num)
theorem B1829117 : Blo 900574 1829117 := bbase (se 3 (by rfl) ⟨342959, by rfl⟩ : syracuseStep 1829117 = 685919) (by norm_num)
theorem B2287885 : Blo 900574 2287885 := bbase (se 3 (by rfl) ⟨428978, by rfl⟩ : syracuseStep 2287885 = 857957) (by norm_num)
theorem B1141057 : Blo 900574 1141057 := bbase (se 2 (by rfl) ⟨427896, by rfl⟩ : syracuseStep 1141057 = 855793) (by norm_num)
theorem B2287997 : Blo 900574 2287997 := bbase (se 3 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 2287997 = 857999) (by norm_num)
theorem B3041765 : Blo 900574 3041765 := bbase (se 4 (by rfl) ⟨285165, by rfl⟩ : syracuseStep 3041765 = 570331) (by norm_num)
theorem B1141229 : Blo 900574 1141229 := bbase (se 3 (by rfl) ⟨213980, by rfl⟩ : syracuseStep 1141229 = 427961) (by norm_num)
theorem B1141285 : Blo 900574 1141285 := bbase (se 4 (by rfl) ⟨106995, by rfl⟩ : syracuseStep 1141285 = 213991) (by norm_num)
theorem B2058797 : Blo 900574 2058797 := bbase (se 3 (by rfl) ⟨386024, by rfl⟩ : syracuseStep 2058797 = 772049) (by norm_num)
theorem B2288189 : Blo 900574 2288189 := bbase (se 3 (by rfl) ⟨429035, by rfl⟩ : syracuseStep 2288189 = 858071) (by norm_num)
theorem B1141381 : Blo 900574 1141381 := bbase (se 4 (by rfl) ⟨107004, by rfl⟩ : syracuseStep 1141381 = 214009) (by norm_num)
theorem B1927901 : Blo 900574 1927901 := bbase (se 3 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 1927901 = 722963) (by norm_num)
theorem B1927909 : Blo 900574 1927909 := bbase (se 4 (by rfl) ⟨180741, by rfl⟩ : syracuseStep 1927909 = 361483) (by norm_num)
theorem B3304165 : Blo 900574 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B1141553 : Blo 900574 1141553 := bbase (se 2 (by rfl) ⟨428082, by rfl⟩ : syracuseStep 1141553 = 856165) (by norm_num)
theorem B1141609 : Blo 900574 1141609 := bbase (se 2 (by rfl) ⟨428103, by rfl⟩ : syracuseStep 1141609 = 856207) (by norm_num)
theorem B2026349 : Blo 900574 2026349 := bbase (se 3 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 2026349 = 759881) (by norm_num)
theorem B3042197 : Blo 900574 3042197 := bbase (se 6 (by rfl) ⟨71301, by rfl⟩ : syracuseStep 3042197 = 142603) (by norm_num)
theorem B2288533 : Blo 900574 2288533 := bbase (se 6 (by rfl) ⟨53637, by rfl⟩ : syracuseStep 2288533 = 107275) (by norm_num)
theorem B2026421 : Blo 900574 2026421 := bbase (se 5 (by rfl) ⟨94988, by rfl⟩ : syracuseStep 2026421 = 189977) (by norm_num)
theorem B1141705 : Blo 900574 1141705 := bbase (se 2 (by rfl) ⟨428139, by rfl⟩ : syracuseStep 1141705 = 856279) (by norm_num)
theorem B2026493 : Blo 900574 2026493 := bbase (se 3 (by rfl) ⟨379967, by rfl⟩ : syracuseStep 2026493 = 759935) (by norm_num)
theorem B2288645 : Blo 900574 2288645 := bbase (se 4 (by rfl) ⟨214560, by rfl⟩ : syracuseStep 2288645 = 429121) (by norm_num)
theorem B2026565 : Blo 900574 2026565 := bbase (se 4 (by rfl) ⟨189990, by rfl⟩ : syracuseStep 2026565 = 379981) (by norm_num)
theorem B1141877 : Blo 900574 1141877 := bbase (se 5 (by rfl) ⟨53525, by rfl⟩ : syracuseStep 1141877 = 107051) (by norm_num)
theorem B2026637 : Blo 900574 2026637 := bbase (se 3 (by rfl) ⟨379994, by rfl⟩ : syracuseStep 2026637 = 759989) (by norm_num)
theorem B1141933 : Blo 900574 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B6515893 : Blo 900574 6515893 := bbase (se 5 (by rfl) ⟨305432, by rfl⟩ : syracuseStep 6515893 = 610865) (by norm_num)
theorem B2288837 : Blo 900574 2288837 := bbase (se 4 (by rfl) ⟨214578, by rfl⟩ : syracuseStep 2288837 = 429157) (by norm_num)
theorem B2026709 : Blo 900574 2026709 := bbase (se 7 (by rfl) ⟨23750, by rfl⟩ : syracuseStep 2026709 = 47501) (by norm_num)
theorem B1142029 : Blo 900574 1142029 := bbase (se 3 (by rfl) ⟨214130, by rfl⟩ : syracuseStep 1142029 = 428261) (by norm_num)
theorem B2026781 : Blo 900574 2026781 := bbase (se 3 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 2026781 = 760043) (by norm_num)
theorem B3042629 : Blo 900574 3042629 := bbase (se 4 (by rfl) ⟨285246, by rfl⟩ : syracuseStep 3042629 = 570493) (by norm_num)
theorem B1371485 : Blo 900574 1371485 := bbase (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) (by norm_num)
theorem B2026853 : Blo 900574 2026853 := bbase (se 4 (by rfl) ⟨190017, by rfl⟩ : syracuseStep 2026853 = 380035) (by norm_num)
theorem B2026925 : Blo 900574 2026925 := bbase (se 3 (by rfl) ⟨380048, by rfl⟩ : syracuseStep 2026925 = 760097) (by norm_num)
theorem B1142201 : Blo 900574 1142201 := bbase (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) (by norm_num)
theorem B1142257 : Blo 900574 1142257 := bbase (se 2 (by rfl) ⟨428346, by rfl⟩ : syracuseStep 1142257 = 856693) (by norm_num)
theorem B2026997 : Blo 900574 2026997 := bbase (se 5 (by rfl) ⟨95015, by rfl⟩ : syracuseStep 2026997 = 190031) (by norm_num)
theorem B8220149 : Blo 900574 8220149 := bbase (se 5 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 8220149 = 770639) (by norm_num)
theorem B2289181 : Blo 900574 2289181 := bbase (se 3 (by rfl) ⟨429221, by rfl⟩ : syracuseStep 2289181 = 858443) (by norm_num)
theorem B2027069 : Blo 900574 2027069 := bbase (se 3 (by rfl) ⟨380075, by rfl⟩ : syracuseStep 2027069 = 760151) (by norm_num)
theorem B2059853 : Blo 900574 2059853 := bbase (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) (by norm_num)
theorem B1142353 : Blo 900574 1142353 := bbase (se 2 (by rfl) ⟨428382, by rfl⟩ : syracuseStep 1142353 = 856765) (by norm_num)
theorem B2027141 : Blo 900574 2027141 := bbase (se 4 (by rfl) ⟨190044, by rfl⟩ : syracuseStep 2027141 = 380089) (by norm_num)
theorem B2289293 : Blo 900574 2289293 := bbase (se 3 (by rfl) ⟨429242, by rfl⟩ : syracuseStep 2289293 = 858485) (by norm_num)
theorem B2027213 : Blo 900574 2027213 := bbase (se 3 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 2027213 = 760205) (by norm_num)
theorem B3043061 : Blo 900574 3043061 := bbase (se 5 (by rfl) ⟨142643, by rfl⟩ : syracuseStep 3043061 = 285287) (by norm_num)
theorem B1142525 : Blo 900574 1142525 := bbase (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) (by norm_num)
theorem B2027285 : Blo 900574 2027285 := bbase (se 6 (by rfl) ⟨47514, by rfl⟩ : syracuseStep 2027285 = 95029) (by norm_num)
theorem B1142581 : Blo 900574 1142581 := bbase (se 5 (by rfl) ⟨53558, by rfl⟩ : syracuseStep 1142581 = 107117) (by norm_num)
theorem B1929037 : Blo 900574 1929037 := bbase (se 3 (by rfl) ⟨361694, by rfl⟩ : syracuseStep 1929037 = 723389) (by norm_num)
theorem B2289485 : Blo 900574 2289485 := bbase (se 3 (by rfl) ⟨429278, by rfl⟩ : syracuseStep 2289485 = 858557) (by norm_num)
theorem B2027357 : Blo 900574 2027357 := bbase (se 3 (by rfl) ⟨380129, by rfl⟩ : syracuseStep 2027357 = 760259) (by norm_num)
theorem B913285 : Blo 900574 913285 := bbase (se 4 (by rfl) ⟨85620, by rfl⟩ : syracuseStep 913285 = 171241) (by norm_num)
theorem B1142677 : Blo 900574 1142677 := bbase (se 6 (by rfl) ⟨26781, by rfl⟩ : syracuseStep 1142677 = 53563) (by norm_num)
theorem B2027429 : Blo 900574 2027429 := bbase (se 4 (by rfl) ⟨190071, by rfl⟩ : syracuseStep 2027429 = 380143) (by norm_num)
theorem B2027501 : Blo 900574 2027501 := bbase (se 3 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 2027501 = 760313) (by norm_num)
theorem B2027573 : Blo 900574 2027573 := bbase (se 5 (by rfl) ⟨95042, by rfl⟩ : syracuseStep 2027573 = 190085) (by norm_num)
theorem B1142849 : Blo 900574 1142849 := bbase (se 2 (by rfl) ⟨428568, by rfl⟩ : syracuseStep 1142849 = 857137) (by norm_num)
theorem B1142905 : Blo 900574 1142905 := bbase (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) (by norm_num)
theorem B2027645 : Blo 900574 2027645 := bbase (se 3 (by rfl) ⟨380183, by rfl⟩ : syracuseStep 2027645 = 760367) (by norm_num)
theorem B3043493 : Blo 900574 3043493 := bbase (se 4 (by rfl) ⟨285327, by rfl⟩ : syracuseStep 3043493 = 570655) (by norm_num)
theorem B2027717 : Blo 900574 2027717 := bbase (se 4 (by rfl) ⟨190098, by rfl⟩ : syracuseStep 2027717 = 380197) (by norm_num)
theorem B1929413 : Blo 900574 1929413 := bbase (se 4 (by rfl) ⟨180882, by rfl⟩ : syracuseStep 1929413 = 361765) (by norm_num)
theorem B2748613 : Blo 900574 2748613 := bbase (se 4 (by rfl) ⟨257682, by rfl⟩ : syracuseStep 2748613 = 515365) (by norm_num)
theorem B1143001 : Blo 900574 1143001 := bbase (se 2 (by rfl) ⟨428625, by rfl⟩ : syracuseStep 1143001 = 857251) (by norm_num)
theorem B2027789 : Blo 900574 2027789 := bbase (se 3 (by rfl) ⟨380210, by rfl⟩ : syracuseStep 2027789 = 760421) (by norm_num)
theorem B1175845 : Blo 900574 1175845 := bbase (se 4 (by rfl) ⟨110235, by rfl⟩ : syracuseStep 1175845 = 220471) (by norm_num)
theorem B2027861 : Blo 900574 2027861 := bbase (se 10 (by rfl) ⟨2970, by rfl⟩ : syracuseStep 2027861 = 5941) (by norm_num)
theorem B1143173 : Blo 900574 1143173 := bbase (se 4 (by rfl) ⟨107172, by rfl⟩ : syracuseStep 1143173 = 214345) (by norm_num)
theorem B2027933 : Blo 900574 2027933 := bbase (se 3 (by rfl) ⟨380237, by rfl⟩ : syracuseStep 2027933 = 760475) (by norm_num)
theorem B1143229 : Blo 900574 1143229 := bbase (se 3 (by rfl) ⟨214355, by rfl⟩ : syracuseStep 1143229 = 428711) (by norm_num)
theorem B2224613 : Blo 900574 2224613 := bbase (se 4 (by rfl) ⟨208557, by rfl⟩ : syracuseStep 2224613 = 417115) (by norm_num)
theorem B2028005 : Blo 900574 2028005 := bbase (se 4 (by rfl) ⟨190125, by rfl⟩ : syracuseStep 2028005 = 380251) (by norm_num)
theorem B1143325 : Blo 900574 1143325 := bbase (se 3 (by rfl) ⟨214373, by rfl⟩ : syracuseStep 1143325 = 428747) (by norm_num)
theorem B2028077 : Blo 900574 2028077 := bbase (se 3 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 2028077 = 760529) (by norm_num)
theorem B3043925 : Blo 900574 3043925 := bbase (se 8 (by rfl) ⟨17835, by rfl⟩ : syracuseStep 3043925 = 35671) (by norm_num)
theorem B2028149 : Blo 900574 2028149 := bbase (se 5 (by rfl) ⟨95069, by rfl⟩ : syracuseStep 2028149 = 190139) (by norm_num)
theorem B2028221 : Blo 900574 2028221 := bbase (se 3 (by rfl) ⟨380291, by rfl⟩ : syracuseStep 2028221 = 760583) (by norm_num)
theorem B1143497 : Blo 900574 1143497 := bbase (se 2 (by rfl) ⟨428811, by rfl⟩ : syracuseStep 1143497 = 857623) (by norm_num)
theorem B914177 : Blo 900574 914177 := bbase (se 2 (by rfl) ⟨342816, by rfl⟩ : syracuseStep 914177 = 685633) (by norm_num)
theorem B1143553 : Blo 900574 1143553 := bbase (se 2 (by rfl) ⟨428832, by rfl⟩ : syracuseStep 1143553 = 857665) (by norm_num)
theorem B2028293 : Blo 900574 2028293 := bbase (se 4 (by rfl) ⟨190152, by rfl⟩ : syracuseStep 2028293 = 380305) (by norm_num)
theorem B2028365 : Blo 900574 2028365 := bbase (se 3 (by rfl) ⟨380318, by rfl⟩ : syracuseStep 2028365 = 760637) (by norm_num)
theorem B1373005 : Blo 900574 1373005 := bbase (se 3 (by rfl) ⟨257438, by rfl⟩ : syracuseStep 1373005 = 514877) (by norm_num)
theorem B1143649 : Blo 900574 1143649 := bbase (se 2 (by rfl) ⟨428868, by rfl⟩ : syracuseStep 1143649 = 857737) (by norm_num)
theorem B2028437 : Blo 900574 2028437 := bbase (se 6 (by rfl) ⟨47541, by rfl⟩ : syracuseStep 2028437 = 95083) (by norm_num)
theorem B2028509 : Blo 900574 2028509 := bbase (se 3 (by rfl) ⟨380345, by rfl⟩ : syracuseStep 2028509 = 760691) (by norm_num)
theorem B3044357 : Blo 900574 3044357 := bbase (se 4 (by rfl) ⟨285408, by rfl⟩ : syracuseStep 3044357 = 570817) (by norm_num)
theorem B914437 : Blo 900574 914437 := bbase (se 4 (by rfl) ⟨85728, by rfl⟩ : syracuseStep 914437 = 171457) (by norm_num)
theorem B1143821 : Blo 900574 1143821 := bbase (se 3 (by rfl) ⟨214466, by rfl⟩ : syracuseStep 1143821 = 428933) (by norm_num)
theorem B2028581 : Blo 900574 2028581 := bbase (se 4 (by rfl) ⟨190179, by rfl⟩ : syracuseStep 2028581 = 380359) (by norm_num)
theorem B1143877 : Blo 900574 1143877 := bbase (se 4 (by rfl) ⟨107238, by rfl⟩ : syracuseStep 1143877 = 214477) (by norm_num)
theorem B2028653 : Blo 900574 2028653 := bbase (se 3 (by rfl) ⟨380372, by rfl⟩ : syracuseStep 2028653 = 760745) (by norm_num)
theorem B1143973 : Blo 900574 1143973 := bbase (se 4 (by rfl) ⟨107247, by rfl⟩ : syracuseStep 1143973 = 214495) (by norm_num)
theorem B2028725 : Blo 900574 2028725 := bbase (se 5 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 2028725 = 190193) (by norm_num)
theorem B2028797 : Blo 900574 2028797 := bbase (se 3 (by rfl) ⟨380399, by rfl⟩ : syracuseStep 2028797 = 760799) (by norm_num)
theorem B2028869 : Blo 900574 2028869 := bbase (se 4 (by rfl) ⟨190206, by rfl⟩ : syracuseStep 2028869 = 380413) (by norm_num)
theorem B1144145 : Blo 900574 1144145 := bbase (se 2 (by rfl) ⟨429054, by rfl⟩ : syracuseStep 1144145 = 858109) (by norm_num)
theorem B1144201 : Blo 900574 1144201 := bbase (se 2 (by rfl) ⟨429075, by rfl⟩ : syracuseStep 1144201 = 858151) (by norm_num)
theorem B2028941 : Blo 900574 2028941 := bbase (se 3 (by rfl) ⟨380426, by rfl⟩ : syracuseStep 2028941 = 760853) (by norm_num)
theorem B3667349 : Blo 900574 3667349 := bbase (se 6 (by rfl) ⟨85953, by rfl⟩ : syracuseStep 3667349 = 171907) (by norm_num)
theorem B1013161 : Blo 900574 1013161 := bbase (se 2 (by rfl) ⟨379935, by rfl⟩ : syracuseStep 1013161 = 759871) (by norm_num)
theorem B3044789 : Blo 900574 3044789 := bbase (se 5 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 3044789 = 285449) (by norm_num)
theorem B1013197 : Blo 900574 1013197 := bbase (se 3 (by rfl) ⟨189974, by rfl⟩ : syracuseStep 1013197 = 379949) (by norm_num)
theorem B2029013 : Blo 900574 2029013 := bbase (se 7 (by rfl) ⟨23777, by rfl⟩ : syracuseStep 2029013 = 47555) (by norm_num)
theorem B1144297 : Blo 900574 1144297 := bbase (se 2 (by rfl) ⟨429111, by rfl⟩ : syracuseStep 1144297 = 858223) (by norm_num)
theorem B1013233 : Blo 900574 1013233 := bbase (se 2 (by rfl) ⟨379962, by rfl⟩ : syracuseStep 1013233 = 759925) (by norm_num)
theorem B1013269 : Blo 900574 1013269 := bbase (se 6 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 1013269 = 47497) (by norm_num)
theorem B2029085 : Blo 900574 2029085 := bbase (se 3 (by rfl) ⟨380453, by rfl⟩ : syracuseStep 2029085 = 760907) (by norm_num)
theorem B1013305 : Blo 900574 1013305 := bbase (se 2 (by rfl) ⟨379989, by rfl⟩ : syracuseStep 1013305 = 759979) (by norm_num)
theorem B1013341 : Blo 900574 1013341 := bbase (se 3 (by rfl) ⟨190001, by rfl⟩ : syracuseStep 1013341 = 380003) (by norm_num)
theorem B2029157 : Blo 900574 2029157 := bbase (se 4 (by rfl) ⟨190233, by rfl⟩ : syracuseStep 2029157 = 380467) (by norm_num)
theorem B1013377 : Blo 900574 1013377 := bbase (se 2 (by rfl) ⟨380016, by rfl⟩ : syracuseStep 1013377 = 760033) (by norm_num)
theorem B1144469 : Blo 900574 1144469 := bbase (se 6 (by rfl) ⟨26823, by rfl⟩ : syracuseStep 1144469 = 53647) (by norm_num)
theorem B915101 : Blo 900574 915101 := bbase (se 3 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 915101 = 343163) (by norm_num)
theorem B1013413 : Blo 900574 1013413 := bbase (se 4 (by rfl) ⟨95007, by rfl⟩ : syracuseStep 1013413 = 190015) (by norm_num)
theorem B2029229 : Blo 900574 2029229 := bbase (se 3 (by rfl) ⟨380480, by rfl⟩ : syracuseStep 2029229 = 760961) (by norm_num)
theorem B1373869 : Blo 900574 1373869 := bbase (se 3 (by rfl) ⟨257600, by rfl⟩ : syracuseStep 1373869 = 515201) (by norm_num)
theorem B1013449 : Blo 900574 1013449 := bbase (se 2 (by rfl) ⟨380043, by rfl⟩ : syracuseStep 1013449 = 760087) (by norm_num)
theorem B1144525 : Blo 900574 1144525 := bbase (se 3 (by rfl) ⟨214598, by rfl⟩ : syracuseStep 1144525 = 429197) (by norm_num)
theorem B1373917 : Blo 900574 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B3471077 : Blo 900574 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B1013485 : Blo 900574 1013485 := bbase (se 3 (by rfl) ⟨190028, by rfl⟩ : syracuseStep 1013485 = 380057) (by norm_num)
theorem B2029301 : Blo 900574 2029301 := bbase (se 5 (by rfl) ⟨95123, by rfl⟩ : syracuseStep 2029301 = 190247) (by norm_num)
theorem B1013521 : Blo 900574 1013521 := bbase (se 2 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 1013521 = 760141) (by norm_num)
theorem B1931053 : Blo 900574 1931053 := bbase (se 3 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 1931053 = 724145) (by norm_num)
theorem B1144621 : Blo 900574 1144621 := bbase (se 3 (by rfl) ⟨214616, by rfl⟩ : syracuseStep 1144621 = 429233) (by norm_num)
theorem B1013557 : Blo 900574 1013557 := bbase (se 5 (by rfl) ⟨47510, by rfl⟩ : syracuseStep 1013557 = 95021) (by norm_num)
theorem B2029373 : Blo 900574 2029373 := bbase (se 3 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 2029373 = 761015) (by norm_num)
theorem B1013593 : Blo 900574 1013593 := bbase (se 2 (by rfl) ⟨380097, by rfl⟩ : syracuseStep 1013593 = 760195) (by norm_num)
theorem B3045221 : Blo 900574 3045221 := bbase (se 4 (by rfl) ⟨285489, by rfl⟩ : syracuseStep 3045221 = 570979) (by norm_num)
theorem B915305 : Blo 900574 915305 := bbase (se 2 (by rfl) ⟨343239, by rfl⟩ : syracuseStep 915305 = 686479) (by norm_num)
theorem B2062189 : Blo 900574 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B1013629 : Blo 900574 1013629 := bbase (se 3 (by rfl) ⟨190055, by rfl⟩ : syracuseStep 1013629 = 380111) (by norm_num)
theorem B2029445 : Blo 900574 2029445 := bbase (se 4 (by rfl) ⟨190260, by rfl⟩ : syracuseStep 2029445 = 380521) (by norm_num)
theorem B1013665 : Blo 900574 1013665 := bbase (se 2 (by rfl) ⟨380124, by rfl⟩ : syracuseStep 1013665 = 760249) (by norm_num)
theorem B1013701 : Blo 900574 1013701 := bbase (se 4 (by rfl) ⟨95034, by rfl⟩ : syracuseStep 1013701 = 190069) (by norm_num)
theorem B2029517 : Blo 900574 2029517 := bbase (se 3 (by rfl) ⟨380534, by rfl⟩ : syracuseStep 2029517 = 761069) (by norm_num)
theorem B1144793 : Blo 900574 1144793 := bbase (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) (by norm_num)
theorem B1013737 : Blo 900574 1013737 := bbase (se 2 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 1013737 = 760303) (by norm_num)
theorem B1013773 : Blo 900574 1013773 := bbase (se 3 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 1013773 = 380165) (by norm_num)
theorem B1144849 : Blo 900574 1144849 := bbase (se 2 (by rfl) ⟨429318, by rfl⟩ : syracuseStep 1144849 = 858637) (by norm_num)
theorem B2029589 : Blo 900574 2029589 := bbase (se 6 (by rfl) ⟨47568, by rfl⟩ : syracuseStep 2029589 = 95137) (by norm_num)
theorem B1013809 : Blo 900574 1013809 := bbase (se 2 (by rfl) ⟨380178, by rfl⟩ : syracuseStep 1013809 = 760357) (by norm_num)
theorem B1013845 : Blo 900574 1013845 := bbase (se 8 (by rfl) ⟨5940, by rfl⟩ : syracuseStep 1013845 = 11881) (by norm_num)
theorem B2029661 : Blo 900574 2029661 := bbase (se 3 (by rfl) ⟨380561, by rfl⟩ : syracuseStep 2029661 = 761123) (by norm_num)
theorem B1013881 : Blo 900574 1013881 := bbase (se 2 (by rfl) ⟨380205, by rfl⟩ : syracuseStep 1013881 = 760411) (by norm_num)
theorem B1013917 : Blo 900574 1013917 := bbase (se 3 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 1013917 = 380219) (by norm_num)
theorem B2029733 : Blo 900574 2029733 := bbase (se 4 (by rfl) ⟨190287, by rfl⟩ : syracuseStep 2029733 = 380575) (by norm_num)
theorem B1013953 : Blo 900574 1013953 := bbase (se 2 (by rfl) ⟨380232, by rfl⟩ : syracuseStep 1013953 = 760465) (by norm_num)
theorem B1013989 : Blo 900574 1013989 := bbase (se 4 (by rfl) ⟨95061, by rfl⟩ : syracuseStep 1013989 = 190123) (by norm_num)
theorem B2029805 : Blo 900574 2029805 := bbase (se 3 (by rfl) ⟨380588, by rfl⟩ : syracuseStep 2029805 = 761177) (by norm_num)
theorem B1014025 : Blo 900574 1014025 := bbase (se 2 (by rfl) ⟨380259, by rfl⟩ : syracuseStep 1014025 = 760519) (by norm_num)
theorem B3045653 : Blo 900574 3045653 := bbase (se 6 (by rfl) ⟨71382, by rfl⟩ : syracuseStep 3045653 = 142765) (by norm_num)
theorem B1014061 : Blo 900574 1014061 := bbase (se 3 (by rfl) ⟨190136, by rfl⟩ : syracuseStep 1014061 = 380273) (by norm_num)
theorem B2029877 : Blo 900574 2029877 := bbase (se 5 (by rfl) ⟨95150, by rfl⟩ : syracuseStep 2029877 = 190301) (by norm_num)
theorem B1014097 : Blo 900574 1014097 := bbase (se 2 (by rfl) ⟨380286, by rfl⟩ : syracuseStep 1014097 = 760573) (by norm_num)
theorem B1014133 : Blo 900574 1014133 := bbase (se 5 (by rfl) ⟨47537, by rfl⟩ : syracuseStep 1014133 = 95075) (by norm_num)
theorem B2029949 : Blo 900574 2029949 := bbase (se 3 (by rfl) ⟨380615, by rfl⟩ : syracuseStep 2029949 = 761231) (by norm_num)
theorem B1014169 : Blo 900574 1014169 := bbase (se 2 (by rfl) ⟨380313, by rfl⟩ : syracuseStep 1014169 = 760627) (by norm_num)
theorem B1014205 : Blo 900574 1014205 := bbase (se 3 (by rfl) ⟨190163, by rfl⟩ : syracuseStep 1014205 = 380327) (by norm_num)
theorem B2030021 : Blo 900574 2030021 := bbase (se 4 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 2030021 = 380629) (by norm_num)
theorem B1374661 : Blo 900574 1374661 := bbase (se 4 (by rfl) ⟨128874, by rfl⟩ : syracuseStep 1374661 = 257749) (by norm_num)
theorem B1014241 : Blo 900574 1014241 := bbase (se 2 (by rfl) ⟨380340, by rfl⟩ : syracuseStep 1014241 = 760681) (by norm_num)
theorem B2193893 : Blo 900574 2193893 := bbase (se 4 (by rfl) ⟨205677, by rfl⟩ : syracuseStep 2193893 = 411355) (by norm_num)
theorem B1014277 : Blo 900574 1014277 := bbase (se 4 (by rfl) ⟨95088, by rfl⟩ : syracuseStep 1014277 = 190177) (by norm_num)
theorem B2030093 : Blo 900574 2030093 := bbase (se 3 (by rfl) ⟨380642, by rfl⟩ : syracuseStep 2030093 = 761285) (by norm_num)
theorem B1014313 : Blo 900574 1014313 := bbase (se 2 (by rfl) ⟨380367, by rfl⟩ : syracuseStep 1014313 = 760735) (by norm_num)
theorem B1014349 : Blo 900574 1014349 := bbase (se 3 (by rfl) ⟨190190, by rfl⟩ : syracuseStep 1014349 = 380381) (by norm_num)
theorem B2030165 : Blo 900574 2030165 := bbase (se 8 (by rfl) ⟨11895, by rfl⟩ : syracuseStep 2030165 = 23791) (by norm_num)
theorem B1014385 : Blo 900574 1014385 := bbase (se 2 (by rfl) ⟨380394, by rfl⟩ : syracuseStep 1014385 = 760789) (by norm_num)
theorem B1014421 : Blo 900574 1014421 := bbase (se 6 (by rfl) ⟨23775, by rfl⟩ : syracuseStep 1014421 = 47551) (by norm_num)
theorem B2030237 : Blo 900574 2030237 := bbase (se 3 (by rfl) ⟨380669, by rfl⟩ : syracuseStep 2030237 = 761339) (by norm_num)
theorem B1014457 : Blo 900574 1014457 := bbase (se 2 (by rfl) ⟨380421, by rfl⟩ : syracuseStep 1014457 = 760843) (by norm_num)
theorem B3046085 : Blo 900574 3046085 := bbase (se 4 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 3046085 = 571141) (by norm_num)
theorem B1014493 : Blo 900574 1014493 := bbase (se 3 (by rfl) ⟨190217, by rfl⟩ : syracuseStep 1014493 = 380435) (by norm_num)
theorem B2030309 : Blo 900574 2030309 := bbase (se 4 (by rfl) ⟨190341, by rfl⟩ : syracuseStep 2030309 = 380683) (by norm_num)
theorem B1014529 : Blo 900574 1014529 := bbase (se 2 (by rfl) ⟨380448, by rfl⟩ : syracuseStep 1014529 = 760897) (by norm_num)
theorem B6847253 : Blo 900574 6847253 := bbase (se 6 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 6847253 = 320965) (by norm_num)
theorem B1014565 : Blo 900574 1014565 := bbase (se 4 (by rfl) ⟨95115, by rfl⟩ : syracuseStep 1014565 = 190231) (by norm_num)
theorem B2030381 : Blo 900574 2030381 := bbase (se 3 (by rfl) ⟨380696, by rfl⟩ : syracuseStep 2030381 = 761393) (by norm_num)
theorem B1014601 : Blo 900574 1014601 := bbase (se 2 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 1014601 = 760951) (by norm_num)
theorem B1014637 : Blo 900574 1014637 := bbase (se 3 (by rfl) ⟨190244, by rfl⟩ : syracuseStep 1014637 = 380489) (by norm_num)
theorem B2030453 : Blo 900574 2030453 := bbase (se 5 (by rfl) ⟨95177, by rfl⟩ : syracuseStep 2030453 = 190355) (by norm_num)
theorem B1014673 : Blo 900574 1014673 := bbase (se 2 (by rfl) ⟨380502, by rfl⟩ : syracuseStep 1014673 = 761005) (by norm_num)
theorem B1014709 : Blo 900574 1014709 := bbase (se 5 (by rfl) ⟨47564, by rfl⟩ : syracuseStep 1014709 = 95129) (by norm_num)
theorem B2030525 : Blo 900574 2030525 := bbase (se 3 (by rfl) ⟨380723, by rfl⟩ : syracuseStep 2030525 = 761447) (by norm_num)
theorem B1014745 : Blo 900574 1014745 := bbase (se 2 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 1014745 = 761059) (by norm_num)
theorem B1014781 : Blo 900574 1014781 := bbase (se 3 (by rfl) ⟨190271, by rfl⟩ : syracuseStep 1014781 = 380543) (by norm_num)
theorem B2030597 : Blo 900574 2030597 := bbase (se 4 (by rfl) ⟨190368, by rfl⟩ : syracuseStep 2030597 = 380737) (by norm_num)
theorem B1014817 : Blo 900574 1014817 := bbase (se 2 (by rfl) ⟨380556, by rfl⟩ : syracuseStep 1014817 = 761113) (by norm_num)
theorem B1014853 : Blo 900574 1014853 := bbase (se 4 (by rfl) ⟨95142, by rfl⟩ : syracuseStep 1014853 = 190285) (by norm_num)
theorem B2030669 : Blo 900574 2030669 := bbase (se 3 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 2030669 = 761501) (by norm_num)
theorem B916561 : Blo 900574 916561 := bbase (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) (by norm_num)
theorem B1014889 : Blo 900574 1014889 := bbase (se 2 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 1014889 = 761167) (by norm_num)
theorem B3046517 : Blo 900574 3046517 := bbase (se 5 (by rfl) ⟨142805, by rfl⟩ : syracuseStep 3046517 = 285611) (by norm_num)
theorem B1014925 : Blo 900574 1014925 := bbase (se 3 (by rfl) ⟨190298, by rfl⟩ : syracuseStep 1014925 = 380597) (by norm_num)
theorem B2030741 : Blo 900574 2030741 := bbase (se 6 (by rfl) ⟨47595, by rfl⟩ : syracuseStep 2030741 = 95191) (by norm_num)
theorem B1014961 : Blo 900574 1014961 := bbase (se 2 (by rfl) ⟨380610, by rfl⟩ : syracuseStep 1014961 = 761221) (by norm_num)
theorem B5143733 : Blo 900574 5143733 := bbase (se 5 (by rfl) ⟨241112, by rfl⟩ : syracuseStep 5143733 = 482225) (by norm_num)
theorem B1014997 : Blo 900574 1014997 := bbase (se 7 (by rfl) ⟨11894, by rfl⟩ : syracuseStep 1014997 = 23789) (by norm_num)
theorem B2030813 : Blo 900574 2030813 := bbase (se 3 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 2030813 = 761555) (by norm_num)
theorem B1015033 : Blo 900574 1015033 := bbase (se 2 (by rfl) ⟨380637, by rfl⟩ : syracuseStep 1015033 = 761275) (by norm_num)
theorem B1015069 : Blo 900574 1015069 := bbase (se 3 (by rfl) ⟨190325, by rfl⟩ : syracuseStep 1015069 = 380651) (by norm_num)
theorem B2030885 : Blo 900574 2030885 := bbase (se 4 (by rfl) ⟨190395, by rfl⟩ : syracuseStep 2030885 = 380791) (by norm_num)
theorem B1015105 : Blo 900574 1015105 := bbase (se 2 (by rfl) ⟨380664, by rfl⟩ : syracuseStep 1015105 = 761329) (by norm_num)
theorem B1015141 : Blo 900574 1015141 := bbase (se 4 (by rfl) ⟨95169, by rfl⟩ : syracuseStep 1015141 = 190339) (by norm_num)
theorem B2030957 : Blo 900574 2030957 := bbase (se 3 (by rfl) ⟨380804, by rfl⟩ : syracuseStep 2030957 = 761609) (by norm_num)
theorem B916853 : Blo 900574 916853 := bbase (se 5 (by rfl) ⟨42977, by rfl⟩ : syracuseStep 916853 = 85955) (by norm_num)
theorem B1015177 : Blo 900574 1015177 := bbase (se 2 (by rfl) ⟨380691, by rfl⟩ : syracuseStep 1015177 = 761383) (by norm_num)
theorem B1015213 : Blo 900574 1015213 := bbase (se 3 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 1015213 = 380705) (by norm_num)
theorem B2031029 : Blo 900574 2031029 := bbase (se 5 (by rfl) ⟨95204, by rfl⟩ : syracuseStep 2031029 = 190409) (by norm_num)
theorem B1015249 : Blo 900574 1015249 := bbase (se 2 (by rfl) ⟨380718, by rfl⟩ : syracuseStep 1015249 = 761437) (by norm_num)
theorem B1015285 : Blo 900574 1015285 := bbase (se 5 (by rfl) ⟨47591, by rfl⟩ : syracuseStep 1015285 = 95183) (by norm_num)
theorem B2031101 : Blo 900574 2031101 := bbase (se 3 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 2031101 = 761663) (by norm_num)
theorem B2260493 : Blo 900574 2260493 := bbase (se 3 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 2260493 = 847685) (by norm_num)
theorem B1015321 : Blo 900574 1015321 := bbase (se 2 (by rfl) ⟨380745, by rfl⟩ : syracuseStep 1015321 = 761491) (by norm_num)
theorem B3046949 : Blo 900574 3046949 := bbase (se 4 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 3046949 = 571303) (by norm_num)
theorem B1015357 : Blo 900574 1015357 := bbase (se 3 (by rfl) ⟨190379, by rfl⟩ : syracuseStep 1015357 = 380759) (by norm_num)
theorem B2031173 : Blo 900574 2031173 := bbase (se 4 (by rfl) ⟨190422, by rfl⟩ : syracuseStep 2031173 = 380845) (by norm_num)
theorem B1015393 : Blo 900574 1015393 := bbase (se 2 (by rfl) ⟨380772, by rfl⟩ : syracuseStep 1015393 = 761545) (by norm_num)
theorem B1015429 : Blo 900574 1015429 := bbase (se 4 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 1015429 = 190393) (by norm_num)
theorem B2031245 : Blo 900574 2031245 := bbase (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) (by norm_num)
theorem B1015465 : Blo 900574 1015465 := bbase (se 2 (by rfl) ⟨380799, by rfl⟩ : syracuseStep 1015465 = 761599) (by norm_num)
theorem B1015501 : Blo 900574 1015501 := bbase (se 3 (by rfl) ⟨190406, by rfl⟩ : syracuseStep 1015501 = 380813) (by norm_num)
theorem B2031317 : Blo 900574 2031317 := bbase (se 7 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 2031317 = 47609) (by norm_num)
theorem B1015537 : Blo 900574 1015537 := bbase (se 2 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 1015537 = 761653) (by norm_num)
theorem B1015573 : Blo 900574 1015573 := bbase (se 6 (by rfl) ⟨23802, by rfl⟩ : syracuseStep 1015573 = 47605) (by norm_num)
theorem B2031389 : Blo 900574 2031389 := bbase (se 3 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 2031389 = 761771) (by norm_num)
theorem B1015609 : Blo 900574 1015609 := bbase (se 2 (by rfl) ⟨380853, by rfl⟩ : syracuseStep 1015609 = 761707) (by norm_num)
theorem B1015645 : Blo 900574 1015645 := bbase (se 3 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 1015645 = 380867) (by norm_num)
theorem B2031461 : Blo 900574 2031461 := bbase (se 4 (by rfl) ⟨190449, by rfl⟩ : syracuseStep 2031461 = 380899) (by norm_num)
theorem B1015681 : Blo 900574 1015681 := bbase (se 2 (by rfl) ⟨380880, by rfl⟩ : syracuseStep 1015681 = 761761) (by norm_num)
theorem B15400853 : Blo 900574 15400853 := bbase (se 6 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 15400853 = 721915) (by norm_num)
theorem B1015717 : Blo 900574 1015717 := bbase (se 4 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 1015717 = 190447) (by norm_num)
theorem B2031533 : Blo 900574 2031533 := bbase (se 3 (by rfl) ⟨380912, by rfl⟩ : syracuseStep 2031533 = 761825) (by norm_num)
theorem B3702725 : Blo 900574 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B1015753 : Blo 900574 1015753 := bbase (se 2 (by rfl) ⟨380907, by rfl⟩ : syracuseStep 1015753 = 761815) (by norm_num)
theorem B3047381 : Blo 900574 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B1015789 : Blo 900574 1015789 := bbase (se 3 (by rfl) ⟨190460, by rfl⟩ : syracuseStep 1015789 = 380921) (by norm_num)
theorem B2031605 : Blo 900574 2031605 := bbase (se 5 (by rfl) ⟨95231, by rfl⟩ : syracuseStep 2031605 = 190463) (by norm_num)
theorem B1015843 : Blo 900574 1015843 := bstep (se 1 (by rfl) ⟨761882, by rfl⟩ : syracuseStep 1015843 = 1523765) B1523765
theorem B3047597 : Blo 900574 3047597 := bstep (se 3 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 3047597 = 1142849) B1142849
theorem B1015987 : Blo 900574 1015987 := bstep (se 1 (by rfl) ⟨761990, by rfl⟩ : syracuseStep 1015987 = 1523981) B1523981
theorem B3047651 : Blo 900574 3047651 := bstep (se 1 (by rfl) ⟨2285738, by rfl⟩ : syracuseStep 3047651 = 4571477) B4571477
theorem B2031857 : Blo 900574 2031857 := bstep (se 2 (by rfl) ⟨761946, by rfl⟩ : syracuseStep 2031857 = 1523893) B1523893
theorem B2031875 : Blo 900574 2031875 := bstep (se 1 (by rfl) ⟨1523906, by rfl⟩ : syracuseStep 2031875 = 3047813) B3047813
theorem B1016131 : Blo 900574 1016131 := bstep (se 1 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 1016131 = 1524197) B1524197
theorem B1540561 : Blo 900574 1540561 := bstep (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) B1155421
theorem B1016275 : Blo 900574 1016275 := bstep (se 1 (by rfl) ⟨762206, by rfl⟩ : syracuseStep 1016275 = 1524413) B1524413
theorem B3047921 : Blo 900574 3047921 := bstep (se 2 (by rfl) ⟨1142970, by rfl⟩ : syracuseStep 3047921 = 2285941) B2285941
theorem B2032145 : Blo 900574 2032145 := bstep (se 2 (by rfl) ⟨762054, by rfl⟩ : syracuseStep 2032145 = 1524109) B1524109
theorem B2032163 : Blo 900574 2032163 := bstep (se 1 (by rfl) ⟨1524122, by rfl⟩ : syracuseStep 2032163 = 3048245) B3048245
theorem B1540691 : Blo 900574 1540691 := bstep (se 1 (by rfl) ⟨1155518, by rfl⟩ : syracuseStep 1540691 = 2311037) B2311037
theorem B1016419 : Blo 900574 1016419 := bstep (se 1 (by rfl) ⟨762314, by rfl⟩ : syracuseStep 1016419 = 1524629) B1524629
theorem B14615153 : Blo 900574 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1016563 : Blo 900574 1016563 := bstep (se 1 (by rfl) ⟨762422, by rfl⟩ : syracuseStep 1016563 = 1524845) B1524845
theorem B2032433 : Blo 900574 2032433 := bstep (se 2 (by rfl) ⟨762162, by rfl⟩ : syracuseStep 2032433 = 1524325) B1524325
theorem B2032451 : Blo 900574 2032451 := bstep (se 1 (by rfl) ⟨1524338, by rfl⟩ : syracuseStep 2032451 = 3048677) B3048677
theorem B7701317 : Blo 900574 7701317 := bstep (se 4 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 7701317 = 1443997) B1443997
theorem B5145443 : Blo 900574 5145443 := bstep (se 1 (by rfl) ⟨3859082, by rfl⟩ : syracuseStep 5145443 = 7718165) B7718165
theorem B1016707 : Blo 900574 1016707 := bstep (se 1 (by rfl) ⟨762530, by rfl⟩ : syracuseStep 1016707 = 1525061) B1525061
theorem B3048461 : Blo 900574 3048461 := bstep (se 3 (by rfl) ⟨571586, by rfl⟩ : syracuseStep 3048461 = 1143173) B1143173
theorem B1016851 : Blo 900574 1016851 := bstep (se 1 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 1016851 = 1525277) B1525277
theorem B3048515 : Blo 900574 3048515 := bstep (se 1 (by rfl) ⟨2286386, by rfl⟩ : syracuseStep 3048515 = 4572773) B4572773
theorem B2032721 : Blo 900574 2032721 := bstep (se 2 (by rfl) ⟨762270, by rfl⟩ : syracuseStep 2032721 = 1524541) B1524541
theorem B2032739 : Blo 900574 2032739 := bstep (se 1 (by rfl) ⟨1524554, by rfl⟩ : syracuseStep 2032739 = 3049109) B3049109
theorem B1016995 : Blo 900574 1016995 := bstep (se 1 (by rfl) ⟨762746, by rfl⟩ : syracuseStep 1016995 = 1525493) B1525493
theorem B1017139 : Blo 900574 1017139 := bstep (se 1 (by rfl) ⟨762854, by rfl⟩ : syracuseStep 1017139 = 1525709) B1525709
theorem B3048785 : Blo 900574 3048785 := bstep (se 2 (by rfl) ⟨1143294, by rfl⟩ : syracuseStep 3048785 = 2286589) B2286589
theorem B2033009 : Blo 900574 2033009 := bstep (se 2 (by rfl) ⟨762378, by rfl⟩ : syracuseStep 2033009 = 1524757) B1524757
theorem B2033027 : Blo 900574 2033027 := bstep (se 1 (by rfl) ⟨1524770, by rfl⟩ : syracuseStep 2033027 = 3049541) B3049541
theorem B1017283 : Blo 900574 1017283 := bstep (se 1 (by rfl) ⟨762962, by rfl⟩ : syracuseStep 1017283 = 1525925) B1525925
theorem B4687409 : Blo 900574 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B1443395 : Blo 900574 1443395 := bstep (se 1 (by rfl) ⟨1082546, by rfl⟩ : syracuseStep 1443395 = 2165093) B2165093
theorem B1017427 : Blo 900574 1017427 := bstep (se 1 (by rfl) ⟨763070, by rfl⟩ : syracuseStep 1017427 = 1526141) B1526141
theorem B2033297 : Blo 900574 2033297 := bstep (se 2 (by rfl) ⟨762486, by rfl⟩ : syracuseStep 2033297 = 1524973) B1524973
theorem B2033315 : Blo 900574 2033315 := bstep (se 1 (by rfl) ⟨1524986, by rfl⟩ : syracuseStep 2033315 = 3049973) B3049973
theorem B1443523 : Blo 900574 1443523 := bstep (se 1 (by rfl) ⟨1082642, by rfl⟩ : syracuseStep 1443523 = 2165285) B2165285
theorem B1017571 : Blo 900574 1017571 := bstep (se 1 (by rfl) ⟨763178, by rfl⟩ : syracuseStep 1017571 = 1526357) B1526357
theorem B1443587 : Blo 900574 1443587 := bstep (se 1 (by rfl) ⟨1082690, by rfl⟩ : syracuseStep 1443587 = 2165381) B2165381
theorem B3049325 : Blo 900574 3049325 := bstep (se 3 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 3049325 = 1143497) B1143497
theorem B3049379 : Blo 900574 3049379 := bstep (se 1 (by rfl) ⟨2287034, by rfl⟩ : syracuseStep 3049379 = 4574069) B4574069
theorem B2033585 : Blo 900574 2033585 := bstep (se 2 (by rfl) ⟨762594, by rfl⟩ : syracuseStep 2033585 = 1525189) B1525189
theorem B2033603 : Blo 900574 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B3049649 : Blo 900574 3049649 := bstep (se 2 (by rfl) ⟨1143618, by rfl⟩ : syracuseStep 3049649 = 2287237) B2287237
theorem B2033873 : Blo 900574 2033873 := bstep (se 2 (by rfl) ⟨762702, by rfl⟩ : syracuseStep 2033873 = 1525405) B1525405
theorem B2033891 : Blo 900574 2033891 := bstep (se 1 (by rfl) ⟨1525418, by rfl⟩ : syracuseStep 2033891 = 3050837) B3050837
theorem B1444081 : Blo 900574 1444081 := bstep (se 2 (by rfl) ⟨541530, by rfl⟩ : syracuseStep 1444081 = 1083061) B1083061
theorem B2885969 : Blo 900574 2885969 := bstep (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) B2164477
theorem B2165123 : Blo 900574 2165123 := bstep (se 1 (by rfl) ⟨1623842, by rfl⟩ : syracuseStep 2165123 = 3247685) B3247685
theorem B2034161 : Blo 900574 2034161 := bstep (se 2 (by rfl) ⟨762810, by rfl⟩ : syracuseStep 2034161 = 1525621) B1525621
theorem B2034179 : Blo 900574 2034179 := bstep (se 1 (by rfl) ⟨1525634, by rfl⟩ : syracuseStep 2034179 = 3051269) B3051269
theorem B6851141 : Blo 900574 6851141 := bstep (se 4 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 6851141 = 1284589) B1284589
theorem B2886317 : Blo 900574 2886317 := bstep (se 3 (by rfl) ⟨541184, by rfl⟩ : syracuseStep 2886317 = 1082369) B1082369
theorem B1084099 : Blo 900574 1084099 := bstep (se 1 (by rfl) ⟨813074, by rfl⟩ : syracuseStep 1084099 = 1626149) B1626149
theorem B6163141 : Blo 900574 6163141 := bstep (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) B1155589
theorem B5147333 : Blo 900574 5147333 := bstep (se 4 (by rfl) ⟨482562, by rfl⟩ : syracuseStep 5147333 = 965125) B965125
theorem B3050189 : Blo 900574 3050189 := bstep (se 3 (by rfl) ⟨571910, by rfl⟩ : syracuseStep 3050189 = 1143821) B1143821
theorem B2165507 : Blo 900574 2165507 := bstep (se 1 (by rfl) ⟨1624130, by rfl⟩ : syracuseStep 2165507 = 3248261) B3248261
theorem B3050243 : Blo 900574 3050243 := bstep (se 1 (by rfl) ⟨2287682, by rfl⟩ : syracuseStep 3050243 = 4575365) B4575365
theorem B2034449 : Blo 900574 2034449 := bstep (se 2 (by rfl) ⟨762918, by rfl⟩ : syracuseStep 2034449 = 1525837) B1525837
theorem B2034467 : Blo 900574 2034467 := bstep (se 1 (by rfl) ⟨1525850, by rfl⟩ : syracuseStep 2034467 = 3051701) B3051701
theorem B10292021 : Blo 900574 10292021 := bstep (se 5 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 10292021 = 964877) B964877
theorem B1444753 : Blo 900574 1444753 := bstep (se 2 (by rfl) ⟨541782, by rfl⟩ : syracuseStep 1444753 = 1083565) B1083565
theorem B1543139 : Blo 900574 1543139 := bstep (se 1 (by rfl) ⟨1157354, by rfl⟩ : syracuseStep 1543139 = 2314709) B2314709
theorem B3050513 : Blo 900574 3050513 := bstep (se 2 (by rfl) ⟨1143942, by rfl⟩ : syracuseStep 3050513 = 2287885) B2287885
theorem B2034737 : Blo 900574 2034737 := bstep (se 2 (by rfl) ⟨763026, by rfl⟩ : syracuseStep 2034737 = 1526053) B1526053
theorem B2034755 : Blo 900574 2034755 := bstep (se 1 (by rfl) ⟨1526066, by rfl⟩ : syracuseStep 2034755 = 3052133) B3052133
theorem B2035025 : Blo 900574 2035025 := bstep (se 2 (by rfl) ⟨763134, by rfl⟩ : syracuseStep 2035025 = 1526269) B1526269
theorem B2035043 : Blo 900574 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B3051053 : Blo 900574 3051053 := bstep (se 3 (by rfl) ⟨572072, by rfl⟩ : syracuseStep 3051053 = 1144145) B1144145
theorem B3051107 : Blo 900574 3051107 := bstep (se 1 (by rfl) ⟨2288330, by rfl⟩ : syracuseStep 3051107 = 4576661) B4576661
theorem B3051377 : Blo 900574 3051377 := bstep (se 2 (by rfl) ⟨1144266, by rfl⟩ : syracuseStep 3051377 = 2288533) B2288533
theorem B1445843 : Blo 900574 1445843 := bstep (se 1 (by rfl) ⟨1084382, by rfl⟩ : syracuseStep 1445843 = 2168765) B2168765
theorem B8687857 : Blo 900574 8687857 := bstep (se 2 (by rfl) ⟨3257946, by rfl⟩ : syracuseStep 8687857 = 6515893) B6515893
theorem B1446131 : Blo 900574 1446131 := bstep (se 1 (by rfl) ⟨1084598, by rfl⟩ : syracuseStep 1446131 = 2169197) B2169197
theorem B3051917 : Blo 900574 3051917 := bstep (se 3 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 3051917 = 1144469) B1144469
theorem B1085843 : Blo 900574 1085843 := bstep (se 1 (by rfl) ⟨814382, by rfl⟩ : syracuseStep 1085843 = 1628765) B1628765
theorem B3248561 : Blo 900574 3248561 := bstep (se 2 (by rfl) ⟨1218210, by rfl⟩ : syracuseStep 3248561 = 2436421) B2436421
theorem B1085891 : Blo 900574 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B3051971 : Blo 900574 3051971 := bstep (se 1 (by rfl) ⟨2288978, by rfl⟩ : syracuseStep 3051971 = 4577957) B4577957
theorem B7934435 : Blo 900574 7934435 := bstep (se 1 (by rfl) ⟨5950826, by rfl⟩ : syracuseStep 7934435 = 11901653) B11901653
theorem B2888173 : Blo 900574 2888173 := bstep (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) B1083065
theorem B1085987 : Blo 900574 1085987 := bstep (se 1 (by rfl) ⟨814490, by rfl⟩ : syracuseStep 1085987 = 1628981) B1628981
theorem B1446547 : Blo 900574 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B1282721 : Blo 900574 1282721 := bstep (se 2 (by rfl) ⟨481020, by rfl⟩ : syracuseStep 1282721 = 962041) B962041
theorem B3052241 : Blo 900574 3052241 := bstep (se 2 (by rfl) ⟨1144590, by rfl⟩ : syracuseStep 3052241 = 2289181) B2289181
theorem B11735779 : Blo 900574 11735779 := bstep (se 1 (by rfl) ⟨8801834, by rfl⟩ : syracuseStep 11735779 = 17603669) B17603669
theorem B1282835 : Blo 900574 1282835 := bstep (se 1 (by rfl) ⟨962126, by rfl⟩ : syracuseStep 1282835 = 1924253) B1924253
theorem B4559651 : Blo 900574 4559651 := bstep (se 1 (by rfl) ⟨3419738, by rfl⟩ : syracuseStep 4559651 = 6839477) B6839477
theorem B1282915 : Blo 900574 1282915 := bstep (se 1 (by rfl) ⟨962186, by rfl⟩ : syracuseStep 1282915 = 1924373) B1924373
theorem B1446817 : Blo 900574 1446817 := bstep (se 2 (by rfl) ⟨542556, by rfl⟩ : syracuseStep 1446817 = 1085113) B1085113
theorem B1447073 : Blo 900574 1447073 := bstep (se 2 (by rfl) ⟨542652, by rfl⟩ : syracuseStep 1447073 = 1085305) B1085305
theorem B3052781 : Blo 900574 3052781 := bstep (se 3 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 3052781 = 1144793) B1144793
theorem B3052835 : Blo 900574 3052835 := bstep (se 1 (by rfl) ⟨2289626, by rfl⟩ : syracuseStep 3052835 = 4579253) B4579253
theorem B1283473 : Blo 900574 1283473 := bstep (se 2 (by rfl) ⟨481302, by rfl⟩ : syracuseStep 1283473 = 962605) B962605
theorem B4560461 : Blo 900574 4560461 := bstep (se 3 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 4560461 = 1710173) B1710173
theorem B988771 : Blo 900574 988771 := bstep (se 1 (by rfl) ⟨741578, by rfl⟩ : syracuseStep 988771 = 1483157) B1483157
theorem B1545985 : Blo 900574 1545985 := bstep (se 2 (by rfl) ⟨579744, by rfl⟩ : syracuseStep 1545985 = 1159489) B1159489
theorem B4888325 : Blo 900574 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B3381005 : Blo 900574 3381005 := bstep (se 3 (by rfl) ⟨633938, by rfl⟩ : syracuseStep 3381005 = 1267877) B1267877
theorem B1447777 : Blo 900574 1447777 := bstep (se 2 (by rfl) ⟨542916, by rfl⟩ : syracuseStep 1447777 = 1085833) B1085833
theorem B1709923 : Blo 900574 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B3479395 : Blo 900574 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B2168707 : Blo 900574 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B1284179 : Blo 900574 1284179 := bstep (se 1 (by rfl) ⟨963134, by rfl⟩ : syracuseStep 1284179 = 1926269) B1926269
theorem B3086531 : Blo 900574 3086531 := bstep (se 1 (by rfl) ⟨2314898, by rfl⟩ : syracuseStep 3086531 = 4629797) B4629797
theorem B5478641 : Blo 900574 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B1710371 : Blo 900574 1710371 := bstep (se 1 (by rfl) ⟨1282778, by rfl⟩ : syracuseStep 1710371 = 2565557) B2565557
theorem B2890019 : Blo 900574 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B2169379 : Blo 900574 2169379 := bstep (se 1 (by rfl) ⟨1627034, by rfl⟩ : syracuseStep 2169379 = 3254069) B3254069
theorem B1710659 : Blo 900574 1710659 := bstep (se 1 (by rfl) ⟨1282994, by rfl⟩ : syracuseStep 1710659 = 2565989) B2565989
theorem B1219249 : Blo 900574 1219249 := bstep (se 2 (by rfl) ⟨457218, by rfl⟩ : syracuseStep 1219249 = 914437) B914437
theorem B2890417 : Blo 900574 2890417 := bstep (se 2 (by rfl) ⟨1083906, by rfl⟩ : syracuseStep 2890417 = 2167813) B2167813
theorem B1284817 : Blo 900574 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B1448675 : Blo 900574 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B1547041 : Blo 900574 1547041 := bstep (se 2 (by rfl) ⟨580140, by rfl⟩ : syracuseStep 1547041 = 1160281) B1160281
theorem B1284931 : Blo 900574 1284931 := bstep (se 1 (by rfl) ⟨963698, by rfl⟩ : syracuseStep 1284931 = 1927397) B1927397
theorem B1547075 : Blo 900574 1547075 := bstep (se 1 (by rfl) ⟨1160306, by rfl⟩ : syracuseStep 1547075 = 2320613) B2320613
theorem B1219411 : Blo 900574 1219411 := bstep (se 1 (by rfl) ⟨914558, by rfl⟩ : syracuseStep 1219411 = 1829117) B1829117
theorem B1448867 : Blo 900574 1448867 := bstep (se 1 (by rfl) ⟨1086650, by rfl⟩ : syracuseStep 1448867 = 2173301) B2173301
theorem B2169841 : Blo 900574 2169841 := bstep (se 2 (by rfl) ⟨813690, by rfl⟩ : syracuseStep 2169841 = 1627381) B1627381
theorem B2890865 : Blo 900574 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B1350881 : Blo 900574 1350881 := bstep (se 2 (by rfl) ⟨506580, by rfl⟩ : syracuseStep 1350881 = 1013161) B1013161
theorem B1350899 : Blo 900574 1350899 := bstep (se 1 (by rfl) ⟨1013174, by rfl⟩ : syracuseStep 1350899 = 2026349) B2026349
theorem B1350929 : Blo 900574 1350929 := bstep (se 2 (by rfl) ⟨506598, by rfl⟩ : syracuseStep 1350929 = 1013197) B1013197
theorem B1350947 : Blo 900574 1350947 := bstep (se 1 (by rfl) ⟨1013210, by rfl⟩ : syracuseStep 1350947 = 2026421) B2026421
theorem B1350977 : Blo 900574 1350977 := bstep (se 2 (by rfl) ⟨506616, by rfl⟩ : syracuseStep 1350977 = 1013233) B1013233
theorem B1350995 : Blo 900574 1350995 := bstep (se 1 (by rfl) ⟨1013246, by rfl⟩ : syracuseStep 1350995 = 2026493) B2026493
theorem B1351025 : Blo 900574 1351025 := bstep (se 2 (by rfl) ⟨506634, by rfl⟩ : syracuseStep 1351025 = 1013269) B1013269
theorem B1351043 : Blo 900574 1351043 := bstep (se 1 (by rfl) ⟨1013282, by rfl⟩ : syracuseStep 1351043 = 2026565) B2026565
theorem B1351073 : Blo 900574 1351073 := bstep (se 2 (by rfl) ⟨506652, by rfl⟩ : syracuseStep 1351073 = 1013305) B1013305
theorem B1351091 : Blo 900574 1351091 := bstep (se 1 (by rfl) ⟨1013318, by rfl⟩ : syracuseStep 1351091 = 2026637) B2026637
theorem B1351121 : Blo 900574 1351121 := bstep (se 2 (by rfl) ⟨506670, by rfl⟩ : syracuseStep 1351121 = 1013341) B1013341
theorem B1351139 : Blo 900574 1351139 := bstep (se 1 (by rfl) ⟨1013354, by rfl⟩ : syracuseStep 1351139 = 2026709) B2026709
theorem B1711601 : Blo 900574 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B1351169 : Blo 900574 1351169 := bstep (se 2 (by rfl) ⟨506688, by rfl⟩ : syracuseStep 1351169 = 1013377) B1013377
theorem B1351187 : Blo 900574 1351187 := bstep (se 1 (by rfl) ⟨1013390, by rfl⟩ : syracuseStep 1351187 = 2026781) B2026781
theorem B1351217 : Blo 900574 1351217 := bstep (se 2 (by rfl) ⟨506706, by rfl⟩ : syracuseStep 1351217 = 1013413) B1013413
theorem B1351235 : Blo 900574 1351235 := bstep (se 1 (by rfl) ⟨1013426, by rfl⟩ : syracuseStep 1351235 = 2026853) B2026853
theorem B1351265 : Blo 900574 1351265 := bstep (se 2 (by rfl) ⟨506724, by rfl⟩ : syracuseStep 1351265 = 1013449) B1013449
theorem B1351283 : Blo 900574 1351283 := bstep (se 1 (by rfl) ⟨1013462, by rfl⟩ : syracuseStep 1351283 = 2026925) B2026925
theorem B1351313 : Blo 900574 1351313 := bstep (se 2 (by rfl) ⟨506742, by rfl⟩ : syracuseStep 1351313 = 1013485) B1013485
theorem B1351331 : Blo 900574 1351331 := bstep (se 1 (by rfl) ⟨1013498, by rfl⟩ : syracuseStep 1351331 = 2026997) B2026997
theorem B5480099 : Blo 900574 5480099 := bstep (se 1 (by rfl) ⟨4110074, by rfl⟩ : syracuseStep 5480099 = 8220149) B8220149
theorem B1351361 : Blo 900574 1351361 := bstep (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) B1013521
theorem B1351379 : Blo 900574 1351379 := bstep (se 1 (by rfl) ⟨1013534, by rfl⟩ : syracuseStep 1351379 = 2027069) B2027069
theorem B1351409 : Blo 900574 1351409 := bstep (se 2 (by rfl) ⟨506778, by rfl⟩ : syracuseStep 1351409 = 1013557) B1013557
theorem B1351427 : Blo 900574 1351427 := bstep (se 1 (by rfl) ⟨1013570, by rfl⟩ : syracuseStep 1351427 = 2027141) B2027141
theorem B1351457 : Blo 900574 1351457 := bstep (se 2 (by rfl) ⟨506796, by rfl⟩ : syracuseStep 1351457 = 1013593) B1013593
theorem B1351475 : Blo 900574 1351475 := bstep (se 1 (by rfl) ⟨1013606, by rfl⟩ : syracuseStep 1351475 = 2027213) B2027213
theorem B1351505 : Blo 900574 1351505 := bstep (se 2 (by rfl) ⟨506814, by rfl⟩ : syracuseStep 1351505 = 1013629) B1013629
theorem B1351523 : Blo 900574 1351523 := bstep (se 1 (by rfl) ⟨1013642, by rfl⟩ : syracuseStep 1351523 = 2027285) B2027285
theorem B1318771 : Blo 900574 1318771 := bstep (se 1 (by rfl) ⟨989078, by rfl⟩ : syracuseStep 1318771 = 1978157) B1978157
theorem B1351553 : Blo 900574 1351553 := bstep (se 2 (by rfl) ⟨506832, by rfl⟩ : syracuseStep 1351553 = 1013665) B1013665
theorem B1351571 : Blo 900574 1351571 := bstep (se 1 (by rfl) ⟨1013678, by rfl⟩ : syracuseStep 1351571 = 2027357) B2027357
theorem B1351601 : Blo 900574 1351601 := bstep (se 2 (by rfl) ⟨506850, by rfl⟩ : syracuseStep 1351601 = 1013701) B1013701
theorem B1351619 : Blo 900574 1351619 := bstep (se 1 (by rfl) ⟨1013714, by rfl⟩ : syracuseStep 1351619 = 2027429) B2027429
theorem B1351649 : Blo 900574 1351649 := bstep (se 2 (by rfl) ⟨506868, by rfl⟩ : syracuseStep 1351649 = 1013737) B1013737
theorem B1351667 : Blo 900574 1351667 := bstep (se 1 (by rfl) ⟨1013750, by rfl⟩ : syracuseStep 1351667 = 2027501) B2027501
theorem B1351697 : Blo 900574 1351697 := bstep (se 2 (by rfl) ⟨506886, by rfl⟩ : syracuseStep 1351697 = 1013773) B1013773
theorem B1351715 : Blo 900574 1351715 := bstep (se 1 (by rfl) ⟨1013786, by rfl⟩ : syracuseStep 1351715 = 2027573) B2027573
theorem B1351745 : Blo 900574 1351745 := bstep (se 2 (by rfl) ⟨506904, by rfl⟩ : syracuseStep 1351745 = 1013809) B1013809
theorem B1351763 : Blo 900574 1351763 := bstep (se 1 (by rfl) ⟨1013822, by rfl⟩ : syracuseStep 1351763 = 2027645) B2027645
theorem B1351793 : Blo 900574 1351793 := bstep (se 2 (by rfl) ⟨506922, by rfl⟩ : syracuseStep 1351793 = 1013845) B1013845
theorem B1351811 : Blo 900574 1351811 := bstep (se 1 (by rfl) ⟨1013858, by rfl⟩ : syracuseStep 1351811 = 2027717) B2027717
theorem B1286275 : Blo 900574 1286275 := bstep (se 1 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 1286275 = 1929413) B1929413
theorem B1351841 : Blo 900574 1351841 := bstep (se 2 (by rfl) ⟨506940, by rfl⟩ : syracuseStep 1351841 = 1013881) B1013881
theorem B1351859 : Blo 900574 1351859 := bstep (se 1 (by rfl) ⟨1013894, by rfl⟩ : syracuseStep 1351859 = 2027789) B2027789
theorem B1351889 : Blo 900574 1351889 := bstep (se 2 (by rfl) ⟨506958, by rfl⟩ : syracuseStep 1351889 = 1013917) B1013917
theorem B1351907 : Blo 900574 1351907 := bstep (se 1 (by rfl) ⟨1013930, by rfl⟩ : syracuseStep 1351907 = 2027861) B2027861
theorem B1351937 : Blo 900574 1351937 := bstep (se 2 (by rfl) ⟨506976, by rfl⟩ : syracuseStep 1351937 = 1013953) B1013953
theorem B4333837 : Blo 900574 4333837 := bstep (se 3 (by rfl) ⟨812594, by rfl⟩ : syracuseStep 4333837 = 1625189) B1625189
theorem B6856973 : Blo 900574 6856973 := bstep (se 3 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 6856973 = 2571365) B2571365
theorem B1351955 : Blo 900574 1351955 := bstep (se 1 (by rfl) ⟨1013966, by rfl⟩ : syracuseStep 1351955 = 2027933) B2027933
theorem B1351985 : Blo 900574 1351985 := bstep (se 2 (by rfl) ⟨506994, by rfl⟩ : syracuseStep 1351985 = 1013989) B1013989
theorem B1483075 : Blo 900574 1483075 := bstep (se 1 (by rfl) ⟨1112306, by rfl⟩ : syracuseStep 1483075 = 2224613) B2224613
theorem B1352003 : Blo 900574 1352003 := bstep (se 1 (by rfl) ⟨1014002, by rfl⟩ : syracuseStep 1352003 = 2028005) B2028005
theorem B1352033 : Blo 900574 1352033 := bstep (se 2 (by rfl) ⟨507012, by rfl⟩ : syracuseStep 1352033 = 1014025) B1014025
theorem B1712497 : Blo 900574 1712497 := bstep (se 2 (by rfl) ⟨642186, by rfl⟩ : syracuseStep 1712497 = 1284373) B1284373
theorem B1352051 : Blo 900574 1352051 := bstep (se 1 (by rfl) ⟨1014038, by rfl⟩ : syracuseStep 1352051 = 2028077) B2028077
theorem B1352081 : Blo 900574 1352081 := bstep (se 2 (by rfl) ⟨507030, by rfl⟩ : syracuseStep 1352081 = 1014061) B1014061
theorem B1352099 : Blo 900574 1352099 := bstep (se 1 (by rfl) ⟨1014074, by rfl⟩ : syracuseStep 1352099 = 2028149) B2028149
theorem B4563377 : Blo 900574 4563377 := bstep (se 2 (by rfl) ⟨1711266, by rfl⟩ : syracuseStep 4563377 = 3422533) B3422533
theorem B1352129 : Blo 900574 1352129 := bstep (se 2 (by rfl) ⟨507048, by rfl⟩ : syracuseStep 1352129 = 1014097) B1014097
theorem B1352147 : Blo 900574 1352147 := bstep (se 1 (by rfl) ⟨1014110, by rfl⟩ : syracuseStep 1352147 = 2028221) B2028221
theorem B1352177 : Blo 900574 1352177 := bstep (se 2 (by rfl) ⟨507066, by rfl⟩ : syracuseStep 1352177 = 1014133) B1014133
theorem B1352195 : Blo 900574 1352195 := bstep (se 1 (by rfl) ⟨1014146, by rfl⟩ : syracuseStep 1352195 = 2028293) B2028293
theorem B1712657 : Blo 900574 1712657 := bstep (se 2 (by rfl) ⟨642246, by rfl⟩ : syracuseStep 1712657 = 1284493) B1284493
theorem B1352225 : Blo 900574 1352225 := bstep (se 2 (by rfl) ⟨507084, by rfl⟩ : syracuseStep 1352225 = 1014169) B1014169
theorem B1352243 : Blo 900574 1352243 := bstep (se 1 (by rfl) ⟨1014182, by rfl⟩ : syracuseStep 1352243 = 2028365) B2028365
theorem B1352273 : Blo 900574 1352273 := bstep (se 2 (by rfl) ⟨507102, by rfl⟩ : syracuseStep 1352273 = 1014205) B1014205
theorem B1352291 : Blo 900574 1352291 := bstep (se 1 (by rfl) ⟨1014218, by rfl⟩ : syracuseStep 1352291 = 2028437) B2028437
theorem B1352321 : Blo 900574 1352321 := bstep (se 2 (by rfl) ⟨507120, by rfl⟩ : syracuseStep 1352321 = 1014241) B1014241
theorem B1352339 : Blo 900574 1352339 := bstep (se 1 (by rfl) ⟨1014254, by rfl⟩ : syracuseStep 1352339 = 2028509) B2028509
theorem B1352369 : Blo 900574 1352369 := bstep (se 2 (by rfl) ⟨507138, by rfl⟩ : syracuseStep 1352369 = 1014277) B1014277
theorem B1352387 : Blo 900574 1352387 := bstep (se 1 (by rfl) ⟨1014290, by rfl⟩ : syracuseStep 1352387 = 2028581) B2028581
theorem B1352417 : Blo 900574 1352417 := bstep (se 2 (by rfl) ⟨507156, by rfl⟩ : syracuseStep 1352417 = 1014313) B1014313
theorem B6497009 : Blo 900574 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B1352435 : Blo 900574 1352435 := bstep (se 1 (by rfl) ⟨1014326, by rfl⟩ : syracuseStep 1352435 = 2028653) B2028653
theorem B1352465 : Blo 900574 1352465 := bstep (se 2 (by rfl) ⟨507174, by rfl⟩ : syracuseStep 1352465 = 1014349) B1014349
theorem B1352483 : Blo 900574 1352483 := bstep (se 1 (by rfl) ⟨1014362, by rfl⟩ : syracuseStep 1352483 = 2028725) B2028725
theorem B1352513 : Blo 900574 1352513 := bstep (se 2 (by rfl) ⟨507192, by rfl⟩ : syracuseStep 1352513 = 1014385) B1014385
theorem B2564941 : Blo 900574 2564941 := bstep (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) B961853
theorem B1352531 : Blo 900574 1352531 := bstep (se 1 (by rfl) ⟨1014398, by rfl⟩ : syracuseStep 1352531 = 2028797) B2028797
theorem B1352561 : Blo 900574 1352561 := bstep (se 2 (by rfl) ⟨507210, by rfl⟩ : syracuseStep 1352561 = 1014421) B1014421
theorem B1352579 : Blo 900574 1352579 := bstep (se 1 (by rfl) ⟨1014434, by rfl⟩ : syracuseStep 1352579 = 2028869) B2028869
theorem B1352609 : Blo 900574 1352609 := bstep (se 2 (by rfl) ⟨507228, by rfl⟩ : syracuseStep 1352609 = 1014457) B1014457
theorem B1713059 : Blo 900574 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B1352627 : Blo 900574 1352627 := bstep (se 1 (by rfl) ⟨1014470, by rfl⟩ : syracuseStep 1352627 = 2028941) B2028941
theorem B1352657 : Blo 900574 1352657 := bstep (se 2 (by rfl) ⟨507246, by rfl⟩ : syracuseStep 1352657 = 1014493) B1014493
theorem B1352675 : Blo 900574 1352675 := bstep (se 1 (by rfl) ⟨1014506, by rfl⟩ : syracuseStep 1352675 = 2029013) B2029013
theorem B2565101 : Blo 900574 2565101 := bstep (se 3 (by rfl) ⟨480956, by rfl⟩ : syracuseStep 2565101 = 961913) B961913
theorem B1352705 : Blo 900574 1352705 := bstep (se 2 (by rfl) ⟨507264, by rfl⟩ : syracuseStep 1352705 = 1014529) B1014529
theorem B1352723 : Blo 900574 1352723 := bstep (se 1 (by rfl) ⟨1014542, by rfl⟩ : syracuseStep 1352723 = 2029085) B2029085
theorem B1352753 : Blo 900574 1352753 := bstep (se 2 (by rfl) ⟨507282, by rfl⟩ : syracuseStep 1352753 = 1014565) B1014565
theorem B1352771 : Blo 900574 1352771 := bstep (se 1 (by rfl) ⟨1014578, by rfl⟩ : syracuseStep 1352771 = 2029157) B2029157
theorem B1352801 : Blo 900574 1352801 := bstep (se 2 (by rfl) ⟨507300, by rfl⟩ : syracuseStep 1352801 = 1014601) B1014601
theorem B1352819 : Blo 900574 1352819 := bstep (se 1 (by rfl) ⟨1014614, by rfl⟩ : syracuseStep 1352819 = 2029229) B2029229
theorem B2892941 : Blo 900574 2892941 := bstep (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) B1084853
theorem B1352849 : Blo 900574 1352849 := bstep (se 2 (by rfl) ⟨507318, by rfl⟩ : syracuseStep 1352849 = 1014637) B1014637
theorem B2565283 : Blo 900574 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1352867 : Blo 900574 1352867 := bstep (se 1 (by rfl) ⟨1014650, by rfl⟩ : syracuseStep 1352867 = 2029301) B2029301
theorem B1352897 : Blo 900574 1352897 := bstep (se 2 (by rfl) ⟨507336, by rfl⟩ : syracuseStep 1352897 = 1014673) B1014673
theorem B1352915 : Blo 900574 1352915 := bstep (se 1 (by rfl) ⟨1014686, by rfl⟩ : syracuseStep 1352915 = 2029373) B2029373
theorem B1352945 : Blo 900574 1352945 := bstep (se 2 (by rfl) ⟨507354, by rfl⟩ : syracuseStep 1352945 = 1014709) B1014709
theorem B1287409 : Blo 900574 1287409 := bstep (se 2 (by rfl) ⟨482778, by rfl⟩ : syracuseStep 1287409 = 965557) B965557
theorem B1352963 : Blo 900574 1352963 := bstep (se 1 (by rfl) ⟨1014722, by rfl⟩ : syracuseStep 1352963 = 2029445) B2029445
theorem B1352993 : Blo 900574 1352993 := bstep (se 2 (by rfl) ⟨507372, by rfl⟩ : syracuseStep 1352993 = 1014745) B1014745
theorem B1353011 : Blo 900574 1353011 := bstep (se 1 (by rfl) ⟨1014758, by rfl⟩ : syracuseStep 1353011 = 2029517) B2029517
theorem B1353041 : Blo 900574 1353041 := bstep (se 2 (by rfl) ⟨507390, by rfl⟩ : syracuseStep 1353041 = 1014781) B1014781
theorem B1287505 : Blo 900574 1287505 := bstep (se 2 (by rfl) ⟨482814, by rfl⟩ : syracuseStep 1287505 = 965629) B965629
theorem B1353059 : Blo 900574 1353059 := bstep (se 1 (by rfl) ⟨1014794, by rfl⟩ : syracuseStep 1353059 = 2029589) B2029589
theorem B7710065 : Blo 900574 7710065 := bstep (se 2 (by rfl) ⟨2891274, by rfl⟩ : syracuseStep 7710065 = 5782549) B5782549
theorem B1353089 : Blo 900574 1353089 := bstep (se 2 (by rfl) ⟨507408, by rfl⟩ : syracuseStep 1353089 = 1014817) B1014817
theorem B1353107 : Blo 900574 1353107 := bstep (se 1 (by rfl) ⟨1014830, by rfl⟩ : syracuseStep 1353107 = 2029661) B2029661
theorem B1353137 : Blo 900574 1353137 := bstep (se 2 (by rfl) ⟨507426, by rfl⟩ : syracuseStep 1353137 = 1014853) B1014853
theorem B1353155 : Blo 900574 1353155 := bstep (se 1 (by rfl) ⟨1014866, by rfl⟩ : syracuseStep 1353155 = 2029733) B2029733
theorem B1353185 : Blo 900574 1353185 := bstep (se 2 (by rfl) ⟨507444, by rfl⟩ : syracuseStep 1353185 = 1014889) B1014889
theorem B1353203 : Blo 900574 1353203 := bstep (se 1 (by rfl) ⟨1014902, by rfl⟩ : syracuseStep 1353203 = 2029805) B2029805
theorem B1353233 : Blo 900574 1353233 := bstep (se 2 (by rfl) ⟨507462, by rfl⟩ : syracuseStep 1353233 = 1014925) B1014925
theorem B1353251 : Blo 900574 1353251 := bstep (se 1 (by rfl) ⟨1014938, by rfl⟩ : syracuseStep 1353251 = 2029877) B2029877
theorem B1353281 : Blo 900574 1353281 := bstep (se 2 (by rfl) ⟨507480, by rfl⟩ : syracuseStep 1353281 = 1014961) B1014961
theorem B3090001 : Blo 900574 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B1353299 : Blo 900574 1353299 := bstep (se 1 (by rfl) ⟨1014974, by rfl⟩ : syracuseStep 1353299 = 2029949) B2029949
theorem B1353329 : Blo 900574 1353329 := bstep (se 2 (by rfl) ⟨507498, by rfl⟩ : syracuseStep 1353329 = 1014997) B1014997
theorem B1353347 : Blo 900574 1353347 := bstep (se 1 (by rfl) ⟨1015010, by rfl⟩ : syracuseStep 1353347 = 2030021) B2030021
theorem B1353377 : Blo 900574 1353377 := bstep (se 2 (by rfl) ⟨507516, by rfl⟩ : syracuseStep 1353377 = 1015033) B1015033
theorem B1353395 : Blo 900574 1353395 := bstep (se 1 (by rfl) ⟨1015046, by rfl⟩ : syracuseStep 1353395 = 2030093) B2030093
theorem B1353425 : Blo 900574 1353425 := bstep (se 2 (by rfl) ⟨507534, by rfl⟩ : syracuseStep 1353425 = 1015069) B1015069
theorem B1353443 : Blo 900574 1353443 := bstep (se 1 (by rfl) ⟨1015082, by rfl⟩ : syracuseStep 1353443 = 2030165) B2030165
theorem B1353473 : Blo 900574 1353473 := bstep (se 2 (by rfl) ⟨507552, by rfl⟩ : syracuseStep 1353473 = 1015105) B1015105
theorem B6956813 : Blo 900574 6956813 := bstep (se 3 (by rfl) ⟨1304402, by rfl⟩ : syracuseStep 6956813 = 2608805) B2608805
theorem B1353491 : Blo 900574 1353491 := bstep (se 1 (by rfl) ⟨1015118, by rfl⟩ : syracuseStep 1353491 = 2030237) B2030237
theorem B1713955 : Blo 900574 1713955 := bstep (se 1 (by rfl) ⟨1285466, by rfl⟩ : syracuseStep 1713955 = 2570933) B2570933
theorem B3090221 : Blo 900574 3090221 := bstep (se 3 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 3090221 = 1158833) B1158833
theorem B1353521 : Blo 900574 1353521 := bstep (se 2 (by rfl) ⟨507570, by rfl⟩ : syracuseStep 1353521 = 1015141) B1015141
theorem B1353539 : Blo 900574 1353539 := bstep (se 1 (by rfl) ⟨1015154, by rfl⟩ : syracuseStep 1353539 = 2030309) B2030309
theorem B1353569 : Blo 900574 1353569 := bstep (se 2 (by rfl) ⟨507588, by rfl⟩ : syracuseStep 1353569 = 1015177) B1015177
theorem B4564835 : Blo 900574 4564835 := bstep (se 1 (by rfl) ⟨3423626, by rfl⟩ : syracuseStep 4564835 = 6847253) B6847253
theorem B1353587 : Blo 900574 1353587 := bstep (se 1 (by rfl) ⟨1015190, by rfl⟩ : syracuseStep 1353587 = 2030381) B2030381
theorem B1353617 : Blo 900574 1353617 := bstep (se 2 (by rfl) ⟨507606, by rfl⟩ : syracuseStep 1353617 = 1015213) B1015213
theorem B1353635 : Blo 900574 1353635 := bstep (se 1 (by rfl) ⟨1015226, by rfl⟩ : syracuseStep 1353635 = 2030453) B2030453
theorem B1353665 : Blo 900574 1353665 := bstep (se 2 (by rfl) ⟨507624, by rfl⟩ : syracuseStep 1353665 = 1015249) B1015249
theorem B1714115 : Blo 900574 1714115 := bstep (se 1 (by rfl) ⟨1285586, by rfl⟩ : syracuseStep 1714115 = 2571173) B2571173
theorem B1353683 : Blo 900574 1353683 := bstep (se 1 (by rfl) ⟨1015262, by rfl⟩ : syracuseStep 1353683 = 2030525) B2030525
theorem B1353713 : Blo 900574 1353713 := bstep (se 2 (by rfl) ⟨507642, by rfl⟩ : syracuseStep 1353713 = 1015285) B1015285
theorem B1353731 : Blo 900574 1353731 := bstep (se 1 (by rfl) ⟨1015298, by rfl⟩ : syracuseStep 1353731 = 2030597) B2030597
theorem B1353761 : Blo 900574 1353761 := bstep (se 2 (by rfl) ⟨507660, by rfl⟩ : syracuseStep 1353761 = 1015321) B1015321
theorem B1353779 : Blo 900574 1353779 := bstep (se 1 (by rfl) ⟨1015334, by rfl⟩ : syracuseStep 1353779 = 2030669) B2030669
theorem B1353809 : Blo 900574 1353809 := bstep (se 2 (by rfl) ⟨507678, by rfl⟩ : syracuseStep 1353809 = 1015357) B1015357
theorem B1353827 : Blo 900574 1353827 := bstep (se 1 (by rfl) ⟨1015370, by rfl⟩ : syracuseStep 1353827 = 2030741) B2030741
theorem B1353857 : Blo 900574 1353857 := bstep (se 2 (by rfl) ⟨507696, by rfl⟩ : syracuseStep 1353857 = 1015393) B1015393
theorem B1353875 : Blo 900574 1353875 := bstep (se 1 (by rfl) ⟨1015406, by rfl⟩ : syracuseStep 1353875 = 2030813) B2030813
theorem B1353905 : Blo 900574 1353905 := bstep (se 2 (by rfl) ⟨507714, by rfl⟩ : syracuseStep 1353905 = 1015429) B1015429
theorem B1353923 : Blo 900574 1353923 := bstep (se 1 (by rfl) ⟨1015442, by rfl⟩ : syracuseStep 1353923 = 2030885) B2030885
theorem B1353953 : Blo 900574 1353953 := bstep (se 2 (by rfl) ⟨507732, by rfl⟩ : syracuseStep 1353953 = 1015465) B1015465
theorem B1353971 : Blo 900574 1353971 := bstep (se 1 (by rfl) ⟨1015478, by rfl⟩ : syracuseStep 1353971 = 2030957) B2030957
theorem B1354001 : Blo 900574 1354001 := bstep (se 2 (by rfl) ⟨507750, by rfl⟩ : syracuseStep 1354001 = 1015501) B1015501
theorem B1354019 : Blo 900574 1354019 := bstep (se 1 (by rfl) ⟨1015514, by rfl⟩ : syracuseStep 1354019 = 2031029) B2031029
theorem B1354049 : Blo 900574 1354049 := bstep (se 2 (by rfl) ⟨507768, by rfl⟩ : syracuseStep 1354049 = 1015537) B1015537
theorem B1354067 : Blo 900574 1354067 := bstep (se 1 (by rfl) ⟨1015550, by rfl⟩ : syracuseStep 1354067 = 2031101) B2031101
theorem B1354097 : Blo 900574 1354097 := bstep (se 2 (by rfl) ⟨507786, by rfl⟩ : syracuseStep 1354097 = 1015573) B1015573
theorem B1354115 : Blo 900574 1354115 := bstep (se 1 (by rfl) ⟨1015586, by rfl⟩ : syracuseStep 1354115 = 2031173) B2031173
theorem B2894221 : Blo 900574 2894221 := bstep (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) B1085333
theorem B1354145 : Blo 900574 1354145 := bstep (se 2 (by rfl) ⟨507804, by rfl⟩ : syracuseStep 1354145 = 1015609) B1015609
theorem B1354163 : Blo 900574 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B1354193 : Blo 900574 1354193 := bstep (se 2 (by rfl) ⟨507822, by rfl⟩ : syracuseStep 1354193 = 1015645) B1015645
theorem B1354211 : Blo 900574 1354211 := bstep (se 1 (by rfl) ⟨1015658, by rfl⟩ : syracuseStep 1354211 = 2031317) B2031317
theorem B1354241 : Blo 900574 1354241 := bstep (se 2 (by rfl) ⟨507840, by rfl⟩ : syracuseStep 1354241 = 1015681) B1015681
theorem B2566673 : Blo 900574 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B1354259 : Blo 900574 1354259 := bstep (se 1 (by rfl) ⟨1015694, by rfl⟩ : syracuseStep 1354259 = 2031389) B2031389
theorem B1354289 : Blo 900574 1354289 := bstep (se 2 (by rfl) ⟨507858, by rfl⟩ : syracuseStep 1354289 = 1015717) B1015717
theorem B1354307 : Blo 900574 1354307 := bstep (se 1 (by rfl) ⟨1015730, by rfl⟩ : syracuseStep 1354307 = 2031461) B2031461
theorem B1354337 : Blo 900574 1354337 := bstep (se 2 (by rfl) ⟨507876, by rfl⟩ : syracuseStep 1354337 = 1015753) B1015753
theorem B10267235 : Blo 900574 10267235 := bstep (se 1 (by rfl) ⟨7700426, by rfl⟩ : syracuseStep 10267235 = 15400853) B15400853
theorem B15444593 : Blo 900574 15444593 := bstep (se 2 (by rfl) ⟨5791722, by rfl⟩ : syracuseStep 15444593 = 11583445) B11583445
theorem B1354355 : Blo 900574 1354355 := bstep (se 1 (by rfl) ⟨1015766, by rfl⟩ : syracuseStep 1354355 = 2031533) B2031533
theorem B2468483 : Blo 900574 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B4565645 : Blo 900574 4565645 := bstep (se 3 (by rfl) ⟨856058, by rfl⟩ : syracuseStep 4565645 = 1712117) B1712117
theorem B1354385 : Blo 900574 1354385 := bstep (se 2 (by rfl) ⟨507894, by rfl⟩ : syracuseStep 1354385 = 1015789) B1015789
theorem B1354403 : Blo 900574 1354403 := bstep (se 1 (by rfl) ⟨1015802, by rfl⟩ : syracuseStep 1354403 = 2031605) B2031605
theorem B1354433 : Blo 900574 1354433 := bstep (se 2 (by rfl) ⟨507912, by rfl⟩ : syracuseStep 1354433 = 1015825) B1015825
theorem B5483213 : Blo 900574 5483213 := bstep (se 3 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 5483213 = 2056205) B2056205
theorem B1354451 : Blo 900574 1354451 := bstep (se 1 (by rfl) ⟨1015838, by rfl⟩ : syracuseStep 1354451 = 2031677) B2031677
theorem B1354481 : Blo 900574 1354481 := bstep (se 2 (by rfl) ⟨507930, by rfl⟩ : syracuseStep 1354481 = 1015861) B1015861
theorem B1354499 : Blo 900574 1354499 := bstep (se 1 (by rfl) ⟨1015874, by rfl⟩ : syracuseStep 1354499 = 2031749) B2031749
theorem B1354529 : Blo 900574 1354529 := bstep (se 2 (by rfl) ⟨507948, by rfl⟩ : syracuseStep 1354529 = 1015897) B1015897
theorem B1354547 : Blo 900574 1354547 := bstep (se 1 (by rfl) ⟨1015910, by rfl⟩ : syracuseStep 1354547 = 2031821) B2031821
theorem B1354577 : Blo 900574 1354577 := bstep (se 2 (by rfl) ⟨507966, by rfl⟩ : syracuseStep 1354577 = 1015933) B1015933
theorem B1157971 : Blo 900574 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B1354595 : Blo 900574 1354595 := bstep (se 1 (by rfl) ⟨1015946, by rfl⟩ : syracuseStep 1354595 = 2031893) B2031893
theorem B1354625 : Blo 900574 1354625 := bstep (se 2 (by rfl) ⟨507984, by rfl⟩ : syracuseStep 1354625 = 1015969) B1015969
theorem B2894723 : Blo 900574 2894723 := bstep (se 1 (by rfl) ⟨2171042, by rfl⟩ : syracuseStep 2894723 = 4342085) B4342085
theorem B1354643 : Blo 900574 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B1354673 : Blo 900574 1354673 := bstep (se 2 (by rfl) ⟨508002, by rfl⟩ : syracuseStep 1354673 = 1016005) B1016005
theorem B1354691 : Blo 900574 1354691 := bstep (se 1 (by rfl) ⟨1016018, by rfl⟩ : syracuseStep 1354691 = 2032037) B2032037
theorem B1354721 : Blo 900574 1354721 := bstep (se 2 (by rfl) ⟨508020, by rfl⟩ : syracuseStep 1354721 = 1016041) B1016041
theorem B1715185 : Blo 900574 1715185 := bstep (se 2 (by rfl) ⟨643194, by rfl⟩ : syracuseStep 1715185 = 1286389) B1286389
theorem B1354739 : Blo 900574 1354739 := bstep (se 1 (by rfl) ⟨1016054, by rfl⟩ : syracuseStep 1354739 = 2032109) B2032109
theorem B1354769 : Blo 900574 1354769 := bstep (se 2 (by rfl) ⟨508038, by rfl⟩ : syracuseStep 1354769 = 1016077) B1016077
theorem B1354787 : Blo 900574 1354787 := bstep (se 1 (by rfl) ⟨1016090, by rfl⟩ : syracuseStep 1354787 = 2032181) B2032181
theorem B1354817 : Blo 900574 1354817 := bstep (se 2 (by rfl) ⟨508056, by rfl⟩ : syracuseStep 1354817 = 1016113) B1016113
theorem B1354835 : Blo 900574 1354835 := bstep (se 1 (by rfl) ⟨1016126, by rfl⟩ : syracuseStep 1354835 = 2032253) B2032253
theorem B1354865 : Blo 900574 1354865 := bstep (se 2 (by rfl) ⟨508074, by rfl⟩ : syracuseStep 1354865 = 1016149) B1016149
theorem B6859889 : Blo 900574 6859889 := bstep (se 2 (by rfl) ⟨2572458, by rfl⟩ : syracuseStep 6859889 = 5144917) B5144917
theorem B1354883 : Blo 900574 1354883 := bstep (se 1 (by rfl) ⟨1016162, by rfl⟩ : syracuseStep 1354883 = 2032325) B2032325
theorem B1354913 : Blo 900574 1354913 := bstep (se 2 (by rfl) ⟨508092, by rfl⟩ : syracuseStep 1354913 = 1016185) B1016185
theorem B1354931 : Blo 900574 1354931 := bstep (se 1 (by rfl) ⟨1016198, by rfl⟩ : syracuseStep 1354931 = 2032397) B2032397
theorem B1354961 : Blo 900574 1354961 := bstep (se 2 (by rfl) ⟨508110, by rfl⟩ : syracuseStep 1354961 = 1016221) B1016221
theorem B1354979 : Blo 900574 1354979 := bstep (se 1 (by rfl) ⟨1016234, by rfl⟩ : syracuseStep 1354979 = 2032469) B2032469
theorem B1355009 : Blo 900574 1355009 := bstep (se 2 (by rfl) ⟨508128, by rfl⟩ : syracuseStep 1355009 = 1016257) B1016257
theorem B3419405 : Blo 900574 3419405 := bstep (se 3 (by rfl) ⟨641138, by rfl⟩ : syracuseStep 3419405 = 1282277) B1282277
theorem B1355027 : Blo 900574 1355027 := bstep (se 1 (by rfl) ⟨1016270, by rfl⟩ : syracuseStep 1355027 = 2032541) B2032541
theorem B1355057 : Blo 900574 1355057 := bstep (se 2 (by rfl) ⟨508146, by rfl⟩ : syracuseStep 1355057 = 1016293) B1016293
theorem B1355075 : Blo 900574 1355075 := bstep (se 1 (by rfl) ⟨1016306, by rfl⟩ : syracuseStep 1355075 = 2032613) B2032613
theorem B1355105 : Blo 900574 1355105 := bstep (se 2 (by rfl) ⟨508164, by rfl⟩ : syracuseStep 1355105 = 1016329) B1016329
theorem B1355123 : Blo 900574 1355123 := bstep (se 1 (by rfl) ⟨1016342, by rfl⟩ : syracuseStep 1355123 = 2032685) B2032685
theorem B1355153 : Blo 900574 1355153 := bstep (se 2 (by rfl) ⟨508182, by rfl⟩ : syracuseStep 1355153 = 1016365) B1016365
theorem B1355171 : Blo 900574 1355171 := bstep (se 1 (by rfl) ⟨1016378, by rfl⟩ : syracuseStep 1355171 = 2032757) B2032757
theorem B1355201 : Blo 900574 1355201 := bstep (se 2 (by rfl) ⟨508200, by rfl⟩ : syracuseStep 1355201 = 1016401) B1016401
theorem B2567629 : Blo 900574 2567629 := bstep (se 3 (by rfl) ⟨481430, by rfl⟩ : syracuseStep 2567629 = 962861) B962861
theorem B962003 : Blo 900574 962003 := bstep (se 1 (by rfl) ⟨721502, by rfl⟩ : syracuseStep 962003 = 1443005) B1443005
theorem B1355219 : Blo 900574 1355219 := bstep (se 1 (by rfl) ⟨1016414, by rfl⟩ : syracuseStep 1355219 = 2032829) B2032829
theorem B1355249 : Blo 900574 1355249 := bstep (se 2 (by rfl) ⟨508218, by rfl⟩ : syracuseStep 1355249 = 1016437) B1016437
theorem B1355267 : Blo 900574 1355267 := bstep (se 1 (by rfl) ⟨1016450, by rfl⟩ : syracuseStep 1355267 = 2032901) B2032901
theorem B1355297 : Blo 900574 1355297 := bstep (se 2 (by rfl) ⟨508236, by rfl⟩ : syracuseStep 1355297 = 1016473) B1016473
theorem B1355315 : Blo 900574 1355315 := bstep (se 1 (by rfl) ⟨1016486, by rfl⟩ : syracuseStep 1355315 = 2032973) B2032973
theorem B1355345 : Blo 900574 1355345 := bstep (se 2 (by rfl) ⟨508254, by rfl⟩ : syracuseStep 1355345 = 1016509) B1016509
theorem B1355363 : Blo 900574 1355363 := bstep (se 1 (by rfl) ⟨1016522, by rfl⟩ : syracuseStep 1355363 = 2033045) B2033045
theorem B1355393 : Blo 900574 1355393 := bstep (se 2 (by rfl) ⟨508272, by rfl⟩ : syracuseStep 1355393 = 1016545) B1016545
theorem B1355411 : Blo 900574 1355411 := bstep (se 1 (by rfl) ⟨1016558, by rfl⟩ : syracuseStep 1355411 = 2033117) B2033117
theorem B2567857 : Blo 900574 2567857 := bstep (se 2 (by rfl) ⟨962946, by rfl⟩ : syracuseStep 2567857 = 1925893) B1925893
theorem B2928305 : Blo 900574 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B1355441 : Blo 900574 1355441 := bstep (se 2 (by rfl) ⟨508290, by rfl⟩ : syracuseStep 1355441 = 1016581) B1016581
theorem B1355459 : Blo 900574 1355459 := bstep (se 1 (by rfl) ⟨1016594, by rfl⟩ : syracuseStep 1355459 = 2033189) B2033189
theorem B1355489 : Blo 900574 1355489 := bstep (se 2 (by rfl) ⟨508308, by rfl⟩ : syracuseStep 1355489 = 1016617) B1016617
theorem B1650403 : Blo 900574 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B1355507 : Blo 900574 1355507 := bstep (se 1 (by rfl) ⟨1016630, by rfl⟩ : syracuseStep 1355507 = 2033261) B2033261
theorem B1355537 : Blo 900574 1355537 := bstep (se 2 (by rfl) ⟨508326, by rfl⟩ : syracuseStep 1355537 = 1016653) B1016653
theorem B1355555 : Blo 900574 1355555 := bstep (se 1 (by rfl) ⟨1016666, by rfl⟩ : syracuseStep 1355555 = 2033333) B2033333
theorem B1355585 : Blo 900574 1355585 := bstep (se 2 (by rfl) ⟨508344, by rfl⟩ : syracuseStep 1355585 = 1016689) B1016689
theorem B2568017 : Blo 900574 2568017 := bstep (se 2 (by rfl) ⟨963006, by rfl⟩ : syracuseStep 2568017 = 1926013) B1926013
theorem B1355603 : Blo 900574 1355603 := bstep (se 1 (by rfl) ⟨1016702, by rfl⟩ : syracuseStep 1355603 = 2033405) B2033405
theorem B6500209 : Blo 900574 6500209 := bstep (se 2 (by rfl) ⟨2437578, by rfl⟩ : syracuseStep 6500209 = 4875157) B4875157
theorem B1355633 : Blo 900574 1355633 := bstep (se 2 (by rfl) ⟨508362, by rfl⟩ : syracuseStep 1355633 = 1016725) B1016725
theorem B1355651 : Blo 900574 1355651 := bstep (se 1 (by rfl) ⟨1016738, by rfl⟩ : syracuseStep 1355651 = 2033477) B2033477
theorem B1355681 : Blo 900574 1355681 := bstep (se 2 (by rfl) ⟨508380, by rfl⟩ : syracuseStep 1355681 = 1016761) B1016761
theorem B1355699 : Blo 900574 1355699 := bstep (se 1 (by rfl) ⟨1016774, by rfl⟩ : syracuseStep 1355699 = 2033549) B2033549
theorem B2568131 : Blo 900574 2568131 := bstep (se 1 (by rfl) ⟨1926098, by rfl⟩ : syracuseStep 2568131 = 3852197) B3852197
theorem B1355729 : Blo 900574 1355729 := bstep (se 2 (by rfl) ⟨508398, by rfl⟩ : syracuseStep 1355729 = 1016797) B1016797
theorem B1355747 : Blo 900574 1355747 := bstep (se 1 (by rfl) ⟨1016810, by rfl⟩ : syracuseStep 1355747 = 2033621) B2033621
theorem B1355777 : Blo 900574 1355777 := bstep (se 2 (by rfl) ⟨508416, by rfl⟩ : syracuseStep 1355777 = 1016833) B1016833
theorem B1716241 : Blo 900574 1716241 := bstep (se 2 (by rfl) ⟨643590, by rfl⟩ : syracuseStep 1716241 = 1287181) B1287181
theorem B1355795 : Blo 900574 1355795 := bstep (se 1 (by rfl) ⟨1016846, by rfl⟩ : syracuseStep 1355795 = 2033693) B2033693
theorem B1355825 : Blo 900574 1355825 := bstep (se 2 (by rfl) ⟨508434, by rfl⟩ : syracuseStep 1355825 = 1016869) B1016869
theorem B1355843 : Blo 900574 1355843 := bstep (se 1 (by rfl) ⟨1016882, by rfl⟩ : syracuseStep 1355843 = 2033765) B2033765
theorem B1355873 : Blo 900574 1355873 := bstep (se 2 (by rfl) ⟨508452, by rfl⟩ : syracuseStep 1355873 = 1016905) B1016905
theorem B1355891 : Blo 900574 1355891 := bstep (se 1 (by rfl) ⟨1016918, by rfl⟩ : syracuseStep 1355891 = 2033837) B2033837
theorem B1355921 : Blo 900574 1355921 := bstep (se 2 (by rfl) ⟨508470, by rfl⟩ : syracuseStep 1355921 = 1016941) B1016941
theorem B1355939 : Blo 900574 1355939 := bstep (se 1 (by rfl) ⟨1016954, by rfl⟩ : syracuseStep 1355939 = 2033909) B2033909
theorem B1355969 : Blo 900574 1355969 := bstep (se 2 (by rfl) ⟨508488, by rfl⟩ : syracuseStep 1355969 = 1016977) B1016977
theorem B2896067 : Blo 900574 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B1355987 : Blo 900574 1355987 := bstep (se 1 (by rfl) ⟨1016990, by rfl⟩ : syracuseStep 1355987 = 2033981) B2033981
theorem B1519843 : Blo 900574 1519843 := bstep (se 1 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 1519843 = 2279765) B2279765
theorem B1356017 : Blo 900574 1356017 := bstep (se 2 (by rfl) ⟨508506, by rfl⟩ : syracuseStep 1356017 = 1017013) B1017013
theorem B1356035 : Blo 900574 1356035 := bstep (se 1 (by rfl) ⟨1017026, by rfl⟩ : syracuseStep 1356035 = 2034053) B2034053
theorem B1356065 : Blo 900574 1356065 := bstep (se 2 (by rfl) ⟨508524, by rfl⟩ : syracuseStep 1356065 = 1017049) B1017049
theorem B1356083 : Blo 900574 1356083 := bstep (se 1 (by rfl) ⟨1017062, by rfl⟩ : syracuseStep 1356083 = 2034125) B2034125
theorem B1356113 : Blo 900574 1356113 := bstep (se 2 (by rfl) ⟨508542, by rfl⟩ : syracuseStep 1356113 = 1017085) B1017085
theorem B1651043 : Blo 900574 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B1356131 : Blo 900574 1356131 := bstep (se 1 (by rfl) ⟨1017098, by rfl⟩ : syracuseStep 1356131 = 2034197) B2034197
theorem B1519985 : Blo 900574 1519985 := bstep (se 2 (by rfl) ⟨569994, by rfl⟩ : syracuseStep 1519985 = 1139989) B1139989
theorem B1356161 : Blo 900574 1356161 := bstep (se 2 (by rfl) ⟨508560, by rfl⟩ : syracuseStep 1356161 = 1017121) B1017121
theorem B1356179 : Blo 900574 1356179 := bstep (se 1 (by rfl) ⟨1017134, by rfl⟩ : syracuseStep 1356179 = 2034269) B2034269
theorem B1716643 : Blo 900574 1716643 := bstep (se 1 (by rfl) ⟨1287482, by rfl⟩ : syracuseStep 1716643 = 2574965) B2574965
theorem B1356209 : Blo 900574 1356209 := bstep (se 2 (by rfl) ⟨508578, by rfl⟩ : syracuseStep 1356209 = 1017157) B1017157
theorem B1356227 : Blo 900574 1356227 := bstep (se 1 (by rfl) ⟨1017170, by rfl⟩ : syracuseStep 1356227 = 2034341) B2034341
theorem B1716689 : Blo 900574 1716689 := bstep (se 2 (by rfl) ⟨643758, by rfl⟩ : syracuseStep 1716689 = 1287517) B1287517
theorem B1356257 : Blo 900574 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B1520113 : Blo 900574 1520113 := bstep (se 2 (by rfl) ⟨570042, by rfl⟩ : syracuseStep 1520113 = 1140085) B1140085
theorem B1356275 : Blo 900574 1356275 := bstep (se 1 (by rfl) ⟨1017206, by rfl⟩ : syracuseStep 1356275 = 2034413) B2034413
theorem B1356305 : Blo 900574 1356305 := bstep (se 2 (by rfl) ⟨508614, by rfl⟩ : syracuseStep 1356305 = 1017229) B1017229
theorem B1520147 : Blo 900574 1520147 := bstep (se 1 (by rfl) ⟨1140110, by rfl⟩ : syracuseStep 1520147 = 2280221) B2280221
theorem B1356323 : Blo 900574 1356323 := bstep (se 1 (by rfl) ⟨1017242, by rfl⟩ : syracuseStep 1356323 = 2034485) B2034485
theorem B1356353 : Blo 900574 1356353 := bstep (se 2 (by rfl) ⟨508632, by rfl⟩ : syracuseStep 1356353 = 1017265) B1017265
theorem B1356371 : Blo 900574 1356371 := bstep (se 1 (by rfl) ⟨1017278, by rfl⟩ : syracuseStep 1356371 = 2034557) B2034557
theorem B1356401 : Blo 900574 1356401 := bstep (se 2 (by rfl) ⟨508650, by rfl⟩ : syracuseStep 1356401 = 1017301) B1017301
theorem B1356419 : Blo 900574 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B3846797 : Blo 900574 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B1520275 : Blo 900574 1520275 := bstep (se 1 (by rfl) ⟨1140206, by rfl⟩ : syracuseStep 1520275 = 2280413) B2280413
theorem B1356449 : Blo 900574 1356449 := bstep (se 2 (by rfl) ⟨508668, by rfl⟩ : syracuseStep 1356449 = 1017337) B1017337
theorem B2437805 : Blo 900574 2437805 := bstep (se 3 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 2437805 = 914177) B914177
theorem B1356467 : Blo 900574 1356467 := bstep (se 1 (by rfl) ⟨1017350, by rfl⟩ : syracuseStep 1356467 = 2034701) B2034701
theorem B1356497 : Blo 900574 1356497 := bstep (se 2 (by rfl) ⟨508686, by rfl⟩ : syracuseStep 1356497 = 1017373) B1017373
theorem B1356515 : Blo 900574 1356515 := bstep (se 1 (by rfl) ⟨1017386, by rfl⟩ : syracuseStep 1356515 = 2034773) B2034773
theorem B1716977 : Blo 900574 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B1356545 : Blo 900574 1356545 := bstep (se 2 (by rfl) ⟨508704, by rfl⟩ : syracuseStep 1356545 = 1017409) B1017409
theorem B4633357 : Blo 900574 4633357 := bstep (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) B1737509
theorem B1356563 : Blo 900574 1356563 := bstep (se 1 (by rfl) ⟨1017422, by rfl⟩ : syracuseStep 1356563 = 2034845) B2034845
theorem B1520417 : Blo 900574 1520417 := bstep (se 2 (by rfl) ⟨570156, by rfl⟩ : syracuseStep 1520417 = 1140313) B1140313
theorem B1356593 : Blo 900574 1356593 := bstep (se 2 (by rfl) ⟨508722, by rfl⟩ : syracuseStep 1356593 = 1017445) B1017445
theorem B1356611 : Blo 900574 1356611 := bstep (se 1 (by rfl) ⟨1017458, by rfl⟩ : syracuseStep 1356611 = 2034917) B2034917
theorem B1356641 : Blo 900574 1356641 := bstep (se 2 (by rfl) ⟨508740, by rfl⟩ : syracuseStep 1356641 = 1017481) B1017481
theorem B1356659 : Blo 900574 1356659 := bstep (se 1 (by rfl) ⟨1017494, by rfl⟩ : syracuseStep 1356659 = 2034989) B2034989
theorem B4109197 : Blo 900574 4109197 := bstep (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) B1540949
theorem B1356689 : Blo 900574 1356689 := bstep (se 2 (by rfl) ⟨508758, by rfl⟩ : syracuseStep 1356689 = 1017517) B1017517
theorem B1520545 : Blo 900574 1520545 := bstep (se 2 (by rfl) ⟨570204, by rfl⟩ : syracuseStep 1520545 = 1140409) B1140409
theorem B1356707 : Blo 900574 1356707 := bstep (se 1 (by rfl) ⟨1017530, by rfl⟩ : syracuseStep 1356707 = 2035061) B2035061
theorem B2569133 : Blo 900574 2569133 := bstep (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) B963425
theorem B1356737 : Blo 900574 1356737 := bstep (se 2 (by rfl) ⟨508776, by rfl⟩ : syracuseStep 1356737 = 1017553) B1017553
theorem B1520579 : Blo 900574 1520579 := bstep (se 1 (by rfl) ⟨1140434, by rfl⟩ : syracuseStep 1520579 = 2280869) B2280869
theorem B1356755 : Blo 900574 1356755 := bstep (se 1 (by rfl) ⟨1017566, by rfl⟩ : syracuseStep 1356755 = 2035133) B2035133
theorem B3847139 : Blo 900574 3847139 := bstep (se 1 (by rfl) ⟨2885354, by rfl⟩ : syracuseStep 3847139 = 5770709) B5770709
theorem B2929645 : Blo 900574 2929645 := bstep (se 3 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 2929645 = 1098617) B1098617
theorem B1356785 : Blo 900574 1356785 := bstep (se 2 (by rfl) ⟨508794, by rfl⟩ : syracuseStep 1356785 = 1017589) B1017589
theorem B1356803 : Blo 900574 1356803 := bstep (se 1 (by rfl) ⟨1017602, by rfl⟩ : syracuseStep 1356803 = 2035205) B2035205
theorem B1356833 : Blo 900574 1356833 := bstep (se 2 (by rfl) ⟨508812, by rfl⟩ : syracuseStep 1356833 = 1017625) B1017625
theorem B1356851 : Blo 900574 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B1520707 : Blo 900574 1520707 := bstep (se 1 (by rfl) ⟨1140530, by rfl⟩ : syracuseStep 1520707 = 2281061) B2281061
theorem B2569315 : Blo 900574 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B2897041 : Blo 900574 2897041 := bstep (se 2 (by rfl) ⟨1086390, by rfl⟩ : syracuseStep 2897041 = 2172781) B2172781
theorem B1520849 : Blo 900574 1520849 := bstep (se 2 (by rfl) ⟨570318, by rfl⟩ : syracuseStep 1520849 = 1140637) B1140637
theorem B2569475 : Blo 900574 2569475 := bstep (se 1 (by rfl) ⟨1927106, by rfl⟩ : syracuseStep 2569475 = 3854213) B3854213
theorem B1520977 : Blo 900574 1520977 := bstep (se 2 (by rfl) ⟨570366, by rfl⟩ : syracuseStep 1520977 = 1140733) B1140733
theorem B1521011 : Blo 900574 1521011 := bstep (se 1 (by rfl) ⟨1140758, by rfl⟩ : syracuseStep 1521011 = 2281517) B2281517
theorem B2897297 : Blo 900574 2897297 := bstep (se 2 (by rfl) ⟨1086486, by rfl⟩ : syracuseStep 2897297 = 2172973) B2172973
theorem B3847601 : Blo 900574 3847601 := bstep (se 2 (by rfl) ⟨1442850, by rfl⟩ : syracuseStep 3847601 = 2885701) B2885701
theorem B964019 : Blo 900574 964019 := bstep (se 1 (by rfl) ⟨723014, by rfl⟩ : syracuseStep 964019 = 1446029) B1446029
theorem B4568561 : Blo 900574 4568561 := bstep (se 2 (by rfl) ⟨1713210, by rfl⟩ : syracuseStep 4568561 = 3426421) B3426421
theorem B1521139 : Blo 900574 1521139 := bstep (se 1 (by rfl) ⟨1140854, by rfl⟩ : syracuseStep 1521139 = 2281709) B2281709
theorem B5781061 : Blo 900574 5781061 := bstep (se 4 (by rfl) ⟨541974, by rfl⟩ : syracuseStep 5781061 = 1083949) B1083949
theorem B1521281 : Blo 900574 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B1521409 : Blo 900574 1521409 := bstep (se 2 (by rfl) ⟨570528, by rfl⟩ : syracuseStep 1521409 = 1141057) B1141057
theorem B1521443 : Blo 900574 1521443 := bstep (se 1 (by rfl) ⟨1141082, by rfl⟩ : syracuseStep 1521443 = 2282165) B2282165
theorem B1521571 : Blo 900574 1521571 := bstep (se 1 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 1521571 = 2282357) B2282357
theorem B10401733 : Blo 900574 10401733 := bstep (se 4 (by rfl) ⟨975162, by rfl⟩ : syracuseStep 10401733 = 1950325) B1950325
theorem B1521713 : Blo 900574 1521713 := bstep (se 2 (by rfl) ⟨570642, by rfl⟩ : syracuseStep 1521713 = 1141285) B1141285
theorem B3422321 : Blo 900574 3422321 := bstep (se 2 (by rfl) ⟨1283370, by rfl⟩ : syracuseStep 3422321 = 2566741) B2566741
theorem B1521841 : Blo 900574 1521841 := bstep (se 2 (by rfl) ⟨570690, by rfl⟩ : syracuseStep 1521841 = 1141381) B1141381
theorem B1521875 : Blo 900574 1521875 := bstep (se 1 (by rfl) ⟨1141406, by rfl⟩ : syracuseStep 1521875 = 2282813) B2282813
theorem B2472241 : Blo 900574 2472241 := bstep (se 2 (by rfl) ⟨927090, by rfl⟩ : syracuseStep 2472241 = 1854181) B1854181
theorem B2570545 : Blo 900574 2570545 := bstep (se 2 (by rfl) ⟨963954, by rfl⟩ : syracuseStep 2570545 = 1927909) B1927909
theorem B4405553 : Blo 900574 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B1522003 : Blo 900574 1522003 := bstep (se 1 (by rfl) ⟨1141502, by rfl⟩ : syracuseStep 1522003 = 2283005) B2283005
theorem B964963 : Blo 900574 964963 := bstep (se 1 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 964963 = 1447445) B1447445
theorem B10041781 : Blo 900574 10041781 := bstep (se 5 (by rfl) ⟨470708, by rfl⟩ : syracuseStep 10041781 = 941417) B941417
theorem B1522145 : Blo 900574 1522145 := bstep (se 2 (by rfl) ⟨570804, by rfl⟩ : syracuseStep 1522145 = 1141609) B1141609
theorem B1522273 : Blo 900574 1522273 := bstep (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) B1141705
theorem B1522307 : Blo 900574 1522307 := bstep (se 1 (by rfl) ⟨1141730, by rfl⟩ : syracuseStep 1522307 = 2283461) B2283461
theorem B11549411 : Blo 900574 11549411 := bstep (se 1 (by rfl) ⟨8662058, by rfl⟩ : syracuseStep 11549411 = 17324117) B17324117
theorem B1522435 : Blo 900574 1522435 := bstep (se 1 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 1522435 = 2283653) B2283653
theorem B1522577 : Blo 900574 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B4570019 : Blo 900574 4570019 := bstep (se 1 (by rfl) ⟨3427514, by rfl⟩ : syracuseStep 4570019 = 6855029) B6855029
theorem B1391555 : Blo 900574 1391555 := bstep (se 1 (by rfl) ⟨1043666, by rfl⟩ : syracuseStep 1391555 = 2087333) B2087333
theorem B1522705 : Blo 900574 1522705 := bstep (se 2 (by rfl) ⟨571014, by rfl⟩ : syracuseStep 1522705 = 1142029) B1142029
theorem B1522739 : Blo 900574 1522739 := bstep (se 1 (by rfl) ⟨1142054, by rfl⟩ : syracuseStep 1522739 = 2284109) B2284109
theorem B1522867 : Blo 900574 1522867 := bstep (se 1 (by rfl) ⟨1142150, by rfl⟩ : syracuseStep 1522867 = 2284301) B2284301
theorem B1981649 : Blo 900574 1981649 := bstep (se 2 (by rfl) ⟨743118, by rfl⟩ : syracuseStep 1981649 = 1486237) B1486237
theorem B1523009 : Blo 900574 1523009 := bstep (se 2 (by rfl) ⟨571128, by rfl⟩ : syracuseStep 1523009 = 1142257) B1142257
theorem B1523137 : Blo 900574 1523137 := bstep (se 2 (by rfl) ⟨571176, by rfl⟩ : syracuseStep 1523137 = 1142353) B1142353
theorem B900579 : Blo 900574 900579 := bstep (se 1 (by rfl) ⟨675434, by rfl⟩ : syracuseStep 900579 = 1350869) B1350869
theorem B1523171 : Blo 900574 1523171 := bstep (se 1 (by rfl) ⟨1142378, by rfl⟩ : syracuseStep 1523171 = 2284757) B2284757
theorem B1883633 : Blo 900574 1883633 := bstep (se 2 (by rfl) ⟨706362, by rfl⟩ : syracuseStep 1883633 = 1412725) B1412725
theorem B900595 : Blo 900574 900595 := bstep (se 1 (by rfl) ⟨675446, by rfl⟩ : syracuseStep 900595 = 1350893) B1350893
theorem B900611 : Blo 900574 900611 := bstep (se 1 (by rfl) ⟨675458, by rfl⟩ : syracuseStep 900611 = 1350917) B1350917
theorem B900627 : Blo 900574 900627 := bstep (se 1 (by rfl) ⟨675470, by rfl⟩ : syracuseStep 900627 = 1350941) B1350941
theorem B900643 : Blo 900574 900643 := bstep (se 1 (by rfl) ⟨675482, by rfl⟩ : syracuseStep 900643 = 1350965) B1350965
theorem B3423779 : Blo 900574 3423779 := bstep (se 1 (by rfl) ⟨2567834, by rfl⟩ : syracuseStep 3423779 = 5135669) B5135669
theorem B2571821 : Blo 900574 2571821 := bstep (se 3 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 2571821 = 964433) B964433
theorem B900659 : Blo 900574 900659 := bstep (se 1 (by rfl) ⟨675494, by rfl⟩ : syracuseStep 900659 = 1350989) B1350989
theorem B900675 : Blo 900574 900675 := bstep (se 1 (by rfl) ⟨675506, by rfl⟩ : syracuseStep 900675 = 1351013) B1351013
theorem B900691 : Blo 900574 900691 := bstep (se 1 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 900691 = 1351037) B1351037
theorem B900707 : Blo 900574 900707 := bstep (se 1 (by rfl) ⟨675530, by rfl⟩ : syracuseStep 900707 = 1351061) B1351061
theorem B1523299 : Blo 900574 1523299 := bstep (se 1 (by rfl) ⟨1142474, by rfl⟩ : syracuseStep 1523299 = 2284949) B2284949
theorem B2440813 : Blo 900574 2440813 := bstep (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) B915305
theorem B900723 : Blo 900574 900723 := bstep (se 1 (by rfl) ⟨675542, by rfl⟩ : syracuseStep 900723 = 1351085) B1351085
theorem B900739 : Blo 900574 900739 := bstep (se 1 (by rfl) ⟨675554, by rfl⟩ : syracuseStep 900739 = 1351109) B1351109
theorem B900755 : Blo 900574 900755 := bstep (se 1 (by rfl) ⟨675566, by rfl⟩ : syracuseStep 900755 = 1351133) B1351133
theorem B900771 : Blo 900574 900771 := bstep (se 1 (by rfl) ⟨675578, by rfl⟩ : syracuseStep 900771 = 1351157) B1351157
theorem B2440867 : Blo 900574 2440867 := bstep (se 1 (by rfl) ⟨1830650, by rfl⟩ : syracuseStep 2440867 = 3661301) B3661301
theorem B900787 : Blo 900574 900787 := bstep (se 1 (by rfl) ⟨675590, by rfl⟩ : syracuseStep 900787 = 1351181) B1351181
theorem B900803 : Blo 900574 900803 := bstep (se 1 (by rfl) ⟨675602, by rfl⟩ : syracuseStep 900803 = 1351205) B1351205
theorem B4570829 : Blo 900574 4570829 := bstep (se 3 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 4570829 = 1714061) B1714061
theorem B900819 : Blo 900574 900819 := bstep (se 1 (by rfl) ⟨675614, by rfl⟩ : syracuseStep 900819 = 1351229) B1351229
theorem B2572003 : Blo 900574 2572003 := bstep (se 1 (by rfl) ⟨1929002, by rfl⟩ : syracuseStep 2572003 = 3858005) B3858005
theorem B900835 : Blo 900574 900835 := bstep (se 1 (by rfl) ⟨675626, by rfl⟩ : syracuseStep 900835 = 1351253) B1351253
theorem B1523441 : Blo 900574 1523441 := bstep (se 2 (by rfl) ⟨571290, by rfl⟩ : syracuseStep 1523441 = 1142581) B1142581
theorem B900851 : Blo 900574 900851 := bstep (se 1 (by rfl) ⟨675638, by rfl⟩ : syracuseStep 900851 = 1351277) B1351277
theorem B900867 : Blo 900574 900867 := bstep (se 1 (by rfl) ⟨675650, by rfl⟩ : syracuseStep 900867 = 1351301) B1351301
theorem B2572049 : Blo 900574 2572049 := bstep (se 2 (by rfl) ⟨964518, by rfl⟩ : syracuseStep 2572049 = 1929037) B1929037
theorem B900883 : Blo 900574 900883 := bstep (se 1 (by rfl) ⟨675662, by rfl⟩ : syracuseStep 900883 = 1351325) B1351325
theorem B900899 : Blo 900574 900899 := bstep (se 1 (by rfl) ⟨675674, by rfl⟩ : syracuseStep 900899 = 1351349) B1351349
theorem B900915 : Blo 900574 900915 := bstep (se 1 (by rfl) ⟨675686, by rfl⟩ : syracuseStep 900915 = 1351373) B1351373
theorem B900931 : Blo 900574 900931 := bstep (se 1 (by rfl) ⟨675698, by rfl⟩ : syracuseStep 900931 = 1351397) B1351397
theorem B900947 : Blo 900574 900947 := bstep (se 1 (by rfl) ⟨675710, by rfl⟩ : syracuseStep 900947 = 1351421) B1351421
theorem B900963 : Blo 900574 900963 := bstep (se 1 (by rfl) ⟨675722, by rfl⟩ : syracuseStep 900963 = 1351445) B1351445
theorem B1523569 : Blo 900574 1523569 := bstep (se 2 (by rfl) ⟨571338, by rfl⟩ : syracuseStep 1523569 = 1142677) B1142677
theorem B900979 : Blo 900574 900979 := bstep (se 1 (by rfl) ⟨675734, by rfl⟩ : syracuseStep 900979 = 1351469) B1351469
theorem B900995 : Blo 900574 900995 := bstep (se 1 (by rfl) ⟨675746, by rfl⟩ : syracuseStep 900995 = 1351493) B1351493
theorem B901011 : Blo 900574 901011 := bstep (se 1 (by rfl) ⟨675758, by rfl⟩ : syracuseStep 901011 = 1351517) B1351517
theorem B1523603 : Blo 900574 1523603 := bstep (se 1 (by rfl) ⟨1142702, by rfl⟩ : syracuseStep 1523603 = 2285405) B2285405
theorem B901027 : Blo 900574 901027 := bstep (se 1 (by rfl) ⟨675770, by rfl⟩ : syracuseStep 901027 = 1351541) B1351541
theorem B901043 : Blo 900574 901043 := bstep (se 1 (by rfl) ⟨675782, by rfl⟩ : syracuseStep 901043 = 1351565) B1351565
theorem B901059 : Blo 900574 901059 := bstep (se 1 (by rfl) ⟨675794, by rfl⟩ : syracuseStep 901059 = 1351589) B1351589
theorem B901075 : Blo 900574 901075 := bstep (se 1 (by rfl) ⟨675806, by rfl⟩ : syracuseStep 901075 = 1351613) B1351613
theorem B901091 : Blo 900574 901091 := bstep (se 1 (by rfl) ⟨675818, by rfl⟩ : syracuseStep 901091 = 1351637) B1351637
theorem B9748451 : Blo 900574 9748451 := bstep (se 1 (by rfl) ⟨7311338, by rfl⟩ : syracuseStep 9748451 = 14622677) B14622677
theorem B901107 : Blo 900574 901107 := bstep (se 1 (by rfl) ⟨675830, by rfl⟩ : syracuseStep 901107 = 1351661) B1351661
theorem B901123 : Blo 900574 901123 := bstep (se 1 (by rfl) ⟨675842, by rfl⟩ : syracuseStep 901123 = 1351685) B1351685
theorem B901139 : Blo 900574 901139 := bstep (se 1 (by rfl) ⟨675854, by rfl⟩ : syracuseStep 901139 = 1351709) B1351709
theorem B1523731 : Blo 900574 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B901155 : Blo 900574 901155 := bstep (se 1 (by rfl) ⟨675866, by rfl⟩ : syracuseStep 901155 = 1351733) B1351733
theorem B901171 : Blo 900574 901171 := bstep (se 1 (by rfl) ⟨675878, by rfl⟩ : syracuseStep 901171 = 1351757) B1351757
theorem B901187 : Blo 900574 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B901203 : Blo 900574 901203 := bstep (se 1 (by rfl) ⟨675902, by rfl⟩ : syracuseStep 901203 = 1351805) B1351805
theorem B901219 : Blo 900574 901219 := bstep (se 1 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 901219 = 1351829) B1351829
theorem B24658033 : Blo 900574 24658033 := bstep (se 2 (by rfl) ⟨9246762, by rfl⟩ : syracuseStep 24658033 = 18493525) B18493525
theorem B901235 : Blo 900574 901235 := bstep (se 1 (by rfl) ⟨675926, by rfl⟩ : syracuseStep 901235 = 1351853) B1351853
theorem B901251 : Blo 900574 901251 := bstep (se 1 (by rfl) ⟨675938, by rfl⟩ : syracuseStep 901251 = 1351877) B1351877
theorem B9748621 : Blo 900574 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B901267 : Blo 900574 901267 := bstep (se 1 (by rfl) ⟨675950, by rfl⟩ : syracuseStep 901267 = 1351901) B1351901
theorem B1523873 : Blo 900574 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B901283 : Blo 900574 901283 := bstep (se 1 (by rfl) ⟨675962, by rfl⟩ : syracuseStep 901283 = 1351925) B1351925
theorem B901299 : Blo 900574 901299 := bstep (se 1 (by rfl) ⟨675974, by rfl⟩ : syracuseStep 901299 = 1351949) B1351949
theorem B901315 : Blo 900574 901315 := bstep (se 1 (by rfl) ⟨675986, by rfl⟩ : syracuseStep 901315 = 1351973) B1351973
theorem B901331 : Blo 900574 901331 := bstep (se 1 (by rfl) ⟨675998, by rfl⟩ : syracuseStep 901331 = 1351997) B1351997
theorem B901347 : Blo 900574 901347 := bstep (se 1 (by rfl) ⟨676010, by rfl⟩ : syracuseStep 901347 = 1352021) B1352021
theorem B901363 : Blo 900574 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B901379 : Blo 900574 901379 := bstep (se 1 (by rfl) ⟨676034, by rfl⟩ : syracuseStep 901379 = 1352069) B1352069
theorem B901395 : Blo 900574 901395 := bstep (se 1 (by rfl) ⟨676046, by rfl⟩ : syracuseStep 901395 = 1352093) B1352093
theorem B1524001 : Blo 900574 1524001 := bstep (se 2 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 1524001 = 1143001) B1143001
theorem B901411 : Blo 900574 901411 := bstep (se 1 (by rfl) ⟨676058, by rfl⟩ : syracuseStep 901411 = 1352117) B1352117
theorem B901427 : Blo 900574 901427 := bstep (se 1 (by rfl) ⟨676070, by rfl⟩ : syracuseStep 901427 = 1352141) B1352141
theorem B901443 : Blo 900574 901443 := bstep (se 1 (by rfl) ⟨676082, by rfl⟩ : syracuseStep 901443 = 1352165) B1352165
theorem B1524035 : Blo 900574 1524035 := bstep (se 1 (by rfl) ⟨1143026, by rfl⟩ : syracuseStep 1524035 = 2286053) B2286053
theorem B901459 : Blo 900574 901459 := bstep (se 1 (by rfl) ⟨676094, by rfl⟩ : syracuseStep 901459 = 1352189) B1352189
theorem B901475 : Blo 900574 901475 := bstep (se 1 (by rfl) ⟨676106, by rfl⟩ : syracuseStep 901475 = 1352213) B1352213
theorem B901491 : Blo 900574 901491 := bstep (se 1 (by rfl) ⟨676118, by rfl⟩ : syracuseStep 901491 = 1352237) B1352237
theorem B901507 : Blo 900574 901507 := bstep (se 1 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 901507 = 1352261) B1352261
theorem B901523 : Blo 900574 901523 := bstep (se 1 (by rfl) ⟨676142, by rfl⟩ : syracuseStep 901523 = 1352285) B1352285
theorem B901539 : Blo 900574 901539 := bstep (se 1 (by rfl) ⟨676154, by rfl⟩ : syracuseStep 901539 = 1352309) B1352309
theorem B901555 : Blo 900574 901555 := bstep (se 1 (by rfl) ⟨676166, by rfl⟩ : syracuseStep 901555 = 1352333) B1352333
theorem B901571 : Blo 900574 901571 := bstep (se 1 (by rfl) ⟨676178, by rfl⟩ : syracuseStep 901571 = 1352357) B1352357
theorem B1524163 : Blo 900574 1524163 := bstep (se 1 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 1524163 = 2286245) B2286245
theorem B901587 : Blo 900574 901587 := bstep (se 1 (by rfl) ⟨676190, by rfl⟩ : syracuseStep 901587 = 1352381) B1352381
theorem B901603 : Blo 900574 901603 := bstep (se 1 (by rfl) ⟨676202, by rfl⟩ : syracuseStep 901603 = 1352405) B1352405
theorem B901619 : Blo 900574 901619 := bstep (se 1 (by rfl) ⟨676214, by rfl⟩ : syracuseStep 901619 = 1352429) B1352429
theorem B901635 : Blo 900574 901635 := bstep (se 1 (by rfl) ⟨676226, by rfl⟩ : syracuseStep 901635 = 1352453) B1352453
theorem B3424781 : Blo 900574 3424781 := bstep (se 3 (by rfl) ⟨642146, by rfl⟩ : syracuseStep 3424781 = 1284293) B1284293
theorem B901651 : Blo 900574 901651 := bstep (se 1 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 901651 = 1352477) B1352477
theorem B3654179 : Blo 900574 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B901667 : Blo 900574 901667 := bstep (se 1 (by rfl) ⟨676250, by rfl⟩ : syracuseStep 901667 = 1352501) B1352501
theorem B901683 : Blo 900574 901683 := bstep (se 1 (by rfl) ⟨676262, by rfl⟩ : syracuseStep 901683 = 1352525) B1352525
theorem B901699 : Blo 900574 901699 := bstep (se 1 (by rfl) ⟨676274, by rfl⟩ : syracuseStep 901699 = 1352549) B1352549
theorem B1524305 : Blo 900574 1524305 := bstep (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) B1143229
theorem B901715 : Blo 900574 901715 := bstep (se 1 (by rfl) ⟨676286, by rfl⟩ : syracuseStep 901715 = 1352573) B1352573
theorem B901731 : Blo 900574 901731 := bstep (se 1 (by rfl) ⟨676298, by rfl⟩ : syracuseStep 901731 = 1352597) B1352597
theorem B4637297 : Blo 900574 4637297 := bstep (se 2 (by rfl) ⟨1738986, by rfl⟩ : syracuseStep 4637297 = 3477973) B3477973
theorem B901747 : Blo 900574 901747 := bstep (se 1 (by rfl) ⟨676310, by rfl⟩ : syracuseStep 901747 = 1352621) B1352621
theorem B901763 : Blo 900574 901763 := bstep (se 1 (by rfl) ⟨676322, by rfl⟩ : syracuseStep 901763 = 1352645) B1352645
theorem B901779 : Blo 900574 901779 := bstep (se 1 (by rfl) ⟨676334, by rfl⟩ : syracuseStep 901779 = 1352669) B1352669
theorem B901795 : Blo 900574 901795 := bstep (se 1 (by rfl) ⟨676346, by rfl⟩ : syracuseStep 901795 = 1352693) B1352693
theorem B2933425 : Blo 900574 2933425 := bstep (se 2 (by rfl) ⟨1100034, by rfl⟩ : syracuseStep 2933425 = 2200069) B2200069
theorem B901811 : Blo 900574 901811 := bstep (se 1 (by rfl) ⟨676358, by rfl⟩ : syracuseStep 901811 = 1352717) B1352717
theorem B2310851 : Blo 900574 2310851 := bstep (se 1 (by rfl) ⟨1733138, by rfl⟩ : syracuseStep 2310851 = 3466277) B3466277
theorem B901827 : Blo 900574 901827 := bstep (se 1 (by rfl) ⟨676370, by rfl⟩ : syracuseStep 901827 = 1352741) B1352741
theorem B6177485 : Blo 900574 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B1524433 : Blo 900574 1524433 := bstep (se 2 (by rfl) ⟨571662, by rfl⟩ : syracuseStep 1524433 = 1143325) B1143325
theorem B901843 : Blo 900574 901843 := bstep (se 1 (by rfl) ⟨676382, by rfl⟩ : syracuseStep 901843 = 1352765) B1352765
theorem B901859 : Blo 900574 901859 := bstep (se 1 (by rfl) ⟨676394, by rfl⟩ : syracuseStep 901859 = 1352789) B1352789
theorem B901875 : Blo 900574 901875 := bstep (se 1 (by rfl) ⟨676406, by rfl⟩ : syracuseStep 901875 = 1352813) B1352813
theorem B1524467 : Blo 900574 1524467 := bstep (se 1 (by rfl) ⟨1143350, by rfl⟩ : syracuseStep 1524467 = 2286701) B2286701
theorem B901891 : Blo 900574 901891 := bstep (se 1 (by rfl) ⟨676418, by rfl⟩ : syracuseStep 901891 = 1352837) B1352837
theorem B901907 : Blo 900574 901907 := bstep (se 1 (by rfl) ⟨676430, by rfl⟩ : syracuseStep 901907 = 1352861) B1352861
theorem B901923 : Blo 900574 901923 := bstep (se 1 (by rfl) ⟨676442, by rfl⟩ : syracuseStep 901923 = 1352885) B1352885
theorem B901939 : Blo 900574 901939 := bstep (se 1 (by rfl) ⟨676454, by rfl⟩ : syracuseStep 901939 = 1352909) B1352909
theorem B901955 : Blo 900574 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B901971 : Blo 900574 901971 := bstep (se 1 (by rfl) ⟨676478, by rfl⟩ : syracuseStep 901971 = 1352957) B1352957
theorem B901987 : Blo 900574 901987 := bstep (se 1 (by rfl) ⟨676490, by rfl⟩ : syracuseStep 901987 = 1352981) B1352981
theorem B1622897 : Blo 900574 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B902003 : Blo 900574 902003 := bstep (se 1 (by rfl) ⟨676502, by rfl⟩ : syracuseStep 902003 = 1353005) B1353005
theorem B1524595 : Blo 900574 1524595 := bstep (se 1 (by rfl) ⟨1143446, by rfl⟩ : syracuseStep 1524595 = 2286893) B2286893
theorem B902019 : Blo 900574 902019 := bstep (se 1 (by rfl) ⟨676514, by rfl⟩ : syracuseStep 902019 = 1353029) B1353029
theorem B902035 : Blo 900574 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B3851171 : Blo 900574 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B902051 : Blo 900574 902051 := bstep (se 1 (by rfl) ⟨676538, by rfl⟩ : syracuseStep 902051 = 1353077) B1353077
theorem B902067 : Blo 900574 902067 := bstep (se 1 (by rfl) ⟨676550, by rfl⟩ : syracuseStep 902067 = 1353101) B1353101
theorem B902083 : Blo 900574 902083 := bstep (se 1 (by rfl) ⟨676562, by rfl⟩ : syracuseStep 902083 = 1353125) B1353125
theorem B902099 : Blo 900574 902099 := bstep (se 1 (by rfl) ⟨676574, by rfl⟩ : syracuseStep 902099 = 1353149) B1353149
theorem B902115 : Blo 900574 902115 := bstep (se 1 (by rfl) ⟨676586, by rfl⟩ : syracuseStep 902115 = 1353173) B1353173
theorem B5784547 : Blo 900574 5784547 := bstep (se 1 (by rfl) ⟨4338410, by rfl⟩ : syracuseStep 5784547 = 8676821) B8676821
theorem B902131 : Blo 900574 902131 := bstep (se 1 (by rfl) ⟨676598, by rfl⟩ : syracuseStep 902131 = 1353197) B1353197
theorem B1524737 : Blo 900574 1524737 := bstep (se 2 (by rfl) ⟨571776, by rfl⟩ : syracuseStep 1524737 = 1143553) B1143553
theorem B902147 : Blo 900574 902147 := bstep (se 1 (by rfl) ⟨676610, by rfl⟩ : syracuseStep 902147 = 1353221) B1353221
theorem B902163 : Blo 900574 902163 := bstep (se 1 (by rfl) ⟨676622, by rfl⟩ : syracuseStep 902163 = 1353245) B1353245
theorem B902179 : Blo 900574 902179 := bstep (se 1 (by rfl) ⟨676634, by rfl⟩ : syracuseStep 902179 = 1353269) B1353269
theorem B902195 : Blo 900574 902195 := bstep (se 1 (by rfl) ⟨676646, by rfl⟩ : syracuseStep 902195 = 1353293) B1353293
theorem B902211 : Blo 900574 902211 := bstep (se 1 (by rfl) ⟨676658, by rfl⟩ : syracuseStep 902211 = 1353317) B1353317
theorem B6505541 : Blo 900574 6505541 := bstep (se 4 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 6505541 = 1219789) B1219789
theorem B902227 : Blo 900574 902227 := bstep (se 1 (by rfl) ⟨676670, by rfl⟩ : syracuseStep 902227 = 1353341) B1353341
theorem B902243 : Blo 900574 902243 := bstep (se 1 (by rfl) ⟨676682, by rfl⟩ : syracuseStep 902243 = 1353365) B1353365
theorem B902259 : Blo 900574 902259 := bstep (se 1 (by rfl) ⟨676694, by rfl⟩ : syracuseStep 902259 = 1353389) B1353389
theorem B1524865 : Blo 900574 1524865 := bstep (se 2 (by rfl) ⟨571824, by rfl⟩ : syracuseStep 1524865 = 1143649) B1143649
theorem B902275 : Blo 900574 902275 := bstep (se 1 (by rfl) ⟨676706, by rfl⟩ : syracuseStep 902275 = 1353413) B1353413
theorem B902291 : Blo 900574 902291 := bstep (se 1 (by rfl) ⟨676718, by rfl⟩ : syracuseStep 902291 = 1353437) B1353437
theorem B902307 : Blo 900574 902307 := bstep (se 1 (by rfl) ⟨676730, by rfl⟩ : syracuseStep 902307 = 1353461) B1353461
theorem B1524899 : Blo 900574 1524899 := bstep (se 1 (by rfl) ⟨1143674, by rfl⟩ : syracuseStep 1524899 = 2287349) B2287349
theorem B902323 : Blo 900574 902323 := bstep (se 1 (by rfl) ⟨676742, by rfl⟩ : syracuseStep 902323 = 1353485) B1353485
theorem B902339 : Blo 900574 902339 := bstep (se 1 (by rfl) ⟨676754, by rfl⟩ : syracuseStep 902339 = 1353509) B1353509
theorem B2573507 : Blo 900574 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B902355 : Blo 900574 902355 := bstep (se 1 (by rfl) ⟨676766, by rfl⟩ : syracuseStep 902355 = 1353533) B1353533
theorem B902371 : Blo 900574 902371 := bstep (se 1 (by rfl) ⟨676778, by rfl⟩ : syracuseStep 902371 = 1353557) B1353557
theorem B902387 : Blo 900574 902387 := bstep (se 1 (by rfl) ⟨676790, by rfl⟩ : syracuseStep 902387 = 1353581) B1353581
theorem B1950979 : Blo 900574 1950979 := bstep (se 1 (by rfl) ⟨1463234, by rfl⟩ : syracuseStep 1950979 = 2926469) B2926469
theorem B902403 : Blo 900574 902403 := bstep (se 1 (by rfl) ⟨676802, by rfl⟩ : syracuseStep 902403 = 1353605) B1353605
theorem B11584781 : Blo 900574 11584781 := bstep (se 3 (by rfl) ⟨2172146, by rfl⟩ : syracuseStep 11584781 = 4344293) B4344293
theorem B902419 : Blo 900574 902419 := bstep (se 1 (by rfl) ⟨676814, by rfl⟩ : syracuseStep 902419 = 1353629) B1353629
theorem B902435 : Blo 900574 902435 := bstep (se 1 (by rfl) ⟨676826, by rfl⟩ : syracuseStep 902435 = 1353653) B1353653
theorem B1525027 : Blo 900574 1525027 := bstep (se 1 (by rfl) ⟨1143770, by rfl⟩ : syracuseStep 1525027 = 2287541) B2287541
theorem B902451 : Blo 900574 902451 := bstep (se 1 (by rfl) ⟨676838, by rfl⟩ : syracuseStep 902451 = 1353677) B1353677
theorem B902467 : Blo 900574 902467 := bstep (se 1 (by rfl) ⟨676850, by rfl⟩ : syracuseStep 902467 = 1353701) B1353701
theorem B902483 : Blo 900574 902483 := bstep (se 1 (by rfl) ⟨676862, by rfl⟩ : syracuseStep 902483 = 1353725) B1353725
theorem B902499 : Blo 900574 902499 := bstep (se 1 (by rfl) ⟨676874, by rfl⟩ : syracuseStep 902499 = 1353749) B1353749
theorem B902515 : Blo 900574 902515 := bstep (se 1 (by rfl) ⟨676886, by rfl⟩ : syracuseStep 902515 = 1353773) B1353773
theorem B902531 : Blo 900574 902531 := bstep (se 1 (by rfl) ⟨676898, by rfl⟩ : syracuseStep 902531 = 1353797) B1353797
theorem B902547 : Blo 900574 902547 := bstep (se 1 (by rfl) ⟨676910, by rfl⟩ : syracuseStep 902547 = 1353821) B1353821
theorem B902563 : Blo 900574 902563 := bstep (se 1 (by rfl) ⟨676922, by rfl⟩ : syracuseStep 902563 = 1353845) B1353845
theorem B1525169 : Blo 900574 1525169 := bstep (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) B1143877
theorem B902579 : Blo 900574 902579 := bstep (se 1 (by rfl) ⟨676934, by rfl⟩ : syracuseStep 902579 = 1353869) B1353869
theorem B12371381 : Blo 900574 12371381 := bstep (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) B1159817
theorem B902595 : Blo 900574 902595 := bstep (se 1 (by rfl) ⟨676946, by rfl⟩ : syracuseStep 902595 = 1353893) B1353893
theorem B902611 : Blo 900574 902611 := bstep (se 1 (by rfl) ⟨676958, by rfl⟩ : syracuseStep 902611 = 1353917) B1353917
theorem B902627 : Blo 900574 902627 := bstep (se 1 (by rfl) ⟨676970, by rfl⟩ : syracuseStep 902627 = 1353941) B1353941
theorem B902643 : Blo 900574 902643 := bstep (se 1 (by rfl) ⟨676982, by rfl⟩ : syracuseStep 902643 = 1353965) B1353965
theorem B902659 : Blo 900574 902659 := bstep (se 1 (by rfl) ⟨676994, by rfl⟩ : syracuseStep 902659 = 1353989) B1353989
theorem B902675 : Blo 900574 902675 := bstep (se 1 (by rfl) ⟨677006, by rfl⟩ : syracuseStep 902675 = 1354013) B1354013
theorem B902691 : Blo 900574 902691 := bstep (se 1 (by rfl) ⟨677018, by rfl⟩ : syracuseStep 902691 = 1354037) B1354037
theorem B1525297 : Blo 900574 1525297 := bstep (se 2 (by rfl) ⟨571986, by rfl⟩ : syracuseStep 1525297 = 1143973) B1143973
theorem B902707 : Blo 900574 902707 := bstep (se 1 (by rfl) ⟨677030, by rfl⟩ : syracuseStep 902707 = 1354061) B1354061
theorem B902723 : Blo 900574 902723 := bstep (se 1 (by rfl) ⟨677042, by rfl⟩ : syracuseStep 902723 = 1354085) B1354085
theorem B902739 : Blo 900574 902739 := bstep (se 1 (by rfl) ⟨677054, by rfl⟩ : syracuseStep 902739 = 1354109) B1354109
theorem B1525331 : Blo 900574 1525331 := bstep (se 1 (by rfl) ⟨1143998, by rfl⟩ : syracuseStep 1525331 = 2287997) B2287997
theorem B902755 : Blo 900574 902755 := bstep (se 1 (by rfl) ⟨677066, by rfl⟩ : syracuseStep 902755 = 1354133) B1354133
theorem B902771 : Blo 900574 902771 := bstep (se 1 (by rfl) ⟨677078, by rfl⟩ : syracuseStep 902771 = 1354157) B1354157
theorem B902787 : Blo 900574 902787 := bstep (se 1 (by rfl) ⟨677090, by rfl⟩ : syracuseStep 902787 = 1354181) B1354181
theorem B902803 : Blo 900574 902803 := bstep (se 1 (by rfl) ⟨677102, by rfl⟩ : syracuseStep 902803 = 1354205) B1354205
theorem B902819 : Blo 900574 902819 := bstep (se 1 (by rfl) ⟨677114, by rfl⟩ : syracuseStep 902819 = 1354229) B1354229
theorem B902835 : Blo 900574 902835 := bstep (se 1 (by rfl) ⟨677126, by rfl⟩ : syracuseStep 902835 = 1354253) B1354253
theorem B902851 : Blo 900574 902851 := bstep (se 1 (by rfl) ⟨677138, by rfl⟩ : syracuseStep 902851 = 1354277) B1354277
theorem B902867 : Blo 900574 902867 := bstep (se 1 (by rfl) ⟨677150, by rfl⟩ : syracuseStep 902867 = 1354301) B1354301
theorem B1525459 : Blo 900574 1525459 := bstep (se 1 (by rfl) ⟨1144094, by rfl⟩ : syracuseStep 1525459 = 2288189) B2288189
theorem B7128803 : Blo 900574 7128803 := bstep (se 1 (by rfl) ⟨5346602, by rfl⟩ : syracuseStep 7128803 = 10693205) B10693205
theorem B902883 : Blo 900574 902883 := bstep (se 1 (by rfl) ⟨677162, by rfl⟩ : syracuseStep 902883 = 1354325) B1354325
theorem B902899 : Blo 900574 902899 := bstep (se 1 (by rfl) ⟨677174, by rfl⟩ : syracuseStep 902899 = 1354349) B1354349
theorem B902915 : Blo 900574 902915 := bstep (se 1 (by rfl) ⟨677186, by rfl⟩ : syracuseStep 902915 = 1354373) B1354373
theorem B902931 : Blo 900574 902931 := bstep (se 1 (by rfl) ⟨677198, by rfl⟩ : syracuseStep 902931 = 1354397) B1354397
theorem B902947 : Blo 900574 902947 := bstep (se 1 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 902947 = 1354421) B1354421
theorem B902963 : Blo 900574 902963 := bstep (se 1 (by rfl) ⟨677222, by rfl⟩ : syracuseStep 902963 = 1354445) B1354445
theorem B902979 : Blo 900574 902979 := bstep (se 1 (by rfl) ⟨677234, by rfl⟩ : syracuseStep 902979 = 1354469) B1354469
theorem B902995 : Blo 900574 902995 := bstep (se 1 (by rfl) ⟨677246, by rfl⟩ : syracuseStep 902995 = 1354493) B1354493
theorem B1525601 : Blo 900574 1525601 := bstep (se 2 (by rfl) ⟨572100, by rfl⟩ : syracuseStep 1525601 = 1144201) B1144201
theorem B903011 : Blo 900574 903011 := bstep (se 1 (by rfl) ⟨677258, by rfl⟩ : syracuseStep 903011 = 1354517) B1354517
theorem B903027 : Blo 900574 903027 := bstep (se 1 (by rfl) ⟨677270, by rfl⟩ : syracuseStep 903027 = 1354541) B1354541
theorem B903043 : Blo 900574 903043 := bstep (se 1 (by rfl) ⟨677282, by rfl⟩ : syracuseStep 903043 = 1354565) B1354565
theorem B903059 : Blo 900574 903059 := bstep (se 1 (by rfl) ⟨677294, by rfl⟩ : syracuseStep 903059 = 1354589) B1354589
theorem B903075 : Blo 900574 903075 := bstep (se 1 (by rfl) ⟨677306, by rfl⟩ : syracuseStep 903075 = 1354613) B1354613
theorem B903091 : Blo 900574 903091 := bstep (se 1 (by rfl) ⟨677318, by rfl⟩ : syracuseStep 903091 = 1354637) B1354637
theorem B903107 : Blo 900574 903107 := bstep (se 1 (by rfl) ⟨677330, by rfl⟩ : syracuseStep 903107 = 1354661) B1354661
theorem B903123 : Blo 900574 903123 := bstep (se 1 (by rfl) ⟨677342, by rfl⟩ : syracuseStep 903123 = 1354685) B1354685
theorem B903139 : Blo 900574 903139 := bstep (se 1 (by rfl) ⟨677354, by rfl⟩ : syracuseStep 903139 = 1354709) B1354709
theorem B1525729 : Blo 900574 1525729 := bstep (se 2 (by rfl) ⟨572148, by rfl⟩ : syracuseStep 1525729 = 1144297) B1144297
theorem B903155 : Blo 900574 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B903171 : Blo 900574 903171 := bstep (se 1 (by rfl) ⟨677378, by rfl⟩ : syracuseStep 903171 = 1354757) B1354757
theorem B1525763 : Blo 900574 1525763 := bstep (se 1 (by rfl) ⟨1144322, by rfl⟩ : syracuseStep 1525763 = 2288645) B2288645
theorem B903187 : Blo 900574 903187 := bstep (se 1 (by rfl) ⟨677390, by rfl⟩ : syracuseStep 903187 = 1354781) B1354781
theorem B903203 : Blo 900574 903203 := bstep (se 1 (by rfl) ⟨677402, by rfl⟩ : syracuseStep 903203 = 1354805) B1354805
theorem B903219 : Blo 900574 903219 := bstep (se 1 (by rfl) ⟨677414, by rfl⟩ : syracuseStep 903219 = 1354829) B1354829
theorem B903235 : Blo 900574 903235 := bstep (se 1 (by rfl) ⟨677426, by rfl⟩ : syracuseStep 903235 = 1354853) B1354853
theorem B903251 : Blo 900574 903251 := bstep (se 1 (by rfl) ⟨677438, by rfl⟩ : syracuseStep 903251 = 1354877) B1354877
theorem B903267 : Blo 900574 903267 := bstep (se 1 (by rfl) ⟨677450, by rfl⟩ : syracuseStep 903267 = 1354901) B1354901
theorem B903283 : Blo 900574 903283 := bstep (se 1 (by rfl) ⟨677462, by rfl⟩ : syracuseStep 903283 = 1354925) B1354925
theorem B903299 : Blo 900574 903299 := bstep (se 1 (by rfl) ⟨677474, by rfl⟩ : syracuseStep 903299 = 1354949) B1354949
theorem B1525891 : Blo 900574 1525891 := bstep (se 1 (by rfl) ⟨1144418, by rfl⟩ : syracuseStep 1525891 = 2288837) B2288837
theorem B903315 : Blo 900574 903315 := bstep (se 1 (by rfl) ⟨677486, by rfl⟩ : syracuseStep 903315 = 1354973) B1354973
theorem B903331 : Blo 900574 903331 := bstep (se 1 (by rfl) ⟨677498, by rfl⟩ : syracuseStep 903331 = 1354997) B1354997
theorem B903347 : Blo 900574 903347 := bstep (se 1 (by rfl) ⟨677510, by rfl⟩ : syracuseStep 903347 = 1355021) B1355021
theorem B903363 : Blo 900574 903363 := bstep (se 1 (by rfl) ⟨677522, by rfl⟩ : syracuseStep 903363 = 1355045) B1355045
theorem B903379 : Blo 900574 903379 := bstep (se 1 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 903379 = 1355069) B1355069
theorem B903395 : Blo 900574 903395 := bstep (se 1 (by rfl) ⟨677546, by rfl⟩ : syracuseStep 903395 = 1355093) B1355093
theorem B903411 : Blo 900574 903411 := bstep (se 1 (by rfl) ⟨677558, by rfl⟩ : syracuseStep 903411 = 1355117) B1355117
theorem B903427 : Blo 900574 903427 := bstep (se 1 (by rfl) ⟨677570, by rfl⟩ : syracuseStep 903427 = 1355141) B1355141
theorem B1526033 : Blo 900574 1526033 := bstep (se 2 (by rfl) ⟨572262, by rfl⟩ : syracuseStep 1526033 = 1144525) B1144525
theorem B903443 : Blo 900574 903443 := bstep (se 1 (by rfl) ⟨677582, by rfl⟩ : syracuseStep 903443 = 1355165) B1355165
theorem B903459 : Blo 900574 903459 := bstep (se 1 (by rfl) ⟨677594, by rfl⟩ : syracuseStep 903459 = 1355189) B1355189
theorem B903475 : Blo 900574 903475 := bstep (se 1 (by rfl) ⟨677606, by rfl⟩ : syracuseStep 903475 = 1355213) B1355213
theorem B903491 : Blo 900574 903491 := bstep (se 1 (by rfl) ⟨677618, by rfl⟩ : syracuseStep 903491 = 1355237) B1355237
theorem B903507 : Blo 900574 903507 := bstep (se 1 (by rfl) ⟨677630, by rfl⟩ : syracuseStep 903507 = 1355261) B1355261
theorem B903523 : Blo 900574 903523 := bstep (se 1 (by rfl) ⟨677642, by rfl⟩ : syracuseStep 903523 = 1355285) B1355285
theorem B903539 : Blo 900574 903539 := bstep (se 1 (by rfl) ⟨677654, by rfl⟩ : syracuseStep 903539 = 1355309) B1355309
theorem B903555 : Blo 900574 903555 := bstep (se 1 (by rfl) ⟨677666, by rfl⟩ : syracuseStep 903555 = 1355333) B1355333
theorem B2574737 : Blo 900574 2574737 := bstep (se 2 (by rfl) ⟨965526, by rfl⟩ : syracuseStep 2574737 = 1931053) B1931053
theorem B1526161 : Blo 900574 1526161 := bstep (se 2 (by rfl) ⟨572310, by rfl⟩ : syracuseStep 1526161 = 1144621) B1144621
theorem B903571 : Blo 900574 903571 := bstep (se 1 (by rfl) ⟨677678, by rfl⟩ : syracuseStep 903571 = 1355357) B1355357
theorem B903587 : Blo 900574 903587 := bstep (se 1 (by rfl) ⟨677690, by rfl⟩ : syracuseStep 903587 = 1355381) B1355381
theorem B903603 : Blo 900574 903603 := bstep (se 1 (by rfl) ⟨677702, by rfl⟩ : syracuseStep 903603 = 1355405) B1355405
theorem B1526195 : Blo 900574 1526195 := bstep (se 1 (by rfl) ⟨1144646, by rfl⟩ : syracuseStep 1526195 = 2289293) B2289293
theorem B903619 : Blo 900574 903619 := bstep (se 1 (by rfl) ⟨677714, by rfl⟩ : syracuseStep 903619 = 1355429) B1355429
theorem B903635 : Blo 900574 903635 := bstep (se 1 (by rfl) ⟨677726, by rfl⟩ : syracuseStep 903635 = 1355453) B1355453
theorem B903651 : Blo 900574 903651 := bstep (se 1 (by rfl) ⟨677738, by rfl⟩ : syracuseStep 903651 = 1355477) B1355477
theorem B903667 : Blo 900574 903667 := bstep (se 1 (by rfl) ⟨677750, by rfl⟩ : syracuseStep 903667 = 1355501) B1355501
theorem B903683 : Blo 900574 903683 := bstep (se 1 (by rfl) ⟨677762, by rfl⟩ : syracuseStep 903683 = 1355525) B1355525
theorem B903699 : Blo 900574 903699 := bstep (se 1 (by rfl) ⟨677774, by rfl⟩ : syracuseStep 903699 = 1355549) B1355549
theorem B903715 : Blo 900574 903715 := bstep (se 1 (by rfl) ⟨677786, by rfl⟩ : syracuseStep 903715 = 1355573) B1355573
theorem B4573745 : Blo 900574 4573745 := bstep (se 2 (by rfl) ⟨1715154, by rfl⟩ : syracuseStep 4573745 = 3430309) B3430309
theorem B903731 : Blo 900574 903731 := bstep (se 1 (by rfl) ⟨677798, by rfl⟩ : syracuseStep 903731 = 1355597) B1355597
theorem B1526323 : Blo 900574 1526323 := bstep (se 1 (by rfl) ⟨1144742, by rfl⟩ : syracuseStep 1526323 = 2289485) B2289485
theorem B903747 : Blo 900574 903747 := bstep (se 1 (by rfl) ⟨677810, by rfl⟩ : syracuseStep 903747 = 1355621) B1355621
theorem B3426893 : Blo 900574 3426893 := bstep (se 3 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 3426893 = 1285085) B1285085
theorem B903763 : Blo 900574 903763 := bstep (se 1 (by rfl) ⟨677822, by rfl⟩ : syracuseStep 903763 = 1355645) B1355645
theorem B903779 : Blo 900574 903779 := bstep (se 1 (by rfl) ⟨677834, by rfl⟩ : syracuseStep 903779 = 1355669) B1355669
theorem B903795 : Blo 900574 903795 := bstep (se 1 (by rfl) ⟨677846, by rfl⟩ : syracuseStep 903795 = 1355693) B1355693
theorem B903811 : Blo 900574 903811 := bstep (se 1 (by rfl) ⟨677858, by rfl⟩ : syracuseStep 903811 = 1355717) B1355717
theorem B903827 : Blo 900574 903827 := bstep (se 1 (by rfl) ⟨677870, by rfl⟩ : syracuseStep 903827 = 1355741) B1355741
theorem B903843 : Blo 900574 903843 := bstep (se 1 (by rfl) ⟨677882, by rfl⟩ : syracuseStep 903843 = 1355765) B1355765
theorem B903859 : Blo 900574 903859 := bstep (se 1 (by rfl) ⟨677894, by rfl⟩ : syracuseStep 903859 = 1355789) B1355789
theorem B1526465 : Blo 900574 1526465 := bstep (se 2 (by rfl) ⟨572424, by rfl⟩ : syracuseStep 1526465 = 1144849) B1144849
theorem B903875 : Blo 900574 903875 := bstep (se 1 (by rfl) ⟨677906, by rfl⟩ : syracuseStep 903875 = 1355813) B1355813
theorem B903891 : Blo 900574 903891 := bstep (se 1 (by rfl) ⟨677918, by rfl⟩ : syracuseStep 903891 = 1355837) B1355837
theorem B2345699 : Blo 900574 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B903907 : Blo 900574 903907 := bstep (se 1 (by rfl) ⟨677930, by rfl⟩ : syracuseStep 903907 = 1355861) B1355861
theorem B903923 : Blo 900574 903923 := bstep (se 1 (by rfl) ⟨677942, by rfl⟩ : syracuseStep 903923 = 1355885) B1355885
theorem B903939 : Blo 900574 903939 := bstep (se 1 (by rfl) ⟨677954, by rfl⟩ : syracuseStep 903939 = 1355909) B1355909
theorem B903955 : Blo 900574 903955 := bstep (se 1 (by rfl) ⟨677966, by rfl⟩ : syracuseStep 903955 = 1355933) B1355933
theorem B42257173 : Blo 900574 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B903971 : Blo 900574 903971 := bstep (se 1 (by rfl) ⟨677978, by rfl⟩ : syracuseStep 903971 = 1355957) B1355957
theorem B903987 : Blo 900574 903987 := bstep (se 1 (by rfl) ⟨677990, by rfl⟩ : syracuseStep 903987 = 1355981) B1355981
theorem B904003 : Blo 900574 904003 := bstep (se 1 (by rfl) ⟨678002, by rfl⟩ : syracuseStep 904003 = 1356005) B1356005
theorem B904019 : Blo 900574 904019 := bstep (se 1 (by rfl) ⟨678014, by rfl⟩ : syracuseStep 904019 = 1356029) B1356029
theorem B904035 : Blo 900574 904035 := bstep (se 1 (by rfl) ⟨678026, by rfl⟩ : syracuseStep 904035 = 1356053) B1356053
theorem B904051 : Blo 900574 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B904067 : Blo 900574 904067 := bstep (se 1 (by rfl) ⟨678050, by rfl⟩ : syracuseStep 904067 = 1356101) B1356101
theorem B904083 : Blo 900574 904083 := bstep (se 1 (by rfl) ⟨678062, by rfl⟩ : syracuseStep 904083 = 1356125) B1356125
theorem B904099 : Blo 900574 904099 := bstep (se 1 (by rfl) ⟨678074, by rfl⟩ : syracuseStep 904099 = 1356149) B1356149
theorem B904115 : Blo 900574 904115 := bstep (se 1 (by rfl) ⟨678086, by rfl⟩ : syracuseStep 904115 = 1356173) B1356173
theorem B904131 : Blo 900574 904131 := bstep (se 1 (by rfl) ⟨678098, by rfl⟩ : syracuseStep 904131 = 1356197) B1356197
theorem B904147 : Blo 900574 904147 := bstep (se 1 (by rfl) ⟨678110, by rfl⟩ : syracuseStep 904147 = 1356221) B1356221
theorem B1625059 : Blo 900574 1625059 := bstep (se 1 (by rfl) ⟨1218794, by rfl⟩ : syracuseStep 1625059 = 2437589) B2437589
theorem B904163 : Blo 900574 904163 := bstep (se 1 (by rfl) ⟨678122, by rfl⟩ : syracuseStep 904163 = 1356245) B1356245
theorem B2280433 : Blo 900574 2280433 := bstep (se 2 (by rfl) ⟨855162, by rfl⟩ : syracuseStep 2280433 = 1710325) B1710325
theorem B904179 : Blo 900574 904179 := bstep (se 1 (by rfl) ⟨678134, by rfl⟩ : syracuseStep 904179 = 1356269) B1356269
theorem B904195 : Blo 900574 904195 := bstep (se 1 (by rfl) ⟨678146, by rfl⟩ : syracuseStep 904195 = 1356293) B1356293
theorem B904211 : Blo 900574 904211 := bstep (se 1 (by rfl) ⟨678158, by rfl⟩ : syracuseStep 904211 = 1356317) B1356317
theorem B904227 : Blo 900574 904227 := bstep (se 1 (by rfl) ⟨678170, by rfl⟩ : syracuseStep 904227 = 1356341) B1356341
theorem B904243 : Blo 900574 904243 := bstep (se 1 (by rfl) ⟨678182, by rfl⟩ : syracuseStep 904243 = 1356365) B1356365
theorem B904259 : Blo 900574 904259 := bstep (se 1 (by rfl) ⟨678194, by rfl⟩ : syracuseStep 904259 = 1356389) B1356389
theorem B3296333 : Blo 900574 3296333 := bstep (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) B1236125
theorem B904275 : Blo 900574 904275 := bstep (se 1 (by rfl) ⟨678206, by rfl⟩ : syracuseStep 904275 = 1356413) B1356413
theorem B904291 : Blo 900574 904291 := bstep (se 1 (by rfl) ⟨678218, by rfl⟩ : syracuseStep 904291 = 1356437) B1356437
theorem B904307 : Blo 900574 904307 := bstep (se 1 (by rfl) ⟨678230, by rfl⟩ : syracuseStep 904307 = 1356461) B1356461
theorem B904323 : Blo 900574 904323 := bstep (se 1 (by rfl) ⟨678242, by rfl⟩ : syracuseStep 904323 = 1356485) B1356485
theorem B904339 : Blo 900574 904339 := bstep (se 1 (by rfl) ⟨678254, by rfl⟩ : syracuseStep 904339 = 1356509) B1356509
theorem B904355 : Blo 900574 904355 := bstep (se 1 (by rfl) ⟨678266, by rfl⟩ : syracuseStep 904355 = 1356533) B1356533
theorem B904371 : Blo 900574 904371 := bstep (se 1 (by rfl) ⟨678278, by rfl⟩ : syracuseStep 904371 = 1356557) B1356557
theorem B904387 : Blo 900574 904387 := bstep (se 1 (by rfl) ⟨678290, by rfl⟩ : syracuseStep 904387 = 1356581) B1356581
theorem B904403 : Blo 900574 904403 := bstep (se 1 (by rfl) ⟨678302, by rfl⟩ : syracuseStep 904403 = 1356605) B1356605
theorem B904419 : Blo 900574 904419 := bstep (se 1 (by rfl) ⟨678314, by rfl⟩ : syracuseStep 904419 = 1356629) B1356629
theorem B904435 : Blo 900574 904435 := bstep (se 1 (by rfl) ⟨678326, by rfl⟩ : syracuseStep 904435 = 1356653) B1356653
theorem B2280707 : Blo 900574 2280707 := bstep (se 1 (by rfl) ⟨1710530, by rfl⟩ : syracuseStep 2280707 = 3421061) B3421061
theorem B904451 : Blo 900574 904451 := bstep (se 1 (by rfl) ⟨678338, by rfl⟩ : syracuseStep 904451 = 1356677) B1356677
theorem B904467 : Blo 900574 904467 := bstep (se 1 (by rfl) ⟨678350, by rfl⟩ : syracuseStep 904467 = 1356701) B1356701
theorem B904483 : Blo 900574 904483 := bstep (se 1 (by rfl) ⟨678362, by rfl⟩ : syracuseStep 904483 = 1356725) B1356725
theorem B904499 : Blo 900574 904499 := bstep (se 1 (by rfl) ⟨678374, by rfl⟩ : syracuseStep 904499 = 1356749) B1356749
theorem B904515 : Blo 900574 904515 := bstep (se 1 (by rfl) ⟨678386, by rfl⟩ : syracuseStep 904515 = 1356773) B1356773
theorem B904531 : Blo 900574 904531 := bstep (se 1 (by rfl) ⟨678398, by rfl⟩ : syracuseStep 904531 = 1356797) B1356797
theorem B904547 : Blo 900574 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B3427697 : Blo 900574 3427697 := bstep (se 2 (by rfl) ⟨1285386, by rfl⟩ : syracuseStep 3427697 = 2570773) B2570773
theorem B904563 : Blo 900574 904563 := bstep (se 1 (by rfl) ⟨678422, by rfl⟩ : syracuseStep 904563 = 1356845) B1356845
theorem B1625521 : Blo 900574 1625521 := bstep (se 2 (by rfl) ⟨609570, by rfl⟩ : syracuseStep 1625521 = 1219141) B1219141
theorem B2280899 : Blo 900574 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B1756721 : Blo 900574 1756721 := bstep (se 2 (by rfl) ⟨658770, by rfl⟩ : syracuseStep 1756721 = 1317541) B1317541
theorem B2444899 : Blo 900574 2444899 := bstep (se 1 (by rfl) ⟨1833674, by rfl⟩ : syracuseStep 2444899 = 3667349) B3667349
theorem B2444941 : Blo 900574 2444941 := bstep (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) B916853
theorem B4116131 : Blo 900574 4116131 := bstep (se 1 (by rfl) ⟨3087098, by rfl⟩ : syracuseStep 4116131 = 6174197) B6174197
theorem B2314051 : Blo 900574 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B4575203 : Blo 900574 4575203 := bstep (se 1 (by rfl) ⟨3431402, by rfl⟩ : syracuseStep 4575203 = 6862805) B6862805
theorem B3428365 : Blo 900574 3428365 := bstep (se 3 (by rfl) ⟨642818, by rfl⟩ : syracuseStep 3428365 = 1285637) B1285637
theorem B5492941 : Blo 900574 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B1462595 : Blo 900574 1462595 := bstep (se 1 (by rfl) ⟨1096946, by rfl⟩ : syracuseStep 1462595 = 2193893) B2193893
theorem B2281841 : Blo 900574 2281841 := bstep (se 2 (by rfl) ⟨855690, by rfl⟩ : syracuseStep 2281841 = 1711381) B1711381
theorem B2281891 : Blo 900574 2281891 := bstep (se 1 (by rfl) ⟨1711418, by rfl⟩ : syracuseStep 2281891 = 3422837) B3422837
theorem B3854861 : Blo 900574 3854861 := bstep (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) B1445573
theorem B2282033 : Blo 900574 2282033 := bstep (se 2 (by rfl) ⟨855762, by rfl⟩ : syracuseStep 2282033 = 1711525) B1711525
theorem B3854897 : Blo 900574 3854897 := bstep (se 2 (by rfl) ⟨1445586, by rfl⟩ : syracuseStep 3854897 = 2891173) B2891173
theorem B4870853 : Blo 900574 4870853 := bstep (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) B913285
theorem B5788421 : Blo 900574 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B4576013 : Blo 900574 4576013 := bstep (se 3 (by rfl) ⟨858002, by rfl⟩ : syracuseStep 4576013 = 1716005) B1716005
theorem B3429155 : Blo 900574 3429155 := bstep (se 1 (by rfl) ⟨2571866, by rfl⟩ : syracuseStep 3429155 = 5143733) B5143733
theorem B5133253 : Blo 900574 5133253 := bstep (se 4 (by rfl) ⟨481242, by rfl⟩ : syracuseStep 5133253 = 962485) B962485
theorem B8803313 : Blo 900574 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B1758275 : Blo 900574 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B3429809 : Blo 900574 3429809 := bstep (se 2 (by rfl) ⟨1286178, by rfl⟩ : syracuseStep 3429809 = 2572357) B2572357
theorem B2283025 : Blo 900574 2283025 := bstep (se 2 (by rfl) ⟨856134, by rfl⟩ : syracuseStep 2283025 = 1712269) B1712269
theorem B2283299 : Blo 900574 2283299 := bstep (se 1 (by rfl) ⟨1712474, by rfl⟩ : syracuseStep 2283299 = 3424949) B3424949
theorem B2742083 : Blo 900574 2742083 := bstep (se 1 (by rfl) ⟨2056562, by rfl⟩ : syracuseStep 2742083 = 4113125) B4113125
theorem B2283491 : Blo 900574 2283491 := bstep (se 1 (by rfl) ⟨1712618, by rfl⟩ : syracuseStep 2283491 = 3425237) B3425237
theorem B1628419 : Blo 900574 1628419 := bstep (se 1 (by rfl) ⟨1221314, by rfl⟩ : syracuseStep 1628419 = 2442629) B2442629
theorem B9263429 : Blo 900574 9263429 := bstep (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) B1736893
theorem B1857937 : Blo 900574 1857937 := bstep (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) B1393453
theorem B11000245 : Blo 900574 11000245 := bstep (se 5 (by rfl) ⟨515636, by rfl⟩ : syracuseStep 11000245 = 1031273) B1031273
theorem B3431267 : Blo 900574 3431267 := bstep (se 1 (by rfl) ⟨2573450, by rfl⟩ : syracuseStep 3431267 = 5146901) B5146901
theorem B3431281 : Blo 900574 3431281 := bstep (se 2 (by rfl) ⟨1286730, by rfl⟩ : syracuseStep 3431281 = 2573461) B2573461
theorem B5135237 : Blo 900574 5135237 := bstep (se 4 (by rfl) ⟨481428, by rfl⟩ : syracuseStep 5135237 = 962857) B962857
theorem B2284433 : Blo 900574 2284433 := bstep (se 2 (by rfl) ⟨856662, by rfl⟩ : syracuseStep 2284433 = 1713325) B1713325
theorem B2284483 : Blo 900574 2284483 := bstep (se 1 (by rfl) ⟨1713362, by rfl⟩ : syracuseStep 2284483 = 3426725) B3426725
theorem B2284625 : Blo 900574 2284625 := bstep (se 2 (by rfl) ⟨856734, by rfl⟩ : syracuseStep 2284625 = 1713469) B1713469
theorem B24697997 : Blo 900574 24697997 := bstep (se 3 (by rfl) ⟨4630874, by rfl⟩ : syracuseStep 24697997 = 9261749) B9261749
theorem B2055395 : Blo 900574 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B1301761 : Blo 900574 1301761 := bstep (se 2 (by rfl) ⟨488160, by rfl⟩ : syracuseStep 1301761 = 976321) B976321
theorem B1924355 : Blo 900574 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B1465777 : Blo 900574 1465777 := bstep (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) B1099333
theorem B4578929 : Blo 900574 4578929 := bstep (se 2 (by rfl) ⟨1717098, by rfl⟩ : syracuseStep 4578929 = 3434197) B3434197
theorem B5791621 : Blo 900574 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B2285617 : Blo 900574 2285617 := bstep (se 2 (by rfl) ⟨857106, by rfl⟩ : syracuseStep 2285617 = 1714213) B1714213
theorem B1466435 : Blo 900574 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B13000931 : Blo 900574 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B3432739 : Blo 900574 3432739 := bstep (se 1 (by rfl) ⟨2574554, by rfl⟩ : syracuseStep 3432739 = 5149109) B5149109
theorem B2285891 : Blo 900574 2285891 := bstep (se 1 (by rfl) ⟨1714418, by rfl⟩ : syracuseStep 2285891 = 3428837) B3428837
theorem B4874573 : Blo 900574 4874573 := bstep (se 3 (by rfl) ⟨913982, by rfl⟩ : syracuseStep 4874573 = 1827965) B1827965
theorem B6185315 : Blo 900574 6185315 := bstep (se 1 (by rfl) ⟨4638986, by rfl⟩ : syracuseStep 6185315 = 9277973) B9277973
theorem B1925603 : Blo 900574 1925603 := bstep (se 1 (by rfl) ⟨1444202, by rfl⟩ : syracuseStep 1925603 = 2888405) B2888405
theorem B2286083 : Blo 900574 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B2744867 : Blo 900574 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B3039821 : Blo 900574 3039821 := bstep (se 3 (by rfl) ⟨569966, by rfl⟩ : syracuseStep 3039821 = 1139933) B1139933
theorem B3039875 : Blo 900574 3039875 := bstep (se 1 (by rfl) ⟨2279906, by rfl⟩ : syracuseStep 3039875 = 4559813) B4559813
theorem B3859235 : Blo 900574 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B5202829 : Blo 900574 5202829 := bstep (se 3 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 5202829 = 1951061) B1951061
theorem B3040145 : Blo 900574 3040145 := bstep (se 2 (by rfl) ⟨1140054, by rfl⟩ : syracuseStep 3040145 = 2280109) B2280109
theorem B1926193 : Blo 900574 1926193 := bstep (se 2 (by rfl) ⟨722322, by rfl⟩ : syracuseStep 1926193 = 1444645) B1444645
theorem B1139827 : Blo 900574 1139827 := bstep (se 1 (by rfl) ⟨854870, by rfl⟩ : syracuseStep 1139827 = 1709741) B1709741
theorem B1139923 : Blo 900574 1139923 := bstep (se 1 (by rfl) ⟨854942, by rfl⟩ : syracuseStep 1139923 = 1709885) B1709885
theorem B5858693 : Blo 900574 5858693 := bstep (se 4 (by rfl) ⟨549252, by rfl⟩ : syracuseStep 5858693 = 1098505) B1098505
theorem B3040685 : Blo 900574 3040685 := bstep (se 3 (by rfl) ⟨570128, by rfl⟩ : syracuseStep 3040685 = 1140257) B1140257
theorem B2287025 : Blo 900574 2287025 := bstep (se 2 (by rfl) ⟨857634, by rfl⟩ : syracuseStep 2287025 = 1715269) B1715269
theorem B3040739 : Blo 900574 3040739 := bstep (se 1 (by rfl) ⟨2280554, by rfl⟩ : syracuseStep 3040739 = 4561109) B4561109
theorem B2287075 : Blo 900574 2287075 := bstep (se 1 (by rfl) ⟨1715306, by rfl⟩ : syracuseStep 2287075 = 3430613) B3430613
theorem B2287217 : Blo 900574 2287217 := bstep (se 2 (by rfl) ⟨857706, by rfl⟩ : syracuseStep 2287217 = 1715413) B1715413
theorem B1140419 : Blo 900574 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B1173187 : Blo 900574 1173187 := bstep (se 1 (by rfl) ⟨879890, by rfl⟩ : syracuseStep 1173187 = 1759781) B1759781
theorem B3041009 : Blo 900574 3041009 := bstep (se 2 (by rfl) ⟨1140378, by rfl⟩ : syracuseStep 3041009 = 2280757) B2280757
theorem B2320579 : Blo 900574 2320579 := bstep (se 1 (by rfl) ⟨1740434, by rfl⟩ : syracuseStep 2320579 = 3480869) B3480869
theorem B6187205 : Blo 900574 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B10414307 : Blo 900574 10414307 := bstep (se 1 (by rfl) ⟨7810730, by rfl⟩ : syracuseStep 10414307 = 15621461) B15621461
theorem B2058467 : Blo 900574 2058467 := bstep (se 1 (by rfl) ⟨1543850, by rfl⟩ : syracuseStep 2058467 = 3087701) B3087701
theorem B16705763 : Blo 900574 16705763 := bstep (se 1 (by rfl) ⟨12529322, by rfl⟩ : syracuseStep 16705763 = 25058645) B25058645
theorem B3041549 : Blo 900574 3041549 := bstep (se 3 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 3041549 = 1140581) B1140581
theorem B3041603 : Blo 900574 3041603 := bstep (se 1 (by rfl) ⟨2281202, by rfl⟩ : syracuseStep 3041603 = 4562405) B4562405
theorem B1141123 : Blo 900574 1141123 := bstep (se 1 (by rfl) ⟨855842, by rfl⟩ : syracuseStep 1141123 = 1711685) B1711685
theorem B1141219 : Blo 900574 1141219 := bstep (se 1 (by rfl) ⟨855914, by rfl⟩ : syracuseStep 1141219 = 1711829) B1711829
theorem B1370609 : Blo 900574 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B3041873 : Blo 900574 3041873 := bstep (se 2 (by rfl) ⟨1140702, by rfl⟩ : syracuseStep 3041873 = 2281405) B2281405
theorem B2288209 : Blo 900574 2288209 := bstep (se 2 (by rfl) ⟨858078, by rfl⟩ : syracuseStep 2288209 = 1716157) B1716157
theorem B5139085 : Blo 900574 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B2288483 : Blo 900574 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B2026385 : Blo 900574 2026385 := bstep (se 2 (by rfl) ⟨759894, by rfl⟩ : syracuseStep 2026385 = 1519789) B1519789
theorem B2026403 : Blo 900574 2026403 := bstep (se 1 (by rfl) ⟨1519802, by rfl⟩ : syracuseStep 2026403 = 3039605) B3039605
theorem B3664817 : Blo 900574 3664817 := bstep (se 2 (by rfl) ⟨1374306, by rfl⟩ : syracuseStep 3664817 = 2748613) B2748613
theorem B1141715 : Blo 900574 1141715 := bstep (se 1 (by rfl) ⟨856286, by rfl⟩ : syracuseStep 1141715 = 1712573) B1712573
theorem B2288675 : Blo 900574 2288675 := bstep (se 1 (by rfl) ⟨1716506, by rfl⟩ : syracuseStep 2288675 = 3433013) B3433013
theorem B1567793 : Blo 900574 1567793 := bstep (se 2 (by rfl) ⟨587922, by rfl⟩ : syracuseStep 1567793 = 1175845) B1175845
theorem B3042413 : Blo 900574 3042413 := bstep (se 3 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 3042413 = 1140905) B1140905
theorem B3042467 : Blo 900574 3042467 := bstep (se 1 (by rfl) ⟨2281850, by rfl⟩ : syracuseStep 3042467 = 4563701) B4563701
theorem B2026673 : Blo 900574 2026673 := bstep (se 2 (by rfl) ⟨760002, by rfl⟩ : syracuseStep 2026673 = 1520005) B1520005
theorem B2026691 : Blo 900574 2026691 := bstep (se 1 (by rfl) ⟨1520018, by rfl⟩ : syracuseStep 2026691 = 3040037) B3040037
theorem B13036913 : Blo 900574 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B5795185 : Blo 900574 5795185 := bstep (se 2 (by rfl) ⟨2173194, by rfl⟩ : syracuseStep 5795185 = 4346389) B4346389
theorem B3042737 : Blo 900574 3042737 := bstep (se 2 (by rfl) ⟨1141026, by rfl⟩ : syracuseStep 3042737 = 2282053) B2282053
theorem B2026961 : Blo 900574 2026961 := bstep (se 2 (by rfl) ⟨760110, by rfl⟩ : syracuseStep 2026961 = 1520221) B1520221
theorem B2026979 : Blo 900574 2026979 := bstep (se 1 (by rfl) ⟨1520234, by rfl⟩ : syracuseStep 2026979 = 3040469) B3040469
theorem B2747981 : Blo 900574 2747981 := bstep (se 3 (by rfl) ⟨515246, by rfl⟩ : syracuseStep 2747981 = 1030493) B1030493
theorem B1142419 : Blo 900574 1142419 := bstep (se 1 (by rfl) ⟨856814, by rfl⟩ : syracuseStep 1142419 = 1713629) B1713629
theorem B2027249 : Blo 900574 2027249 := bstep (se 2 (by rfl) ⟨760218, by rfl⟩ : syracuseStep 2027249 = 1520437) B1520437
theorem B1142515 : Blo 900574 1142515 := bstep (se 1 (by rfl) ⟨856886, by rfl⟩ : syracuseStep 1142515 = 1713773) B1713773
theorem B2027267 : Blo 900574 2027267 := bstep (se 1 (by rfl) ⟨1520450, by rfl⟩ : syracuseStep 2027267 = 3040901) B3040901
theorem B1830673 : Blo 900574 1830673 := bstep (se 2 (by rfl) ⟨686502, by rfl⟩ : syracuseStep 1830673 = 1373005) B1373005
theorem B41676565 : Blo 900574 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B3043277 : Blo 900574 3043277 := bstep (se 3 (by rfl) ⟨570614, by rfl⟩ : syracuseStep 3043277 = 1141229) B1141229
theorem B2289617 : Blo 900574 2289617 := bstep (se 2 (by rfl) ⟨858606, by rfl⟩ : syracuseStep 2289617 = 1717213) B1717213
theorem B3043331 : Blo 900574 3043331 := bstep (se 1 (by rfl) ⟨2282498, by rfl⟩ : syracuseStep 3043331 = 4564997) B4564997
theorem B2289667 : Blo 900574 2289667 := bstep (se 1 (by rfl) ⟨1717250, by rfl⟩ : syracuseStep 2289667 = 3434501) B3434501
theorem B2027537 : Blo 900574 2027537 := bstep (se 2 (by rfl) ⟨760326, by rfl⟩ : syracuseStep 2027537 = 1520653) B1520653
theorem B2027555 : Blo 900574 2027555 := bstep (se 1 (by rfl) ⟨1520666, by rfl⟩ : syracuseStep 2027555 = 3041333) B3041333
theorem B2060401 : Blo 900574 2060401 := bstep (se 2 (by rfl) ⟨772650, by rfl⟩ : syracuseStep 2060401 = 1545301) B1545301
theorem B1929379 : Blo 900574 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B1143011 : Blo 900574 1143011 := bstep (se 1 (by rfl) ⟨857258, by rfl⟩ : syracuseStep 1143011 = 1714517) B1714517
theorem B3043601 : Blo 900574 3043601 := bstep (se 2 (by rfl) ⟨1141350, by rfl⟩ : syracuseStep 3043601 = 2282701) B2282701
theorem B2027825 : Blo 900574 2027825 := bstep (se 2 (by rfl) ⟨760434, by rfl⟩ : syracuseStep 2027825 = 1520869) B1520869
theorem B9761077 : Blo 900574 9761077 := bstep (se 5 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 9761077 = 915101) B915101
theorem B2027843 : Blo 900574 2027843 := bstep (se 1 (by rfl) ⟨1520882, by rfl⟩ : syracuseStep 2027843 = 3041765) B3041765
theorem B1372531 : Blo 900574 1372531 := bstep (se 1 (by rfl) ⟨1029398, by rfl⟩ : syracuseStep 1372531 = 2058797) B2058797
theorem B3862961 : Blo 900574 3862961 := bstep (se 2 (by rfl) ⟨1448610, by rfl⟩ : syracuseStep 3862961 = 2897221) B2897221
theorem B5141069 : Blo 900574 5141069 := bstep (se 3 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 5141069 = 1927901) B1927901
theorem B2028113 : Blo 900574 2028113 := bstep (se 2 (by rfl) ⟨760542, by rfl⟩ : syracuseStep 2028113 = 1521085) B1521085
theorem B2028131 : Blo 900574 2028131 := bstep (se 1 (by rfl) ⟨1521098, by rfl⟩ : syracuseStep 2028131 = 3042197) B3042197
theorem B3044141 : Blo 900574 3044141 := bstep (se 3 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 3044141 = 1141553) B1141553
theorem B3044195 : Blo 900574 3044195 := bstep (se 1 (by rfl) ⟨2283146, by rfl⟩ : syracuseStep 3044195 = 4566293) B4566293
theorem B2028401 : Blo 900574 2028401 := bstep (se 2 (by rfl) ⟨760650, by rfl⟩ : syracuseStep 2028401 = 1521301) B1521301
theorem B2028419 : Blo 900574 2028419 := bstep (se 1 (by rfl) ⟨1521314, by rfl⟩ : syracuseStep 2028419 = 3042629) B3042629
theorem B1831825 : Blo 900574 1831825 := bstep (se 2 (by rfl) ⟨686934, by rfl⟩ : syracuseStep 1831825 = 1373869) B1373869
theorem B914323 : Blo 900574 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1143715 : Blo 900574 1143715 := bstep (se 1 (by rfl) ⟨857786, by rfl⟩ : syracuseStep 1143715 = 1715573) B1715573
theorem B1831889 : Blo 900574 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B1930225 : Blo 900574 1930225 := bstep (se 2 (by rfl) ⟨723834, by rfl⟩ : syracuseStep 1930225 = 1447669) B1447669
theorem B1143811 : Blo 900574 1143811 := bstep (se 1 (by rfl) ⟨857858, by rfl⟩ : syracuseStep 1143811 = 1715717) B1715717
theorem B2061379 : Blo 900574 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B3044465 : Blo 900574 3044465 := bstep (se 2 (by rfl) ⟨1141674, by rfl⟩ : syracuseStep 3044465 = 2283349) B2283349
theorem B9270413 : Blo 900574 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B2028689 : Blo 900574 2028689 := bstep (se 2 (by rfl) ⟨760758, by rfl⟩ : syracuseStep 2028689 = 1521517) B1521517
theorem B2749585 : Blo 900574 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B2028707 : Blo 900574 2028707 := bstep (se 1 (by rfl) ⟨1521530, by rfl⟩ : syracuseStep 2028707 = 3043061) B3043061
theorem B1373377 : Blo 900574 1373377 := bstep (se 2 (by rfl) ⟨515016, by rfl⟩ : syracuseStep 1373377 = 1030033) B1030033
theorem B6845795 : Blo 900574 6845795 := bstep (se 1 (by rfl) ⟨5134346, by rfl⟩ : syracuseStep 6845795 = 10268693) B10268693
theorem B2028977 : Blo 900574 2028977 := bstep (se 2 (by rfl) ⟨760866, by rfl⟩ : syracuseStep 2028977 = 1521733) B1521733
theorem B2028995 : Blo 900574 2028995 := bstep (se 1 (by rfl) ⟨1521746, by rfl⟩ : syracuseStep 2028995 = 3043493) B3043493
theorem B5142001 : Blo 900574 5142001 := bstep (se 2 (by rfl) ⟨1928250, by rfl⟩ : syracuseStep 5142001 = 3856501) B3856501
theorem B1144307 : Blo 900574 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B1013251 : Blo 900574 1013251 := bstep (se 1 (by rfl) ⟨759938, by rfl⟩ : syracuseStep 1013251 = 1519877) B1519877
theorem B5797453 : Blo 900574 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B3045005 : Blo 900574 3045005 := bstep (se 3 (by rfl) ⟨570938, by rfl⟩ : syracuseStep 3045005 = 1141877) B1141877
theorem B1013395 : Blo 900574 1013395 := bstep (se 1 (by rfl) ⟨760046, by rfl⟩ : syracuseStep 1013395 = 1520093) B1520093
theorem B3045059 : Blo 900574 3045059 := bstep (se 1 (by rfl) ⟨2283794, by rfl⟩ : syracuseStep 3045059 = 4567589) B4567589
theorem B2029265 : Blo 900574 2029265 := bstep (se 2 (by rfl) ⟨760974, by rfl⟩ : syracuseStep 2029265 = 1521949) B1521949
theorem B2029283 : Blo 900574 2029283 := bstep (se 1 (by rfl) ⟨1521962, by rfl⟩ : syracuseStep 2029283 = 3043925) B3043925
theorem B1734385 : Blo 900574 1734385 := bstep (se 2 (by rfl) ⟨650394, by rfl⟩ : syracuseStep 1734385 = 1300789) B1300789
theorem B1013539 : Blo 900574 1013539 := bstep (se 1 (by rfl) ⟨760154, by rfl⟩ : syracuseStep 1013539 = 1520309) B1520309
theorem B1832881 : Blo 900574 1832881 := bstep (se 2 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 1832881 = 1374661) B1374661
theorem B1013683 : Blo 900574 1013683 := bstep (se 1 (by rfl) ⟨760262, by rfl⟩ : syracuseStep 1013683 = 1520525) B1520525
theorem B3045329 : Blo 900574 3045329 := bstep (se 2 (by rfl) ⟨1141998, by rfl⟩ : syracuseStep 3045329 = 2283997) B2283997
theorem B2029553 : Blo 900574 2029553 := bstep (se 2 (by rfl) ⟨761082, by rfl⟩ : syracuseStep 2029553 = 1522165) B1522165
theorem B2029571 : Blo 900574 2029571 := bstep (se 1 (by rfl) ⟨1522178, by rfl⟩ : syracuseStep 2029571 = 3044357) B3044357
theorem B1013827 : Blo 900574 1013827 := bstep (se 1 (by rfl) ⟨760370, by rfl⟩ : syracuseStep 1013827 = 1520741) B1520741
theorem B1013971 : Blo 900574 1013971 := bstep (se 1 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 1013971 = 1520957) B1520957
theorem B2029841 : Blo 900574 2029841 := bstep (se 2 (by rfl) ⟨761190, by rfl⟩ : syracuseStep 2029841 = 1522381) B1522381
theorem B2029859 : Blo 900574 2029859 := bstep (se 1 (by rfl) ⟨1522394, by rfl⟩ : syracuseStep 2029859 = 3044789) B3044789
theorem B1014115 : Blo 900574 1014115 := bstep (se 1 (by rfl) ⟨760586, by rfl⟩ : syracuseStep 1014115 = 1521173) B1521173
theorem B3045869 : Blo 900574 3045869 := bstep (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) B1142201
theorem B1014259 : Blo 900574 1014259 := bstep (se 1 (by rfl) ⟨760694, by rfl⟩ : syracuseStep 1014259 = 1521389) B1521389
theorem B3045923 : Blo 900574 3045923 := bstep (se 1 (by rfl) ⟨2284442, by rfl⟩ : syracuseStep 3045923 = 4568885) B4568885
theorem B2030129 : Blo 900574 2030129 := bstep (se 2 (by rfl) ⟨761298, by rfl⟩ : syracuseStep 2030129 = 1522597) B1522597
theorem B1374769 : Blo 900574 1374769 := bstep (se 2 (by rfl) ⟨515538, by rfl⟩ : syracuseStep 1374769 = 1031077) B1031077
theorem B2030147 : Blo 900574 2030147 := bstep (se 1 (by rfl) ⟨1522610, by rfl⟩ : syracuseStep 2030147 = 3045221) B3045221
theorem B1014403 : Blo 900574 1014403 := bstep (se 1 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 1014403 = 1521605) B1521605
theorem B2063011 : Blo 900574 2063011 := bstep (se 1 (by rfl) ⟨1547258, by rfl⟩ : syracuseStep 2063011 = 3094517) B3094517
theorem B1014547 : Blo 900574 1014547 := bstep (se 1 (by rfl) ⟨760910, by rfl⟩ : syracuseStep 1014547 = 1521821) B1521821
theorem B3046193 : Blo 900574 3046193 := bstep (se 2 (by rfl) ⟨1142322, by rfl⟩ : syracuseStep 3046193 = 2284645) B2284645
theorem B2030417 : Blo 900574 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B2030435 : Blo 900574 2030435 := bstep (se 1 (by rfl) ⟨1522826, by rfl⟩ : syracuseStep 2030435 = 3045653) B3045653
theorem B1014691 : Blo 900574 1014691 := bstep (se 1 (by rfl) ⟨761018, by rfl⟩ : syracuseStep 1014691 = 1522037) B1522037
theorem B5143459 : Blo 900574 5143459 := bstep (se 1 (by rfl) ⟨3857594, by rfl⟩ : syracuseStep 5143459 = 7715189) B7715189
theorem B1014835 : Blo 900574 1014835 := bstep (se 1 (by rfl) ⟨761126, by rfl⟩ : syracuseStep 1014835 = 1522253) B1522253
theorem B2030705 : Blo 900574 2030705 := bstep (se 2 (by rfl) ⟨761514, by rfl⟩ : syracuseStep 2030705 = 1523029) B1523029
theorem B2030723 : Blo 900574 2030723 := bstep (se 1 (by rfl) ⟨1523042, by rfl⟩ : syracuseStep 2030723 = 3046085) B3046085
theorem B1014979 : Blo 900574 1014979 := bstep (se 1 (by rfl) ⟨761234, by rfl⟩ : syracuseStep 1014979 = 1522469) B1522469
theorem B3767501 : Blo 900574 3767501 := bstep (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) B1412813
theorem B3046733 : Blo 900574 3046733 := bstep (se 3 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 3046733 = 1142525) B1142525
theorem B1015123 : Blo 900574 1015123 := bstep (se 1 (by rfl) ⟨761342, by rfl⟩ : syracuseStep 1015123 = 1522685) B1522685
theorem B3046787 : Blo 900574 3046787 := bstep (se 1 (by rfl) ⟨2285090, by rfl⟩ : syracuseStep 3046787 = 4570181) B4570181
theorem B2030993 : Blo 900574 2030993 := bstep (se 2 (by rfl) ⟨761622, by rfl⟩ : syracuseStep 2030993 = 1523245) B1523245
theorem B2031011 : Blo 900574 2031011 := bstep (se 1 (by rfl) ⟨1523258, by rfl⟩ : syracuseStep 2031011 = 3046517) B3046517
theorem B5143985 : Blo 900574 5143985 := bstep (se 2 (by rfl) ⟨1928994, by rfl⟩ : syracuseStep 5143985 = 3857989) B3857989
theorem B1015267 : Blo 900574 1015267 := bstep (se 1 (by rfl) ⟨761450, by rfl⟩ : syracuseStep 1015267 = 1522901) B1522901
theorem B1015411 : Blo 900574 1015411 := bstep (se 1 (by rfl) ⟨761558, by rfl⟩ : syracuseStep 1015411 = 1523117) B1523117
theorem B3047057 : Blo 900574 3047057 := bstep (se 2 (by rfl) ⟨1142646, by rfl⟩ : syracuseStep 3047057 = 2285293) B2285293
theorem B2031281 : Blo 900574 2031281 := bstep (se 2 (by rfl) ⟨761730, by rfl⟩ : syracuseStep 2031281 = 1523461) B1523461
theorem B1506995 : Blo 900574 1506995 := bstep (se 1 (by rfl) ⟨1130246, by rfl⟩ : syracuseStep 1506995 = 2260493) B2260493
theorem B2031299 : Blo 900574 2031299 := bstep (se 1 (by rfl) ⟨1523474, by rfl⟩ : syracuseStep 2031299 = 3046949) B3046949
theorem B1015555 : Blo 900574 1015555 := bstep (se 1 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 1015555 = 1523333) B1523333
theorem B1015699 : Blo 900574 1015699 := bstep (se 1 (by rfl) ⟨761774, by rfl⟩ : syracuseStep 1015699 = 1523549) B1523549
theorem B2031569 : Blo 900574 2031569 := bstep (se 2 (by rfl) ⟨761838, by rfl⟩ : syracuseStep 2031569 = 1523677) B1523677
theorem B2031587 : Blo 900574 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B2031641 : Blo 900574 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B3047489 : Blo 900574 3047489 := bstep (se 2 (by rfl) ⟨1142808, by rfl⟩ : syracuseStep 3047489 = 2285617) B2285617
theorem B1015915 : Blo 900574 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B2031731 : Blo 900574 2031731 := bstep (se 1 (by rfl) ⟨1523798, by rfl⟩ : syracuseStep 2031731 = 3047597) B3047597
theorem B2031767 : Blo 900574 2031767 := bstep (se 1 (by rfl) ⟨1523825, by rfl⟩ : syracuseStep 2031767 = 3047651) B3047651
theorem B1016023 : Blo 900574 1016023 := bstep (se 1 (by rfl) ⟨762017, by rfl⟩ : syracuseStep 1016023 = 1524035) B1524035
theorem B2031947 : Blo 900574 2031947 := bstep (se 1 (by rfl) ⟨1523960, by rfl⟩ : syracuseStep 2031947 = 3047921) B3047921
theorem B2032001 : Blo 900574 2032001 := bstep (se 2 (by rfl) ⟨762000, by rfl⟩ : syracuseStep 2032001 = 1524001) B1524001
theorem B1016203 : Blo 900574 1016203 := bstep (se 1 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 1016203 = 1524305) B1524305
theorem B1540567 : Blo 900574 1540567 := bstep (se 1 (by rfl) ⟨1155425, by rfl⟩ : syracuseStep 1540567 = 2310851) B2310851
theorem B1016311 : Blo 900574 1016311 := bstep (se 1 (by rfl) ⟨762233, by rfl⟩ : syracuseStep 1016311 = 1524467) B1524467
theorem B1081931 : Blo 900574 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B2032217 : Blo 900574 2032217 := bstep (se 2 (by rfl) ⟨762081, by rfl⟩ : syracuseStep 2032217 = 1524163) B1524163
theorem B3048029 : Blo 900574 3048029 := bstep (se 3 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 3048029 = 1143011) B1143011
theorem B1016491 : Blo 900574 1016491 := bstep (se 1 (by rfl) ⟨762368, by rfl⟩ : syracuseStep 1016491 = 1524737) B1524737
theorem B2032307 : Blo 900574 2032307 := bstep (se 1 (by rfl) ⟨1524230, by rfl⟩ : syracuseStep 2032307 = 3048461) B3048461
theorem B2032343 : Blo 900574 2032343 := bstep (se 1 (by rfl) ⟨1524257, by rfl⟩ : syracuseStep 2032343 = 3048515) B3048515
theorem B1016599 : Blo 900574 1016599 := bstep (se 1 (by rfl) ⟨762449, by rfl⟩ : syracuseStep 1016599 = 1524899) B1524899
theorem B3900253 : Blo 900574 3900253 := bstep (se 3 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 3900253 = 1462595) B1462595
theorem B2032523 : Blo 900574 2032523 := bstep (se 1 (by rfl) ⟨1524392, by rfl⟩ : syracuseStep 2032523 = 3048785) B3048785
theorem B2032577 : Blo 900574 2032577 := bstep (se 2 (by rfl) ⟨762216, by rfl⟩ : syracuseStep 2032577 = 1524433) B1524433
theorem B1016779 : Blo 900574 1016779 := bstep (se 1 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 1016779 = 1525169) B1525169
theorem B1016887 : Blo 900574 1016887 := bstep (se 1 (by rfl) ⟨762665, by rfl⟩ : syracuseStep 1016887 = 1525331) B1525331
theorem B29295685 : Blo 900574 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B4752535 : Blo 900574 4752535 := bstep (se 1 (by rfl) ⟨3564401, by rfl⟩ : syracuseStep 4752535 = 7128803) B7128803
theorem B2032793 : Blo 900574 2032793 := bstep (se 2 (by rfl) ⟨762297, by rfl⟩ : syracuseStep 2032793 = 1524595) B1524595
theorem B1017067 : Blo 900574 1017067 := bstep (se 1 (by rfl) ⟨762800, by rfl⟩ : syracuseStep 1017067 = 1525601) B1525601
theorem B2032883 : Blo 900574 2032883 := bstep (se 1 (by rfl) ⟨1524662, by rfl⟩ : syracuseStep 2032883 = 3049325) B3049325
theorem B2032919 : Blo 900574 2032919 := bstep (se 1 (by rfl) ⟨1524689, by rfl⟩ : syracuseStep 2032919 = 3049379) B3049379
theorem B1017175 : Blo 900574 1017175 := bstep (se 1 (by rfl) ⟨762881, by rfl⟩ : syracuseStep 1017175 = 1525763) B1525763
theorem B2033099 : Blo 900574 2033099 := bstep (se 1 (by rfl) ⟨1524824, by rfl⟩ : syracuseStep 2033099 = 3049649) B3049649
theorem B2033153 : Blo 900574 2033153 := bstep (se 2 (by rfl) ⟨762432, by rfl⟩ : syracuseStep 2033153 = 1524865) B1524865
theorem B1017355 : Blo 900574 1017355 := bstep (se 1 (by rfl) ⟨763016, by rfl⟩ : syracuseStep 1017355 = 1526033) B1526033
theorem B1443415 : Blo 900574 1443415 := bstep (se 1 (by rfl) ⟨1082561, by rfl⟩ : syracuseStep 1443415 = 2165123) B2165123
theorem B1017463 : Blo 900574 1017463 := bstep (se 1 (by rfl) ⟨763097, by rfl⟩ : syracuseStep 1017463 = 1526195) B1526195
theorem B3049163 : Blo 900574 3049163 := bstep (se 1 (by rfl) ⟨2286872, by rfl⟩ : syracuseStep 3049163 = 4573745) B4573745
theorem B2033369 : Blo 900574 2033369 := bstep (se 2 (by rfl) ⟨762513, by rfl⟩ : syracuseStep 2033369 = 1525027) B1525027
theorem B1017643 : Blo 900574 1017643 := bstep (se 1 (by rfl) ⟨763232, by rfl⟩ : syracuseStep 1017643 = 1526465) B1526465
theorem B2033459 : Blo 900574 2033459 := bstep (se 1 (by rfl) ⟨1525094, by rfl⟩ : syracuseStep 2033459 = 3050189) B3050189
theorem B1443671 : Blo 900574 1443671 := bstep (se 1 (by rfl) ⟨1082753, by rfl⟩ : syracuseStep 1443671 = 2165507) B2165507
theorem B2033495 : Blo 900574 2033495 := bstep (se 1 (by rfl) ⟨1525121, by rfl⟩ : syracuseStep 2033495 = 3050243) B3050243
theorem B3049433 : Blo 900574 3049433 := bstep (se 2 (by rfl) ⟨1143537, by rfl⟩ : syracuseStep 3049433 = 2287075) B2287075
theorem B2033675 : Blo 900574 2033675 := bstep (se 1 (by rfl) ⟨1525256, by rfl⟩ : syracuseStep 2033675 = 3050513) B3050513
theorem B2033729 : Blo 900574 2033729 := bstep (se 2 (by rfl) ⟨762648, by rfl⟩ : syracuseStep 2033729 = 1525297) B1525297
theorem B15435845 : Blo 900574 15435845 := bstep (se 4 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 15435845 = 2894221) B2894221
theorem B2033945 : Blo 900574 2033945 := bstep (se 2 (by rfl) ⟨762729, by rfl⟩ : syracuseStep 2033945 = 1525459) B1525459
theorem B2034035 : Blo 900574 2034035 := bstep (se 1 (by rfl) ⟨1525526, by rfl⟩ : syracuseStep 2034035 = 3051053) B3051053
theorem B2034071 : Blo 900574 2034071 := bstep (se 1 (by rfl) ⟨1525553, by rfl⟩ : syracuseStep 2034071 = 3051107) B3051107
theorem B4885037 : Blo 900574 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B2034251 : Blo 900574 2034251 := bstep (se 1 (by rfl) ⟨1525688, by rfl⟩ : syracuseStep 2034251 = 3051377) B3051377
theorem B2034305 : Blo 900574 2034305 := bstep (se 2 (by rfl) ⟨762864, by rfl⟩ : syracuseStep 2034305 = 1525729) B1525729
theorem B3050135 : Blo 900574 3050135 := bstep (se 1 (by rfl) ⟨2287601, by rfl⟩ : syracuseStep 3050135 = 4575203) B4575203
theorem B2034521 : Blo 900574 2034521 := bstep (se 2 (by rfl) ⟨762945, by rfl⟩ : syracuseStep 2034521 = 1525891) B1525891
theorem B2034611 : Blo 900574 2034611 := bstep (se 1 (by rfl) ⟨1525958, by rfl⟩ : syracuseStep 2034611 = 3051917) B3051917
theorem B2165707 : Blo 900574 2165707 := bstep (se 1 (by rfl) ⟨1624280, by rfl⟩ : syracuseStep 2165707 = 3248561) B3248561
theorem B2034647 : Blo 900574 2034647 := bstep (se 1 (by rfl) ⟨1525985, by rfl⟩ : syracuseStep 2034647 = 3051971) B3051971
theorem B3247235 : Blo 900574 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B2034827 : Blo 900574 2034827 := bstep (se 1 (by rfl) ⟨1526120, by rfl⟩ : syracuseStep 2034827 = 3052241) B3052241
theorem B3050675 : Blo 900574 3050675 := bstep (se 1 (by rfl) ⟨2288006, by rfl⟩ : syracuseStep 3050675 = 4576013) B4576013
theorem B2034881 : Blo 900574 2034881 := bstep (se 2 (by rfl) ⟨763080, by rfl⟩ : syracuseStep 2034881 = 1526161) B1526161
theorem B5868875 : Blo 900574 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B2035097 : Blo 900574 2035097 := bstep (se 2 (by rfl) ⟨763161, by rfl⟩ : syracuseStep 2035097 = 1526323) B1526323
theorem B3050945 : Blo 900574 3050945 := bstep (se 2 (by rfl) ⟨1144104, by rfl⟩ : syracuseStep 3050945 = 2288209) B2288209
theorem B2035187 : Blo 900574 2035187 := bstep (se 1 (by rfl) ⟨1526390, by rfl⟩ : syracuseStep 2035187 = 3052781) B3052781
theorem B6852113 : Blo 900574 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B2035223 : Blo 900574 2035223 := bstep (se 1 (by rfl) ⟨1526417, by rfl⟩ : syracuseStep 2035223 = 3052835) B3052835
theorem B1445465 : Blo 900574 1445465 := bstep (se 2 (by rfl) ⟨542049, by rfl⟩ : syracuseStep 1445465 = 1084099) B1084099
theorem B1543961 : Blo 900574 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B2166745 : Blo 900574 2166745 := bstep (se 2 (by rfl) ⟨812529, by rfl⟩ : syracuseStep 2166745 = 1625059) B1625059
theorem B3051485 : Blo 900574 3051485 := bstep (se 3 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 3051485 = 1144307) B1144307
theorem B2167361 : Blo 900574 2167361 := bstep (se 2 (by rfl) ⟨812760, by rfl⟩ : syracuseStep 2167361 = 1625521) B1625521
theorem B18551501 : Blo 900574 18551501 := bstep (se 3 (by rfl) ⟨3478406, by rfl⟩ : syracuseStep 18551501 = 6956813) B6956813
theorem B2200537 : Blo 900574 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B3052619 : Blo 900574 3052619 := bstep (se 1 (by rfl) ⟨2289464, by rfl⟩ : syracuseStep 3052619 = 4578929) B4578929
theorem B20092085 : Blo 900574 20092085 := bstep (se 5 (by rfl) ⟨941816, by rfl⟩ : syracuseStep 20092085 = 1883633) B1883633
theorem B3052889 : Blo 900574 3052889 := bstep (se 2 (by rfl) ⟨1144833, by rfl⟩ : syracuseStep 3052889 = 2289667) B2289667
theorem B3249715 : Blo 900574 3249715 := bstep (se 1 (by rfl) ⟨2437286, by rfl⟩ : syracuseStep 3249715 = 4874573) B4874573
theorem B1283735 : Blo 900574 1283735 := bstep (se 1 (by rfl) ⟨962801, by rfl⟩ : syracuseStep 1283735 = 1925603) B1925603
theorem B13014769 : Blo 900574 13014769 := bstep (se 2 (by rfl) ⟨4880538, by rfl⟩ : syracuseStep 13014769 = 9761077) B9761077
theorem B4331339 : Blo 900574 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B1710067 : Blo 900574 1710067 := bstep (se 1 (by rfl) ⟨1282550, by rfl⟩ : syracuseStep 1710067 = 2565101) B2565101
theorem B3905795 : Blo 900574 3905795 := bstep (se 1 (by rfl) ⟨2929346, by rfl⟩ : syracuseStep 3905795 = 5858693) B5858693
theorem B1710553 : Blo 900574 1710553 := bstep (se 2 (by rfl) ⟨641457, by rfl⟩ : syracuseStep 1710553 = 1282915) B1282915
theorem B5478929 : Blo 900574 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B1219097 : Blo 900574 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B3906193 : Blo 900574 3906193 := bstep (se 2 (by rfl) ⟨1464822, by rfl⟩ : syracuseStep 3906193 = 2929645) B2929645
theorem B4561757 : Blo 900574 4561757 := bstep (se 3 (by rfl) ⟨855329, by rfl⟩ : syracuseStep 4561757 = 1710659) B1710659
theorem B1711115 : Blo 900574 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B10296395 : Blo 900574 10296395 := bstep (se 1 (by rfl) ⟨7722296, by rfl⟩ : syracuseStep 10296395 = 15444593) B15444593
theorem B1645655 : Blo 900574 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B1711297 : Blo 900574 1711297 := bstep (se 2 (by rfl) ⟨641736, by rfl⟩ : syracuseStep 1711297 = 1283473) B1283473
theorem B1350923 : Blo 900574 1350923 := bstep (se 1 (by rfl) ⟨1013192, by rfl⟩ : syracuseStep 1350923 = 2026385) B2026385
theorem B1350935 : Blo 900574 1350935 := bstep (se 1 (by rfl) ⟨1013201, by rfl⟩ : syracuseStep 1350935 = 2026403) B2026403
theorem B6856001 : Blo 900574 6856001 := bstep (se 2 (by rfl) ⟨2571000, by rfl⟩ : syracuseStep 6856001 = 5142001) B5142001
theorem B1351001 : Blo 900574 1351001 := bstep (se 2 (by rfl) ⟨506625, by rfl⟩ : syracuseStep 1351001 = 1013251) B1013251
theorem B7708081 : Blo 900574 7708081 := bstep (se 2 (by rfl) ⟨2890530, by rfl⟩ : syracuseStep 7708081 = 5781061) B5781061
theorem B1351115 : Blo 900574 1351115 := bstep (se 1 (by rfl) ⟨1013336, by rfl⟩ : syracuseStep 1351115 = 2026673) B2026673
theorem B1351127 : Blo 900574 1351127 := bstep (se 1 (by rfl) ⟨1013345, by rfl⟩ : syracuseStep 1351127 = 2026691) B2026691
theorem B1318361 : Blo 900574 1318361 := bstep (se 2 (by rfl) ⟨494385, by rfl⟩ : syracuseStep 1318361 = 988771) B988771
theorem B1351193 : Blo 900574 1351193 := bstep (se 2 (by rfl) ⟨506697, by rfl⟩ : syracuseStep 1351193 = 1013395) B1013395
theorem B8691275 : Blo 900574 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B1351307 : Blo 900574 1351307 := bstep (se 1 (by rfl) ⟨1013480, by rfl⟩ : syracuseStep 1351307 = 2026961) B2026961
theorem B1351319 : Blo 900574 1351319 := bstep (se 1 (by rfl) ⟨1013489, by rfl⟩ : syracuseStep 1351319 = 2026979) B2026979
theorem B1351385 : Blo 900574 1351385 := bstep (se 2 (by rfl) ⟨506769, by rfl⟩ : syracuseStep 1351385 = 1013539) B1013539
theorem B1351499 : Blo 900574 1351499 := bstep (se 1 (by rfl) ⟨1013624, by rfl⟩ : syracuseStep 1351499 = 2027249) B2027249
theorem B1351511 : Blo 900574 1351511 := bstep (se 1 (by rfl) ⟨1013633, by rfl⟩ : syracuseStep 1351511 = 2027267) B2027267
theorem B2891609 : Blo 900574 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B1712011 : Blo 900574 1712011 := bstep (se 1 (by rfl) ⟨1284008, by rfl⟩ : syracuseStep 1712011 = 2568017) B2568017
theorem B1351577 : Blo 900574 1351577 := bstep (se 2 (by rfl) ⟨506841, by rfl⟩ : syracuseStep 1351577 = 1013683) B1013683
theorem B13868977 : Blo 900574 13868977 := bstep (se 2 (by rfl) ⟨5200866, by rfl⟩ : syracuseStep 13868977 = 10401733) B10401733
theorem B1712087 : Blo 900574 1712087 := bstep (se 1 (by rfl) ⟨1284065, by rfl⟩ : syracuseStep 1712087 = 2568131) B2568131
theorem B1351691 : Blo 900574 1351691 := bstep (se 1 (by rfl) ⟨1013768, by rfl⟩ : syracuseStep 1351691 = 2027537) B2027537
theorem B1351703 : Blo 900574 1351703 := bstep (se 1 (by rfl) ⟨1013777, by rfl⟩ : syracuseStep 1351703 = 2027555) B2027555
theorem B1351769 : Blo 900574 1351769 := bstep (se 2 (by rfl) ⟨506913, by rfl⟩ : syracuseStep 1351769 = 1013827) B1013827
theorem B1351883 : Blo 900574 1351883 := bstep (se 1 (by rfl) ⟨1013912, by rfl⟩ : syracuseStep 1351883 = 2027825) B2027825
theorem B8790221 : Blo 900574 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B1351895 : Blo 900574 1351895 := bstep (se 1 (by rfl) ⟨1013921, by rfl⟩ : syracuseStep 1351895 = 2027843) B2027843
theorem B1351961 : Blo 900574 1351961 := bstep (se 2 (by rfl) ⟨506985, by rfl⟩ : syracuseStep 1351961 = 1013971) B1013971
theorem B2171225 : Blo 900574 2171225 := bstep (se 2 (by rfl) ⟨814209, by rfl⟩ : syracuseStep 2171225 = 1628419) B1628419
theorem B1352075 : Blo 900574 1352075 := bstep (se 1 (by rfl) ⟨1014056, by rfl⟩ : syracuseStep 1352075 = 2028113) B2028113
theorem B1352087 : Blo 900574 1352087 := bstep (se 1 (by rfl) ⟨1014065, by rfl⟩ : syracuseStep 1352087 = 2028131) B2028131
theorem B2564531 : Blo 900574 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B1352153 : Blo 900574 1352153 := bstep (se 2 (by rfl) ⟨507057, by rfl⟩ : syracuseStep 1352153 = 1014115) B1014115
theorem B1286617 : Blo 900574 1286617 := bstep (se 2 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 1286617 = 964963) B964963
theorem B1352267 : Blo 900574 1352267 := bstep (se 1 (by rfl) ⟨1014200, by rfl⟩ : syracuseStep 1352267 = 2028401) B2028401
theorem B1352279 : Blo 900574 1352279 := bstep (se 1 (by rfl) ⟨1014209, by rfl⟩ : syracuseStep 1352279 = 2028419) B2028419
theorem B1712755 : Blo 900574 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B2564759 : Blo 900574 2564759 := bstep (se 1 (by rfl) ⟨1923569, by rfl⟩ : syracuseStep 2564759 = 3847139) B3847139
theorem B1352345 : Blo 900574 1352345 := bstep (se 2 (by rfl) ⟨507129, by rfl⟩ : syracuseStep 1352345 = 1014259) B1014259
theorem B2892505 : Blo 900574 2892505 := bstep (se 2 (by rfl) ⟨1084689, by rfl⟩ : syracuseStep 2892505 = 2169379) B2169379
theorem B1352459 : Blo 900574 1352459 := bstep (se 1 (by rfl) ⟨1014344, by rfl⟩ : syracuseStep 1352459 = 2028689) B2028689
theorem B1352471 : Blo 900574 1352471 := bstep (se 1 (by rfl) ⟨1014353, by rfl⟩ : syracuseStep 1352471 = 2028707) B2028707
theorem B1712983 : Blo 900574 1712983 := bstep (se 1 (by rfl) ⟨1284737, by rfl⟩ : syracuseStep 1712983 = 2569475) B2569475
theorem B1352537 : Blo 900574 1352537 := bstep (se 2 (by rfl) ⟨507201, by rfl⟩ : syracuseStep 1352537 = 1014403) B1014403
theorem B4563863 : Blo 900574 4563863 := bstep (se 1 (by rfl) ⟨3422897, by rfl⟩ : syracuseStep 4563863 = 6845795) B6845795
theorem B1713089 : Blo 900574 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B2565067 : Blo 900574 2565067 := bstep (se 1 (by rfl) ⟨1923800, by rfl⟩ : syracuseStep 2565067 = 3847601) B3847601
theorem B1352651 : Blo 900574 1352651 := bstep (se 1 (by rfl) ⟨1014488, by rfl⟩ : syracuseStep 1352651 = 2028977) B2028977
theorem B1352663 : Blo 900574 1352663 := bstep (se 1 (by rfl) ⟨1014497, by rfl⟩ : syracuseStep 1352663 = 2028995) B2028995
theorem B1352729 : Blo 900574 1352729 := bstep (se 2 (by rfl) ⟨507273, by rfl⟩ : syracuseStep 1352729 = 1014547) B1014547
theorem B1713241 : Blo 900574 1713241 := bstep (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) B1284931
theorem B1352843 : Blo 900574 1352843 := bstep (se 1 (by rfl) ⟨1014632, by rfl⟩ : syracuseStep 1352843 = 2029265) B2029265
theorem B1352855 : Blo 900574 1352855 := bstep (se 1 (by rfl) ⟨1014641, by rfl⟩ : syracuseStep 1352855 = 2029283) B2029283
theorem B1352921 : Blo 900574 1352921 := bstep (se 2 (by rfl) ⟨507345, by rfl⟩ : syracuseStep 1352921 = 1014691) B1014691
theorem B6857945 : Blo 900574 6857945 := bstep (se 2 (by rfl) ⟨2571729, by rfl⟩ : syracuseStep 6857945 = 5143459) B5143459
theorem B2565341 : Blo 900574 2565341 := bstep (se 3 (by rfl) ⟨481001, by rfl⟩ : syracuseStep 2565341 = 962003) B962003
theorem B2893121 : Blo 900574 2893121 := bstep (se 2 (by rfl) ⟨1084920, by rfl⟩ : syracuseStep 2893121 = 2169841) B2169841
theorem B1353035 : Blo 900574 1353035 := bstep (se 1 (by rfl) ⟨1014776, by rfl⟩ : syracuseStep 1353035 = 2029553) B2029553
theorem B1353047 : Blo 900574 1353047 := bstep (se 1 (by rfl) ⟨1014785, by rfl⟩ : syracuseStep 1353047 = 2029571) B2029571
theorem B1353113 : Blo 900574 1353113 := bstep (se 2 (by rfl) ⟨507417, by rfl⟩ : syracuseStep 1353113 = 1014835) B1014835
theorem B1353227 : Blo 900574 1353227 := bstep (se 1 (by rfl) ⟨1014920, by rfl⟩ : syracuseStep 1353227 = 2029841) B2029841
theorem B1353239 : Blo 900574 1353239 := bstep (se 1 (by rfl) ⟨1014929, by rfl⟩ : syracuseStep 1353239 = 2029859) B2029859
theorem B1353305 : Blo 900574 1353305 := bstep (se 2 (by rfl) ⟨507489, by rfl⟩ : syracuseStep 1353305 = 1014979) B1014979
theorem B1353419 : Blo 900574 1353419 := bstep (se 1 (by rfl) ⟨1015064, by rfl⟩ : syracuseStep 1353419 = 2030129) B2030129
theorem B1353431 : Blo 900574 1353431 := bstep (se 1 (by rfl) ⟨1015073, by rfl⟩ : syracuseStep 1353431 = 2030147) B2030147
theorem B1353497 : Blo 900574 1353497 := bstep (se 2 (by rfl) ⟨507561, by rfl⟩ : syracuseStep 1353497 = 1015123) B1015123
theorem B7808813 : Blo 900574 7808813 := bstep (se 3 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 7808813 = 2928305) B2928305
theorem B1353611 : Blo 900574 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B1353623 : Blo 900574 1353623 := bstep (se 1 (by rfl) ⟨1015217, by rfl⟩ : syracuseStep 1353623 = 2030435) B2030435
theorem B927703 : Blo 900574 927703 := bstep (se 1 (by rfl) ⟨695777, by rfl⟩ : syracuseStep 927703 = 1391555) B1391555
theorem B1353689 : Blo 900574 1353689 := bstep (se 2 (by rfl) ⟨507633, by rfl⟩ : syracuseStep 1353689 = 1015267) B1015267
theorem B1353803 : Blo 900574 1353803 := bstep (se 1 (by rfl) ⟨1015352, by rfl⟩ : syracuseStep 1353803 = 2030705) B2030705
theorem B1353815 : Blo 900574 1353815 := bstep (se 1 (by rfl) ⟨1015361, by rfl⟩ : syracuseStep 1353815 = 2030723) B2030723
theorem B1321099 : Blo 900574 1321099 := bstep (se 1 (by rfl) ⟨990824, by rfl⟩ : syracuseStep 1321099 = 1981649) B1981649
theorem B3254417 : Blo 900574 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B1353881 : Blo 900574 1353881 := bstep (se 2 (by rfl) ⟨507705, by rfl⟩ : syracuseStep 1353881 = 1015411) B1015411
theorem B3254489 : Blo 900574 3254489 := bstep (se 2 (by rfl) ⟨1220433, by rfl⟩ : syracuseStep 3254489 = 2440867) B2440867
theorem B1353995 : Blo 900574 1353995 := bstep (se 1 (by rfl) ⟨1015496, by rfl⟩ : syracuseStep 1353995 = 2030993) B2030993
theorem B1354007 : Blo 900574 1354007 := bstep (se 1 (by rfl) ⟨1015505, by rfl⟩ : syracuseStep 1354007 = 2031011) B2031011
theorem B1354073 : Blo 900574 1354073 := bstep (se 2 (by rfl) ⟨507777, by rfl⟩ : syracuseStep 1354073 = 1015555) B1015555
theorem B1714547 : Blo 900574 1714547 := bstep (se 1 (by rfl) ⟨1285910, by rfl⟩ : syracuseStep 1714547 = 2571821) B2571821
theorem B1354187 : Blo 900574 1354187 := bstep (se 1 (by rfl) ⟨1015640, by rfl⟩ : syracuseStep 1354187 = 2031281) B2031281
theorem B1354199 : Blo 900574 1354199 := bstep (se 1 (by rfl) ⟨1015649, by rfl⟩ : syracuseStep 1354199 = 2031299) B2031299
theorem B1714699 : Blo 900574 1714699 := bstep (se 1 (by rfl) ⟨1286024, by rfl⟩ : syracuseStep 1714699 = 2572049) B2572049
theorem B1354265 : Blo 900574 1354265 := bstep (se 2 (by rfl) ⟨507849, by rfl⟩ : syracuseStep 1354265 = 1015699) B1015699
theorem B1354379 : Blo 900574 1354379 := bstep (se 1 (by rfl) ⟨1015784, by rfl⟩ : syracuseStep 1354379 = 2031569) B2031569
theorem B6498967 : Blo 900574 6498967 := bstep (se 1 (by rfl) ⟨4874225, by rfl⟩ : syracuseStep 6498967 = 9748451) B9748451
theorem B1354391 : Blo 900574 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B1354457 : Blo 900574 1354457 := bstep (se 2 (by rfl) ⟨507921, by rfl⟩ : syracuseStep 1354457 = 1015843) B1015843
theorem B32877377 : Blo 900574 32877377 := bstep (se 2 (by rfl) ⟨12329016, by rfl⟩ : syracuseStep 32877377 = 24658033) B24658033
theorem B1354571 : Blo 900574 1354571 := bstep (se 1 (by rfl) ⟨1015928, by rfl⟩ : syracuseStep 1354571 = 2031857) B2031857
theorem B1354583 : Blo 900574 1354583 := bstep (se 1 (by rfl) ⟨1015937, by rfl⟩ : syracuseStep 1354583 = 2031875) B2031875
theorem B1715033 : Blo 900574 1715033 := bstep (se 2 (by rfl) ⟨643137, by rfl⟩ : syracuseStep 1715033 = 1286275) B1286275
theorem B3910493 : Blo 900574 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B1354649 : Blo 900574 1354649 := bstep (se 2 (by rfl) ⟨507993, by rfl⟩ : syracuseStep 1354649 = 1015987) B1015987
theorem B1354763 : Blo 900574 1354763 := bstep (se 1 (by rfl) ⟨1016072, by rfl⟩ : syracuseStep 1354763 = 2032145) B2032145
theorem B5778449 : Blo 900574 5778449 := bstep (se 2 (by rfl) ⟨2166918, by rfl⟩ : syracuseStep 5778449 = 4333837) B4333837
theorem B2436119 : Blo 900574 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B1354775 : Blo 900574 1354775 := bstep (se 1 (by rfl) ⟨1016081, by rfl⟩ : syracuseStep 1354775 = 2032163) B2032163
theorem B1027127 : Blo 900574 1027127 := bstep (se 1 (by rfl) ⟨770345, by rfl⟩ : syracuseStep 1027127 = 1540691) B1540691
theorem B9743435 : Blo 900574 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B1977433 : Blo 900574 1977433 := bstep (se 2 (by rfl) ⟨741537, by rfl⟩ : syracuseStep 1977433 = 1483075) B1483075
theorem B1354841 : Blo 900574 1354841 := bstep (se 2 (by rfl) ⟨508065, by rfl⟩ : syracuseStep 1354841 = 1016131) B1016131
theorem B1354955 : Blo 900574 1354955 := bstep (se 1 (by rfl) ⟨1016216, by rfl⟩ : syracuseStep 1354955 = 2032433) B2032433
theorem B1354967 : Blo 900574 1354967 := bstep (se 1 (by rfl) ⟨1016225, by rfl⟩ : syracuseStep 1354967 = 2032451) B2032451
theorem B2567447 : Blo 900574 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B1355033 : Blo 900574 1355033 := bstep (se 2 (by rfl) ⟨508137, by rfl⟩ : syracuseStep 1355033 = 1016275) B1016275
theorem B4337027 : Blo 900574 4337027 := bstep (se 1 (by rfl) ⟨3252770, by rfl⟩ : syracuseStep 4337027 = 6505541) B6505541
theorem B1355147 : Blo 900574 1355147 := bstep (se 1 (by rfl) ⟨1016360, by rfl⟩ : syracuseStep 1355147 = 2032721) B2032721
theorem B1355159 : Blo 900574 1355159 := bstep (se 1 (by rfl) ⟨1016369, by rfl⟩ : syracuseStep 1355159 = 2032739) B2032739
theorem B1715671 : Blo 900574 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B1355225 : Blo 900574 1355225 := bstep (se 2 (by rfl) ⟨508209, by rfl⟩ : syracuseStep 1355225 = 1016419) B1016419
theorem B1355339 : Blo 900574 1355339 := bstep (se 1 (by rfl) ⟨1016504, by rfl⟩ : syracuseStep 1355339 = 2033009) B2033009
theorem B1355351 : Blo 900574 1355351 := bstep (se 1 (by rfl) ⟨1016513, by rfl⟩ : syracuseStep 1355351 = 2033027) B2033027
theorem B4402781 : Blo 900574 4402781 := bstep (se 3 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 4402781 = 1651043) B1651043
theorem B1355417 : Blo 900574 1355417 := bstep (se 2 (by rfl) ⟨508281, by rfl⟩ : syracuseStep 1355417 = 1016563) B1016563
theorem B3124939 : Blo 900574 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B962263 : Blo 900574 962263 := bstep (se 1 (by rfl) ⟨721697, by rfl⟩ : syracuseStep 962263 = 1443395) B1443395
theorem B2895581 : Blo 900574 2895581 := bstep (se 3 (by rfl) ⟨542921, by rfl⟩ : syracuseStep 2895581 = 1085843) B1085843
theorem B1355531 : Blo 900574 1355531 := bstep (se 1 (by rfl) ⟨1016648, by rfl⟩ : syracuseStep 1355531 = 2033297) B2033297
theorem B3419921 : Blo 900574 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B1355543 : Blo 900574 1355543 := bstep (se 1 (by rfl) ⟨1016657, by rfl⟩ : syracuseStep 1355543 = 2033315) B2033315
theorem B1355609 : Blo 900574 1355609 := bstep (se 2 (by rfl) ⟨508353, by rfl⟩ : syracuseStep 1355609 = 1016707) B1016707
theorem B2895709 : Blo 900574 2895709 := bstep (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) B1085891
theorem B1355723 : Blo 900574 1355723 := bstep (se 1 (by rfl) ⟨1016792, by rfl⟩ : syracuseStep 1355723 = 2033585) B2033585
theorem B1355735 : Blo 900574 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B7712729 : Blo 900574 7712729 := bstep (se 2 (by rfl) ⟨2892273, by rfl⟩ : syracuseStep 7712729 = 5784547) B5784547
theorem B1355801 : Blo 900574 1355801 := bstep (se 2 (by rfl) ⟨508425, by rfl⟩ : syracuseStep 1355801 = 1016851) B1016851
theorem B2568257 : Blo 900574 2568257 := bstep (se 2 (by rfl) ⟨963096, by rfl⟩ : syracuseStep 2568257 = 1926193) B1926193
theorem B7319645 : Blo 900574 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B2895965 : Blo 900574 2895965 := bstep (se 3 (by rfl) ⟨542993, by rfl⟩ : syracuseStep 2895965 = 1085987) B1085987
theorem B1355915 : Blo 900574 1355915 := bstep (se 1 (by rfl) ⟨1016936, by rfl⟩ : syracuseStep 1355915 = 2033873) B2033873
theorem B1355927 : Blo 900574 1355927 := bstep (se 1 (by rfl) ⟨1016945, by rfl⟩ : syracuseStep 1355927 = 2033891) B2033891
theorem B1519769 : Blo 900574 1519769 := bstep (se 2 (by rfl) ⟨569913, by rfl⟩ : syracuseStep 1519769 = 1139827) B1139827
theorem B3420377 : Blo 900574 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B1355993 : Blo 900574 1355993 := bstep (se 2 (by rfl) ⟨508497, by rfl⟩ : syracuseStep 1355993 = 1016995) B1016995
theorem B1716491 : Blo 900574 1716491 := bstep (se 1 (by rfl) ⟨1287368, by rfl⟩ : syracuseStep 1716491 = 2574737) B2574737
theorem B1519897 : Blo 900574 1519897 := bstep (se 2 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 1519897 = 1139923) B1139923
theorem B12366125 : Blo 900574 12366125 := bstep (se 3 (by rfl) ⟨2318648, by rfl⟩ : syracuseStep 12366125 = 4637297) B4637297
theorem B1716545 : Blo 900574 1716545 := bstep (se 2 (by rfl) ⟨643704, by rfl⟩ : syracuseStep 1716545 = 1287409) B1287409
theorem B1356107 : Blo 900574 1356107 := bstep (se 1 (by rfl) ⟨1017080, by rfl⟩ : syracuseStep 1356107 = 2034161) B2034161
theorem B1356119 : Blo 900574 1356119 := bstep (se 1 (by rfl) ⟨1017089, by rfl⟩ : syracuseStep 1356119 = 2034179) B2034179
theorem B2601305 : Blo 900574 2601305 := bstep (se 2 (by rfl) ⟨975489, by rfl⟩ : syracuseStep 2601305 = 1950979) B1950979
theorem B4567427 : Blo 900574 4567427 := bstep (se 1 (by rfl) ⟨3425570, by rfl⟩ : syracuseStep 4567427 = 6851141) B6851141
theorem B1356185 : Blo 900574 1356185 := bstep (se 2 (by rfl) ⟨508569, by rfl⟩ : syracuseStep 1356185 = 1017139) B1017139
theorem B3420589 : Blo 900574 3420589 := bstep (se 3 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 3420589 = 1282721) B1282721
theorem B1356299 : Blo 900574 1356299 := bstep (se 1 (by rfl) ⟨1017224, by rfl⟩ : syracuseStep 1356299 = 2034449) B2034449
theorem B1356311 : Blo 900574 1356311 := bstep (se 1 (by rfl) ⟨1017233, by rfl⟩ : syracuseStep 1356311 = 2034467) B2034467
theorem B6861347 : Blo 900574 6861347 := bstep (se 1 (by rfl) ⟨5146010, by rfl⟩ : syracuseStep 6861347 = 10292021) B10292021
theorem B1356377 : Blo 900574 1356377 := bstep (se 2 (by rfl) ⟨508641, by rfl⟩ : syracuseStep 1356377 = 1017283) B1017283
theorem B1028759 : Blo 900574 1028759 := bstep (se 1 (by rfl) ⟨771569, by rfl⟩ : syracuseStep 1028759 = 1543139) B1543139
theorem B1356491 : Blo 900574 1356491 := bstep (se 1 (by rfl) ⟨1017368, by rfl⟩ : syracuseStep 1356491 = 2034737) B2034737
theorem B1356503 : Blo 900574 1356503 := bstep (se 1 (by rfl) ⟨1017377, by rfl⟩ : syracuseStep 1356503 = 2034755) B2034755
theorem B3420893 : Blo 900574 3420893 := bstep (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) B1282835
theorem B1356569 : Blo 900574 1356569 := bstep (se 2 (by rfl) ⟨508713, by rfl⟩ : syracuseStep 1356569 = 1017427) B1017427
theorem B1520471 : Blo 900574 1520471 := bstep (se 1 (by rfl) ⟨1140353, by rfl⟩ : syracuseStep 1520471 = 2280707) B2280707
theorem B1356683 : Blo 900574 1356683 := bstep (se 1 (by rfl) ⟨1017512, by rfl⟩ : syracuseStep 1356683 = 2035025) B2035025
theorem B1356695 : Blo 900574 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B1520599 : Blo 900574 1520599 := bstep (se 1 (by rfl) ⟨1140449, by rfl⟩ : syracuseStep 1520599 = 2280899) B2280899
theorem B1356761 : Blo 900574 1356761 := bstep (se 2 (by rfl) ⟨508785, by rfl⟩ : syracuseStep 1356761 = 1017571) B1017571
theorem B963895 : Blo 900574 963895 := bstep (se 1 (by rfl) ⟨722921, by rfl⟩ : syracuseStep 963895 = 1445843) B1445843
theorem B1521227 : Blo 900574 1521227 := bstep (se 1 (by rfl) ⟨1140920, by rfl⟩ : syracuseStep 1521227 = 2281841) B2281841
theorem B3094105 : Blo 900574 3094105 := bstep (se 2 (by rfl) ⟨1160289, by rfl⟩ : syracuseStep 3094105 = 2320579) B2320579
theorem B5289623 : Blo 900574 5289623 := bstep (se 1 (by rfl) ⟨3967217, by rfl⟩ : syracuseStep 5289623 = 7934435) B7934435
theorem B2569907 : Blo 900574 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B1521355 : Blo 900574 1521355 := bstep (se 1 (by rfl) ⟨1141016, by rfl⟩ : syracuseStep 1521355 = 2282033) B2282033
theorem B2569931 : Blo 900574 2569931 := bstep (se 1 (by rfl) ⟨1927448, by rfl⟩ : syracuseStep 2569931 = 3854897) B3854897
theorem B1521497 : Blo 900574 1521497 := bstep (se 2 (by rfl) ⟨570561, by rfl⟩ : syracuseStep 1521497 = 1141123) B1141123
theorem B1521625 : Blo 900574 1521625 := bstep (se 2 (by rfl) ⟨570609, by rfl⟩ : syracuseStep 1521625 = 1141219) B1141219
theorem B964715 : Blo 900574 964715 := bstep (se 1 (by rfl) ⟨723536, by rfl⟩ : syracuseStep 964715 = 1447073) B1447073
theorem B15644933 : Blo 900574 15644933 := bstep (se 4 (by rfl) ⟨1466712, by rfl⟩ : syracuseStep 15644933 = 2933425) B2933425
theorem B56342897 : Blo 900574 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B2570717 : Blo 900574 2570717 := bstep (se 3 (by rfl) ⟨482009, by rfl⟩ : syracuseStep 2570717 = 964019) B964019
theorem B3258883 : Blo 900574 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B1522199 : Blo 900574 1522199 := bstep (se 1 (by rfl) ⟨1141649, by rfl⟩ : syracuseStep 1522199 = 2283299) B2283299
theorem B1522327 : Blo 900574 1522327 := bstep (se 1 (by rfl) ⟨1141745, by rfl⟩ : syracuseStep 1522327 = 2283491) B2283491
theorem B3652427 : Blo 900574 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B6175619 : Blo 900574 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B965783 : Blo 900574 965783 := bstep (se 1 (by rfl) ⟨724337, by rfl⟩ : syracuseStep 965783 = 1448675) B1448675
theorem B1031383 : Blo 900574 1031383 := bstep (se 1 (by rfl) ⟨773537, by rfl⟩ : syracuseStep 1031383 = 1547075) B1547075
theorem B3423491 : Blo 900574 3423491 := bstep (se 1 (by rfl) ⟨2567618, by rfl⟩ : syracuseStep 3423491 = 5135237) B5135237
theorem B1522955 : Blo 900574 1522955 := bstep (se 1 (by rfl) ⟨1142216, by rfl⟩ : syracuseStep 1522955 = 2284433) B2284433
theorem B3423505 : Blo 900574 3423505 := bstep (se 2 (by rfl) ⟨1283814, by rfl⟩ : syracuseStep 3423505 = 2567629) B2567629
theorem B3849565 : Blo 900574 3849565 := bstep (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) B1443587
theorem B1523083 : Blo 900574 1523083 := bstep (se 1 (by rfl) ⟨1142312, by rfl⟩ : syracuseStep 1523083 = 2284625) B2284625
theorem B16465331 : Blo 900574 16465331 := bstep (se 1 (by rfl) ⟨12348998, by rfl⟩ : syracuseStep 16465331 = 24697997) B24697997
theorem B3259865 : Blo 900574 3259865 := bstep (se 2 (by rfl) ⟨1222449, by rfl⟩ : syracuseStep 3259865 = 2444899) B2444899
theorem B900587 : Blo 900574 900587 := bstep (se 1 (by rfl) ⟨675440, by rfl⟩ : syracuseStep 900587 = 1350881) B1350881
theorem B900599 : Blo 900574 900599 := bstep (se 1 (by rfl) ⟨675449, by rfl⟩ : syracuseStep 900599 = 1350899) B1350899
theorem B900619 : Blo 900574 900619 := bstep (se 1 (by rfl) ⟨675464, by rfl⟩ : syracuseStep 900619 = 1350929) B1350929
theorem B3259921 : Blo 900574 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B900631 : Blo 900574 900631 := bstep (se 1 (by rfl) ⟨675473, by rfl⟩ : syracuseStep 900631 = 1350947) B1350947
theorem B1523225 : Blo 900574 1523225 := bstep (se 2 (by rfl) ⟨571209, by rfl⟩ : syracuseStep 1523225 = 1142419) B1142419
theorem B900651 : Blo 900574 900651 := bstep (se 1 (by rfl) ⟨675488, by rfl⟩ : syracuseStep 900651 = 1350977) B1350977
theorem B900663 : Blo 900574 900663 := bstep (se 1 (by rfl) ⟨675497, by rfl⟩ : syracuseStep 900663 = 1350995) B1350995
theorem B3423809 : Blo 900574 3423809 := bstep (se 2 (by rfl) ⟨1283928, by rfl⟩ : syracuseStep 3423809 = 2567857) B2567857
theorem B900683 : Blo 900574 900683 := bstep (se 1 (by rfl) ⟨675512, by rfl⟩ : syracuseStep 900683 = 1351025) B1351025
theorem B900695 : Blo 900574 900695 := bstep (se 1 (by rfl) ⟨675521, by rfl⟩ : syracuseStep 900695 = 1351043) B1351043
theorem B900715 : Blo 900574 900715 := bstep (se 1 (by rfl) ⟨675536, by rfl⟩ : syracuseStep 900715 = 1351073) B1351073
theorem B900727 : Blo 900574 900727 := bstep (se 1 (by rfl) ⟨675545, by rfl⟩ : syracuseStep 900727 = 1351091) B1351091
theorem B900747 : Blo 900574 900747 := bstep (se 1 (by rfl) ⟨675560, by rfl⟩ : syracuseStep 900747 = 1351121) B1351121
theorem B900759 : Blo 900574 900759 := bstep (se 1 (by rfl) ⟨675569, by rfl⟩ : syracuseStep 900759 = 1351139) B1351139
theorem B1523353 : Blo 900574 1523353 := bstep (se 2 (by rfl) ⟨571257, by rfl⟩ : syracuseStep 1523353 = 1142515) B1142515
theorem B900779 : Blo 900574 900779 := bstep (se 1 (by rfl) ⟨675584, by rfl⟩ : syracuseStep 900779 = 1351169) B1351169
theorem B900791 : Blo 900574 900791 := bstep (se 1 (by rfl) ⟨675593, by rfl⟩ : syracuseStep 900791 = 1351187) B1351187
theorem B2440897 : Blo 900574 2440897 := bstep (se 2 (by rfl) ⟨915336, by rfl⟩ : syracuseStep 2440897 = 1830673) B1830673
theorem B900811 : Blo 900574 900811 := bstep (se 1 (by rfl) ⟨675608, by rfl⟩ : syracuseStep 900811 = 1351217) B1351217
theorem B900823 : Blo 900574 900823 := bstep (se 1 (by rfl) ⟨675617, by rfl⟩ : syracuseStep 900823 = 1351235) B1351235
theorem B900843 : Blo 900574 900843 := bstep (se 1 (by rfl) ⟨675632, by rfl⟩ : syracuseStep 900843 = 1351265) B1351265
theorem B900855 : Blo 900574 900855 := bstep (se 1 (by rfl) ⟨675641, by rfl⟩ : syracuseStep 900855 = 1351283) B1351283
theorem B900875 : Blo 900574 900875 := bstep (se 1 (by rfl) ⟨675656, by rfl⟩ : syracuseStep 900875 = 1351313) B1351313
theorem B900887 : Blo 900574 900887 := bstep (se 1 (by rfl) ⟨675665, by rfl⟩ : syracuseStep 900887 = 1351331) B1351331
theorem B3653399 : Blo 900574 3653399 := bstep (se 1 (by rfl) ⟨2740049, by rfl⟩ : syracuseStep 3653399 = 5480099) B5480099
theorem B900907 : Blo 900574 900907 := bstep (se 1 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 900907 = 1351361) B1351361
theorem B900919 : Blo 900574 900919 := bstep (se 1 (by rfl) ⟨675689, by rfl⟩ : syracuseStep 900919 = 1351379) B1351379
theorem B8666945 : Blo 900574 8666945 := bstep (se 2 (by rfl) ⟨3250104, by rfl⟩ : syracuseStep 8666945 = 6500209) B6500209
theorem B900939 : Blo 900574 900939 := bstep (se 1 (by rfl) ⟨675704, by rfl⟩ : syracuseStep 900939 = 1351409) B1351409
theorem B900951 : Blo 900574 900951 := bstep (se 1 (by rfl) ⟨675713, by rfl⟩ : syracuseStep 900951 = 1351427) B1351427
theorem B900971 : Blo 900574 900971 := bstep (se 1 (by rfl) ⟨675728, by rfl⟩ : syracuseStep 900971 = 1351457) B1351457
theorem B900983 : Blo 900574 900983 := bstep (se 1 (by rfl) ⟨675737, by rfl⟩ : syracuseStep 900983 = 1351475) B1351475
theorem B901003 : Blo 900574 901003 := bstep (se 1 (by rfl) ⟨675752, by rfl⟩ : syracuseStep 901003 = 1351505) B1351505
theorem B901015 : Blo 900574 901015 := bstep (se 1 (by rfl) ⟨675761, by rfl⟩ : syracuseStep 901015 = 1351523) B1351523
theorem B901035 : Blo 900574 901035 := bstep (se 1 (by rfl) ⟨675776, by rfl⟩ : syracuseStep 901035 = 1351553) B1351553
theorem B901047 : Blo 900574 901047 := bstep (se 1 (by rfl) ⟨675785, by rfl⟩ : syracuseStep 901047 = 1351571) B1351571
theorem B901067 : Blo 900574 901067 := bstep (se 1 (by rfl) ⟨675800, by rfl⟩ : syracuseStep 901067 = 1351601) B1351601
theorem B901079 : Blo 900574 901079 := bstep (se 1 (by rfl) ⟨675809, by rfl⟩ : syracuseStep 901079 = 1351619) B1351619
theorem B901099 : Blo 900574 901099 := bstep (se 1 (by rfl) ⟨675824, by rfl⟩ : syracuseStep 901099 = 1351649) B1351649
theorem B901111 : Blo 900574 901111 := bstep (se 1 (by rfl) ⟨675833, by rfl⟩ : syracuseStep 901111 = 1351667) B1351667
theorem B901131 : Blo 900574 901131 := bstep (se 1 (by rfl) ⟨675848, by rfl⟩ : syracuseStep 901131 = 1351697) B1351697
theorem B4571153 : Blo 900574 4571153 := bstep (se 2 (by rfl) ⟨1714182, by rfl⟩ : syracuseStep 4571153 = 3428365) B3428365
theorem B901143 : Blo 900574 901143 := bstep (se 1 (by rfl) ⟨675857, by rfl⟩ : syracuseStep 901143 = 1351715) B1351715
theorem B901163 : Blo 900574 901163 := bstep (se 1 (by rfl) ⟨675872, by rfl⟩ : syracuseStep 901163 = 1351745) B1351745
theorem B901175 : Blo 900574 901175 := bstep (se 1 (by rfl) ⟨675881, by rfl⟩ : syracuseStep 901175 = 1351763) B1351763
theorem B901195 : Blo 900574 901195 := bstep (se 1 (by rfl) ⟨675896, by rfl⟩ : syracuseStep 901195 = 1351793) B1351793
theorem B901207 : Blo 900574 901207 := bstep (se 1 (by rfl) ⟨675905, by rfl⟩ : syracuseStep 901207 = 1351811) B1351811
theorem B901227 : Blo 900574 901227 := bstep (se 1 (by rfl) ⟨675920, by rfl⟩ : syracuseStep 901227 = 1351841) B1351841
theorem B901239 : Blo 900574 901239 := bstep (se 1 (by rfl) ⟨675929, by rfl⟩ : syracuseStep 901239 = 1351859) B1351859
theorem B901259 : Blo 900574 901259 := bstep (se 1 (by rfl) ⟨675944, by rfl⟩ : syracuseStep 901259 = 1351889) B1351889
theorem B901271 : Blo 900574 901271 := bstep (se 1 (by rfl) ⟨675953, by rfl⟩ : syracuseStep 901271 = 1351907) B1351907
theorem B8667287 : Blo 900574 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B901291 : Blo 900574 901291 := bstep (se 1 (by rfl) ⟨675968, by rfl⟩ : syracuseStep 901291 = 1351937) B1351937
theorem B4571315 : Blo 900574 4571315 := bstep (se 1 (by rfl) ⟨3428486, by rfl⟩ : syracuseStep 4571315 = 6856973) B6856973
theorem B901303 : Blo 900574 901303 := bstep (se 1 (by rfl) ⟨675977, by rfl⟩ : syracuseStep 901303 = 1351955) B1351955
theorem B901323 : Blo 900574 901323 := bstep (se 1 (by rfl) ⟨675992, by rfl⟩ : syracuseStep 901323 = 1351985) B1351985
theorem B901335 : Blo 900574 901335 := bstep (se 1 (by rfl) ⟨676001, by rfl⟩ : syracuseStep 901335 = 1352003) B1352003
theorem B1523927 : Blo 900574 1523927 := bstep (se 1 (by rfl) ⟨1142945, by rfl⟩ : syracuseStep 1523927 = 2285891) B2285891
theorem B2572505 : Blo 900574 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B3424477 : Blo 900574 3424477 := bstep (se 3 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 3424477 = 1284179) B1284179
theorem B901355 : Blo 900574 901355 := bstep (se 1 (by rfl) ⟨676016, by rfl⟩ : syracuseStep 901355 = 1352033) B1352033
theorem B901367 : Blo 900574 901367 := bstep (se 1 (by rfl) ⟨676025, by rfl⟩ : syracuseStep 901367 = 1352051) B1352051
theorem B901387 : Blo 900574 901387 := bstep (se 1 (by rfl) ⟨676040, by rfl⟩ : syracuseStep 901387 = 1352081) B1352081
theorem B901399 : Blo 900574 901399 := bstep (se 1 (by rfl) ⟨676049, by rfl⟩ : syracuseStep 901399 = 1352099) B1352099
theorem B901419 : Blo 900574 901419 := bstep (se 1 (by rfl) ⟨676064, by rfl⟩ : syracuseStep 901419 = 1352129) B1352129
theorem B901431 : Blo 900574 901431 := bstep (se 1 (by rfl) ⟨676073, by rfl⟩ : syracuseStep 901431 = 1352147) B1352147
theorem B11583809 : Blo 900574 11583809 := bstep (se 2 (by rfl) ⟨4343928, by rfl⟩ : syracuseStep 11583809 = 8687857) B8687857
theorem B901451 : Blo 900574 901451 := bstep (se 1 (by rfl) ⟨676088, by rfl⟩ : syracuseStep 901451 = 1352177) B1352177
theorem B901463 : Blo 900574 901463 := bstep (se 1 (by rfl) ⟨676097, by rfl⟩ : syracuseStep 901463 = 1352195) B1352195
theorem B1524055 : Blo 900574 1524055 := bstep (se 1 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 1524055 = 2286083) B2286083
theorem B901483 : Blo 900574 901483 := bstep (se 1 (by rfl) ⟨676112, by rfl⟩ : syracuseStep 901483 = 1352225) B1352225
theorem B901495 : Blo 900574 901495 := bstep (se 1 (by rfl) ⟨676121, by rfl⟩ : syracuseStep 901495 = 1352243) B1352243
theorem B901515 : Blo 900574 901515 := bstep (se 1 (by rfl) ⟨676136, by rfl⟩ : syracuseStep 901515 = 1352273) B1352273
theorem B901527 : Blo 900574 901527 := bstep (se 1 (by rfl) ⟨676145, by rfl⟩ : syracuseStep 901527 = 1352291) B1352291
theorem B901547 : Blo 900574 901547 := bstep (se 1 (by rfl) ⟨676160, by rfl⟩ : syracuseStep 901547 = 1352321) B1352321
theorem B901559 : Blo 900574 901559 := bstep (se 1 (by rfl) ⟨676169, by rfl⟩ : syracuseStep 901559 = 1352339) B1352339
theorem B901579 : Blo 900574 901579 := bstep (se 1 (by rfl) ⟨676184, by rfl⟩ : syracuseStep 901579 = 1352369) B1352369
theorem B901591 : Blo 900574 901591 := bstep (se 1 (by rfl) ⟨676193, by rfl⟩ : syracuseStep 901591 = 1352387) B1352387
theorem B901611 : Blo 900574 901611 := bstep (se 1 (by rfl) ⟨676208, by rfl⟩ : syracuseStep 901611 = 1352417) B1352417
theorem B901623 : Blo 900574 901623 := bstep (se 1 (by rfl) ⟨676217, by rfl⟩ : syracuseStep 901623 = 1352435) B1352435
theorem B901643 : Blo 900574 901643 := bstep (se 1 (by rfl) ⟨676232, by rfl⟩ : syracuseStep 901643 = 1352465) B1352465
theorem B901655 : Blo 900574 901655 := bstep (se 1 (by rfl) ⟨676241, by rfl⟩ : syracuseStep 901655 = 1352483) B1352483
theorem B2572823 : Blo 900574 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B901675 : Blo 900574 901675 := bstep (se 1 (by rfl) ⟨676256, by rfl⟩ : syracuseStep 901675 = 1352513) B1352513
theorem B901687 : Blo 900574 901687 := bstep (se 1 (by rfl) ⟨676265, by rfl⟩ : syracuseStep 901687 = 1352531) B1352531
theorem B901707 : Blo 900574 901707 := bstep (se 1 (by rfl) ⟨676280, by rfl⟩ : syracuseStep 901707 = 1352561) B1352561
theorem B901719 : Blo 900574 901719 := bstep (se 1 (by rfl) ⟨676289, by rfl⟩ : syracuseStep 901719 = 1352579) B1352579
theorem B5489245 : Blo 900574 5489245 := bstep (se 3 (by rfl) ⟨1029233, by rfl⟩ : syracuseStep 5489245 = 2058467) B2058467
theorem B901739 : Blo 900574 901739 := bstep (se 1 (by rfl) ⟨676304, by rfl⟩ : syracuseStep 901739 = 1352609) B1352609
theorem B901751 : Blo 900574 901751 := bstep (se 1 (by rfl) ⟨676313, by rfl⟩ : syracuseStep 901751 = 1352627) B1352627
theorem B901771 : Blo 900574 901771 := bstep (se 1 (by rfl) ⟨676328, by rfl⟩ : syracuseStep 901771 = 1352657) B1352657
theorem B3850897 : Blo 900574 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B901783 : Blo 900574 901783 := bstep (se 1 (by rfl) ⟨676337, by rfl⟩ : syracuseStep 901783 = 1352675) B1352675
theorem B901803 : Blo 900574 901803 := bstep (se 1 (by rfl) ⟨676352, by rfl⟩ : syracuseStep 901803 = 1352705) B1352705
theorem B901815 : Blo 900574 901815 := bstep (se 1 (by rfl) ⟨676361, by rfl⟩ : syracuseStep 901815 = 1352723) B1352723
theorem B901835 : Blo 900574 901835 := bstep (se 1 (by rfl) ⟨676376, by rfl⟩ : syracuseStep 901835 = 1352753) B1352753
theorem B901847 : Blo 900574 901847 := bstep (se 1 (by rfl) ⟨676385, by rfl⟩ : syracuseStep 901847 = 1352771) B1352771
theorem B901867 : Blo 900574 901867 := bstep (se 1 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 901867 = 1352801) B1352801
theorem B901879 : Blo 900574 901879 := bstep (se 1 (by rfl) ⟨676409, by rfl⟩ : syracuseStep 901879 = 1352819) B1352819
theorem B901899 : Blo 900574 901899 := bstep (se 1 (by rfl) ⟨676424, by rfl⟩ : syracuseStep 901899 = 1352849) B1352849
theorem B901911 : Blo 900574 901911 := bstep (se 1 (by rfl) ⟨676433, by rfl⟩ : syracuseStep 901911 = 1352867) B1352867
theorem B901931 : Blo 900574 901931 := bstep (se 1 (by rfl) ⟨676448, by rfl⟩ : syracuseStep 901931 = 1352897) B1352897
theorem B901943 : Blo 900574 901943 := bstep (se 1 (by rfl) ⟨676457, by rfl⟩ : syracuseStep 901943 = 1352915) B1352915
theorem B901963 : Blo 900574 901963 := bstep (se 1 (by rfl) ⟨676472, by rfl⟩ : syracuseStep 901963 = 1352945) B1352945
theorem B901975 : Blo 900574 901975 := bstep (se 1 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 901975 = 1352963) B1352963
theorem B901995 : Blo 900574 901995 := bstep (se 1 (by rfl) ⟨676496, by rfl⟩ : syracuseStep 901995 = 1352993) B1352993
theorem B902007 : Blo 900574 902007 := bstep (se 1 (by rfl) ⟨676505, by rfl⟩ : syracuseStep 902007 = 1353011) B1353011
theorem B902027 : Blo 900574 902027 := bstep (se 1 (by rfl) ⟨676520, by rfl⟩ : syracuseStep 902027 = 1353041) B1353041
theorem B902039 : Blo 900574 902039 := bstep (se 1 (by rfl) ⟨676529, by rfl⟩ : syracuseStep 902039 = 1353059) B1353059
theorem B902059 : Blo 900574 902059 := bstep (se 1 (by rfl) ⟨676544, by rfl⟩ : syracuseStep 902059 = 1353089) B1353089
theorem B902071 : Blo 900574 902071 := bstep (se 1 (by rfl) ⟨676553, by rfl⟩ : syracuseStep 902071 = 1353107) B1353107
theorem B902091 : Blo 900574 902091 := bstep (se 1 (by rfl) ⟨676568, by rfl⟩ : syracuseStep 902091 = 1353137) B1353137
theorem B1524683 : Blo 900574 1524683 := bstep (se 1 (by rfl) ⟨1143512, by rfl⟩ : syracuseStep 1524683 = 2287025) B2287025
theorem B902103 : Blo 900574 902103 := bstep (se 1 (by rfl) ⟨676577, by rfl⟩ : syracuseStep 902103 = 1353155) B1353155
theorem B15647705 : Blo 900574 15647705 := bstep (se 2 (by rfl) ⟨5867889, by rfl⟩ : syracuseStep 15647705 = 11735779) B11735779
theorem B902123 : Blo 900574 902123 := bstep (se 1 (by rfl) ⟨676592, by rfl⟩ : syracuseStep 902123 = 1353185) B1353185
theorem B902135 : Blo 900574 902135 := bstep (se 1 (by rfl) ⟨676601, by rfl⟩ : syracuseStep 902135 = 1353203) B1353203
theorem B902155 : Blo 900574 902155 := bstep (se 1 (by rfl) ⟨676616, by rfl⟩ : syracuseStep 902155 = 1353233) B1353233
theorem B6177809 : Blo 900574 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B902167 : Blo 900574 902167 := bstep (se 1 (by rfl) ⟨676625, by rfl⟩ : syracuseStep 902167 = 1353251) B1353251
theorem B902187 : Blo 900574 902187 := bstep (se 1 (by rfl) ⟨676640, by rfl⟩ : syracuseStep 902187 = 1353281) B1353281
theorem B902199 : Blo 900574 902199 := bstep (se 1 (by rfl) ⟨676649, by rfl⟩ : syracuseStep 902199 = 1353299) B1353299
theorem B902219 : Blo 900574 902219 := bstep (se 1 (by rfl) ⟨676664, by rfl⟩ : syracuseStep 902219 = 1353329) B1353329
theorem B1524811 : Blo 900574 1524811 := bstep (se 1 (by rfl) ⟨1143608, by rfl⟩ : syracuseStep 1524811 = 2287217) B2287217
theorem B902231 : Blo 900574 902231 := bstep (se 1 (by rfl) ⟨676673, by rfl⟩ : syracuseStep 902231 = 1353347) B1353347
theorem B902251 : Blo 900574 902251 := bstep (se 1 (by rfl) ⟨676688, by rfl⟩ : syracuseStep 902251 = 1353377) B1353377
theorem B902263 : Blo 900574 902263 := bstep (se 1 (by rfl) ⟨676697, by rfl⟩ : syracuseStep 902263 = 1353395) B1353395
theorem B902283 : Blo 900574 902283 := bstep (se 1 (by rfl) ⟨676712, by rfl⟩ : syracuseStep 902283 = 1353425) B1353425
theorem B902295 : Blo 900574 902295 := bstep (se 1 (by rfl) ⟨676721, by rfl⟩ : syracuseStep 902295 = 1353443) B1353443
theorem B902315 : Blo 900574 902315 := bstep (se 1 (by rfl) ⟨676736, by rfl⟩ : syracuseStep 902315 = 1353473) B1353473
theorem B902327 : Blo 900574 902327 := bstep (se 1 (by rfl) ⟨676745, by rfl⟩ : syracuseStep 902327 = 1353491) B1353491
theorem B2442433 : Blo 900574 2442433 := bstep (se 2 (by rfl) ⟨915912, by rfl⟩ : syracuseStep 2442433 = 1831825) B1831825
theorem B902347 : Blo 900574 902347 := bstep (se 1 (by rfl) ⟨676760, by rfl⟩ : syracuseStep 902347 = 1353521) B1353521
theorem B902359 : Blo 900574 902359 := bstep (se 1 (by rfl) ⟨676769, by rfl⟩ : syracuseStep 902359 = 1353539) B1353539
theorem B1524953 : Blo 900574 1524953 := bstep (se 2 (by rfl) ⟨571857, by rfl⟩ : syracuseStep 1524953 = 1143715) B1143715
theorem B902379 : Blo 900574 902379 := bstep (se 1 (by rfl) ⟨676784, by rfl⟩ : syracuseStep 902379 = 1353569) B1353569
theorem B902391 : Blo 900574 902391 := bstep (se 1 (by rfl) ⟨676793, by rfl⟩ : syracuseStep 902391 = 1353587) B1353587
theorem B902411 : Blo 900574 902411 := bstep (se 1 (by rfl) ⟨676808, by rfl⟩ : syracuseStep 902411 = 1353617) B1353617
theorem B902423 : Blo 900574 902423 := bstep (se 1 (by rfl) ⟨676817, by rfl⟩ : syracuseStep 902423 = 1353635) B1353635
theorem B902443 : Blo 900574 902443 := bstep (se 1 (by rfl) ⟨676832, by rfl⟩ : syracuseStep 902443 = 1353665) B1353665
theorem B902455 : Blo 900574 902455 := bstep (se 1 (by rfl) ⟨676841, by rfl⟩ : syracuseStep 902455 = 1353683) B1353683
theorem B2573633 : Blo 900574 2573633 := bstep (se 2 (by rfl) ⟨965112, by rfl⟩ : syracuseStep 2573633 = 1930225) B1930225
theorem B902475 : Blo 900574 902475 := bstep (se 1 (by rfl) ⟨676856, by rfl⟩ : syracuseStep 902475 = 1353713) B1353713
theorem B902487 : Blo 900574 902487 := bstep (se 1 (by rfl) ⟨676865, by rfl⟩ : syracuseStep 902487 = 1353731) B1353731
theorem B1525081 : Blo 900574 1525081 := bstep (se 2 (by rfl) ⟨571905, by rfl⟩ : syracuseStep 1525081 = 1143811) B1143811
theorem B902507 : Blo 900574 902507 := bstep (se 1 (by rfl) ⟨676880, by rfl⟩ : syracuseStep 902507 = 1353761) B1353761
theorem B902519 : Blo 900574 902519 := bstep (se 1 (by rfl) ⟨676889, by rfl⟩ : syracuseStep 902519 = 1353779) B1353779
theorem B902539 : Blo 900574 902539 := bstep (se 1 (by rfl) ⟨676904, by rfl⟩ : syracuseStep 902539 = 1353809) B1353809
theorem B902551 : Blo 900574 902551 := bstep (se 1 (by rfl) ⟨676913, by rfl⟩ : syracuseStep 902551 = 1353827) B1353827
theorem B902571 : Blo 900574 902571 := bstep (se 1 (by rfl) ⟨676928, by rfl⟩ : syracuseStep 902571 = 1353857) B1353857
theorem B902583 : Blo 900574 902583 := bstep (se 1 (by rfl) ⟨676937, by rfl⟩ : syracuseStep 902583 = 1353875) B1353875
theorem B902603 : Blo 900574 902603 := bstep (se 1 (by rfl) ⟨676952, by rfl⟩ : syracuseStep 902603 = 1353905) B1353905
theorem B902615 : Blo 900574 902615 := bstep (se 1 (by rfl) ⟨676961, by rfl⟩ : syracuseStep 902615 = 1353923) B1353923
theorem B3425753 : Blo 900574 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B902635 : Blo 900574 902635 := bstep (se 1 (by rfl) ⟨676976, by rfl⟩ : syracuseStep 902635 = 1353953) B1353953
theorem B902647 : Blo 900574 902647 := bstep (se 1 (by rfl) ⟨676985, by rfl⟩ : syracuseStep 902647 = 1353971) B1353971
theorem B902667 : Blo 900574 902667 := bstep (se 1 (by rfl) ⟨677000, by rfl⟩ : syracuseStep 902667 = 1354001) B1354001
theorem B902679 : Blo 900574 902679 := bstep (se 1 (by rfl) ⟨677009, by rfl⟩ : syracuseStep 902679 = 1354019) B1354019
theorem B902699 : Blo 900574 902699 := bstep (se 1 (by rfl) ⟨677024, by rfl⟩ : syracuseStep 902699 = 1354049) B1354049
theorem B902711 : Blo 900574 902711 := bstep (se 1 (by rfl) ⟨677033, by rfl⟩ : syracuseStep 902711 = 1354067) B1354067
theorem B902731 : Blo 900574 902731 := bstep (se 1 (by rfl) ⟨677048, by rfl⟩ : syracuseStep 902731 = 1354097) B1354097
theorem B902743 : Blo 900574 902743 := bstep (se 1 (by rfl) ⟨677057, by rfl⟩ : syracuseStep 902743 = 1354115) B1354115
theorem B902763 : Blo 900574 902763 := bstep (se 1 (by rfl) ⟨677072, by rfl⟩ : syracuseStep 902763 = 1354145) B1354145
theorem B902775 : Blo 900574 902775 := bstep (se 1 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 902775 = 1354163) B1354163
theorem B902795 : Blo 900574 902795 := bstep (se 1 (by rfl) ⟨677096, by rfl⟩ : syracuseStep 902795 = 1354193) B1354193
theorem B902807 : Blo 900574 902807 := bstep (se 1 (by rfl) ⟨677105, by rfl⟩ : syracuseStep 902807 = 1354211) B1354211
theorem B902827 : Blo 900574 902827 := bstep (se 1 (by rfl) ⟨677120, by rfl⟩ : syracuseStep 902827 = 1354241) B1354241
theorem B902839 : Blo 900574 902839 := bstep (se 1 (by rfl) ⟨677129, by rfl⟩ : syracuseStep 902839 = 1354259) B1354259
theorem B902859 : Blo 900574 902859 := bstep (se 1 (by rfl) ⟨677144, by rfl⟩ : syracuseStep 902859 = 1354289) B1354289
theorem B902871 : Blo 900574 902871 := bstep (se 1 (by rfl) ⟨677153, by rfl⟩ : syracuseStep 902871 = 1354307) B1354307
theorem B902891 : Blo 900574 902891 := bstep (se 1 (by rfl) ⟨677168, by rfl⟩ : syracuseStep 902891 = 1354337) B1354337
theorem B902903 : Blo 900574 902903 := bstep (se 1 (by rfl) ⟨677177, by rfl⟩ : syracuseStep 902903 = 1354355) B1354355
theorem B6866693 : Blo 900574 6866693 := bstep (se 4 (by rfl) ⟨643752, by rfl⟩ : syracuseStep 6866693 = 1287505) B1287505
theorem B902923 : Blo 900574 902923 := bstep (se 1 (by rfl) ⟨677192, by rfl⟩ : syracuseStep 902923 = 1354385) B1354385
theorem B902935 : Blo 900574 902935 := bstep (se 1 (by rfl) ⟨677201, by rfl⟩ : syracuseStep 902935 = 1354403) B1354403
theorem B902955 : Blo 900574 902955 := bstep (se 1 (by rfl) ⟨677216, by rfl⟩ : syracuseStep 902955 = 1354433) B1354433
theorem B3655475 : Blo 900574 3655475 := bstep (se 1 (by rfl) ⟨2741606, by rfl⟩ : syracuseStep 3655475 = 5483213) B5483213
theorem B902967 : Blo 900574 902967 := bstep (se 1 (by rfl) ⟨677225, by rfl⟩ : syracuseStep 902967 = 1354451) B1354451
theorem B902987 : Blo 900574 902987 := bstep (se 1 (by rfl) ⟨677240, by rfl⟩ : syracuseStep 902987 = 1354481) B1354481
theorem B902999 : Blo 900574 902999 := bstep (se 1 (by rfl) ⟨677249, by rfl⟩ : syracuseStep 902999 = 1354499) B1354499
theorem B903019 : Blo 900574 903019 := bstep (se 1 (by rfl) ⟨677264, by rfl⟩ : syracuseStep 903019 = 1354529) B1354529
theorem B903031 : Blo 900574 903031 := bstep (se 1 (by rfl) ⟨677273, by rfl⟩ : syracuseStep 903031 = 1354547) B1354547
theorem B903051 : Blo 900574 903051 := bstep (se 1 (by rfl) ⟨677288, by rfl⟩ : syracuseStep 903051 = 1354577) B1354577
theorem B903063 : Blo 900574 903063 := bstep (se 1 (by rfl) ⟨677297, by rfl⟩ : syracuseStep 903063 = 1354595) B1354595
theorem B1525655 : Blo 900574 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B903083 : Blo 900574 903083 := bstep (se 1 (by rfl) ⟨677312, by rfl⟩ : syracuseStep 903083 = 1354625) B1354625
theorem B903095 : Blo 900574 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B903115 : Blo 900574 903115 := bstep (se 1 (by rfl) ⟨677336, by rfl⟩ : syracuseStep 903115 = 1354673) B1354673
theorem B2443211 : Blo 900574 2443211 := bstep (se 1 (by rfl) ⟨1832408, by rfl⟩ : syracuseStep 2443211 = 3664817) B3664817
theorem B903127 : Blo 900574 903127 := bstep (se 1 (by rfl) ⟨677345, by rfl⟩ : syracuseStep 903127 = 1354691) B1354691
theorem B903147 : Blo 900574 903147 := bstep (se 1 (by rfl) ⟨677360, by rfl⟩ : syracuseStep 903147 = 1354721) B1354721
theorem B903159 : Blo 900574 903159 := bstep (se 1 (by rfl) ⟨677369, by rfl⟩ : syracuseStep 903159 = 1354739) B1354739
theorem B903179 : Blo 900574 903179 := bstep (se 1 (by rfl) ⟨677384, by rfl⟩ : syracuseStep 903179 = 1354769) B1354769
theorem B903191 : Blo 900574 903191 := bstep (se 1 (by rfl) ⟨677393, by rfl⟩ : syracuseStep 903191 = 1354787) B1354787
theorem B1525783 : Blo 900574 1525783 := bstep (se 1 (by rfl) ⟨1144337, by rfl⟩ : syracuseStep 1525783 = 2288675) B2288675
theorem B903211 : Blo 900574 903211 := bstep (se 1 (by rfl) ⟨677408, by rfl⟩ : syracuseStep 903211 = 1354817) B1354817
theorem B903223 : Blo 900574 903223 := bstep (se 1 (by rfl) ⟨677417, by rfl⟩ : syracuseStep 903223 = 1354835) B1354835
theorem B903243 : Blo 900574 903243 := bstep (se 1 (by rfl) ⟨677432, by rfl⟩ : syracuseStep 903243 = 1354865) B1354865
theorem B4573259 : Blo 900574 4573259 := bstep (se 1 (by rfl) ⟨3429944, by rfl⟩ : syracuseStep 4573259 = 6859889) B6859889
theorem B903255 : Blo 900574 903255 := bstep (se 1 (by rfl) ⟨677441, by rfl⟩ : syracuseStep 903255 = 1354883) B1354883
theorem B903275 : Blo 900574 903275 := bstep (se 1 (by rfl) ⟨677456, by rfl⟩ : syracuseStep 903275 = 1354913) B1354913
theorem B903287 : Blo 900574 903287 := bstep (se 1 (by rfl) ⟨677465, by rfl⟩ : syracuseStep 903287 = 1354931) B1354931
theorem B903307 : Blo 900574 903307 := bstep (se 1 (by rfl) ⟨677480, by rfl⟩ : syracuseStep 903307 = 1354961) B1354961
theorem B903319 : Blo 900574 903319 := bstep (se 1 (by rfl) ⟨677489, by rfl⟩ : syracuseStep 903319 = 1354979) B1354979
theorem B903339 : Blo 900574 903339 := bstep (se 1 (by rfl) ⟨677504, by rfl⟩ : syracuseStep 903339 = 1355009) B1355009
theorem B2279603 : Blo 900574 2279603 := bstep (se 1 (by rfl) ⟨1709702, by rfl⟩ : syracuseStep 2279603 = 3419405) B3419405
theorem B903351 : Blo 900574 903351 := bstep (se 1 (by rfl) ⟨677513, by rfl⟩ : syracuseStep 903351 = 1355027) B1355027
theorem B903371 : Blo 900574 903371 := bstep (se 1 (by rfl) ⟨677528, by rfl⟩ : syracuseStep 903371 = 1355057) B1355057
theorem B903383 : Blo 900574 903383 := bstep (se 1 (by rfl) ⟨677537, by rfl⟩ : syracuseStep 903383 = 1355075) B1355075
theorem B903403 : Blo 900574 903403 := bstep (se 1 (by rfl) ⟨677552, by rfl⟩ : syracuseStep 903403 = 1355105) B1355105
theorem B903415 : Blo 900574 903415 := bstep (se 1 (by rfl) ⟨677561, by rfl⟩ : syracuseStep 903415 = 1355123) B1355123
theorem B7817477 : Blo 900574 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B903435 : Blo 900574 903435 := bstep (se 1 (by rfl) ⟨677576, by rfl⟩ : syracuseStep 903435 = 1355153) B1355153
theorem B903447 : Blo 900574 903447 := bstep (se 1 (by rfl) ⟨677585, by rfl⟩ : syracuseStep 903447 = 1355171) B1355171
theorem B903467 : Blo 900574 903467 := bstep (se 1 (by rfl) ⟨677600, by rfl⟩ : syracuseStep 903467 = 1355201) B1355201
theorem B903479 : Blo 900574 903479 := bstep (se 1 (by rfl) ⟨677609, by rfl⟩ : syracuseStep 903479 = 1355219) B1355219
theorem B2312513 : Blo 900574 2312513 := bstep (se 2 (by rfl) ⟨867192, by rfl⟩ : syracuseStep 2312513 = 1734385) B1734385
theorem B903499 : Blo 900574 903499 := bstep (se 1 (by rfl) ⟨677624, by rfl⟩ : syracuseStep 903499 = 1355249) B1355249
theorem B903511 : Blo 900574 903511 := bstep (se 1 (by rfl) ⟨677633, by rfl⟩ : syracuseStep 903511 = 1355267) B1355267
theorem B903531 : Blo 900574 903531 := bstep (se 1 (by rfl) ⟨677648, by rfl⟩ : syracuseStep 903531 = 1355297) B1355297
theorem B903543 : Blo 900574 903543 := bstep (se 1 (by rfl) ⟨677657, by rfl⟩ : syracuseStep 903543 = 1355315) B1355315
theorem B903563 : Blo 900574 903563 := bstep (se 1 (by rfl) ⟨677672, by rfl⟩ : syracuseStep 903563 = 1355345) B1355345
theorem B903575 : Blo 900574 903575 := bstep (se 1 (by rfl) ⟨677681, by rfl⟩ : syracuseStep 903575 = 1355363) B1355363
theorem B903595 : Blo 900574 903595 := bstep (se 1 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 903595 = 1355393) B1355393
theorem B903607 : Blo 900574 903607 := bstep (se 1 (by rfl) ⟨677705, by rfl⟩ : syracuseStep 903607 = 1355411) B1355411
theorem B903627 : Blo 900574 903627 := bstep (se 1 (by rfl) ⟨677720, by rfl⟩ : syracuseStep 903627 = 1355441) B1355441
theorem B903639 : Blo 900574 903639 := bstep (se 1 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 903639 = 1355459) B1355459
theorem B2279897 : Blo 900574 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B4639193 : Blo 900574 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B903659 : Blo 900574 903659 := bstep (se 1 (by rfl) ⟨677744, by rfl⟩ : syracuseStep 903659 = 1355489) B1355489
theorem B903671 : Blo 900574 903671 := bstep (se 1 (by rfl) ⟨677753, by rfl⟩ : syracuseStep 903671 = 1355507) B1355507
theorem B903691 : Blo 900574 903691 := bstep (se 1 (by rfl) ⟨677768, by rfl⟩ : syracuseStep 903691 = 1355537) B1355537
theorem B903703 : Blo 900574 903703 := bstep (se 1 (by rfl) ⟨677777, by rfl⟩ : syracuseStep 903703 = 1355555) B1355555
theorem B903723 : Blo 900574 903723 := bstep (se 1 (by rfl) ⟨677792, by rfl⟩ : syracuseStep 903723 = 1355585) B1355585
theorem B903735 : Blo 900574 903735 := bstep (se 1 (by rfl) ⟨677801, by rfl⟩ : syracuseStep 903735 = 1355603) B1355603
theorem B2443841 : Blo 900574 2443841 := bstep (se 2 (by rfl) ⟨916440, by rfl⟩ : syracuseStep 2443841 = 1832881) B1832881
theorem B903755 : Blo 900574 903755 := bstep (se 1 (by rfl) ⟨677816, by rfl⟩ : syracuseStep 903755 = 1355633) B1355633
theorem B903767 : Blo 900574 903767 := bstep (se 1 (by rfl) ⟨677825, by rfl⟩ : syracuseStep 903767 = 1355651) B1355651
theorem B903787 : Blo 900574 903787 := bstep (se 1 (by rfl) ⟨677840, by rfl⟩ : syracuseStep 903787 = 1355681) B1355681
theorem B903799 : Blo 900574 903799 := bstep (se 1 (by rfl) ⟨677849, by rfl⟩ : syracuseStep 903799 = 1355699) B1355699
theorem B903819 : Blo 900574 903819 := bstep (se 1 (by rfl) ⟨677864, by rfl⟩ : syracuseStep 903819 = 1355729) B1355729
theorem B1526411 : Blo 900574 1526411 := bstep (se 1 (by rfl) ⟨1144808, by rfl⟩ : syracuseStep 1526411 = 2289617) B2289617
theorem B903831 : Blo 900574 903831 := bstep (se 1 (by rfl) ⟨677873, by rfl⟩ : syracuseStep 903831 = 1355747) B1355747
theorem B903851 : Blo 900574 903851 := bstep (se 1 (by rfl) ⟨677888, by rfl⟩ : syracuseStep 903851 = 1355777) B1355777
theorem B903863 : Blo 900574 903863 := bstep (se 1 (by rfl) ⟨677897, by rfl⟩ : syracuseStep 903863 = 1355795) B1355795
theorem B903883 : Blo 900574 903883 := bstep (se 1 (by rfl) ⟨677912, by rfl⟩ : syracuseStep 903883 = 1355825) B1355825
theorem B903895 : Blo 900574 903895 := bstep (se 1 (by rfl) ⟨677921, by rfl⟩ : syracuseStep 903895 = 1355843) B1355843
theorem B903915 : Blo 900574 903915 := bstep (se 1 (by rfl) ⟨677936, by rfl⟩ : syracuseStep 903915 = 1355873) B1355873
theorem B903927 : Blo 900574 903927 := bstep (se 1 (by rfl) ⟨677945, by rfl⟩ : syracuseStep 903927 = 1355891) B1355891
theorem B903947 : Blo 900574 903947 := bstep (se 1 (by rfl) ⟨677960, by rfl⟩ : syracuseStep 903947 = 1355921) B1355921
theorem B903959 : Blo 900574 903959 := bstep (se 1 (by rfl) ⟨677969, by rfl⟩ : syracuseStep 903959 = 1355939) B1355939
theorem B903979 : Blo 900574 903979 := bstep (se 1 (by rfl) ⟨677984, by rfl⟩ : syracuseStep 903979 = 1355969) B1355969
theorem B4180781 : Blo 900574 4180781 := bstep (se 3 (by rfl) ⟨783896, by rfl⟩ : syracuseStep 4180781 = 1567793) B1567793
theorem B903991 : Blo 900574 903991 := bstep (se 1 (by rfl) ⟨677993, by rfl⟩ : syracuseStep 903991 = 1355987) B1355987
theorem B904011 : Blo 900574 904011 := bstep (se 1 (by rfl) ⟨678008, by rfl⟩ : syracuseStep 904011 = 1356017) B1356017
theorem B904023 : Blo 900574 904023 := bstep (se 1 (by rfl) ⟨678017, by rfl⟩ : syracuseStep 904023 = 1356035) B1356035
theorem B904043 : Blo 900574 904043 := bstep (se 1 (by rfl) ⟨678032, by rfl⟩ : syracuseStep 904043 = 1356065) B1356065
theorem B904055 : Blo 900574 904055 := bstep (se 1 (by rfl) ⟨678041, by rfl⟩ : syracuseStep 904055 = 1356083) B1356083
theorem B904075 : Blo 900574 904075 := bstep (se 1 (by rfl) ⟨678056, by rfl⟩ : syracuseStep 904075 = 1356113) B1356113
theorem B904087 : Blo 900574 904087 := bstep (se 1 (by rfl) ⟨678065, by rfl⟩ : syracuseStep 904087 = 1356131) B1356131
theorem B904107 : Blo 900574 904107 := bstep (se 1 (by rfl) ⟨678080, by rfl⟩ : syracuseStep 904107 = 1356161) B1356161
theorem B904119 : Blo 900574 904119 := bstep (se 1 (by rfl) ⟨678089, by rfl⟩ : syracuseStep 904119 = 1356179) B1356179
theorem B904139 : Blo 900574 904139 := bstep (se 1 (by rfl) ⟨678104, by rfl⟩ : syracuseStep 904139 = 1356209) B1356209
theorem B2575307 : Blo 900574 2575307 := bstep (se 1 (by rfl) ⟨1931480, by rfl⟩ : syracuseStep 2575307 = 3862961) B3862961
theorem B904151 : Blo 900574 904151 := bstep (se 1 (by rfl) ⟨678113, by rfl⟩ : syracuseStep 904151 = 1356227) B1356227
theorem B904171 : Blo 900574 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B904183 : Blo 900574 904183 := bstep (se 1 (by rfl) ⟨678137, by rfl⟩ : syracuseStep 904183 = 1356275) B1356275
theorem B904203 : Blo 900574 904203 := bstep (se 1 (by rfl) ⟨678152, by rfl⟩ : syracuseStep 904203 = 1356305) B1356305
theorem B904215 : Blo 900574 904215 := bstep (se 1 (by rfl) ⟨678161, by rfl⟩ : syracuseStep 904215 = 1356323) B1356323
theorem B904235 : Blo 900574 904235 := bstep (se 1 (by rfl) ⟨678176, by rfl⟩ : syracuseStep 904235 = 1356353) B1356353
theorem B3427379 : Blo 900574 3427379 := bstep (se 1 (by rfl) ⟨2570534, by rfl⟩ : syracuseStep 3427379 = 5141069) B5141069
theorem B904247 : Blo 900574 904247 := bstep (se 1 (by rfl) ⟨678185, by rfl⟩ : syracuseStep 904247 = 1356371) B1356371
theorem B3296321 : Blo 900574 3296321 := bstep (se 2 (by rfl) ⟨1236120, by rfl⟩ : syracuseStep 3296321 = 2472241) B2472241
theorem B3427393 : Blo 900574 3427393 := bstep (se 2 (by rfl) ⟨1285272, by rfl⟩ : syracuseStep 3427393 = 2570545) B2570545
theorem B904267 : Blo 900574 904267 := bstep (se 1 (by rfl) ⟨678200, by rfl⟩ : syracuseStep 904267 = 1356401) B1356401
theorem B904279 : Blo 900574 904279 := bstep (se 1 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 904279 = 1356419) B1356419
theorem B904299 : Blo 900574 904299 := bstep (se 1 (by rfl) ⟨678224, by rfl⟩ : syracuseStep 904299 = 1356449) B1356449
theorem B1625203 : Blo 900574 1625203 := bstep (se 1 (by rfl) ⟨1218902, by rfl⟩ : syracuseStep 1625203 = 2437805) B2437805
theorem B904311 : Blo 900574 904311 := bstep (se 1 (by rfl) ⟨678233, by rfl⟩ : syracuseStep 904311 = 1356467) B1356467
theorem B904331 : Blo 900574 904331 := bstep (se 1 (by rfl) ⟨678248, by rfl⟩ : syracuseStep 904331 = 1356497) B1356497
theorem B904343 : Blo 900574 904343 := bstep (se 1 (by rfl) ⟨678257, by rfl⟩ : syracuseStep 904343 = 1356515) B1356515
theorem B904363 : Blo 900574 904363 := bstep (se 1 (by rfl) ⟨678272, by rfl⟩ : syracuseStep 904363 = 1356545) B1356545
theorem B904375 : Blo 900574 904375 := bstep (se 1 (by rfl) ⟨678281, by rfl⟩ : syracuseStep 904375 = 1356563) B1356563
theorem B2477249 : Blo 900574 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B904395 : Blo 900574 904395 := bstep (se 1 (by rfl) ⟨678296, by rfl⟩ : syracuseStep 904395 = 1356593) B1356593
theorem B904407 : Blo 900574 904407 := bstep (se 1 (by rfl) ⟨678305, by rfl⟩ : syracuseStep 904407 = 1356611) B1356611
theorem B904427 : Blo 900574 904427 := bstep (se 1 (by rfl) ⟨678320, by rfl⟩ : syracuseStep 904427 = 1356641) B1356641
theorem B13389041 : Blo 900574 13389041 := bstep (se 2 (by rfl) ⟨5020890, by rfl⟩ : syracuseStep 13389041 = 10041781) B10041781
theorem B14666993 : Blo 900574 14666993 := bstep (se 2 (by rfl) ⟨5500122, by rfl⟩ : syracuseStep 14666993 = 11000245) B11000245
theorem B904439 : Blo 900574 904439 := bstep (se 1 (by rfl) ⟨678329, by rfl⟩ : syracuseStep 904439 = 1356659) B1356659
theorem B904459 : Blo 900574 904459 := bstep (se 1 (by rfl) ⟨678344, by rfl⟩ : syracuseStep 904459 = 1356689) B1356689
theorem B904471 : Blo 900574 904471 := bstep (se 1 (by rfl) ⟨678353, by rfl⟩ : syracuseStep 904471 = 1356707) B1356707
theorem B904491 : Blo 900574 904491 := bstep (se 1 (by rfl) ⟨678368, by rfl⟩ : syracuseStep 904491 = 1356737) B1356737
theorem B904503 : Blo 900574 904503 := bstep (se 1 (by rfl) ⟨678377, by rfl⟩ : syracuseStep 904503 = 1356755) B1356755
theorem B904523 : Blo 900574 904523 := bstep (se 1 (by rfl) ⟨678392, by rfl⟩ : syracuseStep 904523 = 1356785) B1356785
theorem B904535 : Blo 900574 904535 := bstep (se 1 (by rfl) ⟨678401, by rfl⟩ : syracuseStep 904535 = 1356803) B1356803
theorem B5131613 : Blo 900574 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B904555 : Blo 900574 904555 := bstep (se 1 (by rfl) ⟨678416, by rfl⟩ : syracuseStep 904555 = 1356833) B1356833
theorem B904567 : Blo 900574 904567 := bstep (se 1 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 904567 = 1356851) B1356851
theorem B6180275 : Blo 900574 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B1625665 : Blo 900574 1625665 := bstep (se 2 (by rfl) ⟨609624, by rfl⟩ : syracuseStep 1625665 = 1219249) B1219249
theorem B3853889 : Blo 900574 3853889 := bstep (se 2 (by rfl) ⟨1445208, by rfl⟩ : syracuseStep 3853889 = 2890417) B2890417
theorem B1625881 : Blo 900574 1625881 := bstep (se 2 (by rfl) ⟨609705, by rfl⟩ : syracuseStep 1625881 = 1219411) B1219411
theorem B4575041 : Blo 900574 4575041 := bstep (se 2 (by rfl) ⟨1715640, by rfl⟩ : syracuseStep 4575041 = 3431281) B3431281
theorem B8245253 : Blo 900574 8245253 := bstep (se 4 (by rfl) ⟨772992, by rfl⟩ : syracuseStep 8245253 = 1545985) B1545985
theorem B2281547 : Blo 900574 2281547 := bstep (se 1 (by rfl) ⟨1711160, by rfl⟩ : syracuseStep 2281547 = 3422321) B3422321
theorem B2937035 : Blo 900574 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B12341605 : Blo 900574 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B7721477 : Blo 900574 7721477 := bstep (se 4 (by rfl) ⟨723888, by rfl⟩ : syracuseStep 7721477 = 1447777) B1447777
theorem B2511667 : Blo 900574 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B3429323 : Blo 900574 3429323 := bstep (se 1 (by rfl) ⟨2571992, by rfl⟩ : syracuseStep 3429323 = 5143985) B5143985
theorem B3429337 : Blo 900574 3429337 := bstep (se 2 (by rfl) ⟨1286001, by rfl⟩ : syracuseStep 3429337 = 2572003) B2572003
theorem B2282519 : Blo 900574 2282519 := bstep (se 1 (by rfl) ⟨1711889, by rfl⟩ : syracuseStep 2282519 = 3423779) B3423779
theorem B1004663 : Blo 900574 1004663 := bstep (se 1 (by rfl) ⟨753497, by rfl⟩ : syracuseStep 1004663 = 1506995) B1506995
theorem B1758361 : Blo 900574 1758361 := bstep (se 2 (by rfl) ⟨659385, by rfl⟩ : syracuseStep 1758361 = 1318771) B1318771
theorem B7722161 : Blo 900574 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B12998161 : Blo 900574 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B2283187 : Blo 900574 2283187 := bstep (se 1 (by rfl) ⟨1712390, by rfl⟩ : syracuseStep 2283187 = 3424781) B3424781
theorem B4576985 : Blo 900574 4576985 := bstep (se 2 (by rfl) ⟨1716369, by rfl⟩ : syracuseStep 4576985 = 3432739) B3432739
theorem B4118323 : Blo 900574 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B2283329 : Blo 900574 2283329 := bstep (se 2 (by rfl) ⟨856248, by rfl⟩ : syracuseStep 2283329 = 1712497) B1712497
theorem B5134211 : Blo 900574 5134211 := bstep (se 1 (by rfl) ⟨3850658, by rfl⟩ : syracuseStep 5134211 = 7701317) B7701317
theorem B3430295 : Blo 900574 3430295 := bstep (se 1 (by rfl) ⟨2572721, by rfl⟩ : syracuseStep 3430295 = 5145443) B5145443
theorem B2054081 : Blo 900574 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B3856349 : Blo 900574 3856349 := bstep (se 3 (by rfl) ⟨723065, by rfl⟩ : syracuseStep 3856349 = 1446131) B1446131
theorem B7723187 : Blo 900574 7723187 := bstep (se 1 (by rfl) ⟨5792390, by rfl⟩ : syracuseStep 7723187 = 11584781) B11584781
theorem B8247587 : Blo 900574 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B6937105 : Blo 900574 6937105 := bstep (se 2 (by rfl) ⟨2601414, by rfl⟩ : syracuseStep 6937105 = 5202829) B5202829
theorem B2284595 : Blo 900574 2284595 := bstep (se 1 (by rfl) ⟨1713446, by rfl⟩ : syracuseStep 2284595 = 3426893) B3426893
theorem B1924211 : Blo 900574 1924211 := bstep (se 1 (by rfl) ⟨1443158, by rfl⟩ : syracuseStep 1924211 = 2886317) B2886317
theorem B3431555 : Blo 900574 3431555 := bstep (se 1 (by rfl) ⟨2573666, by rfl⟩ : syracuseStep 3431555 = 5147333) B5147333
theorem B4578605 : Blo 900574 4578605 := bstep (se 3 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 4578605 = 1716977) B1716977
theorem B4120001 : Blo 900574 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B2285131 : Blo 900574 2285131 := bstep (se 1 (by rfl) ⟨1713848, by rfl⟩ : syracuseStep 2285131 = 3427697) B3427697
theorem B1924697 : Blo 900574 1924697 := bstep (se 2 (by rfl) ⟨721761, by rfl⟩ : syracuseStep 1924697 = 1443523) B1443523
theorem B1171147 : Blo 900574 1171147 := bstep (se 1 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 1171147 = 1756721) B1756721
theorem B2285273 : Blo 900574 2285273 := bstep (se 2 (by rfl) ⟨856977, by rfl⟩ : syracuseStep 2285273 = 1713955) B1713955
theorem B2744087 : Blo 900574 2744087 := bstep (se 1 (by rfl) ⟨2058065, by rfl⟩ : syracuseStep 2744087 = 4116131) B4116131
theorem B1925441 : Blo 900574 1925441 := bstep (se 2 (by rfl) ⟨722040, by rfl⟩ : syracuseStep 1925441 = 1444081) B1444081
theorem B3858947 : Blo 900574 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B3039767 : Blo 900574 3039767 := bstep (se 1 (by rfl) ⟨2279825, by rfl⟩ : syracuseStep 3039767 = 4559651) B4559651
theorem B2286103 : Blo 900574 2286103 := bstep (se 1 (by rfl) ⟨1714577, by rfl⟩ : syracuseStep 2286103 = 3429155) B3429155
theorem B1172183 : Blo 900574 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B8217521 : Blo 900574 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B2286539 : Blo 900574 2286539 := bstep (se 1 (by rfl) ⟨1714904, by rfl⟩ : syracuseStep 2286539 = 3429809) B3429809
theorem B3040307 : Blo 900574 3040307 := bstep (se 1 (by rfl) ⟨2280230, by rfl⟩ : syracuseStep 3040307 = 4560461) B4560461
theorem B2254003 : Blo 900574 2254003 := bstep (se 1 (by rfl) ⟨1690502, by rfl⟩ : syracuseStep 2254003 = 3381005) B3381005
theorem B1926337 : Blo 900574 1926337 := bstep (se 2 (by rfl) ⟨722376, by rfl⟩ : syracuseStep 1926337 = 1444753) B1444753
theorem B1828055 : Blo 900574 1828055 := bstep (se 1 (by rfl) ⟨1371041, by rfl⟩ : syracuseStep 1828055 = 2742083) B2742083
theorem B3040577 : Blo 900574 3040577 := bstep (se 2 (by rfl) ⟨1140216, by rfl⟩ : syracuseStep 3040577 = 2280433) B2280433
theorem B2286913 : Blo 900574 2286913 := bstep (se 2 (by rfl) ⟨857592, by rfl⟩ : syracuseStep 2286913 = 1715185) B1715185
theorem B2057687 : Blo 900574 2057687 := bstep (se 1 (by rfl) ⟨1543265, by rfl⟩ : syracuseStep 2057687 = 3086531) B3086531
theorem B1140247 : Blo 900574 1140247 := bstep (se 1 (by rfl) ⟨855185, by rfl⟩ : syracuseStep 1140247 = 1710371) B1710371
theorem B1926679 : Blo 900574 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B7726913 : Blo 900574 7726913 := bstep (se 2 (by rfl) ⟨2897592, by rfl⟩ : syracuseStep 7726913 = 5795185) B5795185
theorem B3041117 : Blo 900574 3041117 := bstep (se 3 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 3041117 = 1140419) B1140419
theorem B2287511 : Blo 900574 2287511 := bstep (se 1 (by rfl) ⟨1715633, by rfl⟩ : syracuseStep 2287511 = 3431267) B3431267
theorem B1927243 : Blo 900574 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B1370263 : Blo 900574 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B1141067 : Blo 900574 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B55568753 : Blo 900574 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B2288321 : Blo 900574 2288321 := bstep (se 2 (by rfl) ⟨858120, by rfl⟩ : syracuseStep 2288321 = 1716241) B1716241
theorem B2747201 : Blo 900574 2747201 := bstep (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) B2060401
theorem B4123543 : Blo 900574 4123543 := bstep (se 1 (by rfl) ⟨3092657, by rfl⟩ : syracuseStep 4123543 = 6185315) B6185315
theorem B3042251 : Blo 900574 3042251 := bstep (se 1 (by rfl) ⟨2281688, by rfl⟩ : syracuseStep 3042251 = 4563377) B4563377
theorem B2026457 : Blo 900574 2026457 := bstep (se 2 (by rfl) ⟨759921, by rfl⟩ : syracuseStep 2026457 = 1519843) B1519843
theorem B1141771 : Blo 900574 1141771 := bstep (se 1 (by rfl) ⟨856328, by rfl⟩ : syracuseStep 1141771 = 1712657) B1712657
theorem B2026547 : Blo 900574 2026547 := bstep (se 1 (by rfl) ⟨1519910, by rfl⟩ : syracuseStep 2026547 = 3039821) B3039821
theorem B2026583 : Blo 900574 2026583 := bstep (se 1 (by rfl) ⟨1519937, by rfl⟩ : syracuseStep 2026583 = 3039875) B3039875
theorem B1830041 : Blo 900574 1830041 := bstep (se 2 (by rfl) ⟨686265, by rfl⟩ : syracuseStep 1830041 = 1372531) B1372531
theorem B3042521 : Blo 900574 3042521 := bstep (se 2 (by rfl) ⟨1140945, by rfl⟩ : syracuseStep 3042521 = 2281891) B2281891
theorem B2288857 : Blo 900574 2288857 := bstep (se 2 (by rfl) ⟨858321, by rfl⟩ : syracuseStep 2288857 = 1716643) B1716643
theorem B2026763 : Blo 900574 2026763 := bstep (se 1 (by rfl) ⟨1520072, by rfl⟩ : syracuseStep 2026763 = 3040145) B3040145
theorem B1142039 : Blo 900574 1142039 := bstep (se 1 (by rfl) ⟨856529, by rfl⟩ : syracuseStep 1142039 = 1713059) B1713059
theorem B2026817 : Blo 900574 2026817 := bstep (se 2 (by rfl) ⟨760056, by rfl⟩ : syracuseStep 2026817 = 1520113) B1520113
theorem B1928627 : Blo 900574 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B2027033 : Blo 900574 2027033 := bstep (se 2 (by rfl) ⟨760137, by rfl⟩ : syracuseStep 2027033 = 1520275) B1520275
theorem B1928729 : Blo 900574 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B7695917 : Blo 900574 7695917 := bstep (se 3 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 7695917 = 2885969) B2885969
theorem B5140043 : Blo 900574 5140043 := bstep (se 1 (by rfl) ⟨3855032, by rfl⟩ : syracuseStep 5140043 = 7710065) B7710065
theorem B2027123 : Blo 900574 2027123 := bstep (se 1 (by rfl) ⟨1520342, by rfl⟩ : syracuseStep 2027123 = 3040685) B3040685
theorem B2027159 : Blo 900574 2027159 := bstep (se 1 (by rfl) ⟨1520369, by rfl⟩ : syracuseStep 2027159 = 3040739) B3040739
theorem B2027339 : Blo 900574 2027339 := bstep (se 1 (by rfl) ⟨1520504, by rfl⟩ : syracuseStep 2027339 = 3041009) B3041009
theorem B2060147 : Blo 900574 2060147 := bstep (se 1 (by rfl) ⟨1545110, by rfl⟩ : syracuseStep 2060147 = 3090221) B3090221
theorem B2027393 : Blo 900574 2027393 := bstep (se 2 (by rfl) ⟨760272, by rfl⟩ : syracuseStep 2027393 = 1520545) B1520545
theorem B1929089 : Blo 900574 1929089 := bstep (se 2 (by rfl) ⟨723408, by rfl⟩ : syracuseStep 1929089 = 1446817) B1446817
theorem B3043223 : Blo 900574 3043223 := bstep (se 1 (by rfl) ⟨2282417, by rfl⟩ : syracuseStep 3043223 = 4564835) B4564835
theorem B6844337 : Blo 900574 6844337 := bstep (se 2 (by rfl) ⟨2566626, by rfl⟩ : syracuseStep 6844337 = 5133253) B5133253
theorem B1142743 : Blo 900574 1142743 := bstep (se 1 (by rfl) ⟨857057, by rfl⟩ : syracuseStep 1142743 = 1714115) B1714115
theorem B2027609 : Blo 900574 2027609 := bstep (se 2 (by rfl) ⟨760353, by rfl⟩ : syracuseStep 2027609 = 1520707) B1520707
theorem B2748505 : Blo 900574 2748505 := bstep (se 2 (by rfl) ⟨1030689, by rfl⟩ : syracuseStep 2748505 = 2061379) B2061379
theorem B4124803 : Blo 900574 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B6942871 : Blo 900574 6942871 := bstep (se 1 (by rfl) ⟨5207153, by rfl⟩ : syracuseStep 6942871 = 10414307) B10414307
theorem B11137175 : Blo 900574 11137175 := bstep (se 1 (by rfl) ⟨8352881, by rfl⟩ : syracuseStep 11137175 = 16705763) B16705763
theorem B2027699 : Blo 900574 2027699 := bstep (se 1 (by rfl) ⟨1520774, by rfl⟩ : syracuseStep 2027699 = 3041549) B3041549
theorem B3666113 : Blo 900574 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B3862721 : Blo 900574 3862721 := bstep (se 2 (by rfl) ⟨1448520, by rfl⟩ : syracuseStep 3862721 = 2897041) B2897041
theorem B2027735 : Blo 900574 2027735 := bstep (se 1 (by rfl) ⟨1520801, by rfl⟩ : syracuseStep 2027735 = 3041603) B3041603
theorem B1831169 : Blo 900574 1831169 := bstep (se 2 (by rfl) ⟨686688, by rfl⟩ : syracuseStep 1831169 = 1373377) B1373377
theorem B913739 : Blo 900574 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B2027915 : Blo 900574 2027915 := bstep (se 1 (by rfl) ⟨1520936, by rfl⟩ : syracuseStep 2027915 = 3041873) B3041873
theorem B6844823 : Blo 900574 6844823 := bstep (se 1 (by rfl) ⟨5133617, by rfl⟩ : syracuseStep 6844823 = 10267235) B10267235
theorem B3043763 : Blo 900574 3043763 := bstep (se 1 (by rfl) ⟨2282822, by rfl⟩ : syracuseStep 3043763 = 4565645) B4565645
theorem B2027969 : Blo 900574 2027969 := bstep (se 2 (by rfl) ⟨760488, by rfl⟩ : syracuseStep 2027969 = 1520977) B1520977
theorem B1929815 : Blo 900574 1929815 := bstep (se 1 (by rfl) ⟨1447361, by rfl⟩ : syracuseStep 1929815 = 2894723) B2894723
theorem B6255197 : Blo 900574 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B2028185 : Blo 900574 2028185 := bstep (se 2 (by rfl) ⟨760569, by rfl⟩ : syracuseStep 2028185 = 1521139) B1521139
theorem B3044033 : Blo 900574 3044033 := bstep (se 2 (by rfl) ⟨1141512, by rfl⟩ : syracuseStep 3044033 = 2283025) B2283025
theorem B2028275 : Blo 900574 2028275 := bstep (se 1 (by rfl) ⟨1521206, by rfl⟩ : syracuseStep 2028275 = 3042413) B3042413
theorem B7729937 : Blo 900574 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B2028311 : Blo 900574 2028311 := bstep (se 1 (by rfl) ⟨1521233, by rfl⟩ : syracuseStep 2028311 = 3042467) B3042467
theorem B2028491 : Blo 900574 2028491 := bstep (se 1 (by rfl) ⟨1521368, by rfl⟩ : syracuseStep 2028491 = 3042737) B3042737
theorem B2028545 : Blo 900574 2028545 := bstep (se 2 (by rfl) ⟨760704, by rfl⟩ : syracuseStep 2028545 = 1521409) B1521409
theorem B1831987 : Blo 900574 1831987 := bstep (se 1 (by rfl) ⟨1373990, by rfl⟩ : syracuseStep 1831987 = 2747981) B2747981
theorem B3863645 : Blo 900574 3863645 := bstep (se 3 (by rfl) ⟨724433, by rfl⟩ : syracuseStep 3863645 = 1448867) B1448867
theorem B2028761 : Blo 900574 2028761 := bstep (se 2 (by rfl) ⟨760785, by rfl⟩ : syracuseStep 2028761 = 1521571) B1521571
theorem B3044573 : Blo 900574 3044573 := bstep (se 3 (by rfl) ⟨570857, by rfl⟩ : syracuseStep 3044573 = 1141715) B1141715
theorem B2028851 : Blo 900574 2028851 := bstep (se 1 (by rfl) ⟨1521638, by rfl⟩ : syracuseStep 2028851 = 3043277) B3043277
theorem B2028887 : Blo 900574 2028887 := bstep (se 1 (by rfl) ⟨1521665, by rfl⟩ : syracuseStep 2028887 = 3043331) B3043331
theorem B1930711 : Blo 900574 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B2029067 : Blo 900574 2029067 := bstep (se 1 (by rfl) ⟨1521800, by rfl⟩ : syracuseStep 2029067 = 3043601) B3043601
theorem B2029121 : Blo 900574 2029121 := bstep (se 2 (by rfl) ⟨760920, by rfl⟩ : syracuseStep 2029121 = 1521841) B1521841
theorem B1013323 : Blo 900574 1013323 := bstep (se 1 (by rfl) ⟨759992, by rfl⟩ : syracuseStep 1013323 = 1519985) B1519985
theorem B1144459 : Blo 900574 1144459 := bstep (se 1 (by rfl) ⟨858344, by rfl⟩ : syracuseStep 1144459 = 1716689) B1716689
theorem B1013431 : Blo 900574 1013431 := bstep (se 1 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 1013431 = 1520147) B1520147
theorem B2029337 : Blo 900574 2029337 := bstep (se 2 (by rfl) ⟨761001, by rfl⟩ : syracuseStep 2029337 = 1522003) B1522003
theorem B1013611 : Blo 900574 1013611 := bstep (se 1 (by rfl) ⟨760208, by rfl⟩ : syracuseStep 1013611 = 1520417) B1520417
theorem B2029427 : Blo 900574 2029427 := bstep (se 1 (by rfl) ⟨1522070, by rfl⟩ : syracuseStep 2029427 = 3044141) B3044141
theorem B2029463 : Blo 900574 2029463 := bstep (se 1 (by rfl) ⟨1522097, by rfl⟩ : syracuseStep 2029463 = 3044195) B3044195
theorem B1013719 : Blo 900574 1013719 := bstep (se 1 (by rfl) ⟨760289, by rfl⟩ : syracuseStep 1013719 = 1520579) B1520579
theorem B1833025 : Blo 900574 1833025 := bstep (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) B1374769
theorem B2029643 : Blo 900574 2029643 := bstep (se 1 (by rfl) ⟨1522232, by rfl⟩ : syracuseStep 2029643 = 3044465) B3044465
theorem B2029697 : Blo 900574 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B1013899 : Blo 900574 1013899 := bstep (se 1 (by rfl) ⟨760424, by rfl⟩ : syracuseStep 1013899 = 1520849) B1520849
theorem B2750681 : Blo 900574 2750681 := bstep (se 2 (by rfl) ⟨1031505, by rfl⟩ : syracuseStep 2750681 = 2063011) B2063011
theorem B1014007 : Blo 900574 1014007 := bstep (se 1 (by rfl) ⟨760505, by rfl⟩ : syracuseStep 1014007 = 1521011) B1521011
theorem B1931531 : Blo 900574 1931531 := bstep (se 1 (by rfl) ⟨1448648, by rfl⟩ : syracuseStep 1931531 = 2897297) B2897297
theorem B3045707 : Blo 900574 3045707 := bstep (se 1 (by rfl) ⟨2284280, by rfl⟩ : syracuseStep 3045707 = 4568561) B4568561
theorem B2029913 : Blo 900574 2029913 := bstep (se 2 (by rfl) ⟨761217, by rfl⟩ : syracuseStep 2029913 = 1522435) B1522435
theorem B6256997 : Blo 900574 6256997 := bstep (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) B1173187
theorem B2062721 : Blo 900574 2062721 := bstep (se 2 (by rfl) ⟨773520, by rfl⟩ : syracuseStep 2062721 = 1547041) B1547041
theorem B1014187 : Blo 900574 1014187 := bstep (se 1 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 1014187 = 1521281) B1521281
theorem B2030003 : Blo 900574 2030003 := bstep (se 1 (by rfl) ⟨1522502, by rfl⟩ : syracuseStep 2030003 = 3045005) B3045005
theorem B2030039 : Blo 900574 2030039 := bstep (se 1 (by rfl) ⟨1522529, by rfl⟩ : syracuseStep 2030039 = 3045059) B3045059
theorem B1014295 : Blo 900574 1014295 := bstep (se 1 (by rfl) ⟨760721, by rfl⟩ : syracuseStep 1014295 = 1521443) B1521443
theorem B3045977 : Blo 900574 3045977 := bstep (se 2 (by rfl) ⟨1142241, by rfl⟩ : syracuseStep 3045977 = 2284483) B2284483
theorem B2030219 : Blo 900574 2030219 := bstep (se 1 (by rfl) ⟨1522664, by rfl⟩ : syracuseStep 2030219 = 3045329) B3045329
theorem B2030273 : Blo 900574 2030273 := bstep (se 2 (by rfl) ⟨761352, by rfl⟩ : syracuseStep 2030273 = 1522705) B1522705
theorem B1014475 : Blo 900574 1014475 := bstep (se 1 (by rfl) ⟨760856, by rfl⟩ : syracuseStep 1014475 = 1521713) B1521713
theorem B1014583 : Blo 900574 1014583 := bstep (se 1 (by rfl) ⟨760937, by rfl⟩ : syracuseStep 1014583 = 1521875) B1521875
theorem B2030489 : Blo 900574 2030489 := bstep (se 2 (by rfl) ⟨761433, by rfl⟩ : syracuseStep 2030489 = 1522867) B1522867
theorem B1014763 : Blo 900574 1014763 := bstep (se 1 (by rfl) ⟨761072, by rfl⟩ : syracuseStep 1014763 = 1522145) B1522145
theorem B2030579 : Blo 900574 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B1735681 : Blo 900574 1735681 := bstep (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) B1301761
theorem B2030615 : Blo 900574 2030615 := bstep (se 1 (by rfl) ⟨1522961, by rfl⟩ : syracuseStep 2030615 = 3045923) B3045923
theorem B1014871 : Blo 900574 1014871 := bstep (se 1 (by rfl) ⟨761153, by rfl⟩ : syracuseStep 1014871 = 1522307) B1522307
theorem B7699607 : Blo 900574 7699607 := bstep (se 1 (by rfl) ⟨5774705, by rfl⟩ : syracuseStep 7699607 = 11549411) B11549411
theorem B2030795 : Blo 900574 2030795 := bstep (se 1 (by rfl) ⟨1523096, by rfl⟩ : syracuseStep 2030795 = 3046193) B3046193
theorem B2030849 : Blo 900574 2030849 := bstep (se 2 (by rfl) ⟨761568, by rfl⟩ : syracuseStep 2030849 = 1523137) B1523137
theorem B1015051 : Blo 900574 1015051 := bstep (se 1 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 1015051 = 1522577) B1522577
theorem B3046679 : Blo 900574 3046679 := bstep (se 1 (by rfl) ⟨2285009, by rfl⟩ : syracuseStep 3046679 = 4570019) B4570019
theorem B1015159 : Blo 900574 1015159 := bstep (se 1 (by rfl) ⟨761369, by rfl⟩ : syracuseStep 1015159 = 1522739) B1522739
theorem B2031065 : Blo 900574 2031065 := bstep (se 2 (by rfl) ⟨761649, by rfl⟩ : syracuseStep 2031065 = 1523299) B1523299
theorem B1015339 : Blo 900574 1015339 := bstep (se 1 (by rfl) ⟨761504, by rfl⟩ : syracuseStep 1015339 = 1523009) B1523009
theorem B2031155 : Blo 900574 2031155 := bstep (se 1 (by rfl) ⟨1523366, by rfl⟩ : syracuseStep 2031155 = 3046733) B3046733
theorem B2031191 : Blo 900574 2031191 := bstep (se 1 (by rfl) ⟨1523393, by rfl⟩ : syracuseStep 2031191 = 3046787) B3046787
theorem B1015447 : Blo 900574 1015447 := bstep (se 1 (by rfl) ⟨761585, by rfl⟩ : syracuseStep 1015447 = 1523171) B1523171
theorem B2031371 : Blo 900574 2031371 := bstep (se 1 (by rfl) ⟨1523528, by rfl⟩ : syracuseStep 2031371 = 3047057) B3047057
theorem B3047219 : Blo 900574 3047219 := bstep (se 1 (by rfl) ⟨2285414, by rfl⟩ : syracuseStep 3047219 = 4570829) B4570829
theorem B2031425 : Blo 900574 2031425 := bstep (se 2 (by rfl) ⟨761784, by rfl⟩ : syracuseStep 2031425 = 1523569) B1523569
theorem B1015627 : Blo 900574 1015627 := bstep (se 1 (by rfl) ⟨761720, by rfl⟩ : syracuseStep 1015627 = 1523441) B1523441
theorem B1015735 : Blo 900574 1015735 := bstep (se 1 (by rfl) ⟨761801, by rfl⟩ : syracuseStep 1015735 = 1523603) B1523603
theorem B3047435 : Blo 900574 3047435 := bstep (se 1 (by rfl) ⟨2285576, by rfl⟩ : syracuseStep 3047435 = 4571153) B4571153
theorem B2031659 : Blo 900574 2031659 := bstep (se 1 (by rfl) ⟨1523744, by rfl⟩ : syracuseStep 2031659 = 3047489) B3047489
theorem B3047543 : Blo 900574 3047543 := bstep (se 1 (by rfl) ⟨2285657, by rfl⟩ : syracuseStep 3047543 = 4571315) B4571315
theorem B1015951 : Blo 900574 1015951 := bstep (se 1 (by rfl) ⟨761963, by rfl⟩ : syracuseStep 1015951 = 1523927) B1523927
theorem B2032019 : Blo 900574 2032019 := bstep (se 1 (by rfl) ⟨1524014, by rfl⟩ : syracuseStep 2032019 = 3048029) B3048029
theorem B2032073 : Blo 900574 2032073 := bstep (se 2 (by rfl) ⟨762027, by rfl⟩ : syracuseStep 2032073 = 1524055) B1524055
theorem B1016455 : Blo 900574 1016455 := bstep (se 1 (by rfl) ⟨762341, by rfl⟩ : syracuseStep 1016455 = 1524683) B1524683
theorem B3048137 : Blo 900574 3048137 := bstep (se 2 (by rfl) ⟨1143051, by rfl⟩ : syracuseStep 3048137 = 2286103) B2286103
theorem B7045861 : Blo 900574 7045861 := bstep (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) B1321099
theorem B1016635 : Blo 900574 1016635 := bstep (se 1 (by rfl) ⟨762476, by rfl⟩ : syracuseStep 1016635 = 1524953) B1524953
theorem B2032775 : Blo 900574 2032775 := bstep (se 1 (by rfl) ⟨1524581, by rfl⟩ : syracuseStep 2032775 = 3049163) B3049163
theorem B1017103 : Blo 900574 1017103 := bstep (se 1 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 1017103 = 1525655) B1525655
theorem B2032955 : Blo 900574 2032955 := bstep (se 1 (by rfl) ⟨1524716, by rfl⟩ : syracuseStep 2032955 = 3049433) B3049433
theorem B10290563 : Blo 900574 10290563 := bstep (se 1 (by rfl) ⟨7717922, by rfl⟩ : syracuseStep 10290563 = 15435845) B15435845
theorem B3048839 : Blo 900574 3048839 := bstep (se 1 (by rfl) ⟨2286629, by rfl⟩ : syracuseStep 3048839 = 4573259) B4573259
theorem B39060913 : Blo 900574 39060913 := bstep (se 2 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 39060913 = 29295685) B29295685
theorem B2033081 : Blo 900574 2033081 := bstep (se 2 (by rfl) ⟨762405, by rfl⟩ : syracuseStep 2033081 = 1524811) B1524811
theorem B2885149 : Blo 900574 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B1541675 : Blo 900574 1541675 := bstep (se 1 (by rfl) ⟨1156256, by rfl⟩ : syracuseStep 1541675 = 2312513) B2312513
theorem B3049217 : Blo 900574 3049217 := bstep (se 2 (by rfl) ⟨1143456, by rfl⟩ : syracuseStep 3049217 = 2286913) B2286913
theorem B1017607 : Blo 900574 1017607 := bstep (se 1 (by rfl) ⟨763205, by rfl⟩ : syracuseStep 1017607 = 1526411) B1526411
theorem B2033423 : Blo 900574 2033423 := bstep (se 1 (by rfl) ⟨1525067, by rfl⟩ : syracuseStep 2033423 = 3050135) B3050135
theorem B2033441 : Blo 900574 2033441 := bstep (se 2 (by rfl) ⟨762540, by rfl⟩ : syracuseStep 2033441 = 1525081) B1525081
theorem B2197547 : Blo 900574 2197547 := bstep (se 1 (by rfl) ⟨1648160, by rfl⟩ : syracuseStep 2197547 = 3296321) B3296321
theorem B2164823 : Blo 900574 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B2033783 : Blo 900574 2033783 := bstep (se 1 (by rfl) ⟨1525337, by rfl⟩ : syracuseStep 2033783 = 3050675) B3050675
theorem B2033963 : Blo 900574 2033963 := bstep (se 1 (by rfl) ⟨1525472, by rfl⟩ : syracuseStep 2033963 = 3050945) B3050945
theorem B3050027 : Blo 900574 3050027 := bstep (se 1 (by rfl) ⟨2287520, by rfl⟩ : syracuseStep 3050027 = 4575041) B4575041
theorem B2034323 : Blo 900574 2034323 := bstep (se 1 (by rfl) ⟨1525742, by rfl⟩ : syracuseStep 2034323 = 3051485) B3051485
theorem B2034377 : Blo 900574 2034377 := bstep (se 2 (by rfl) ⟨762891, by rfl⟩ : syracuseStep 2034377 = 1525783) B1525783
theorem B5147651 : Blo 900574 5147651 := bstep (se 1 (by rfl) ⟨3860738, by rfl⟩ : syracuseStep 5147651 = 7721477) B7721477
theorem B1444907 : Blo 900574 1444907 := bstep (se 1 (by rfl) ⟨1083680, by rfl⟩ : syracuseStep 1444907 = 2167361) B2167361
theorem B2035079 : Blo 900574 2035079 := bstep (se 1 (by rfl) ⟨1526309, by rfl⟩ : syracuseStep 2035079 = 3052619) B3052619
theorem B5148107 : Blo 900574 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B2035259 : Blo 900574 2035259 := bstep (se 1 (by rfl) ⟨1526444, by rfl⟩ : syracuseStep 2035259 = 3052889) B3052889
theorem B3051323 : Blo 900574 3051323 := bstep (se 1 (by rfl) ⟨2288492, by rfl⟩ : syracuseStep 3051323 = 4576985) B4576985
theorem B2887559 : Blo 900574 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B5148791 : Blo 900574 5148791 := bstep (se 1 (by rfl) ⟨3861593, by rfl⟩ : syracuseStep 5148791 = 7723187) B7723187
theorem B3051809 : Blo 900574 3051809 := bstep (se 2 (by rfl) ⟨1144428, by rfl⟩ : syracuseStep 3051809 = 2288857) B2288857
theorem B6853085 : Blo 900574 6853085 := bstep (se 3 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 6853085 = 2569907) B2569907
theorem B1282807 : Blo 900574 1282807 := bstep (se 1 (by rfl) ⟨962105, by rfl⟩ : syracuseStep 1282807 = 1924211) B1924211
theorem B2167553 : Blo 900574 2167553 := bstep (se 2 (by rfl) ⟨812832, by rfl⟩ : syracuseStep 2167553 = 1625665) B1625665
theorem B3052403 : Blo 900574 3052403 := bstep (se 1 (by rfl) ⟨2289302, by rfl⟩ : syracuseStep 3052403 = 4578605) B4578605
theorem B14062517 : Blo 900574 14062517 := bstep (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) B1318361
theorem B4166585 : Blo 900574 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B2167841 : Blo 900574 2167841 := bstep (se 2 (by rfl) ⟨812940, by rfl⟩ : syracuseStep 2167841 = 1625881) B1625881
theorem B1283131 : Blo 900574 1283131 := bstep (se 1 (by rfl) ⟨962348, by rfl⟩ : syracuseStep 1283131 = 1924697) B1924697
theorem B2888993 : Blo 900574 2888993 := bstep (se 2 (by rfl) ⟨1083372, by rfl⟩ : syracuseStep 2888993 = 2166745) B2166745
theorem B1283627 : Blo 900574 1283627 := bstep (se 1 (by rfl) ⟨962720, by rfl⟩ : syracuseStep 1283627 = 1925441) B1925441
theorem B1447483 : Blo 900574 1447483 := bstep (se 1 (by rfl) ⟨1085612, by rfl⟩ : syracuseStep 1447483 = 2171225) B2171225
theorem B1709687 : Blo 900574 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B1709839 : Blo 900574 1709839 := bstep (se 1 (by rfl) ⟨1282379, by rfl⟩ : syracuseStep 1709839 = 2564759) B2564759
theorem B16455473 : Blo 900574 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B4560785 : Blo 900574 4560785 := bstep (se 2 (by rfl) ⟨1710294, by rfl⟩ : syracuseStep 4560785 = 3420589) B3420589
theorem B5478347 : Blo 900574 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B20846605 : Blo 900574 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B5150749 : Blo 900574 5150749 := bstep (se 3 (by rfl) ⟨965765, by rfl⟩ : syracuseStep 5150749 = 1931531) B1931531
theorem B21993565 : Blo 900574 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B1710227 : Blo 900574 1710227 := bstep (se 1 (by rfl) ⟨1282670, by rfl⟩ : syracuseStep 1710227 = 2565341) B2565341
theorem B5151275 : Blo 900574 5151275 := bstep (se 1 (by rfl) ⟨3863456, by rfl⟩ : syracuseStep 5151275 = 7726913) B7726913
theorem B3250925 : Blo 900574 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B2169611 : Blo 900574 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B2169659 : Blo 900574 2169659 := bstep (se 1 (by rfl) ⟨1627244, by rfl⟩ : syracuseStep 2169659 = 3254489) B3254489
theorem B1285193 : Blo 900574 1285193 := bstep (se 2 (by rfl) ⟨481947, by rfl⟩ : syracuseStep 1285193 = 963895) B963895
theorem B1350971 : Blo 900574 1350971 := bstep (se 1 (by rfl) ⟨1013228, by rfl⟩ : syracuseStep 1350971 = 2026457) B2026457
theorem B1351031 : Blo 900574 1351031 := bstep (se 1 (by rfl) ⟨1013273, by rfl⟩ : syracuseStep 1351031 = 2026547) B2026547
theorem B6495623 : Blo 900574 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1351055 : Blo 900574 1351055 := bstep (se 1 (by rfl) ⟨1013291, by rfl⟩ : syracuseStep 1351055 = 2026583) B2026583
theorem B4332953 : Blo 900574 4332953 := bstep (se 2 (by rfl) ⟨1624857, by rfl⟩ : syracuseStep 4332953 = 3249715) B3249715
theorem B1351097 : Blo 900574 1351097 := bstep (se 2 (by rfl) ⟨506661, by rfl⟩ : syracuseStep 1351097 = 1013323) B1013323
theorem B1220027 : Blo 900574 1220027 := bstep (se 1 (by rfl) ⟨915020, by rfl⟩ : syracuseStep 1220027 = 1830041) B1830041
theorem B11148749 : Blo 900574 11148749 := bstep (se 3 (by rfl) ⟨2090390, by rfl⟩ : syracuseStep 11148749 = 4180781) B4180781
theorem B1351175 : Blo 900574 1351175 := bstep (se 1 (by rfl) ⟨1013381, by rfl⟩ : syracuseStep 1351175 = 2026763) B2026763
theorem B1711631 : Blo 900574 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B1351211 : Blo 900574 1351211 := bstep (se 1 (by rfl) ⟨1013408, by rfl⟩ : syracuseStep 1351211 = 2026817) B2026817
theorem B1351241 : Blo 900574 1351241 := bstep (se 2 (by rfl) ⟨506715, by rfl⟩ : syracuseStep 1351241 = 1013431) B1013431
theorem B2891351 : Blo 900574 2891351 := bstep (se 1 (by rfl) ⟨2168513, by rfl⟩ : syracuseStep 2891351 = 4337027) B4337027
theorem B1285751 : Blo 900574 1285751 := bstep (se 1 (by rfl) ⟨964313, by rfl⟩ : syracuseStep 1285751 = 1928627) B1928627
theorem B1351355 : Blo 900574 1351355 := bstep (se 1 (by rfl) ⟨1013516, by rfl⟩ : syracuseStep 1351355 = 2027033) B2027033
theorem B1351415 : Blo 900574 1351415 := bstep (se 1 (by rfl) ⟨1013561, by rfl⟩ : syracuseStep 1351415 = 2027123) B2027123
theorem B1351439 : Blo 900574 1351439 := bstep (se 1 (by rfl) ⟨1013579, by rfl⟩ : syracuseStep 1351439 = 2027159) B2027159
theorem B1351481 : Blo 900574 1351481 := bstep (se 2 (by rfl) ⟨506805, by rfl⟩ : syracuseStep 1351481 = 1013611) B1013611
theorem B1351559 : Blo 900574 1351559 := bstep (se 1 (by rfl) ⟨1013669, by rfl⟩ : syracuseStep 1351559 = 2027339) B2027339
theorem B1351595 : Blo 900574 1351595 := bstep (se 1 (by rfl) ⟨1013696, by rfl⟩ : syracuseStep 1351595 = 2027393) B2027393
theorem B1286059 : Blo 900574 1286059 := bstep (se 1 (by rfl) ⟨964544, by rfl⟩ : syracuseStep 1286059 = 1929089) B1929089
theorem B1351625 : Blo 900574 1351625 := bstep (se 2 (by rfl) ⟨506859, by rfl⟩ : syracuseStep 1351625 = 1013719) B1013719
theorem B4562891 : Blo 900574 4562891 := bstep (se 1 (by rfl) ⟨3422168, by rfl⟩ : syracuseStep 4562891 = 6844337) B6844337
theorem B1712171 : Blo 900574 1712171 := bstep (se 1 (by rfl) ⟨1284128, by rfl⟩ : syracuseStep 1712171 = 2568257) B2568257
theorem B1351739 : Blo 900574 1351739 := bstep (se 1 (by rfl) ⟨1013804, by rfl⟩ : syracuseStep 1351739 = 2027609) B2027609
theorem B1351799 : Blo 900574 1351799 := bstep (se 1 (by rfl) ⟨1013849, by rfl⟩ : syracuseStep 1351799 = 2027699) B2027699
theorem B1351823 : Blo 900574 1351823 := bstep (se 1 (by rfl) ⟨1013867, by rfl⟩ : syracuseStep 1351823 = 2027735) B2027735
theorem B1220779 : Blo 900574 1220779 := bstep (se 1 (by rfl) ⟨915584, by rfl⟩ : syracuseStep 1220779 = 1831169) B1831169
theorem B1351865 : Blo 900574 1351865 := bstep (se 2 (by rfl) ⟨506949, by rfl⟩ : syracuseStep 1351865 = 1013899) B1013899
theorem B29270261 : Blo 900574 29270261 := bstep (se 5 (by rfl) ⟨1372043, by rfl⟩ : syracuseStep 29270261 = 2744087) B2744087
theorem B1351943 : Blo 900574 1351943 := bstep (se 1 (by rfl) ⟨1013957, by rfl⟩ : syracuseStep 1351943 = 2027915) B2027915
theorem B4563215 : Blo 900574 4563215 := bstep (se 1 (by rfl) ⟨3422411, by rfl⟩ : syracuseStep 4563215 = 6844823) B6844823
theorem B1351979 : Blo 900574 1351979 := bstep (se 1 (by rfl) ⟨1013984, by rfl⟩ : syracuseStep 1351979 = 2027969) B2027969
theorem B1352009 : Blo 900574 1352009 := bstep (se 2 (by rfl) ⟨507003, by rfl⟩ : syracuseStep 1352009 = 1014007) B1014007
theorem B1286543 : Blo 900574 1286543 := bstep (se 1 (by rfl) ⟨964907, by rfl⟩ : syracuseStep 1286543 = 1929815) B1929815
theorem B4170131 : Blo 900574 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B1352123 : Blo 900574 1352123 := bstep (se 1 (by rfl) ⟨1014092, by rfl⟩ : syracuseStep 1352123 = 2028185) B2028185
theorem B1352183 : Blo 900574 1352183 := bstep (se 1 (by rfl) ⟨1014137, by rfl⟩ : syracuseStep 1352183 = 2028275) B2028275
theorem B5153291 : Blo 900574 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B1352207 : Blo 900574 1352207 := bstep (se 1 (by rfl) ⟨1014155, by rfl⟩ : syracuseStep 1352207 = 2028311) B2028311
theorem B1352249 : Blo 900574 1352249 := bstep (se 2 (by rfl) ⟨507093, by rfl⟩ : syracuseStep 1352249 = 1014187) B1014187
theorem B1352327 : Blo 900574 1352327 := bstep (se 1 (by rfl) ⟨1014245, by rfl⟩ : syracuseStep 1352327 = 2028491) B2028491
theorem B1352363 : Blo 900574 1352363 := bstep (se 1 (by rfl) ⟨1014272, by rfl⟩ : syracuseStep 1352363 = 2028545) B2028545
theorem B29303477 : Blo 900574 29303477 := bstep (se 5 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 29303477 = 2747201) B2747201
theorem B9249473 : Blo 900574 9249473 := bstep (se 2 (by rfl) ⟨3468552, by rfl⟩ : syracuseStep 9249473 = 6937105) B6937105
theorem B1352393 : Blo 900574 1352393 := bstep (se 2 (by rfl) ⟨507147, by rfl⟩ : syracuseStep 1352393 = 1014295) B1014295
theorem B1352507 : Blo 900574 1352507 := bstep (se 1 (by rfl) ⟨1014380, by rfl⟩ : syracuseStep 1352507 = 2028761) B2028761
theorem B1352567 : Blo 900574 1352567 := bstep (se 1 (by rfl) ⟨1014425, by rfl⟩ : syracuseStep 1352567 = 2028851) B2028851
theorem B1352591 : Blo 900574 1352591 := bstep (se 1 (by rfl) ⟨1014443, by rfl⟩ : syracuseStep 1352591 = 2028887) B2028887
theorem B1352633 : Blo 900574 1352633 := bstep (se 2 (by rfl) ⟨507237, by rfl⟩ : syracuseStep 1352633 = 1014475) B1014475
theorem B13018117 : Blo 900574 13018117 := bstep (se 4 (by rfl) ⟨1220448, by rfl⟩ : syracuseStep 13018117 = 2440897) B2440897
theorem B1352711 : Blo 900574 1352711 := bstep (se 1 (by rfl) ⟨1014533, by rfl⟩ : syracuseStep 1352711 = 2029067) B2029067
theorem B1352747 : Blo 900574 1352747 := bstep (se 1 (by rfl) ⟨1014560, by rfl⟩ : syracuseStep 1352747 = 2029121) B2029121
theorem B1352777 : Blo 900574 1352777 := bstep (se 2 (by rfl) ⟨507291, by rfl⟩ : syracuseStep 1352777 = 1014583) B1014583
theorem B1713287 : Blo 900574 1713287 := bstep (se 1 (by rfl) ⟨1284965, by rfl⟩ : syracuseStep 1713287 = 2569931) B2569931
theorem B1352891 : Blo 900574 1352891 := bstep (se 1 (by rfl) ⟨1014668, by rfl⟩ : syracuseStep 1352891 = 2029337) B2029337
theorem B1352951 : Blo 900574 1352951 := bstep (se 1 (by rfl) ⟨1014713, by rfl⟩ : syracuseStep 1352951 = 2029427) B2029427
theorem B1352975 : Blo 900574 1352975 := bstep (se 1 (by rfl) ⟨1014731, by rfl⟩ : syracuseStep 1352975 = 2029463) B2029463
theorem B1353017 : Blo 900574 1353017 := bstep (se 2 (by rfl) ⟨507381, by rfl⟩ : syracuseStep 1353017 = 1014763) B1014763
theorem B1353095 : Blo 900574 1353095 := bstep (se 1 (by rfl) ⟨1014821, by rfl⟩ : syracuseStep 1353095 = 2029643) B2029643
theorem B1353131 : Blo 900574 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B1353161 : Blo 900574 1353161 := bstep (se 2 (by rfl) ⟨507435, by rfl⟩ : syracuseStep 1353161 = 1014871) B1014871
theorem B10429955 : Blo 900574 10429955 := bstep (se 1 (by rfl) ⟨7822466, by rfl⟩ : syracuseStep 10429955 = 15644933) B15644933
theorem B1353275 : Blo 900574 1353275 := bstep (se 1 (by rfl) ⟨1014956, by rfl⟩ : syracuseStep 1353275 = 2029913) B2029913
theorem B4171331 : Blo 900574 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B37561931 : Blo 900574 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B1353335 : Blo 900574 1353335 := bstep (se 1 (by rfl) ⟨1015001, by rfl⟩ : syracuseStep 1353335 = 2030003) B2030003
theorem B1353359 : Blo 900574 1353359 := bstep (se 1 (by rfl) ⟨1015019, by rfl⟩ : syracuseStep 1353359 = 2030039) B2030039
theorem B1713811 : Blo 900574 1713811 := bstep (se 1 (by rfl) ⟨1285358, by rfl⟩ : syracuseStep 1713811 = 2570717) B2570717
theorem B1353401 : Blo 900574 1353401 := bstep (se 2 (by rfl) ⟨507525, by rfl⟩ : syracuseStep 1353401 = 1015051) B1015051
theorem B4564673 : Blo 900574 4564673 := bstep (se 2 (by rfl) ⟨1711752, by rfl⟩ : syracuseStep 4564673 = 3423505) B3423505
theorem B1353479 : Blo 900574 1353479 := bstep (se 1 (by rfl) ⟨1015109, by rfl⟩ : syracuseStep 1353479 = 2030219) B2030219
theorem B1353515 : Blo 900574 1353515 := bstep (se 1 (by rfl) ⟨1015136, by rfl⟩ : syracuseStep 1353515 = 2030273) B2030273
theorem B1353545 : Blo 900574 1353545 := bstep (se 2 (by rfl) ⟨507579, by rfl⟩ : syracuseStep 1353545 = 1015159) B1015159
theorem B2434951 : Blo 900574 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B1353659 : Blo 900574 1353659 := bstep (se 1 (by rfl) ⟨1015244, by rfl⟩ : syracuseStep 1353659 = 2030489) B2030489
theorem B1353719 : Blo 900574 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B1353743 : Blo 900574 1353743 := bstep (se 1 (by rfl) ⟨1015307, by rfl⟩ : syracuseStep 1353743 = 2030615) B2030615
theorem B1353785 : Blo 900574 1353785 := bstep (se 2 (by rfl) ⟨507669, by rfl⟩ : syracuseStep 1353785 = 1015339) B1015339
theorem B1353863 : Blo 900574 1353863 := bstep (se 1 (by rfl) ⟨1015397, by rfl⟩ : syracuseStep 1353863 = 2030795) B2030795
theorem B1353899 : Blo 900574 1353899 := bstep (se 1 (by rfl) ⟨1015424, by rfl⟩ : syracuseStep 1353899 = 2030849) B2030849
theorem B1353929 : Blo 900574 1353929 := bstep (se 2 (by rfl) ⟨507723, by rfl⟩ : syracuseStep 1353929 = 1015447) B1015447
theorem B1354043 : Blo 900574 1354043 := bstep (se 1 (by rfl) ⟨1015532, by rfl⟩ : syracuseStep 1354043 = 2031065) B2031065
theorem B2173243 : Blo 900574 2173243 := bstep (se 1 (by rfl) ⟨1629932, by rfl⟩ : syracuseStep 2173243 = 3259865) B3259865
theorem B1354103 : Blo 900574 1354103 := bstep (se 1 (by rfl) ⟨1015577, by rfl⟩ : syracuseStep 1354103 = 2031155) B2031155
theorem B1354127 : Blo 900574 1354127 := bstep (se 1 (by rfl) ⟨1015595, by rfl⟩ : syracuseStep 1354127 = 2031191) B2031191
theorem B1354169 : Blo 900574 1354169 := bstep (se 2 (by rfl) ⟨507813, by rfl⟩ : syracuseStep 1354169 = 1015627) B1015627
theorem B1354247 : Blo 900574 1354247 := bstep (se 1 (by rfl) ⟨1015685, by rfl⟩ : syracuseStep 1354247 = 2031371) B2031371
theorem B2435599 : Blo 900574 2435599 := bstep (se 1 (by rfl) ⟨1826699, by rfl⟩ : syracuseStep 2435599 = 3653399) B3653399
theorem B5777963 : Blo 900574 5777963 := bstep (se 1 (by rfl) ⟨4333472, by rfl⟩ : syracuseStep 5777963 = 8666945) B8666945
theorem B1354283 : Blo 900574 1354283 := bstep (se 1 (by rfl) ⟨1015712, by rfl⟩ : syracuseStep 1354283 = 2031425) B2031425
theorem B18491969 : Blo 900574 18491969 := bstep (se 2 (by rfl) ⟨6934488, by rfl⟩ : syracuseStep 18491969 = 13868977) B13868977
theorem B1354313 : Blo 900574 1354313 := bstep (se 2 (by rfl) ⟨507867, by rfl⟩ : syracuseStep 1354313 = 1015735) B1015735
theorem B1354427 : Blo 900574 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B1354487 : Blo 900574 1354487 := bstep (se 1 (by rfl) ⟨1015865, by rfl⟩ : syracuseStep 1354487 = 2031731) B2031731
theorem B5778191 : Blo 900574 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B1354511 : Blo 900574 1354511 := bstep (se 1 (by rfl) ⟨1015883, by rfl⟩ : syracuseStep 1354511 = 2031767) B2031767
theorem B1354553 : Blo 900574 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B1715003 : Blo 900574 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B1354631 : Blo 900574 1354631 := bstep (se 1 (by rfl) ⟨1015973, by rfl⟩ : syracuseStep 1354631 = 2031947) B2031947
theorem B1354667 : Blo 900574 1354667 := bstep (se 1 (by rfl) ⟨1016000, by rfl⟩ : syracuseStep 1354667 = 2032001) B2032001
theorem B1354697 : Blo 900574 1354697 := bstep (se 2 (by rfl) ⟨508011, by rfl⟩ : syracuseStep 1354697 = 1016023) B1016023
theorem B4565969 : Blo 900574 4565969 := bstep (se 2 (by rfl) ⟨1712238, by rfl⟩ : syracuseStep 4565969 = 3424477) B3424477
theorem B1354811 : Blo 900574 1354811 := bstep (se 1 (by rfl) ⟨1016108, by rfl⟩ : syracuseStep 1354811 = 2032217) B2032217
theorem B1354871 : Blo 900574 1354871 := bstep (se 1 (by rfl) ⟨1016153, by rfl⟩ : syracuseStep 1354871 = 2032307) B2032307
theorem B1354895 : Blo 900574 1354895 := bstep (se 1 (by rfl) ⟨1016171, by rfl⟩ : syracuseStep 1354895 = 2032343) B2032343
theorem B1354937 : Blo 900574 1354937 := bstep (se 2 (by rfl) ⟨508101, by rfl⟩ : syracuseStep 1354937 = 1016203) B1016203
theorem B1355015 : Blo 900574 1355015 := bstep (se 1 (by rfl) ⟨1016261, by rfl⟩ : syracuseStep 1355015 = 2032523) B2032523
theorem B1715489 : Blo 900574 1715489 := bstep (se 2 (by rfl) ⟨643308, by rfl⟩ : syracuseStep 1715489 = 1286617) B1286617
theorem B1355051 : Blo 900574 1355051 := bstep (se 1 (by rfl) ⟨1016288, by rfl⟩ : syracuseStep 1355051 = 2032577) B2032577
theorem B10431803 : Blo 900574 10431803 := bstep (se 1 (by rfl) ⟨7823852, by rfl⟩ : syracuseStep 10431803 = 15647705) B15647705
theorem B1355081 : Blo 900574 1355081 := bstep (se 2 (by rfl) ⟨508155, by rfl⟩ : syracuseStep 1355081 = 1016311) B1016311
theorem B1355195 : Blo 900574 1355195 := bstep (se 1 (by rfl) ⟨1016396, by rfl⟩ : syracuseStep 1355195 = 2032793) B2032793
theorem B7318993 : Blo 900574 7318993 := bstep (se 2 (by rfl) ⟨2744622, by rfl⟩ : syracuseStep 7318993 = 5489245) B5489245
theorem B1355255 : Blo 900574 1355255 := bstep (se 1 (by rfl) ⟨1016441, by rfl⟩ : syracuseStep 1355255 = 2032883) B2032883
theorem B1355279 : Blo 900574 1355279 := bstep (se 1 (by rfl) ⟨1016459, by rfl⟩ : syracuseStep 1355279 = 2032919) B2032919
theorem B2436637 : Blo 900574 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B1715755 : Blo 900574 1715755 := bstep (se 1 (by rfl) ⟨1286816, by rfl⟩ : syracuseStep 1715755 = 2573633) B2573633
theorem B1355321 : Blo 900574 1355321 := bstep (se 2 (by rfl) ⟨508245, by rfl⟩ : syracuseStep 1355321 = 1016491) B1016491
theorem B1355399 : Blo 900574 1355399 := bstep (se 1 (by rfl) ⟨1016549, by rfl⟩ : syracuseStep 1355399 = 2033099) B2033099
theorem B1355435 : Blo 900574 1355435 := bstep (se 1 (by rfl) ⟨1016576, by rfl⟩ : syracuseStep 1355435 = 2033153) B2033153
theorem B1355465 : Blo 900574 1355465 := bstep (se 2 (by rfl) ⟨508299, by rfl⟩ : syracuseStep 1355465 = 1016599) B1016599
theorem B1355579 : Blo 900574 1355579 := bstep (se 1 (by rfl) ⟨1016684, by rfl⟩ : syracuseStep 1355579 = 2033369) B2033369
theorem B2436983 : Blo 900574 2436983 := bstep (se 1 (by rfl) ⟨1827737, by rfl⟩ : syracuseStep 2436983 = 3655475) B3655475
theorem B1355639 : Blo 900574 1355639 := bstep (se 1 (by rfl) ⟨1016729, by rfl⟩ : syracuseStep 1355639 = 2033459) B2033459
theorem B962447 : Blo 900574 962447 := bstep (se 1 (by rfl) ⟨721835, by rfl⟩ : syracuseStep 962447 = 1443671) B1443671
theorem B1355663 : Blo 900574 1355663 := bstep (se 1 (by rfl) ⟨1016747, by rfl⟩ : syracuseStep 1355663 = 2033495) B2033495
theorem B3420089 : Blo 900574 3420089 := bstep (se 2 (by rfl) ⟨1282533, by rfl⟩ : syracuseStep 3420089 = 2565067) B2565067
theorem B1355705 : Blo 900574 1355705 := bstep (se 2 (by rfl) ⟨508389, by rfl⟩ : syracuseStep 1355705 = 1016779) B1016779
theorem B1355783 : Blo 900574 1355783 := bstep (se 1 (by rfl) ⟨1016837, by rfl⟩ : syracuseStep 1355783 = 2033675) B2033675
theorem B1355819 : Blo 900574 1355819 := bstep (se 1 (by rfl) ⟨1016864, by rfl⟩ : syracuseStep 1355819 = 2033729) B2033729
theorem B6860861 : Blo 900574 6860861 := bstep (se 3 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 6860861 = 2572823) B2572823
theorem B1355849 : Blo 900574 1355849 := bstep (se 2 (by rfl) ⟨508443, by rfl⟩ : syracuseStep 1355849 = 1016887) B1016887
theorem B1519735 : Blo 900574 1519735 := bstep (se 1 (by rfl) ⟨1139801, by rfl⟩ : syracuseStep 1519735 = 2279603) B2279603
theorem B1355963 : Blo 900574 1355963 := bstep (se 1 (by rfl) ⟨1016972, by rfl⟩ : syracuseStep 1355963 = 2033945) B2033945
theorem B6336713 : Blo 900574 6336713 := bstep (se 2 (by rfl) ⟨2376267, by rfl⟩ : syracuseStep 6336713 = 4752535) B4752535
theorem B1356023 : Blo 900574 1356023 := bstep (se 1 (by rfl) ⟨1017017, by rfl⟩ : syracuseStep 1356023 = 2034035) B2034035
theorem B2568449 : Blo 900574 2568449 := bstep (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) B1926337
theorem B3256577 : Blo 900574 3256577 := bstep (se 2 (by rfl) ⟨1221216, by rfl⟩ : syracuseStep 3256577 = 2442433) B2442433
theorem B1356047 : Blo 900574 1356047 := bstep (se 1 (by rfl) ⟨1017035, by rfl⟩ : syracuseStep 1356047 = 2034071) B2034071
theorem B1356089 : Blo 900574 1356089 := bstep (se 2 (by rfl) ⟨508533, by rfl⟩ : syracuseStep 1356089 = 1017067) B1017067
theorem B1519931 : Blo 900574 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B3092795 : Blo 900574 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B3256691 : Blo 900574 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B1356167 : Blo 900574 1356167 := bstep (se 1 (by rfl) ⟨1017125, by rfl⟩ : syracuseStep 1356167 = 2034251) B2034251
theorem B1356203 : Blo 900574 1356203 := bstep (se 1 (by rfl) ⟨1017152, by rfl⟩ : syracuseStep 1356203 = 2034305) B2034305
theorem B1356233 : Blo 900574 1356233 := bstep (se 2 (by rfl) ⟨508587, by rfl⟩ : syracuseStep 1356233 = 1017175) B1017175
theorem B1356347 : Blo 900574 1356347 := bstep (se 1 (by rfl) ⟨1017260, by rfl⟩ : syracuseStep 1356347 = 2034521) B2034521
theorem B1356407 : Blo 900574 1356407 := bstep (se 1 (by rfl) ⟨1017305, by rfl⟩ : syracuseStep 1356407 = 2034611) B2034611
theorem B1716871 : Blo 900574 1716871 := bstep (se 1 (by rfl) ⟨1287653, by rfl⟩ : syracuseStep 1716871 = 2575307) B2575307
theorem B1356431 : Blo 900574 1356431 := bstep (se 1 (by rfl) ⟨1017323, by rfl⟩ : syracuseStep 1356431 = 2034647) B2034647
theorem B1356473 : Blo 900574 1356473 := bstep (se 2 (by rfl) ⟨508677, by rfl⟩ : syracuseStep 1356473 = 1017355) B1017355
theorem B1520329 : Blo 900574 1520329 := bstep (se 2 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 1520329 = 1140247) B1140247
theorem B2568905 : Blo 900574 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B1356551 : Blo 900574 1356551 := bstep (se 1 (by rfl) ⟨1017413, by rfl⟩ : syracuseStep 1356551 = 2034827) B2034827
theorem B1651499 : Blo 900574 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B1356587 : Blo 900574 1356587 := bstep (se 1 (by rfl) ⟨1017440, by rfl⟩ : syracuseStep 1356587 = 2034881) B2034881
theorem B1356617 : Blo 900574 1356617 := bstep (se 2 (by rfl) ⟨508731, by rfl⟩ : syracuseStep 1356617 = 1017463) B1017463
theorem B8926027 : Blo 900574 8926027 := bstep (se 1 (by rfl) ⟨6694520, by rfl⟩ : syracuseStep 8926027 = 13389041) B13389041
theorem B9777995 : Blo 900574 9777995 := bstep (se 1 (by rfl) ⟨7333496, by rfl⟩ : syracuseStep 9777995 = 14666993) B14666993
theorem B3421075 : Blo 900574 3421075 := bstep (se 1 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 3421075 = 5131613) B5131613
theorem B1356731 : Blo 900574 1356731 := bstep (se 1 (by rfl) ⟨1017548, by rfl⟩ : syracuseStep 1356731 = 2035097) B2035097
theorem B1356791 : Blo 900574 1356791 := bstep (se 1 (by rfl) ⟨1017593, by rfl⟩ : syracuseStep 1356791 = 2035187) B2035187
theorem B4568075 : Blo 900574 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B1356815 : Blo 900574 1356815 := bstep (se 1 (by rfl) ⟨1017611, by rfl⟩ : syracuseStep 1356815 = 2035223) B2035223
theorem B2569259 : Blo 900574 2569259 := bstep (se 1 (by rfl) ⟨1926944, by rfl⟩ : syracuseStep 2569259 = 3853889) B3853889
theorem B1356857 : Blo 900574 1356857 := bstep (se 2 (by rfl) ⟨508821, by rfl⟩ : syracuseStep 1356857 = 1017643) B1017643
theorem B4568237 : Blo 900574 4568237 := bstep (se 3 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 4568237 = 1713089) B1713089
theorem B1521031 : Blo 900574 1521031 := bstep (se 1 (by rfl) ⟨1140773, by rfl⟩ : syracuseStep 1521031 = 2281547) B2281547
theorem B2569657 : Blo 900574 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B12367667 : Blo 900574 12367667 := bstep (se 1 (by rfl) ⟨9275750, by rfl⟩ : syracuseStep 12367667 = 18551501) B18551501
theorem B1521679 : Blo 900574 1521679 := bstep (se 1 (by rfl) ⟨1141259, by rfl⟩ : syracuseStep 1521679 = 2282519) B2282519
theorem B8665289 : Blo 900574 8665289 := bstep (se 2 (by rfl) ⟨3249483, by rfl⟩ : syracuseStep 8665289 = 6498967) B6498967
theorem B48085397 : Blo 900574 48085397 := bstep (se 6 (by rfl) ⟨1127001, by rfl⟩ : syracuseStep 48085397 = 2254003) B2254003
theorem B1522219 : Blo 900574 1522219 := bstep (se 1 (by rfl) ⟨1141664, by rfl⟩ : syracuseStep 1522219 = 2283329) B2283329
theorem B3422807 : Blo 900574 3422807 := bstep (se 1 (by rfl) ⟨2567105, by rfl⟩ : syracuseStep 3422807 = 5134211) B5134211
theorem B2570899 : Blo 900574 2570899 := bstep (se 1 (by rfl) ⟨1928174, by rfl⟩ : syracuseStep 2570899 = 3856349) B3856349
theorem B1522361 : Blo 900574 1522361 := bstep (se 2 (by rfl) ⟨570885, by rfl⟩ : syracuseStep 1522361 = 1141771) B1141771
theorem B4569857 : Blo 900574 4569857 := bstep (se 2 (by rfl) ⟨1713696, by rfl⟩ : syracuseStep 4569857 = 3427393) B3427393
theorem B2603863 : Blo 900574 2603863 := bstep (se 1 (by rfl) ⟨1952897, by rfl⟩ : syracuseStep 2603863 = 3905795) B3905795
theorem B3652619 : Blo 900574 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B3423293 : Blo 900574 3423293 := bstep (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) B1283735
theorem B1523063 : Blo 900574 1523063 := bstep (se 1 (by rfl) ⟨1142297, by rfl⟩ : syracuseStep 1523063 = 2284595) B2284595
theorem B6864263 : Blo 900574 6864263 := bstep (se 1 (by rfl) ⟨5148197, by rfl⟩ : syracuseStep 6864263 = 10296395) B10296395
theorem B900615 : Blo 900574 900615 := bstep (se 1 (by rfl) ⟨675461, by rfl⟩ : syracuseStep 900615 = 1350923) B1350923
theorem B900623 : Blo 900574 900623 := bstep (se 1 (by rfl) ⟨675467, by rfl⟩ : syracuseStep 900623 = 1350935) B1350935
theorem B4570667 : Blo 900574 4570667 := bstep (se 1 (by rfl) ⟨3428000, by rfl⟩ : syracuseStep 4570667 = 6856001) B6856001
theorem B900667 : Blo 900574 900667 := bstep (se 1 (by rfl) ⟨675500, by rfl⟩ : syracuseStep 900667 = 1351001) B1351001
theorem B900743 : Blo 900574 900743 := bstep (se 1 (by rfl) ⟨675557, by rfl⟩ : syracuseStep 900743 = 1351115) B1351115
theorem B900751 : Blo 900574 900751 := bstep (se 1 (by rfl) ⟨675563, by rfl⟩ : syracuseStep 900751 = 1351127) B1351127
theorem B900795 : Blo 900574 900795 := bstep (se 1 (by rfl) ⟨675596, by rfl⟩ : syracuseStep 900795 = 1351193) B1351193
theorem B11550437 : Blo 900574 11550437 := bstep (se 4 (by rfl) ⟨1082853, by rfl⟩ : syracuseStep 11550437 = 2165707) B2165707
theorem B900871 : Blo 900574 900871 := bstep (se 1 (by rfl) ⟨675653, by rfl⟩ : syracuseStep 900871 = 1351307) B1351307
theorem B900879 : Blo 900574 900879 := bstep (se 1 (by rfl) ⟨675659, by rfl⟩ : syracuseStep 900879 = 1351319) B1351319
theorem B900923 : Blo 900574 900923 := bstep (se 1 (by rfl) ⟨675692, by rfl⟩ : syracuseStep 900923 = 1351385) B1351385
theorem B1523515 : Blo 900574 1523515 := bstep (se 1 (by rfl) ⟨1142636, by rfl⟩ : syracuseStep 1523515 = 2285273) B2285273
theorem B900999 : Blo 900574 900999 := bstep (se 1 (by rfl) ⟨675749, by rfl⟩ : syracuseStep 900999 = 1351499) B1351499
theorem B901007 : Blo 900574 901007 := bstep (se 1 (by rfl) ⟨675755, by rfl⟩ : syracuseStep 901007 = 1351511) B1351511
theorem B901051 : Blo 900574 901051 := bstep (se 1 (by rfl) ⟨675788, by rfl⟩ : syracuseStep 901051 = 1351577) B1351577
theorem B1523657 : Blo 900574 1523657 := bstep (se 2 (by rfl) ⟨571371, by rfl⟩ : syracuseStep 1523657 = 1142743) B1142743
theorem B901127 : Blo 900574 901127 := bstep (se 1 (by rfl) ⟨675845, by rfl⟩ : syracuseStep 901127 = 1351691) B1351691
theorem B901135 : Blo 900574 901135 := bstep (se 1 (by rfl) ⟨675851, by rfl⟩ : syracuseStep 901135 = 1351703) B1351703
theorem B901179 : Blo 900574 901179 := bstep (se 1 (by rfl) ⟨675884, by rfl⟩ : syracuseStep 901179 = 1351769) B1351769
theorem B901255 : Blo 900574 901255 := bstep (se 1 (by rfl) ⟨675941, by rfl⟩ : syracuseStep 901255 = 1351883) B1351883
theorem B901263 : Blo 900574 901263 := bstep (se 1 (by rfl) ⟨675947, by rfl⟩ : syracuseStep 901263 = 1351895) B1351895
theorem B901307 : Blo 900574 901307 := bstep (se 1 (by rfl) ⟨675980, by rfl⟩ : syracuseStep 901307 = 1351961) B1351961
theorem B9257161 : Blo 900574 9257161 := bstep (se 2 (by rfl) ⟨3471435, by rfl⟩ : syracuseStep 9257161 = 6942871) B6942871
theorem B901383 : Blo 900574 901383 := bstep (se 1 (by rfl) ⟨676037, by rfl⟩ : syracuseStep 901383 = 1352075) B1352075
theorem B901391 : Blo 900574 901391 := bstep (se 1 (by rfl) ⟨676043, by rfl⟩ : syracuseStep 901391 = 1352087) B1352087
theorem B2572573 : Blo 900574 2572573 := bstep (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) B964715
theorem B901435 : Blo 900574 901435 := bstep (se 1 (by rfl) ⟨676076, by rfl⟩ : syracuseStep 901435 = 1352153) B1352153
theorem B2572631 : Blo 900574 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B901511 : Blo 900574 901511 := bstep (se 1 (by rfl) ⟨676133, by rfl⟩ : syracuseStep 901511 = 1352267) B1352267
theorem B901519 : Blo 900574 901519 := bstep (se 1 (by rfl) ⟨676139, by rfl⟩ : syracuseStep 901519 = 1352279) B1352279
theorem B901563 : Blo 900574 901563 := bstep (se 1 (by rfl) ⟨676172, by rfl⟩ : syracuseStep 901563 = 1352345) B1352345
theorem B901639 : Blo 900574 901639 := bstep (se 1 (by rfl) ⟨676229, by rfl⟩ : syracuseStep 901639 = 1352459) B1352459
theorem B901647 : Blo 900574 901647 := bstep (se 1 (by rfl) ⟨676235, by rfl⟩ : syracuseStep 901647 = 1352471) B1352471
theorem B901691 : Blo 900574 901691 := bstep (se 1 (by rfl) ⟨676268, by rfl⟩ : syracuseStep 901691 = 1352537) B1352537
theorem B8667749 : Blo 900574 8667749 := bstep (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) B1625203
theorem B901767 : Blo 900574 901767 := bstep (se 1 (by rfl) ⟨676325, by rfl⟩ : syracuseStep 901767 = 1352651) B1352651
theorem B1524359 : Blo 900574 1524359 := bstep (se 1 (by rfl) ⟨1143269, by rfl⟩ : syracuseStep 1524359 = 2286539) B2286539
theorem B901775 : Blo 900574 901775 := bstep (se 1 (by rfl) ⟨676331, by rfl⟩ : syracuseStep 901775 = 1352663) B1352663
theorem B901819 : Blo 900574 901819 := bstep (se 1 (by rfl) ⟨676364, by rfl⟩ : syracuseStep 901819 = 1352729) B1352729
theorem B901895 : Blo 900574 901895 := bstep (se 1 (by rfl) ⟨676421, by rfl⟩ : syracuseStep 901895 = 1352843) B1352843
theorem B901903 : Blo 900574 901903 := bstep (se 1 (by rfl) ⟨676427, by rfl⟩ : syracuseStep 901903 = 1352855) B1352855
theorem B901947 : Blo 900574 901947 := bstep (se 1 (by rfl) ⟨676460, by rfl⟩ : syracuseStep 901947 = 1352921) B1352921
theorem B4571963 : Blo 900574 4571963 := bstep (se 1 (by rfl) ⟨3428972, by rfl⟩ : syracuseStep 4571963 = 6857945) B6857945
theorem B902023 : Blo 900574 902023 := bstep (se 1 (by rfl) ⟨676517, by rfl⟩ : syracuseStep 902023 = 1353035) B1353035
theorem B902031 : Blo 900574 902031 := bstep (se 1 (by rfl) ⟨676523, by rfl⟩ : syracuseStep 902031 = 1353047) B1353047
theorem B902075 : Blo 900574 902075 := bstep (se 1 (by rfl) ⟨676556, by rfl⟩ : syracuseStep 902075 = 1353113) B1353113
theorem B4572125 : Blo 900574 4572125 := bstep (se 3 (by rfl) ⟨857273, by rfl⟩ : syracuseStep 4572125 = 1714547) B1714547
theorem B902151 : Blo 900574 902151 := bstep (se 1 (by rfl) ⟨676613, by rfl⟩ : syracuseStep 902151 = 1353227) B1353227
theorem B902159 : Blo 900574 902159 := bstep (se 1 (by rfl) ⟨676619, by rfl⟩ : syracuseStep 902159 = 1353239) B1353239
theorem B902203 : Blo 900574 902203 := bstep (se 1 (by rfl) ⟨676652, by rfl⟩ : syracuseStep 902203 = 1353305) B1353305
theorem B902279 : Blo 900574 902279 := bstep (se 1 (by rfl) ⟨676709, by rfl⟩ : syracuseStep 902279 = 1353419) B1353419
theorem B902287 : Blo 900574 902287 := bstep (se 1 (by rfl) ⟨676715, by rfl⟩ : syracuseStep 902287 = 1353431) B1353431
theorem B902331 : Blo 900574 902331 := bstep (se 1 (by rfl) ⟨676748, by rfl⟩ : syracuseStep 902331 = 1353497) B1353497
theorem B902407 : Blo 900574 902407 := bstep (se 1 (by rfl) ⟨676805, by rfl⟩ : syracuseStep 902407 = 1353611) B1353611
theorem B902415 : Blo 900574 902415 := bstep (se 1 (by rfl) ⟨676811, by rfl⟩ : syracuseStep 902415 = 1353623) B1353623
theorem B1525007 : Blo 900574 1525007 := bstep (se 1 (by rfl) ⟨1143755, by rfl⟩ : syracuseStep 1525007 = 2287511) B2287511
theorem B4572449 : Blo 900574 4572449 := bstep (se 2 (by rfl) ⟨1714668, by rfl⟩ : syracuseStep 4572449 = 3429337) B3429337
theorem B2934049 : Blo 900574 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B902459 : Blo 900574 902459 := bstep (se 1 (by rfl) ⟨676844, by rfl⟩ : syracuseStep 902459 = 1353689) B1353689
theorem B902535 : Blo 900574 902535 := bstep (se 1 (by rfl) ⟨676901, by rfl⟩ : syracuseStep 902535 = 1353803) B1353803
theorem B902543 : Blo 900574 902543 := bstep (se 1 (by rfl) ⟨676907, by rfl⟩ : syracuseStep 902543 = 1353815) B1353815
theorem B2442649 : Blo 900574 2442649 := bstep (se 2 (by rfl) ⟨915993, by rfl⟩ : syracuseStep 2442649 = 1831987) B1831987
theorem B902587 : Blo 900574 902587 := bstep (se 1 (by rfl) ⟨676940, by rfl⟩ : syracuseStep 902587 = 1353881) B1353881
theorem B902663 : Blo 900574 902663 := bstep (se 1 (by rfl) ⟨676997, by rfl⟩ : syracuseStep 902663 = 1353995) B1353995
theorem B902671 : Blo 900574 902671 := bstep (se 1 (by rfl) ⟨677003, by rfl⟩ : syracuseStep 902671 = 1354007) B1354007
theorem B2344481 : Blo 900574 2344481 := bstep (se 2 (by rfl) ⟨879180, by rfl⟩ : syracuseStep 2344481 = 1758361) B1758361
theorem B902715 : Blo 900574 902715 := bstep (se 1 (by rfl) ⟨677036, by rfl⟩ : syracuseStep 902715 = 1354073) B1354073
theorem B37045835 : Blo 900574 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B902791 : Blo 900574 902791 := bstep (se 1 (by rfl) ⟨677093, by rfl⟩ : syracuseStep 902791 = 1354187) B1354187
theorem B902799 : Blo 900574 902799 := bstep (se 1 (by rfl) ⟨677099, by rfl⟩ : syracuseStep 902799 = 1354199) B1354199
theorem B902843 : Blo 900574 902843 := bstep (se 1 (by rfl) ⟨677132, by rfl⟩ : syracuseStep 902843 = 1354265) B1354265
theorem B902919 : Blo 900574 902919 := bstep (se 1 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 902919 = 1354379) B1354379
theorem B902927 : Blo 900574 902927 := bstep (se 1 (by rfl) ⟨677195, by rfl⟩ : syracuseStep 902927 = 1354391) B1354391
theorem B1525547 : Blo 900574 1525547 := bstep (se 1 (by rfl) ⟨1144160, by rfl⟩ : syracuseStep 1525547 = 2288321) B2288321
theorem B902971 : Blo 900574 902971 := bstep (se 1 (by rfl) ⟨677228, by rfl⟩ : syracuseStep 902971 = 1354457) B1354457
theorem B903047 : Blo 900574 903047 := bstep (se 1 (by rfl) ⟨677285, by rfl⟩ : syracuseStep 903047 = 1354571) B1354571
theorem B903055 : Blo 900574 903055 := bstep (se 1 (by rfl) ⟨677291, by rfl⟩ : syracuseStep 903055 = 1354583) B1354583
theorem B2606995 : Blo 900574 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B903099 : Blo 900574 903099 := bstep (se 1 (by rfl) ⟨677324, by rfl⟩ : syracuseStep 903099 = 1354649) B1354649
theorem B2574281 : Blo 900574 2574281 := bstep (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) B1930711
theorem B903175 : Blo 900574 903175 := bstep (se 1 (by rfl) ⟨677381, by rfl⟩ : syracuseStep 903175 = 1354763) B1354763
theorem B3852299 : Blo 900574 3852299 := bstep (se 1 (by rfl) ⟨2889224, by rfl⟩ : syracuseStep 3852299 = 5778449) B5778449
theorem B1624079 : Blo 900574 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B903183 : Blo 900574 903183 := bstep (se 1 (by rfl) ⟨677387, by rfl⟩ : syracuseStep 903183 = 1354775) B1354775
theorem B903227 : Blo 900574 903227 := bstep (se 1 (by rfl) ⟨677420, by rfl⟩ : syracuseStep 903227 = 1354841) B1354841
theorem B903303 : Blo 900574 903303 := bstep (se 1 (by rfl) ⟨677477, by rfl⟩ : syracuseStep 903303 = 1354955) B1354955
theorem B903311 : Blo 900574 903311 := bstep (se 1 (by rfl) ⟨677483, by rfl⟩ : syracuseStep 903311 = 1354967) B1354967
theorem B1525945 : Blo 900574 1525945 := bstep (se 2 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 1525945 = 1144459) B1144459
theorem B903355 : Blo 900574 903355 := bstep (se 1 (by rfl) ⟨677516, by rfl⟩ : syracuseStep 903355 = 1355033) B1355033
theorem B4573421 : Blo 900574 4573421 := bstep (se 3 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 4573421 = 1715033) B1715033
theorem B12503285 : Blo 900574 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B903431 : Blo 900574 903431 := bstep (se 1 (by rfl) ⟨677573, by rfl⟩ : syracuseStep 903431 = 1355147) B1355147
theorem B903439 : Blo 900574 903439 := bstep (se 1 (by rfl) ⟨677579, by rfl⟩ : syracuseStep 903439 = 1355159) B1355159
theorem B903483 : Blo 900574 903483 := bstep (se 1 (by rfl) ⟨677612, by rfl⟩ : syracuseStep 903483 = 1355225) B1355225
theorem B17353025 : Blo 900574 17353025 := bstep (se 2 (by rfl) ⟨6507384, by rfl⟩ : syracuseStep 17353025 = 13014769) B13014769
theorem B5130611 : Blo 900574 5130611 := bstep (se 1 (by rfl) ⟨3847958, by rfl⟩ : syracuseStep 5130611 = 7695917) B7695917
theorem B3426695 : Blo 900574 3426695 := bstep (se 1 (by rfl) ⟨2570021, by rfl⟩ : syracuseStep 3426695 = 5140043) B5140043
theorem B903559 : Blo 900574 903559 := bstep (se 1 (by rfl) ⟨677669, by rfl⟩ : syracuseStep 903559 = 1355339) B1355339
theorem B903567 : Blo 900574 903567 := bstep (se 1 (by rfl) ⟨677675, by rfl⟩ : syracuseStep 903567 = 1355351) B1355351
theorem B2935187 : Blo 900574 2935187 := bstep (se 1 (by rfl) ⟨2201390, by rfl⟩ : syracuseStep 2935187 = 4402781) B4402781
theorem B5491097 : Blo 900574 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B903611 : Blo 900574 903611 := bstep (se 1 (by rfl) ⟨677708, by rfl⟩ : syracuseStep 903611 = 1355417) B1355417
theorem B903687 : Blo 900574 903687 := bstep (se 1 (by rfl) ⟨677765, by rfl⟩ : syracuseStep 903687 = 1355531) B1355531
theorem B2279947 : Blo 900574 2279947 := bstep (se 1 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 2279947 = 3419921) B3419921
theorem B903695 : Blo 900574 903695 := bstep (se 1 (by rfl) ⟨677771, by rfl⟩ : syracuseStep 903695 = 1355543) B1355543
theorem B903739 : Blo 900574 903739 := bstep (se 1 (by rfl) ⟨677804, by rfl⟩ : syracuseStep 903739 = 1355609) B1355609
theorem B903815 : Blo 900574 903815 := bstep (se 1 (by rfl) ⟨677861, by rfl⟩ : syracuseStep 903815 = 1355723) B1355723
theorem B903823 : Blo 900574 903823 := bstep (se 1 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 903823 = 1355735) B1355735
theorem B2280089 : Blo 900574 2280089 := bstep (se 2 (by rfl) ⟨855033, by rfl⟩ : syracuseStep 2280089 = 1710067) B1710067
theorem B903867 : Blo 900574 903867 := bstep (se 1 (by rfl) ⟨677900, by rfl⟩ : syracuseStep 903867 = 1355801) B1355801
theorem B2444033 : Blo 900574 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B903943 : Blo 900574 903943 := bstep (se 1 (by rfl) ⟨677957, by rfl⟩ : syracuseStep 903943 = 1355915) B1355915
theorem B7424783 : Blo 900574 7424783 := bstep (se 1 (by rfl) ⟨5568587, by rfl⟩ : syracuseStep 7424783 = 11137175) B11137175
theorem B903951 : Blo 900574 903951 := bstep (se 1 (by rfl) ⟨677963, by rfl⟩ : syracuseStep 903951 = 1355927) B1355927
theorem B2444075 : Blo 900574 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B2575147 : Blo 900574 2575147 := bstep (se 1 (by rfl) ⟨1931360, by rfl⟩ : syracuseStep 2575147 = 3862721) B3862721
theorem B2280251 : Blo 900574 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B903995 : Blo 900574 903995 := bstep (se 1 (by rfl) ⟨677996, by rfl⟩ : syracuseStep 903995 = 1355993) B1355993
theorem B2739005 : Blo 900574 2739005 := bstep (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) B1027127
theorem B8244083 : Blo 900574 8244083 := bstep (se 1 (by rfl) ⟨6183062, by rfl⟩ : syracuseStep 8244083 = 12366125) B12366125
theorem B904071 : Blo 900574 904071 := bstep (se 1 (by rfl) ⟨678053, by rfl⟩ : syracuseStep 904071 = 1356107) B1356107
theorem B904079 : Blo 900574 904079 := bstep (se 1 (by rfl) ⟨678059, by rfl⟩ : syracuseStep 904079 = 1356119) B1356119
theorem B904123 : Blo 900574 904123 := bstep (se 1 (by rfl) ⟨678092, by rfl⟩ : syracuseStep 904123 = 1356185) B1356185
theorem B904199 : Blo 900574 904199 := bstep (se 1 (by rfl) ⟨678149, by rfl⟩ : syracuseStep 904199 = 1356299) B1356299
theorem B904207 : Blo 900574 904207 := bstep (se 1 (by rfl) ⟨678155, by rfl⟩ : syracuseStep 904207 = 1356311) B1356311
theorem B4574231 : Blo 900574 4574231 := bstep (se 1 (by rfl) ⟨3430673, by rfl⟩ : syracuseStep 4574231 = 6861347) B6861347
theorem B904251 : Blo 900574 904251 := bstep (se 1 (by rfl) ⟨678188, by rfl⟩ : syracuseStep 904251 = 1356377) B1356377
theorem B2575421 : Blo 900574 2575421 := bstep (se 3 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 2575421 = 965783) B965783
theorem B904327 : Blo 900574 904327 := bstep (se 1 (by rfl) ⟨678245, by rfl⟩ : syracuseStep 904327 = 1356491) B1356491
theorem B904335 : Blo 900574 904335 := bstep (se 1 (by rfl) ⟨678251, by rfl⟩ : syracuseStep 904335 = 1356503) B1356503
theorem B2280595 : Blo 900574 2280595 := bstep (se 1 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 2280595 = 3420893) B3420893
theorem B904379 : Blo 900574 904379 := bstep (se 1 (by rfl) ⟨678284, by rfl⟩ : syracuseStep 904379 = 1356569) B1356569
theorem B904455 : Blo 900574 904455 := bstep (se 1 (by rfl) ⟨678341, by rfl⟩ : syracuseStep 904455 = 1356683) B1356683
theorem B904463 : Blo 900574 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B2280737 : Blo 900574 2280737 := bstep (se 2 (by rfl) ⟨855276, by rfl⟩ : syracuseStep 2280737 = 1710553) B1710553
theorem B904507 : Blo 900574 904507 := bstep (se 1 (by rfl) ⟨678380, by rfl⟩ : syracuseStep 904507 = 1356761) B1356761
theorem B4345177 : Blo 900574 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B2575763 : Blo 900574 2575763 := bstep (se 1 (by rfl) ⟨1931822, by rfl⟩ : syracuseStep 2575763 = 3863645) B3863645
theorem B15650333 : Blo 900574 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B3526415 : Blo 900574 3526415 := bstep (se 1 (by rfl) ⟨2644811, by rfl⟩ : syracuseStep 3526415 = 5289623) B5289623
theorem B5132069 : Blo 900574 5132069 := bstep (se 4 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 5132069 = 962263) B962263
theorem B2314241 : Blo 900574 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B3854573 : Blo 900574 3854573 := bstep (se 3 (by rfl) ⟨722732, by rfl⟩ : syracuseStep 3854573 = 1445465) B1445465
theorem B2281729 : Blo 900574 2281729 := bstep (se 2 (by rfl) ⟨855648, by rfl⟩ : syracuseStep 2281729 = 1711297) B1711297
theorem B5132753 : Blo 900574 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B10277441 : Blo 900574 10277441 := bstep (se 2 (by rfl) ⟨3854040, by rfl⟩ : syracuseStep 10277441 = 7708081) B7708081
theorem B4117079 : Blo 900574 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B4346561 : Blo 900574 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B4117229 : Blo 900574 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B5133071 : Blo 900574 5133071 := bstep (se 1 (by rfl) ⟨3849803, by rfl⟩ : syracuseStep 5133071 = 7699607) B7699607
theorem B2282327 : Blo 900574 2282327 := bstep (se 1 (by rfl) ⟨1711745, by rfl⟩ : syracuseStep 2282327 = 3423491) B3423491
theorem B1561529 : Blo 900574 1561529 := bstep (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) B1171147
theorem B2282539 : Blo 900574 2282539 := bstep (se 1 (by rfl) ⟨1711904, by rfl⟩ : syracuseStep 2282539 = 3423809) B3423809
theorem B2282681 : Blo 900574 2282681 := bstep (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) B1712011
theorem B7722539 : Blo 900574 7722539 := bstep (se 1 (by rfl) ⟨5791904, by rfl⟩ : syracuseStep 7722539 = 11583809) B11583809
theorem B2054089 : Blo 900574 2054089 := bstep (se 2 (by rfl) ⟨770283, by rfl⟩ : syracuseStep 2054089 = 1540567) B1540567
theorem B4118539 : Blo 900574 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B4577309 : Blo 900574 4577309 := bstep (se 3 (by rfl) ⟨858245, by rfl⟩ : syracuseStep 4577309 = 1716491) B1716491
theorem B2283673 : Blo 900574 2283673 := bstep (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) B1712755
theorem B5134529 : Blo 900574 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B3856673 : Blo 900574 3856673 := bstep (se 2 (by rfl) ⟨1446252, by rfl⟩ : syracuseStep 3856673 = 2892505) B2892505
theorem B2283835 : Blo 900574 2283835 := bstep (se 1 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 2283835 = 3425753) B3425753
theorem B2283977 : Blo 900574 2283977 := bstep (se 2 (by rfl) ⟨856491, by rfl⟩ : syracuseStep 2283977 = 1712983) B1712983
theorem B5200337 : Blo 900574 5200337 := bstep (se 2 (by rfl) ⟨1950126, by rfl⟩ : syracuseStep 5200337 = 3900253) B3900253
theorem B4577795 : Blo 900574 4577795 := bstep (se 1 (by rfl) ⟨3433346, by rfl⟩ : syracuseStep 4577795 = 6866693) B6866693
theorem B1628807 : Blo 900574 1628807 := bstep (se 1 (by rfl) ⟨1221605, by rfl⟩ : syracuseStep 1628807 = 2443211) B2443211
theorem B2284321 : Blo 900574 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B1629227 : Blo 900574 1629227 := bstep (se 1 (by rfl) ⟨1221920, by rfl⟩ : syracuseStep 1629227 = 2443841) B2443841
theorem B2743357 : Blo 900574 2743357 := bstep (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) B1028759
theorem B2284919 : Blo 900574 2284919 := bstep (se 1 (by rfl) ⟨1713689, by rfl⟩ : syracuseStep 2284919 = 3427379) B3427379
theorem B1924553 : Blo 900574 1924553 := bstep (se 2 (by rfl) ⟨721707, by rfl⟩ : syracuseStep 1924553 = 1443415) B1443415
theorem B4120183 : Blo 900574 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B5496835 : Blo 900574 5496835 := bstep (se 1 (by rfl) ⟨4122626, by rfl⟩ : syracuseStep 5496835 = 8245253) B8245253
theorem B1958023 : Blo 900574 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B1827017 : Blo 900574 1827017 := bstep (se 2 (by rfl) ⟨685131, by rfl⟩ : syracuseStep 1827017 = 1370263) B1370263
theorem B2679101 : Blo 900574 2679101 := bstep (se 3 (by rfl) ⟨502331, by rfl⟩ : syracuseStep 2679101 = 1004663) B1004663
theorem B4874813 : Blo 900574 4874813 := bstep (se 3 (by rfl) ⟨914027, by rfl⟩ : syracuseStep 4874813 = 1828055) B1828055
theorem B2286215 : Blo 900574 2286215 := bstep (se 1 (by rfl) ⟨1714661, by rfl⟩ : syracuseStep 2286215 = 3429323) B3429323
theorem B2286265 : Blo 900574 2286265 := bstep (se 2 (by rfl) ⟨857349, by rfl⟩ : syracuseStep 2286265 = 1714699) B1714699
theorem B13394723 : Blo 900574 13394723 := bstep (se 1 (by rfl) ⟨10046042, by rfl⟩ : syracuseStep 13394723 = 20092085) B20092085
theorem B5498057 : Blo 900574 5498057 := bstep (se 2 (by rfl) ⟨2061771, by rfl⟩ : syracuseStep 5498057 = 4123543) B4123543
theorem B2286863 : Blo 900574 2286863 := bstep (se 1 (by rfl) ⟨1715147, by rfl⟩ : syracuseStep 2286863 = 3430295) B3430295
theorem B1369387 : Blo 900574 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B13395557 : Blo 900574 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B3041171 : Blo 900574 3041171 := bstep (se 1 (by rfl) ⟨2280878, by rfl⟩ : syracuseStep 3041171 = 4561757) B4561757
theorem B2287561 : Blo 900574 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B1140743 : Blo 900574 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B2287703 : Blo 900574 2287703 := bstep (se 1 (by rfl) ⟨1715777, by rfl⟩ : syracuseStep 2287703 = 3431555) B3431555
theorem B2746667 : Blo 900574 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B5794183 : Blo 900574 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B3860945 : Blo 900574 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B1927739 : Blo 900574 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B1141391 : Blo 900574 1141391 := bstep (se 1 (by rfl) ⟨856043, by rfl⟩ : syracuseStep 1141391 = 1712087) B1712087
theorem B3664673 : Blo 900574 3664673 := bstep (se 2 (by rfl) ⟨1374252, by rfl⟩ : syracuseStep 3664673 = 2748505) B2748505
theorem B5860147 : Blo 900574 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B5499737 : Blo 900574 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B2026511 : Blo 900574 2026511 := bstep (se 1 (by rfl) ⟨1519883, by rfl⟩ : syracuseStep 2026511 = 3039767) B3039767
theorem B2026529 : Blo 900574 2026529 := bstep (se 2 (by rfl) ⟨759948, by rfl⟩ : syracuseStep 2026529 = 1519897) B1519897
theorem B10546309 : Blo 900574 10546309 := bstep (se 4 (by rfl) ⟨988716, by rfl⟩ : syracuseStep 10546309 = 1977433) B1977433
theorem B3042575 : Blo 900574 3042575 := bstep (se 1 (by rfl) ⟨2281931, by rfl⟩ : syracuseStep 3042575 = 4563863) B4563863
theorem B2026871 : Blo 900574 2026871 := bstep (se 1 (by rfl) ⟨1520153, by rfl⟩ : syracuseStep 2026871 = 3040307) B3040307
theorem B3042845 : Blo 900574 3042845 := bstep (se 3 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 3042845 = 1141067) B1141067
theorem B2027051 : Blo 900574 2027051 := bstep (se 1 (by rfl) ⟨1520288, by rfl⟩ : syracuseStep 2027051 = 3040577) B3040577
theorem B1928747 : Blo 900574 1928747 := bstep (se 1 (by rfl) ⟨1446560, by rfl⟩ : syracuseStep 1928747 = 2893121) B2893121
theorem B1371791 : Blo 900574 1371791 := bstep (se 1 (by rfl) ⟨1028843, by rfl⟩ : syracuseStep 1371791 = 2057687) B2057687
theorem B5500709 : Blo 900574 5500709 := bstep (se 4 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 5500709 = 1031383) B1031383
theorem B5205875 : Blo 900574 5205875 := bstep (se 1 (by rfl) ⟨3904406, by rfl⟩ : syracuseStep 5205875 = 7808813) B7808813
theorem B2027411 : Blo 900574 2027411 := bstep (se 1 (by rfl) ⟨1520558, by rfl⟩ : syracuseStep 2027411 = 3041117) B3041117
theorem B2027465 : Blo 900574 2027465 := bstep (se 2 (by rfl) ⟨760299, by rfl⟩ : syracuseStep 2027465 = 1520599) B1520599
theorem B21918251 : Blo 900574 21918251 := bstep (se 1 (by rfl) ⟨16438688, by rfl⟩ : syracuseStep 21918251 = 32877377) B32877377
theorem B2028167 : Blo 900574 2028167 := bstep (se 1 (by rfl) ⟨1521125, by rfl⟩ : syracuseStep 2028167 = 3042251) B3042251
theorem B17330881 : Blo 900574 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B4125473 : Blo 900574 4125473 := bstep (se 2 (by rfl) ⟨1547052, by rfl⟩ : syracuseStep 4125473 = 3094105) B3094105
theorem B2028347 : Blo 900574 2028347 := bstep (se 1 (by rfl) ⟨1521260, by rfl⟩ : syracuseStep 2028347 = 3042521) B3042521
theorem B3044249 : Blo 900574 3044249 := bstep (se 2 (by rfl) ⟨1141593, by rfl⟩ : syracuseStep 3044249 = 2283187) B2283187
theorem B2028473 : Blo 900574 2028473 := bstep (se 2 (by rfl) ⟨760677, by rfl⟩ : syracuseStep 2028473 = 1521355) B1521355
theorem B1930387 : Blo 900574 1930387 := bstep (se 1 (by rfl) ⟨1447790, by rfl⟩ : syracuseStep 1930387 = 2895581) B2895581
theorem B1373431 : Blo 900574 1373431 := bstep (se 1 (by rfl) ⟨1030073, by rfl⟩ : syracuseStep 1373431 = 2060147) B2060147
theorem B2028815 : Blo 900574 2028815 := bstep (se 1 (by rfl) ⟨1521611, by rfl⟩ : syracuseStep 2028815 = 3043223) B3043223
theorem B2028833 : Blo 900574 2028833 := bstep (se 2 (by rfl) ⟨760812, by rfl⟩ : syracuseStep 2028833 = 1521625) B1521625
theorem B5141819 : Blo 900574 5141819 := bstep (se 1 (by rfl) ⟨3856364, by rfl⟩ : syracuseStep 5141819 = 7712729) B7712729
theorem B4879763 : Blo 900574 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B1930643 : Blo 900574 1930643 := bstep (se 1 (by rfl) ⟨1447982, by rfl⟩ : syracuseStep 1930643 = 2895965) B2895965
theorem B1013179 : Blo 900574 1013179 := bstep (se 1 (by rfl) ⟨759884, by rfl⟩ : syracuseStep 1013179 = 1519769) B1519769
theorem B1144363 : Blo 900574 1144363 := bstep (se 1 (by rfl) ⟨858272, by rfl⟩ : syracuseStep 1144363 = 1716545) B1716545
theorem B1734203 : Blo 900574 1734203 := bstep (se 1 (by rfl) ⟨1300652, by rfl⟩ : syracuseStep 1734203 = 2601305) B2601305
theorem B4388413 : Blo 900574 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B3044951 : Blo 900574 3044951 := bstep (se 1 (by rfl) ⟨2283713, by rfl⟩ : syracuseStep 3044951 = 4567427) B4567427
theorem B2029175 : Blo 900574 2029175 := bstep (se 1 (by rfl) ⟨1521881, by rfl⟩ : syracuseStep 2029175 = 3043763) B3043763
theorem B2029355 : Blo 900574 2029355 := bstep (se 1 (by rfl) ⟨1522016, by rfl⟩ : syracuseStep 2029355 = 3044033) B3044033
theorem B1013647 : Blo 900574 1013647 := bstep (se 1 (by rfl) ⟨760235, by rfl⟩ : syracuseStep 1013647 = 1520471) B1520471
theorem B3045437 : Blo 900574 3045437 := bstep (se 3 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 3045437 = 1142039) B1142039
theorem B2029715 : Blo 900574 2029715 := bstep (se 1 (by rfl) ⟨1522286, by rfl⟩ : syracuseStep 2029715 = 3044573) B3044573
theorem B5208257 : Blo 900574 5208257 := bstep (se 2 (by rfl) ⟨1953096, by rfl⟩ : syracuseStep 5208257 = 3906193) B3906193
theorem B2029769 : Blo 900574 2029769 := bstep (se 2 (by rfl) ⟨761163, by rfl⟩ : syracuseStep 2029769 = 1522327) B1522327
theorem B1014151 : Blo 900574 1014151 := bstep (se 1 (by rfl) ⟨760613, by rfl⟩ : syracuseStep 1014151 = 1521227) B1521227
theorem B1014331 : Blo 900574 1014331 := bstep (se 1 (by rfl) ⟨760748, by rfl⟩ : syracuseStep 1014331 = 1521497) B1521497
theorem B5143277 : Blo 900574 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B1833787 : Blo 900574 1833787 := bstep (se 1 (by rfl) ⟨1375340, by rfl⟩ : syracuseStep 1833787 = 2750681) B2750681
theorem B2030471 : Blo 900574 2030471 := bstep (se 1 (by rfl) ⟨1522853, by rfl⟩ : syracuseStep 2030471 = 3045707) B3045707
theorem B1375147 : Blo 900574 1375147 := bstep (se 1 (by rfl) ⟨1031360, by rfl⟩ : syracuseStep 1375147 = 2062721) B2062721
theorem B1014799 : Blo 900574 1014799 := bstep (se 1 (by rfl) ⟨761099, by rfl⟩ : syracuseStep 1014799 = 1522199) B1522199
theorem B2030651 : Blo 900574 2030651 := bstep (se 1 (by rfl) ⟨1522988, by rfl⟩ : syracuseStep 2030651 = 3045977) B3045977
theorem B2030777 : Blo 900574 2030777 := bstep (se 2 (by rfl) ⟨761541, by rfl⟩ : syracuseStep 2030777 = 1523083) B1523083
theorem B3046841 : Blo 900574 3046841 := bstep (se 2 (by rfl) ⟨1142565, by rfl⟩ : syracuseStep 3046841 = 2285131) B2285131
theorem B1015303 : Blo 900574 1015303 := bstep (se 1 (by rfl) ⟨761477, by rfl⟩ : syracuseStep 1015303 = 1522955) B1522955
theorem B2031119 : Blo 900574 2031119 := bstep (se 1 (by rfl) ⟨1523339, by rfl⟩ : syracuseStep 2031119 = 3046679) B3046679
theorem B2031137 : Blo 900574 2031137 := bstep (se 2 (by rfl) ⟨761676, by rfl⟩ : syracuseStep 2031137 = 1523353) B1523353
theorem B10976887 : Blo 900574 10976887 := bstep (se 1 (by rfl) ⟨8232665, by rfl⟩ : syracuseStep 10976887 = 16465331) B16465331
theorem B1015483 : Blo 900574 1015483 := bstep (se 1 (by rfl) ⟨761612, by rfl⟩ : syracuseStep 1015483 = 1523225) B1523225
theorem B4947749 : Blo 900574 4947749 := bstep (se 4 (by rfl) ⟨463851, by rfl⟩ : syracuseStep 4947749 = 927703) B927703
theorem B2031479 : Blo 900574 2031479 := bstep (se 1 (by rfl) ⟨1523609, by rfl⟩ : syracuseStep 2031479 = 3047219) B3047219
theorem B2031623 : Blo 900574 2031623 := bstep (se 1 (by rfl) ⟨1523717, by rfl⟩ : syracuseStep 2031623 = 3047435) B3047435
theorem B2031695 : Blo 900574 2031695 := bstep (se 1 (by rfl) ⟨1523771, by rfl⟩ : syracuseStep 2031695 = 3047543) B3047543
theorem B38961269 : Blo 900574 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B1016239 : Blo 900574 1016239 := bstep (se 1 (by rfl) ⟨762179, by rfl⟩ : syracuseStep 1016239 = 1524359) B1524359
theorem B2032091 : Blo 900574 2032091 := bstep (se 1 (by rfl) ⟨1524068, by rfl⟩ : syracuseStep 2032091 = 3048137) B3048137
theorem B3047975 : Blo 900574 3047975 := bstep (se 1 (by rfl) ⟨2285981, by rfl⟩ : syracuseStep 3047975 = 4571963) B4571963
theorem B3048083 : Blo 900574 3048083 := bstep (se 1 (by rfl) ⟨2286062, by rfl⟩ : syracuseStep 3048083 = 4572125) B4572125
theorem B6849197 : Blo 900574 6849197 := bstep (se 3 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 6849197 = 2568449) B2568449
theorem B1016671 : Blo 900574 1016671 := bstep (se 1 (by rfl) ⟨762503, by rfl⟩ : syracuseStep 1016671 = 1525007) B1525007
theorem B3048299 : Blo 900574 3048299 := bstep (se 1 (by rfl) ⟨2286224, by rfl⟩ : syracuseStep 3048299 = 4572449) B4572449
theorem B3048353 : Blo 900574 3048353 := bstep (se 2 (by rfl) ⟨1143132, by rfl⟩ : syracuseStep 3048353 = 2286265) B2286265
theorem B2032559 : Blo 900574 2032559 := bstep (se 1 (by rfl) ⟨1524419, by rfl⟩ : syracuseStep 2032559 = 3048839) B3048839
theorem B8684509 : Blo 900574 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B2032811 : Blo 900574 2032811 := bstep (se 1 (by rfl) ⟨1524608, by rfl⟩ : syracuseStep 2032811 = 3049217) B3049217
theorem B1017031 : Blo 900574 1017031 := bstep (se 1 (by rfl) ⟨762773, by rfl⟩ : syracuseStep 1017031 = 1525547) B1525547
theorem B1082719 : Blo 900574 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B1443215 : Blo 900574 1443215 := bstep (se 1 (by rfl) ⟨1082411, by rfl⟩ : syracuseStep 1443215 = 2164823) B2164823
theorem B3048947 : Blo 900574 3048947 := bstep (se 1 (by rfl) ⟨2286710, by rfl⟩ : syracuseStep 3048947 = 4573421) B4573421
theorem B11568683 : Blo 900574 11568683 := bstep (se 1 (by rfl) ⟨8676512, by rfl⟩ : syracuseStep 11568683 = 17353025) B17353025
theorem B10978877 : Blo 900574 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B2033351 : Blo 900574 2033351 := bstep (se 1 (by rfl) ⟨1525013, by rfl⟩ : syracuseStep 2033351 = 3050027) B3050027
theorem B4949855 : Blo 900574 4949855 := bstep (se 1 (by rfl) ⟨3712391, by rfl⟩ : syracuseStep 4949855 = 7424783) B7424783
theorem B3049487 : Blo 900574 3049487 := bstep (se 1 (by rfl) ⟨2287115, by rfl⟩ : syracuseStep 3049487 = 4574231) B4574231
theorem B35719261 : Blo 900574 35719261 := bstep (se 3 (by rfl) ⟨6697361, by rfl⟩ : syracuseStep 35719261 = 13394723) B13394723
theorem B4164077 : Blo 900574 4164077 := bstep (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) B1561529
theorem B3475993 : Blo 900574 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B2034215 : Blo 900574 2034215 := bstep (se 1 (by rfl) ⟨1525661, by rfl⟩ : syracuseStep 2034215 = 3051323) B3051323
theorem B3050081 : Blo 900574 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B1542827 : Blo 900574 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B2034539 : Blo 900574 2034539 := bstep (se 1 (by rfl) ⟨1525904, by rfl⟩ : syracuseStep 2034539 = 3051809) B3051809
theorem B2034593 : Blo 900574 2034593 := bstep (se 2 (by rfl) ⟨762972, by rfl⟩ : syracuseStep 2034593 = 1525945) B1525945
theorem B6851627 : Blo 900574 6851627 := bstep (se 1 (by rfl) ⟨5138720, by rfl⟩ : syracuseStep 6851627 = 10277441) B10277441
theorem B1445035 : Blo 900574 1445035 := bstep (se 1 (by rfl) ⟨1083776, by rfl⟩ : syracuseStep 1445035 = 2167553) B2167553
theorem B2034935 : Blo 900574 2034935 := bstep (se 1 (by rfl) ⟨1526201, by rfl⟩ : syracuseStep 2034935 = 3052403) B3052403
theorem B9375011 : Blo 900574 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B3247465 : Blo 900574 3247465 := bstep (se 2 (by rfl) ⟨1217799, by rfl⟩ : syracuseStep 3247465 = 2435599) B2435599
theorem B7703981 : Blo 900574 7703981 := bstep (se 3 (by rfl) ⟨1444496, by rfl⟩ : syracuseStep 7703981 = 2888993) B2888993
theorem B5148359 : Blo 900574 5148359 := bstep (se 1 (by rfl) ⟨3861269, by rfl⟩ : syracuseStep 5148359 = 7722539) B7722539
theorem B3051539 : Blo 900574 3051539 := bstep (se 1 (by rfl) ⟨2288654, by rfl⟩ : syracuseStep 3051539 = 4577309) B4577309
theorem B14061745 : Blo 900574 14061745 := bstep (se 2 (by rfl) ⟨5273154, by rfl⟩ : syracuseStep 14061745 = 10546309) B10546309
theorem B4559165 : Blo 900574 4559165 := bstep (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) B1709687
theorem B3051863 : Blo 900574 3051863 := bstep (se 1 (by rfl) ⟨2288897, by rfl⟩ : syracuseStep 3051863 = 4577795) B4577795
theorem B2167283 : Blo 900574 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B1446407 : Blo 900574 1446407 := bstep (se 1 (by rfl) ⟨1084805, by rfl⟩ : syracuseStep 1446407 = 2169611) B2169611
theorem B1446439 : Blo 900574 1446439 := bstep (se 1 (by rfl) ⟨1084829, by rfl⟩ : syracuseStep 1446439 = 2169659) B2169659
theorem B13013621 : Blo 900574 13013621 := bstep (se 5 (by rfl) ⟨610013, by rfl⟩ : syracuseStep 13013621 = 1220027) B1220027
theorem B1086151 : Blo 900574 1086151 := bstep (se 1 (by rfl) ⟨814613, by rfl⟩ : syracuseStep 1086151 = 1629227) B1629227
theorem B3248849 : Blo 900574 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B4330415 : Blo 900574 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B2888635 : Blo 900574 2888635 := bstep (se 1 (by rfl) ⟨2166476, by rfl⟩ : syracuseStep 2888635 = 4332953) B4332953
theorem B1283035 : Blo 900574 1283035 := bstep (se 1 (by rfl) ⟨962276, by rfl⟩ : syracuseStep 1283035 = 1924553) B1924553
theorem B1218011 : Blo 900574 1218011 := bstep (se 1 (by rfl) ⟨913508, by rfl⟩ : syracuseStep 1218011 = 1827017) B1827017
theorem B3249875 : Blo 900574 3249875 := bstep (se 1 (by rfl) ⟨2437406, by rfl⟩ : syracuseStep 3249875 = 4874813) B4874813
theorem B19535651 : Blo 900574 19535651 := bstep (se 1 (by rfl) ⟨14651738, by rfl⟩ : syracuseStep 19535651 = 29303477) B29303477
theorem B6166315 : Blo 900574 6166315 := bstep (se 1 (by rfl) ⟨4624736, by rfl⟩ : syracuseStep 6166315 = 9249473) B9249473
theorem B23107841 : Blo 900574 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B1710409 : Blo 900574 1710409 := bstep (se 2 (by rfl) ⟨641403, by rfl⟩ : syracuseStep 1710409 = 1282807) B1282807
theorem B6953303 : Blo 900574 6953303 := bstep (se 1 (by rfl) ⟨5214977, by rfl⟩ : syracuseStep 6953303 = 10429955) B10429955
theorem B25041287 : Blo 900574 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B4561433 : Blo 900574 4561433 := bstep (se 2 (by rfl) ⟨1710537, by rfl⟩ : syracuseStep 4561433 = 3421075) B3421075
theorem B1285159 : Blo 900574 1285159 := bstep (se 1 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 1285159 = 1927739) B1927739
theorem B12327979 : Blo 900574 12327979 := bstep (se 1 (by rfl) ⟨9245984, by rfl⟩ : syracuseStep 12327979 = 18491969) B18491969
theorem B1350905 : Blo 900574 1350905 := bstep (se 2 (by rfl) ⟨506589, by rfl⟩ : syracuseStep 1350905 = 1013179) B1013179
theorem B1351007 : Blo 900574 1351007 := bstep (se 1 (by rfl) ⟨1013255, by rfl⟩ : syracuseStep 1351007 = 2026511) B2026511
theorem B1351019 : Blo 900574 1351019 := bstep (se 1 (by rfl) ⟨1013264, by rfl⟩ : syracuseStep 1351019 = 2026529) B2026529
theorem B6954535 : Blo 900574 6954535 := bstep (se 1 (by rfl) ⟨5215901, by rfl⟩ : syracuseStep 6954535 = 10431803) B10431803
theorem B1351247 : Blo 900574 1351247 := bstep (se 1 (by rfl) ⟨1013435, by rfl⟩ : syracuseStep 1351247 = 2026871) B2026871
theorem B1351367 : Blo 900574 1351367 := bstep (se 1 (by rfl) ⟨1013525, by rfl⟩ : syracuseStep 1351367 = 2027051) B2027051
theorem B1285831 : Blo 900574 1285831 := bstep (se 1 (by rfl) ⟨964373, by rfl⟩ : syracuseStep 1285831 = 1928747) B1928747
theorem B1351529 : Blo 900574 1351529 := bstep (se 2 (by rfl) ⟨506823, by rfl⟩ : syracuseStep 1351529 = 1013647) B1013647
theorem B1351607 : Blo 900574 1351607 := bstep (se 1 (by rfl) ⟨1013705, by rfl⟩ : syracuseStep 1351607 = 2027411) B2027411
theorem B1351643 : Blo 900574 1351643 := bstep (se 1 (by rfl) ⟨1013732, by rfl⟩ : syracuseStep 1351643 = 2027465) B2027465
theorem B27795473 : Blo 900574 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B2171051 : Blo 900574 2171051 := bstep (se 1 (by rfl) ⟨1628288, by rfl⟩ : syracuseStep 2171051 = 3256577) B3256577
theorem B1352111 : Blo 900574 1352111 := bstep (se 1 (by rfl) ⟨1014083, by rfl⟩ : syracuseStep 1352111 = 2028167) B2028167
theorem B1712603 : Blo 900574 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B1352201 : Blo 900574 1352201 := bstep (se 2 (by rfl) ⟨507075, by rfl⟩ : syracuseStep 1352201 = 1014151) B1014151
theorem B1352231 : Blo 900574 1352231 := bstep (se 1 (by rfl) ⟨1014173, by rfl⟩ : syracuseStep 1352231 = 2028347) B2028347
theorem B1352315 : Blo 900574 1352315 := bstep (se 1 (by rfl) ⟨1014236, by rfl⟩ : syracuseStep 1352315 = 2028473) B2028473
theorem B1712839 : Blo 900574 1712839 := bstep (se 1 (by rfl) ⟨1284629, by rfl⟩ : syracuseStep 1712839 = 2569259) B2569259
theorem B1352441 : Blo 900574 1352441 := bstep (se 2 (by rfl) ⟨507165, by rfl⟩ : syracuseStep 1352441 = 1014331) B1014331
theorem B1352543 : Blo 900574 1352543 := bstep (se 1 (by rfl) ⟨1014407, by rfl⟩ : syracuseStep 1352543 = 2028815) B2028815
theorem B1352555 : Blo 900574 1352555 := bstep (se 1 (by rfl) ⟨1014416, by rfl⟩ : syracuseStep 1352555 = 2028833) B2028833
theorem B3253175 : Blo 900574 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B1287095 : Blo 900574 1287095 := bstep (se 1 (by rfl) ⟨965321, by rfl⟩ : syracuseStep 1287095 = 1930643) B1930643
theorem B1156135 : Blo 900574 1156135 := bstep (se 1 (by rfl) ⟨867101, by rfl⟩ : syracuseStep 1156135 = 1734203) B1734203
theorem B1352783 : Blo 900574 1352783 := bstep (se 1 (by rfl) ⟨1014587, by rfl⟩ : syracuseStep 1352783 = 2029175) B2029175
theorem B1352903 : Blo 900574 1352903 := bstep (se 1 (by rfl) ⟨1014677, by rfl⟩ : syracuseStep 1352903 = 2029355) B2029355
theorem B1353065 : Blo 900574 1353065 := bstep (se 2 (by rfl) ⟨507399, by rfl⟩ : syracuseStep 1353065 = 1014799) B1014799
theorem B4564349 : Blo 900574 4564349 := bstep (se 3 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 4564349 = 1711631) B1711631
theorem B1353143 : Blo 900574 1353143 := bstep (se 1 (by rfl) ⟨1014857, by rfl⟩ : syracuseStep 1353143 = 2029715) B2029715
theorem B5776859 : Blo 900574 5776859 := bstep (se 1 (by rfl) ⟨4332644, by rfl⟩ : syracuseStep 5776859 = 8665289) B8665289
theorem B1353179 : Blo 900574 1353179 := bstep (se 1 (by rfl) ⟨1014884, by rfl⟩ : syracuseStep 1353179 = 2029769) B2029769
theorem B32056931 : Blo 900574 32056931 := bstep (se 1 (by rfl) ⟨24042698, by rfl⟩ : syracuseStep 32056931 = 48085397) B48085397
theorem B1353647 : Blo 900574 1353647 := bstep (se 1 (by rfl) ⟨1015235, by rfl⟩ : syracuseStep 1353647 = 2030471) B2030471
theorem B1353737 : Blo 900574 1353737 := bstep (se 2 (by rfl) ⟨507651, by rfl⟩ : syracuseStep 1353737 = 1015303) B1015303
theorem B12986405 : Blo 900574 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B1353767 : Blo 900574 1353767 := bstep (se 1 (by rfl) ⟨1015325, by rfl⟩ : syracuseStep 1353767 = 2030651) B2030651
theorem B1353851 : Blo 900574 1353851 := bstep (se 1 (by rfl) ⟨1015388, by rfl⟩ : syracuseStep 1353851 = 2030777) B2030777
theorem B1353977 : Blo 900574 1353977 := bstep (se 2 (by rfl) ⟨507741, by rfl⟩ : syracuseStep 1353977 = 1015483) B1015483
theorem B1354079 : Blo 900574 1354079 := bstep (se 1 (by rfl) ⟨1015559, by rfl⟩ : syracuseStep 1354079 = 2031119) B2031119
theorem B1354091 : Blo 900574 1354091 := bstep (se 1 (by rfl) ⟨1015568, by rfl⟩ : syracuseStep 1354091 = 2031137) B2031137
theorem B2566525 : Blo 900574 2566525 := bstep (se 3 (by rfl) ⟨481223, by rfl⟩ : syracuseStep 2566525 = 962447) B962447
theorem B1714745 : Blo 900574 1714745 := bstep (se 2 (by rfl) ⟨643029, by rfl⟩ : syracuseStep 1714745 = 1286059) B1286059
theorem B1354319 : Blo 900574 1354319 := bstep (se 1 (by rfl) ⟨1015739, by rfl⟩ : syracuseStep 1354319 = 2031479) B2031479
theorem B1354439 : Blo 900574 1354439 := bstep (se 1 (by rfl) ⟨1015829, by rfl⟩ : syracuseStep 1354439 = 2031659) B2031659
theorem B1354601 : Blo 900574 1354601 := bstep (se 2 (by rfl) ⟨507975, by rfl⟩ : syracuseStep 1354601 = 1015951) B1015951
theorem B1715087 : Blo 900574 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B1354679 : Blo 900574 1354679 := bstep (se 1 (by rfl) ⟨1016009, by rfl⟩ : syracuseStep 1354679 = 2032019) B2032019
theorem B1354715 : Blo 900574 1354715 := bstep (se 1 (by rfl) ⟨1016036, by rfl⟩ : syracuseStep 1354715 = 2032073) B2032073
theorem B5778499 : Blo 900574 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B1355183 : Blo 900574 1355183 := bstep (se 1 (by rfl) ⟨1016387, by rfl⟩ : syracuseStep 1355183 = 2032775) B2032775
theorem B1355273 : Blo 900574 1355273 := bstep (se 2 (by rfl) ⟨508227, by rfl⟩ : syracuseStep 1355273 = 1016455) B1016455
theorem B1355303 : Blo 900574 1355303 := bstep (se 1 (by rfl) ⟨1016477, by rfl⟩ : syracuseStep 1355303 = 2032955) B2032955
theorem B6860375 : Blo 900574 6860375 := bstep (se 1 (by rfl) ⟨5145281, by rfl⟩ : syracuseStep 6860375 = 10290563) B10290563
theorem B1355387 : Blo 900574 1355387 := bstep (se 1 (by rfl) ⟨1016540, by rfl⟩ : syracuseStep 1355387 = 2033081) B2033081
theorem B1355513 : Blo 900574 1355513 := bstep (se 2 (by rfl) ⟨508317, by rfl⟩ : syracuseStep 1355513 = 1016635) B1016635
theorem B1355615 : Blo 900574 1355615 := bstep (se 1 (by rfl) ⟨1016711, by rfl⟩ : syracuseStep 1355615 = 2033423) B2033423
theorem B1355627 : Blo 900574 1355627 := bstep (se 1 (by rfl) ⟨1016720, by rfl⟩ : syracuseStep 1355627 = 2033441) B2033441
theorem B2568199 : Blo 900574 2568199 := bstep (se 1 (by rfl) ⟨1926149, by rfl⟩ : syracuseStep 2568199 = 3852299) B3852299
theorem B1355855 : Blo 900574 1355855 := bstep (se 1 (by rfl) ⟨1016891, by rfl⟩ : syracuseStep 1355855 = 2033783) B2033783
theorem B8335523 : Blo 900574 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B1355975 : Blo 900574 1355975 := bstep (se 1 (by rfl) ⟨1016981, by rfl⟩ : syracuseStep 1355975 = 2033963) B2033963
theorem B3420407 : Blo 900574 3420407 := bstep (se 1 (by rfl) ⟨2565305, by rfl⟩ : syracuseStep 3420407 = 5130611) B5130611
theorem B1356137 : Blo 900574 1356137 := bstep (se 2 (by rfl) ⟨508551, by rfl⟩ : syracuseStep 1356137 = 1017103) B1017103
theorem B3912065 : Blo 900574 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B1356215 : Blo 900574 1356215 := bstep (se 1 (by rfl) ⟨1017161, by rfl⟩ : syracuseStep 1356215 = 2034323) B2034323
theorem B1520059 : Blo 900574 1520059 := bstep (se 1 (by rfl) ⟨1140044, by rfl⟩ : syracuseStep 1520059 = 2280089) B2280089
theorem B1356251 : Blo 900574 1356251 := bstep (se 1 (by rfl) ⟨1017188, by rfl⟩ : syracuseStep 1356251 = 2034377) B2034377
theorem B3256865 : Blo 900574 3256865 := bstep (se 2 (by rfl) ⟨1221324, by rfl⟩ : syracuseStep 3256865 = 2442649) B2442649
theorem B1520167 : Blo 900574 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B52081217 : Blo 900574 52081217 := bstep (se 2 (by rfl) ⟨19530456, by rfl⟩ : syracuseStep 52081217 = 39060913) B39060913
theorem B963271 : Blo 900574 963271 := bstep (se 1 (by rfl) ⟨722453, by rfl⟩ : syracuseStep 963271 = 1444907) B1444907
theorem B3846865 : Blo 900574 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B1716947 : Blo 900574 1716947 := bstep (se 1 (by rfl) ⟨1287710, by rfl⟩ : syracuseStep 1716947 = 2575421) B2575421
theorem B1520491 : Blo 900574 1520491 := bstep (se 1 (by rfl) ⟨1140368, by rfl⟩ : syracuseStep 1520491 = 2280737) B2280737
theorem B1356719 : Blo 900574 1356719 := bstep (se 1 (by rfl) ⟨1017539, by rfl⟩ : syracuseStep 1356719 = 2035079) B2035079
theorem B1717175 : Blo 900574 1717175 := bstep (se 1 (by rfl) ⟨1287881, by rfl⟩ : syracuseStep 1717175 = 2575763) B2575763
theorem B1356809 : Blo 900574 1356809 := bstep (se 2 (by rfl) ⟨508803, by rfl⟩ : syracuseStep 1356809 = 1017607) B1017607
theorem B10433555 : Blo 900574 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B1356839 : Blo 900574 1356839 := bstep (se 1 (by rfl) ⟨1017629, by rfl⟩ : syracuseStep 1356839 = 2035259) B2035259
theorem B3421379 : Blo 900574 3421379 := bstep (se 1 (by rfl) ⟨2566034, by rfl⟩ : syracuseStep 3421379 = 5132069) B5132069
theorem B5780909 : Blo 900574 5780909 := bstep (se 3 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 5780909 = 2167841) B2167841
theorem B2569715 : Blo 900574 2569715 := bstep (se 1 (by rfl) ⟨1927286, by rfl⟩ : syracuseStep 2569715 = 3854573) B3854573
theorem B3421835 : Blo 900574 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B4568723 : Blo 900574 4568723 := bstep (se 1 (by rfl) ⟨3426542, by rfl⟩ : syracuseStep 4568723 = 6853085) B6853085
theorem B2897657 : Blo 900574 2897657 := bstep (se 2 (by rfl) ⟨1086621, by rfl⟩ : syracuseStep 2897657 = 2173243) B2173243
theorem B2897707 : Blo 900574 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B3422047 : Blo 900574 3422047 := bstep (se 1 (by rfl) ⟨2566535, by rfl⟩ : syracuseStep 3422047 = 5133071) B5133071
theorem B1521551 : Blo 900574 1521551 := bstep (se 1 (by rfl) ⟨1141163, by rfl⟩ : syracuseStep 1521551 = 2282327) B2282327
theorem B1521787 : Blo 900574 1521787 := bstep (se 1 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 1521787 = 2282681) B2282681
theorem B7813529 : Blo 900574 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B3652231 : Blo 900574 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B4111133 : Blo 900574 4111133 := bstep (se 3 (by rfl) ⟨770837, by rfl⟩ : syracuseStep 4111133 = 1541675) B1541675
theorem B3423005 : Blo 900574 3423005 := bstep (se 3 (by rfl) ⟨641813, by rfl⟩ : syracuseStep 3423005 = 1283627) B1283627
theorem B3423019 : Blo 900574 3423019 := bstep (se 1 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 3423019 = 5134529) B5134529
theorem B2571115 : Blo 900574 2571115 := bstep (se 1 (by rfl) ⟨1928336, by rfl⟩ : syracuseStep 2571115 = 3856673) B3856673
theorem B1522651 : Blo 900574 1522651 := bstep (se 1 (by rfl) ⟨1141988, by rfl⟩ : syracuseStep 1522651 = 2283977) B2283977
theorem B900647 : Blo 900574 900647 := bstep (se 1 (by rfl) ⟨675485, by rfl⟩ : syracuseStep 900647 = 1350971) B1350971
theorem B900687 : Blo 900574 900687 := bstep (se 1 (by rfl) ⟨675515, by rfl⟩ : syracuseStep 900687 = 1351031) B1351031
theorem B1523279 : Blo 900574 1523279 := bstep (se 1 (by rfl) ⟨1142459, by rfl⟩ : syracuseStep 1523279 = 2284919) B2284919
theorem B900703 : Blo 900574 900703 := bstep (se 1 (by rfl) ⟨675527, by rfl⟩ : syracuseStep 900703 = 1351055) B1351055
theorem B900731 : Blo 900574 900731 := bstep (se 1 (by rfl) ⟨675548, by rfl⟩ : syracuseStep 900731 = 1351097) B1351097
theorem B900783 : Blo 900574 900783 := bstep (se 1 (by rfl) ⟨675587, by rfl⟩ : syracuseStep 900783 = 1351175) B1351175
theorem B900807 : Blo 900574 900807 := bstep (se 1 (by rfl) ⟨675605, by rfl⟩ : syracuseStep 900807 = 1351211) B1351211
theorem B900827 : Blo 900574 900827 := bstep (se 1 (by rfl) ⟨675620, by rfl⟩ : syracuseStep 900827 = 1351241) B1351241
theorem B900903 : Blo 900574 900903 := bstep (se 1 (by rfl) ⟨675677, by rfl⟩ : syracuseStep 900903 = 1351355) B1351355
theorem B900943 : Blo 900574 900943 := bstep (se 1 (by rfl) ⟨675707, by rfl⟩ : syracuseStep 900943 = 1351415) B1351415
theorem B900959 : Blo 900574 900959 := bstep (se 1 (by rfl) ⟨675719, by rfl⟩ : syracuseStep 900959 = 1351439) B1351439
theorem B6864749 : Blo 900574 6864749 := bstep (se 3 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 6864749 = 2574281) B2574281
theorem B900987 : Blo 900574 900987 := bstep (se 1 (by rfl) ⟨675740, by rfl⟩ : syracuseStep 900987 = 1351481) B1351481
theorem B901039 : Blo 900574 901039 := bstep (se 1 (by rfl) ⟨675779, by rfl⟩ : syracuseStep 901039 = 1351559) B1351559
theorem B901063 : Blo 900574 901063 := bstep (se 1 (by rfl) ⟨675797, by rfl⟩ : syracuseStep 901063 = 1351595) B1351595
theorem B901083 : Blo 900574 901083 := bstep (se 1 (by rfl) ⟨675812, by rfl⟩ : syracuseStep 901083 = 1351625) B1351625
theorem B901159 : Blo 900574 901159 := bstep (se 1 (by rfl) ⟨675869, by rfl⟩ : syracuseStep 901159 = 1351739) B1351739
theorem B901199 : Blo 900574 901199 := bstep (se 1 (by rfl) ⟨675899, by rfl⟩ : syracuseStep 901199 = 1351799) B1351799
theorem B901215 : Blo 900574 901215 := bstep (se 1 (by rfl) ⟨675911, by rfl⟩ : syracuseStep 901215 = 1351823) B1351823
theorem B901243 : Blo 900574 901243 := bstep (se 1 (by rfl) ⟨675932, by rfl⟩ : syracuseStep 901243 = 1351865) B1351865
theorem B19513507 : Blo 900574 19513507 := bstep (se 1 (by rfl) ⟨14635130, by rfl⟩ : syracuseStep 19513507 = 29270261) B29270261
theorem B901295 : Blo 900574 901295 := bstep (se 1 (by rfl) ⟨675971, by rfl⟩ : syracuseStep 901295 = 1351943) B1351943
theorem B901319 : Blo 900574 901319 := bstep (se 1 (by rfl) ⟨675989, by rfl⟩ : syracuseStep 901319 = 1351979) B1351979
theorem B1786067 : Blo 900574 1786067 := bstep (se 1 (by rfl) ⟨1339550, by rfl⟩ : syracuseStep 1786067 = 2679101) B2679101
theorem B901339 : Blo 900574 901339 := bstep (se 1 (by rfl) ⟨676004, by rfl⟩ : syracuseStep 901339 = 1352009) B1352009
theorem B901415 : Blo 900574 901415 := bstep (se 1 (by rfl) ⟨676061, by rfl⟩ : syracuseStep 901415 = 1352123) B1352123
theorem B901455 : Blo 900574 901455 := bstep (se 1 (by rfl) ⟨676091, by rfl⟩ : syracuseStep 901455 = 1352183) B1352183
theorem B901471 : Blo 900574 901471 := bstep (se 1 (by rfl) ⟨676103, by rfl⟩ : syracuseStep 901471 = 1352207) B1352207
theorem B901499 : Blo 900574 901499 := bstep (se 1 (by rfl) ⟨676124, by rfl⟩ : syracuseStep 901499 = 1352249) B1352249
theorem B901551 : Blo 900574 901551 := bstep (se 1 (by rfl) ⟨676163, by rfl⟩ : syracuseStep 901551 = 1352327) B1352327
theorem B1524143 : Blo 900574 1524143 := bstep (se 1 (by rfl) ⟨1143107, by rfl⟩ : syracuseStep 1524143 = 2286215) B2286215
theorem B901575 : Blo 900574 901575 := bstep (se 1 (by rfl) ⟨676181, by rfl⟩ : syracuseStep 901575 = 1352363) B1352363
theorem B901595 : Blo 900574 901595 := bstep (se 1 (by rfl) ⟨676196, by rfl⟩ : syracuseStep 901595 = 1352393) B1352393
theorem B901671 : Blo 900574 901671 := bstep (se 1 (by rfl) ⟨676253, by rfl⟩ : syracuseStep 901671 = 1352507) B1352507
theorem B901711 : Blo 900574 901711 := bstep (se 1 (by rfl) ⟨676283, by rfl⟩ : syracuseStep 901711 = 1352567) B1352567
theorem B901727 : Blo 900574 901727 := bstep (se 1 (by rfl) ⟨676295, by rfl⟩ : syracuseStep 901727 = 1352591) B1352591
theorem B901755 : Blo 900574 901755 := bstep (se 1 (by rfl) ⟨676316, by rfl⟩ : syracuseStep 901755 = 1352633) B1352633
theorem B901807 : Blo 900574 901807 := bstep (se 1 (by rfl) ⟨676355, by rfl⟩ : syracuseStep 901807 = 1352711) B1352711
theorem B901831 : Blo 900574 901831 := bstep (se 1 (by rfl) ⟨676373, by rfl⟩ : syracuseStep 901831 = 1352747) B1352747
theorem B901851 : Blo 900574 901851 := bstep (se 1 (by rfl) ⟨676388, by rfl⟩ : syracuseStep 901851 = 1352777) B1352777
theorem B7324445 : Blo 900574 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B901927 : Blo 900574 901927 := bstep (se 1 (by rfl) ⟨676445, by rfl⟩ : syracuseStep 901927 = 1352891) B1352891
theorem B901967 : Blo 900574 901967 := bstep (se 1 (by rfl) ⟨676475, by rfl⟩ : syracuseStep 901967 = 1352951) B1352951
theorem B901983 : Blo 900574 901983 := bstep (se 1 (by rfl) ⟨676487, by rfl⟩ : syracuseStep 901983 = 1352975) B1352975
theorem B1524575 : Blo 900574 1524575 := bstep (se 1 (by rfl) ⟨1143431, by rfl⟩ : syracuseStep 1524575 = 2286863) B2286863
theorem B902011 : Blo 900574 902011 := bstep (se 1 (by rfl) ⟨676508, by rfl⟩ : syracuseStep 902011 = 1353017) B1353017
theorem B902063 : Blo 900574 902063 := bstep (se 1 (by rfl) ⟨676547, by rfl⟩ : syracuseStep 902063 = 1353095) B1353095
theorem B902087 : Blo 900574 902087 := bstep (se 1 (by rfl) ⟨676565, by rfl⟩ : syracuseStep 902087 = 1353131) B1353131
theorem B902107 : Blo 900574 902107 := bstep (se 1 (by rfl) ⟨676580, by rfl⟩ : syracuseStep 902107 = 1353161) B1353161
theorem B902183 : Blo 900574 902183 := bstep (se 1 (by rfl) ⟨676637, by rfl⟩ : syracuseStep 902183 = 1353275) B1353275
theorem B8930371 : Blo 900574 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B902223 : Blo 900574 902223 := bstep (se 1 (by rfl) ⟨676667, by rfl⟩ : syracuseStep 902223 = 1353335) B1353335
theorem B902239 : Blo 900574 902239 := bstep (se 1 (by rfl) ⟨676679, by rfl⟩ : syracuseStep 902239 = 1353359) B1353359
theorem B902267 : Blo 900574 902267 := bstep (se 1 (by rfl) ⟨676700, by rfl⟩ : syracuseStep 902267 = 1353401) B1353401
theorem B902319 : Blo 900574 902319 := bstep (se 1 (by rfl) ⟨676739, by rfl⟩ : syracuseStep 902319 = 1353479) B1353479
theorem B902343 : Blo 900574 902343 := bstep (se 1 (by rfl) ⟨676757, by rfl⟩ : syracuseStep 902343 = 1353515) B1353515
theorem B902363 : Blo 900574 902363 := bstep (se 1 (by rfl) ⟨676772, by rfl⟩ : syracuseStep 902363 = 1353545) B1353545
theorem B902439 : Blo 900574 902439 := bstep (se 1 (by rfl) ⟨676829, by rfl⟩ : syracuseStep 902439 = 1353659) B1353659
theorem B902479 : Blo 900574 902479 := bstep (se 1 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 902479 = 1353719) B1353719
theorem B902495 : Blo 900574 902495 := bstep (se 1 (by rfl) ⟨676871, by rfl⟩ : syracuseStep 902495 = 1353743) B1353743
theorem B902523 : Blo 900574 902523 := bstep (se 1 (by rfl) ⟨676892, by rfl⟩ : syracuseStep 902523 = 1353785) B1353785
theorem B1525135 : Blo 900574 1525135 := bstep (se 1 (by rfl) ⟨1143851, by rfl⟩ : syracuseStep 1525135 = 2287703) B2287703
theorem B902575 : Blo 900574 902575 := bstep (se 1 (by rfl) ⟨676931, by rfl⟩ : syracuseStep 902575 = 1353863) B1353863
theorem B902599 : Blo 900574 902599 := bstep (se 1 (by rfl) ⟨676949, by rfl⟩ : syracuseStep 902599 = 1353899) B1353899
theorem B902619 : Blo 900574 902619 := bstep (se 1 (by rfl) ⟨676964, by rfl⟩ : syracuseStep 902619 = 1353929) B1353929
theorem B2573849 : Blo 900574 2573849 := bstep (se 2 (by rfl) ⟨965193, by rfl⟩ : syracuseStep 2573849 = 1930387) B1930387
theorem B902695 : Blo 900574 902695 := bstep (se 1 (by rfl) ⟨677021, by rfl⟩ : syracuseStep 902695 = 1354043) B1354043
theorem B902735 : Blo 900574 902735 := bstep (se 1 (by rfl) ⟨677051, by rfl⟩ : syracuseStep 902735 = 1354103) B1354103
theorem B902751 : Blo 900574 902751 := bstep (se 1 (by rfl) ⟨677063, by rfl⟩ : syracuseStep 902751 = 1354127) B1354127
theorem B902779 : Blo 900574 902779 := bstep (se 1 (by rfl) ⟨677084, by rfl⟩ : syracuseStep 902779 = 1354169) B1354169
theorem B2573963 : Blo 900574 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B902831 : Blo 900574 902831 := bstep (se 1 (by rfl) ⟨677123, by rfl⟩ : syracuseStep 902831 = 1354247) B1354247
theorem B4343485 : Blo 900574 4343485 := bstep (se 3 (by rfl) ⟨814403, by rfl⟩ : syracuseStep 4343485 = 1628807) B1628807
theorem B3851975 : Blo 900574 3851975 := bstep (se 1 (by rfl) ⟨2888981, by rfl⟩ : syracuseStep 3851975 = 5777963) B5777963
theorem B902855 : Blo 900574 902855 := bstep (se 1 (by rfl) ⟨677141, by rfl⟩ : syracuseStep 902855 = 1354283) B1354283
theorem B902875 : Blo 900574 902875 := bstep (se 1 (by rfl) ⟨677156, by rfl⟩ : syracuseStep 902875 = 1354313) B1354313
theorem B902951 : Blo 900574 902951 := bstep (se 1 (by rfl) ⟨677213, by rfl⟩ : syracuseStep 902951 = 1354427) B1354427
theorem B902991 : Blo 900574 902991 := bstep (se 1 (by rfl) ⟨677243, by rfl⟩ : syracuseStep 902991 = 1354487) B1354487
theorem B3852127 : Blo 900574 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B903007 : Blo 900574 903007 := bstep (se 1 (by rfl) ⟨677255, by rfl⟩ : syracuseStep 903007 = 1354511) B1354511
theorem B2443115 : Blo 900574 2443115 := bstep (se 1 (by rfl) ⟨1832336, by rfl⟩ : syracuseStep 2443115 = 3664673) B3664673
theorem B903035 : Blo 900574 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B3426209 : Blo 900574 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B903087 : Blo 900574 903087 := bstep (se 1 (by rfl) ⟨677315, by rfl⟩ : syracuseStep 903087 = 1354631) B1354631
theorem B903111 : Blo 900574 903111 := bstep (se 1 (by rfl) ⟨677333, by rfl⟩ : syracuseStep 903111 = 1354667) B1354667
theorem B903131 : Blo 900574 903131 := bstep (se 1 (by rfl) ⟨677348, by rfl⟩ : syracuseStep 903131 = 1354697) B1354697
theorem B903207 : Blo 900574 903207 := bstep (se 1 (by rfl) ⟨677405, by rfl⟩ : syracuseStep 903207 = 1354811) B1354811
theorem B1525817 : Blo 900574 1525817 := bstep (se 2 (by rfl) ⟨572181, by rfl⟩ : syracuseStep 1525817 = 1144363) B1144363
theorem B903247 : Blo 900574 903247 := bstep (se 1 (by rfl) ⟨677435, by rfl⟩ : syracuseStep 903247 = 1354871) B1354871
theorem B5851217 : Blo 900574 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B903263 : Blo 900574 903263 := bstep (se 1 (by rfl) ⟨677447, by rfl⟩ : syracuseStep 903263 = 1354895) B1354895
theorem B903291 : Blo 900574 903291 := bstep (se 1 (by rfl) ⟨677468, by rfl⟩ : syracuseStep 903291 = 1354937) B1354937
theorem B903343 : Blo 900574 903343 := bstep (se 1 (by rfl) ⟨677507, by rfl⟩ : syracuseStep 903343 = 1355015) B1355015
theorem B903367 : Blo 900574 903367 := bstep (se 1 (by rfl) ⟨677525, by rfl⟩ : syracuseStep 903367 = 1355051) B1355051
theorem B903387 : Blo 900574 903387 := bstep (se 1 (by rfl) ⟨677540, by rfl⟩ : syracuseStep 903387 = 1355081) B1355081
theorem B903463 : Blo 900574 903463 := bstep (se 1 (by rfl) ⟨677597, by rfl⟩ : syracuseStep 903463 = 1355195) B1355195
theorem B903503 : Blo 900574 903503 := bstep (se 1 (by rfl) ⟨677627, by rfl⟩ : syracuseStep 903503 = 1355255) B1355255
theorem B903519 : Blo 900574 903519 := bstep (se 1 (by rfl) ⟨677639, by rfl⟩ : syracuseStep 903519 = 1355279) B1355279
theorem B2279785 : Blo 900574 2279785 := bstep (se 2 (by rfl) ⟨854919, by rfl⟩ : syracuseStep 2279785 = 1709839) B1709839
theorem B903547 : Blo 900574 903547 := bstep (se 1 (by rfl) ⟨677660, by rfl⟩ : syracuseStep 903547 = 1355321) B1355321
theorem B903599 : Blo 900574 903599 := bstep (se 1 (by rfl) ⟨677699, by rfl⟩ : syracuseStep 903599 = 1355399) B1355399
theorem B903623 : Blo 900574 903623 := bstep (se 1 (by rfl) ⟨677717, by rfl⟩ : syracuseStep 903623 = 1355435) B1355435
theorem B903643 : Blo 900574 903643 := bstep (se 1 (by rfl) ⟨677732, by rfl⟩ : syracuseStep 903643 = 1355465) B1355465
theorem B903719 : Blo 900574 903719 := bstep (se 1 (by rfl) ⟨677789, by rfl⟩ : syracuseStep 903719 = 1355579) B1355579
theorem B1624655 : Blo 900574 1624655 := bstep (se 1 (by rfl) ⟨1218491, by rfl⟩ : syracuseStep 1624655 = 2436983) B2436983
theorem B903759 : Blo 900574 903759 := bstep (se 1 (by rfl) ⟨677819, by rfl⟩ : syracuseStep 903759 = 1355639) B1355639
theorem B903775 : Blo 900574 903775 := bstep (se 1 (by rfl) ⟨677831, by rfl⟩ : syracuseStep 903775 = 1355663) B1355663
theorem B2738785 : Blo 900574 2738785 := bstep (se 2 (by rfl) ⟨1027044, by rfl⟩ : syracuseStep 2738785 = 2054089) B2054089
theorem B2280059 : Blo 900574 2280059 := bstep (se 1 (by rfl) ⟨1710044, by rfl⟩ : syracuseStep 2280059 = 3420089) B3420089
theorem B903803 : Blo 900574 903803 := bstep (se 1 (by rfl) ⟨677852, by rfl⟩ : syracuseStep 903803 = 1355705) B1355705
theorem B903855 : Blo 900574 903855 := bstep (se 1 (by rfl) ⟨677891, by rfl⟩ : syracuseStep 903855 = 1355783) B1355783
theorem B5491385 : Blo 900574 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B903879 : Blo 900574 903879 := bstep (se 1 (by rfl) ⟨677909, by rfl⟩ : syracuseStep 903879 = 1355819) B1355819
theorem B6867665 : Blo 900574 6867665 := bstep (se 2 (by rfl) ⟨2575374, by rfl⟩ : syracuseStep 6867665 = 5150749) B5150749
theorem B4573907 : Blo 900574 4573907 := bstep (se 1 (by rfl) ⟨3430430, by rfl⟩ : syracuseStep 4573907 = 6860861) B6860861
theorem B903899 : Blo 900574 903899 := bstep (se 1 (by rfl) ⟨677924, by rfl⟩ : syracuseStep 903899 = 1355849) B1355849
theorem B903975 : Blo 900574 903975 := bstep (se 1 (by rfl) ⟨677981, by rfl⟩ : syracuseStep 903975 = 1355963) B1355963
theorem B904015 : Blo 900574 904015 := bstep (se 1 (by rfl) ⟨678011, by rfl⟩ : syracuseStep 904015 = 1356023) B1356023
theorem B904031 : Blo 900574 904031 := bstep (se 1 (by rfl) ⟨678023, by rfl⟩ : syracuseStep 904031 = 1356047) B1356047
theorem B3427181 : Blo 900574 3427181 := bstep (se 3 (by rfl) ⟨642596, by rfl⟩ : syracuseStep 3427181 = 1285193) B1285193
theorem B904059 : Blo 900574 904059 := bstep (se 1 (by rfl) ⟨678044, by rfl⟩ : syracuseStep 904059 = 1356089) B1356089
theorem B904111 : Blo 900574 904111 := bstep (se 1 (by rfl) ⟨678083, by rfl⟩ : syracuseStep 904111 = 1356167) B1356167
theorem B904135 : Blo 900574 904135 := bstep (se 1 (by rfl) ⟨678101, by rfl⟩ : syracuseStep 904135 = 1356203) B1356203
theorem B904155 : Blo 900574 904155 := bstep (se 1 (by rfl) ⟨678116, by rfl⟩ : syracuseStep 904155 = 1356233) B1356233
theorem B904231 : Blo 900574 904231 := bstep (se 1 (by rfl) ⟨678173, by rfl⟩ : syracuseStep 904231 = 1356347) B1356347
theorem B904271 : Blo 900574 904271 := bstep (se 1 (by rfl) ⟨678203, by rfl⟩ : syracuseStep 904271 = 1356407) B1356407
theorem B904287 : Blo 900574 904287 := bstep (se 1 (by rfl) ⟨678215, by rfl⟩ : syracuseStep 904287 = 1356431) B1356431
theorem B26070133 : Blo 900574 26070133 := bstep (se 5 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 26070133 = 2444075) B2444075
theorem B904315 : Blo 900574 904315 := bstep (se 1 (by rfl) ⟨678236, by rfl⟩ : syracuseStep 904315 = 1356473) B1356473
theorem B904367 : Blo 900574 904367 := bstep (se 1 (by rfl) ⟨678275, by rfl⟩ : syracuseStep 904367 = 1356551) B1356551
theorem B1100999 : Blo 900574 1100999 := bstep (se 1 (by rfl) ⟨825749, by rfl⟩ : syracuseStep 1100999 = 1651499) B1651499
theorem B904391 : Blo 900574 904391 := bstep (se 1 (by rfl) ⟨678293, by rfl⟩ : syracuseStep 904391 = 1356587) B1356587
theorem B904411 : Blo 900574 904411 := bstep (se 1 (by rfl) ⟨678308, by rfl⟩ : syracuseStep 904411 = 1356617) B1356617
theorem B904487 : Blo 900574 904487 := bstep (se 1 (by rfl) ⟨678365, by rfl⟩ : syracuseStep 904487 = 1356731) B1356731
theorem B904527 : Blo 900574 904527 := bstep (se 1 (by rfl) ⟨678395, by rfl⟩ : syracuseStep 904527 = 1356791) B1356791
theorem B904543 : Blo 900574 904543 := bstep (se 1 (by rfl) ⟨678407, by rfl⟩ : syracuseStep 904543 = 1356815) B1356815
theorem B904571 : Blo 900574 904571 := bstep (se 1 (by rfl) ⟨678428, by rfl⟩ : syracuseStep 904571 = 1356857) B1356857
theorem B3427865 : Blo 900574 3427865 := bstep (se 2 (by rfl) ⟨1285449, by rfl⟩ : syracuseStep 3427865 = 2570899) B2570899
theorem B3427879 : Blo 900574 3427879 := bstep (se 1 (by rfl) ⟨2570909, by rfl⟩ : syracuseStep 3427879 = 5141819) B5141819
theorem B2445049 : Blo 900574 2445049 := bstep (se 2 (by rfl) ⟨916893, by rfl⟩ : syracuseStep 2445049 = 1833787) B1833787
theorem B55529333 : Blo 900574 55529333 := bstep (se 5 (by rfl) ⟨2602937, by rfl⟩ : syracuseStep 55529333 = 5205875) B5205875
theorem B8245111 : Blo 900574 8245111 := bstep (se 1 (by rfl) ⟨6183833, by rfl⟩ : syracuseStep 8245111 = 12367667) B12367667
theorem B3657809 : Blo 900574 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B3428669 : Blo 900574 3428669 := bstep (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) B1285751
theorem B2281871 : Blo 900574 2281871 := bstep (se 1 (by rfl) ⟨1711403, by rfl⟩ : syracuseStep 2281871 = 3422807) B3422807
theorem B3428851 : Blo 900574 3428851 := bstep (se 1 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 3428851 = 5143277) B5143277
theorem B2282195 : Blo 900574 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B14635849 : Blo 900574 14635849 := bstep (se 2 (by rfl) ⟨5488443, by rfl⟩ : syracuseStep 14635849 = 10976887) B10976887
theorem B5493577 : Blo 900574 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B4576175 : Blo 900574 4576175 := bstep (se 1 (by rfl) ⟨3432131, by rfl⟩ : syracuseStep 4576175 = 6864263) B6864263
theorem B3298499 : Blo 900574 3298499 := bstep (se 1 (by rfl) ⟨2473874, by rfl⟩ : syracuseStep 3298499 = 4947749) B4947749
theorem B7329113 : Blo 900574 7329113 := bstep (se 2 (by rfl) ⟨2748417, by rfl⟩ : syracuseStep 7329113 = 5496835) B5496835
theorem B1627705 : Blo 900574 1627705 := bstep (se 2 (by rfl) ⟨610389, by rfl⟩ : syracuseStep 1627705 = 1220779) B1220779
theorem B12342881 : Blo 900574 12342881 := bstep (se 2 (by rfl) ⟨4628580, by rfl⟩ : syracuseStep 12342881 = 9257161) B9257161
theorem B3430097 : Blo 900574 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B16897901 : Blo 900574 16897901 := bstep (se 3 (by rfl) ⟨3168356, by rfl⟩ : syracuseStep 16897901 = 6336713) B6336713
theorem B10442789 : Blo 900574 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B9394481 : Blo 900574 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B1562987 : Blo 900574 1562987 := bstep (se 1 (by rfl) ⟨1172240, by rfl⟩ : syracuseStep 1562987 = 2344481) B2344481
theorem B3430781 : Blo 900574 3430781 := bstep (se 3 (by rfl) ⟨643271, by rfl⟩ : syracuseStep 3430781 = 1286543) B1286543
theorem B24697223 : Blo 900574 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B17357489 : Blo 900574 17357489 := bstep (se 2 (by rfl) ⟨6509058, by rfl⟩ : syracuseStep 17357489 = 13018117) B13018117
theorem B1465031 : Blo 900574 1465031 := bstep (se 1 (by rfl) ⟨1098773, by rfl⟩ : syracuseStep 1465031 = 2197547) B2197547
theorem B2284463 : Blo 900574 2284463 := bstep (se 1 (by rfl) ⟨1713347, by rfl⟩ : syracuseStep 2284463 = 3426695) B3426695
theorem B1956791 : Blo 900574 1956791 := bstep (se 1 (by rfl) ⟨1467593, by rfl⟩ : syracuseStep 1956791 = 2935187) B2935187
theorem B3660731 : Blo 900574 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B1825849 : Blo 900574 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B1826003 : Blo 900574 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B5496055 : Blo 900574 5496055 := bstep (se 1 (by rfl) ⟨4122041, by rfl⟩ : syracuseStep 5496055 = 8244083) B8244083
theorem B3431767 : Blo 900574 3431767 := bstep (se 1 (by rfl) ⟨2573825, by rfl⟩ : syracuseStep 3431767 = 5147651) B5147651
theorem B2285081 : Blo 900574 2285081 := bstep (se 2 (by rfl) ⟨856905, by rfl⟩ : syracuseStep 2285081 = 1713811) B1713811
theorem B3432071 : Blo 900574 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B2350943 : Blo 900574 2350943 := bstep (se 1 (by rfl) ⟨1763207, by rfl⟩ : syracuseStep 2350943 = 3526415) B3526415
theorem B1925039 : Blo 900574 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B3432527 : Blo 900574 3432527 := bstep (se 1 (by rfl) ⟨2574395, by rfl⟩ : syracuseStep 3432527 = 5148791) B5148791
theorem B2744819 : Blo 900574 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B7725577 : Blo 900574 7725577 := bstep (se 2 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 7725577 = 5794183) B5794183
theorem B2777723 : Blo 900574 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B3039929 : Blo 900574 3039929 := bstep (se 2 (by rfl) ⟨1139973, by rfl⟩ : syracuseStep 3039929 = 2279947) B2279947
theorem B3433529 : Blo 900574 3433529 := bstep (se 2 (by rfl) ⟨1287573, by rfl⟩ : syracuseStep 3433529 = 2575147) B2575147
theorem B10970315 : Blo 900574 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B3040523 : Blo 900574 3040523 := bstep (se 1 (by rfl) ⟨2280392, by rfl⟩ : syracuseStep 3040523 = 4560785) B4560785
theorem B1140151 : Blo 900574 1140151 := bstep (se 1 (by rfl) ⟨855113, by rfl⟩ : syracuseStep 1140151 = 1710227) B1710227
theorem B3040793 : Blo 900574 3040793 := bstep (se 2 (by rfl) ⟨1140297, by rfl⟩ : syracuseStep 3040793 = 2280595) B2280595
theorem B3466891 : Blo 900574 3466891 := bstep (se 1 (by rfl) ⟨2600168, by rfl⟩ : syracuseStep 3466891 = 5200337) B5200337
theorem B3434183 : Blo 900574 3434183 := bstep (se 1 (by rfl) ⟨2575637, by rfl⟩ : syracuseStep 3434183 = 5151275) B5151275
theorem B47605477 : Blo 900574 47605477 := bstep (se 4 (by rfl) ⟨4463013, by rfl⟩ : syracuseStep 47605477 = 8926027) B8926027
theorem B5793569 : Blo 900574 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B9758657 : Blo 900574 9758657 := bstep (se 2 (by rfl) ⟨3659496, by rfl⟩ : syracuseStep 9758657 = 7318993) B7318993
theorem B2287673 : Blo 900574 2287673 := bstep (se 2 (by rfl) ⟨857877, by rfl⟩ : syracuseStep 2287673 = 1715755) B1715755
theorem B7432499 : Blo 900574 7432499 := bstep (se 1 (by rfl) ⟨5574374, by rfl⟩ : syracuseStep 7432499 = 11148749) B11148749
theorem B1927567 : Blo 900574 1927567 := bstep (se 1 (by rfl) ⟨1445675, by rfl⟩ : syracuseStep 1927567 = 2891351) B2891351
theorem B3041927 : Blo 900574 3041927 := bstep (se 1 (by rfl) ⟨2281445, by rfl⟩ : syracuseStep 3041927 = 4562891) B4562891
theorem B3041981 : Blo 900574 3041981 := bstep (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) B1140743
theorem B1141447 : Blo 900574 1141447 := bstep (se 1 (by rfl) ⟨856085, by rfl⟩ : syracuseStep 1141447 = 1712171) B1712171
theorem B2026313 : Blo 900574 2026313 := bstep (se 2 (by rfl) ⟨759867, by rfl⟩ : syracuseStep 2026313 = 1519735) B1519735
theorem B3042143 : Blo 900574 3042143 := bstep (se 1 (by rfl) ⟨2281607, by rfl⟩ : syracuseStep 3042143 = 4563215) B4563215
theorem B2780087 : Blo 900574 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B6843365 : Blo 900574 6843365 := bstep (se 4 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 6843365 = 1283131) B1283131
theorem B3042305 : Blo 900574 3042305 := bstep (se 2 (by rfl) ⟨1140864, by rfl⟩ : syracuseStep 3042305 = 2281729) B2281729
theorem B3435527 : Blo 900574 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B13888685 : Blo 900574 13888685 := bstep (se 3 (by rfl) ⟨2604128, by rfl⟩ : syracuseStep 13888685 = 5208257) B5208257
theorem B1142191 : Blo 900574 1142191 := bstep (se 1 (by rfl) ⟨856643, by rfl⟩ : syracuseStep 1142191 = 1713287) B1713287
theorem B3665371 : Blo 900574 3665371 := bstep (se 1 (by rfl) ⟨2749028, by rfl⟩ : syracuseStep 3665371 = 5498057) B5498057
theorem B2289161 : Blo 900574 2289161 := bstep (se 2 (by rfl) ⟨858435, by rfl⟩ : syracuseStep 2289161 = 1716871) B1716871
theorem B2027105 : Blo 900574 2027105 := bstep (se 2 (by rfl) ⟨760164, by rfl⟩ : syracuseStep 2027105 = 1520329) B1520329
theorem B2780887 : Blo 900574 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B3043115 : Blo 900574 3043115 := bstep (se 1 (by rfl) ⟨2282336, by rfl⟩ : syracuseStep 3043115 = 4564673) B4564673
theorem B2027447 : Blo 900574 2027447 := bstep (se 1 (by rfl) ⟨1520585, by rfl⟩ : syracuseStep 2027447 = 3041171) B3041171
theorem B3043385 : Blo 900574 3043385 := bstep (se 2 (by rfl) ⟨1141269, by rfl⟩ : syracuseStep 3043385 = 2282539) B2282539
theorem B1831241 : Blo 900574 1831241 := bstep (se 2 (by rfl) ⟨686715, by rfl⟩ : syracuseStep 1831241 = 1373431) B1373431
theorem B3043709 : Blo 900574 3043709 := bstep (se 3 (by rfl) ⟨570695, by rfl⟩ : syracuseStep 3043709 = 1141391) B1141391
theorem B2028041 : Blo 900574 2028041 := bstep (se 2 (by rfl) ⟨760515, by rfl⟩ : syracuseStep 2028041 = 1521031) B1521031
theorem B1143335 : Blo 900574 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B3666491 : Blo 900574 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B3043979 : Blo 900574 3043979 := bstep (se 1 (by rfl) ⟨2282984, by rfl⟩ : syracuseStep 3043979 = 4565969) B4565969
theorem B6517421 : Blo 900574 6517421 := bstep (se 3 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 6517421 = 2444033) B2444033
theorem B1929977 : Blo 900574 1929977 := bstep (se 2 (by rfl) ⟨723741, by rfl⟩ : syracuseStep 1929977 = 1447483) B1447483
theorem B2028383 : Blo 900574 2028383 := bstep (se 1 (by rfl) ⟨1521287, by rfl⟩ : syracuseStep 2028383 = 3042575) B3042575
theorem B1143659 : Blo 900574 1143659 := bstep (se 1 (by rfl) ⟨857744, by rfl⟩ : syracuseStep 1143659 = 1715489) B1715489
theorem B2028563 : Blo 900574 2028563 := bstep (se 1 (by rfl) ⟨1521422, by rfl⟩ : syracuseStep 2028563 = 3042845) B3042845
theorem B914527 : Blo 900574 914527 := bstep (se 1 (by rfl) ⟨685895, by rfl⟩ : syracuseStep 914527 = 1371791) B1371791
theorem B3667139 : Blo 900574 3667139 := bstep (se 1 (by rfl) ⟨2750354, by rfl⟩ : syracuseStep 3667139 = 5500709) B5500709
theorem B2028905 : Blo 900574 2028905 := bstep (se 2 (by rfl) ⟨760839, by rfl⟩ : syracuseStep 2028905 = 1521679) B1521679
theorem B29324753 : Blo 900574 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B3044897 : Blo 900574 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B1013287 : Blo 900574 1013287 := bstep (se 1 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 1013287 = 1519931) B1519931
theorem B2061863 : Blo 900574 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B14612167 : Blo 900574 14612167 := bstep (se 1 (by rfl) ⟨10959125, by rfl⟩ : syracuseStep 14612167 = 21918251) B21918251
theorem B3045113 : Blo 900574 3045113 := bstep (se 2 (by rfl) ⟨1141917, by rfl⟩ : syracuseStep 3045113 = 2283835) B2283835
theorem B2750315 : Blo 900574 2750315 := bstep (se 1 (by rfl) ⟨2062736, by rfl⟩ : syracuseStep 2750315 = 4125473) B4125473
theorem B6518663 : Blo 900574 6518663 := bstep (se 1 (by rfl) ⟨4888997, by rfl⟩ : syracuseStep 6518663 = 9777995) B9777995
theorem B2029499 : Blo 900574 2029499 := bstep (se 1 (by rfl) ⟨1522124, by rfl⟩ : syracuseStep 2029499 = 3044249) B3044249
theorem B3045383 : Blo 900574 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B2029625 : Blo 900574 2029625 := bstep (se 2 (by rfl) ⟨761109, by rfl⟩ : syracuseStep 2029625 = 1522219) B1522219
theorem B3045491 : Blo 900574 3045491 := bstep (se 1 (by rfl) ⟨2284118, by rfl⟩ : syracuseStep 3045491 = 4568237) B4568237
theorem B3045761 : Blo 900574 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B2029967 : Blo 900574 2029967 := bstep (se 1 (by rfl) ⟨1522475, by rfl⟩ : syracuseStep 2029967 = 3044951) B3044951
theorem B3471817 : Blo 900574 3471817 := bstep (se 2 (by rfl) ⟨1301931, by rfl⟩ : syracuseStep 3471817 = 2603863) B2603863
theorem B1833529 : Blo 900574 1833529 := bstep (se 2 (by rfl) ⟨687573, by rfl⟩ : syracuseStep 1833529 = 1375147) B1375147
theorem B2030291 : Blo 900574 2030291 := bstep (se 1 (by rfl) ⟨1522718, by rfl⟩ : syracuseStep 2030291 = 3045437) B3045437
theorem B1014907 : Blo 900574 1014907 := bstep (se 1 (by rfl) ⟨761180, by rfl⟩ : syracuseStep 1014907 = 1522361) B1522361
theorem B3046571 : Blo 900574 3046571 := bstep (se 1 (by rfl) ⟨2284928, by rfl⟩ : syracuseStep 3046571 = 4569857) B4569857
theorem B1015375 : Blo 900574 1015375 := bstep (se 1 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 1015375 = 1523063) B1523063
theorem B2031227 : Blo 900574 2031227 := bstep (se 1 (by rfl) ⟨1523420, by rfl⟩ : syracuseStep 2031227 = 3046841) B3046841
theorem B3047111 : Blo 900574 3047111 := bstep (se 1 (by rfl) ⟨2285333, by rfl⟩ : syracuseStep 3047111 = 4570667) B4570667
theorem B2031353 : Blo 900574 2031353 := bstep (se 2 (by rfl) ⟨761757, by rfl⟩ : syracuseStep 2031353 = 1523515) B1523515
theorem B7700291 : Blo 900574 7700291 := bstep (se 1 (by rfl) ⟨5775218, by rfl⟩ : syracuseStep 7700291 = 11550437) B11550437
theorem B1015771 : Blo 900574 1015771 := bstep (se 1 (by rfl) ⟨761828, by rfl⟩ : syracuseStep 1015771 = 1523657) B1523657
theorem B26018009 : Blo 900574 26018009 := bstep (se 2 (by rfl) ⟨9756753, by rfl⟩ : syracuseStep 26018009 = 19513507) B19513507
theorem B1016095 : Blo 900574 1016095 := bstep (se 1 (by rfl) ⟨762071, by rfl⟩ : syracuseStep 1016095 = 1524143) B1524143
theorem B2031983 : Blo 900574 2031983 := bstep (se 1 (by rfl) ⟨1523987, by rfl⟩ : syracuseStep 2031983 = 3047975) B3047975
theorem B2032055 : Blo 900574 2032055 := bstep (se 1 (by rfl) ⟨1524041, by rfl⟩ : syracuseStep 2032055 = 3048083) B3048083
theorem B4882963 : Blo 900574 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B1016383 : Blo 900574 1016383 := bstep (se 1 (by rfl) ⟨762287, by rfl⟩ : syracuseStep 1016383 = 1524575) B1524575
theorem B2032199 : Blo 900574 2032199 := bstep (se 1 (by rfl) ⟨1524149, by rfl⟩ : syracuseStep 2032199 = 3048299) B3048299
theorem B2032235 : Blo 900574 2032235 := bstep (se 1 (by rfl) ⟨1524176, by rfl⟩ : syracuseStep 2032235 = 3048353) B3048353
theorem B2032631 : Blo 900574 2032631 := bstep (se 1 (by rfl) ⟨1524473, by rfl⟩ : syracuseStep 2032631 = 3048947) B3048947
theorem B2032991 : Blo 900574 2032991 := bstep (se 1 (by rfl) ⟨1524743, by rfl⟩ : syracuseStep 2032991 = 3049487) B3049487
theorem B1017211 : Blo 900574 1017211 := bstep (se 1 (by rfl) ⟨762908, by rfl⟩ : syracuseStep 1017211 = 1525817) B1525817
theorem B1541513 : Blo 900574 1541513 := bstep (se 2 (by rfl) ⟨578067, by rfl⟩ : syracuseStep 1541513 = 1156135) B1156135
theorem B3900811 : Blo 900574 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B3048893 : Blo 900574 3048893 := bstep (se 3 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 3048893 = 1143335) B1143335
theorem B2033387 : Blo 900574 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B1443625 : Blo 900574 1443625 := bstep (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) B1082719
theorem B3049271 : Blo 900574 3049271 := bstep (se 1 (by rfl) ⟨2286953, by rfl⟩ : syracuseStep 3049271 = 4573907) B4573907
theorem B2033513 : Blo 900574 2033513 := bstep (se 2 (by rfl) ⟨762567, by rfl⟩ : syracuseStep 2033513 = 1525135) B1525135
theorem B4622521 : Blo 900574 4622521 := bstep (se 2 (by rfl) ⟨1733445, by rfl⟩ : syracuseStep 4622521 = 3466891) B3466891
theorem B3049757 : Blo 900574 3049757 := bstep (se 3 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 3049757 = 1143659) B1143659
theorem B63473969 : Blo 900574 63473969 := bstep (se 2 (by rfl) ⟨23802738, by rfl⟩ : syracuseStep 63473969 = 47605477) B47605477
theorem B2034359 : Blo 900574 2034359 := bstep (se 1 (by rfl) ⟨1525769, by rfl⟩ : syracuseStep 2034359 = 3051539) B3051539
theorem B2034575 : Blo 900574 2034575 := bstep (se 1 (by rfl) ⟨1525931, by rfl⟩ : syracuseStep 2034575 = 3051863) B3051863
theorem B2886943 : Blo 900574 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B3050783 : Blo 900574 3050783 := bstep (se 1 (by rfl) ⟨2288087, by rfl⟩ : syracuseStep 3050783 = 4576175) B4576175
theorem B2198999 : Blo 900574 2198999 := bstep (se 1 (by rfl) ⟨1649249, by rfl⟩ : syracuseStep 2198999 = 3298499) B3298499
theorem B4886075 : Blo 900574 4886075 := bstep (se 1 (by rfl) ⟨3664556, by rfl⟩ : syracuseStep 4886075 = 7329113) B7329113
theorem B8228587 : Blo 900574 8228587 := bstep (se 1 (by rfl) ⟨6171440, by rfl⟩ : syracuseStep 8228587 = 12342881) B12342881
theorem B2166583 : Blo 900574 2166583 := bstep (se 1 (by rfl) ⟨1624937, by rfl⟩ : syracuseStep 2166583 = 3249875) B3249875
theorem B3248029 : Blo 900574 3248029 := bstep (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) B1218011
theorem B7704665 : Blo 900574 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B15405227 : Blo 900574 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B11571659 : Blo 900574 11571659 := bstep (se 1 (by rfl) ⟨8678744, by rfl⟩ : syracuseStep 11571659 = 17357489) B17357489
theorem B4329953 : Blo 900574 4329953 := bstep (se 2 (by rfl) ⟨1623732, by rfl⟩ : syracuseStep 4329953 = 3247465) B3247465
theorem B4887161 : Blo 900574 4887161 := bstep (se 2 (by rfl) ⟨1832685, by rfl⟩ : syracuseStep 4887161 = 3665371) B3665371
theorem B3707849 : Blo 900574 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B45061069 : Blo 900574 45061069 := bstep (se 3 (by rfl) ⟨8448950, by rfl⟩ : syracuseStep 45061069 = 16897901) B16897901
theorem B1283359 : Blo 900574 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B1447367 : Blo 900574 1447367 := bstep (se 1 (by rfl) ⟨1085525, by rfl⟩ : syracuseStep 1447367 = 2171051) B2171051
theorem B18748993 : Blo 900574 18748993 := bstep (se 2 (by rfl) ⟨7030872, by rfl⟩ : syracuseStep 18748993 = 14061745) B14061745
theorem B2168783 : Blo 900574 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B7313543 : Blo 900574 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B1448201 : Blo 900574 1448201 := bstep (se 2 (by rfl) ⟨543075, by rfl⟩ : syracuseStep 1448201 = 1086151) B1086151
theorem B1710713 : Blo 900574 1710713 := bstep (se 2 (by rfl) ⟨641517, by rfl⟩ : syracuseStep 1710713 = 1283035) B1283035
theorem B8657603 : Blo 900574 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B1219369 : Blo 900574 1219369 := bstep (se 2 (by rfl) ⟨457263, by rfl⟩ : syracuseStep 1219369 = 914527) B914527
theorem B4332413 : Blo 900574 4332413 := bstep (se 3 (by rfl) ⟨812327, by rfl⟩ : syracuseStep 4332413 = 1624655) B1624655
theorem B3906749 : Blo 900574 3906749 := bstep (se 3 (by rfl) ⟨732515, by rfl⟩ : syracuseStep 3906749 = 1465031) B1465031
theorem B1350875 : Blo 900574 1350875 := bstep (se 1 (by rfl) ⟨1013156, by rfl⟩ : syracuseStep 1350875 = 2026313) B2026313
theorem B4562243 : Blo 900574 4562243 := bstep (se 1 (by rfl) ⟨3421682, by rfl⟩ : syracuseStep 4562243 = 6843365) B6843365
theorem B1351049 : Blo 900574 1351049 := bstep (se 2 (by rfl) ⟨506643, by rfl⟩ : syracuseStep 1351049 = 1013287) B1013287
theorem B1351403 : Blo 900574 1351403 := bstep (se 1 (by rfl) ⟨1013552, by rfl⟩ : syracuseStep 1351403 = 2027105) B2027105
theorem B4562729 : Blo 900574 4562729 := bstep (se 2 (by rfl) ⟨1711023, by rfl⟩ : syracuseStep 4562729 = 3422047) B3422047
theorem B7413565 : Blo 900574 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B1351631 : Blo 900574 1351631 := bstep (se 1 (by rfl) ⟨1013723, by rfl⟩ : syracuseStep 1351631 = 2027447) B2027447
theorem B1220827 : Blo 900574 1220827 := bstep (se 1 (by rfl) ⟨915620, by rfl⟩ : syracuseStep 1220827 = 1831241) B1831241
theorem B1352027 : Blo 900574 1352027 := bstep (se 1 (by rfl) ⟨1014020, by rfl⟩ : syracuseStep 1352027 = 2028041) B2028041
theorem B2171243 : Blo 900574 2171243 := bstep (se 1 (by rfl) ⟨1628432, by rfl⟩ : syracuseStep 2171243 = 3256865) B3256865
theorem B1286651 : Blo 900574 1286651 := bstep (se 1 (by rfl) ⟨964988, by rfl⟩ : syracuseStep 1286651 = 1929977) B1929977
theorem B1352255 : Blo 900574 1352255 := bstep (se 1 (by rfl) ⟨1014191, by rfl⟩ : syracuseStep 1352255 = 2028383) B2028383
theorem B4629089 : Blo 900574 4629089 := bstep (se 2 (by rfl) ⟨1735908, by rfl⟩ : syracuseStep 4629089 = 3471817) B3471817
theorem B1352375 : Blo 900574 1352375 := bstep (se 1 (by rfl) ⟨1014281, by rfl⟩ : syracuseStep 1352375 = 2028563) B2028563
theorem B6955703 : Blo 900574 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B1352603 : Blo 900574 1352603 := bstep (se 1 (by rfl) ⟨1014452, by rfl⟩ : syracuseStep 1352603 = 2028905) B2028905
theorem B1713143 : Blo 900574 1713143 := bstep (se 1 (by rfl) ⟨1284857, by rfl⟩ : syracuseStep 1713143 = 2569715) B2569715
theorem B4564025 : Blo 900574 4564025 := bstep (se 2 (by rfl) ⟨1711509, by rfl⟩ : syracuseStep 4564025 = 3423019) B3423019
theorem B1352999 : Blo 900574 1352999 := bstep (se 1 (by rfl) ⟨1014749, by rfl⟩ : syracuseStep 1352999 = 2029499) B2029499
theorem B1353083 : Blo 900574 1353083 := bstep (se 1 (by rfl) ⟨1014812, by rfl⟩ : syracuseStep 1353083 = 2029625) B2029625
theorem B1713545 : Blo 900574 1713545 := bstep (se 2 (by rfl) ⟨642579, by rfl⟩ : syracuseStep 1713545 = 1285159) B1285159
theorem B2434465 : Blo 900574 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B1353209 : Blo 900574 1353209 := bstep (se 2 (by rfl) ⟨507453, by rfl⟩ : syracuseStep 1353209 = 1014907) B1014907
theorem B1353311 : Blo 900574 1353311 := bstep (se 1 (by rfl) ⟨1014983, by rfl⟩ : syracuseStep 1353311 = 2029967) B2029967
theorem B1353527 : Blo 900574 1353527 := bstep (se 1 (by rfl) ⟨1015145, by rfl⟩ : syracuseStep 1353527 = 2030291) B2030291
theorem B1353833 : Blo 900574 1353833 := bstep (se 2 (by rfl) ⟨507687, by rfl⟩ : syracuseStep 1353833 = 1015375) B1015375
theorem B1714441 : Blo 900574 1714441 := bstep (se 2 (by rfl) ⟨642915, by rfl⟩ : syracuseStep 1714441 = 1285831) B1285831
theorem B1354151 : Blo 900574 1354151 := bstep (se 1 (by rfl) ⟨1015613, by rfl⟩ : syracuseStep 1354151 = 2031227) B2031227
theorem B1354235 : Blo 900574 1354235 := bstep (se 1 (by rfl) ⟨1015676, by rfl⟩ : syracuseStep 1354235 = 2031353) B2031353
theorem B1354361 : Blo 900574 1354361 := bstep (se 2 (by rfl) ⟨507885, by rfl⟩ : syracuseStep 1354361 = 1015771) B1015771
theorem B1354415 : Blo 900574 1354415 := bstep (se 1 (by rfl) ⟨1015811, by rfl⟩ : syracuseStep 1354415 = 2031623) B2031623
theorem B1354463 : Blo 900574 1354463 := bstep (se 1 (by rfl) ⟨1015847, by rfl⟩ : syracuseStep 1354463 = 2031695) B2031695
theorem B1190711 : Blo 900574 1190711 := bstep (se 1 (by rfl) ⟨893033, by rfl⟩ : syracuseStep 1190711 = 1786067) B1786067
theorem B1354727 : Blo 900574 1354727 := bstep (se 1 (by rfl) ⟨1016045, by rfl⟩ : syracuseStep 1354727 = 2032091) B2032091
theorem B4566131 : Blo 900574 4566131 := bstep (se 1 (by rfl) ⟨3424598, by rfl⟩ : syracuseStep 4566131 = 6849197) B6849197
theorem B1354985 : Blo 900574 1354985 := bstep (se 2 (by rfl) ⟨508119, by rfl⟩ : syracuseStep 1354985 = 1016239) B1016239
theorem B1355039 : Blo 900574 1355039 := bstep (se 1 (by rfl) ⟨1016279, by rfl⟩ : syracuseStep 1355039 = 2032559) B2032559
theorem B10300769 : Blo 900574 10300769 := bstep (se 2 (by rfl) ⟨3862788, by rfl⟩ : syracuseStep 10300769 = 7725577) B7725577
theorem B1355207 : Blo 900574 1355207 := bstep (se 1 (by rfl) ⟨1016405, by rfl⟩ : syracuseStep 1355207 = 2032811) B2032811
theorem B1715899 : Blo 900574 1715899 := bstep (se 1 (by rfl) ⟨1286924, by rfl⟩ : syracuseStep 1715899 = 2573849) B2573849
theorem B7712455 : Blo 900574 7712455 := bstep (se 1 (by rfl) ⟨5784341, by rfl⟩ : syracuseStep 7712455 = 11568683) B11568683
theorem B7319251 : Blo 900574 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B1715975 : Blo 900574 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B1355561 : Blo 900574 1355561 := bstep (se 2 (by rfl) ⟨508335, by rfl⟩ : syracuseStep 1355561 = 1016671) B1016671
theorem B2567983 : Blo 900574 2567983 := bstep (se 1 (by rfl) ⟨1925987, by rfl⟩ : syracuseStep 2567983 = 3851975) B3851975
theorem B1355567 : Blo 900574 1355567 := bstep (se 1 (by rfl) ⟨1016675, by rfl⟩ : syracuseStep 1355567 = 2033351) B2033351
theorem B4566941 : Blo 900574 4566941 := bstep (se 3 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 4566941 = 1712603) B1712603
theorem B11579345 : Blo 900574 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B5779421 : Blo 900574 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B11907161 : Blo 900574 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B1356041 : Blo 900574 1356041 := bstep (se 2 (by rfl) ⟨508515, by rfl⟩ : syracuseStep 1356041 = 1017031) B1017031
theorem B1356143 : Blo 900574 1356143 := bstep (se 1 (by rfl) ⟨1017107, by rfl⟩ : syracuseStep 1356143 = 2034215) B2034215
theorem B1520039 : Blo 900574 1520039 := bstep (se 1 (by rfl) ⟨1140029, by rfl⟩ : syracuseStep 1520039 = 2280059) B2280059
theorem B1028551 : Blo 900574 1028551 := bstep (se 1 (by rfl) ⟨771413, by rfl⟩ : syracuseStep 1028551 = 1542827) B1542827
theorem B8663597 : Blo 900574 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B1356359 : Blo 900574 1356359 := bstep (se 1 (by rfl) ⟨1017269, by rfl⟩ : syracuseStep 1356359 = 2034539) B2034539
theorem B1520201 : Blo 900574 1520201 := bstep (se 2 (by rfl) ⟨570075, by rfl⟩ : syracuseStep 1520201 = 1140151) B1140151
theorem B1356395 : Blo 900574 1356395 := bstep (se 1 (by rfl) ⟨1017296, by rfl⟩ : syracuseStep 1356395 = 2034593) B2034593
theorem B4567751 : Blo 900574 4567751 := bstep (se 1 (by rfl) ⟨3425813, by rfl⟩ : syracuseStep 4567751 = 6851627) B6851627
theorem B1356623 : Blo 900574 1356623 := bstep (se 1 (by rfl) ⟨1017467, by rfl⟩ : syracuseStep 1356623 = 2034935) B2034935
theorem B1521247 : Blo 900574 1521247 := bstep (se 1 (by rfl) ⟨1140935, by rfl⟩ : syracuseStep 1521247 = 2281871) B2281871
theorem B964271 : Blo 900574 964271 := bstep (se 1 (by rfl) ⟨723203, by rfl⟩ : syracuseStep 964271 = 1446407) B1446407
theorem B1521463 : Blo 900574 1521463 := bstep (se 1 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 1521463 = 2282195) B2282195
theorem B3422033 : Blo 900574 3422033 := bstep (se 2 (by rfl) ⟨1283262, by rfl⟩ : syracuseStep 3422033 = 2566525) B2566525
theorem B4634657 : Blo 900574 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B3651713 : Blo 900574 3651713 := bstep (se 2 (by rfl) ⟨1369392, by rfl⟩ : syracuseStep 3651713 = 2738785) B2738785
theorem B1521929 : Blo 900574 1521929 := bstep (se 2 (by rfl) ⟨570723, by rfl⟩ : syracuseStep 1521929 = 1141447) B1141447
theorem B3848573 : Blo 900574 3848573 := bstep (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) B1443215
theorem B13023767 : Blo 900574 13023767 := bstep (se 1 (by rfl) ⟨9767825, by rfl⟩ : syracuseStep 13023767 = 19535651) B19535651
theorem B6961859 : Blo 900574 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B4635535 : Blo 900574 4635535 := bstep (se 1 (by rfl) ⟨3476651, by rfl⟩ : syracuseStep 4635535 = 6953303) B6953303
theorem B16464815 : Blo 900574 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B16694191 : Blo 900574 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B1522921 : Blo 900574 1522921 := bstep (se 2 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 1522921 = 1142191) B1142191
theorem B1522975 : Blo 900574 1522975 := bstep (se 1 (by rfl) ⟨1142231, by rfl⟩ : syracuseStep 1522975 = 2284463) B2284463
theorem B2440487 : Blo 900574 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B4570505 : Blo 900574 4570505 := bstep (se 2 (by rfl) ⟨1713939, by rfl⟩ : syracuseStep 4570505 = 3427879) B3427879
theorem B900603 : Blo 900574 900603 := bstep (se 1 (by rfl) ⟨675452, by rfl⟩ : syracuseStep 900603 = 1350905) B1350905
theorem B900671 : Blo 900574 900671 := bstep (se 1 (by rfl) ⟨675503, by rfl⟩ : syracuseStep 900671 = 1351007) B1351007
theorem B900679 : Blo 900574 900679 := bstep (se 1 (by rfl) ⟨675509, by rfl⟩ : syracuseStep 900679 = 1351019) B1351019
theorem B1523387 : Blo 900574 1523387 := bstep (se 1 (by rfl) ⟨1142540, by rfl⟩ : syracuseStep 1523387 = 2285081) B2285081
theorem B900831 : Blo 900574 900831 := bstep (se 1 (by rfl) ⟨675623, by rfl⟩ : syracuseStep 900831 = 1351247) B1351247
theorem B900911 : Blo 900574 900911 := bstep (se 1 (by rfl) ⟨675683, by rfl⟩ : syracuseStep 900911 = 1351367) B1351367
theorem B10993481 : Blo 900574 10993481 := bstep (se 2 (by rfl) ⟨4122555, by rfl⟩ : syracuseStep 10993481 = 8245111) B8245111
theorem B901019 : Blo 900574 901019 := bstep (se 1 (by rfl) ⟨675764, by rfl⟩ : syracuseStep 901019 = 1351529) B1351529
theorem B901071 : Blo 900574 901071 := bstep (se 1 (by rfl) ⟨675803, by rfl⟩ : syracuseStep 901071 = 1351607) B1351607
theorem B901095 : Blo 900574 901095 := bstep (se 1 (by rfl) ⟨675821, by rfl⟩ : syracuseStep 901095 = 1351643) B1351643
theorem B3424265 : Blo 900574 3424265 := bstep (se 2 (by rfl) ⟨1284099, by rfl⟩ : syracuseStep 3424265 = 2568199) B2568199
theorem B18530315 : Blo 900574 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B901407 : Blo 900574 901407 := bstep (se 1 (by rfl) ⟨676055, by rfl⟩ : syracuseStep 901407 = 1352111) B1352111
theorem B901467 : Blo 900574 901467 := bstep (se 1 (by rfl) ⟨676100, by rfl⟩ : syracuseStep 901467 = 1352201) B1352201
theorem B901487 : Blo 900574 901487 := bstep (se 1 (by rfl) ⟨676115, by rfl⟩ : syracuseStep 901487 = 1352231) B1352231
theorem B1851815 : Blo 900574 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B901543 : Blo 900574 901543 := bstep (se 1 (by rfl) ⟨676157, by rfl⟩ : syracuseStep 901543 = 1352315) B1352315
theorem B901627 : Blo 900574 901627 := bstep (se 1 (by rfl) ⟨676220, by rfl⟩ : syracuseStep 901627 = 1352441) B1352441
theorem B901695 : Blo 900574 901695 := bstep (se 1 (by rfl) ⟨676271, by rfl⟩ : syracuseStep 901695 = 1352543) B1352543
theorem B901703 : Blo 900574 901703 := bstep (se 1 (by rfl) ⟨676277, by rfl⟩ : syracuseStep 901703 = 1352555) B1352555
theorem B4571801 : Blo 900574 4571801 := bstep (se 2 (by rfl) ⟨1714425, by rfl⟩ : syracuseStep 4571801 = 3428851) B3428851
theorem B901855 : Blo 900574 901855 := bstep (se 1 (by rfl) ⟨676391, by rfl⟩ : syracuseStep 901855 = 1352783) B1352783
theorem B25051949 : Blo 900574 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B901935 : Blo 900574 901935 := bstep (se 1 (by rfl) ⟨676451, by rfl⟩ : syracuseStep 901935 = 1352903) B1352903
theorem B902043 : Blo 900574 902043 := bstep (se 1 (by rfl) ⟨676532, by rfl⟩ : syracuseStep 902043 = 1353065) B1353065
theorem B5129153 : Blo 900574 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B902095 : Blo 900574 902095 := bstep (se 1 (by rfl) ⟨676571, by rfl⟩ : syracuseStep 902095 = 1353143) B1353143
theorem B3851239 : Blo 900574 3851239 := bstep (se 1 (by rfl) ⟨2888429, by rfl⟩ : syracuseStep 3851239 = 5776859) B5776859
theorem B902119 : Blo 900574 902119 := bstep (se 1 (by rfl) ⟨676589, by rfl⟩ : syracuseStep 902119 = 1353179) B1353179
theorem B19514465 : Blo 900574 19514465 := bstep (se 2 (by rfl) ⟨7317924, by rfl⟩ : syracuseStep 19514465 = 14635849) B14635849
theorem B7324769 : Blo 900574 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B3851513 : Blo 900574 3851513 := bstep (se 2 (by rfl) ⟨1444317, by rfl⟩ : syracuseStep 3851513 = 2888635) B2888635
theorem B902431 : Blo 900574 902431 := bstep (se 1 (by rfl) ⟨676823, by rfl⟩ : syracuseStep 902431 = 1353647) B1353647
theorem B29312293 : Blo 900574 29312293 := bstep (se 4 (by rfl) ⟨2748027, by rfl⟩ : syracuseStep 29312293 = 5496055) B5496055
theorem B6505771 : Blo 900574 6505771 := bstep (se 1 (by rfl) ⟨4879328, by rfl⟩ : syracuseStep 6505771 = 9758657) B9758657
theorem B902491 : Blo 900574 902491 := bstep (se 1 (by rfl) ⟨676868, by rfl⟩ : syracuseStep 902491 = 1353737) B1353737
theorem B902511 : Blo 900574 902511 := bstep (se 1 (by rfl) ⟨676883, by rfl⟩ : syracuseStep 902511 = 1353767) B1353767
theorem B1525115 : Blo 900574 1525115 := bstep (se 1 (by rfl) ⟨1143836, by rfl⟩ : syracuseStep 1525115 = 2287673) B2287673
theorem B902567 : Blo 900574 902567 := bstep (se 1 (by rfl) ⟨676925, by rfl⟩ : syracuseStep 902567 = 1353851) B1353851
theorem B902651 : Blo 900574 902651 := bstep (se 1 (by rfl) ⟨676988, by rfl⟩ : syracuseStep 902651 = 1353977) B1353977
theorem B902719 : Blo 900574 902719 := bstep (se 1 (by rfl) ⟨677039, by rfl⟩ : syracuseStep 902719 = 1354079) B1354079
theorem B902727 : Blo 900574 902727 := bstep (se 1 (by rfl) ⟨677045, by rfl⟩ : syracuseStep 902727 = 1354091) B1354091
theorem B902879 : Blo 900574 902879 := bstep (se 1 (by rfl) ⟨677159, by rfl⟩ : syracuseStep 902879 = 1354319) B1354319
theorem B902959 : Blo 900574 902959 := bstep (se 1 (by rfl) ⟨677219, by rfl⟩ : syracuseStep 902959 = 1354439) B1354439
theorem B903067 : Blo 900574 903067 := bstep (se 1 (by rfl) ⟨677300, by rfl⟩ : syracuseStep 903067 = 1354601) B1354601
theorem B903119 : Blo 900574 903119 := bstep (se 1 (by rfl) ⟨677339, by rfl⟩ : syracuseStep 903119 = 1354679) B1354679
theorem B903143 : Blo 900574 903143 := bstep (se 1 (by rfl) ⟨677357, by rfl⟩ : syracuseStep 903143 = 1354715) B1354715
theorem B10963021 : Blo 900574 10963021 := bstep (se 3 (by rfl) ⟨2055566, by rfl⟩ : syracuseStep 10963021 = 4111133) B4111133
theorem B9259123 : Blo 900574 9259123 := bstep (se 1 (by rfl) ⟨6944342, by rfl⟩ : syracuseStep 9259123 = 13888685) B13888685
theorem B19482889 : Blo 900574 19482889 := bstep (se 2 (by rfl) ⟨7306083, by rfl⟩ : syracuseStep 19482889 = 14612167) B14612167
theorem B903455 : Blo 900574 903455 := bstep (se 1 (by rfl) ⟨677591, by rfl⟩ : syracuseStep 903455 = 1355183) B1355183
theorem B903515 : Blo 900574 903515 := bstep (se 1 (by rfl) ⟨677636, by rfl⟩ : syracuseStep 903515 = 1355273) B1355273
theorem B1526107 : Blo 900574 1526107 := bstep (se 1 (by rfl) ⟨1144580, by rfl⟩ : syracuseStep 1526107 = 2289161) B2289161
theorem B903535 : Blo 900574 903535 := bstep (se 1 (by rfl) ⟨677651, by rfl⟩ : syracuseStep 903535 = 1355303) B1355303
theorem B4573583 : Blo 900574 4573583 := bstep (se 1 (by rfl) ⟨3430187, by rfl⟩ : syracuseStep 4573583 = 6860375) B6860375
theorem B903591 : Blo 900574 903591 := bstep (se 1 (by rfl) ⟨677693, by rfl⟩ : syracuseStep 903591 = 1355387) B1355387
theorem B903675 : Blo 900574 903675 := bstep (se 1 (by rfl) ⟨677756, by rfl⟩ : syracuseStep 903675 = 1355513) B1355513
theorem B903743 : Blo 900574 903743 := bstep (se 1 (by rfl) ⟨677807, by rfl⟩ : syracuseStep 903743 = 1355615) B1355615
theorem B903751 : Blo 900574 903751 := bstep (se 1 (by rfl) ⟨677813, by rfl⟩ : syracuseStep 903751 = 1355627) B1355627
theorem B903903 : Blo 900574 903903 := bstep (se 1 (by rfl) ⟨677927, by rfl⟩ : syracuseStep 903903 = 1355855) B1355855
theorem B5557015 : Blo 900574 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B903983 : Blo 900574 903983 := bstep (se 1 (by rfl) ⟨677987, by rfl⟩ : syracuseStep 903983 = 1355975) B1355975
theorem B2280271 : Blo 900574 2280271 := bstep (se 1 (by rfl) ⟨1710203, by rfl⟩ : syracuseStep 2280271 = 3420407) B3420407
theorem B904091 : Blo 900574 904091 := bstep (se 1 (by rfl) ⟨678068, by rfl⟩ : syracuseStep 904091 = 1356137) B1356137
theorem B2608043 : Blo 900574 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B904143 : Blo 900574 904143 := bstep (se 1 (by rfl) ⟨678107, by rfl⟩ : syracuseStep 904143 = 1356215) B1356215
theorem B904167 : Blo 900574 904167 := bstep (se 1 (by rfl) ⟨678125, by rfl⟩ : syracuseStep 904167 = 1356251) B1356251
theorem B2444327 : Blo 900574 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B34720811 : Blo 900574 34720811 := bstep (se 1 (by rfl) ⟨26040608, by rfl⟩ : syracuseStep 34720811 = 52081217) B52081217
theorem B2280545 : Blo 900574 2280545 := bstep (se 2 (by rfl) ⟨855204, by rfl⟩ : syracuseStep 2280545 = 1710409) B1710409
theorem B4344947 : Blo 900574 4344947 := bstep (se 1 (by rfl) ⟨3258710, by rfl⟩ : syracuseStep 4344947 = 6517421) B6517421
theorem B2935997 : Blo 900574 2935997 := bstep (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) B1100999
theorem B4869341 : Blo 900574 4869341 := bstep (se 3 (by rfl) ⟨913001, by rfl⟩ : syracuseStep 4869341 = 1826003) B1826003
theorem B904479 : Blo 900574 904479 := bstep (se 1 (by rfl) ⟨678359, by rfl⟩ : syracuseStep 904479 = 1356719) B1356719
theorem B904539 : Blo 900574 904539 := bstep (se 1 (by rfl) ⟨678404, by rfl⟩ : syracuseStep 904539 = 1356809) B1356809
theorem B904559 : Blo 900574 904559 := bstep (se 1 (by rfl) ⟨678419, by rfl⟩ : syracuseStep 904559 = 1356839) B1356839
theorem B2444705 : Blo 900574 2444705 := bstep (se 2 (by rfl) ⟨916764, by rfl⟩ : syracuseStep 2444705 = 1833529) B1833529
theorem B2280919 : Blo 900574 2280919 := bstep (se 1 (by rfl) ⟨1710689, by rfl⟩ : syracuseStep 2280919 = 3421379) B3421379
theorem B2444759 : Blo 900574 2444759 := bstep (se 1 (by rfl) ⟨1833569, by rfl⟩ : syracuseStep 2444759 = 3667139) B3667139
theorem B4869641 : Blo 900574 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B3853939 : Blo 900574 3853939 := bstep (se 1 (by rfl) ⟨2890454, by rfl⟩ : syracuseStep 3853939 = 5780909) B5780909
theorem B19549835 : Blo 900574 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B2281223 : Blo 900574 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B3428153 : Blo 900574 3428153 := bstep (se 2 (by rfl) ⟨1285557, by rfl⟩ : syracuseStep 3428153 = 2571115) B2571115
theorem B4345775 : Blo 900574 4345775 := bstep (se 1 (by rfl) ⟨3259331, by rfl⟩ : syracuseStep 4345775 = 6518663) B6518663
theorem B16437305 : Blo 900574 16437305 := bstep (se 2 (by rfl) ⟨6163989, by rfl⟩ : syracuseStep 16437305 = 12327979) B12327979
theorem B4575689 : Blo 900574 4575689 := bstep (se 2 (by rfl) ⟨1715883, by rfl⟩ : syracuseStep 4575689 = 3431767) B3431767
theorem B2282003 : Blo 900574 2282003 := bstep (se 1 (by rfl) ⟨1711502, by rfl⟩ : syracuseStep 2282003 = 3423005) B3423005
theorem B5133527 : Blo 900574 5133527 := bstep (se 1 (by rfl) ⟨3850145, by rfl⟩ : syracuseStep 5133527 = 7700291) B7700291
theorem B4576499 : Blo 900574 4576499 := bstep (se 1 (by rfl) ⟨3432374, by rfl⟩ : syracuseStep 4576499 = 6864749) B6864749
theorem B25974179 : Blo 900574 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B9754157 : Blo 900574 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B190502725 : Blo 900574 190502725 := bstep (se 4 (by rfl) ⟨17859630, by rfl⟩ : syracuseStep 190502725 = 35719261) B35719261
theorem B2283785 : Blo 900574 2283785 := bstep (se 2 (by rfl) ⟨856419, by rfl⟩ : syracuseStep 2283785 = 1712839) B1712839
theorem B3299903 : Blo 900574 3299903 := bstep (se 1 (by rfl) ⟨2474927, by rfl⟩ : syracuseStep 3299903 = 4949855) B4949855
theorem B1628743 : Blo 900574 1628743 := bstep (se 1 (by rfl) ⟨1221557, by rfl⟩ : syracuseStep 1628743 = 2443115) B2443115
theorem B2284139 : Blo 900574 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B2776051 : Blo 900574 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B3660923 : Blo 900574 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B4578443 : Blo 900574 4578443 := bstep (se 1 (by rfl) ⟨3433832, by rfl⟩ : syracuseStep 4578443 = 6867665) B6867665
theorem B2284787 : Blo 900574 2284787 := bstep (se 1 (by rfl) ⟨1713590, by rfl⟩ : syracuseStep 2284787 = 3427181) B3427181
theorem B10280357 : Blo 900574 10280357 := bstep (se 4 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 10280357 = 1927567) B1927567
theorem B6250007 : Blo 900574 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B5791313 : Blo 900574 5791313 := bstep (se 2 (by rfl) ⟨2171742, by rfl⟩ : syracuseStep 5791313 = 4343485) B4343485
theorem B5135987 : Blo 900574 5135987 := bstep (se 1 (by rfl) ⟨3851990, by rfl⟩ : syracuseStep 5135987 = 7703981) B7703981
theorem B2285243 : Blo 900574 2285243 := bstep (se 1 (by rfl) ⟨1713932, by rfl⟩ : syracuseStep 2285243 = 3427865) B3427865
theorem B5136169 : Blo 900574 5136169 := bstep (se 2 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 5136169 = 3852127) B3852127
theorem B3432239 : Blo 900574 3432239 := bstep (se 1 (by rfl) ⟨2574179, by rfl⟩ : syracuseStep 3432239 = 5148359) B5148359
theorem B3432253 : Blo 900574 3432253 := bstep (se 3 (by rfl) ⟨643547, by rfl⟩ : syracuseStep 3432253 = 1287095) B1287095
theorem B37019555 : Blo 900574 37019555 := bstep (se 1 (by rfl) ⟨27764666, by rfl⟩ : syracuseStep 37019555 = 55529333) B55529333
theorem B3039443 : Blo 900574 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B2285779 : Blo 900574 2285779 := bstep (se 1 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 2285779 = 3428669) B3428669
theorem B8675747 : Blo 900574 8675747 := bstep (se 1 (by rfl) ⟨6506810, by rfl⟩ : syracuseStep 8675747 = 13013621) B13013621
theorem B3039713 : Blo 900574 3039713 := bstep (se 2 (by rfl) ⟨1139892, by rfl⟩ : syracuseStep 3039713 = 2279785) B2279785
theorem B5137445 : Blo 900574 5137445 := bstep (se 4 (by rfl) ⟨481635, by rfl⟩ : syracuseStep 5137445 = 963271) B963271
theorem B2286731 : Blo 900574 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B34760177 : Blo 900574 34760177 := bstep (se 2 (by rfl) ⟨13035066, by rfl⟩ : syracuseStep 34760177 = 26070133) B26070133
theorem B1926713 : Blo 900574 1926713 := bstep (se 2 (by rfl) ⟨722517, by rfl⟩ : syracuseStep 1926713 = 1445035) B1445035
theorem B1041991 : Blo 900574 1041991 := bstep (se 1 (by rfl) ⟨781493, by rfl⟩ : syracuseStep 1041991 = 1562987) B1562987
theorem B2287187 : Blo 900574 2287187 := bstep (se 1 (by rfl) ⟨1715390, by rfl⟩ : syracuseStep 2287187 = 3430781) B3430781
theorem B85485149 : Blo 900574 85485149 := bstep (se 3 (by rfl) ⟨16028465, by rfl⟩ : syracuseStep 85485149 = 32056931) B32056931
theorem B3040955 : Blo 900574 3040955 := bstep (se 1 (by rfl) ⟨2280716, by rfl⟩ : syracuseStep 3040955 = 4561433) B4561433
theorem B1304527 : Blo 900574 1304527 := bstep (se 1 (by rfl) ⟨978395, by rfl⟩ : syracuseStep 1304527 = 1956791) B1956791
theorem B7334173 : Blo 900574 7334173 := bstep (se 3 (by rfl) ⟨1375157, by rfl⟩ : syracuseStep 7334173 = 2750315) B2750315
theorem B2288047 : Blo 900574 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B1567295 : Blo 900574 1567295 := bstep (se 1 (by rfl) ⟨1175471, by rfl⟩ : syracuseStep 1567295 = 2350943) B2350943
theorem B2288351 : Blo 900574 2288351 := bstep (se 1 (by rfl) ⟨1716263, by rfl⟩ : syracuseStep 2288351 = 3432527) B3432527
theorem B1829879 : Blo 900574 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B2026619 : Blo 900574 2026619 := bstep (se 1 (by rfl) ⟨1519964, by rfl⟩ : syracuseStep 2026619 = 3039929) B3039929
theorem B2026745 : Blo 900574 2026745 := bstep (se 2 (by rfl) ⟨760029, by rfl⟩ : syracuseStep 2026745 = 1520059) B1520059
theorem B2289019 : Blo 900574 2289019 := bstep (se 1 (by rfl) ⟨1716764, by rfl⟩ : syracuseStep 2289019 = 3433529) B3433529
theorem B2026889 : Blo 900574 2026889 := bstep (se 2 (by rfl) ⟨760083, by rfl⟩ : syracuseStep 2026889 = 1520167) B1520167
theorem B1928585 : Blo 900574 1928585 := bstep (se 2 (by rfl) ⟨723219, by rfl⟩ : syracuseStep 1928585 = 1446439) B1446439
theorem B19819997 : Blo 900574 19819997 := bstep (se 3 (by rfl) ⟨3716249, by rfl⟩ : syracuseStep 19819997 = 7432499) B7432499
theorem B2027015 : Blo 900574 2027015 := bstep (se 1 (by rfl) ⟨1520261, by rfl⟩ : syracuseStep 2027015 = 3040523) B3040523
theorem B3042899 : Blo 900574 3042899 := bstep (se 1 (by rfl) ⟨2282174, by rfl⟩ : syracuseStep 3042899 = 4564349) B4564349
theorem B2027195 : Blo 900574 2027195 := bstep (se 1 (by rfl) ⟨1520396, by rfl⟩ : syracuseStep 2027195 = 3040793) B3040793
theorem B2289455 : Blo 900574 2289455 := bstep (se 1 (by rfl) ⟨1717091, by rfl⟩ : syracuseStep 2289455 = 3434183) B3434183
theorem B2027321 : Blo 900574 2027321 := bstep (se 2 (by rfl) ⟨760245, by rfl⟩ : syracuseStep 2027321 = 1520491) B1520491
theorem B3862379 : Blo 900574 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B1143163 : Blo 900574 1143163 := bstep (se 1 (by rfl) ⟨857372, by rfl⟩ : syracuseStep 1143163 = 1714745) B1714745
theorem B2027951 : Blo 900574 2027951 := bstep (se 1 (by rfl) ⟨1520963, by rfl⟩ : syracuseStep 2027951 = 3041927) B3041927
theorem B2027987 : Blo 900574 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B2028095 : Blo 900574 2028095 := bstep (se 1 (by rfl) ⟨1521071, by rfl⟩ : syracuseStep 2028095 = 3042143) B3042143
theorem B1143391 : Blo 900574 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B2028203 : Blo 900574 2028203 := bstep (se 1 (by rfl) ⟨1521152, by rfl⟩ : syracuseStep 2028203 = 3042305) B3042305
theorem B2290351 : Blo 900574 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B8221753 : Blo 900574 8221753 := bstep (se 2 (by rfl) ⟨3083157, by rfl⟩ : syracuseStep 8221753 = 6166315) B6166315
theorem B3863609 : Blo 900574 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B2028743 : Blo 900574 2028743 := bstep (se 1 (by rfl) ⟨1521557, by rfl⟩ : syracuseStep 2028743 = 3043115) B3043115
theorem B2028923 : Blo 900574 2028923 := bstep (se 1 (by rfl) ⟨1521692, by rfl⟩ : syracuseStep 2028923 = 3043385) B3043385
theorem B2029049 : Blo 900574 2029049 := bstep (se 2 (by rfl) ⟨760893, by rfl⟩ : syracuseStep 2029049 = 1521787) B1521787
theorem B2029139 : Blo 900574 2029139 := bstep (se 1 (by rfl) ⟨1521854, by rfl⟩ : syracuseStep 2029139 = 3043709) B3043709
theorem B8681093 : Blo 900574 8681093 := bstep (se 4 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 8681093 = 1627705) B1627705
theorem B2029319 : Blo 900574 2029319 := bstep (se 1 (by rfl) ⟨1521989, by rfl⟩ : syracuseStep 2029319 = 3043979) B3043979
theorem B1144631 : Blo 900574 1144631 := bstep (se 1 (by rfl) ⟨858473, by rfl⟩ : syracuseStep 1144631 = 1716947) B1716947
theorem B1144783 : Blo 900574 1144783 := bstep (se 1 (by rfl) ⟨858587, by rfl⟩ : syracuseStep 1144783 = 1717175) B1717175
theorem B2029931 : Blo 900574 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B1374575 : Blo 900574 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B3045815 : Blo 900574 3045815 := bstep (se 1 (by rfl) ⟨2284361, by rfl⟩ : syracuseStep 3045815 = 4568723) B4568723
theorem B2030075 : Blo 900574 2030075 := bstep (se 1 (by rfl) ⟨1522556, by rfl⟩ : syracuseStep 2030075 = 3045113) B3045113
theorem B1931771 : Blo 900574 1931771 := bstep (se 1 (by rfl) ⟨1448828, by rfl⟩ : syracuseStep 1931771 = 2897657) B2897657
theorem B1014367 : Blo 900574 1014367 := bstep (se 1 (by rfl) ⟨760775, by rfl⟩ : syracuseStep 1014367 = 1521551) B1521551
theorem B2030201 : Blo 900574 2030201 := bstep (se 2 (by rfl) ⟨761325, by rfl⟩ : syracuseStep 2030201 = 1522651) B1522651
theorem B13040261 : Blo 900574 13040261 := bstep (se 4 (by rfl) ⟨1222524, by rfl⟩ : syracuseStep 13040261 = 2445049) B2445049
theorem B2030255 : Blo 900574 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B2030327 : Blo 900574 2030327 := bstep (se 1 (by rfl) ⟨1522745, by rfl⟩ : syracuseStep 2030327 = 3045491) B3045491
theorem B2030507 : Blo 900574 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B5209019 : Blo 900574 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B9272713 : Blo 900574 9272713 := bstep (se 2 (by rfl) ⟨3477267, by rfl⟩ : syracuseStep 9272713 = 6954535) B6954535
theorem B2031047 : Blo 900574 2031047 := bstep (se 1 (by rfl) ⟨1523285, by rfl⟩ : syracuseStep 2031047 = 3046571) B3046571
theorem B1015519 : Blo 900574 1015519 := bstep (se 1 (by rfl) ⟨761639, by rfl⟩ : syracuseStep 1015519 = 1523279) B1523279
theorem B2031407 : Blo 900574 2031407 := bstep (se 1 (by rfl) ⟨1523555, by rfl⟩ : syracuseStep 2031407 = 3047111) B3047111
theorem B12353543 : Blo 900574 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B3047705 : Blo 900574 3047705 := bstep (se 2 (by rfl) ⟨1142889, by rfl⟩ : syracuseStep 3047705 = 2285779) B2285779
theorem B3047867 : Blo 900574 3047867 := bstep (se 1 (by rfl) ⟨2285900, by rfl⟩ : syracuseStep 3047867 = 4571801) B4571801
theorem B13009643 : Blo 900574 13009643 := bstep (se 1 (by rfl) ⟨9757232, by rfl⟩ : syracuseStep 13009643 = 19514465) B19514465
theorem B4883179 : Blo 900574 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B1016743 : Blo 900574 1016743 := bstep (se 1 (by rfl) ⟨762557, by rfl⟩ : syracuseStep 1016743 = 1525115) B1525115
theorem B2032595 : Blo 900574 2032595 := bstep (se 1 (by rfl) ⟨1524446, by rfl⟩ : syracuseStep 2032595 = 3048893) B3048893
theorem B2032847 : Blo 900574 2032847 := bstep (se 1 (by rfl) ⟨1524635, by rfl⟩ : syracuseStep 2032847 = 3049271) B3049271
theorem B2033171 : Blo 900574 2033171 := bstep (se 1 (by rfl) ⟨1524878, by rfl⟩ : syracuseStep 2033171 = 3049757) B3049757
theorem B3049055 : Blo 900574 3049055 := bstep (se 1 (by rfl) ⟨2286791, by rfl⟩ : syracuseStep 3049055 = 4573583) B4573583
theorem B3245953 : Blo 900574 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B3246227 : Blo 900574 3246227 := bstep (se 1 (by rfl) ⟨2434670, by rfl⟩ : syracuseStep 3246227 = 4869341) B4869341
theorem B2033855 : Blo 900574 2033855 := bstep (se 1 (by rfl) ⟨1525391, by rfl⟩ : syracuseStep 2033855 = 3050783) B3050783
theorem B3246427 : Blo 900574 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B14617361 : Blo 900574 14617361 := bstep (se 2 (by rfl) ⟨5481510, by rfl⟩ : syracuseStep 14617361 = 10963021) B10963021
theorem B6163361 : Blo 900574 6163361 := bstep (se 2 (by rfl) ⟨2311260, by rfl⟩ : syracuseStep 6163361 = 4622521) B4622521
theorem B3050459 : Blo 900574 3050459 := bstep (se 1 (by rfl) ⟨2287844, by rfl⟩ : syracuseStep 3050459 = 4575689) B4575689
theorem B2886635 : Blo 900574 2886635 := bstep (se 1 (by rfl) ⟨2164976, by rfl⟩ : syracuseStep 2886635 = 4329953) B4329953
theorem B2034809 : Blo 900574 2034809 := bstep (se 2 (by rfl) ⟨763053, by rfl⟩ : syracuseStep 2034809 = 1526107) B1526107
theorem B3050729 : Blo 900574 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B3050999 : Blo 900574 3050999 := bstep (se 1 (by rfl) ⟨2288249, by rfl⟩ : syracuseStep 3050999 = 4576499) B4576499
theorem B1445855 : Blo 900574 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B2199935 : Blo 900574 2199935 := bstep (se 1 (by rfl) ⟨1649951, by rfl⟩ : syracuseStep 2199935 = 3299903) B3299903
theorem B5771735 : Blo 900574 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B3052025 : Blo 900574 3052025 := bstep (se 2 (by rfl) ⟨1144509, by rfl⟩ : syracuseStep 3052025 = 2289019) B2289019
theorem B3052295 : Blo 900574 3052295 := bstep (se 1 (by rfl) ⟨2289221, by rfl⟩ : syracuseStep 3052295 = 4578443) B4578443
theorem B3052349 : Blo 900574 3052349 := bstep (se 3 (by rfl) ⟨572315, by rfl⟩ : syracuseStep 3052349 = 1144631) B1144631
theorem B6853571 : Blo 900574 6853571 := bstep (se 1 (by rfl) ⟨5140178, by rfl⟩ : syracuseStep 6853571 = 10280357) B10280357
theorem B4166671 : Blo 900574 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B2888777 : Blo 900574 2888777 := bstep (se 2 (by rfl) ⟨1083291, by rfl⟩ : syracuseStep 2888777 = 2166583) B2166583
theorem B4330705 : Blo 900574 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B24679703 : Blo 900574 24679703 := bstep (se 1 (by rfl) ⟨18509777, by rfl⟩ : syracuseStep 24679703 = 37019555) B37019555
theorem B43849349 : Blo 900574 43849349 := bstep (se 4 (by rfl) ⟨4110876, by rfl⟩ : syracuseStep 43849349 = 8221753) B8221753
theorem B3086059 : Blo 900574 3086059 := bstep (se 1 (by rfl) ⟨2314544, by rfl⟩ : syracuseStep 3086059 = 4629089) B4629089
theorem B3053801 : Blo 900574 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B23173451 : Blo 900574 23173451 := bstep (se 1 (by rfl) ⟨17380088, by rfl⟩ : syracuseStep 23173451 = 34760177) B34760177
theorem B10262861 : Blo 900574 10262861 := bstep (se 3 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 10262861 = 3848573) B3848573
theorem B56990099 : Blo 900574 56990099 := bstep (se 1 (by rfl) ⟨42742574, by rfl⟩ : syracuseStep 56990099 = 85485149) B85485149
theorem B1711145 : Blo 900574 1711145 := bstep (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) B1283359
theorem B1219919 : Blo 900574 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B1351079 : Blo 900574 1351079 := bstep (se 1 (by rfl) ⟨1013309, by rfl⟩ : syracuseStep 1351079 = 2026619) B2026619
theorem B1351163 : Blo 900574 1351163 := bstep (se 1 (by rfl) ⟨1013372, by rfl⟩ : syracuseStep 1351163 = 2026745) B2026745
theorem B1351259 : Blo 900574 1351259 := bstep (se 1 (by rfl) ⟨1013444, by rfl⟩ : syracuseStep 1351259 = 2026889) B2026889
theorem B1285723 : Blo 900574 1285723 := bstep (se 1 (by rfl) ⟨964292, by rfl⟩ : syracuseStep 1285723 = 1928585) B1928585
theorem B13213331 : Blo 900574 13213331 := bstep (se 1 (by rfl) ⟨9909998, by rfl⟩ : syracuseStep 13213331 = 19819997) B19819997
theorem B1351343 : Blo 900574 1351343 := bstep (se 1 (by rfl) ⟨1013507, by rfl⟩ : syracuseStep 1351343 = 2027015) B2027015
theorem B6954781 : Blo 900574 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B1351463 : Blo 900574 1351463 := bstep (se 1 (by rfl) ⟨1013597, by rfl⟩ : syracuseStep 1351463 = 2027195) B2027195
theorem B1351547 : Blo 900574 1351547 := bstep (se 1 (by rfl) ⟨1013660, by rfl⟩ : syracuseStep 1351547 = 2027321) B2027321
theorem B7938107 : Blo 900574 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B1351967 : Blo 900574 1351967 := bstep (se 1 (by rfl) ⟨1013975, by rfl⟩ : syracuseStep 1351967 = 2027951) B2027951
theorem B1351991 : Blo 900574 1351991 := bstep (se 1 (by rfl) ⟨1013993, by rfl⟩ : syracuseStep 1351991 = 2027987) B2027987
theorem B5775731 : Blo 900574 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B1352063 : Blo 900574 1352063 := bstep (se 1 (by rfl) ⟨1014047, by rfl⟩ : syracuseStep 1352063 = 2028095) B2028095
theorem B1352135 : Blo 900574 1352135 := bstep (se 1 (by rfl) ⟨1014101, by rfl⟩ : syracuseStep 1352135 = 2028203) B2028203
theorem B2171657 : Blo 900574 2171657 := bstep (se 2 (by rfl) ⟨814371, by rfl⟩ : syracuseStep 2171657 = 1628743) B1628743
theorem B1352489 : Blo 900574 1352489 := bstep (se 2 (by rfl) ⟨507183, by rfl⟩ : syracuseStep 1352489 = 1014367) B1014367
theorem B1352495 : Blo 900574 1352495 := bstep (se 1 (by rfl) ⟨1014371, by rfl⟩ : syracuseStep 1352495 = 2028743) B2028743
theorem B1352615 : Blo 900574 1352615 := bstep (se 1 (by rfl) ⟨1014461, by rfl⟩ : syracuseStep 1352615 = 2028923) B2028923
theorem B1352699 : Blo 900574 1352699 := bstep (se 1 (by rfl) ⟨1014524, by rfl⟩ : syracuseStep 1352699 = 2029049) B2029049
theorem B1352759 : Blo 900574 1352759 := bstep (se 1 (by rfl) ⟨1014569, by rfl⟩ : syracuseStep 1352759 = 2029139) B2029139
theorem B39036005 : Blo 900574 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B1352879 : Blo 900574 1352879 := bstep (se 1 (by rfl) ⟨1014659, by rfl⟩ : syracuseStep 1352879 = 2029319) B2029319
theorem B22258921 : Blo 900574 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B3089771 : Blo 900574 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B2434475 : Blo 900574 2434475 := bstep (se 1 (by rfl) ⟨1825856, by rfl⟩ : syracuseStep 2434475 = 3651713) B3651713
theorem B1353287 : Blo 900574 1353287 := bstep (se 1 (by rfl) ⟨1014965, by rfl⟩ : syracuseStep 1353287 = 2029931) B2029931
theorem B27829909 : Blo 900574 27829909 := bstep (se 6 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 27829909 = 1304527) B1304527
theorem B1353383 : Blo 900574 1353383 := bstep (se 1 (by rfl) ⟨1015037, by rfl⟩ : syracuseStep 1353383 = 2030075) B2030075
theorem B1287847 : Blo 900574 1287847 := bstep (se 1 (by rfl) ⟨965885, by rfl⟩ : syracuseStep 1287847 = 1931771) B1931771
theorem B1353467 : Blo 900574 1353467 := bstep (se 1 (by rfl) ⟨1015100, by rfl⟩ : syracuseStep 1353467 = 2030201) B2030201
theorem B8693507 : Blo 900574 8693507 := bstep (se 1 (by rfl) ⟨6520130, by rfl⟩ : syracuseStep 8693507 = 13040261) B13040261
theorem B1353503 : Blo 900574 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B1353551 : Blo 900574 1353551 := bstep (se 1 (by rfl) ⟨1015163, by rfl⟩ : syracuseStep 1353551 = 2030327) B2030327
theorem B12363617 : Blo 900574 12363617 := bstep (se 2 (by rfl) ⟨4636356, by rfl⟩ : syracuseStep 12363617 = 9272713) B9272713
theorem B1353671 : Blo 900574 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B1354025 : Blo 900574 1354025 := bstep (se 2 (by rfl) ⟨507759, by rfl⟩ : syracuseStep 1354025 = 1015519) B1015519
theorem B1354031 : Blo 900574 1354031 := bstep (se 1 (by rfl) ⟨1015523, by rfl⟩ : syracuseStep 1354031 = 2031047) B2031047
theorem B1354271 : Blo 900574 1354271 := bstep (se 1 (by rfl) ⟨1015703, by rfl⟩ : syracuseStep 1354271 = 2031407) B2031407
theorem B17345339 : Blo 900574 17345339 := bstep (se 1 (by rfl) ⟨13009004, by rfl⟩ : syracuseStep 17345339 = 26018009) B26018009
theorem B1354655 : Blo 900574 1354655 := bstep (se 1 (by rfl) ⟨1015991, by rfl⟩ : syracuseStep 1354655 = 2031983) B2031983
theorem B1354703 : Blo 900574 1354703 := bstep (se 1 (by rfl) ⟨1016027, by rfl⟩ : syracuseStep 1354703 = 2032055) B2032055
theorem B1354793 : Blo 900574 1354793 := bstep (se 2 (by rfl) ⟨508047, by rfl⟩ : syracuseStep 1354793 = 1016095) B1016095
theorem B1354799 : Blo 900574 1354799 := bstep (se 1 (by rfl) ⟨1016099, by rfl⟩ : syracuseStep 1354799 = 2032199) B2032199
theorem B1354823 : Blo 900574 1354823 := bstep (se 1 (by rfl) ⟨1016117, by rfl⟩ : syracuseStep 1354823 = 2032235) B2032235
theorem B3419435 : Blo 900574 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B1355087 : Blo 900574 1355087 := bstep (se 1 (by rfl) ⟨1016315, by rfl⟩ : syracuseStep 1355087 = 2032631) B2032631
theorem B1355177 : Blo 900574 1355177 := bstep (se 2 (by rfl) ⟨508191, by rfl⟩ : syracuseStep 1355177 = 1016383) B1016383
theorem B2567675 : Blo 900574 2567675 := bstep (se 1 (by rfl) ⟨1925756, by rfl⟩ : syracuseStep 2567675 = 3851513) B3851513
theorem B1355327 : Blo 900574 1355327 := bstep (se 1 (by rfl) ⟨1016495, by rfl⟩ : syracuseStep 1355327 = 2032991) B2032991
theorem B1027675 : Blo 900574 1027675 := bstep (se 1 (by rfl) ⟨770756, by rfl⟩ : syracuseStep 1027675 = 1541513) B1541513
theorem B1355591 : Blo 900574 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B1355675 : Blo 900574 1355675 := bstep (se 1 (by rfl) ⟨1016756, by rfl⟩ : syracuseStep 1355675 = 2033513) B2033513
theorem B42315979 : Blo 900574 42315979 := bstep (se 1 (by rfl) ⟨31736984, by rfl⟩ : syracuseStep 42315979 = 63473969) B63473969
theorem B1356239 : Blo 900574 1356239 := bstep (se 1 (by rfl) ⟨1017179, by rfl⟩ : syracuseStep 1356239 = 2034359) B2034359
theorem B1356281 : Blo 900574 1356281 := bstep (se 2 (by rfl) ⟨508605, by rfl⟩ : syracuseStep 1356281 = 1017211) B1017211
theorem B1356383 : Blo 900574 1356383 := bstep (se 1 (by rfl) ⟨1017287, by rfl⟩ : syracuseStep 1356383 = 2034575) B2034575
theorem B23147207 : Blo 900574 23147207 := bstep (se 1 (by rfl) ⟨17360405, by rfl⟩ : syracuseStep 23147207 = 34720811) B34720811
theorem B1520363 : Blo 900574 1520363 := bstep (se 1 (by rfl) ⟨1140272, by rfl⟩ : syracuseStep 1520363 = 2280545) B2280545
theorem B2896631 : Blo 900574 2896631 := bstep (se 1 (by rfl) ⟨2172473, by rfl⟩ : syracuseStep 2896631 = 4344947) B4344947
theorem B3257383 : Blo 900574 3257383 := bstep (se 1 (by rfl) ⟨2443037, by rfl⟩ : syracuseStep 3257383 = 4886075) B4886075
theorem B1520815 : Blo 900574 1520815 := bstep (se 1 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 1520815 = 2281223) B2281223
theorem B2897183 : Blo 900574 2897183 := bstep (se 1 (by rfl) ⟨2172887, by rfl⟩ : syracuseStep 2897183 = 4345775) B4345775
theorem B10958203 : Blo 900574 10958203 := bstep (se 1 (by rfl) ⟨8218652, by rfl⟩ : syracuseStep 10958203 = 16437305) B16437305
theorem B10270151 : Blo 900574 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B7714439 : Blo 900574 7714439 := bstep (se 1 (by rfl) ⟨5785829, by rfl⟩ : syracuseStep 7714439 = 11571659) B11571659
theorem B1521335 : Blo 900574 1521335 := bstep (se 1 (by rfl) ⟨1141001, by rfl⟩ : syracuseStep 1521335 = 2282003) B2282003
theorem B9778897 : Blo 900574 9778897 := bstep (se 2 (by rfl) ⟨3667086, by rfl⟩ : syracuseStep 9778897 = 7334173) B7334173
theorem B3258107 : Blo 900574 3258107 := bstep (se 1 (by rfl) ⟨2443580, by rfl⟩ : syracuseStep 3258107 = 4887161) B4887161
theorem B2471899 : Blo 900574 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B3422351 : Blo 900574 3422351 := bstep (se 1 (by rfl) ⟨2566763, by rfl⟩ : syracuseStep 3422351 = 5133527) B5133527
theorem B17316119 : Blo 900574 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B6502771 : Blo 900574 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B29637413 : Blo 900574 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B1522523 : Blo 900574 1522523 := bstep (se 1 (by rfl) ⟨1141892, by rfl⟩ : syracuseStep 1522523 = 2283785) B2283785
theorem B965467 : Blo 900574 965467 := bstep (se 1 (by rfl) ⟨724100, by rfl⟩ : syracuseStep 965467 = 1448201) B1448201
theorem B3849257 : Blo 900574 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1522759 : Blo 900574 1522759 := bstep (se 1 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 1522759 = 2284139) B2284139
theorem B2571389 : Blo 900574 2571389 := bstep (se 3 (by rfl) ⟨482135, by rfl⟩ : syracuseStep 2571389 = 964271) B964271
theorem B900583 : Blo 900574 900583 := bstep (se 1 (by rfl) ⟨675437, by rfl⟩ : syracuseStep 900583 = 1350875) B1350875
theorem B1523191 : Blo 900574 1523191 := bstep (se 1 (by rfl) ⟨1142393, by rfl⟩ : syracuseStep 1523191 = 2284787) B2284787
theorem B900699 : Blo 900574 900699 := bstep (se 1 (by rfl) ⟨675524, by rfl⟩ : syracuseStep 900699 = 1351049) B1351049
theorem B3423977 : Blo 900574 3423977 := bstep (se 2 (by rfl) ⟨1283991, by rfl⟩ : syracuseStep 3423977 = 2567983) B2567983
theorem B3423991 : Blo 900574 3423991 := bstep (se 1 (by rfl) ⟨2567993, by rfl⟩ : syracuseStep 3423991 = 5135987) B5135987
theorem B1523495 : Blo 900574 1523495 := bstep (se 1 (by rfl) ⟨1142621, by rfl⟩ : syracuseStep 1523495 = 2285243) B2285243
theorem B900935 : Blo 900574 900935 := bstep (se 1 (by rfl) ⟨675701, by rfl⟩ : syracuseStep 900935 = 1351403) B1351403
theorem B901087 : Blo 900574 901087 := bstep (se 1 (by rfl) ⟨675815, by rfl⟩ : syracuseStep 901087 = 1351631) B1351631
theorem B901351 : Blo 900574 901351 := bstep (se 1 (by rfl) ⟨676013, by rfl⟩ : syracuseStep 901351 = 1352027) B1352027
theorem B5783831 : Blo 900574 5783831 := bstep (se 1 (by rfl) ⟨4337873, by rfl⟩ : syracuseStep 5783831 = 8675747) B8675747
theorem B901503 : Blo 900574 901503 := bstep (se 1 (by rfl) ⟨676127, by rfl⟩ : syracuseStep 901503 = 1352255) B1352255
theorem B901583 : Blo 900574 901583 := bstep (se 1 (by rfl) ⟨676187, by rfl⟩ : syracuseStep 901583 = 1352375) B1352375
theorem B4637135 : Blo 900574 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B1524217 : Blo 900574 1524217 := bstep (se 2 (by rfl) ⟨571581, by rfl⟩ : syracuseStep 1524217 = 1143163) B1143163
theorem B901735 : Blo 900574 901735 := bstep (se 1 (by rfl) ⟨676301, by rfl⟩ : syracuseStep 901735 = 1352603) B1352603
theorem B3424963 : Blo 900574 3424963 := bstep (se 1 (by rfl) ⟨2568722, by rfl⟩ : syracuseStep 3424963 = 5137445) B5137445
theorem B1524487 : Blo 900574 1524487 := bstep (se 1 (by rfl) ⟨1143365, by rfl⟩ : syracuseStep 1524487 = 2286731) B2286731
theorem B1524521 : Blo 900574 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B901999 : Blo 900574 901999 := bstep (se 1 (by rfl) ⟨676499, by rfl⟩ : syracuseStep 901999 = 1352999) B1352999
theorem B902055 : Blo 900574 902055 := bstep (se 1 (by rfl) ⟨676541, by rfl⟩ : syracuseStep 902055 = 1353083) B1353083
theorem B902139 : Blo 900574 902139 := bstep (se 1 (by rfl) ⟨676604, by rfl⟩ : syracuseStep 902139 = 1353209) B1353209
theorem B1524791 : Blo 900574 1524791 := bstep (se 1 (by rfl) ⟨1143593, by rfl⟩ : syracuseStep 1524791 = 2287187) B2287187
theorem B902207 : Blo 900574 902207 := bstep (se 1 (by rfl) ⟨676655, by rfl⟩ : syracuseStep 902207 = 1353311) B1353311
theorem B902351 : Blo 900574 902351 := bstep (se 1 (by rfl) ⟨676763, by rfl⟩ : syracuseStep 902351 = 1353527) B1353527
theorem B60081425 : Blo 900574 60081425 := bstep (se 2 (by rfl) ⟨22530534, by rfl⟩ : syracuseStep 60081425 = 45061069) B45061069
theorem B902555 : Blo 900574 902555 := bstep (se 1 (by rfl) ⟨676916, by rfl⟩ : syracuseStep 902555 = 1353833) B1353833
theorem B902767 : Blo 900574 902767 := bstep (se 1 (by rfl) ⟨677075, by rfl⟩ : syracuseStep 902767 = 1354151) B1354151
theorem B902823 : Blo 900574 902823 := bstep (se 1 (by rfl) ⟨677117, by rfl⟩ : syracuseStep 902823 = 1354235) B1354235
theorem B902907 : Blo 900574 902907 := bstep (se 1 (by rfl) ⟨677180, by rfl⟩ : syracuseStep 902907 = 1354361) B1354361
theorem B902943 : Blo 900574 902943 := bstep (se 1 (by rfl) ⟨677207, by rfl⟩ : syracuseStep 902943 = 1354415) B1354415
theorem B902975 : Blo 900574 902975 := bstep (se 1 (by rfl) ⟨677231, by rfl⟩ : syracuseStep 902975 = 1354463) B1354463
theorem B1525567 : Blo 900574 1525567 := bstep (se 1 (by rfl) ⟨1144175, by rfl⟩ : syracuseStep 1525567 = 2288351) B2288351
theorem B903151 : Blo 900574 903151 := bstep (se 1 (by rfl) ⟨677363, by rfl⟩ : syracuseStep 903151 = 1354727) B1354727
theorem B903323 : Blo 900574 903323 := bstep (se 1 (by rfl) ⟨677492, by rfl⟩ : syracuseStep 903323 = 1354985) B1354985
theorem B903359 : Blo 900574 903359 := bstep (se 1 (by rfl) ⟨677519, by rfl⟩ : syracuseStep 903359 = 1355039) B1355039
theorem B6867179 : Blo 900574 6867179 := bstep (se 1 (by rfl) ⟨5150384, by rfl⟩ : syracuseStep 6867179 = 10300769) B10300769
theorem B903471 : Blo 900574 903471 := bstep (se 1 (by rfl) ⟨677603, by rfl⟩ : syracuseStep 903471 = 1355207) B1355207
theorem B11553101 : Blo 900574 11553101 := bstep (se 3 (by rfl) ⟨2166206, by rfl⟩ : syracuseStep 11553101 = 4332413) B4332413
theorem B254003633 : Blo 900574 254003633 := bstep (se 2 (by rfl) ⟨95251362, by rfl⟩ : syracuseStep 254003633 = 190502725) B190502725
theorem B903707 : Blo 900574 903707 := bstep (se 1 (by rfl) ⟨677780, by rfl⟩ : syracuseStep 903707 = 1355561) B1355561
theorem B903711 : Blo 900574 903711 := bstep (se 1 (by rfl) ⟨677783, by rfl⟩ : syracuseStep 903711 = 1355567) B1355567
theorem B1526303 : Blo 900574 1526303 := bstep (se 1 (by rfl) ⟨1144727, by rfl⟩ : syracuseStep 1526303 = 2289455) B2289455
theorem B2574919 : Blo 900574 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B1526377 : Blo 900574 1526377 := bstep (se 2 (by rfl) ⟨572391, by rfl⟩ : syracuseStep 1526377 = 1144783) B1144783
theorem B7719563 : Blo 900574 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B3852947 : Blo 900574 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B904027 : Blo 900574 904027 := bstep (se 1 (by rfl) ⟨678020, by rfl⟩ : syracuseStep 904027 = 1356041) B1356041
theorem B904095 : Blo 900574 904095 := bstep (se 1 (by rfl) ⟨678071, by rfl⟩ : syracuseStep 904095 = 1356143) B1356143
theorem B5557285 : Blo 900574 5557285 := bstep (se 4 (by rfl) ⟨520995, by rfl⟩ : syracuseStep 5557285 = 1041991) B1041991
theorem B904239 : Blo 900574 904239 := bstep (se 1 (by rfl) ⟨678179, by rfl⟩ : syracuseStep 904239 = 1356359) B1356359
theorem B904263 : Blo 900574 904263 := bstep (se 1 (by rfl) ⟨678197, by rfl⟩ : syracuseStep 904263 = 1356395) B1356395
theorem B904415 : Blo 900574 904415 := bstep (se 1 (by rfl) ⟨678311, by rfl⟩ : syracuseStep 904415 = 1356623) B1356623
theorem B2575739 : Blo 900574 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B6507965 : Blo 900574 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B1625825 : Blo 900574 1625825 := bstep (se 2 (by rfl) ⟨609684, by rfl⟩ : syracuseStep 1625825 = 1219369) B1219369
theorem B5787395 : Blo 900574 5787395 := bstep (se 1 (by rfl) ⟨4340546, by rfl⟩ : syracuseStep 5787395 = 8681093) B8681093
theorem B6180713 : Blo 900574 6180713 := bstep (se 2 (by rfl) ⟨2317767, by rfl⟩ : syracuseStep 6180713 = 4635535) B4635535
theorem B2281355 : Blo 900574 2281355 := bstep (se 1 (by rfl) ⟨1711016, by rfl⟩ : syracuseStep 2281355 = 3422033) B3422033
theorem B4641239 : Blo 900574 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B9884753 : Blo 900574 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B4576337 : Blo 900574 4576337 := bstep (se 2 (by rfl) ⟨1716126, by rfl⟩ : syracuseStep 4576337 = 3432253) B3432253
theorem B7328987 : Blo 900574 7328987 := bstep (se 1 (by rfl) ⟨5496740, by rfl⟩ : syracuseStep 7328987 = 10993481) B10993481
theorem B2282843 : Blo 900574 2282843 := bstep (se 1 (by rfl) ⟨1712132, by rfl⟩ : syracuseStep 2282843 = 3424265) B3424265
theorem B1234543 : Blo 900574 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B1627769 : Blo 900574 1627769 := bstep (se 2 (by rfl) ⟨610413, by rfl⟩ : syracuseStep 1627769 = 1220827) B1220827
theorem B16701299 : Blo 900574 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B6510617 : Blo 900574 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B5789981 : Blo 900574 5789981 := bstep (se 3 (by rfl) ⟨1085621, by rfl⟩ : syracuseStep 5789981 = 2171243) B2171243
theorem B5134985 : Blo 900574 5134985 := bstep (se 2 (by rfl) ⟨1925619, by rfl⟩ : syracuseStep 5134985 = 3851239) B3851239
theorem B3431069 : Blo 900574 3431069 := bstep (se 3 (by rfl) ⟨643325, by rfl⟩ : syracuseStep 3431069 = 1286651) B1286651
theorem B39083057 : Blo 900574 39083057 := bstep (se 2 (by rfl) ⟨14656146, by rfl⟩ : syracuseStep 39083057 = 29312293) B29312293
theorem B8674361 : Blo 900574 8674361 := bstep (se 2 (by rfl) ⟨3252885, by rfl⟩ : syracuseStep 8674361 = 6505771) B6505771
theorem B5201081 : Blo 900574 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B1629551 : Blo 900574 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B1957331 : Blo 900574 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B1629803 : Blo 900574 1629803 := bstep (se 1 (by rfl) ⟨1222352, by rfl⟩ : syracuseStep 1629803 = 2444705) B2444705
theorem B1629839 : Blo 900574 1629839 := bstep (se 1 (by rfl) ⟨1222379, by rfl⟩ : syracuseStep 1629839 = 2444759) B2444759
theorem B13033223 : Blo 900574 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B2285435 : Blo 900574 2285435 := bstep (se 1 (by rfl) ⟨1714076, by rfl⟩ : syracuseStep 2285435 = 3428153) B3428153
theorem B5136443 : Blo 900574 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B12345497 : Blo 900574 12345497 := bstep (se 2 (by rfl) ⟨4629561, by rfl⟩ : syracuseStep 12345497 = 9259123) B9259123
theorem B25977185 : Blo 900574 25977185 := bstep (se 2 (by rfl) ⟨9741444, by rfl⟩ : syracuseStep 25977185 = 19482889) B19482889
theorem B2285921 : Blo 900574 2285921 := bstep (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) B1714441
theorem B3040361 : Blo 900574 3040361 := bstep (se 2 (by rfl) ⟨1140135, by rfl⟩ : syracuseStep 3040361 = 2280271) B2280271
theorem B3859645 : Blo 900574 3859645 := bstep (se 3 (by rfl) ⟨723683, by rfl⟩ : syracuseStep 3859645 = 1447367) B1447367
theorem B4875695 : Blo 900574 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B5137901 : Blo 900574 5137901 := bstep (se 3 (by rfl) ⟨963356, by rfl⟩ : syracuseStep 5137901 = 1926713) B1926713
theorem B1140475 : Blo 900574 1140475 := bstep (se 1 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 1140475 = 1710713) B1710713
theorem B3041225 : Blo 900574 3041225 := bstep (se 2 (by rfl) ⟨1140459, by rfl⟩ : syracuseStep 3041225 = 2280919) B2280919
theorem B5138585 : Blo 900574 5138585 := bstep (se 2 (by rfl) ⟨1926969, by rfl⟩ : syracuseStep 5138585 = 3853939) B3853939
theorem B3041495 : Blo 900574 3041495 := bstep (se 1 (by rfl) ⟨2281121, by rfl⟩ : syracuseStep 3041495 = 4562243) B4562243
theorem B2287865 : Blo 900574 2287865 := bstep (se 2 (by rfl) ⟨857949, by rfl⟩ : syracuseStep 2287865 = 1715899) B1715899
theorem B10283273 : Blo 900574 10283273 := bstep (se 2 (by rfl) ⟨3856227, by rfl⟩ : syracuseStep 10283273 = 7712455) B7712455
theorem B10971449 : Blo 900574 10971449 := bstep (se 2 (by rfl) ⟨4114293, by rfl⟩ : syracuseStep 10971449 = 8228587) B8228587
theorem B3860875 : Blo 900574 3860875 := bstep (se 1 (by rfl) ⟨2895656, by rfl⟩ : syracuseStep 3860875 = 5791313) B5791313
theorem B3041819 : Blo 900574 3041819 := bstep (se 1 (by rfl) ⟨2281364, by rfl⟩ : syracuseStep 3041819 = 4562729) B4562729
theorem B2288159 : Blo 900574 2288159 := bstep (se 1 (by rfl) ⟨1716119, by rfl⟩ : syracuseStep 2288159 = 3432239) B3432239
theorem B14805605 : Blo 900574 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B2026295 : Blo 900574 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B2026475 : Blo 900574 2026475 := bstep (se 1 (by rfl) ⟨1519856, by rfl⟩ : syracuseStep 2026475 = 3039713) B3039713
theorem B1371401 : Blo 900574 1371401 := bstep (se 2 (by rfl) ⟨514275, by rfl⟩ : syracuseStep 1371401 = 1028551) B1028551
theorem B1142095 : Blo 900574 1142095 := bstep (se 1 (by rfl) ⟨856571, by rfl⟩ : syracuseStep 1142095 = 1713143) B1713143
theorem B3042683 : Blo 900574 3042683 := bstep (se 1 (by rfl) ⟨2282012, by rfl⟩ : syracuseStep 3042683 = 4564025) B4564025
theorem B1142363 : Blo 900574 1142363 := bstep (se 1 (by rfl) ⟨856772, by rfl⟩ : syracuseStep 1142363 = 1713545) B1713545
theorem B3665533 : Blo 900574 3665533 := bstep (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) B1374575
theorem B2027303 : Blo 900574 2027303 := bstep (se 1 (by rfl) ⟨1520477, by rfl⟩ : syracuseStep 2027303 = 3040955) B3040955
theorem B1044863 : Blo 900574 1044863 := bstep (se 1 (by rfl) ⟨783647, by rfl⟩ : syracuseStep 1044863 = 1567295) B1567295
theorem B3044087 : Blo 900574 3044087 := bstep (se 1 (by rfl) ⟨2283065, by rfl⟩ : syracuseStep 3044087 = 4566131) B4566131
theorem B24998657 : Blo 900574 24998657 := bstep (se 2 (by rfl) ⟨9374496, by rfl⟩ : syracuseStep 24998657 = 18748993) B18748993
theorem B2028329 : Blo 900574 2028329 := bstep (se 2 (by rfl) ⟨760623, by rfl⟩ : syracuseStep 2028329 = 1521247) B1521247
theorem B3175229 : Blo 900574 3175229 := bstep (se 3 (by rfl) ⟨595355, by rfl⟩ : syracuseStep 3175229 = 1190711) B1190711
theorem B2028599 : Blo 900574 2028599 := bstep (se 1 (by rfl) ⟨1521449, by rfl⟩ : syracuseStep 2028599 = 3042899) B3042899
theorem B2028617 : Blo 900574 2028617 := bstep (se 2 (by rfl) ⟨760731, by rfl⟩ : syracuseStep 2028617 = 1521463) B1521463
theorem B1143983 : Blo 900574 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B3044627 : Blo 900574 3044627 := bstep (se 1 (by rfl) ⟨2283470, by rfl⟩ : syracuseStep 3044627 = 4566941) B4566941
theorem B1013359 : Blo 900574 1013359 := bstep (se 1 (by rfl) ⟨760019, by rfl⟩ : syracuseStep 1013359 = 1520039) B1520039
theorem B9762461 : Blo 900574 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B1013467 : Blo 900574 1013467 := bstep (se 1 (by rfl) ⟨760100, by rfl⟩ : syracuseStep 1013467 = 1520201) B1520201
theorem B3045167 : Blo 900574 3045167 := bstep (se 1 (by rfl) ⟨2283875, by rfl⟩ : syracuseStep 3045167 = 4567751) B4567751
theorem B10417997 : Blo 900574 10417997 := bstep (se 3 (by rfl) ⟨1953374, by rfl⟩ : syracuseStep 10417997 = 3906749) B3906749
theorem B5863997 : Blo 900574 5863997 := bstep (se 3 (by rfl) ⟨1099499, by rfl⟩ : syracuseStep 5863997 = 2198999) B2198999
theorem B1014619 : Blo 900574 1014619 := bstep (se 1 (by rfl) ⟨760964, by rfl⟩ : syracuseStep 1014619 = 1521929) B1521929
theorem B7699333 : Blo 900574 7699333 := bstep (se 4 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 7699333 = 1443625) B1443625
theorem B2030543 : Blo 900574 2030543 := bstep (se 1 (by rfl) ⟨1522907, by rfl⟩ : syracuseStep 2030543 = 3045815) B3045815
theorem B2030561 : Blo 900574 2030561 := bstep (se 2 (by rfl) ⟨761460, by rfl⟩ : syracuseStep 2030561 = 1522921) B1522921
theorem B8682511 : Blo 900574 8682511 := bstep (se 1 (by rfl) ⟨6511883, by rfl⟩ : syracuseStep 8682511 = 13023767) B13023767
theorem B2030633 : Blo 900574 2030633 := bstep (se 2 (by rfl) ⟨761487, by rfl⟩ : syracuseStep 2030633 = 1522975) B1522975
theorem B10976543 : Blo 900574 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B3472679 : Blo 900574 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B3047003 : Blo 900574 3047003 := bstep (se 1 (by rfl) ⟨2285252, by rfl⟩ : syracuseStep 3047003 = 4570505) B4570505
theorem B6848225 : Blo 900574 6848225 := bstep (se 2 (by rfl) ⟨2568084, by rfl⟩ : syracuseStep 6848225 = 5136169) B5136169
theorem B1015591 : Blo 900574 1015591 := bstep (se 1 (by rfl) ⟨761693, by rfl⟩ : syracuseStep 1015591 = 1523387) B1523387
theorem B2031803 : Blo 900574 2031803 := bstep (se 1 (by rfl) ⟨1523852, by rfl⟩ : syracuseStep 2031803 = 3047705) B3047705
theorem B2031911 : Blo 900574 2031911 := bstep (se 1 (by rfl) ⟨1523933, by rfl⟩ : syracuseStep 2031911 = 3047867) B3047867
theorem B1016347 : Blo 900574 1016347 := bstep (se 1 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 1016347 = 1524521) B1524521
theorem B2032289 : Blo 900574 2032289 := bstep (se 2 (by rfl) ⟨762108, by rfl⟩ : syracuseStep 2032289 = 1524217) B1524217
theorem B1016527 : Blo 900574 1016527 := bstep (se 1 (by rfl) ⟨762395, by rfl⟩ : syracuseStep 1016527 = 1524791) B1524791
theorem B2032649 : Blo 900574 2032649 := bstep (se 2 (by rfl) ⟨762243, by rfl⟩ : syracuseStep 2032649 = 1524487) B1524487
theorem B2032703 : Blo 900574 2032703 := bstep (se 1 (by rfl) ⟨1524527, by rfl⟩ : syracuseStep 2032703 = 3049055) B3049055
theorem B2164151 : Blo 900574 2164151 := bstep (se 1 (by rfl) ⟨1623113, by rfl⟩ : syracuseStep 2164151 = 3246227) B3246227
theorem B7702067 : Blo 900574 7702067 := bstep (se 1 (by rfl) ⟨5776550, by rfl⟩ : syracuseStep 7702067 = 11553101) B11553101
theorem B5146193 : Blo 900574 5146193 := bstep (se 2 (by rfl) ⟨1929822, by rfl⟩ : syracuseStep 5146193 = 3859645) B3859645
theorem B1017535 : Blo 900574 1017535 := bstep (se 1 (by rfl) ⟨763151, by rfl⟩ : syracuseStep 1017535 = 1526303) B1526303
theorem B5146375 : Blo 900574 5146375 := bstep (se 1 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 5146375 = 7719563) B7719563
theorem B2033639 : Blo 900574 2033639 := bstep (se 1 (by rfl) ⟨1525229, by rfl⟩ : syracuseStep 2033639 = 3050459) B3050459
theorem B2033819 : Blo 900574 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B2033999 : Blo 900574 2033999 := bstep (se 1 (by rfl) ⟨1525499, by rfl⟩ : syracuseStep 2033999 = 3050999) B3050999
theorem B2034089 : Blo 900574 2034089 := bstep (se 2 (by rfl) ⟨762783, by rfl⟩ : syracuseStep 2034089 = 1525567) B1525567
theorem B1083883 : Blo 900574 1083883 := bstep (se 1 (by rfl) ⟨812912, by rfl⟩ : syracuseStep 1083883 = 1625825) B1625825
theorem B4327937 : Blo 900574 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B2034683 : Blo 900574 2034683 := bstep (se 1 (by rfl) ⟨1526012, by rfl⟩ : syracuseStep 2034683 = 3052025) B3052025
theorem B4328569 : Blo 900574 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B3050621 : Blo 900574 3050621 := bstep (se 3 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 3050621 = 1143983) B1143983
theorem B2034863 : Blo 900574 2034863 := bstep (se 1 (by rfl) ⟨1526147, by rfl⟩ : syracuseStep 2034863 = 3052295) B3052295
theorem B5147833 : Blo 900574 5147833 := bstep (se 2 (by rfl) ⟨1930437, by rfl⟩ : syracuseStep 5147833 = 3860875) B3860875
theorem B2034899 : Blo 900574 2034899 := bstep (se 1 (by rfl) ⟨1526174, by rfl⟩ : syracuseStep 2034899 = 3052349) B3052349
theorem B6589835 : Blo 900574 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B3050891 : Blo 900574 3050891 := bstep (se 1 (by rfl) ⟨2288168, by rfl⟩ : syracuseStep 3050891 = 4576337) B4576337
theorem B2035169 : Blo 900574 2035169 := bstep (se 2 (by rfl) ⟨763188, by rfl⟩ : syracuseStep 2035169 = 1526377) B1526377
theorem B4885991 : Blo 900574 4885991 := bstep (se 1 (by rfl) ⟨3664493, by rfl⟩ : syracuseStep 4885991 = 7328987) B7328987
theorem B16453135 : Blo 900574 16453135 := bstep (se 1 (by rfl) ⟨12339851, by rfl⟩ : syracuseStep 16453135 = 24679703) B24679703
theorem B29232899 : Blo 900574 29232899 := bstep (se 1 (by rfl) ⟨21924674, by rfl⟩ : syracuseStep 29232899 = 43849349) B43849349
theorem B6491933 : Blo 900574 6491933 := bstep (se 3 (by rfl) ⟨1217237, by rfl⟩ : syracuseStep 6491933 = 2434475) B2434475
theorem B11145205 : Blo 900574 11145205 := bstep (se 5 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 11145205 = 1044863) B1044863
theorem B7409713 : Blo 900574 7409713 := bstep (se 2 (by rfl) ⟨2778642, by rfl⟩ : syracuseStep 7409713 = 5557285) B5557285
theorem B2035867 : Blo 900574 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B26055371 : Blo 900574 26055371 := bstep (se 1 (by rfl) ⟨19541528, by rfl⟩ : syracuseStep 26055371 = 39083057) B39083057
theorem B4887377 : Blo 900574 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B1086367 : Blo 900574 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B1086535 : Blo 900574 1086535 := bstep (se 1 (by rfl) ⟨814901, by rfl⟩ : syracuseStep 1086535 = 1629803) B1629803
theorem B8688815 : Blo 900574 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B8230331 : Blo 900574 8230331 := bstep (se 1 (by rfl) ⟨6172748, by rfl⟩ : syracuseStep 8230331 = 12345497) B12345497
theorem B26024003 : Blo 900574 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B3250463 : Blo 900574 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B6855515 : Blo 900574 6855515 := bstep (se 1 (by rfl) ⟨5141636, by rfl⟩ : syracuseStep 6855515 = 10283273) B10283273
theorem B7314299 : Blo 900574 7314299 := bstep (se 1 (by rfl) ⟨5485724, by rfl⟩ : syracuseStep 7314299 = 10971449) B10971449
theorem B5774273 : Blo 900574 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B9870403 : Blo 900574 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B1350863 : Blo 900574 1350863 := bstep (se 1 (by rfl) ⟨1013147, by rfl⟩ : syracuseStep 1350863 = 2026295) B2026295
theorem B1350983 : Blo 900574 1350983 := bstep (se 1 (by rfl) ⟨1013237, by rfl⟩ : syracuseStep 1350983 = 2026475) B2026475
theorem B1351145 : Blo 900574 1351145 := bstep (se 2 (by rfl) ⟨506679, by rfl⟩ : syracuseStep 1351145 = 1013359) B1013359
theorem B1646057 : Blo 900574 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B1351289 : Blo 900574 1351289 := bstep (se 2 (by rfl) ⟨506733, by rfl⟩ : syracuseStep 1351289 = 1013467) B1013467
theorem B1711783 : Blo 900574 1711783 := bstep (se 1 (by rfl) ⟨1283837, by rfl⟩ : syracuseStep 1711783 = 2567675) B2567675
theorem B1351535 : Blo 900574 1351535 := bstep (se 1 (by rfl) ⟨1013651, by rfl⟩ : syracuseStep 1351535 = 2027303) B2027303
theorem B4563053 : Blo 900574 4563053 := bstep (se 3 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 4563053 = 1711145) B1711145
theorem B1352219 : Blo 900574 1352219 := bstep (se 1 (by rfl) ⟨1014164, by rfl⟩ : syracuseStep 1352219 = 2028329) B2028329
theorem B1352399 : Blo 900574 1352399 := bstep (se 1 (by rfl) ⟨1014299, by rfl⟩ : syracuseStep 1352399 = 2028599) B2028599
theorem B1352411 : Blo 900574 1352411 := bstep (se 1 (by rfl) ⟨1014308, by rfl⟩ : syracuseStep 1352411 = 2028617) B2028617
theorem B3253117 : Blo 900574 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B1352825 : Blo 900574 1352825 := bstep (se 2 (by rfl) ⟨507309, by rfl⟩ : syracuseStep 1352825 = 1014619) B1014619
theorem B1287289 : Blo 900574 1287289 := bstep (se 2 (by rfl) ⟨482733, by rfl⟩ : syracuseStep 1287289 = 965467) B965467
theorem B2172071 : Blo 900574 2172071 := bstep (se 1 (by rfl) ⟨1629053, by rfl⟩ : syracuseStep 2172071 = 3258107) B3258107
theorem B10265777 : Blo 900574 10265777 := bstep (se 2 (by rfl) ⟨3849666, by rfl⟩ : syracuseStep 10265777 = 7699333) B7699333
theorem B5219549 : Blo 900574 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B11576681 : Blo 900574 11576681 := bstep (se 2 (by rfl) ⟨4341255, by rfl⟩ : syracuseStep 11576681 = 8682511) B8682511
theorem B11544079 : Blo 900574 11544079 := bstep (se 1 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 11544079 = 17316119) B17316119
theorem B3909331 : Blo 900574 3909331 := bstep (se 1 (by rfl) ⟨2931998, by rfl⟩ : syracuseStep 3909331 = 5863997) B5863997
theorem B1353695 : Blo 900574 1353695 := bstep (se 1 (by rfl) ⟨1015271, by rfl⟩ : syracuseStep 1353695 = 2030543) B2030543
theorem B1353707 : Blo 900574 1353707 := bstep (se 1 (by rfl) ⟨1015280, by rfl⟩ : syracuseStep 1353707 = 2030561) B2030561
theorem B2566171 : Blo 900574 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B1353755 : Blo 900574 1353755 := bstep (se 1 (by rfl) ⟨1015316, by rfl⟩ : syracuseStep 1353755 = 2030633) B2030633
theorem B1714259 : Blo 900574 1714259 := bstep (se 1 (by rfl) ⟨1285694, by rfl⟩ : syracuseStep 1714259 = 2571389) B2571389
theorem B1714297 : Blo 900574 1714297 := bstep (se 2 (by rfl) ⟨642861, by rfl⟩ : syracuseStep 1714297 = 1285723) B1285723
theorem B7317695 : Blo 900574 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B4565321 : Blo 900574 4565321 := bstep (se 2 (by rfl) ⟨1711995, by rfl⟩ : syracuseStep 4565321 = 3423991) B3423991
theorem B1354121 : Blo 900574 1354121 := bstep (se 2 (by rfl) ⟨507795, by rfl⟩ : syracuseStep 1354121 = 1015591) B1015591
theorem B4565483 : Blo 900574 4565483 := bstep (se 1 (by rfl) ⟨3424112, by rfl⟩ : syracuseStep 4565483 = 6848225) B6848225
theorem B8235695 : Blo 900574 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B1355063 : Blo 900574 1355063 := bstep (se 1 (by rfl) ⟨1016297, by rfl⟩ : syracuseStep 1355063 = 2032595) B2032595
theorem B1355231 : Blo 900574 1355231 := bstep (se 1 (by rfl) ⟨1016423, by rfl⟩ : syracuseStep 1355231 = 2032847) B2032847
theorem B40054283 : Blo 900574 40054283 := bstep (se 1 (by rfl) ⟨30040712, by rfl⟩ : syracuseStep 40054283 = 60081425) B60081425
theorem B4566617 : Blo 900574 4566617 := bstep (se 2 (by rfl) ⟨1712481, by rfl⟩ : syracuseStep 4566617 = 3424963) B3424963
theorem B1355447 : Blo 900574 1355447 := bstep (se 1 (by rfl) ⟨1016585, by rfl⟩ : syracuseStep 1355447 = 2033171) B2033171
theorem B12365693 : Blo 900574 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B1355657 : Blo 900574 1355657 := bstep (se 2 (by rfl) ⟨508371, by rfl⟩ : syracuseStep 1355657 = 1016743) B1016743
theorem B1355903 : Blo 900574 1355903 := bstep (se 1 (by rfl) ⟨1016927, by rfl⟩ : syracuseStep 1355903 = 2033855) B2033855
theorem B9744907 : Blo 900574 9744907 := bstep (se 1 (by rfl) ⟨7308680, by rfl⟩ : syracuseStep 9744907 = 14617361) B14617361
theorem B34681445 : Blo 900574 34681445 := bstep (se 4 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 34681445 = 6502771) B6502771
theorem B4108907 : Blo 900574 4108907 := bstep (se 1 (by rfl) ⟨3081680, by rfl⟩ : syracuseStep 4108907 = 6163361) B6163361
theorem B66663085 : Blo 900574 66663085 := bstep (se 3 (by rfl) ⟨12499328, by rfl⟩ : syracuseStep 66663085 = 24998657) B24998657
theorem B1356539 : Blo 900574 1356539 := bstep (se 1 (by rfl) ⟨1017404, by rfl⟩ : syracuseStep 1356539 = 2034809) B2034809
theorem B37106545 : Blo 900574 37106545 := bstep (se 2 (by rfl) ⟨13914954, by rfl⟩ : syracuseStep 37106545 = 27829909) B27829909
theorem B1717129 : Blo 900574 1717129 := bstep (se 2 (by rfl) ⟨643923, by rfl⟩ : syracuseStep 1717129 = 1287847) B1287847
theorem B4338643 : Blo 900574 4338643 := bstep (se 1 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 4338643 = 6507965) B6507965
theorem B1520633 : Blo 900574 1520633 := bstep (se 2 (by rfl) ⟨570237, by rfl⟩ : syracuseStep 1520633 = 1140475) B1140475
theorem B1520903 : Blo 900574 1520903 := bstep (se 1 (by rfl) ⟨1140677, by rfl⟩ : syracuseStep 1520903 = 2281355) B2281355
theorem B3847823 : Blo 900574 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B4569047 : Blo 900574 4569047 := bstep (se 1 (by rfl) ⟨3426785, by rfl⟩ : syracuseStep 4569047 = 6853571) B6853571
theorem B1521895 : Blo 900574 1521895 := bstep (se 1 (by rfl) ⟨1141421, by rfl⟩ : syracuseStep 1521895 = 2282843) B2282843
theorem B4340411 : Blo 900574 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B15448967 : Blo 900574 15448967 := bstep (se 1 (by rfl) ⟨11586725, by rfl⟩ : syracuseStep 15448967 = 23173451) B23173451
theorem B4340717 : Blo 900574 4340717 := bstep (se 3 (by rfl) ⟨813884, by rfl⟩ : syracuseStep 4340717 = 1627769) B1627769
theorem B3423323 : Blo 900574 3423323 := bstep (se 1 (by rfl) ⟨2567492, by rfl⟩ : syracuseStep 3423323 = 5134985) B5134985
theorem B1522793 : Blo 900574 1522793 := bstep (se 2 (by rfl) ⟨571047, by rfl⟩ : syracuseStep 1522793 = 1142095) B1142095
theorem B5782907 : Blo 900574 5782907 := bstep (se 1 (by rfl) ⟨4337180, by rfl⟩ : syracuseStep 5782907 = 8674361) B8674361
theorem B900719 : Blo 900574 900719 := bstep (se 1 (by rfl) ⟨675539, by rfl⟩ : syracuseStep 900719 = 1351079) B1351079
theorem B900775 : Blo 900574 900775 := bstep (se 1 (by rfl) ⟨675581, by rfl⟩ : syracuseStep 900775 = 1351163) B1351163
theorem B900839 : Blo 900574 900839 := bstep (se 1 (by rfl) ⟨675629, by rfl⟩ : syracuseStep 900839 = 1351259) B1351259
theorem B900895 : Blo 900574 900895 := bstep (se 1 (by rfl) ⟨675671, by rfl⟩ : syracuseStep 900895 = 1351343) B1351343
theorem B900975 : Blo 900574 900975 := bstep (se 1 (by rfl) ⟨675731, by rfl⟩ : syracuseStep 900975 = 1351463) B1351463
theorem B901031 : Blo 900574 901031 := bstep (se 1 (by rfl) ⟨675773, by rfl⟩ : syracuseStep 901031 = 1351547) B1351547
theorem B1523623 : Blo 900574 1523623 := bstep (se 1 (by rfl) ⟨1142717, by rfl⟩ : syracuseStep 1523623 = 2285435) B2285435
theorem B3424295 : Blo 900574 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B5292071 : Blo 900574 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B901311 : Blo 900574 901311 := bstep (se 1 (by rfl) ⟨675983, by rfl⟩ : syracuseStep 901311 = 1351967) B1351967
theorem B901327 : Blo 900574 901327 := bstep (se 1 (by rfl) ⟨675995, by rfl⟩ : syracuseStep 901327 = 1351991) B1351991
theorem B17318123 : Blo 900574 17318123 := bstep (se 1 (by rfl) ⟨12988592, by rfl⟩ : syracuseStep 17318123 = 25977185) B25977185
theorem B1523947 : Blo 900574 1523947 := bstep (se 1 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 1523947 = 2285921) B2285921
theorem B3850487 : Blo 900574 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B901375 : Blo 900574 901375 := bstep (se 1 (by rfl) ⟨676031, by rfl⟩ : syracuseStep 901375 = 1352063) B1352063
theorem B901423 : Blo 900574 901423 := bstep (se 1 (by rfl) ⟨676067, by rfl⟩ : syracuseStep 901423 = 1352135) B1352135
theorem B901659 : Blo 900574 901659 := bstep (se 1 (by rfl) ⟨676244, by rfl⟩ : syracuseStep 901659 = 1352489) B1352489
theorem B901663 : Blo 900574 901663 := bstep (se 1 (by rfl) ⟨676247, by rfl⟩ : syracuseStep 901663 = 1352495) B1352495
theorem B901743 : Blo 900574 901743 := bstep (se 1 (by rfl) ⟨676307, by rfl⟩ : syracuseStep 901743 = 1352615) B1352615
theorem B901799 : Blo 900574 901799 := bstep (se 1 (by rfl) ⟨676349, by rfl⟩ : syracuseStep 901799 = 1352699) B1352699
theorem B901839 : Blo 900574 901839 := bstep (se 1 (by rfl) ⟨676379, by rfl⟩ : syracuseStep 901839 = 1352759) B1352759
theorem B901919 : Blo 900574 901919 := bstep (se 1 (by rfl) ⟨676439, by rfl⟩ : syracuseStep 901919 = 1352879) B1352879
theorem B3425267 : Blo 900574 3425267 := bstep (se 1 (by rfl) ⟨2568950, by rfl⟩ : syracuseStep 3425267 = 5137901) B5137901
theorem B902191 : Blo 900574 902191 := bstep (se 1 (by rfl) ⟨676643, by rfl⟩ : syracuseStep 902191 = 1353287) B1353287
theorem B902255 : Blo 900574 902255 := bstep (se 1 (by rfl) ⟨676691, by rfl⟩ : syracuseStep 902255 = 1353383) B1353383
theorem B902311 : Blo 900574 902311 := bstep (se 1 (by rfl) ⟨676733, by rfl⟩ : syracuseStep 902311 = 1353467) B1353467
theorem B902335 : Blo 900574 902335 := bstep (se 1 (by rfl) ⟨676751, by rfl⟩ : syracuseStep 902335 = 1353503) B1353503
theorem B902367 : Blo 900574 902367 := bstep (se 1 (by rfl) ⟨676775, by rfl⟩ : syracuseStep 902367 = 1353551) B1353551
theorem B8242411 : Blo 900574 8242411 := bstep (se 1 (by rfl) ⟨6181808, by rfl⟩ : syracuseStep 8242411 = 12363617) B12363617
theorem B902447 : Blo 900574 902447 := bstep (se 1 (by rfl) ⟨676835, by rfl⟩ : syracuseStep 902447 = 1353671) B1353671
theorem B5555561 : Blo 900574 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B4343177 : Blo 900574 4343177 := bstep (se 2 (by rfl) ⟨1628691, by rfl⟩ : syracuseStep 4343177 = 3257383) B3257383
theorem B3425723 : Blo 900574 3425723 := bstep (se 1 (by rfl) ⟨2569292, by rfl⟩ : syracuseStep 3425723 = 5138585) B5138585
theorem B1525243 : Blo 900574 1525243 := bstep (se 1 (by rfl) ⟨1143932, by rfl⟩ : syracuseStep 1525243 = 2287865) B2287865
theorem B902683 : Blo 900574 902683 := bstep (se 1 (by rfl) ⟨677012, by rfl⟩ : syracuseStep 902683 = 1354025) B1354025
theorem B902687 : Blo 900574 902687 := bstep (se 1 (by rfl) ⟨677015, by rfl⟩ : syracuseStep 902687 = 1354031) B1354031
theorem B902847 : Blo 900574 902847 := bstep (se 1 (by rfl) ⟨677135, by rfl⟩ : syracuseStep 902847 = 1354271) B1354271
theorem B1525439 : Blo 900574 1525439 := bstep (se 1 (by rfl) ⟨1144079, by rfl⟩ : syracuseStep 1525439 = 2288159) B2288159
theorem B10274525 : Blo 900574 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B903103 : Blo 900574 903103 := bstep (se 1 (by rfl) ⟨677327, by rfl⟩ : syracuseStep 903103 = 1354655) B1354655
theorem B903135 : Blo 900574 903135 := bstep (se 1 (by rfl) ⟨677351, by rfl⟩ : syracuseStep 903135 = 1354703) B1354703
theorem B903195 : Blo 900574 903195 := bstep (se 1 (by rfl) ⟨677396, by rfl⟩ : syracuseStep 903195 = 1354793) B1354793
theorem B903199 : Blo 900574 903199 := bstep (se 1 (by rfl) ⟨677399, by rfl⟩ : syracuseStep 903199 = 1354799) B1354799
theorem B903215 : Blo 900574 903215 := bstep (se 1 (by rfl) ⟨677411, by rfl⟩ : syracuseStep 903215 = 1354823) B1354823
theorem B2279623 : Blo 900574 2279623 := bstep (se 1 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 2279623 = 3419435) B3419435
theorem B903391 : Blo 900574 903391 := bstep (se 1 (by rfl) ⟨677543, by rfl⟩ : syracuseStep 903391 = 1355087) B1355087
theorem B903451 : Blo 900574 903451 := bstep (se 1 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 903451 = 1355177) B1355177
theorem B4114745 : Blo 900574 4114745 := bstep (se 2 (by rfl) ⟨1543029, by rfl⟩ : syracuseStep 4114745 = 3086059) B3086059
theorem B903551 : Blo 900574 903551 := bstep (se 1 (by rfl) ⟨677663, by rfl⟩ : syracuseStep 903551 = 1355327) B1355327
theorem B903727 : Blo 900574 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B903783 : Blo 900574 903783 := bstep (se 1 (by rfl) ⟨677837, by rfl⟩ : syracuseStep 903783 = 1355675) B1355675
theorem B3295865 : Blo 900574 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B904159 : Blo 900574 904159 := bstep (se 1 (by rfl) ⟨678119, by rfl⟩ : syracuseStep 904159 = 1356239) B1356239
theorem B904187 : Blo 900574 904187 := bstep (se 1 (by rfl) ⟨678140, by rfl⟩ : syracuseStep 904187 = 1356281) B1356281
theorem B904255 : Blo 900574 904255 := bstep (se 1 (by rfl) ⟨678191, by rfl⟩ : syracuseStep 904255 = 1356383) B1356383
theorem B2116819 : Blo 900574 2116819 := bstep (se 1 (by rfl) ⟨1587614, by rfl⟩ : syracuseStep 2116819 = 3175229) B3175229
theorem B9260477 : Blo 900574 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B6868637 : Blo 900574 6868637 := bstep (se 3 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 6868637 = 2575739) B2575739
theorem B6508307 : Blo 900574 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B2281567 : Blo 900574 2281567 := bstep (se 1 (by rfl) ⟨1711175, by rfl⟩ : syracuseStep 2281567 = 3422351) B3422351
theorem B4346237 : Blo 900574 4346237 := bstep (se 3 (by rfl) ⟨814919, by rfl⟩ : syracuseStep 4346237 = 1629839) B1629839
theorem B2282651 : Blo 900574 2282651 := bstep (se 1 (by rfl) ⟨1711988, by rfl⟩ : syracuseStep 2282651 = 3423977) B3423977
theorem B3855613 : Blo 900574 3855613 := bstep (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) B1445855
theorem B3855887 : Blo 900574 3855887 := bstep (se 1 (by rfl) ⟨2891915, by rfl⟩ : syracuseStep 3855887 = 5783831) B5783831
theorem B8673095 : Blo 900574 8673095 := bstep (se 1 (by rfl) ⟨6504821, by rfl⟩ : syracuseStep 8673095 = 13009643) B13009643
theorem B6510905 : Blo 900574 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B12376637 : Blo 900574 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B4578119 : Blo 900574 4578119 := bstep (se 1 (by rfl) ⟨3433589, by rfl⟩ : syracuseStep 4578119 = 6867179) B6867179
theorem B169335755 : Blo 900574 169335755 := bstep (se 1 (by rfl) ⟨127001816, by rfl⟩ : syracuseStep 169335755 = 254003633) B254003633
theorem B29678561 : Blo 900574 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B5791085 : Blo 900574 5791085 := bstep (se 3 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 5791085 = 2171657) B2171657
theorem B3858263 : Blo 900574 3858263 := bstep (se 1 (by rfl) ⟨2893697, by rfl⟩ : syracuseStep 3858263 = 5787395) B5787395
theorem B4120475 : Blo 900574 4120475 := bstep (se 1 (by rfl) ⟨3090356, by rfl⟩ : syracuseStep 4120475 = 6180713) B6180713
theorem B1466623 : Blo 900574 1466623 := bstep (se 1 (by rfl) ⟨1099967, by rfl⟩ : syracuseStep 1466623 = 2199935) B2199935
theorem B1925851 : Blo 900574 1925851 := bstep (se 1 (by rfl) ⟨1444388, by rfl⟩ : syracuseStep 1925851 = 2888777) B2888777
theorem B3433225 : Blo 900574 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B11134199 : Blo 900574 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B3859987 : Blo 900574 3859987 := bstep (se 1 (by rfl) ⟨2894990, by rfl⟩ : syracuseStep 3859987 = 5789981) B5789981
theorem B6841907 : Blo 900574 6841907 := bstep (se 1 (by rfl) ⟨5131430, by rfl⟩ : syracuseStep 6841907 = 10262861) B10262861
theorem B2287379 : Blo 900574 2287379 := bstep (se 1 (by rfl) ⟨1715534, by rfl⟩ : syracuseStep 2287379 = 3431069) B3431069
theorem B1370233 : Blo 900574 1370233 := bstep (se 2 (by rfl) ⟨513837, by rfl⟩ : syracuseStep 1370233 = 1027675) B1027675
theorem B3467387 : Blo 900574 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B27781325 : Blo 900574 27781325 := bstep (se 3 (by rfl) ⟨5208998, by rfl⟩ : syracuseStep 27781325 = 10417997) B10417997
theorem B8808887 : Blo 900574 8808887 := bstep (se 1 (by rfl) ⟨6606665, by rfl⟩ : syracuseStep 8808887 = 13213331) B13213331
theorem B56421305 : Blo 900574 56421305 := bstep (se 2 (by rfl) ⟨21157989, by rfl⟩ : syracuseStep 56421305 = 42315979) B42315979
theorem B2026907 : Blo 900574 2026907 := bstep (se 1 (by rfl) ⟨1520180, by rfl⟩ : syracuseStep 2026907 = 3040361) B3040361
theorem B2059847 : Blo 900574 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B151973597 : Blo 900574 151973597 := bstep (se 3 (by rfl) ⟨28495049, by rfl⟩ : syracuseStep 151973597 = 56990099) B56990099
theorem B5795671 : Blo 900574 5795671 := bstep (se 1 (by rfl) ⟨4346753, by rfl⟩ : syracuseStep 5795671 = 8693507) B8693507
theorem B2027483 : Blo 900574 2027483 := bstep (se 1 (by rfl) ⟨1520612, by rfl⟩ : syracuseStep 2027483 = 3041225) B3041225
theorem B2027663 : Blo 900574 2027663 := bstep (se 1 (by rfl) ⟨1520747, by rfl⟩ : syracuseStep 2027663 = 3041495) B3041495
theorem B2027753 : Blo 900574 2027753 := bstep (se 2 (by rfl) ⟨760407, by rfl⟩ : syracuseStep 2027753 = 1520815) B1520815
theorem B2027879 : Blo 900574 2027879 := bstep (se 1 (by rfl) ⟨1520909, by rfl⟩ : syracuseStep 2027879 = 3041819) B3041819
theorem B14610937 : Blo 900574 14610937 := bstep (se 2 (by rfl) ⟨5479101, by rfl⟩ : syracuseStep 14610937 = 10958203) B10958203
theorem B11563559 : Blo 900574 11563559 := bstep (se 1 (by rfl) ⟨8672669, by rfl⟩ : syracuseStep 11563559 = 17345339) B17345339
theorem B914267 : Blo 900574 914267 := bstep (se 1 (by rfl) ⟨685700, by rfl⟩ : syracuseStep 914267 = 1371401) B1371401
theorem B2028455 : Blo 900574 2028455 := bstep (se 1 (by rfl) ⟨1521341, by rfl⟩ : syracuseStep 2028455 = 3042683) B3042683
theorem B13038529 : Blo 900574 13038529 := bstep (se 2 (by rfl) ⟨4889448, by rfl⟩ : syracuseStep 13038529 = 9778897) B9778897
theorem B7697693 : Blo 900574 7697693 := bstep (se 3 (by rfl) ⟨1443317, by rfl⟩ : syracuseStep 7697693 = 2886635) B2886635
theorem B15431471 : Blo 900574 15431471 := bstep (se 1 (by rfl) ⟨11573603, by rfl⟩ : syracuseStep 15431471 = 23147207) B23147207
theorem B1013575 : Blo 900574 1013575 := bstep (se 1 (by rfl) ⟨760181, by rfl⟩ : syracuseStep 1013575 = 1520363) B1520363
theorem B2029391 : Blo 900574 2029391 := bstep (se 1 (by rfl) ⟨1522043, by rfl⟩ : syracuseStep 2029391 = 3044087) B3044087
theorem B1931087 : Blo 900574 1931087 := bstep (se 1 (by rfl) ⟨1448315, by rfl⟩ : syracuseStep 1931087 = 2896631) B2896631
theorem B2029751 : Blo 900574 2029751 := bstep (se 1 (by rfl) ⟨1522313, by rfl⟩ : syracuseStep 2029751 = 3044627) B3044627
theorem B1931455 : Blo 900574 1931455 := bstep (se 1 (by rfl) ⟨1448591, by rfl⟩ : syracuseStep 1931455 = 2897183) B2897183
theorem B6846767 : Blo 900574 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B5142959 : Blo 900574 5142959 := bstep (se 1 (by rfl) ⟨3857219, by rfl⟩ : syracuseStep 5142959 = 7714439) B7714439
theorem B1014223 : Blo 900574 1014223 := bstep (se 1 (by rfl) ⟨760667, by rfl⟩ : syracuseStep 1014223 = 1521335) B1521335
theorem B2030111 : Blo 900574 2030111 := bstep (se 1 (by rfl) ⟨1522583, by rfl⟩ : syracuseStep 2030111 = 3045167) B3045167
theorem B2030345 : Blo 900574 2030345 := bstep (se 2 (by rfl) ⟨761379, by rfl⟩ : syracuseStep 2030345 = 1522759) B1522759
theorem B3046301 : Blo 900574 3046301 := bstep (se 3 (by rfl) ⟨571181, by rfl⟩ : syracuseStep 3046301 = 1142363) B1142363
theorem B19758275 : Blo 900574 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1015015 : Blo 900574 1015015 := bstep (se 1 (by rfl) ⟨761261, by rfl⟩ : syracuseStep 1015015 = 1522523) B1522523
theorem B2030921 : Blo 900574 2030921 := bstep (se 2 (by rfl) ⟨761595, by rfl⟩ : syracuseStep 2030921 = 1523191) B1523191
theorem B9273041 : Blo 900574 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B2031335 : Blo 900574 2031335 := bstep (se 1 (by rfl) ⟨1523501, by rfl⟩ : syracuseStep 2031335 = 3047003) B3047003
theorem B1015663 : Blo 900574 1015663 := bstep (se 1 (by rfl) ⟨761747, by rfl⟩ : syracuseStep 1015663 = 1523495) B1523495
theorem B2031929 : Blo 900574 2031929 := bstep (se 2 (by rfl) ⟨761973, by rfl⟩ : syracuseStep 2031929 = 1523947) B1523947
theorem B1442767 : Blo 900574 1442767 := bstep (se 1 (by rfl) ⟨1082075, by rfl⟩ : syracuseStep 1442767 = 2164151) B2164151
theorem B1016959 : Blo 900574 1016959 := bstep (se 1 (by rfl) ⟨762719, by rfl⟩ : syracuseStep 1016959 = 1525439) B1525439
theorem B6849683 : Blo 900574 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B2885291 : Blo 900574 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B2197243 : Blo 900574 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B2033657 : Blo 900574 2033657 := bstep (se 2 (by rfl) ⟨762621, by rfl⟩ : syracuseStep 2033657 = 1525243) B1525243
theorem B5146649 : Blo 900574 5146649 := bstep (se 2 (by rfl) ⟨1929993, by rfl⟩ : syracuseStep 5146649 = 3859987) B3859987
theorem B2033747 : Blo 900574 2033747 := bstep (se 1 (by rfl) ⟨1525310, by rfl⟩ : syracuseStep 2033747 = 3050621) B3050621
theorem B4393223 : Blo 900574 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B2033927 : Blo 900574 2033927 := bstep (se 1 (by rfl) ⟨1525445, by rfl⟩ : syracuseStep 2033927 = 3050891) B3050891
theorem B5212441 : Blo 900574 5212441 := bstep (se 2 (by rfl) ⟨1954665, by rfl⟩ : syracuseStep 5212441 = 3909331) B3909331
theorem B4327955 : Blo 900574 4327955 := bstep (se 1 (by rfl) ⟨3245966, by rfl⟩ : syracuseStep 4327955 = 6491933) B6491933
theorem B17370247 : Blo 900574 17370247 := bstep (se 1 (by rfl) ⟨13027685, by rfl⟩ : syracuseStep 17370247 = 26055371) B26055371
theorem B1445177 : Blo 900574 1445177 := bstep (se 2 (by rfl) ⟨541941, by rfl⟩ : syracuseStep 1445177 = 1083883) B1083883
theorem B14814829 : Blo 900574 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B5771425 : Blo 900574 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B3052079 : Blo 900574 3052079 := bstep (se 1 (by rfl) ⟨2289059, by rfl⟩ : syracuseStep 3052079 = 4578119) B4578119
theorem B112890503 : Blo 900574 112890503 := bstep (se 1 (by rfl) ⟨84667877, by rfl⟩ : syracuseStep 112890503 = 169335755) B169335755
theorem B5149565 : Blo 900574 5149565 := bstep (se 3 (by rfl) ⟨965543, by rfl⟩ : syracuseStep 5149565 = 1931087) B1931087
theorem B1448047 : Blo 900574 1448047 := bstep (se 1 (by rfl) ⟨1086035, by rfl⟩ : syracuseStep 1448047 = 2172071) B2172071
theorem B3479699 : Blo 900574 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B4561271 : Blo 900574 4561271 := bstep (se 1 (by rfl) ⟨3420953, by rfl⟩ : syracuseStep 4561271 = 6841907) B6841907
theorem B1448489 : Blo 900574 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B1448713 : Blo 900574 1448713 := bstep (se 2 (by rfl) ⟨543267, by rfl⟩ : syracuseStep 1448713 = 1086535) B1086535
theorem B18520883 : Blo 900574 18520883 := bstep (se 1 (by rfl) ⟨13890662, by rfl⟩ : syracuseStep 18520883 = 27781325) B27781325
theorem B5872591 : Blo 900574 5872591 := bstep (se 1 (by rfl) ⟨4404443, by rfl⟩ : syracuseStep 5872591 = 8808887) B8808887
theorem B21961853 : Blo 900574 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B1351271 : Blo 900574 1351271 := bstep (se 1 (by rfl) ⟨1013453, by rfl⟩ : syracuseStep 1351271 = 2026907) B2026907
theorem B1351433 : Blo 900574 1351433 := bstep (se 2 (by rfl) ⟨506787, by rfl⟩ : syracuseStep 1351433 = 1013575) B1013575
theorem B1351655 : Blo 900574 1351655 := bstep (se 1 (by rfl) ⟨1013741, by rfl⟩ : syracuseStep 1351655 = 2027483) B2027483
theorem B1351775 : Blo 900574 1351775 := bstep (se 1 (by rfl) ⟨1013831, by rfl⟩ : syracuseStep 1351775 = 2027663) B2027663
theorem B1351835 : Blo 900574 1351835 := bstep (se 1 (by rfl) ⟨1013876, by rfl⟩ : syracuseStep 1351835 = 2027753) B2027753
theorem B1351919 : Blo 900574 1351919 := bstep (se 1 (by rfl) ⟨1013939, by rfl⟩ : syracuseStep 1351919 = 2027879) B2027879
theorem B7709039 : Blo 900574 7709039 := bstep (se 1 (by rfl) ⟨5781779, by rfl⟩ : syracuseStep 7709039 = 11563559) B11563559
theorem B1352297 : Blo 900574 1352297 := bstep (se 2 (by rfl) ⟨507111, by rfl⟩ : syracuseStep 1352297 = 1014223) B1014223
theorem B1352303 : Blo 900574 1352303 := bstep (se 1 (by rfl) ⟨1014227, by rfl⟩ : syracuseStep 1352303 = 2028455) B2028455
theorem B2565215 : Blo 900574 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B1352927 : Blo 900574 1352927 := bstep (se 1 (by rfl) ⟨1014695, by rfl⟩ : syracuseStep 1352927 = 2029391) B2029391
theorem B1353167 : Blo 900574 1353167 := bstep (se 1 (by rfl) ⟨1014875, by rfl⟩ : syracuseStep 1353167 = 2029751) B2029751
theorem B4564511 : Blo 900574 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B1353353 : Blo 900574 1353353 := bstep (se 2 (by rfl) ⟨507507, by rfl⟩ : syracuseStep 1353353 = 1015015) B1015015
theorem B1353407 : Blo 900574 1353407 := bstep (se 1 (by rfl) ⟨1015055, by rfl⟩ : syracuseStep 1353407 = 2030111) B2030111
theorem B2893607 : Blo 900574 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B1353563 : Blo 900574 1353563 := bstep (se 1 (by rfl) ⟨1015172, by rfl⟩ : syracuseStep 1353563 = 2030345) B2030345
theorem B10299311 : Blo 900574 10299311 := bstep (se 1 (by rfl) ⟨7724483, by rfl⟩ : syracuseStep 10299311 = 15448967) B15448967
theorem B2893811 : Blo 900574 2893811 := bstep (se 1 (by rfl) ⟨2170358, by rfl⟩ : syracuseStep 2893811 = 4340717) B4340717
theorem B1353947 : Blo 900574 1353947 := bstep (se 1 (by rfl) ⟨1015460, by rfl⟩ : syracuseStep 1353947 = 2030921) B2030921
theorem B10987933 : Blo 900574 10987933 := bstep (se 3 (by rfl) ⟨2060237, by rfl⟩ : syracuseStep 10987933 = 4120475) B4120475
theorem B1354217 : Blo 900574 1354217 := bstep (se 2 (by rfl) ⟨507831, by rfl⟩ : syracuseStep 1354217 = 1015663) B1015663
theorem B1354223 : Blo 900574 1354223 := bstep (se 1 (by rfl) ⟨1015667, by rfl⟩ : syracuseStep 1354223 = 2031335) B2031335
theorem B1354535 : Blo 900574 1354535 := bstep (se 1 (by rfl) ⟨1015901, by rfl⟩ : syracuseStep 1354535 = 2031803) B2031803
theorem B11545415 : Blo 900574 11545415 := bstep (se 1 (by rfl) ⟨8659061, by rfl⟩ : syracuseStep 11545415 = 17318123) B17318123
theorem B2566991 : Blo 900574 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B1354607 : Blo 900574 1354607 := bstep (se 1 (by rfl) ⟨1015955, by rfl⟩ : syracuseStep 1354607 = 2031911) B2031911
theorem B1354859 : Blo 900574 1354859 := bstep (se 1 (by rfl) ⟨1016144, by rfl⟩ : syracuseStep 1354859 = 2032289) B2032289
theorem B1355099 : Blo 900574 1355099 := bstep (se 1 (by rfl) ⟨1016324, by rfl⟩ : syracuseStep 1355099 = 2032649) B2032649
theorem B1355129 : Blo 900574 1355129 := bstep (se 2 (by rfl) ⟨508173, by rfl⟩ : syracuseStep 1355129 = 1016347) B1016347
theorem B1355135 : Blo 900574 1355135 := bstep (se 1 (by rfl) ⟨1016351, by rfl⟩ : syracuseStep 1355135 = 2032703) B2032703
theorem B1355369 : Blo 900574 1355369 := bstep (se 2 (by rfl) ⟨508263, by rfl⟩ : syracuseStep 1355369 = 1016527) B1016527
theorem B2567801 : Blo 900574 2567801 := bstep (se 2 (by rfl) ⟨962925, by rfl⟩ : syracuseStep 2567801 = 1925851) B1925851
theorem B4337489 : Blo 900574 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B1355759 : Blo 900574 1355759 := bstep (se 1 (by rfl) ⟨1016819, by rfl⟩ : syracuseStep 1355759 = 2033639) B2033639
theorem B1355879 : Blo 900574 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B1716385 : Blo 900574 1716385 := bstep (se 2 (by rfl) ⟨643644, by rfl⟩ : syracuseStep 1716385 = 1287289) B1287289
theorem B1355999 : Blo 900574 1355999 := bstep (se 1 (by rfl) ⟨1016999, by rfl⟩ : syracuseStep 1355999 = 2033999) B2033999
theorem B1356059 : Blo 900574 1356059 := bstep (se 1 (by rfl) ⟨1017044, by rfl⟩ : syracuseStep 1356059 = 2034089) B2034089
theorem B10989881 : Blo 900574 10989881 := bstep (se 2 (by rfl) ⟨4121205, by rfl⟩ : syracuseStep 10989881 = 8242411) B8242411
theorem B1356455 : Blo 900574 1356455 := bstep (se 1 (by rfl) ⟨1017341, by rfl⟩ : syracuseStep 1356455 = 2034683) B2034683
theorem B1356575 : Blo 900574 1356575 := bstep (se 1 (by rfl) ⟨1017431, by rfl⟩ : syracuseStep 1356575 = 2034863) B2034863
theorem B1356599 : Blo 900574 1356599 := bstep (se 1 (by rfl) ⟨1017449, by rfl⟩ : syracuseStep 1356599 = 2034899) B2034899
theorem B2438045 : Blo 900574 2438045 := bstep (se 3 (by rfl) ⟨457133, by rfl⟩ : syracuseStep 2438045 = 914267) B914267
theorem B1356713 : Blo 900574 1356713 := bstep (se 2 (by rfl) ⟨508767, by rfl⟩ : syracuseStep 1356713 = 1017535) B1017535
theorem B6173651 : Blo 900574 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B1356779 : Blo 900574 1356779 := bstep (se 1 (by rfl) ⟨1017584, by rfl⟩ : syracuseStep 1356779 = 2035169) B2035169
theorem B3257327 : Blo 900574 3257327 := bstep (se 1 (by rfl) ⟨2442995, by rfl⟩ : syracuseStep 3257327 = 4885991) B4885991
theorem B6861833 : Blo 900574 6861833 := bstep (se 2 (by rfl) ⟨2573187, by rfl⟩ : syracuseStep 6861833 = 5146375) B5146375
theorem B3421561 : Blo 900574 3421561 := bstep (se 2 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 3421561 = 2566171) B2566171
theorem B2897491 : Blo 900574 2897491 := bstep (se 1 (by rfl) ⟨2173118, by rfl⟩ : syracuseStep 2897491 = 4346237) B4346237
theorem B3258251 : Blo 900574 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B1521767 : Blo 900574 1521767 := bstep (se 1 (by rfl) ⟨1141325, by rfl⟩ : syracuseStep 1521767 = 2282651) B2282651
theorem B5486887 : Blo 900574 5486887 := bstep (se 1 (by rfl) ⟨4115165, by rfl⟩ : syracuseStep 5486887 = 8230331) B8230331
theorem B2570591 : Blo 900574 2570591 := bstep (se 1 (by rfl) ⟨1927943, by rfl⟩ : syracuseStep 2570591 = 3855887) B3855887
theorem B11581805 : Blo 900574 11581805 := bstep (se 3 (by rfl) ⟨2171588, by rfl⟩ : syracuseStep 11581805 = 4343177) B4343177
theorem B5782063 : Blo 900574 5782063 := bstep (se 1 (by rfl) ⟨4336547, by rfl⟩ : syracuseStep 5782063 = 8673095) B8673095
theorem B17349335 : Blo 900574 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B4340603 : Blo 900574 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B6863777 : Blo 900574 6863777 := bstep (se 2 (by rfl) ⟨2573916, by rfl⟩ : syracuseStep 6863777 = 5147833) B5147833
theorem B4570343 : Blo 900574 4570343 := bstep (se 1 (by rfl) ⟨3427757, by rfl⟩ : syracuseStep 4570343 = 6855515) B6855515
theorem B3849515 : Blo 900574 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B21937513 : Blo 900574 21937513 := bstep (se 2 (by rfl) ⟨8226567, by rfl⟩ : syracuseStep 21937513 = 16453135) B16453135
theorem B900575 : Blo 900574 900575 := bstep (se 1 (by rfl) ⟨675431, by rfl⟩ : syracuseStep 900575 = 1350863) B1350863
theorem B900655 : Blo 900574 900655 := bstep (se 1 (by rfl) ⟨675491, by rfl⟩ : syracuseStep 900655 = 1350983) B1350983
theorem B900763 : Blo 900574 900763 := bstep (se 1 (by rfl) ⟨675572, by rfl⟩ : syracuseStep 900763 = 1351145) B1351145
theorem B1097371 : Blo 900574 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B900859 : Blo 900574 900859 := bstep (se 1 (by rfl) ⟨675644, by rfl⟩ : syracuseStep 900859 = 1351289) B1351289
theorem B2572175 : Blo 900574 2572175 := bstep (se 1 (by rfl) ⟨1929131, by rfl⟩ : syracuseStep 2572175 = 3858263) B3858263
theorem B901023 : Blo 900574 901023 := bstep (se 1 (by rfl) ⟨675767, by rfl⟩ : syracuseStep 901023 = 1351535) B1351535
theorem B14860273 : Blo 900574 14860273 := bstep (se 2 (by rfl) ⟨5572602, by rfl⟩ : syracuseStep 14860273 = 11145205) B11145205
theorem B9879617 : Blo 900574 9879617 := bstep (se 2 (by rfl) ⟨3704856, by rfl⟩ : syracuseStep 9879617 = 7409713) B7409713
theorem B901479 : Blo 900574 901479 := bstep (se 1 (by rfl) ⟨676109, by rfl⟩ : syracuseStep 901479 = 1352219) B1352219
theorem B901599 : Blo 900574 901599 := bstep (se 1 (by rfl) ⟨676199, by rfl⟩ : syracuseStep 901599 = 1352399) B1352399
theorem B901607 : Blo 900574 901607 := bstep (se 1 (by rfl) ⟨676205, by rfl⟩ : syracuseStep 901607 = 1352411) B1352411
theorem B19481249 : Blo 900574 19481249 := bstep (se 2 (by rfl) ⟨7305468, by rfl⟩ : syracuseStep 19481249 = 14610937) B14610937
theorem B12993209 : Blo 900574 12993209 := bstep (se 2 (by rfl) ⟨4872453, by rfl⟩ : syracuseStep 12993209 = 9744907) B9744907
theorem B901883 : Blo 900574 901883 := bstep (se 1 (by rfl) ⟨676412, by rfl⟩ : syracuseStep 901883 = 1352825) B1352825
theorem B8667901 : Blo 900574 8667901 := bstep (se 3 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 8667901 = 3250463) B3250463
theorem B7422799 : Blo 900574 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B88884113 : Blo 900574 88884113 := bstep (se 2 (by rfl) ⟨33331542, by rfl⟩ : syracuseStep 88884113 = 66663085) B66663085
theorem B7717787 : Blo 900574 7717787 := bstep (se 1 (by rfl) ⟨5788340, by rfl⟩ : syracuseStep 7717787 = 11576681) B11576681
theorem B11289701 : Blo 900574 11289701 := bstep (se 4 (by rfl) ⟨1058409, by rfl⟩ : syracuseStep 11289701 = 2116819) B2116819
theorem B1524919 : Blo 900574 1524919 := bstep (se 1 (by rfl) ⟨1143689, by rfl⟩ : syracuseStep 1524919 = 2287379) B2287379
theorem B17384705 : Blo 900574 17384705 := bstep (se 2 (by rfl) ⟨6519264, by rfl⟩ : syracuseStep 17384705 = 13038529) B13038529
theorem B5784857 : Blo 900574 5784857 := bstep (se 2 (by rfl) ⟨2169321, by rfl⟩ : syracuseStep 5784857 = 4338643) B4338643
theorem B902463 : Blo 900574 902463 := bstep (se 1 (by rfl) ⟨676847, by rfl⟩ : syracuseStep 902463 = 1353695) B1353695
theorem B902471 : Blo 900574 902471 := bstep (se 1 (by rfl) ⟨676853, by rfl⟩ : syracuseStep 902471 = 1353707) B1353707
theorem B902503 : Blo 900574 902503 := bstep (se 1 (by rfl) ⟨676877, by rfl⟩ : syracuseStep 902503 = 1353755) B1353755
theorem B2311591 : Blo 900574 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B902747 : Blo 900574 902747 := bstep (se 1 (by rfl) ⟨677060, by rfl⟩ : syracuseStep 902747 = 1354121) B1354121
theorem B903375 : Blo 900574 903375 := bstep (se 1 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 903375 = 1355063) B1355063
theorem B903487 : Blo 900574 903487 := bstep (se 1 (by rfl) ⟨677615, by rfl⟩ : syracuseStep 903487 = 1355231) B1355231
theorem B903631 : Blo 900574 903631 := bstep (se 1 (by rfl) ⟨677723, by rfl⟩ : syracuseStep 903631 = 1355447) B1355447
theorem B8243795 : Blo 900574 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B903771 : Blo 900574 903771 := bstep (se 1 (by rfl) ⟨677828, by rfl⟩ : syracuseStep 903771 = 1355657) B1355657
theorem B903935 : Blo 900574 903935 := bstep (se 1 (by rfl) ⟨677951, by rfl⟩ : syracuseStep 903935 = 1355903) B1355903
theorem B2575273 : Blo 900574 2575273 := bstep (se 2 (by rfl) ⟨965727, by rfl⟩ : syracuseStep 2575273 = 1931455) B1931455
theorem B23120963 : Blo 900574 23120963 := bstep (se 1 (by rfl) ⟨17340722, by rfl⟩ : syracuseStep 23120963 = 34681445) B34681445
theorem B2739271 : Blo 900574 2739271 := bstep (se 1 (by rfl) ⟨2054453, by rfl⟩ : syracuseStep 2739271 = 4108907) B4108907
theorem B904359 : Blo 900574 904359 := bstep (se 1 (by rfl) ⟨678269, by rfl⟩ : syracuseStep 904359 = 1356539) B1356539
theorem B5131795 : Blo 900574 5131795 := bstep (se 1 (by rfl) ⟨3848846, by rfl⟩ : syracuseStep 5131795 = 7697693) B7697693
theorem B13160537 : Blo 900574 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B3428639 : Blo 900574 3428639 := bstep (se 1 (by rfl) ⟨2571479, by rfl⟩ : syracuseStep 3428639 = 5142959) B5142959
theorem B405262925 : Blo 900574 405262925 := bstep (se 3 (by rfl) ⟨75986798, by rfl⟩ : syracuseStep 405262925 = 151973597) B151973597
theorem B17355485 : Blo 900574 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B2282215 : Blo 900574 2282215 := bstep (se 1 (by rfl) ⟨1711661, by rfl⟩ : syracuseStep 2282215 = 3423323) B3423323
theorem B2282377 : Blo 900574 2282377 := bstep (se 2 (by rfl) ⟨855891, by rfl⟩ : syracuseStep 2282377 = 1711783) B1711783
theorem B3855271 : Blo 900574 3855271 := bstep (se 1 (by rfl) ⟨2891453, by rfl⟩ : syracuseStep 3855271 = 5782907) B5782907
theorem B6182027 : Blo 900574 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B2282863 : Blo 900574 2282863 := bstep (se 1 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 2282863 = 3424295) B3424295
theorem B3528047 : Blo 900574 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B1955497 : Blo 900574 1955497 := bstep (se 2 (by rfl) ⟨733311, by rfl⟩ : syracuseStep 1955497 = 1466623) B1466623
theorem B2283511 : Blo 900574 2283511 := bstep (se 1 (by rfl) ⟨1712633, by rfl⟩ : syracuseStep 2283511 = 3425267) B3425267
theorem B2283815 : Blo 900574 2283815 := bstep (se 1 (by rfl) ⟨1712861, by rfl⟩ : syracuseStep 2283815 = 3425723) B3425723
theorem B4577633 : Blo 900574 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B5134711 : Blo 900574 5134711 := bstep (se 1 (by rfl) ⟨3851033, by rfl⟩ : syracuseStep 5134711 = 7702067) B7702067
theorem B3430795 : Blo 900574 3430795 := bstep (se 1 (by rfl) ⟨2573096, by rfl⟩ : syracuseStep 3430795 = 5146193) B5146193
theorem B2743163 : Blo 900574 2743163 := bstep (se 1 (by rfl) ⟨2057372, by rfl⟩ : syracuseStep 2743163 = 4114745) B4114745
theorem B15392105 : Blo 900574 15392105 := bstep (se 2 (by rfl) ⟨5772039, by rfl⟩ : syracuseStep 15392105 = 11544079) B11544079
theorem B4579091 : Blo 900574 4579091 := bstep (se 1 (by rfl) ⟨3434318, by rfl⟩ : syracuseStep 4579091 = 6868637) B6868637
theorem B19488599 : Blo 900574 19488599 := bstep (se 1 (by rfl) ⟨14616449, by rfl⟩ : syracuseStep 19488599 = 29232899) B29232899
theorem B1826977 : Blo 900574 1826977 := bstep (se 2 (by rfl) ⟨685116, by rfl⟩ : syracuseStep 1826977 = 1370233) B1370233
theorem B2285729 : Blo 900574 2285729 := bstep (se 2 (by rfl) ⟨857148, by rfl⟩ : syracuseStep 2285729 = 1714297) B1714297
theorem B3039497 : Blo 900574 3039497 := bstep (se 2 (by rfl) ⟨1139811, by rfl⟩ : syracuseStep 3039497 = 2279623) B2279623
theorem B5792543 : Blo 900574 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B8251091 : Blo 900574 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B4876199 : Blo 900574 4876199 := bstep (se 1 (by rfl) ⟨3657149, by rfl⟩ : syracuseStep 4876199 = 7314299) B7314299
theorem B19785707 : Blo 900574 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B3860723 : Blo 900574 3860723 := bstep (se 1 (by rfl) ⟨2895542, by rfl⟩ : syracuseStep 3860723 = 5791085) B5791085
theorem B7727561 : Blo 900574 7727561 := bstep (se 2 (by rfl) ⟨2897835, by rfl⟩ : syracuseStep 7727561 = 5795671) B5795671
theorem B3042035 : Blo 900574 3042035 := bstep (se 1 (by rfl) ⟨2281526, by rfl⟩ : syracuseStep 3042035 = 4563053) B4563053
theorem B3042089 : Blo 900574 3042089 := bstep (se 2 (by rfl) ⟨1140783, by rfl⟩ : syracuseStep 3042089 = 2281567) B2281567
theorem B2714489 : Blo 900574 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B6843851 : Blo 900574 6843851 := bstep (se 1 (by rfl) ⟨5132888, by rfl⟩ : syracuseStep 6843851 = 10265777) B10265777
theorem B49475393 : Blo 900574 49475393 := bstep (se 2 (by rfl) ⟨18553272, by rfl⟩ : syracuseStep 49475393 = 37106545) B37106545
theorem B2289505 : Blo 900574 2289505 := bstep (se 2 (by rfl) ⟨858564, by rfl⟩ : syracuseStep 2289505 = 1717129) B1717129
theorem B1142839 : Blo 900574 1142839 := bstep (se 1 (by rfl) ⟨857129, by rfl⟩ : syracuseStep 1142839 = 1714259) B1714259
theorem B4878463 : Blo 900574 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B3043547 : Blo 900574 3043547 := bstep (se 1 (by rfl) ⟨2282660, by rfl⟩ : syracuseStep 3043547 = 4565321) B4565321
theorem B3043655 : Blo 900574 3043655 := bstep (se 1 (by rfl) ⟨2282741, by rfl⟩ : syracuseStep 3043655 = 4565483) B4565483
theorem B5140817 : Blo 900574 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B37614203 : Blo 900574 37614203 := bstep (se 1 (by rfl) ⟨28210652, by rfl⟩ : syracuseStep 37614203 = 56421305) B56421305
theorem B26702855 : Blo 900574 26702855 := bstep (se 1 (by rfl) ⟨20027141, by rfl⟩ : syracuseStep 26702855 = 40054283) B40054283
theorem B1373231 : Blo 900574 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B3044411 : Blo 900574 3044411 := bstep (se 1 (by rfl) ⟨2283308, by rfl⟩ : syracuseStep 3044411 = 4566617) B4566617
theorem B2029193 : Blo 900574 2029193 := bstep (se 2 (by rfl) ⟨760947, by rfl⟩ : syracuseStep 2029193 = 1521895) B1521895
theorem B1013755 : Blo 900574 1013755 := bstep (se 1 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 1013755 = 1520633) B1520633
theorem B1013935 : Blo 900574 1013935 := bstep (se 1 (by rfl) ⟨760451, by rfl⟩ : syracuseStep 1013935 = 1520903) B1520903
theorem B10287647 : Blo 900574 10287647 := bstep (se 1 (by rfl) ⟨7715735, by rfl⟩ : syracuseStep 10287647 = 15431471) B15431471
theorem B3046031 : Blo 900574 3046031 := bstep (se 1 (by rfl) ⟨2284523, by rfl⟩ : syracuseStep 3046031 = 4569047) B4569047
theorem B2030867 : Blo 900574 2030867 := bstep (se 1 (by rfl) ⟨1523150, by rfl⟩ : syracuseStep 2030867 = 3046301) B3046301
theorem B1015195 : Blo 900574 1015195 := bstep (se 1 (by rfl) ⟨761396, by rfl⟩ : syracuseStep 1015195 = 1522793) B1522793
theorem B13172183 : Blo 900574 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B2031497 : Blo 900574 2031497 := bstep (se 2 (by rfl) ⟨761811, by rfl⟩ : syracuseStep 2031497 = 1523623) B1523623
theorem B26345645 : Blo 900574 26345645 := bstep (se 3 (by rfl) ⟨4939808, by rfl⟩ : syracuseStep 26345645 = 9879617) B9879617
theorem B5145191 : Blo 900574 5145191 := bstep (se 1 (by rfl) ⟨3858893, by rfl⟩ : syracuseStep 5145191 = 7717787) B7717787
theorem B9897065 : Blo 900574 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B2033225 : Blo 900574 2033225 := bstep (se 2 (by rfl) ⟨762459, by rfl⟩ : syracuseStep 2033225 = 1524919) B1524919
theorem B2885303 : Blo 900574 2885303 := bstep (se 1 (by rfl) ⟨2163977, by rfl⟩ : syracuseStep 2885303 = 4327955) B4327955
theorem B3082121 : Blo 900574 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B2034719 : Blo 900574 2034719 := bstep (se 1 (by rfl) ⟨1526039, by rfl⟩ : syracuseStep 2034719 = 3052079) B3052079
theorem B6949921 : Blo 900574 6949921 := bstep (se 2 (by rfl) ⟨2606220, by rfl⟩ : syracuseStep 6949921 = 5212441) B5212441
theorem B270175283 : Blo 900574 270175283 := bstep (se 1 (by rfl) ⟨202631462, by rfl⟩ : syracuseStep 270175283 = 405262925) B405262925
theorem B11570323 : Blo 900574 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B14650577 : Blo 900574 14650577 := bstep (se 2 (by rfl) ⟨5493966, by rfl⟩ : syracuseStep 14650577 = 10987933) B10987933
theorem B9408125 : Blo 900574 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B3051755 : Blo 900574 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B10261403 : Blo 900574 10261403 := bstep (se 1 (by rfl) ⟨7696052, by rfl⟩ : syracuseStep 10261403 = 15392105) B15392105
theorem B3052673 : Blo 900574 3052673 := bstep (se 2 (by rfl) ⟨1144752, by rfl⟩ : syracuseStep 3052673 = 2289505) B2289505
theorem B3052727 : Blo 900574 3052727 := bstep (se 1 (by rfl) ⟨2289545, by rfl⟩ : syracuseStep 3052727 = 4579091) B4579091
theorem B9279197 : Blo 900574 9279197 := bstep (se 3 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 9279197 = 3479699) B3479699
theorem B1710143 : Blo 900574 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B3250799 : Blo 900574 3250799 := bstep (se 1 (by rfl) ⟨2438099, by rfl⟩ : syracuseStep 3250799 = 4876199) B4876199
theorem B5151707 : Blo 900574 5151707 := bstep (se 1 (by rfl) ⟨3863780, by rfl⟩ : syracuseStep 5151707 = 7727561) B7727561
theorem B4562081 : Blo 900574 4562081 := bstep (se 2 (by rfl) ⟨1710780, by rfl⟩ : syracuseStep 4562081 = 3421561) B3421561
theorem B1809659 : Blo 900574 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B4562567 : Blo 900574 4562567 := bstep (se 1 (by rfl) ⟨3421925, by rfl⟩ : syracuseStep 4562567 = 6843851) B6843851
theorem B1711867 : Blo 900574 1711867 := bstep (se 1 (by rfl) ⟨1283900, by rfl⟩ : syracuseStep 1711867 = 2567801) B2567801
theorem B2891659 : Blo 900574 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B1351673 : Blo 900574 1351673 := bstep (se 2 (by rfl) ⟨506877, by rfl⟩ : syracuseStep 1351673 = 1013755) B1013755
theorem B1351913 : Blo 900574 1351913 := bstep (se 2 (by rfl) ⟨506967, by rfl⟩ : syracuseStep 1351913 = 1013935) B1013935
theorem B7315849 : Blo 900574 7315849 := bstep (se 2 (by rfl) ⟨2743443, by rfl⟩ : syracuseStep 7315849 = 5486887) B5486887
theorem B25076135 : Blo 900574 25076135 := bstep (se 1 (by rfl) ⟨18807101, by rfl⟩ : syracuseStep 25076135 = 37614203) B37614203
theorem B2171551 : Blo 900574 2171551 := bstep (se 1 (by rfl) ⟨1628663, by rfl⟩ : syracuseStep 2171551 = 3257327) B3257327
theorem B17801903 : Blo 900574 17801903 := bstep (se 1 (by rfl) ⟨13351427, by rfl⟩ : syracuseStep 17801903 = 26702855) B26702855
theorem B7709417 : Blo 900574 7709417 := bstep (se 2 (by rfl) ⟨2891031, by rfl⟩ : syracuseStep 7709417 = 5782063) B5782063
theorem B1352795 : Blo 900574 1352795 := bstep (se 1 (by rfl) ⟨1014596, by rfl⟩ : syracuseStep 1352795 = 2029193) B2029193
theorem B2172167 : Blo 900574 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B1713727 : Blo 900574 1713727 := bstep (se 1 (by rfl) ⟨1285295, by rfl⟩ : syracuseStep 1713727 = 2570591) B2570591
theorem B6858431 : Blo 900574 6858431 := bstep (se 1 (by rfl) ⟨5143823, by rfl⟩ : syracuseStep 6858431 = 10287647) B10287647
theorem B1353593 : Blo 900574 1353593 := bstep (se 2 (by rfl) ⟨507597, by rfl⟩ : syracuseStep 1353593 = 1015195) B1015195
theorem B2893735 : Blo 900574 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B1353911 : Blo 900574 1353911 := bstep (se 1 (by rfl) ⟨1015433, by rfl⟩ : syracuseStep 1353911 = 2030867) B2030867
theorem B2566343 : Blo 900574 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B1354331 : Blo 900574 1354331 := bstep (se 1 (by rfl) ⟨1015748, by rfl⟩ : syracuseStep 1354331 = 2031497) B2031497
theorem B1714783 : Blo 900574 1714783 := bstep (se 1 (by rfl) ⟨1286087, by rfl⟩ : syracuseStep 1714783 = 2572175) B2572175
theorem B1354619 : Blo 900574 1354619 := bstep (se 1 (by rfl) ⟨1015964, by rfl⟩ : syracuseStep 1354619 = 2031929) B2031929
theorem B2435969 : Blo 900574 2435969 := bstep (se 2 (by rfl) ⟨913488, by rfl⟩ : syracuseStep 2435969 = 1826977) B1826977
theorem B12987499 : Blo 900574 12987499 := bstep (se 1 (by rfl) ⟨9740624, by rfl⟩ : syracuseStep 12987499 = 19481249) B19481249
theorem B8662139 : Blo 900574 8662139 := bstep (se 1 (by rfl) ⟨6496604, by rfl⟩ : syracuseStep 8662139 = 12993209) B12993209
theorem B4566455 : Blo 900574 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B1355771 : Blo 900574 1355771 := bstep (se 1 (by rfl) ⟨1016828, by rfl⟩ : syracuseStep 1355771 = 2033657) B2033657
theorem B1355831 : Blo 900574 1355831 := bstep (se 1 (by rfl) ⟨1016873, by rfl⟩ : syracuseStep 1355831 = 2033747) B2033747
theorem B1355945 : Blo 900574 1355945 := bstep (se 2 (by rfl) ⟨508479, by rfl⟩ : syracuseStep 1355945 = 1016959) B1016959
theorem B2928815 : Blo 900574 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B1355951 : Blo 900574 1355951 := bstep (se 1 (by rfl) ⟨1016963, by rfl⟩ : syracuseStep 1355951 = 2033927) B2033927
theorem B15413975 : Blo 900574 15413975 := bstep (se 1 (by rfl) ⟨11560481, by rfl⟩ : syracuseStep 15413975 = 23120963) B23120963
theorem B963451 : Blo 900574 963451 := bstep (se 1 (by rfl) ⟨722588, by rfl⟩ : syracuseStep 963451 = 1445177) B1445177
theorem B2929657 : Blo 900574 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B237024301 : Blo 900574 237024301 := bstep (se 3 (by rfl) ⟨44442056, by rfl⟩ : syracuseStep 237024301 = 88884113) B88884113
theorem B3652361 : Blo 900574 3652361 := bstep (se 2 (by rfl) ⟨1369635, by rfl⟩ : syracuseStep 3652361 = 2739271) B2739271
theorem B1522543 : Blo 900574 1522543 := bstep (se 1 (by rfl) ⟨1141907, by rfl⟩ : syracuseStep 1522543 = 2283815) B2283815
theorem B900847 : Blo 900574 900847 := bstep (se 1 (by rfl) ⟨675635, by rfl⟩ : syracuseStep 900847 = 1351271) B1351271
theorem B900955 : Blo 900574 900955 := bstep (se 1 (by rfl) ⟨675716, by rfl⟩ : syracuseStep 900955 = 1351433) B1351433
theorem B12992399 : Blo 900574 12992399 := bstep (se 1 (by rfl) ⟨9744299, by rfl⟩ : syracuseStep 12992399 = 19488599) B19488599
theorem B7716829 : Blo 900574 7716829 := bstep (se 3 (by rfl) ⟨1446905, by rfl⟩ : syracuseStep 7716829 = 2893811) B2893811
theorem B901103 : Blo 900574 901103 := bstep (se 1 (by rfl) ⟨675827, by rfl⟩ : syracuseStep 901103 = 1351655) B1351655
theorem B901183 : Blo 900574 901183 := bstep (se 1 (by rfl) ⟨675887, by rfl⟩ : syracuseStep 901183 = 1351775) B1351775
theorem B1523785 : Blo 900574 1523785 := bstep (se 2 (by rfl) ⟨571419, by rfl⟩ : syracuseStep 1523785 = 1142839) B1142839
theorem B901223 : Blo 900574 901223 := bstep (se 1 (by rfl) ⟨675917, by rfl⟩ : syracuseStep 901223 = 1351835) B1351835
theorem B1523819 : Blo 900574 1523819 := bstep (se 1 (by rfl) ⟨1142864, by rfl⟩ : syracuseStep 1523819 = 2285729) B2285729
theorem B901279 : Blo 900574 901279 := bstep (se 1 (by rfl) ⟨675959, by rfl⟩ : syracuseStep 901279 = 1351919) B1351919
theorem B6504617 : Blo 900574 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B901531 : Blo 900574 901531 := bstep (se 1 (by rfl) ⟨676148, by rfl⟩ : syracuseStep 901531 = 1352297) B1352297
theorem B901535 : Blo 900574 901535 := bstep (se 1 (by rfl) ⟨676151, by rfl⟩ : syracuseStep 901535 = 1352303) B1352303
theorem B901951 : Blo 900574 901951 := bstep (se 1 (by rfl) ⟨676463, by rfl⟩ : syracuseStep 901951 = 1352927) B1352927
theorem B902111 : Blo 900574 902111 := bstep (se 1 (by rfl) ⟨676583, by rfl⟩ : syracuseStep 902111 = 1353167) B1353167
theorem B902235 : Blo 900574 902235 := bstep (se 1 (by rfl) ⟨676676, by rfl⟩ : syracuseStep 902235 = 1353353) B1353353
theorem B902271 : Blo 900574 902271 := bstep (se 1 (by rfl) ⟨676703, by rfl⟩ : syracuseStep 902271 = 1353407) B1353407
theorem B902375 : Blo 900574 902375 := bstep (se 1 (by rfl) ⟨676781, by rfl⟩ : syracuseStep 902375 = 1353563) B1353563
theorem B6866207 : Blo 900574 6866207 := bstep (se 1 (by rfl) ⟨5149655, by rfl⟩ : syracuseStep 6866207 = 10299311) B10299311
theorem B13190471 : Blo 900574 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B902631 : Blo 900574 902631 := bstep (se 1 (by rfl) ⟨676973, by rfl⟩ : syracuseStep 902631 = 1353947) B1353947
theorem B2573815 : Blo 900574 2573815 := bstep (se 1 (by rfl) ⟨1930361, by rfl⟩ : syracuseStep 2573815 = 3860723) B3860723
theorem B902811 : Blo 900574 902811 := bstep (se 1 (by rfl) ⟨677108, by rfl⟩ : syracuseStep 902811 = 1354217) B1354217
theorem B902815 : Blo 900574 902815 := bstep (se 1 (by rfl) ⟨677111, by rfl⟩ : syracuseStep 902815 = 1354223) B1354223
theorem B903023 : Blo 900574 903023 := bstep (se 1 (by rfl) ⟨677267, by rfl⟩ : syracuseStep 903023 = 1354535) B1354535
theorem B903071 : Blo 900574 903071 := bstep (se 1 (by rfl) ⟨677303, by rfl⟩ : syracuseStep 903071 = 1354607) B1354607
theorem B903239 : Blo 900574 903239 := bstep (se 1 (by rfl) ⟨677429, by rfl⟩ : syracuseStep 903239 = 1354859) B1354859
theorem B2607329 : Blo 900574 2607329 := bstep (se 2 (by rfl) ⟨977748, by rfl⟩ : syracuseStep 2607329 = 1955497) B1955497
theorem B903399 : Blo 900574 903399 := bstep (se 1 (by rfl) ⟨677549, by rfl⟩ : syracuseStep 903399 = 1355099) B1355099
theorem B903419 : Blo 900574 903419 := bstep (se 1 (by rfl) ⟨677564, by rfl⟩ : syracuseStep 903419 = 1355129) B1355129
theorem B903423 : Blo 900574 903423 := bstep (se 1 (by rfl) ⟨677567, by rfl⟩ : syracuseStep 903423 = 1355135) B1355135
theorem B903579 : Blo 900574 903579 := bstep (se 1 (by rfl) ⟨677684, by rfl⟩ : syracuseStep 903579 = 1355369) B1355369
theorem B32983595 : Blo 900574 32983595 := bstep (se 1 (by rfl) ⟨24737696, by rfl⟩ : syracuseStep 32983595 = 49475393) B49475393
theorem B903839 : Blo 900574 903839 := bstep (se 1 (by rfl) ⟨677879, by rfl⟩ : syracuseStep 903839 = 1355759) B1355759
theorem B903919 : Blo 900574 903919 := bstep (se 1 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 903919 = 1355879) B1355879
theorem B903999 : Blo 900574 903999 := bstep (se 1 (by rfl) ⟨677999, by rfl⟩ : syracuseStep 903999 = 1355999) B1355999
theorem B904039 : Blo 900574 904039 := bstep (se 1 (by rfl) ⟨678029, by rfl⟩ : syracuseStep 904039 = 1356059) B1356059
theorem B7326587 : Blo 900574 7326587 := bstep (se 1 (by rfl) ⟨5494940, by rfl⟩ : syracuseStep 7326587 = 10989881) B10989881
theorem B3427211 : Blo 900574 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B904303 : Blo 900574 904303 := bstep (se 1 (by rfl) ⟨678227, by rfl⟩ : syracuseStep 904303 = 1356455) B1356455
theorem B4574393 : Blo 900574 4574393 := bstep (se 2 (by rfl) ⟨1715397, by rfl⟩ : syracuseStep 4574393 = 3430795) B3430795
theorem B904383 : Blo 900574 904383 := bstep (se 1 (by rfl) ⟨678287, by rfl⟩ : syracuseStep 904383 = 1356575) B1356575
theorem B904399 : Blo 900574 904399 := bstep (se 1 (by rfl) ⟨678299, by rfl⟩ : syracuseStep 904399 = 1356599) B1356599
theorem B1625363 : Blo 900574 1625363 := bstep (se 1 (by rfl) ⟨1219022, by rfl⟩ : syracuseStep 1625363 = 2438045) B2438045
theorem B904475 : Blo 900574 904475 := bstep (se 1 (by rfl) ⟨678356, by rfl⟩ : syracuseStep 904475 = 1356713) B1356713
theorem B4115767 : Blo 900574 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B904519 : Blo 900574 904519 := bstep (se 1 (by rfl) ⟨678389, by rfl⟩ : syracuseStep 904519 = 1356779) B1356779
theorem B4574555 : Blo 900574 4574555 := bstep (se 1 (by rfl) ⟨3430916, by rfl⟩ : syracuseStep 4574555 = 6861833) B6861833
theorem B5852645 : Blo 900574 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B7721203 : Blo 900574 7721203 := bstep (se 1 (by rfl) ⟨5790902, by rfl⟩ : syracuseStep 7721203 = 11581805) B11581805
theorem B29250017 : Blo 900574 29250017 := bstep (se 2 (by rfl) ⟨10968756, by rfl⟩ : syracuseStep 29250017 = 21937513) B21937513
theorem B4575851 : Blo 900574 4575851 := bstep (se 1 (by rfl) ⟨3431888, by rfl⟩ : syracuseStep 4575851 = 6863777) B6863777
theorem B19813697 : Blo 900574 19813697 := bstep (se 2 (by rfl) ⟨7430136, by rfl⟩ : syracuseStep 19813697 = 14860273) B14860273
theorem B7526467 : Blo 900574 7526467 := bstep (se 1 (by rfl) ⟨5644850, by rfl⟩ : syracuseStep 7526467 = 11289701) B11289701
theorem B11589803 : Blo 900574 11589803 := bstep (se 1 (by rfl) ⟨8692352, by rfl⟩ : syracuseStep 11589803 = 17384705) B17384705
theorem B3856571 : Blo 900574 3856571 := bstep (se 1 (by rfl) ⟨2892428, by rfl⟩ : syracuseStep 3856571 = 5784857) B5784857
theorem B11557201 : Blo 900574 11557201 := bstep (se 2 (by rfl) ⟨4333950, by rfl⟩ : syracuseStep 11557201 = 8667901) B8667901
theorem B1923527 : Blo 900574 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B1923689 : Blo 900574 1923689 := bstep (se 2 (by rfl) ⟨721383, by rfl⟩ : syracuseStep 1923689 = 1442767) B1442767
theorem B3431099 : Blo 900574 3431099 := bstep (se 1 (by rfl) ⟨2573324, by rfl⟩ : syracuseStep 3431099 = 5146649) B5146649
theorem B5495863 : Blo 900574 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B8773691 : Blo 900574 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B3661949 : Blo 900574 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B2285759 : Blo 900574 2285759 := bstep (se 1 (by rfl) ⟨1714319, by rfl⟩ : syracuseStep 2285759 = 3428639) B3428639
theorem B75260335 : Blo 900574 75260335 := bstep (se 1 (by rfl) ⟨56445251, by rfl⟩ : syracuseStep 75260335 = 112890503) B112890503
theorem B3433043 : Blo 900574 3433043 := bstep (se 1 (by rfl) ⟨2574782, by rfl⟩ : syracuseStep 3433043 = 5149565) B5149565
theorem B4121351 : Blo 900574 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B3433697 : Blo 900574 3433697 := bstep (se 2 (by rfl) ⟨1287636, by rfl⟩ : syracuseStep 3433697 = 2575273) B2575273
theorem B23160329 : Blo 900574 23160329 := bstep (se 2 (by rfl) ⟨8685123, by rfl⟩ : syracuseStep 23160329 = 17370247) B17370247
theorem B3040847 : Blo 900574 3040847 := bstep (se 1 (by rfl) ⟨2280635, by rfl⟩ : syracuseStep 3040847 = 4561271) B4561271
theorem B12347255 : Blo 900574 12347255 := bstep (se 1 (by rfl) ⟨9260441, by rfl⟩ : syracuseStep 12347255 = 18520883) B18520883
theorem B1828775 : Blo 900574 1828775 := bstep (se 1 (by rfl) ⟨1371581, by rfl⟩ : syracuseStep 1828775 = 2743163) B2743163
theorem B6842393 : Blo 900574 6842393 := bstep (se 2 (by rfl) ⟨2565897, by rfl⟩ : syracuseStep 6842393 = 5131795) B5131795
theorem B14641235 : Blo 900574 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B19753105 : Blo 900574 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B2026331 : Blo 900574 2026331 := bstep (se 1 (by rfl) ⟨1519748, by rfl⟩ : syracuseStep 2026331 = 3039497) B3039497
theorem B7695233 : Blo 900574 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B2288513 : Blo 900574 2288513 := bstep (se 2 (by rfl) ⟨858192, by rfl⟩ : syracuseStep 2288513 = 1716385) B1716385
theorem B5139359 : Blo 900574 5139359 := bstep (se 1 (by rfl) ⟨3854519, by rfl⟩ : syracuseStep 5139359 = 7709039) B7709039
theorem B3861695 : Blo 900574 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B3042953 : Blo 900574 3042953 := bstep (se 2 (by rfl) ⟨1141107, by rfl⟩ : syracuseStep 3042953 = 2282215) B2282215
theorem B3043007 : Blo 900574 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B5500727 : Blo 900574 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B3043169 : Blo 900574 3043169 := bstep (se 2 (by rfl) ⟨1141188, by rfl⟩ : syracuseStep 3043169 = 2282377) B2282377
theorem B1929071 : Blo 900574 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B5140361 : Blo 900574 5140361 := bstep (se 2 (by rfl) ⟨1927635, by rfl⟩ : syracuseStep 5140361 = 3855271) B3855271
theorem B3862637 : Blo 900574 3862637 := bstep (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) B1448489
theorem B3043817 : Blo 900574 3043817 := bstep (se 2 (by rfl) ⟨1141431, by rfl⟩ : syracuseStep 3043817 = 2282863) B2282863
theorem B2028023 : Blo 900574 2028023 := bstep (se 1 (by rfl) ⟨1521017, by rfl⟩ : syracuseStep 2028023 = 3042035) B3042035
theorem B2028059 : Blo 900574 2028059 := bstep (se 1 (by rfl) ⟨1521044, by rfl⟩ : syracuseStep 2028059 = 3042089) B3042089
theorem B7696943 : Blo 900574 7696943 := bstep (se 1 (by rfl) ⟨5772707, by rfl⟩ : syracuseStep 7696943 = 11545415) B11545415
theorem B3863321 : Blo 900574 3863321 := bstep (se 2 (by rfl) ⟨1448745, by rfl⟩ : syracuseStep 3863321 = 2897491) B2897491
theorem B6845309 : Blo 900574 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B3044681 : Blo 900574 3044681 := bstep (se 2 (by rfl) ⟨1141755, by rfl⟩ : syracuseStep 3044681 = 2283511) B2283511
theorem B2029031 : Blo 900574 2029031 := bstep (se 1 (by rfl) ⟨1521773, by rfl⟩ : syracuseStep 2029031 = 3043547) B3043547
theorem B1930729 : Blo 900574 1930729 := bstep (se 2 (by rfl) ⟨724023, by rfl⟩ : syracuseStep 1930729 = 1448047) B1448047
theorem B2029103 : Blo 900574 2029103 := bstep (se 1 (by rfl) ⟨1521827, by rfl⟩ : syracuseStep 2029103 = 3043655) B3043655
theorem B6846281 : Blo 900574 6846281 := bstep (se 2 (by rfl) ⟨2567355, by rfl⟩ : syracuseStep 6846281 = 5134711) B5134711
theorem B2029607 : Blo 900574 2029607 := bstep (se 1 (by rfl) ⟨1522205, by rfl⟩ : syracuseStep 2029607 = 3044411) B3044411
theorem B1931617 : Blo 900574 1931617 := bstep (se 2 (by rfl) ⟨724356, by rfl⟩ : syracuseStep 1931617 = 1448713) B1448713
theorem B7830121 : Blo 900574 7830121 := bstep (se 2 (by rfl) ⟨2936295, by rfl⟩ : syracuseStep 7830121 = 5872591) B5872591
theorem B1014511 : Blo 900574 1014511 := bstep (se 1 (by rfl) ⟨760883, by rfl⟩ : syracuseStep 1014511 = 1521767) B1521767
theorem B2030687 : Blo 900574 2030687 := bstep (se 1 (by rfl) ⟨1523015, by rfl⟩ : syracuseStep 2030687 = 3046031) B3046031
theorem B11566223 : Blo 900574 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B3046895 : Blo 900574 3046895 := bstep (se 1 (by rfl) ⟨2285171, by rfl⟩ : syracuseStep 3046895 = 4570343) B4570343
theorem B8781455 : Blo 900574 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B1015879 : Blo 900574 1015879 := bstep (se 1 (by rfl) ⟨761909, by rfl⟩ : syracuseStep 1015879 = 1523819) B1523819
theorem B2031713 : Blo 900574 2031713 := bstep (se 2 (by rfl) ⟨761892, by rfl⟩ : syracuseStep 2031713 = 1523785) B1523785
theorem B17563763 : Blo 900574 17563763 := bstep (se 1 (by rfl) ⟨13172822, by rfl⟩ : syracuseStep 17563763 = 26345645) B26345645
theorem B23396509 : Blo 900574 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B9765197 : Blo 900574 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B1738219 : Blo 900574 1738219 := bstep (se 1 (by rfl) ⟨1303664, by rfl⟩ : syracuseStep 1738219 = 2607329) B2607329
theorem B21989063 : Blo 900574 21989063 := bstep (se 1 (by rfl) ⟨16491797, by rfl⟩ : syracuseStep 21989063 = 32983595) B32983595
theorem B4884391 : Blo 900574 4884391 := bstep (se 1 (by rfl) ⟨3663293, by rfl⟩ : syracuseStep 4884391 = 7326587) B7326587
theorem B3049595 : Blo 900574 3049595 := bstep (se 1 (by rfl) ⟨2287196, by rfl⟩ : syracuseStep 3049595 = 4574393) B4574393
theorem B9767051 : Blo 900574 9767051 := bstep (se 1 (by rfl) ⟨7325288, by rfl⟩ : syracuseStep 9767051 = 14650577) B14650577
theorem B1083575 : Blo 900574 1083575 := bstep (se 1 (by rfl) ⟨812681, by rfl⟩ : syracuseStep 1083575 = 1625363) B1625363
theorem B3049703 : Blo 900574 3049703 := bstep (se 1 (by rfl) ⟨2287277, by rfl⟩ : syracuseStep 3049703 = 4574555) B4574555
theorem B3901763 : Blo 900574 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B2034503 : Blo 900574 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B19500011 : Blo 900574 19500011 := bstep (se 1 (by rfl) ⟨14625008, by rfl⟩ : syracuseStep 19500011 = 29250017) B29250017
theorem B3050567 : Blo 900574 3050567 := bstep (se 1 (by rfl) ⟨2287925, by rfl⟩ : syracuseStep 3050567 = 4575851) B4575851
theorem B2035115 : Blo 900574 2035115 := bstep (se 1 (by rfl) ⟨1526336, by rfl⟩ : syracuseStep 2035115 = 3052673) B3052673
theorem B2035151 : Blo 900574 2035151 := bstep (se 1 (by rfl) ⟨1526363, by rfl⟩ : syracuseStep 2035151 = 3052727) B3052727
theorem B13209131 : Blo 900574 13209131 := bstep (se 1 (by rfl) ⟨9906848, by rfl⟩ : syracuseStep 13209131 = 19813697) B19813697
theorem B2167199 : Blo 900574 2167199 := bstep (se 1 (by rfl) ⟨1625399, by rfl⟩ : syracuseStep 2167199 = 3250799) B3250799
theorem B16717423 : Blo 900574 16717423 := bstep (se 1 (by rfl) ⟨12538067, by rfl⟩ : syracuseStep 16717423 = 25076135) B25076135
theorem B10294937 : Blo 900574 10294937 := bstep (se 2 (by rfl) ⟨3860601, by rfl⟩ : syracuseStep 10294937 = 7721203) B7721203
theorem B1448111 : Blo 900574 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B15440219 : Blo 900574 15440219 := bstep (se 1 (by rfl) ⟨11580164, by rfl⟩ : syracuseStep 15440219 = 23160329) B23160329
theorem B1284601 : Blo 900574 1284601 := bstep (se 2 (by rfl) ⟨481725, by rfl⟩ : syracuseStep 1284601 = 963451) B963451
theorem B8231503 : Blo 900574 8231503 := bstep (se 1 (by rfl) ⟨6173627, by rfl⟩ : syracuseStep 8231503 = 12347255) B12347255
theorem B3906209 : Blo 900574 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B4561595 : Blo 900574 4561595 := bstep (se 1 (by rfl) ⟨3421196, by rfl⟩ : syracuseStep 4561595 = 6842393) B6842393
theorem B1710895 : Blo 900574 1710895 := bstep (se 1 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 1710895 = 2566343) B2566343
theorem B1350887 : Blo 900574 1350887 := bstep (se 1 (by rfl) ⟨1013165, by rfl⟩ : syracuseStep 1350887 = 2026331) B2026331
theorem B5774759 : Blo 900574 5774759 := bstep (se 1 (by rfl) ⟨4331069, by rfl⟩ : syracuseStep 5774759 = 8662139) B8662139
theorem B1286047 : Blo 900574 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B10035289 : Blo 900574 10035289 := bstep (se 2 (by rfl) ⟨3763233, by rfl⟩ : syracuseStep 10035289 = 7526467) B7526467
theorem B1352015 : Blo 900574 1352015 := bstep (se 1 (by rfl) ⟨1014011, by rfl⟩ : syracuseStep 1352015 = 2028023) B2028023
theorem B1352039 : Blo 900574 1352039 := bstep (se 1 (by rfl) ⟨1014029, by rfl⟩ : syracuseStep 1352039 = 2028059) B2028059
theorem B15409601 : Blo 900574 15409601 := bstep (se 2 (by rfl) ⟨5778600, by rfl⟩ : syracuseStep 15409601 = 11557201) B11557201
theorem B10297853 : Blo 900574 10297853 := bstep (se 3 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 10297853 = 3861695) B3861695
theorem B4563539 : Blo 900574 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B4825757 : Blo 900574 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B1352681 : Blo 900574 1352681 := bstep (se 2 (by rfl) ⟨507255, by rfl⟩ : syracuseStep 1352681 = 1014511) B1014511
theorem B1352687 : Blo 900574 1352687 := bstep (se 1 (by rfl) ⟨1014515, by rfl⟩ : syracuseStep 1352687 = 2029031) B2029031
theorem B1352735 : Blo 900574 1352735 := bstep (se 1 (by rfl) ⟨1014551, by rfl⟩ : syracuseStep 1352735 = 2029103) B2029103
theorem B4564187 : Blo 900574 4564187 := bstep (se 1 (by rfl) ⟨3423140, by rfl⟩ : syracuseStep 4564187 = 6846281) B6846281
theorem B1353071 : Blo 900574 1353071 := bstep (se 1 (by rfl) ⟨1014803, by rfl⟩ : syracuseStep 1353071 = 2029607) B2029607
theorem B2434907 : Blo 900574 2434907 := bstep (se 1 (by rfl) ⟨1826180, by rfl⟩ : syracuseStep 2434907 = 3652361) B3652361
theorem B1353791 : Blo 900574 1353791 := bstep (se 1 (by rfl) ⟨1015343, by rfl⟩ : syracuseStep 1353791 = 2030687) B2030687
theorem B7710815 : Blo 900574 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B8661599 : Blo 900574 8661599 := bstep (se 1 (by rfl) ⟨6496199, by rfl⟩ : syracuseStep 8661599 = 12992399) B12992399
theorem B4336411 : Blo 900574 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B100347113 : Blo 900574 100347113 := bstep (se 2 (by rfl) ⟨37630167, by rfl⟩ : syracuseStep 100347113 = 75260335) B75260335
theorem B6598043 : Blo 900574 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B2895401 : Blo 900574 2895401 := bstep (se 2 (by rfl) ⟨1085775, by rfl⟩ : syracuseStep 2895401 = 2171551) B2171551
theorem B8793647 : Blo 900574 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B1355483 : Blo 900574 1355483 := bstep (se 1 (by rfl) ⟨1016612, by rfl⟩ : syracuseStep 1355483 = 2033225) B2033225
theorem B1356479 : Blo 900574 1356479 := bstep (se 1 (by rfl) ⟨1017359, by rfl⟩ : syracuseStep 1356479 = 2034719) B2034719
theorem B6272083 : Blo 900574 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B2571047 : Blo 900574 2571047 := bstep (se 1 (by rfl) ⟨1928285, by rfl⟩ : syracuseStep 2571047 = 3856571) B3856571
theorem B17316665 : Blo 900574 17316665 := bstep (se 2 (by rfl) ⟨6493749, by rfl⟩ : syracuseStep 17316665 = 12987499) B12987499
theorem B5487689 : Blo 900574 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B901115 : Blo 900574 901115 := bstep (se 1 (by rfl) ⟨675836, by rfl⟩ : syracuseStep 901115 = 1351673) B1351673
theorem B1523839 : Blo 900574 1523839 := bstep (se 1 (by rfl) ⟨1142879, by rfl⟩ : syracuseStep 1523839 = 2285759) B2285759
theorem B901275 : Blo 900574 901275 := bstep (se 1 (by rfl) ⟨675956, by rfl⟩ : syracuseStep 901275 = 1351913) B1351913
theorem B901863 : Blo 900574 901863 := bstep (se 1 (by rfl) ⟨676397, by rfl⟩ : syracuseStep 901863 = 1352795) B1352795
theorem B4572287 : Blo 900574 4572287 := bstep (se 1 (by rfl) ⟨3429215, by rfl⟩ : syracuseStep 4572287 = 6858431) B6858431
theorem B5129405 : Blo 900574 5129405 := bstep (se 3 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 5129405 = 1923527) B1923527
theorem B902395 : Blo 900574 902395 := bstep (se 1 (by rfl) ⟨676796, by rfl⟩ : syracuseStep 902395 = 1353593) B1353593
theorem B316032401 : Blo 900574 316032401 := bstep (se 2 (by rfl) ⟨118512150, by rfl⟩ : syracuseStep 316032401 = 237024301) B237024301
theorem B902607 : Blo 900574 902607 := bstep (se 1 (by rfl) ⟨676955, by rfl⟩ : syracuseStep 902607 = 1353911) B1353911
theorem B5129837 : Blo 900574 5129837 := bstep (se 3 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 5129837 = 1923689) B1923689
theorem B902887 : Blo 900574 902887 := bstep (se 1 (by rfl) ⟨677165, by rfl⟩ : syracuseStep 902887 = 1354331) B1354331
theorem B903079 : Blo 900574 903079 := bstep (se 1 (by rfl) ⟨677309, by rfl⟩ : syracuseStep 903079 = 1354619) B1354619
theorem B5130155 : Blo 900574 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B1623979 : Blo 900574 1623979 := bstep (se 1 (by rfl) ⟨1217984, by rfl⟩ : syracuseStep 1623979 = 2435969) B2435969
theorem B1525675 : Blo 900574 1525675 := bstep (se 1 (by rfl) ⟨1144256, by rfl⟩ : syracuseStep 1525675 = 2288513) B2288513
theorem B3426239 : Blo 900574 3426239 := bstep (se 1 (by rfl) ⟨2569679, by rfl⟩ : syracuseStep 3426239 = 5139359) B5139359
theorem B2574305 : Blo 900574 2574305 := bstep (se 2 (by rfl) ⟨965364, by rfl⟩ : syracuseStep 2574305 = 1930729) B1930729
theorem B3426907 : Blo 900574 3426907 := bstep (se 1 (by rfl) ⟨2570180, by rfl⟩ : syracuseStep 3426907 = 5140361) B5140361
theorem B903847 : Blo 900574 903847 := bstep (se 1 (by rfl) ⟨677885, by rfl⟩ : syracuseStep 903847 = 1355771) B1355771
theorem B903887 : Blo 900574 903887 := bstep (se 1 (by rfl) ⟨677915, by rfl⟩ : syracuseStep 903887 = 1355831) B1355831
theorem B2575091 : Blo 900574 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B903963 : Blo 900574 903963 := bstep (se 1 (by rfl) ⟨677972, by rfl⟩ : syracuseStep 903963 = 1355945) B1355945
theorem B1952543 : Blo 900574 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B903967 : Blo 900574 903967 := bstep (se 1 (by rfl) ⟨677975, by rfl⟩ : syracuseStep 903967 = 1355951) B1355951
theorem B5131295 : Blo 900574 5131295 := bstep (se 1 (by rfl) ⟨3848471, by rfl⟩ : syracuseStep 5131295 = 7696943) B7696943
theorem B2575489 : Blo 900574 2575489 := bstep (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) B1931617
theorem B10275983 : Blo 900574 10275983 := bstep (se 1 (by rfl) ⟨7706987, by rfl⟩ : syracuseStep 10275983 = 15413975) B15413975
theorem B2575547 : Blo 900574 2575547 := bstep (se 1 (by rfl) ⟨1931660, by rfl⟩ : syracuseStep 2575547 = 3863321) B3863321
theorem B10440161 : Blo 900574 10440161 := bstep (se 2 (by rfl) ⟨3915060, by rfl⟩ : syracuseStep 10440161 = 7830121) B7830121
theorem B7327817 : Blo 900574 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B2282489 : Blo 900574 2282489 := bstep (se 2 (by rfl) ⟨855933, by rfl⟩ : syracuseStep 2282489 = 1711867) B1711867
theorem B5854303 : Blo 900574 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B3855545 : Blo 900574 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B3430127 : Blo 900574 3430127 := bstep (se 1 (by rfl) ⟨2572595, by rfl⟩ : syracuseStep 3430127 = 5145191) B5145191
theorem B9754465 : Blo 900574 9754465 := bstep (se 2 (by rfl) ⟨3657924, by rfl⟩ : syracuseStep 9754465 = 7315849) B7315849
theorem B4577471 : Blo 900574 4577471 := bstep (se 1 (by rfl) ⟨3433103, by rfl⟩ : syracuseStep 4577471 = 6866207) B6866207
theorem B1923535 : Blo 900574 1923535 := bstep (se 1 (by rfl) ⟨1442651, by rfl⟩ : syracuseStep 1923535 = 2885303) B2885303
theorem B2054747 : Blo 900574 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B47471741 : Blo 900574 47471741 := bstep (se 3 (by rfl) ⟨8900951, by rfl⟩ : syracuseStep 47471741 = 17801903) B17801903
theorem B2284807 : Blo 900574 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B3431753 : Blo 900574 3431753 := bstep (se 2 (by rfl) ⟨1286907, by rfl⟩ : syracuseStep 3431753 = 2573815) B2573815
theorem B180116855 : Blo 900574 180116855 := bstep (se 1 (by rfl) ⟨135087641, by rfl⟩ : syracuseStep 180116855 = 270175283) B270175283
theorem B2284969 : Blo 900574 2284969 := bstep (se 2 (by rfl) ⟨856863, by rfl⟩ : syracuseStep 2284969 = 1713727) B1713727
theorem B3858313 : Blo 900574 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B26337473 : Blo 900574 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B6840935 : Blo 900574 6840935 := bstep (se 1 (by rfl) ⟨5130701, by rfl⟩ : syracuseStep 6840935 = 10261403) B10261403
theorem B2286377 : Blo 900574 2286377 := bstep (se 2 (by rfl) ⟨857391, by rfl⟩ : syracuseStep 2286377 = 1714783) B1714783
theorem B6186131 : Blo 900574 6186131 := bstep (se 1 (by rfl) ⟨4639598, by rfl⟩ : syracuseStep 6186131 = 9279197) B9279197
theorem B1140095 : Blo 900574 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B9266561 : Blo 900574 9266561 := bstep (se 2 (by rfl) ⟨3474960, by rfl⟩ : syracuseStep 9266561 = 6949921) B6949921
theorem B7726535 : Blo 900574 7726535 := bstep (se 1 (by rfl) ⟨5794901, by rfl⟩ : syracuseStep 7726535 = 11589803) B11589803
theorem B15427097 : Blo 900574 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B2287399 : Blo 900574 2287399 := bstep (se 1 (by rfl) ⟨1715549, by rfl⟩ : syracuseStep 2287399 = 3431099) B3431099
theorem B3434471 : Blo 900574 3434471 := bstep (se 1 (by rfl) ⟨2575853, by rfl⟩ : syracuseStep 3434471 = 5151707) B5151707
theorem B3041387 : Blo 900574 3041387 := bstep (se 1 (by rfl) ⟨2281040, by rfl⟩ : syracuseStep 3041387 = 4562081) B4562081
theorem B3041711 : Blo 900574 3041711 := bstep (se 1 (by rfl) ⟨2281283, by rfl⟩ : syracuseStep 3041711 = 4562567) B4562567
theorem B4876733 : Blo 900574 4876733 := bstep (se 3 (by rfl) ⟨914387, by rfl⟩ : syracuseStep 4876733 = 1828775) B1828775
theorem B2288695 : Blo 900574 2288695 := bstep (se 1 (by rfl) ⟨1716521, by rfl⟩ : syracuseStep 2288695 = 3433043) B3433043
theorem B5139611 : Blo 900574 5139611 := bstep (se 1 (by rfl) ⟨3854708, by rfl⟩ : syracuseStep 5139611 = 7709417) B7709417
theorem B2747567 : Blo 900574 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B2289131 : Blo 900574 2289131 := bstep (se 1 (by rfl) ⟨1716848, by rfl⟩ : syracuseStep 2289131 = 3433697) B3433697
theorem B2027231 : Blo 900574 2027231 := bstep (se 1 (by rfl) ⟨1520423, by rfl⟩ : syracuseStep 2027231 = 3040847) B3040847
theorem B9760823 : Blo 900574 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B3044303 : Blo 900574 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B2028635 : Blo 900574 2028635 := bstep (se 1 (by rfl) ⟨1521476, by rfl⟩ : syracuseStep 2028635 = 3042953) B3042953
theorem B2028671 : Blo 900574 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B3667151 : Blo 900574 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B2028779 : Blo 900574 2028779 := bstep (se 1 (by rfl) ⟨1521584, by rfl⟩ : syracuseStep 2028779 = 3043169) B3043169
theorem B2029211 : Blo 900574 2029211 := bstep (se 1 (by rfl) ⟨1521908, by rfl⟩ : syracuseStep 2029211 = 3043817) B3043817
theorem B2029787 : Blo 900574 2029787 := bstep (se 1 (by rfl) ⟨1522340, by rfl⟩ : syracuseStep 2029787 = 3044681) B3044681
theorem B2030057 : Blo 900574 2030057 := bstep (se 2 (by rfl) ⟨761271, by rfl⟩ : syracuseStep 2030057 = 1522543) B1522543
theorem B2031263 : Blo 900574 2031263 := bstep (se 1 (by rfl) ⟨1523447, by rfl⟩ : syracuseStep 2031263 = 3046895) B3046895
theorem B10289105 : Blo 900574 10289105 := bstep (se 2 (by rfl) ⟨3858414, by rfl⟩ : syracuseStep 10289105 = 7716829) B7716829
theorem B2031785 : Blo 900574 2031785 := bstep (se 2 (by rfl) ⟨761919, by rfl⟩ : syracuseStep 2031785 = 1523839) B1523839
theorem B3048191 : Blo 900574 3048191 := bstep (se 1 (by rfl) ⟨2286143, by rfl⟩ : syracuseStep 3048191 = 4572287) B4572287
theorem B124781381 : Blo 900574 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B2033063 : Blo 900574 2033063 := bstep (se 1 (by rfl) ⟨1524797, by rfl⟩ : syracuseStep 2033063 = 3049595) B3049595
theorem B2033135 : Blo 900574 2033135 := bstep (se 1 (by rfl) ⟨1524851, by rfl⟩ : syracuseStep 2033135 = 3049703) B3049703
theorem B2033711 : Blo 900574 2033711 := bstep (se 1 (by rfl) ⟨1525283, by rfl⟩ : syracuseStep 2033711 = 3050567) B3050567
theorem B6850655 : Blo 900574 6850655 := bstep (se 1 (by rfl) ⟨5137991, by rfl⟩ : syracuseStep 6850655 = 10275983) B10275983
theorem B3049865 : Blo 900574 3049865 := bstep (se 2 (by rfl) ⟨1143699, by rfl⟩ : syracuseStep 3049865 = 2287399) B2287399
theorem B2165305 : Blo 900574 2165305 := bstep (se 2 (by rfl) ⟨811989, by rfl⟩ : syracuseStep 2165305 = 1623979) B1623979
theorem B2034233 : Blo 900574 2034233 := bstep (se 2 (by rfl) ⟨762837, by rfl⟩ : syracuseStep 2034233 = 1525675) B1525675
theorem B4885211 : Blo 900574 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B1444799 : Blo 900574 1444799 := bstep (se 1 (by rfl) ⟨1083599, by rfl⟩ : syracuseStep 1444799 = 2167199) B2167199
theorem B3051593 : Blo 900574 3051593 := bstep (se 2 (by rfl) ⟨1144347, by rfl⟩ : syracuseStep 3051593 = 2288695) B2288695
theorem B3051647 : Blo 900574 3051647 := bstep (se 1 (by rfl) ⟨2288735, by rfl⟩ : syracuseStep 3051647 = 4577471) B4577471
theorem B10293479 : Blo 900574 10293479 := bstep (se 1 (by rfl) ⟨7720109, by rfl⟩ : syracuseStep 10293479 = 15440219) B15440219
theorem B6493085 : Blo 900574 6493085 := bstep (se 3 (by rfl) ⟨1217453, by rfl⟩ : syracuseStep 6493085 = 2434907) B2434907
theorem B4560623 : Blo 900574 4560623 := bstep (se 1 (by rfl) ⟨3420467, by rfl⟩ : syracuseStep 4560623 = 6840935) B6840935
theorem B3217171 : Blo 900574 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B2889533 : Blo 900574 2889533 := bstep (se 3 (by rfl) ⟨541787, by rfl⟩ : syracuseStep 2889533 = 1083575) B1083575
theorem B5151023 : Blo 900574 5151023 := bstep (se 1 (by rfl) ⟨3863267, by rfl⟩ : syracuseStep 5151023 = 7726535) B7726535
theorem B8362777 : Blo 900574 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B7805737 : Blo 900574 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B5479325 : Blo 900574 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B5774399 : Blo 900574 5774399 := bstep (se 1 (by rfl) ⟨4330799, by rfl⟩ : syracuseStep 5774399 = 8661599) B8661599
theorem B22289897 : Blo 900574 22289897 := bstep (se 2 (by rfl) ⟨8358711, by rfl⟩ : syracuseStep 22289897 = 16717423) B16717423
theorem B4398695 : Blo 900574 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B1351487 : Blo 900574 1351487 := bstep (se 1 (by rfl) ⟨1013615, by rfl⟩ : syracuseStep 1351487 = 2027231) B2027231
theorem B2564713 : Blo 900574 2564713 := bstep (se 2 (by rfl) ⟨961767, by rfl⟩ : syracuseStep 2564713 = 1923535) B1923535
theorem B1712801 : Blo 900574 1712801 := bstep (se 2 (by rfl) ⟨642300, by rfl⟩ : syracuseStep 1712801 = 1284601) B1284601
theorem B1352423 : Blo 900574 1352423 := bstep (se 1 (by rfl) ⟨1014317, by rfl⟩ : syracuseStep 1352423 = 2028635) B2028635
theorem B1352447 : Blo 900574 1352447 := bstep (se 1 (by rfl) ⟨1014335, by rfl⟩ : syracuseStep 1352447 = 2028671) B2028671
theorem B1352519 : Blo 900574 1352519 := bstep (se 1 (by rfl) ⟨1014389, by rfl⟩ : syracuseStep 1352519 = 2028779) B2028779
theorem B1352807 : Blo 900574 1352807 := bstep (se 1 (by rfl) ⟨1014605, by rfl⟩ : syracuseStep 1352807 = 2029211) B2029211
theorem B1353191 : Blo 900574 1353191 := bstep (se 1 (by rfl) ⟨1014893, by rfl⟩ : syracuseStep 1353191 = 2029787) B2029787
theorem B1353371 : Blo 900574 1353371 := bstep (se 1 (by rfl) ⟨1015028, by rfl⟩ : syracuseStep 1353371 = 2030057) B2030057
theorem B1714031 : Blo 900574 1714031 := bstep (se 1 (by rfl) ⟨1285523, by rfl⟩ : syracuseStep 1714031 = 2571047) B2571047
theorem B11544443 : Blo 900574 11544443 := bstep (se 1 (by rfl) ⟨8658332, by rfl⟩ : syracuseStep 11544443 = 17316665) B17316665
theorem B6858917 : Blo 900574 6858917 := bstep (se 4 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 6858917 = 1286047) B1286047
theorem B1354175 : Blo 900574 1354175 := bstep (se 1 (by rfl) ⟨1015631, by rfl⟩ : syracuseStep 1354175 = 2031263) B2031263
theorem B6859403 : Blo 900574 6859403 := bstep (se 1 (by rfl) ⟨5144552, by rfl⟩ : syracuseStep 6859403 = 10289105) B10289105
theorem B1354475 : Blo 900574 1354475 := bstep (se 1 (by rfl) ⟨1015856, by rfl⟩ : syracuseStep 1354475 = 2031713) B2031713
theorem B1354505 : Blo 900574 1354505 := bstep (se 2 (by rfl) ⟨507939, by rfl⟩ : syracuseStep 1354505 = 1015879) B1015879
theorem B13380385 : Blo 900574 13380385 := bstep (se 2 (by rfl) ⟨5017644, by rfl⟩ : syracuseStep 13380385 = 10035289) B10035289
theorem B46836701 : Blo 900574 46836701 := bstep (se 3 (by rfl) ⟨8781881, by rfl⟩ : syracuseStep 46836701 = 17563763) B17563763
theorem B3419603 : Blo 900574 3419603 := bstep (se 1 (by rfl) ⟨2564702, by rfl⟩ : syracuseStep 3419603 = 5129405) B5129405
theorem B3419891 : Blo 900574 3419891 := bstep (se 1 (by rfl) ⟨2564918, by rfl⟩ : syracuseStep 3419891 = 5129837) B5129837
theorem B14659375 : Blo 900574 14659375 := bstep (se 1 (by rfl) ⟨10994531, by rfl⟩ : syracuseStep 14659375 = 21989063) B21989063
theorem B3420103 : Blo 900574 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B1716203 : Blo 900574 1716203 := bstep (se 1 (by rfl) ⟨1287152, by rfl⟩ : syracuseStep 1716203 = 2574305) B2574305
theorem B2601175 : Blo 900574 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B1716727 : Blo 900574 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B1356335 : Blo 900574 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B3420863 : Blo 900574 3420863 := bstep (se 1 (by rfl) ⟨2565647, by rfl⟩ : syracuseStep 3420863 = 5131295) B5131295
theorem B1717031 : Blo 900574 1717031 := bstep (se 1 (by rfl) ⟨1287773, by rfl⟩ : syracuseStep 1717031 = 2575547) B2575547
theorem B1356743 : Blo 900574 1356743 := bstep (se 1 (by rfl) ⟨1017557, by rfl⟩ : syracuseStep 1356743 = 2035115) B2035115
theorem B1356767 : Blo 900574 1356767 := bstep (se 1 (by rfl) ⟨1017575, by rfl⟩ : syracuseStep 1356767 = 2035151) B2035151
theorem B6960107 : Blo 900574 6960107 := bstep (se 1 (by rfl) ⟨5220080, by rfl⟩ : syracuseStep 6960107 = 10440161) B10440161
theorem B9779069 : Blo 900574 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B1521659 : Blo 900574 1521659 := bstep (se 1 (by rfl) ⟨1141244, by rfl⟩ : syracuseStep 1521659 = 2282489) B2282489
theorem B4569209 : Blo 900574 4569209 := bstep (se 2 (by rfl) ⟨1713453, by rfl⟩ : syracuseStep 4569209 = 3426907) B3426907
theorem B2570363 : Blo 900574 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B5781881 : Blo 900574 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B6863291 : Blo 900574 6863291 := bstep (se 1 (by rfl) ⟨5147468, by rfl⟩ : syracuseStep 6863291 = 10294937) B10294937
theorem B965407 : Blo 900574 965407 := bstep (se 1 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 965407 = 1448111) B1448111
theorem B2604139 : Blo 900574 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B900591 : Blo 900574 900591 := bstep (se 1 (by rfl) ⟨675443, by rfl⟩ : syracuseStep 900591 = 1350887) B1350887
theorem B120077903 : Blo 900574 120077903 := bstep (se 1 (by rfl) ⟨90058427, by rfl⟩ : syracuseStep 120077903 = 180116855) B180116855
theorem B3849839 : Blo 900574 3849839 := bstep (se 1 (by rfl) ⟨2887379, by rfl⟩ : syracuseStep 3849839 = 5774759) B5774759
theorem B901343 : Blo 900574 901343 := bstep (se 1 (by rfl) ⟨676007, by rfl⟩ : syracuseStep 901343 = 1352015) B1352015
theorem B901359 : Blo 900574 901359 := bstep (se 1 (by rfl) ⟨676019, by rfl⟩ : syracuseStep 901359 = 1352039) B1352039
theorem B10273067 : Blo 900574 10273067 := bstep (se 1 (by rfl) ⟨7704800, by rfl⟩ : syracuseStep 10273067 = 15409601) B15409601
theorem B6865235 : Blo 900574 6865235 := bstep (se 1 (by rfl) ⟨5148926, by rfl⟩ : syracuseStep 6865235 = 10297853) B10297853
theorem B1524251 : Blo 900574 1524251 := bstep (se 1 (by rfl) ⟨1143188, by rfl⟩ : syracuseStep 1524251 = 2286377) B2286377
theorem B901787 : Blo 900574 901787 := bstep (se 1 (by rfl) ⟨676340, by rfl⟩ : syracuseStep 901787 = 1352681) B1352681
theorem B901791 : Blo 900574 901791 := bstep (se 1 (by rfl) ⟨676343, by rfl⟩ : syracuseStep 901791 = 1352687) B1352687
theorem B901823 : Blo 900574 901823 := bstep (se 1 (by rfl) ⟨676367, by rfl⟩ : syracuseStep 901823 = 1352735) B1352735
theorem B902047 : Blo 900574 902047 := bstep (se 1 (by rfl) ⟨676535, by rfl⟩ : syracuseStep 902047 = 1353071) B1353071
theorem B6177707 : Blo 900574 6177707 := bstep (se 1 (by rfl) ⟨4633280, by rfl⟩ : syracuseStep 6177707 = 9266561) B9266561
theorem B902527 : Blo 900574 902527 := bstep (se 1 (by rfl) ⟨676895, by rfl⟩ : syracuseStep 902527 = 1353791) B1353791
theorem B3426407 : Blo 900574 3426407 := bstep (se 1 (by rfl) ⟨2569805, by rfl⟩ : syracuseStep 3426407 = 5139611) B5139611
theorem B66898075 : Blo 900574 66898075 := bstep (se 1 (by rfl) ⟨50173556, by rfl⟩ : syracuseStep 66898075 = 100347113) B100347113
theorem B1526087 : Blo 900574 1526087 := bstep (se 1 (by rfl) ⟨1144565, by rfl⟩ : syracuseStep 1526087 = 2289131) B2289131
theorem B903655 : Blo 900574 903655 := bstep (se 1 (by rfl) ⟨677741, by rfl⟩ : syracuseStep 903655 = 1355483) B1355483
theorem B6507215 : Blo 900574 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B7326845 : Blo 900574 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B904319 : Blo 900574 904319 := bstep (se 1 (by rfl) ⟨678239, by rfl⟩ : syracuseStep 904319 = 1356479) B1356479
theorem B2281193 : Blo 900574 2281193 := bstep (se 2 (by rfl) ⟨855447, by rfl⟩ : syracuseStep 2281193 = 1710895) B1710895
theorem B3658459 : Blo 900574 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B6510131 : Blo 900574 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B2284159 : Blo 900574 2284159 := bstep (se 1 (by rfl) ⟨1713119, by rfl⟩ : syracuseStep 2284159 = 3426239) B3426239
theorem B6511367 : Blo 900574 6511367 := bstep (se 1 (by rfl) ⟨4883525, by rfl⟩ : syracuseStep 6511367 = 9767051) B9767051
theorem B2317625 : Blo 900574 2317625 := bstep (se 2 (by rfl) ⟨869109, by rfl⟩ : syracuseStep 2317625 = 1738219) B1738219
theorem B13000007 : Blo 900574 13000007 := bstep (se 1 (by rfl) ⟨9750005, by rfl⟩ : syracuseStep 13000007 = 19500011) B19500011
theorem B8806087 : Blo 900574 8806087 := bstep (se 1 (by rfl) ⟨6604565, by rfl⟩ : syracuseStep 8806087 = 13209131) B13209131
theorem B6512521 : Blo 900574 6512521 := bstep (se 2 (by rfl) ⟨2442195, by rfl⟩ : syracuseStep 6512521 = 4884391) B4884391
theorem B3040253 : Blo 900574 3040253 := bstep (se 3 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 3040253 = 1140095) B1140095
theorem B842753069 : Blo 900574 842753069 := bstep (se 3 (by rfl) ⟨158016200, by rfl⟩ : syracuseStep 842753069 = 316032401) B316032401
theorem B2286751 : Blo 900574 2286751 := bstep (se 1 (by rfl) ⟨1715063, by rfl⟩ : syracuseStep 2286751 = 3430127) B3430127
theorem B3433985 : Blo 900574 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B3041063 : Blo 900574 3041063 := bstep (se 1 (by rfl) ⟨2280797, by rfl⟩ : syracuseStep 3041063 = 4561595) B4561595
theorem B31647827 : Blo 900574 31647827 := bstep (se 1 (by rfl) ⟨23735870, by rfl⟩ : syracuseStep 31647827 = 47471741) B47471741
theorem B2287835 : Blo 900574 2287835 := bstep (se 1 (by rfl) ⟨1715876, by rfl⟩ : syracuseStep 2287835 = 3431753) B3431753
theorem B17558315 : Blo 900574 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B3042359 : Blo 900574 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B4124087 : Blo 900574 4124087 := bstep (se 1 (by rfl) ⟨3093065, by rfl⟩ : syracuseStep 4124087 = 6186131) B6186131
theorem B3042791 : Blo 900574 3042791 := bstep (se 1 (by rfl) ⟨2282093, by rfl⟩ : syracuseStep 3042791 = 4564187) B4564187
theorem B10284731 : Blo 900574 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B13004621 : Blo 900574 13004621 := bstep (se 3 (by rfl) ⟨2438366, by rfl⟩ : syracuseStep 13004621 = 4876733) B4876733
theorem B2289647 : Blo 900574 2289647 := bstep (se 1 (by rfl) ⟨1717235, by rfl⟩ : syracuseStep 2289647 = 3434471) B3434471
theorem B5140543 : Blo 900574 5140543 := bstep (se 1 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 5140543 = 7710815) B7710815
theorem B2027591 : Blo 900574 2027591 := bstep (se 1 (by rfl) ⟨1520693, by rfl⟩ : syracuseStep 2027591 = 3041387) B3041387
theorem B2027807 : Blo 900574 2027807 := bstep (se 1 (by rfl) ⟨1520855, by rfl⟩ : syracuseStep 2027807 = 3041711) B3041711
theorem B5206781 : Blo 900574 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B1930267 : Blo 900574 1930267 := bstep (se 1 (by rfl) ⟨1447700, by rfl⟩ : syracuseStep 1930267 = 2895401) B2895401
theorem B5862431 : Blo 900574 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B13005953 : Blo 900574 13005953 := bstep (se 2 (by rfl) ⟨4877232, by rfl⟩ : syracuseStep 13005953 = 9754465) B9754465
theorem B2029535 : Blo 900574 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B10975337 : Blo 900574 10975337 := bstep (se 2 (by rfl) ⟨4115751, by rfl⟩ : syracuseStep 10975337 = 8231503) B8231503
theorem B3046409 : Blo 900574 3046409 := bstep (se 2 (by rfl) ⟨1142403, by rfl⟩ : syracuseStep 3046409 = 2284807) B2284807
theorem B3046625 : Blo 900574 3046625 := bstep (se 2 (by rfl) ⟨1142484, by rfl⟩ : syracuseStep 3046625 = 2284969) B2284969
theorem B5144417 : Blo 900574 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B6848711 : Blo 900574 6848711 := bstep (se 1 (by rfl) ⟨5136533, by rfl⟩ : syracuseStep 6848711 = 10273067) B10273067
theorem B1016167 : Blo 900574 1016167 := bstep (se 1 (by rfl) ⟨762125, by rfl⟩ : syracuseStep 1016167 = 1524251) B1524251
theorem B2032127 : Blo 900574 2032127 := bstep (se 1 (by rfl) ⟨1524095, by rfl⟩ : syracuseStep 2032127 = 3048191) B3048191
theorem B3049001 : Blo 900574 3049001 := bstep (se 2 (by rfl) ⟨1143375, by rfl⟩ : syracuseStep 3049001 = 2286751) B2286751
theorem B1017391 : Blo 900574 1017391 := bstep (se 1 (by rfl) ⟨763043, by rfl⟩ : syracuseStep 1017391 = 1526087) B1526087
theorem B2033243 : Blo 900574 2033243 := bstep (se 1 (by rfl) ⟨1524932, by rfl⟩ : syracuseStep 2033243 = 3049865) B3049865
theorem B4884563 : Blo 900574 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B2034395 : Blo 900574 2034395 := bstep (se 1 (by rfl) ⟨1525796, by rfl⟩ : syracuseStep 2034395 = 3051593) B3051593
theorem B2034431 : Blo 900574 2034431 := bstep (se 1 (by rfl) ⟨1525823, by rfl⟩ : syracuseStep 2034431 = 3051647) B3051647
theorem B89197433 : Blo 900574 89197433 := bstep (se 2 (by rfl) ⟨33449037, by rfl⟩ : syracuseStep 89197433 = 66898075) B66898075
theorem B4328723 : Blo 900574 4328723 := bstep (se 1 (by rfl) ⟨3246542, by rfl⟩ : syracuseStep 4328723 = 6493085) B6493085
theorem B2887073 : Blo 900574 2887073 := bstep (se 2 (by rfl) ⟨1082652, by rfl⟩ : syracuseStep 2887073 = 2165305) B2165305
theorem B1545083 : Blo 900574 1545083 := bstep (se 1 (by rfl) ⟨1158812, by rfl⟩ : syracuseStep 1545083 = 2317625) B2317625
theorem B4560137 : Blo 900574 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B6854057 : Blo 900574 6854057 := bstep (se 2 (by rfl) ⟨2570271, by rfl⟩ : syracuseStep 6854057 = 5140543) B5140543
theorem B11705543 : Blo 900574 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B6856487 : Blo 900574 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B1351727 : Blo 900574 1351727 := bstep (se 1 (by rfl) ⟨1013795, by rfl⟩ : syracuseStep 1351727 = 2027591) B2027591
theorem B1351871 : Blo 900574 1351871 := bstep (se 1 (by rfl) ⟨1013903, by rfl⟩ : syracuseStep 1351871 = 2027807) B2027807
theorem B3908287 : Blo 900574 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B11150369 : Blo 900574 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B1287209 : Blo 900574 1287209 := bstep (se 2 (by rfl) ⟨482703, by rfl⟩ : syracuseStep 1287209 = 965407) B965407
theorem B1353023 : Blo 900574 1353023 := bstep (se 1 (by rfl) ⟨1014767, by rfl⟩ : syracuseStep 1353023 = 2029535) B2029535
theorem B7316891 : Blo 900574 7316891 := bstep (se 1 (by rfl) ⟨5487668, by rfl⟩ : syracuseStep 7316891 = 10975337) B10975337
theorem B1713575 : Blo 900574 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B11741449 : Blo 900574 11741449 := bstep (se 2 (by rfl) ⟨4403043, by rfl⟩ : syracuseStep 11741449 = 8806087) B8806087
theorem B2566559 : Blo 900574 2566559 := bstep (se 1 (by rfl) ⟨1924919, by rfl⟩ : syracuseStep 2566559 = 3849839) B3849839
theorem B1354523 : Blo 900574 1354523 := bstep (se 1 (by rfl) ⟨1015892, by rfl⟩ : syracuseStep 1354523 = 2031785) B2031785
theorem B3419617 : Blo 900574 3419617 := bstep (se 2 (by rfl) ⟨1282356, by rfl⟩ : syracuseStep 3419617 = 2564713) B2564713
theorem B1355375 : Blo 900574 1355375 := bstep (se 1 (by rfl) ⟨1016531, by rfl⟩ : syracuseStep 1355375 = 2033063) B2033063
theorem B1355423 : Blo 900574 1355423 := bstep (se 1 (by rfl) ⟨1016567, by rfl⟩ : syracuseStep 1355423 = 2033135) B2033135
theorem B1355807 : Blo 900574 1355807 := bstep (se 1 (by rfl) ⟨1016855, by rfl⟩ : syracuseStep 1355807 = 2033711) B2033711
theorem B4567103 : Blo 900574 4567103 := bstep (se 1 (by rfl) ⟨3425327, by rfl⟩ : syracuseStep 4567103 = 6850655) B6850655
theorem B1356155 : Blo 900574 1356155 := bstep (se 1 (by rfl) ⟨1017116, by rfl⟩ : syracuseStep 1356155 = 2034233) B2034233
theorem B4338143 : Blo 900574 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B963199 : Blo 900574 963199 := bstep (se 1 (by rfl) ⟨722399, by rfl⟩ : syracuseStep 963199 = 1444799) B1444799
theorem B1520795 : Blo 900574 1520795 := bstep (se 1 (by rfl) ⟨1140596, by rfl⟩ : syracuseStep 1520795 = 2281193) B2281193
theorem B18560285 : Blo 900574 18560285 := bstep (se 3 (by rfl) ⟨3480053, by rfl⟩ : syracuseStep 18560285 = 6960107) B6960107
theorem B6862319 : Blo 900574 6862319 := bstep (se 1 (by rfl) ⟨5146739, by rfl⟩ : syracuseStep 6862319 = 10293479) B10293479
theorem B4340087 : Blo 900574 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B17840513 : Blo 900574 17840513 := bstep (se 2 (by rfl) ⟨6690192, by rfl⟩ : syracuseStep 17840513 = 13380385) B13380385
theorem B4340911 : Blo 900574 4340911 := bstep (se 1 (by rfl) ⟨3255683, by rfl⟩ : syracuseStep 4340911 = 6511367) B6511367
theorem B3652883 : Blo 900574 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B3849599 : Blo 900574 3849599 := bstep (se 1 (by rfl) ⟨2887199, by rfl⟩ : syracuseStep 3849599 = 5774399) B5774399
theorem B8666671 : Blo 900574 8666671 := bstep (se 1 (by rfl) ⟨6500003, by rfl⟩ : syracuseStep 8666671 = 13000007) B13000007
theorem B14859931 : Blo 900574 14859931 := bstep (se 1 (by rfl) ⟨11144948, by rfl⟩ : syracuseStep 14859931 = 22289897) B22289897
theorem B19545833 : Blo 900574 19545833 := bstep (se 2 (by rfl) ⟨7329687, by rfl⟩ : syracuseStep 19545833 = 14659375) B14659375
theorem B2932463 : Blo 900574 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B900991 : Blo 900574 900991 := bstep (se 1 (by rfl) ⟨675743, by rfl⟩ : syracuseStep 900991 = 1351487) B1351487
theorem B901615 : Blo 900574 901615 := bstep (se 1 (by rfl) ⟨676211, by rfl⟩ : syracuseStep 901615 = 1352423) B1352423
theorem B901631 : Blo 900574 901631 := bstep (se 1 (by rfl) ⟨676223, by rfl⟩ : syracuseStep 901631 = 1352447) B1352447
theorem B901679 : Blo 900574 901679 := bstep (se 1 (by rfl) ⟨676259, by rfl⟩ : syracuseStep 901679 = 1352519) B1352519
theorem B901871 : Blo 900574 901871 := bstep (se 1 (by rfl) ⟨676403, by rfl⟩ : syracuseStep 901871 = 1352807) B1352807
theorem B15418349 : Blo 900574 15418349 := bstep (se 3 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 15418349 = 5781881) B5781881
theorem B902127 : Blo 900574 902127 := bstep (se 1 (by rfl) ⟨676595, by rfl⟩ : syracuseStep 902127 = 1353191) B1353191
theorem B902247 : Blo 900574 902247 := bstep (se 1 (by rfl) ⟨676685, by rfl⟩ : syracuseStep 902247 = 1353371) B1353371
theorem B2573689 : Blo 900574 2573689 := bstep (se 2 (by rfl) ⟨965133, by rfl⟩ : syracuseStep 2573689 = 1930267) B1930267
theorem B4572611 : Blo 900574 4572611 := bstep (se 1 (by rfl) ⟨3429458, by rfl⟩ : syracuseStep 4572611 = 6858917) B6858917
theorem B1525223 : Blo 900574 1525223 := bstep (se 1 (by rfl) ⟨1143917, by rfl⟩ : syracuseStep 1525223 = 2287835) B2287835
theorem B902783 : Blo 900574 902783 := bstep (se 1 (by rfl) ⟨677087, by rfl⟩ : syracuseStep 902783 = 1354175) B1354175
theorem B4572935 : Blo 900574 4572935 := bstep (se 1 (by rfl) ⟨3429701, by rfl⟩ : syracuseStep 4572935 = 6859403) B6859403
theorem B902983 : Blo 900574 902983 := bstep (se 1 (by rfl) ⟨677237, by rfl⟩ : syracuseStep 902983 = 1354475) B1354475
theorem B903003 : Blo 900574 903003 := bstep (se 1 (by rfl) ⟨677252, by rfl⟩ : syracuseStep 903003 = 1354505) B1354505
theorem B13027229 : Blo 900574 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B2279735 : Blo 900574 2279735 := bstep (se 1 (by rfl) ⟨1709801, by rfl⟩ : syracuseStep 2279735 = 3419603) B3419603
theorem B2279927 : Blo 900574 2279927 := bstep (se 1 (by rfl) ⟨1709945, by rfl⟩ : syracuseStep 2279927 = 3419891) B3419891
theorem B8669747 : Blo 900574 8669747 := bstep (se 1 (by rfl) ⟨6502310, by rfl⟩ : syracuseStep 8669747 = 13004621) B13004621
theorem B1526431 : Blo 900574 1526431 := bstep (se 1 (by rfl) ⟨1144823, by rfl⟩ : syracuseStep 1526431 = 2289647) B2289647
theorem B904223 : Blo 900574 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B2280575 : Blo 900574 2280575 := bstep (se 1 (by rfl) ⟨1710431, by rfl⟩ : syracuseStep 2280575 = 3420863) B3420863
theorem B904495 : Blo 900574 904495 := bstep (se 1 (by rfl) ⟨678371, by rfl⟩ : syracuseStep 904495 = 1356743) B1356743
theorem B904511 : Blo 900574 904511 := bstep (se 1 (by rfl) ⟨678383, by rfl⟩ : syracuseStep 904511 = 1356767) B1356767
theorem B8670635 : Blo 900574 8670635 := bstep (se 1 (by rfl) ⟨6502976, by rfl⟩ : syracuseStep 8670635 = 13005953) B13005953
theorem B10407649 : Blo 900574 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B4575527 : Blo 900574 4575527 := bstep (se 1 (by rfl) ⟨3431645, by rfl⟩ : syracuseStep 4575527 = 6863291) B6863291
theorem B3429611 : Blo 900574 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B4576823 : Blo 900574 4576823 := bstep (se 1 (by rfl) ⟨3432617, by rfl⟩ : syracuseStep 4576823 = 6865235) B6865235
theorem B83187587 : Blo 900574 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B4118471 : Blo 900574 4118471 := bstep (se 1 (by rfl) ⟨3088853, by rfl⟩ : syracuseStep 4118471 = 6177707) B6177707
theorem B2284271 : Blo 900574 2284271 := bstep (se 1 (by rfl) ⟨1713203, by rfl⟩ : syracuseStep 2284271 = 3426407) B3426407
theorem B3040415 : Blo 900574 3040415 := bstep (se 1 (by rfl) ⟨2280311, by rfl⟩ : syracuseStep 3040415 = 4560623) B4560623
theorem B1926355 : Blo 900574 1926355 := bstep (se 1 (by rfl) ⟨1444766, by rfl⟩ : syracuseStep 1926355 = 2889533) B2889533
theorem B3434015 : Blo 900574 3434015 := bstep (se 1 (by rfl) ⟨2575511, by rfl⟩ : syracuseStep 3434015 = 5151023) B5151023
theorem B3468233 : Blo 900574 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B1141867 : Blo 900574 1141867 := bstep (se 1 (by rfl) ⟨856400, by rfl⟩ : syracuseStep 1141867 = 1712801) B1712801
theorem B13888741 : Blo 900574 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B2288969 : Blo 900574 2288969 := bstep (se 2 (by rfl) ⟨858363, by rfl⟩ : syracuseStep 2288969 = 1716727) B1716727
theorem B2026835 : Blo 900574 2026835 := bstep (se 1 (by rfl) ⟨1520126, by rfl⟩ : syracuseStep 2026835 = 3040253) B3040253
theorem B561835379 : Blo 900574 561835379 := bstep (se 1 (by rfl) ⟨421376534, by rfl⟩ : syracuseStep 561835379 = 842753069) B842753069
theorem B4877945 : Blo 900574 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B2289323 : Blo 900574 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B2027375 : Blo 900574 2027375 := bstep (se 1 (by rfl) ⟨1520531, by rfl⟩ : syracuseStep 2027375 = 3041063) B3041063
theorem B1142687 : Blo 900574 1142687 := bstep (se 1 (by rfl) ⟨857015, by rfl⟩ : syracuseStep 1142687 = 1714031) B1714031
theorem B7696295 : Blo 900574 7696295 := bstep (se 1 (by rfl) ⟨5772221, by rfl⟩ : syracuseStep 7696295 = 11544443) B11544443
theorem B21098551 : Blo 900574 21098551 := bstep (se 1 (by rfl) ⟨15823913, by rfl⟩ : syracuseStep 21098551 = 31647827) B31647827
theorem B31224467 : Blo 900574 31224467 := bstep (se 1 (by rfl) ⟨23418350, by rfl⟩ : syracuseStep 31224467 = 46836701) B46836701
theorem B2028239 : Blo 900574 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B2749391 : Blo 900574 2749391 := bstep (se 1 (by rfl) ⟨2062043, by rfl⟩ : syracuseStep 2749391 = 4124087) B4124087
theorem B2028527 : Blo 900574 2028527 := bstep (se 1 (by rfl) ⟨1521395, by rfl⟩ : syracuseStep 2028527 = 3042791) B3042791
theorem B4289561 : Blo 900574 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B1144135 : Blo 900574 1144135 := bstep (se 1 (by rfl) ⟨858101, by rfl⟩ : syracuseStep 1144135 = 1716203) B1716203
theorem B3471187 : Blo 900574 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B1144687 : Blo 900574 1144687 := bstep (se 1 (by rfl) ⟨858515, by rfl⟩ : syracuseStep 1144687 = 1717031) B1717031
theorem B3045545 : Blo 900574 3045545 := bstep (se 2 (by rfl) ⟨1142079, by rfl⟩ : syracuseStep 3045545 = 2284159) B2284159
theorem B6519379 : Blo 900574 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B1014439 : Blo 900574 1014439 := bstep (se 1 (by rfl) ⟨760829, by rfl⟩ : syracuseStep 1014439 = 1521659) B1521659
theorem B3046139 : Blo 900574 3046139 := bstep (se 1 (by rfl) ⟨2284604, by rfl⟩ : syracuseStep 3046139 = 4569209) B4569209
theorem B2030939 : Blo 900574 2030939 := bstep (se 1 (by rfl) ⟨1523204, by rfl⟩ : syracuseStep 2030939 = 3046409) B3046409
theorem B2031083 : Blo 900574 2031083 := bstep (se 1 (by rfl) ⟨1523312, by rfl⟩ : syracuseStep 2031083 = 3046625) B3046625
theorem B80051935 : Blo 900574 80051935 := bstep (se 1 (by rfl) ⟨60038951, by rfl⟩ : syracuseStep 80051935 = 120077903) B120077903
theorem B8683361 : Blo 900574 8683361 := bstep (se 2 (by rfl) ⟨3256260, by rfl⟩ : syracuseStep 8683361 = 6512521) B6512521
theorem B5211049 : Blo 900574 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B3048407 : Blo 900574 3048407 := bstep (se 1 (by rfl) ⟨2286305, by rfl⟩ : syracuseStep 3048407 = 4572611) B4572611
theorem B1016815 : Blo 900574 1016815 := bstep (se 1 (by rfl) ⟨762611, by rfl⟩ : syracuseStep 1016815 = 1525223) B1525223
theorem B2032667 : Blo 900574 2032667 := bstep (se 1 (by rfl) ⟨1524500, by rfl⟩ : syracuseStep 2032667 = 3049001) B3049001
theorem B3048623 : Blo 900574 3048623 := bstep (se 1 (by rfl) ⟨2286467, by rfl⟩ : syracuseStep 3048623 = 4572935) B4572935
theorem B8684819 : Blo 900574 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B2885815 : Blo 900574 2885815 := bstep (se 1 (by rfl) ⟨2164361, by rfl⟩ : syracuseStep 2885815 = 4328723) B4328723
theorem B3050351 : Blo 900574 3050351 := bstep (se 1 (by rfl) ⟨2287763, by rfl⟩ : syracuseStep 3050351 = 4575527) B4575527
theorem B2035241 : Blo 900574 2035241 := bstep (se 2 (by rfl) ⟨763215, by rfl⟩ : syracuseStep 2035241 = 1526431) B1526431
theorem B3051215 : Blo 900574 3051215 := bstep (se 1 (by rfl) ⟨2288411, by rfl⟩ : syracuseStep 3051215 = 4576823) B4576823
theorem B18518321 : Blo 900574 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B4559489 : Blo 900574 4559489 := bstep (se 2 (by rfl) ⟨1709808, by rfl⟩ : syracuseStep 4559489 = 3419617) B3419617
theorem B7803695 : Blo 900574 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B1284265 : Blo 900574 1284265 := bstep (se 2 (by rfl) ⟨481599, by rfl⟩ : syracuseStep 1284265 = 963199) B963199
theorem B1711039 : Blo 900574 1711039 := bstep (se 1 (by rfl) ⟨1283279, by rfl⟩ : syracuseStep 1711039 = 2566559) B2566559
theorem B1351223 : Blo 900574 1351223 := bstep (se 1 (by rfl) ⟨1013417, by rfl⟩ : syracuseStep 1351223 = 2026835) B2026835
theorem B3251963 : Blo 900574 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B4628249 : Blo 900574 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B1351583 : Blo 900574 1351583 := bstep (se 1 (by rfl) ⟨1013687, by rfl⟩ : syracuseStep 1351583 = 2027375) B2027375
theorem B2892095 : Blo 900574 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B20816311 : Blo 900574 20816311 := bstep (se 1 (by rfl) ⟨15612233, by rfl⟩ : syracuseStep 20816311 = 31224467) B31224467
theorem B1352159 : Blo 900574 1352159 := bstep (se 1 (by rfl) ⟨1014119, by rfl⟩ : syracuseStep 1352159 = 2028239) B2028239
theorem B1352351 : Blo 900574 1352351 := bstep (se 1 (by rfl) ⟨1014263, by rfl⟩ : syracuseStep 1352351 = 2028527) B2028527
theorem B2859707 : Blo 900574 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B8692505 : Blo 900574 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B1352585 : Blo 900574 1352585 := bstep (se 2 (by rfl) ⟨507219, by rfl⟩ : syracuseStep 1352585 = 1014439) B1014439
theorem B1498227677 : Blo 900574 1498227677 := bstep (se 3 (by rfl) ⟨280917689, by rfl⟩ : syracuseStep 1498227677 = 561835379) B561835379
theorem B2893391 : Blo 900574 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B2435255 : Blo 900574 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B1353959 : Blo 900574 1353959 := bstep (se 1 (by rfl) ⟨1015469, by rfl⟩ : syracuseStep 1353959 = 2030939) B2030939
theorem B2566399 : Blo 900574 2566399 := bstep (se 1 (by rfl) ⟨1924799, by rfl⟩ : syracuseStep 2566399 = 3849599) B3849599
theorem B106735913 : Blo 900574 106735913 := bstep (se 2 (by rfl) ⟨40025967, by rfl⟩ : syracuseStep 106735913 = 80051935) B80051935
theorem B1354055 : Blo 900574 1354055 := bstep (se 1 (by rfl) ⟨1015541, by rfl⟩ : syracuseStep 1354055 = 2031083) B2031083
theorem B4565807 : Blo 900574 4565807 := bstep (se 1 (by rfl) ⟨3424355, by rfl⟩ : syracuseStep 4565807 = 6848711) B6848711
theorem B1354751 : Blo 900574 1354751 := bstep (se 1 (by rfl) ⟨1016063, by rfl⟩ : syracuseStep 1354751 = 2032127) B2032127
theorem B1354889 : Blo 900574 1354889 := bstep (se 2 (by rfl) ⟨508083, by rfl⟩ : syracuseStep 1354889 = 1016167) B1016167
theorem B1355495 : Blo 900574 1355495 := bstep (se 1 (by rfl) ⟨1016621, by rfl⟩ : syracuseStep 1355495 = 2033243) B2033243
theorem B3256375 : Blo 900574 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B1519823 : Blo 900574 1519823 := bstep (se 1 (by rfl) ⟨1139867, by rfl⟩ : syracuseStep 1519823 = 2279735) B2279735
theorem B2568473 : Blo 900574 2568473 := bstep (se 2 (by rfl) ⟨963177, by rfl⟩ : syracuseStep 2568473 = 1926355) B1926355
theorem B1519951 : Blo 900574 1519951 := bstep (se 1 (by rfl) ⟨1139963, by rfl⟩ : syracuseStep 1519951 = 2279927) B2279927
theorem B5779831 : Blo 900574 5779831 := bstep (se 1 (by rfl) ⟨4334873, by rfl⟩ : syracuseStep 5779831 = 8669747) B8669747
theorem B1356263 : Blo 900574 1356263 := bstep (se 1 (by rfl) ⟨1017197, by rfl⟩ : syracuseStep 1356263 = 2034395) B2034395
theorem B1356287 : Blo 900574 1356287 := bstep (se 1 (by rfl) ⟨1017215, by rfl⟩ : syracuseStep 1356287 = 2034431) B2034431
theorem B1356521 : Blo 900574 1356521 := bstep (se 2 (by rfl) ⟨508695, by rfl⟩ : syracuseStep 1356521 = 1017391) B1017391
theorem B1520383 : Blo 900574 1520383 := bstep (se 1 (by rfl) ⟨1140287, by rfl⟩ : syracuseStep 1520383 = 2280575) B2280575
theorem B5780423 : Blo 900574 5780423 := bstep (se 1 (by rfl) ⟨4335317, by rfl⟩ : syracuseStep 5780423 = 8670635) B8670635
theorem B1030055 : Blo 900574 1030055 := bstep (se 1 (by rfl) ⟨772541, by rfl⟩ : syracuseStep 1030055 = 1545083) B1545083
theorem B4569371 : Blo 900574 4569371 := bstep (se 1 (by rfl) ⟨3427028, by rfl⟩ : syracuseStep 4569371 = 6854057) B6854057
theorem B4569533 : Blo 900574 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B55458391 : Blo 900574 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B1522489 : Blo 900574 1522489 := bstep (se 2 (by rfl) ⟨570933, by rfl⟩ : syracuseStep 1522489 = 1141867) B1141867
theorem B1522847 : Blo 900574 1522847 := bstep (se 1 (by rfl) ⟨1142135, by rfl⟩ : syracuseStep 1522847 = 2284271) B2284271
theorem B13876865 : Blo 900574 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B4570991 : Blo 900574 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B901151 : Blo 900574 901151 := bstep (se 1 (by rfl) ⟨675863, by rfl⟩ : syracuseStep 901151 = 1351727) B1351727
theorem B28131401 : Blo 900574 28131401 := bstep (se 2 (by rfl) ⟨10549275, by rfl⟩ : syracuseStep 28131401 = 21098551) B21098551
theorem B901247 : Blo 900574 901247 := bstep (se 1 (by rfl) ⟨675935, by rfl⟩ : syracuseStep 901247 = 1351871) B1351871
theorem B902015 : Blo 900574 902015 := bstep (se 1 (by rfl) ⟨676511, by rfl⟩ : syracuseStep 902015 = 1353023) B1353023
theorem B1525513 : Blo 900574 1525513 := bstep (se 2 (by rfl) ⟨572067, by rfl⟩ : syracuseStep 1525513 = 1144135) B1144135
theorem B903015 : Blo 900574 903015 := bstep (se 1 (by rfl) ⟨677261, by rfl⟩ : syracuseStep 903015 = 1354523) B1354523
theorem B2312155 : Blo 900574 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B1525979 : Blo 900574 1525979 := bstep (se 1 (by rfl) ⟨1144484, by rfl⟩ : syracuseStep 1525979 = 2288969) B2288969
theorem B903583 : Blo 900574 903583 := bstep (se 1 (by rfl) ⟨677687, by rfl⟩ : syracuseStep 903583 = 1355375) B1355375
theorem B903615 : Blo 900574 903615 := bstep (se 1 (by rfl) ⟨677711, by rfl⟩ : syracuseStep 903615 = 1355423) B1355423
theorem B1526215 : Blo 900574 1526215 := bstep (se 1 (by rfl) ⟨1144661, by rfl⟩ : syracuseStep 1526215 = 2289323) B2289323
theorem B1526249 : Blo 900574 1526249 := bstep (se 2 (by rfl) ⟨572343, by rfl⟩ : syracuseStep 1526249 = 1144687) B1144687
theorem B5130863 : Blo 900574 5130863 := bstep (se 1 (by rfl) ⟨3848147, by rfl⟩ : syracuseStep 5130863 = 7696295) B7696295
theorem B903871 : Blo 900574 903871 := bstep (se 1 (by rfl) ⟨677903, by rfl⟩ : syracuseStep 903871 = 1355807) B1355807
theorem B904103 : Blo 900574 904103 := bstep (se 1 (by rfl) ⟨678077, by rfl⟩ : syracuseStep 904103 = 1356155) B1356155
theorem B12373523 : Blo 900574 12373523 := bstep (se 1 (by rfl) ⟨9280142, by rfl⟩ : syracuseStep 12373523 = 18560285) B18560285
theorem B4574879 : Blo 900574 4574879 := bstep (se 1 (by rfl) ⟨3431159, by rfl⟩ : syracuseStep 4574879 = 6862319) B6862319
theorem B5787881 : Blo 900574 5787881 := bstep (se 2 (by rfl) ⟨2170455, by rfl⟩ : syracuseStep 5787881 = 4340911) B4340911
theorem B7819901 : Blo 900574 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B11555561 : Blo 900574 11555561 := bstep (se 2 (by rfl) ⟨4333335, by rfl⟩ : syracuseStep 11555561 = 8666671) B8666671
theorem B19813241 : Blo 900574 19813241 := bstep (se 2 (by rfl) ⟨7429965, by rfl⟩ : syracuseStep 19813241 = 14859931) B14859931
theorem B13030555 : Blo 900574 13030555 := bstep (se 1 (by rfl) ⟨9772916, by rfl⟩ : syracuseStep 13030555 = 19545833) B19545833
theorem B5788907 : Blo 900574 5788907 := bstep (se 1 (by rfl) ⟨4341680, by rfl⟩ : syracuseStep 5788907 = 8683361) B8683361
theorem B10278899 : Blo 900574 10278899 := bstep (se 1 (by rfl) ⟨7709174, by rfl⟩ : syracuseStep 10278899 = 15418349) B15418349
theorem B3431585 : Blo 900574 3431585 := bstep (se 2 (by rfl) ⟨1286844, by rfl⟩ : syracuseStep 3431585 = 2573689) B2573689
theorem B59464955 : Blo 900574 59464955 := bstep (se 1 (by rfl) ⟨44598716, by rfl⟩ : syracuseStep 59464955 = 89197433) B89197433
theorem B1924715 : Blo 900574 1924715 := bstep (se 1 (by rfl) ⟨1443536, by rfl⟩ : syracuseStep 1924715 = 2887073) B2887073
theorem B3432557 : Blo 900574 3432557 := bstep (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) B1287209
theorem B15655265 : Blo 900574 15655265 := bstep (se 2 (by rfl) ⟨5870724, by rfl⟩ : syracuseStep 15655265 = 11741449) B11741449
theorem B2286407 : Blo 900574 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B3040091 : Blo 900574 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B2745647 : Blo 900574 2745647 := bstep (se 1 (by rfl) ⟨2059235, by rfl⟩ : syracuseStep 2745647 = 4118471) B4118471
theorem B7433579 : Blo 900574 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B2026943 : Blo 900574 2026943 := bstep (se 1 (by rfl) ⟨1520207, by rfl⟩ : syracuseStep 2026943 = 3040415) B3040415
theorem B4877927 : Blo 900574 4877927 := bstep (se 1 (by rfl) ⟨3658445, by rfl⟩ : syracuseStep 4877927 = 7316891) B7316891
theorem B47574701 : Blo 900574 47574701 := bstep (se 3 (by rfl) ⟨8920256, by rfl⟩ : syracuseStep 47574701 = 17840513) B17840513
theorem B2289343 : Blo 900574 2289343 := bstep (se 1 (by rfl) ⟨1717007, by rfl⟩ : syracuseStep 2289343 = 3434015) B3434015
theorem B3044735 : Blo 900574 3044735 := bstep (se 1 (by rfl) ⟨2283551, by rfl⟩ : syracuseStep 3044735 = 4567103) B4567103
theorem B1832927 : Blo 900574 1832927 := bstep (se 1 (by rfl) ⟨1374695, by rfl⟩ : syracuseStep 1832927 = 2749391) B2749391
theorem B1013863 : Blo 900574 1013863 := bstep (se 1 (by rfl) ⟨760397, by rfl⟩ : syracuseStep 1013863 = 1520795) B1520795
theorem B2030363 : Blo 900574 2030363 := bstep (se 1 (by rfl) ⟨1522772, by rfl⟩ : syracuseStep 2030363 = 3045545) B3045545
theorem B2030759 : Blo 900574 2030759 := bstep (se 1 (by rfl) ⟨1523069, by rfl⟩ : syracuseStep 2030759 = 3046139) B3046139
theorem B3047165 : Blo 900574 3047165 := bstep (se 3 (by rfl) ⟨571343, by rfl⟩ : syracuseStep 3047165 = 1142687) B1142687
theorem B27755081 : Blo 900574 27755081 := bstep (se 2 (by rfl) ⟨10408155, by rfl⟩ : syracuseStep 27755081 = 20816311) B20816311
theorem B2032271 : Blo 900574 2032271 := bstep (se 1 (by rfl) ⟨1524203, by rfl⟩ : syracuseStep 2032271 = 3048407) B3048407
theorem B2032415 : Blo 900574 2032415 := bstep (se 1 (by rfl) ⟨1524311, by rfl⟩ : syracuseStep 2032415 = 3048623) B3048623
theorem B6948065 : Blo 900574 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B1017319 : Blo 900574 1017319 := bstep (se 1 (by rfl) ⟨762989, by rfl⟩ : syracuseStep 1017319 = 1525979) B1525979
theorem B1017499 : Blo 900574 1017499 := bstep (se 1 (by rfl) ⟨763124, by rfl⟩ : syracuseStep 1017499 = 1526249) B1526249
theorem B2033567 : Blo 900574 2033567 := bstep (se 1 (by rfl) ⟨1525175, by rfl⟩ : syracuseStep 2033567 = 3050351) B3050351
theorem B2034017 : Blo 900574 2034017 := bstep (se 2 (by rfl) ⟨762756, by rfl⟩ : syracuseStep 2034017 = 1525513) B1525513
theorem B3049919 : Blo 900574 3049919 := bstep (se 1 (by rfl) ⟨2287439, by rfl⟩ : syracuseStep 3049919 = 4574879) B4574879
theorem B2034143 : Blo 900574 2034143 := bstep (se 1 (by rfl) ⟨1525607, by rfl⟩ : syracuseStep 2034143 = 3051215) B3051215
theorem B3082873 : Blo 900574 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B5213267 : Blo 900574 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B7703707 : Blo 900574 7703707 := bstep (se 1 (by rfl) ⟨5777780, by rfl⟩ : syracuseStep 7703707 = 11555561) B11555561
theorem B13208827 : Blo 900574 13208827 := bstep (se 1 (by rfl) ⟨9906620, by rfl⟩ : syracuseStep 13208827 = 19813241) B19813241
theorem B2034953 : Blo 900574 2034953 := bstep (se 2 (by rfl) ⟨763107, by rfl⟩ : syracuseStep 2034953 = 1526215) B1526215
theorem B6852599 : Blo 900574 6852599 := bstep (se 1 (by rfl) ⟨5139449, by rfl⟩ : syracuseStep 6852599 = 10278899) B10278899
theorem B3052457 : Blo 900574 3052457 := bstep (se 2 (by rfl) ⟨1144671, by rfl⟩ : syracuseStep 3052457 = 2289343) B2289343
theorem B1283143 : Blo 900574 1283143 := bstep (se 1 (by rfl) ⟨962357, by rfl⟩ : syracuseStep 1283143 = 1924715) B1924715
theorem B2167975 : Blo 900574 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B3085499 : Blo 900574 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B4887805 : Blo 900574 4887805 := bstep (se 3 (by rfl) ⟨916463, by rfl⟩ : syracuseStep 4887805 = 1832927) B1832927
theorem B1906471 : Blo 900574 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B7706441 : Blo 900574 7706441 := bstep (se 2 (by rfl) ⟨2889915, by rfl⟩ : syracuseStep 7706441 = 5779831) B5779831
theorem B17374073 : Blo 900574 17374073 := bstep (se 2 (by rfl) ⟨6515277, by rfl⟩ : syracuseStep 17374073 = 13030555) B13030555
theorem B1351295 : Blo 900574 1351295 := bstep (se 1 (by rfl) ⟨1013471, by rfl⟩ : syracuseStep 1351295 = 2026943) B2026943
theorem B3251951 : Blo 900574 3251951 := bstep (se 1 (by rfl) ⟨2438963, by rfl⟩ : syracuseStep 3251951 = 4877927) B4877927
theorem B1351817 : Blo 900574 1351817 := bstep (se 2 (by rfl) ⟨506931, by rfl⟩ : syracuseStep 1351817 = 1013863) B1013863
theorem B1712315 : Blo 900574 1712315 := bstep (se 1 (by rfl) ⟨1284236, by rfl⟩ : syracuseStep 1712315 = 2568473) B2568473
theorem B1712353 : Blo 900574 1712353 := bstep (se 2 (by rfl) ⟨642132, by rfl⟩ : syracuseStep 1712353 = 1284265) B1284265
theorem B1353575 : Blo 900574 1353575 := bstep (se 1 (by rfl) ⟨1015181, by rfl⟩ : syracuseStep 1353575 = 2030363) B2030363
theorem B1353839 : Blo 900574 1353839 := bstep (se 1 (by rfl) ⟨1015379, by rfl⟩ : syracuseStep 1353839 = 2030759) B2030759
theorem B9251243 : Blo 900574 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B18754267 : Blo 900574 18754267 := bstep (se 1 (by rfl) ⟨14065700, by rfl⟩ : syracuseStep 18754267 = 28131401) B28131401
theorem B1355111 : Blo 900574 1355111 := bstep (se 1 (by rfl) ⟨1016333, by rfl⟩ : syracuseStep 1355111 = 2032667) B2032667
theorem B1355753 : Blo 900574 1355753 := bstep (se 2 (by rfl) ⟨508407, by rfl⟩ : syracuseStep 1355753 = 1016815) B1016815
theorem B3420575 : Blo 900574 3420575 := bstep (se 1 (by rfl) ⟨2565431, by rfl⟩ : syracuseStep 3420575 = 5130863) B5130863
theorem B1356827 : Blo 900574 1356827 := bstep (se 1 (by rfl) ⟨1017620, by rfl⟩ : syracuseStep 1356827 = 2035241) B2035241
theorem B3847753 : Blo 900574 3847753 := bstep (se 2 (by rfl) ⟨1442907, by rfl⟩ : syracuseStep 3847753 = 2885815) B2885815
theorem B3421865 : Blo 900574 3421865 := bstep (se 2 (by rfl) ⟨1283199, by rfl⟩ : syracuseStep 3421865 = 2566399) B2566399
theorem B900815 : Blo 900574 900815 := bstep (se 1 (by rfl) ⟨675611, by rfl⟩ : syracuseStep 900815 = 1351223) B1351223
theorem B901055 : Blo 900574 901055 := bstep (se 1 (by rfl) ⟨675791, by rfl⟩ : syracuseStep 901055 = 1351583) B1351583
theorem B4341833 : Blo 900574 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B10436843 : Blo 900574 10436843 := bstep (se 1 (by rfl) ⟨7827632, by rfl⟩ : syracuseStep 10436843 = 15655265) B15655265
theorem B901439 : Blo 900574 901439 := bstep (se 1 (by rfl) ⟨676079, by rfl⟩ : syracuseStep 901439 = 1352159) B1352159
theorem B901567 : Blo 900574 901567 := bstep (se 1 (by rfl) ⟨676175, by rfl⟩ : syracuseStep 901567 = 1352351) B1352351
theorem B1524271 : Blo 900574 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B901723 : Blo 900574 901723 := bstep (se 1 (by rfl) ⟨676292, by rfl⟩ : syracuseStep 901723 = 1352585) B1352585
theorem B998818451 : Blo 900574 998818451 := bstep (se 1 (by rfl) ⟨749113838, by rfl⟩ : syracuseStep 998818451 = 1498227677) B1498227677
theorem B1623503 : Blo 900574 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B902639 : Blo 900574 902639 := bstep (se 1 (by rfl) ⟨676979, by rfl⟩ : syracuseStep 902639 = 1353959) B1353959
theorem B71157275 : Blo 900574 71157275 := bstep (se 1 (by rfl) ⟨53367956, by rfl⟩ : syracuseStep 71157275 = 106735913) B106735913
theorem B902703 : Blo 900574 902703 := bstep (se 1 (by rfl) ⟨677027, by rfl⟩ : syracuseStep 902703 = 1354055) B1354055
theorem B903167 : Blo 900574 903167 := bstep (se 1 (by rfl) ⟨677375, by rfl⟩ : syracuseStep 903167 = 1354751) B1354751
theorem B903259 : Blo 900574 903259 := bstep (se 1 (by rfl) ⟨677444, by rfl⟩ : syracuseStep 903259 = 1354889) B1354889
theorem B903663 : Blo 900574 903663 := bstep (se 1 (by rfl) ⟨677747, by rfl⟩ : syracuseStep 903663 = 1355495) B1355495
theorem B904175 : Blo 900574 904175 := bstep (se 1 (by rfl) ⟨678131, by rfl⟩ : syracuseStep 904175 = 1356263) B1356263
theorem B904191 : Blo 900574 904191 := bstep (se 1 (by rfl) ⟨678143, by rfl⟩ : syracuseStep 904191 = 1356287) B1356287
theorem B904347 : Blo 900574 904347 := bstep (se 1 (by rfl) ⟨678260, by rfl⟩ : syracuseStep 904347 = 1356521) B1356521
theorem B3853615 : Blo 900574 3853615 := bstep (se 1 (by rfl) ⟨2890211, by rfl⟩ : syracuseStep 3853615 = 5780423) B5780423
theorem B73944521 : Blo 900574 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B2281385 : Blo 900574 2281385 := bstep (se 2 (by rfl) ⟨855519, by rfl⟩ : syracuseStep 2281385 = 1711039) B1711039
theorem B5789879 : Blo 900574 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B8249015 : Blo 900574 8249015 := bstep (se 1 (by rfl) ⟨6186761, by rfl⟩ : syracuseStep 8249015 = 12373523) B12373523
theorem B3858587 : Blo 900574 3858587 := bstep (se 1 (by rfl) ⟨2893940, by rfl⟩ : syracuseStep 3858587 = 5787881) B5787881
theorem B12345547 : Blo 900574 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B3039659 : Blo 900574 3039659 := bstep (se 1 (by rfl) ⟨2279744, by rfl⟩ : syracuseStep 3039659 = 4559489) B4559489
theorem B5202463 : Blo 900574 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B3859271 : Blo 900574 3859271 := bstep (se 1 (by rfl) ⟨2894453, by rfl⟩ : syracuseStep 3859271 = 5788907) B5788907
theorem B2287723 : Blo 900574 2287723 := bstep (se 1 (by rfl) ⟨1715792, by rfl⟩ : syracuseStep 2287723 = 3431585) B3431585
theorem B39643303 : Blo 900574 39643303 := bstep (se 1 (by rfl) ⟨29732477, by rfl⟩ : syracuseStep 39643303 = 59464955) B59464955
theorem B2746813 : Blo 900574 2746813 := bstep (se 3 (by rfl) ⟨515027, by rfl⟩ : syracuseStep 2746813 = 1030055) B1030055
theorem B2288371 : Blo 900574 2288371 := bstep (se 1 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 2288371 = 3432557) B3432557
theorem B1928063 : Blo 900574 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B2026601 : Blo 900574 2026601 := bstep (se 2 (by rfl) ⟨759975, by rfl⟩ : syracuseStep 2026601 = 1519951) B1519951
theorem B5795003 : Blo 900574 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B2026727 : Blo 900574 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B1830431 : Blo 900574 1830431 := bstep (se 1 (by rfl) ⟨1372823, by rfl⟩ : syracuseStep 1830431 = 2745647) B2745647
theorem B2027177 : Blo 900574 2027177 := bstep (se 2 (by rfl) ⟨760191, by rfl⟩ : syracuseStep 2027177 = 1520383) B1520383
theorem B1928927 : Blo 900574 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B3043871 : Blo 900574 3043871 := bstep (se 1 (by rfl) ⟨2282903, by rfl⟩ : syracuseStep 3043871 = 4565807) B4565807
theorem B31716467 : Blo 900574 31716467 := bstep (se 1 (by rfl) ⟨23787350, by rfl⟩ : syracuseStep 31716467 = 47574701) B47574701
theorem B1013215 : Blo 900574 1013215 := bstep (se 1 (by rfl) ⟨759911, by rfl⟩ : syracuseStep 1013215 = 1519823) B1519823
theorem B2029823 : Blo 900574 2029823 := bstep (se 1 (by rfl) ⟨1522367, by rfl⟩ : syracuseStep 2029823 = 3044735) B3044735
theorem B19822877 : Blo 900574 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B2029985 : Blo 900574 2029985 := bstep (se 2 (by rfl) ⟨761244, by rfl⟩ : syracuseStep 2029985 = 1522489) B1522489
theorem B3046247 : Blo 900574 3046247 := bstep (se 1 (by rfl) ⟨2284685, by rfl⟩ : syracuseStep 3046247 = 4569371) B4569371
theorem B3046355 : Blo 900574 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B1015231 : Blo 900574 1015231 := bstep (se 1 (by rfl) ⟨761423, by rfl⟩ : syracuseStep 1015231 = 1522847) B1522847
theorem B2031443 : Blo 900574 2031443 := bstep (se 1 (by rfl) ⟨1523582, by rfl⟩ : syracuseStep 2031443 = 3047165) B3047165
theorem B3047327 : Blo 900574 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B665878967 : Blo 900574 665878967 := bstep (se 1 (by rfl) ⟨499409225, by rfl⟩ : syracuseStep 665878967 = 998818451) B998818451
theorem B2032361 : Blo 900574 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B1082335 : Blo 900574 1082335 := bstep (se 1 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 1082335 = 1623503) B1623503
theorem B2033279 : Blo 900574 2033279 := bstep (se 1 (by rfl) ⟨1524959, by rfl⟩ : syracuseStep 2033279 = 3049919) B3049919
theorem B3475511 : Blo 900574 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B3050297 : Blo 900574 3050297 := bstep (se 2 (by rfl) ⟨1143861, by rfl⟩ : syracuseStep 3050297 = 2287723) B2287723
theorem B52857737 : Blo 900574 52857737 := bstep (se 2 (by rfl) ⟨19821651, by rfl⟩ : syracuseStep 52857737 = 39643303) B39643303
theorem B2034971 : Blo 900574 2034971 := bstep (se 1 (by rfl) ⟨1526228, by rfl⟩ : syracuseStep 2034971 = 3052457) B3052457
theorem B25005689 : Blo 900574 25005689 := bstep (se 2 (by rfl) ⟨9377133, by rfl⟩ : syracuseStep 25005689 = 18754267) B18754267
theorem B3051161 : Blo 900574 3051161 := bstep (se 2 (by rfl) ⟨1144185, by rfl⟩ : syracuseStep 3051161 = 2288371) B2288371
theorem B2167967 : Blo 900574 2167967 := bstep (se 1 (by rfl) ⟨1625975, by rfl⟩ : syracuseStep 2167967 = 3251951) B3251951
theorem B1710857 : Blo 900574 1710857 := bstep (se 2 (by rfl) ⟨641571, by rfl⟩ : syracuseStep 1710857 = 1283143) B1283143
theorem B6167495 : Blo 900574 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B1350953 : Blo 900574 1350953 := bstep (se 2 (by rfl) ⟨506607, by rfl⟩ : syracuseStep 1350953 = 1013215) B1013215
theorem B1351067 : Blo 900574 1351067 := bstep (se 1 (by rfl) ⟨1013300, by rfl⟩ : syracuseStep 1351067 = 2026601) B2026601
theorem B1351151 : Blo 900574 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B1220287 : Blo 900574 1220287 := bstep (se 1 (by rfl) ⟨915215, by rfl⟩ : syracuseStep 1220287 = 1830431) B1830431
theorem B1351451 : Blo 900574 1351451 := bstep (se 1 (by rfl) ⟨1013588, by rfl⟩ : syracuseStep 1351451 = 2027177) B2027177
theorem B1285951 : Blo 900574 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B21144311 : Blo 900574 21144311 := bstep (se 1 (by rfl) ⟨15858233, by rfl⟩ : syracuseStep 21144311 = 31716467) B31716467
theorem B1353215 : Blo 900574 1353215 := bstep (se 1 (by rfl) ⟨1014911, by rfl⟩ : syracuseStep 1353215 = 2029823) B2029823
theorem B13215251 : Blo 900574 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B1353323 : Blo 900574 1353323 := bstep (se 1 (by rfl) ⟨1014992, by rfl⟩ : syracuseStep 1353323 = 2029985) B2029985
theorem B1353641 : Blo 900574 1353641 := bstep (se 2 (by rfl) ⟨507615, by rfl⟩ : syracuseStep 1353641 = 1015231) B1015231
theorem B1354295 : Blo 900574 1354295 := bstep (se 1 (by rfl) ⟨1015721, by rfl⟩ : syracuseStep 1354295 = 2031443) B2031443
theorem B2894555 : Blo 900574 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B6957895 : Blo 900574 6957895 := bstep (se 1 (by rfl) ⟨5218421, by rfl⟩ : syracuseStep 6957895 = 10436843) B10436843
theorem B16460729 : Blo 900574 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B1354847 : Blo 900574 1354847 := bstep (se 1 (by rfl) ⟨1016135, by rfl⟩ : syracuseStep 1354847 = 2032271) B2032271
theorem B1354943 : Blo 900574 1354943 := bstep (se 1 (by rfl) ⟨1016207, by rfl⟩ : syracuseStep 1354943 = 2032415) B2032415
theorem B1355711 : Blo 900574 1355711 := bstep (se 1 (by rfl) ⟨1016783, by rfl⟩ : syracuseStep 1355711 = 2033567) B2033567
theorem B1356011 : Blo 900574 1356011 := bstep (se 1 (by rfl) ⟨1017008, by rfl⟩ : syracuseStep 1356011 = 2034017) B2034017
theorem B1356095 : Blo 900574 1356095 := bstep (se 1 (by rfl) ⟨1017071, by rfl⟩ : syracuseStep 1356095 = 2034143) B2034143
theorem B1356425 : Blo 900574 1356425 := bstep (se 2 (by rfl) ⟨508659, by rfl⟩ : syracuseStep 1356425 = 1017319) B1017319
theorem B1356635 : Blo 900574 1356635 := bstep (se 1 (by rfl) ⟨1017476, by rfl⟩ : syracuseStep 1356635 = 2034953) B2034953
theorem B1356665 : Blo 900574 1356665 := bstep (se 2 (by rfl) ⟨508749, by rfl⟩ : syracuseStep 1356665 = 1017499) B1017499
theorem B49296347 : Blo 900574 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B1520923 : Blo 900574 1520923 := bstep (se 1 (by rfl) ⟨1140692, by rfl⟩ : syracuseStep 1520923 = 2281385) B2281385
theorem B4568399 : Blo 900574 4568399 := bstep (se 1 (by rfl) ⟨3426299, by rfl⟩ : syracuseStep 4568399 = 6852599) B6852599
theorem B18528173 : Blo 900574 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B4110497 : Blo 900574 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B10271609 : Blo 900574 10271609 := bstep (se 2 (by rfl) ⟨3851853, by rfl⟩ : syracuseStep 10271609 = 7703707) B7703707
theorem B17611769 : Blo 900574 17611769 := bstep (se 2 (by rfl) ⟨6604413, by rfl⟩ : syracuseStep 17611769 = 13208827) B13208827
theorem B900863 : Blo 900574 900863 := bstep (se 1 (by rfl) ⟨675647, by rfl⟩ : syracuseStep 900863 = 1351295) B1351295
theorem B901211 : Blo 900574 901211 := bstep (se 1 (by rfl) ⟨675908, by rfl⟩ : syracuseStep 901211 = 1351817) B1351817
theorem B2572391 : Blo 900574 2572391 := bstep (se 1 (by rfl) ⟨1929293, by rfl⟩ : syracuseStep 2572391 = 3858587) B3858587
theorem B2572847 : Blo 900574 2572847 := bstep (se 1 (by rfl) ⟨1929635, by rfl⟩ : syracuseStep 2572847 = 3859271) B3859271
theorem B902383 : Blo 900574 902383 := bstep (se 1 (by rfl) ⟨676787, by rfl⟩ : syracuseStep 902383 = 1353575) B1353575
theorem B902559 : Blo 900574 902559 := bstep (se 1 (by rfl) ⟨676919, by rfl⟩ : syracuseStep 902559 = 1353839) B1353839
theorem B5130337 : Blo 900574 5130337 := bstep (se 2 (by rfl) ⟨1923876, by rfl⟩ : syracuseStep 5130337 = 3847753) B3847753
theorem B903407 : Blo 900574 903407 := bstep (se 1 (by rfl) ⟨677555, by rfl⟩ : syracuseStep 903407 = 1355111) B1355111
theorem B2541961 : Blo 900574 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B903835 : Blo 900574 903835 := bstep (se 1 (by rfl) ⟨677876, by rfl⟩ : syracuseStep 903835 = 1355753) B1355753
theorem B2280383 : Blo 900574 2280383 := bstep (se 1 (by rfl) ⟨1710287, by rfl⟩ : syracuseStep 2280383 = 3420575) B3420575
theorem B15453341 : Blo 900574 15453341 := bstep (se 3 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 15453341 = 5795003) B5795003
theorem B904551 : Blo 900574 904551 := bstep (se 1 (by rfl) ⟨678413, by rfl⟩ : syracuseStep 904551 = 1356827) B1356827
theorem B2281243 : Blo 900574 2281243 := bstep (se 1 (by rfl) ⟨1710932, by rfl⟩ : syracuseStep 2281243 = 3421865) B3421865
theorem B2283137 : Blo 900574 2283137 := bstep (se 2 (by rfl) ⟨856176, by rfl⟩ : syracuseStep 2283137 = 1712353) B1712353
theorem B18503387 : Blo 900574 18503387 := bstep (se 1 (by rfl) ⟨13877540, by rfl⟩ : syracuseStep 18503387 = 27755081) B27755081
theorem B6936617 : Blo 900574 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B47438183 : Blo 900574 47438183 := bstep (se 1 (by rfl) ⟨35578637, by rfl⟩ : syracuseStep 47438183 = 71157275) B71157275
theorem B3662417 : Blo 900574 3662417 := bstep (se 2 (by rfl) ⟨1373406, by rfl⟩ : syracuseStep 3662417 = 2746813) B2746813
theorem B2056999 : Blo 900574 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B5137627 : Blo 900574 5137627 := bstep (se 1 (by rfl) ⟨3853220, by rfl⟩ : syracuseStep 5137627 = 7706441) B7706441
theorem B3859919 : Blo 900574 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B5138153 : Blo 900574 5138153 := bstep (se 2 (by rfl) ⟨1926807, by rfl⟩ : syracuseStep 5138153 = 3853615) B3853615
theorem B5499343 : Blo 900574 5499343 := bstep (se 1 (by rfl) ⟨4124507, by rfl⟩ : syracuseStep 5499343 = 8249015) B8249015
theorem B1141543 : Blo 900574 1141543 := bstep (se 1 (by rfl) ⟨856157, by rfl⟩ : syracuseStep 1141543 = 1712315) B1712315
theorem B2026439 : Blo 900574 2026439 := bstep (se 1 (by rfl) ⟨1519829, by rfl⟩ : syracuseStep 2026439 = 3039659) B3039659
theorem B11562533 : Blo 900574 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B6517073 : Blo 900574 6517073 := bstep (se 2 (by rfl) ⟨2443902, by rfl⟩ : syracuseStep 6517073 = 4887805) B4887805
theorem B46330861 : Blo 900574 46330861 := bstep (se 3 (by rfl) ⟨8687036, by rfl⟩ : syracuseStep 46330861 = 17374073) B17374073
theorem B5141501 : Blo 900574 5141501 := bstep (se 3 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 5141501 = 1928063) B1928063
theorem B2029247 : Blo 900574 2029247 := bstep (se 1 (by rfl) ⟨1521935, by rfl⟩ : syracuseStep 2029247 = 3043871) B3043871
theorem B2030831 : Blo 900574 2030831 := bstep (se 1 (by rfl) ⟨1523123, by rfl⟩ : syracuseStep 2030831 = 3046247) B3046247
theorem B2030903 : Blo 900574 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B2031551 : Blo 900574 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B1443113 : Blo 900574 1443113 := bstep (se 2 (by rfl) ⟨541167, by rfl⟩ : syracuseStep 1443113 = 1082335) B1082335
theorem B6850169 : Blo 900574 6850169 := bstep (se 2 (by rfl) ⟨2568813, by rfl⟩ : syracuseStep 6850169 = 5137627) B5137627
theorem B2033531 : Blo 900574 2033531 := bstep (se 1 (by rfl) ⟨1525148, by rfl⟩ : syracuseStep 2033531 = 3050297) B3050297
theorem B2034107 : Blo 900574 2034107 := bstep (se 1 (by rfl) ⟨1525580, by rfl⟩ : syracuseStep 2034107 = 3051161) B3051161
theorem B1445311 : Blo 900574 1445311 := bstep (se 1 (by rfl) ⟨1083983, by rfl⟩ : syracuseStep 1445311 = 2167967) B2167967
theorem B9277193 : Blo 900574 9277193 := bstep (se 2 (by rfl) ⟨3478947, by rfl⟩ : syracuseStep 9277193 = 6957895) B6957895
theorem B14096207 : Blo 900574 14096207 := bstep (se 1 (by rfl) ⟨10572155, by rfl⟩ : syracuseStep 14096207 = 21144311) B21144311
theorem B61774481 : Blo 900574 61774481 := bstep (se 2 (by rfl) ⟨23165430, by rfl⟩ : syracuseStep 61774481 = 46330861) B46330861
theorem B1350959 : Blo 900574 1350959 := bstep (se 1 (by rfl) ⟨1013219, by rfl⟩ : syracuseStep 1350959 = 2026439) B2026439
theorem B7708355 : Blo 900574 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B46964717 : Blo 900574 46964717 := bstep (se 3 (by rfl) ⟨8805884, by rfl⟩ : syracuseStep 46964717 = 17611769) B17611769
theorem B1352831 : Blo 900574 1352831 := bstep (se 1 (by rfl) ⟨1014623, by rfl⟩ : syracuseStep 1352831 = 2029247) B2029247
theorem B1353887 : Blo 900574 1353887 := bstep (se 1 (by rfl) ⟨1015415, by rfl⟩ : syracuseStep 1353887 = 2030831) B2030831
theorem B1353935 : Blo 900574 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B1714601 : Blo 900574 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B1354367 : Blo 900574 1354367 := bstep (se 1 (by rfl) ⟨1015775, by rfl⟩ : syracuseStep 1354367 = 2031551) B2031551
theorem B1714927 : Blo 900574 1714927 := bstep (se 1 (by rfl) ⟨1286195, by rfl⟩ : syracuseStep 1714927 = 2572391) B2572391
theorem B443919311 : Blo 900574 443919311 := bstep (se 1 (by rfl) ⟨332939483, by rfl⟩ : syracuseStep 443919311 = 665878967) B665878967
theorem B1715231 : Blo 900574 1715231 := bstep (se 1 (by rfl) ⟨1286423, by rfl⟩ : syracuseStep 1715231 = 2572847) B2572847
theorem B1354907 : Blo 900574 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B1355519 : Blo 900574 1355519 := bstep (se 1 (by rfl) ⟨1016639, by rfl⟩ : syracuseStep 1355519 = 2033279) B2033279
theorem B35238491 : Blo 900574 35238491 := bstep (se 1 (by rfl) ⟨26428868, by rfl⟩ : syracuseStep 35238491 = 52857737) B52857737
theorem B1520255 : Blo 900574 1520255 := bstep (se 1 (by rfl) ⟨1140191, by rfl⟩ : syracuseStep 1520255 = 2280383) B2280383
theorem B10302227 : Blo 900574 10302227 := bstep (se 1 (by rfl) ⟨7726670, by rfl⟩ : syracuseStep 10302227 = 15453341) B15453341
theorem B1356647 : Blo 900574 1356647 := bstep (se 1 (by rfl) ⟨1017485, by rfl⟩ : syracuseStep 1356647 = 2034971) B2034971
theorem B1522057 : Blo 900574 1522057 := bstep (se 2 (by rfl) ⟨570771, by rfl⟩ : syracuseStep 1522057 = 1141543) B1141543
theorem B1522091 : Blo 900574 1522091 := bstep (se 1 (by rfl) ⟨1141568, by rfl⟩ : syracuseStep 1522091 = 2283137) B2283137
theorem B12335591 : Blo 900574 12335591 := bstep (se 1 (by rfl) ⟨9251693, by rfl⟩ : syracuseStep 12335591 = 18503387) B18503387
theorem B4111663 : Blo 900574 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B900635 : Blo 900574 900635 := bstep (se 1 (by rfl) ⟨675476, by rfl⟩ : syracuseStep 900635 = 1350953) B1350953
theorem B900711 : Blo 900574 900711 := bstep (se 1 (by rfl) ⟨675533, by rfl⟩ : syracuseStep 900711 = 1351067) B1351067
theorem B900767 : Blo 900574 900767 := bstep (se 1 (by rfl) ⟨675575, by rfl⟩ : syracuseStep 900767 = 1351151) B1351151
theorem B900967 : Blo 900574 900967 := bstep (se 1 (by rfl) ⟨675725, by rfl⟩ : syracuseStep 900967 = 1351451) B1351451
theorem B18497645 : Blo 900574 18497645 := bstep (se 3 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 18497645 = 6936617) B6936617
theorem B2441611 : Blo 900574 2441611 := bstep (se 1 (by rfl) ⟨1831208, by rfl⟩ : syracuseStep 2441611 = 3662417) B3662417
theorem B126501821 : Blo 900574 126501821 := bstep (se 3 (by rfl) ⟨23719091, by rfl⟩ : syracuseStep 126501821 = 47438183) B47438183
theorem B2573279 : Blo 900574 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B902143 : Blo 900574 902143 := bstep (se 1 (by rfl) ⟨676607, by rfl⟩ : syracuseStep 902143 = 1353215) B1353215
theorem B902215 : Blo 900574 902215 := bstep (se 1 (by rfl) ⟨676661, by rfl⟩ : syracuseStep 902215 = 1353323) B1353323
theorem B3425435 : Blo 900574 3425435 := bstep (se 1 (by rfl) ⟨2569076, by rfl⟩ : syracuseStep 3425435 = 5138153) B5138153
theorem B902427 : Blo 900574 902427 := bstep (se 1 (by rfl) ⟨676820, by rfl⟩ : syracuseStep 902427 = 1353641) B1353641
theorem B902863 : Blo 900574 902863 := bstep (se 1 (by rfl) ⟨677147, by rfl⟩ : syracuseStep 902863 = 1354295) B1354295
theorem B7718813 : Blo 900574 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B903231 : Blo 900574 903231 := bstep (se 1 (by rfl) ⟨677423, by rfl⟩ : syracuseStep 903231 = 1354847) B1354847
theorem B903295 : Blo 900574 903295 := bstep (se 1 (by rfl) ⟨677471, by rfl⟩ : syracuseStep 903295 = 1354943) B1354943
theorem B903807 : Blo 900574 903807 := bstep (se 1 (by rfl) ⟨677855, by rfl⟩ : syracuseStep 903807 = 1355711) B1355711
theorem B904007 : Blo 900574 904007 := bstep (se 1 (by rfl) ⟨678005, by rfl⟩ : syracuseStep 904007 = 1356011) B1356011
theorem B904063 : Blo 900574 904063 := bstep (se 1 (by rfl) ⟨678047, by rfl⟩ : syracuseStep 904063 = 1356095) B1356095
theorem B4344715 : Blo 900574 4344715 := bstep (se 1 (by rfl) ⟨3258536, by rfl⟩ : syracuseStep 4344715 = 6517073) B6517073
theorem B904283 : Blo 900574 904283 := bstep (se 1 (by rfl) ⟨678212, by rfl⟩ : syracuseStep 904283 = 1356425) B1356425
theorem B904423 : Blo 900574 904423 := bstep (se 1 (by rfl) ⟨678317, by rfl⟩ : syracuseStep 904423 = 1356635) B1356635
theorem B904443 : Blo 900574 904443 := bstep (se 1 (by rfl) ⟨678332, by rfl⟩ : syracuseStep 904443 = 1356665) B1356665
theorem B3427667 : Blo 900574 3427667 := bstep (se 1 (by rfl) ⟨2570750, by rfl⟩ : syracuseStep 3427667 = 5141501) B5141501
theorem B2740331 : Blo 900574 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B1627049 : Blo 900574 1627049 := bstep (se 2 (by rfl) ⟨610143, by rfl⟩ : syracuseStep 1627049 = 1220287) B1220287
theorem B2742665 : Blo 900574 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B2317007 : Blo 900574 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B13557125 : Blo 900574 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B16670459 : Blo 900574 16670459 := bstep (se 1 (by rfl) ⟨12502844, by rfl⟩ : syracuseStep 16670459 = 25005689) B25005689
theorem B6840449 : Blo 900574 6840449 := bstep (se 2 (by rfl) ⟨2565168, by rfl⟩ : syracuseStep 6840449 = 5130337) B5130337
theorem B7332457 : Blo 900574 7332457 := bstep (se 2 (by rfl) ⟨2749671, by rfl⟩ : syracuseStep 7332457 = 5499343) B5499343
theorem B1140571 : Blo 900574 1140571 := bstep (se 1 (by rfl) ⟨855428, by rfl⟩ : syracuseStep 1140571 = 1710857) B1710857
theorem B3041657 : Blo 900574 3041657 := bstep (se 2 (by rfl) ⟨1140621, by rfl⟩ : syracuseStep 3041657 = 2281243) B2281243
theorem B8810167 : Blo 900574 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B2027897 : Blo 900574 2027897 := bstep (se 2 (by rfl) ⟨760461, by rfl⟩ : syracuseStep 2027897 = 1520923) B1520923
theorem B10973819 : Blo 900574 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B32864231 : Blo 900574 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B3045599 : Blo 900574 3045599 := bstep (se 1 (by rfl) ⟨2284199, by rfl⟩ : syracuseStep 3045599 = 4568399) B4568399
theorem B12352115 : Blo 900574 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B6847739 : Blo 900574 6847739 := bstep (se 1 (by rfl) ⟨5135804, by rfl⟩ : syracuseStep 6847739 = 10271609) B10271609
theorem B5145875 : Blo 900574 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B29263517 : Blo 900574 29263517 := bstep (se 3 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 29263517 = 10973819) B10973819
theorem B1084699 : Blo 900574 1084699 := bstep (se 1 (by rfl) ⟨813524, by rfl⟩ : syracuseStep 1084699 = 1627049) B1627049
theorem B4560299 : Blo 900574 4560299 := bstep (se 1 (by rfl) ⟨3420224, by rfl⟩ : syracuseStep 4560299 = 6840449) B6840449
theorem B7313773 : Blo 900574 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B1351931 : Blo 900574 1351931 := bstep (se 1 (by rfl) ⟨1013948, by rfl⟩ : syracuseStep 1351931 = 2027897) B2027897
theorem B5482217 : Blo 900574 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B8234743 : Blo 900574 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B4565159 : Blo 900574 4565159 := bstep (se 1 (by rfl) ⟨3423869, by rfl⟩ : syracuseStep 4565159 = 6847739) B6847739
theorem B12331763 : Blo 900574 12331763 := bstep (se 1 (by rfl) ⟨9248822, by rfl⟩ : syracuseStep 12331763 = 18497645) B18497645
theorem B3255481 : Blo 900574 3255481 := bstep (se 2 (by rfl) ⟨1220805, by rfl⟩ : syracuseStep 3255481 = 2441611) B2441611
theorem B1715519 : Blo 900574 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B9776609 : Blo 900574 9776609 := bstep (se 2 (by rfl) ⟨3666228, by rfl⟩ : syracuseStep 9776609 = 7332457) B7332457
theorem B962075 : Blo 900574 962075 := bstep (se 1 (by rfl) ⟨721556, by rfl⟩ : syracuseStep 962075 = 1443113) B1443113
theorem B4566779 : Blo 900574 4566779 := bstep (se 1 (by rfl) ⟨3425084, by rfl⟩ : syracuseStep 4566779 = 6850169) B6850169
theorem B1355687 : Blo 900574 1355687 := bstep (se 1 (by rfl) ⟨1016765, by rfl⟩ : syracuseStep 1355687 = 2033531) B2033531
theorem B1356071 : Blo 900574 1356071 := bstep (se 1 (by rfl) ⟨1017053, by rfl⟩ : syracuseStep 1356071 = 2034107) B2034107
theorem B1520761 : Blo 900574 1520761 := bstep (se 2 (by rfl) ⟨570285, by rfl⟩ : syracuseStep 1520761 = 1140571) B1140571
theorem B900639 : Blo 900574 900639 := bstep (se 1 (by rfl) ⟨675479, by rfl⟩ : syracuseStep 900639 = 1350959) B1350959
theorem B11746889 : Blo 900574 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B31309811 : Blo 900574 31309811 := bstep (se 1 (by rfl) ⟨23482358, by rfl⟩ : syracuseStep 31309811 = 46964717) B46964717
theorem B901887 : Blo 900574 901887 := bstep (se 1 (by rfl) ⟨676415, by rfl⟩ : syracuseStep 901887 = 1352831) B1352831
theorem B902591 : Blo 900574 902591 := bstep (se 1 (by rfl) ⟨676943, by rfl⟩ : syracuseStep 902591 = 1353887) B1353887
theorem B902623 : Blo 900574 902623 := bstep (se 1 (by rfl) ⟨676967, by rfl⟩ : syracuseStep 902623 = 1353935) B1353935
theorem B902911 : Blo 900574 902911 := bstep (se 1 (by rfl) ⟨677183, by rfl⟩ : syracuseStep 902911 = 1354367) B1354367
theorem B6178685 : Blo 900574 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B295946207 : Blo 900574 295946207 := bstep (se 1 (by rfl) ⟨221959655, by rfl⟩ : syracuseStep 295946207 = 443919311) B443919311
theorem B903271 : Blo 900574 903271 := bstep (se 1 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 903271 = 1354907) B1354907
theorem B903679 : Blo 900574 903679 := bstep (se 1 (by rfl) ⟨677759, by rfl⟩ : syracuseStep 903679 = 1355519) B1355519
theorem B6868151 : Blo 900574 6868151 := bstep (se 1 (by rfl) ⟨5151113, by rfl⟩ : syracuseStep 6868151 = 10302227) B10302227
theorem B904431 : Blo 900574 904431 := bstep (se 1 (by rfl) ⟨678323, by rfl⟩ : syracuseStep 904431 = 1356647) B1356647
theorem B21909487 : Blo 900574 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B44454557 : Blo 900574 44454557 := bstep (se 3 (by rfl) ⟨8335229, by rfl⟩ : syracuseStep 44454557 = 16670459) B16670459
theorem B84334547 : Blo 900574 84334547 := bstep (se 1 (by rfl) ⟨63250910, by rfl⟩ : syracuseStep 84334547 = 126501821) B126501821
theorem B2283623 : Blo 900574 2283623 := bstep (se 1 (by rfl) ⟨1712717, by rfl⟩ : syracuseStep 2283623 = 3425435) B3425435
theorem B2285111 : Blo 900574 2285111 := bstep (se 1 (by rfl) ⟨1713833, by rfl⟩ : syracuseStep 2285111 = 3427667) B3427667
theorem B6184795 : Blo 900574 6184795 := bstep (se 1 (by rfl) ⟨4638596, by rfl⟩ : syracuseStep 6184795 = 9277193) B9277193
theorem B1826887 : Blo 900574 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B2286569 : Blo 900574 2286569 := bstep (se 2 (by rfl) ⟨857463, by rfl⟩ : syracuseStep 2286569 = 1714927) B1714927
theorem B5792953 : Blo 900574 5792953 := bstep (se 2 (by rfl) ⟨2172357, by rfl⟩ : syracuseStep 5792953 = 4344715) B4344715
theorem B9397471 : Blo 900574 9397471 := bstep (se 1 (by rfl) ⟨7048103, by rfl⟩ : syracuseStep 9397471 = 14096207) B14096207
theorem B41182987 : Blo 900574 41182987 := bstep (se 1 (by rfl) ⟨30887240, by rfl⟩ : syracuseStep 41182987 = 61774481) B61774481
theorem B1927081 : Blo 900574 1927081 := bstep (se 2 (by rfl) ⟨722655, by rfl⟩ : syracuseStep 1927081 = 1445311) B1445311
theorem B9038083 : Blo 900574 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B5138903 : Blo 900574 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B32894909 : Blo 900574 32894909 := bstep (se 3 (by rfl) ⟨6167795, by rfl⟩ : syracuseStep 32894909 = 12335591) B12335591
theorem B2027771 : Blo 900574 2027771 := bstep (se 1 (by rfl) ⟨1520828, by rfl⟩ : syracuseStep 2027771 = 3041657) B3041657
theorem B1143067 : Blo 900574 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B1143487 : Blo 900574 1143487 := bstep (se 1 (by rfl) ⟨857615, by rfl⟩ : syracuseStep 1143487 = 1715231) B1715231
theorem B23492327 : Blo 900574 23492327 := bstep (se 1 (by rfl) ⟨17619245, by rfl⟩ : syracuseStep 23492327 = 35238491) B35238491
theorem B1013503 : Blo 900574 1013503 := bstep (se 1 (by rfl) ⟨760127, by rfl⟩ : syracuseStep 1013503 = 1520255) B1520255
theorem B2029409 : Blo 900574 2029409 := bstep (se 2 (by rfl) ⟨761028, by rfl⟩ : syracuseStep 2029409 = 1522057) B1522057
theorem B2030399 : Blo 900574 2030399 := bstep (se 1 (by rfl) ⟨1522799, by rfl⟩ : syracuseStep 2030399 = 3045599) B3045599
theorem B1014727 : Blo 900574 1014727 := bstep (se 1 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 1014727 = 1522091) B1522091
theorem B197297471 : Blo 900574 197297471 := bstep (se 1 (by rfl) ⟨147973103, by rfl⟩ : syracuseStep 197297471 = 295946207) B295946207
theorem B10979657 : Blo 900574 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B1446265 : Blo 900574 1446265 := bstep (se 2 (by rfl) ⟨542349, by rfl⟩ : syracuseStep 1446265 = 1084699) B1084699
theorem B1351337 : Blo 900574 1351337 := bstep (se 2 (by rfl) ⟨506751, by rfl⟩ : syracuseStep 1351337 = 1013503) B1013503
theorem B21929939 : Blo 900574 21929939 := bstep (se 1 (by rfl) ⟨16447454, by rfl⟩ : syracuseStep 21929939 = 32894909) B32894909
theorem B1351847 : Blo 900574 1351847 := bstep (se 1 (by rfl) ⟨1013885, by rfl⟩ : syracuseStep 1351847 = 2027771) B2027771
theorem B1352939 : Blo 900574 1352939 := bstep (se 1 (by rfl) ⟨1014704, by rfl⟩ : syracuseStep 1352939 = 2029409) B2029409
theorem B1352969 : Blo 900574 1352969 := bstep (se 2 (by rfl) ⟨507363, by rfl⟩ : syracuseStep 1352969 = 1014727) B1014727
theorem B2565533 : Blo 900574 2565533 := bstep (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) B962075
theorem B1353599 : Blo 900574 1353599 := bstep (se 1 (by rfl) ⟨1015199, by rfl⟩ : syracuseStep 1353599 = 2030399) B2030399
theorem B2435849 : Blo 900574 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B19509011 : Blo 900574 19509011 := bstep (se 1 (by rfl) ⟨14631758, by rfl⟩ : syracuseStep 19509011 = 29263517) B29263517
theorem B12529961 : Blo 900574 12529961 := bstep (se 2 (by rfl) ⟨4698735, by rfl⟩ : syracuseStep 12529961 = 9397471) B9397471
theorem B2569441 : Blo 900574 2569441 := bstep (se 2 (by rfl) ⟨963540, by rfl⟩ : syracuseStep 2569441 = 1927081) B1927081
theorem B29636371 : Blo 900574 29636371 := bstep (se 1 (by rfl) ⟨22227278, by rfl⟩ : syracuseStep 29636371 = 44454557) B44454557
theorem B1522415 : Blo 900574 1522415 := bstep (se 1 (by rfl) ⟨1141811, by rfl⟩ : syracuseStep 1522415 = 2283623) B2283623
theorem B4340641 : Blo 900574 4340641 := bstep (se 2 (by rfl) ⟨1627740, by rfl⟩ : syracuseStep 4340641 = 3255481) B3255481
theorem B1523407 : Blo 900574 1523407 := bstep (se 1 (by rfl) ⟨1142555, by rfl⟩ : syracuseStep 1523407 = 2285111) B2285111
theorem B29212649 : Blo 900574 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B901287 : Blo 900574 901287 := bstep (se 1 (by rfl) ⟨675965, by rfl⟩ : syracuseStep 901287 = 1351931) B1351931
theorem B1524089 : Blo 900574 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B1524379 : Blo 900574 1524379 := bstep (se 1 (by rfl) ⟨1143284, by rfl⟩ : syracuseStep 1524379 = 2286569) B2286569
theorem B1524649 : Blo 900574 1524649 := bstep (se 2 (by rfl) ⟨571743, by rfl⟩ : syracuseStep 1524649 = 1143487) B1143487
theorem B3654811 : Blo 900574 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B3425935 : Blo 900574 3425935 := bstep (se 1 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 3425935 = 5138903) B5138903
theorem B903791 : Blo 900574 903791 := bstep (se 1 (by rfl) ⟨677843, by rfl⟩ : syracuseStep 903791 = 1355687) B1355687
theorem B904047 : Blo 900574 904047 := bstep (se 1 (by rfl) ⟨678035, by rfl⟩ : syracuseStep 904047 = 1356071) B1356071
theorem B9751697 : Blo 900574 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B4574717 : Blo 900574 4574717 := bstep (se 3 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 4574717 = 1715519) B1715519
theorem B8246393 : Blo 900574 8246393 := bstep (se 2 (by rfl) ⟨3092397, by rfl⟩ : syracuseStep 8246393 = 6184795) B6184795
theorem B3430583 : Blo 900574 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B7723937 : Blo 900574 7723937 := bstep (se 2 (by rfl) ⟨2896476, by rfl⟩ : syracuseStep 7723937 = 5792953) B5792953
theorem B4578767 : Blo 900574 4578767 := bstep (se 1 (by rfl) ⟨3434075, by rfl⟩ : syracuseStep 4578767 = 6868151) B6868151
theorem B54910649 : Blo 900574 54910649 := bstep (se 2 (by rfl) ⟨20591493, by rfl⟩ : syracuseStep 54910649 = 41182987) B41182987
theorem B12050777 : Blo 900574 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B3040199 : Blo 900574 3040199 := bstep (se 1 (by rfl) ⟨2280149, by rfl⟩ : syracuseStep 3040199 = 4560299) B4560299
theorem B56223031 : Blo 900574 56223031 := bstep (se 1 (by rfl) ⟨42167273, by rfl⟩ : syracuseStep 56223031 = 84334547) B84334547
theorem B62646205 : Blo 900574 62646205 := bstep (se 3 (by rfl) ⟨11746163, by rfl⟩ : syracuseStep 62646205 = 23492327) B23492327
theorem B16476493 : Blo 900574 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B3043439 : Blo 900574 3043439 := bstep (se 1 (by rfl) ⟨2282579, by rfl⟩ : syracuseStep 3043439 = 4565159) B4565159
theorem B2027681 : Blo 900574 2027681 := bstep (se 2 (by rfl) ⟨760380, by rfl⟩ : syracuseStep 2027681 = 1520761) B1520761
theorem B8221175 : Blo 900574 8221175 := bstep (se 1 (by rfl) ⟨6165881, by rfl⟩ : syracuseStep 8221175 = 12331763) B12331763
theorem B6517739 : Blo 900574 6517739 := bstep (se 1 (by rfl) ⟨4888304, by rfl⟩ : syracuseStep 6517739 = 9776609) B9776609
theorem B3044519 : Blo 900574 3044519 := bstep (se 1 (by rfl) ⟨2283389, by rfl⟩ : syracuseStep 3044519 = 4566779) B4566779
theorem B7831259 : Blo 900574 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B20873207 : Blo 900574 20873207 := bstep (se 1 (by rfl) ⟨15654905, by rfl⟩ : syracuseStep 20873207 = 31309811) B31309811
theorem B1016059 : Blo 900574 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B2032505 : Blo 900574 2032505 := bstep (se 2 (by rfl) ⟨762189, by rfl⟩ : syracuseStep 2032505 = 1524379) B1524379
theorem B131531647 : Blo 900574 131531647 := bstep (se 1 (by rfl) ⟨98648735, by rfl⟩ : syracuseStep 131531647 = 197297471) B197297471
theorem B2032865 : Blo 900574 2032865 := bstep (se 2 (by rfl) ⟨762324, by rfl⟩ : syracuseStep 2032865 = 1524649) B1524649
theorem B3049811 : Blo 900574 3049811 := bstep (se 1 (by rfl) ⟨2287358, by rfl⟩ : syracuseStep 3049811 = 4574717) B4574717
theorem B83528273 : Blo 900574 83528273 := bstep (se 2 (by rfl) ⟨31323102, by rfl⟩ : syracuseStep 83528273 = 62646205) B62646205
theorem B5149291 : Blo 900574 5149291 := bstep (se 1 (by rfl) ⟨3861968, by rfl⟩ : syracuseStep 5149291 = 7723937) B7723937
theorem B3052511 : Blo 900574 3052511 := bstep (se 1 (by rfl) ⟨2289383, by rfl⟩ : syracuseStep 3052511 = 4578767) B4578767
theorem B36607099 : Blo 900574 36607099 := bstep (se 1 (by rfl) ⟨27455324, by rfl⟩ : syracuseStep 36607099 = 54910649) B54910649
theorem B14619959 : Blo 900574 14619959 := bstep (se 1 (by rfl) ⟨10964969, by rfl⟩ : syracuseStep 14619959 = 21929939) B21929939
theorem B8033851 : Blo 900574 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B1351787 : Blo 900574 1351787 := bstep (se 1 (by rfl) ⟨1013840, by rfl⟩ : syracuseStep 1351787 = 2027681) B2027681
theorem B5480783 : Blo 900574 5480783 := bstep (se 1 (by rfl) ⟨4110587, by rfl⟩ : syracuseStep 5480783 = 8221175) B8221175
theorem B5220839 : Blo 900574 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B19475099 : Blo 900574 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B7319771 : Blo 900574 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B7713413 : Blo 900574 7713413 := bstep (se 4 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 7713413 = 1446265) B1446265
theorem B6501131 : Blo 900574 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B4567913 : Blo 900574 4567913 := bstep (se 2 (by rfl) ⟨1712967, by rfl⟩ : syracuseStep 4567913 = 3425935) B3425935
theorem B21968657 : Blo 900574 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B900891 : Blo 900574 900891 := bstep (se 1 (by rfl) ⟨675668, by rfl⟩ : syracuseStep 900891 = 1351337) B1351337
theorem B901231 : Blo 900574 901231 := bstep (se 1 (by rfl) ⟨675923, by rfl⟩ : syracuseStep 901231 = 1351847) B1351847
theorem B901959 : Blo 900574 901959 := bstep (se 1 (by rfl) ⟨676469, by rfl⟩ : syracuseStep 901959 = 1352939) B1352939
theorem B901979 : Blo 900574 901979 := bstep (se 1 (by rfl) ⟨676484, by rfl⟩ : syracuseStep 901979 = 1352969) B1352969
theorem B902399 : Blo 900574 902399 := bstep (se 1 (by rfl) ⟨676799, by rfl⟩ : syracuseStep 902399 = 1353599) B1353599
theorem B3425921 : Blo 900574 3425921 := bstep (se 2 (by rfl) ⟨1284720, by rfl⟩ : syracuseStep 3425921 = 2569441) B2569441
theorem B1623899 : Blo 900574 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B4345159 : Blo 900574 4345159 := bstep (se 1 (by rfl) ⟨3258869, by rfl⟩ : syracuseStep 4345159 = 6517739) B6517739
theorem B5787521 : Blo 900574 5787521 := bstep (se 2 (by rfl) ⟨2170320, by rfl⟩ : syracuseStep 5787521 = 4340641) B4340641
theorem B13915471 : Blo 900574 13915471 := bstep (se 1 (by rfl) ⟨10436603, by rfl⟩ : syracuseStep 13915471 = 20873207) B20873207
theorem B4873081 : Blo 900574 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B74964041 : Blo 900574 74964041 := bstep (se 2 (by rfl) ⟨28111515, by rfl⟩ : syracuseStep 74964041 = 56223031) B56223031
theorem B5497595 : Blo 900574 5497595 := bstep (se 1 (by rfl) ⟨4123196, by rfl⟩ : syracuseStep 5497595 = 8246393) B8246393
theorem B6841421 : Blo 900574 6841421 := bstep (se 3 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 6841421 = 2565533) B2565533
theorem B2287055 : Blo 900574 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B2026799 : Blo 900574 2026799 := bstep (se 1 (by rfl) ⟨1520099, by rfl⟩ : syracuseStep 2026799 = 3040199) B3040199
theorem B39515161 : Blo 900574 39515161 := bstep (se 2 (by rfl) ⟨14818185, by rfl⟩ : syracuseStep 39515161 = 29636371) B29636371
theorem B13006007 : Blo 900574 13006007 := bstep (se 1 (by rfl) ⟨9754505, by rfl⟩ : syracuseStep 13006007 = 19509011) B19509011
theorem B2028959 : Blo 900574 2028959 := bstep (se 1 (by rfl) ⟨1521719, by rfl⟩ : syracuseStep 2028959 = 3043439) B3043439
theorem B8353307 : Blo 900574 8353307 := bstep (se 1 (by rfl) ⟨6264980, by rfl⟩ : syracuseStep 8353307 = 12529961) B12529961
theorem B2029679 : Blo 900574 2029679 := bstep (se 1 (by rfl) ⟨1522259, by rfl⟩ : syracuseStep 2029679 = 3044519) B3044519
theorem B1014943 : Blo 900574 1014943 := bstep (se 1 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 1014943 = 1522415) B1522415
theorem B2031209 : Blo 900574 2031209 := bstep (se 2 (by rfl) ⟨761703, by rfl⟩ : syracuseStep 2031209 = 1523407) B1523407
theorem B175375529 : Blo 900574 175375529 := bstep (se 2 (by rfl) ⟨65765823, by rfl⟩ : syracuseStep 175375529 = 131531647) B131531647
theorem B2033207 : Blo 900574 2033207 := bstep (se 1 (by rfl) ⟨1524905, by rfl⟩ : syracuseStep 2033207 = 3049811) B3049811
theorem B2035007 : Blo 900574 2035007 := bstep (se 1 (by rfl) ⟨1526255, by rfl⟩ : syracuseStep 2035007 = 3052511) B3052511
theorem B49976027 : Blo 900574 49976027 := bstep (se 1 (by rfl) ⟨37482020, by rfl⟩ : syracuseStep 49976027 = 74964041) B74964041
theorem B4330397 : Blo 900574 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B4560947 : Blo 900574 4560947 := bstep (se 1 (by rfl) ⟨3420710, by rfl⟩ : syracuseStep 4560947 = 6841421) B6841421
theorem B12983399 : Blo 900574 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B18553961 : Blo 900574 18553961 := bstep (se 2 (by rfl) ⟨6957735, by rfl⟩ : syracuseStep 18553961 = 13915471) B13915471
theorem B1351199 : Blo 900574 1351199 := bstep (se 1 (by rfl) ⟨1013399, by rfl⟩ : syracuseStep 1351199 = 2026799) B2026799
theorem B4334087 : Blo 900574 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B1352639 : Blo 900574 1352639 := bstep (se 1 (by rfl) ⟨1014479, by rfl⟩ : syracuseStep 1352639 = 2028959) B2028959
theorem B6497441 : Blo 900574 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B1353119 : Blo 900574 1353119 := bstep (se 1 (by rfl) ⟨1014839, by rfl⟩ : syracuseStep 1353119 = 2029679) B2029679
theorem B1353257 : Blo 900574 1353257 := bstep (se 2 (by rfl) ⟨507471, by rfl⟩ : syracuseStep 1353257 = 1014943) B1014943
theorem B1354139 : Blo 900574 1354139 := bstep (se 1 (by rfl) ⟨1015604, by rfl⟩ : syracuseStep 1354139 = 2031209) B2031209
theorem B1354745 : Blo 900574 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B1355003 : Blo 900574 1355003 := bstep (se 1 (by rfl) ⟨1016252, by rfl⟩ : syracuseStep 1355003 = 2032505) B2032505
theorem B1355243 : Blo 900574 1355243 := bstep (se 1 (by rfl) ⟨1016432, by rfl⟩ : syracuseStep 1355243 = 2032865) B2032865
theorem B55685515 : Blo 900574 55685515 := bstep (se 1 (by rfl) ⟨41764136, by rfl⟩ : syracuseStep 55685515 = 83528273) B83528273
theorem B9746639 : Blo 900574 9746639 := bstep (se 1 (by rfl) ⟨7309979, by rfl⟩ : syracuseStep 9746639 = 14619959) B14619959
theorem B901191 : Blo 900574 901191 := bstep (se 1 (by rfl) ⟨675893, by rfl⟩ : syracuseStep 901191 = 1351787) B1351787
theorem B3653855 : Blo 900574 3653855 := bstep (se 1 (by rfl) ⟨2740391, by rfl⟩ : syracuseStep 3653855 = 5480783) B5480783
theorem B6865721 : Blo 900574 6865721 := bstep (se 2 (by rfl) ⟨2574645, by rfl⟩ : syracuseStep 6865721 = 5149291) B5149291
theorem B1524703 : Blo 900574 1524703 := bstep (se 1 (by rfl) ⟨1143527, by rfl⟩ : syracuseStep 1524703 = 2287055) B2287055
theorem B48809465 : Blo 900574 48809465 := bstep (se 2 (by rfl) ⟨18303549, by rfl⟩ : syracuseStep 48809465 = 36607099) B36607099
theorem B8670671 : Blo 900574 8670671 := bstep (se 1 (by rfl) ⟨6503003, by rfl⟩ : syracuseStep 8670671 = 13006007) B13006007
theorem B2283947 : Blo 900574 2283947 := bstep (se 1 (by rfl) ⟨1712960, by rfl⟩ : syracuseStep 2283947 = 3425921) B3425921
theorem B3858347 : Blo 900574 3858347 := bstep (se 1 (by rfl) ⟨2893760, by rfl⟩ : syracuseStep 3858347 = 5787521) B5787521
theorem B22275485 : Blo 900574 22275485 := bstep (se 3 (by rfl) ⟨4176653, by rfl⟩ : syracuseStep 22275485 = 8353307) B8353307
theorem B5793545 : Blo 900574 5793545 := bstep (se 2 (by rfl) ⟨2172579, by rfl⟩ : syracuseStep 5793545 = 4345159) B4345159
theorem B3665063 : Blo 900574 3665063 := bstep (se 1 (by rfl) ⟨2748797, by rfl⟩ : syracuseStep 3665063 = 5497595) B5497595
theorem B13922237 : Blo 900574 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B52686881 : Blo 900574 52686881 := bstep (se 2 (by rfl) ⟨19757580, by rfl⟩ : syracuseStep 52686881 = 39515161) B39515161
theorem B10711801 : Blo 900574 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B4879847 : Blo 900574 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B5142275 : Blo 900574 5142275 := bstep (se 1 (by rfl) ⟨3856706, by rfl⟩ : syracuseStep 5142275 = 7713413) B7713413
theorem B3045275 : Blo 900574 3045275 := bstep (se 1 (by rfl) ⟨2283956, by rfl⟩ : syracuseStep 3045275 = 4567913) B4567913
theorem B14645771 : Blo 900574 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B116917019 : Blo 900574 116917019 := bstep (se 1 (by rfl) ⟨87687764, by rfl⟩ : syracuseStep 116917019 = 175375529) B175375529
theorem B32539643 : Blo 900574 32539643 := bstep (se 1 (by rfl) ⟨24404732, by rfl⟩ : syracuseStep 32539643 = 48809465) B48809465
theorem B2032937 : Blo 900574 2032937 := bstep (se 2 (by rfl) ⟨762351, by rfl⟩ : syracuseStep 2032937 = 1524703) B1524703
theorem B2886931 : Blo 900574 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B8655599 : Blo 900574 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B4331627 : Blo 900574 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B14850323 : Blo 900574 14850323 := bstep (se 1 (by rfl) ⟨11137742, by rfl⟩ : syracuseStep 14850323 = 22275485) B22275485
theorem B3253231 : Blo 900574 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B6497759 : Blo 900574 6497759 := bstep (se 1 (by rfl) ⟨4873319, by rfl⟩ : syracuseStep 6497759 = 9746639) B9746639
theorem B2435903 : Blo 900574 2435903 := bstep (se 1 (by rfl) ⟨1826927, by rfl⟩ : syracuseStep 2435903 = 3653855) B3653855
theorem B1355471 : Blo 900574 1355471 := bstep (se 1 (by rfl) ⟨1016603, by rfl⟩ : syracuseStep 1355471 = 2033207) B2033207
theorem B1356671 : Blo 900574 1356671 := bstep (se 1 (by rfl) ⟨1017503, by rfl⟩ : syracuseStep 1356671 = 2035007) B2035007
theorem B5780447 : Blo 900574 5780447 := bstep (se 1 (by rfl) ⟨4335335, by rfl⟩ : syracuseStep 5780447 = 8670671) B8670671
theorem B1522631 : Blo 900574 1522631 := bstep (se 1 (by rfl) ⟨1141973, by rfl⟩ : syracuseStep 1522631 = 2283947) B2283947
theorem B12369307 : Blo 900574 12369307 := bstep (se 1 (by rfl) ⟨9276980, by rfl⟩ : syracuseStep 12369307 = 18553961) B18553961
theorem B900799 : Blo 900574 900799 := bstep (se 1 (by rfl) ⟨675599, by rfl⟩ : syracuseStep 900799 = 1351199) B1351199
theorem B2572231 : Blo 900574 2572231 := bstep (se 1 (by rfl) ⟨1929173, by rfl⟩ : syracuseStep 2572231 = 3858347) B3858347
theorem B901759 : Blo 900574 901759 := bstep (se 1 (by rfl) ⟨676319, by rfl⟩ : syracuseStep 901759 = 1352639) B1352639
theorem B902079 : Blo 900574 902079 := bstep (se 1 (by rfl) ⟨676559, by rfl⟩ : syracuseStep 902079 = 1353119) B1353119
theorem B902171 : Blo 900574 902171 := bstep (se 1 (by rfl) ⟨676628, by rfl⟩ : syracuseStep 902171 = 1353257) B1353257
theorem B902759 : Blo 900574 902759 := bstep (se 1 (by rfl) ⟨677069, by rfl⟩ : syracuseStep 902759 = 1354139) B1354139
theorem B903163 : Blo 900574 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B2443375 : Blo 900574 2443375 := bstep (se 1 (by rfl) ⟨1832531, by rfl⟩ : syracuseStep 2443375 = 3665063) B3665063
theorem B903335 : Blo 900574 903335 := bstep (se 1 (by rfl) ⟨677501, by rfl⟩ : syracuseStep 903335 = 1355003) B1355003
theorem B903495 : Blo 900574 903495 := bstep (se 1 (by rfl) ⟨677621, by rfl⟩ : syracuseStep 903495 = 1355243) B1355243
theorem B3428183 : Blo 900574 3428183 := bstep (se 1 (by rfl) ⟨2571137, by rfl⟩ : syracuseStep 3428183 = 5142275) B5142275
theorem B4577147 : Blo 900574 4577147 := bstep (se 1 (by rfl) ⟨3432860, by rfl⟩ : syracuseStep 4577147 = 6865721) B6865721
theorem B11557565 : Blo 900574 11557565 := bstep (se 3 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 11557565 = 4334087) B4334087
theorem B33317351 : Blo 900574 33317351 := bstep (se 1 (by rfl) ⟨24988013, by rfl⟩ : syracuseStep 33317351 = 49976027) B49976027
theorem B3040631 : Blo 900574 3040631 := bstep (se 1 (by rfl) ⟨2280473, by rfl⟩ : syracuseStep 3040631 = 4560947) B4560947
theorem B74247353 : Blo 900574 74247353 := bstep (se 2 (by rfl) ⟨27842757, by rfl⟩ : syracuseStep 74247353 = 55685515) B55685515
theorem B14282401 : Blo 900574 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B3862363 : Blo 900574 3862363 := bstep (se 1 (by rfl) ⟨2896772, by rfl⟩ : syracuseStep 3862363 = 5793545) B5793545
theorem B35124587 : Blo 900574 35124587 := bstep (se 1 (by rfl) ⟨26343440, by rfl⟩ : syracuseStep 35124587 = 52686881) B52686881
theorem B2030183 : Blo 900574 2030183 := bstep (se 1 (by rfl) ⟨1522637, by rfl⟩ : syracuseStep 2030183 = 3045275) B3045275
theorem B9763847 : Blo 900574 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B37125965 : Blo 900574 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B21693095 : Blo 900574 21693095 := bstep (se 1 (by rfl) ⟨16269821, by rfl⟩ : syracuseStep 21693095 = 32539643) B32539643
theorem B3051431 : Blo 900574 3051431 := bstep (se 1 (by rfl) ⟨2288573, by rfl⟩ : syracuseStep 3051431 = 4577147) B4577147
theorem B2887751 : Blo 900574 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B9900215 : Blo 900574 9900215 := bstep (se 1 (by rfl) ⟨7425161, by rfl⟩ : syracuseStep 9900215 = 14850323) B14850323
theorem B7705043 : Blo 900574 7705043 := bstep (se 1 (by rfl) ⟨5778782, by rfl⟩ : syracuseStep 7705043 = 11557565) B11557565
theorem B19043201 : Blo 900574 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B5149817 : Blo 900574 5149817 := bstep (se 2 (by rfl) ⟨1931181, by rfl⟩ : syracuseStep 5149817 = 3862363) B3862363
theorem B4331839 : Blo 900574 4331839 := bstep (se 1 (by rfl) ⟨3248879, by rfl⟩ : syracuseStep 4331839 = 6497759) B6497759
theorem B1353455 : Blo 900574 1353455 := bstep (se 1 (by rfl) ⟨1015091, by rfl⟩ : syracuseStep 1353455 = 2030183) B2030183
theorem B16492409 : Blo 900574 16492409 := bstep (se 2 (by rfl) ⟨6184653, by rfl⟩ : syracuseStep 16492409 = 12369307) B12369307
theorem B99002573 : Blo 900574 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B1355291 : Blo 900574 1355291 := bstep (se 1 (by rfl) ⟨1016468, by rfl⟩ : syracuseStep 1355291 = 2032937) B2032937
theorem B4337641 : Blo 900574 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B23081597 : Blo 900574 23081597 := bstep (se 3 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 23081597 = 8655599) B8655599
theorem B3257833 : Blo 900574 3257833 := bstep (se 2 (by rfl) ⟨1221687, by rfl⟩ : syracuseStep 3257833 = 2443375) B2443375
theorem B3849241 : Blo 900574 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B1623935 : Blo 900574 1623935 := bstep (se 1 (by rfl) ⟨1217951, by rfl⟩ : syracuseStep 1623935 = 2435903) B2435903
theorem B49498235 : Blo 900574 49498235 := bstep (se 1 (by rfl) ⟨37123676, by rfl⟩ : syracuseStep 49498235 = 74247353) B74247353
theorem B903647 : Blo 900574 903647 := bstep (se 1 (by rfl) ⟨677735, by rfl⟩ : syracuseStep 903647 = 1355471) B1355471
theorem B904447 : Blo 900574 904447 := bstep (se 1 (by rfl) ⟨678335, by rfl⟩ : syracuseStep 904447 = 1356671) B1356671
theorem B3853631 : Blo 900574 3853631 := bstep (se 1 (by rfl) ⟨2890223, by rfl⟩ : syracuseStep 3853631 = 5780447) B5780447
theorem B23416391 : Blo 900574 23416391 := bstep (se 1 (by rfl) ⟨17562293, by rfl⟩ : syracuseStep 23416391 = 35124587) B35124587
theorem B6509231 : Blo 900574 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B3429641 : Blo 900574 3429641 := bstep (se 2 (by rfl) ⟨1286115, by rfl⟩ : syracuseStep 3429641 = 2572231) B2572231
theorem B77944679 : Blo 900574 77944679 := bstep (se 1 (by rfl) ⟨58458509, by rfl⟩ : syracuseStep 77944679 = 116917019) B116917019
theorem B2285455 : Blo 900574 2285455 := bstep (se 1 (by rfl) ⟨1714091, by rfl⟩ : syracuseStep 2285455 = 3428183) B3428183
theorem B22211567 : Blo 900574 22211567 := bstep (se 1 (by rfl) ⟨16658675, by rfl⟩ : syracuseStep 22211567 = 33317351) B33317351
theorem B2027087 : Blo 900574 2027087 := bstep (se 1 (by rfl) ⟨1520315, by rfl⟩ : syracuseStep 2027087 = 3040631) B3040631
theorem B1015087 : Blo 900574 1015087 := bstep (se 1 (by rfl) ⟨761315, by rfl⟩ : syracuseStep 1015087 = 1522631) B1522631
theorem B7700669 : Blo 900574 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B32998823 : Blo 900574 32998823 := bstep (se 1 (by rfl) ⟨24749117, by rfl⟩ : syracuseStep 32998823 = 49498235) B49498235
theorem B2034287 : Blo 900574 2034287 := bstep (se 1 (by rfl) ⟨1525715, by rfl⟩ : syracuseStep 2034287 = 3051431) B3051431
theorem B4330493 : Blo 900574 4330493 := bstep (se 3 (by rfl) ⟨811967, by rfl⟩ : syracuseStep 4330493 = 1623935) B1623935
theorem B66001715 : Blo 900574 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B1351391 : Blo 900574 1351391 := bstep (se 1 (by rfl) ⟨1013543, by rfl⟩ : syracuseStep 1351391 = 2027087) B2027087
theorem B5775785 : Blo 900574 5775785 := bstep (se 2 (by rfl) ⟨2165919, by rfl⟩ : syracuseStep 5775785 = 4331839) B4331839
theorem B1353449 : Blo 900574 1353449 := bstep (se 2 (by rfl) ⟨507543, by rfl⟩ : syracuseStep 1353449 = 1015087) B1015087
theorem B14462063 : Blo 900574 14462063 := bstep (se 1 (by rfl) ⟨10846547, by rfl⟩ : syracuseStep 14462063 = 21693095) B21693095
theorem B2569087 : Blo 900574 2569087 := bstep (se 1 (by rfl) ⟨1926815, by rfl⟩ : syracuseStep 2569087 = 3853631) B3853631
theorem B15610927 : Blo 900574 15610927 := bstep (se 1 (by rfl) ⟨11708195, by rfl⟩ : syracuseStep 15610927 = 23416391) B23416391
theorem B6600143 : Blo 900574 6600143 := bstep (se 1 (by rfl) ⟨4950107, by rfl⟩ : syracuseStep 6600143 = 9900215) B9900215
theorem B4339487 : Blo 900574 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B12695467 : Blo 900574 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B902303 : Blo 900574 902303 := bstep (se 1 (by rfl) ⟨676727, by rfl⟩ : syracuseStep 902303 = 1353455) B1353455
theorem B10994939 : Blo 900574 10994939 := bstep (se 1 (by rfl) ⟨8246204, by rfl⟩ : syracuseStep 10994939 = 16492409) B16492409
theorem B4343777 : Blo 900574 4343777 := bstep (se 2 (by rfl) ⟨1628916, by rfl⟩ : syracuseStep 4343777 = 3257833) B3257833
theorem B903527 : Blo 900574 903527 := bstep (se 1 (by rfl) ⟨677645, by rfl⟩ : syracuseStep 903527 = 1355291) B1355291
theorem B15387731 : Blo 900574 15387731 := bstep (se 1 (by rfl) ⟨11540798, by rfl⟩ : syracuseStep 15387731 = 23081597) B23081597
theorem B5132321 : Blo 900574 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B5136695 : Blo 900574 5136695 := bstep (se 1 (by rfl) ⟨3852521, by rfl⟩ : syracuseStep 5136695 = 7705043) B7705043
theorem B3433211 : Blo 900574 3433211 := bstep (se 1 (by rfl) ⟨2574908, by rfl⟩ : syracuseStep 3433211 = 5149817) B5149817
theorem B2286427 : Blo 900574 2286427 := bstep (se 1 (by rfl) ⟨1714820, by rfl⟩ : syracuseStep 2286427 = 3429641) B3429641
theorem B51963119 : Blo 900574 51963119 := bstep (se 1 (by rfl) ⟨38972339, by rfl⟩ : syracuseStep 51963119 = 77944679) B77944679
theorem B14807711 : Blo 900574 14807711 := bstep (se 1 (by rfl) ⟨11105783, by rfl⟩ : syracuseStep 14807711 = 22211567) B22211567
theorem B3047273 : Blo 900574 3047273 := bstep (se 2 (by rfl) ⟨1142727, by rfl⟩ : syracuseStep 3047273 = 2285455) B2285455
theorem B23134085 : Blo 900574 23134085 := bstep (se 4 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 23134085 = 4337641) B4337641
theorem B3048569 : Blo 900574 3048569 := bstep (se 2 (by rfl) ⟨1143213, by rfl⟩ : syracuseStep 3048569 = 2286427) B2286427
theorem B10258487 : Blo 900574 10258487 := bstep (se 1 (by rfl) ⟨7693865, by rfl⟩ : syracuseStep 10258487 = 15387731) B15387731
theorem B2886995 : Blo 900574 2886995 := bstep (se 1 (by rfl) ⟨2165246, by rfl⟩ : syracuseStep 2886995 = 4330493) B4330493
theorem B17600381 : Blo 900574 17600381 := bstep (se 3 (by rfl) ⟨3300071, by rfl⟩ : syracuseStep 17600381 = 6600143) B6600143
theorem B34642079 : Blo 900574 34642079 := bstep (se 1 (by rfl) ⟨25981559, by rfl⟩ : syracuseStep 34642079 = 51963119) B51963119
theorem B20814569 : Blo 900574 20814569 := bstep (se 2 (by rfl) ⟨7805463, by rfl⟩ : syracuseStep 20814569 = 15610927) B15610927
theorem B9641375 : Blo 900574 9641375 := bstep (se 1 (by rfl) ⟨7231031, by rfl⟩ : syracuseStep 9641375 = 14462063) B14462063
theorem B9871807 : Blo 900574 9871807 := bstep (se 1 (by rfl) ⟨7403855, by rfl⟩ : syracuseStep 9871807 = 14807711) B14807711
theorem B2892991 : Blo 900574 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B21999215 : Blo 900574 21999215 := bstep (se 1 (by rfl) ⟨16499411, by rfl⟩ : syracuseStep 21999215 = 32998823) B32998823
theorem B2895851 : Blo 900574 2895851 := bstep (se 1 (by rfl) ⟨2171888, by rfl⟩ : syracuseStep 2895851 = 4343777) B4343777
theorem B1356191 : Blo 900574 1356191 := bstep (se 1 (by rfl) ⟨1017143, by rfl⟩ : syracuseStep 1356191 = 2034287) B2034287
theorem B3421547 : Blo 900574 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B900927 : Blo 900574 900927 := bstep (se 1 (by rfl) ⟨675695, by rfl⟩ : syracuseStep 900927 = 1351391) B1351391
theorem B3424463 : Blo 900574 3424463 := bstep (se 1 (by rfl) ⟨2568347, by rfl⟩ : syracuseStep 3424463 = 5136695) B5136695
theorem B3850523 : Blo 900574 3850523 := bstep (se 1 (by rfl) ⟨2887892, by rfl⟩ : syracuseStep 3850523 = 5775785) B5775785
theorem B902299 : Blo 900574 902299 := bstep (se 1 (by rfl) ⟨676724, by rfl⟩ : syracuseStep 902299 = 1353449) B1353449
theorem B3425449 : Blo 900574 3425449 := bstep (se 2 (by rfl) ⟨1284543, by rfl⟩ : syracuseStep 3425449 = 2569087) B2569087
theorem B16927289 : Blo 900574 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B15422723 : Blo 900574 15422723 := bstep (se 1 (by rfl) ⟨11567042, by rfl⟩ : syracuseStep 15422723 = 23134085) B23134085
theorem B5133779 : Blo 900574 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B7329959 : Blo 900574 7329959 := bstep (se 1 (by rfl) ⟨5497469, by rfl⟩ : syracuseStep 7329959 = 10994939) B10994939
theorem B44001143 : Blo 900574 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B2288807 : Blo 900574 2288807 := bstep (se 1 (by rfl) ⟨1716605, by rfl⟩ : syracuseStep 2288807 = 3433211) B3433211
theorem B2031515 : Blo 900574 2031515 := bstep (se 1 (by rfl) ⟨1523636, by rfl⟩ : syracuseStep 2031515 = 3047273) B3047273
theorem B2032379 : Blo 900574 2032379 := bstep (se 1 (by rfl) ⟨1524284, by rfl⟩ : syracuseStep 2032379 = 3048569) B3048569
theorem B11733587 : Blo 900574 11733587 := bstep (se 1 (by rfl) ⟨8800190, by rfl⟩ : syracuseStep 11733587 = 17600381) B17600381
theorem B4886639 : Blo 900574 4886639 := bstep (se 1 (by rfl) ⟨3664979, by rfl⟩ : syracuseStep 4886639 = 7329959) B7329959
theorem B6427583 : Blo 900574 6427583 := bstep (se 1 (by rfl) ⟨4820687, by rfl⟩ : syracuseStep 6427583 = 9641375) B9641375
theorem B29334095 : Blo 900574 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B1354343 : Blo 900574 1354343 := bstep (se 1 (by rfl) ⟨1015757, by rfl⟩ : syracuseStep 1354343 = 2031515) B2031515
theorem B2567015 : Blo 900574 2567015 := bstep (se 1 (by rfl) ⟨1925261, by rfl⟩ : syracuseStep 2567015 = 3850523) B3850523
theorem B4567265 : Blo 900574 4567265 := bstep (se 2 (by rfl) ⟨1712724, by rfl⟩ : syracuseStep 4567265 = 3425449) B3425449
theorem B11284859 : Blo 900574 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B3422519 : Blo 900574 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B13876379 : Blo 900574 13876379 := bstep (se 1 (by rfl) ⟨10407284, by rfl⟩ : syracuseStep 13876379 = 20814569) B20814569
theorem B1525871 : Blo 900574 1525871 := bstep (se 1 (by rfl) ⟨1144403, by rfl⟩ : syracuseStep 1525871 = 2288807) B2288807
theorem B14666143 : Blo 900574 14666143 := bstep (se 1 (by rfl) ⟨10999607, by rfl⟩ : syracuseStep 14666143 = 21999215) B21999215
theorem B904127 : Blo 900574 904127 := bstep (se 1 (by rfl) ⟨678095, by rfl⟩ : syracuseStep 904127 = 1356191) B1356191
theorem B2281031 : Blo 900574 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B2282975 : Blo 900574 2282975 := bstep (se 1 (by rfl) ⟨1712231, by rfl⟩ : syracuseStep 2282975 = 3424463) B3424463
theorem B13162409 : Blo 900574 13162409 := bstep (se 2 (by rfl) ⟨4935903, by rfl⟩ : syracuseStep 13162409 = 9871807) B9871807
theorem B6838991 : Blo 900574 6838991 := bstep (se 1 (by rfl) ⟨5129243, by rfl⟩ : syracuseStep 6838991 = 10258487) B10258487
theorem B3857321 : Blo 900574 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B1924663 : Blo 900574 1924663 := bstep (se 1 (by rfl) ⟨1443497, by rfl⟩ : syracuseStep 1924663 = 2886995) B2886995
theorem B10281815 : Blo 900574 10281815 := bstep (se 1 (by rfl) ⟨7711361, by rfl⟩ : syracuseStep 10281815 = 15422723) B15422723
theorem B23094719 : Blo 900574 23094719 := bstep (se 1 (by rfl) ⟨17321039, by rfl⟩ : syracuseStep 23094719 = 34642079) B34642079
theorem B1930567 : Blo 900574 1930567 := bstep (se 1 (by rfl) ⟨1447925, by rfl⟩ : syracuseStep 1930567 = 2895851) B2895851
theorem B1017247 : Blo 900574 1017247 := bstep (se 1 (by rfl) ⟨762935, by rfl⟩ : syracuseStep 1017247 = 1525871) B1525871
theorem B4559327 : Blo 900574 4559327 := bstep (se 1 (by rfl) ⟨3419495, by rfl⟩ : syracuseStep 4559327 = 6838991) B6838991
theorem B6854543 : Blo 900574 6854543 := bstep (se 1 (by rfl) ⟨5140907, by rfl⟩ : syracuseStep 6854543 = 10281815) B10281815
theorem B1711343 : Blo 900574 1711343 := bstep (se 1 (by rfl) ⟨1283507, by rfl⟩ : syracuseStep 1711343 = 2567015) B2567015
theorem B2566217 : Blo 900574 2566217 := bstep (se 2 (by rfl) ⟨962331, by rfl⟩ : syracuseStep 2566217 = 1924663) B1924663
theorem B9250919 : Blo 900574 9250919 := bstep (se 1 (by rfl) ⟨6938189, by rfl⟩ : syracuseStep 9250919 = 13876379) B13876379
theorem B1354919 : Blo 900574 1354919 := bstep (se 1 (by rfl) ⟨1016189, by rfl⟩ : syracuseStep 1354919 = 2032379) B2032379
theorem B1520687 : Blo 900574 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B3257759 : Blo 900574 3257759 := bstep (se 1 (by rfl) ⟨2443319, by rfl⟩ : syracuseStep 3257759 = 4886639) B4886639
theorem B1521983 : Blo 900574 1521983 := bstep (se 1 (by rfl) ⟨1141487, by rfl⟩ : syracuseStep 1521983 = 2282975) B2282975
theorem B902895 : Blo 900574 902895 := bstep (se 1 (by rfl) ⟨677171, by rfl⟩ : syracuseStep 902895 = 1354343) B1354343
theorem B2574089 : Blo 900574 2574089 := bstep (se 2 (by rfl) ⟨965283, by rfl⟩ : syracuseStep 2574089 = 1930567) B1930567
theorem B7523239 : Blo 900574 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B2281679 : Blo 900574 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B7822391 : Blo 900574 7822391 := bstep (se 1 (by rfl) ⟨5866793, by rfl⟩ : syracuseStep 7822391 = 11733587) B11733587
theorem B19554857 : Blo 900574 19554857 := bstep (se 2 (by rfl) ⟨7333071, by rfl⟩ : syracuseStep 19554857 = 14666143) B14666143
theorem B4285055 : Blo 900574 4285055 := bstep (se 1 (by rfl) ⟨3213791, by rfl⟩ : syracuseStep 4285055 = 6427583) B6427583
theorem B8774939 : Blo 900574 8774939 := bstep (se 1 (by rfl) ⟨6581204, by rfl⟩ : syracuseStep 8774939 = 13162409) B13162409
theorem B19556063 : Blo 900574 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B15396479 : Blo 900574 15396479 := bstep (se 1 (by rfl) ⟨11547359, by rfl⟩ : syracuseStep 15396479 = 23094719) B23094719
theorem B10286189 : Blo 900574 10286189 := bstep (se 3 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 10286189 = 3857321) B3857321
theorem B3044843 : Blo 900574 3044843 := bstep (se 1 (by rfl) ⟨2283632, by rfl⟩ : syracuseStep 3044843 = 4567265) B4567265
theorem B23399837 : Blo 900574 23399837 := bstep (se 3 (by rfl) ⟨4387469, by rfl⟩ : syracuseStep 23399837 = 8774939) B8774939
theorem B8687357 : Blo 900574 8687357 := bstep (se 3 (by rfl) ⟨1628879, by rfl⟩ : syracuseStep 8687357 = 3257759) B3257759
theorem B10030985 : Blo 900574 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B2856703 : Blo 900574 2856703 := bstep (se 1 (by rfl) ⟨2142527, by rfl⟩ : syracuseStep 2856703 = 4285055) B4285055
theorem B1710811 : Blo 900574 1710811 := bstep (se 1 (by rfl) ⟨1283108, by rfl⟩ : syracuseStep 1710811 = 2566217) B2566217
theorem B6167279 : Blo 900574 6167279 := bstep (se 1 (by rfl) ⟨4625459, by rfl⟩ : syracuseStep 6167279 = 9250919) B9250919
theorem B10264319 : Blo 900574 10264319 := bstep (se 1 (by rfl) ⟨7698239, by rfl⟩ : syracuseStep 10264319 = 15396479) B15396479
theorem B6857459 : Blo 900574 6857459 := bstep (se 1 (by rfl) ⟨5143094, by rfl⟩ : syracuseStep 6857459 = 10286189) B10286189
theorem B1716059 : Blo 900574 1716059 := bstep (se 1 (by rfl) ⟨1287044, by rfl⟩ : syracuseStep 1716059 = 2574089) B2574089
theorem B1356329 : Blo 900574 1356329 := bstep (se 2 (by rfl) ⟨508623, by rfl⟩ : syracuseStep 1356329 = 1017247) B1017247
theorem B1521119 : Blo 900574 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B4569695 : Blo 900574 4569695 := bstep (se 1 (by rfl) ⟨3427271, by rfl⟩ : syracuseStep 4569695 = 6854543) B6854543
theorem B903279 : Blo 900574 903279 := bstep (se 1 (by rfl) ⟨677459, by rfl⟩ : syracuseStep 903279 = 1354919) B1354919
theorem B20859709 : Blo 900574 20859709 := bstep (se 3 (by rfl) ⟨3911195, by rfl⟩ : syracuseStep 20859709 = 7822391) B7822391
theorem B3039551 : Blo 900574 3039551 := bstep (se 1 (by rfl) ⟨2279663, by rfl⟩ : syracuseStep 3039551 = 4559327) B4559327
theorem B1140895 : Blo 900574 1140895 := bstep (se 1 (by rfl) ⟨855671, by rfl⟩ : syracuseStep 1140895 = 1711343) B1711343
theorem B13036571 : Blo 900574 13036571 := bstep (se 1 (by rfl) ⟨9777428, by rfl⟩ : syracuseStep 13036571 = 19554857) B19554857
theorem B13037375 : Blo 900574 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B1013791 : Blo 900574 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B2029895 : Blo 900574 2029895 := bstep (se 1 (by rfl) ⟨1522421, by rfl⟩ : syracuseStep 2029895 = 3044843) B3044843
theorem B1014655 : Blo 900574 1014655 := bstep (se 1 (by rfl) ⟨760991, by rfl⟩ : syracuseStep 1014655 = 1521983) B1521983
theorem B15599891 : Blo 900574 15599891 := bstep (se 1 (by rfl) ⟨11699918, by rfl⟩ : syracuseStep 15599891 = 23399837) B23399837
theorem B6687323 : Blo 900574 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B8691047 : Blo 900574 8691047 := bstep (se 1 (by rfl) ⟨6518285, by rfl⟩ : syracuseStep 8691047 = 13036571) B13036571
theorem B3808937 : Blo 900574 3808937 := bstep (se 2 (by rfl) ⟨1428351, by rfl⟩ : syracuseStep 3808937 = 2856703) B2856703
theorem B8691583 : Blo 900574 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B1351721 : Blo 900574 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B1352873 : Blo 900574 1352873 := bstep (se 2 (by rfl) ⟨507327, by rfl⟩ : syracuseStep 1352873 = 1014655) B1014655
theorem B1353263 : Blo 900574 1353263 := bstep (se 1 (by rfl) ⟨1014947, by rfl⟩ : syracuseStep 1353263 = 2029895) B2029895
theorem B1521193 : Blo 900574 1521193 := bstep (se 2 (by rfl) ⟨570447, by rfl⟩ : syracuseStep 1521193 = 1140895) B1140895
theorem B4111519 : Blo 900574 4111519 := bstep (se 1 (by rfl) ⟨3083639, by rfl⟩ : syracuseStep 4111519 = 6167279) B6167279
theorem B4571639 : Blo 900574 4571639 := bstep (se 1 (by rfl) ⟨3428729, by rfl⟩ : syracuseStep 4571639 = 6857459) B6857459
theorem B904219 : Blo 900574 904219 := bstep (se 1 (by rfl) ⟨678164, by rfl⟩ : syracuseStep 904219 = 1356329) B1356329
theorem B2281081 : Blo 900574 2281081 := bstep (se 2 (by rfl) ⟨855405, by rfl⟩ : syracuseStep 2281081 = 1710811) B1710811
theorem B5791571 : Blo 900574 5791571 := bstep (se 1 (by rfl) ⟨4343678, by rfl⟩ : syracuseStep 5791571 = 8687357) B8687357
theorem B27812945 : Blo 900574 27812945 := bstep (se 2 (by rfl) ⟨10429854, by rfl⟩ : syracuseStep 27812945 = 20859709) B20859709
theorem B6842879 : Blo 900574 6842879 := bstep (se 1 (by rfl) ⟨5132159, by rfl⟩ : syracuseStep 6842879 = 10264319) B10264319
theorem B2026367 : Blo 900574 2026367 := bstep (se 1 (by rfl) ⟨1519775, by rfl⟩ : syracuseStep 2026367 = 3039551) B3039551
theorem B1144039 : Blo 900574 1144039 := bstep (se 1 (by rfl) ⟨858029, by rfl⟩ : syracuseStep 1144039 = 1716059) B1716059
theorem B1014079 : Blo 900574 1014079 := bstep (se 1 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 1014079 = 1521119) B1521119
theorem B3046463 : Blo 900574 3046463 := bstep (se 1 (by rfl) ⟨2284847, by rfl⟩ : syracuseStep 3046463 = 4569695) B4569695
theorem B3047759 : Blo 900574 3047759 := bstep (se 1 (by rfl) ⟨2285819, by rfl⟩ : syracuseStep 3047759 = 4571639) B4571639
theorem B4458215 : Blo 900574 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B4561919 : Blo 900574 4561919 := bstep (se 1 (by rfl) ⟨3421439, by rfl⟩ : syracuseStep 4561919 = 6842879) B6842879
theorem B1350911 : Blo 900574 1350911 := bstep (se 1 (by rfl) ⟨1013183, by rfl⟩ : syracuseStep 1350911 = 2026367) B2026367
theorem B1352105 : Blo 900574 1352105 := bstep (se 2 (by rfl) ⟨507039, by rfl⟩ : syracuseStep 1352105 = 1014079) B1014079
theorem B5482025 : Blo 900574 5482025 := bstep (se 2 (by rfl) ⟨2055759, by rfl⟩ : syracuseStep 5482025 = 4111519) B4111519
theorem B10399927 : Blo 900574 10399927 := bstep (se 1 (by rfl) ⟨7799945, by rfl⟩ : syracuseStep 10399927 = 15599891) B15599891
theorem B2539291 : Blo 900574 2539291 := bstep (se 1 (by rfl) ⟨1904468, by rfl⟩ : syracuseStep 2539291 = 3808937) B3808937
theorem B901147 : Blo 900574 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B901915 : Blo 900574 901915 := bstep (se 1 (by rfl) ⟨676436, by rfl⟩ : syracuseStep 901915 = 1352873) B1352873
theorem B902175 : Blo 900574 902175 := bstep (se 1 (by rfl) ⟨676631, by rfl⟩ : syracuseStep 902175 = 1353263) B1353263
theorem B1525385 : Blo 900574 1525385 := bstep (se 2 (by rfl) ⟨572019, by rfl⟩ : syracuseStep 1525385 = 1144039) B1144039
theorem B11588777 : Blo 900574 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B3041441 : Blo 900574 3041441 := bstep (se 2 (by rfl) ⟨1140540, by rfl⟩ : syracuseStep 3041441 = 2281081) B2281081
theorem B5794031 : Blo 900574 5794031 := bstep (se 1 (by rfl) ⟨4345523, by rfl⟩ : syracuseStep 5794031 = 8691047) B8691047
theorem B3861047 : Blo 900574 3861047 := bstep (se 1 (by rfl) ⟨2895785, by rfl⟩ : syracuseStep 3861047 = 5791571) B5791571
theorem B18541963 : Blo 900574 18541963 := bstep (se 1 (by rfl) ⟨13906472, by rfl⟩ : syracuseStep 18541963 = 27812945) B27812945
theorem B2028257 : Blo 900574 2028257 := bstep (se 2 (by rfl) ⟨760596, by rfl⟩ : syracuseStep 2028257 = 1521193) B1521193
theorem B2030975 : Blo 900574 2030975 := bstep (se 1 (by rfl) ⟨1523231, by rfl⟩ : syracuseStep 2030975 = 3046463) B3046463
theorem B2031839 : Blo 900574 2031839 := bstep (se 1 (by rfl) ⟨1523879, by rfl⟩ : syracuseStep 2031839 = 3047759) B3047759
theorem B1016923 : Blo 900574 1016923 := bstep (se 1 (by rfl) ⟨762692, by rfl⟩ : syracuseStep 1016923 = 1525385) B1525385
theorem B13866569 : Blo 900574 13866569 := bstep (se 2 (by rfl) ⟨5199963, by rfl⟩ : syracuseStep 13866569 = 10399927) B10399927
theorem B1352171 : Blo 900574 1352171 := bstep (se 1 (by rfl) ⟨1014128, by rfl⟩ : syracuseStep 1352171 = 2028257) B2028257
theorem B1353983 : Blo 900574 1353983 := bstep (se 1 (by rfl) ⟨1015487, by rfl⟩ : syracuseStep 1353983 = 2030975) B2030975
theorem B3385721 : Blo 900574 3385721 := bstep (se 2 (by rfl) ⟨1269645, by rfl⟩ : syracuseStep 3385721 = 2539291) B2539291
theorem B900607 : Blo 900574 900607 := bstep (se 1 (by rfl) ⟨675455, by rfl⟩ : syracuseStep 900607 = 1350911) B1350911
theorem B901403 : Blo 900574 901403 := bstep (se 1 (by rfl) ⟨676052, by rfl⟩ : syracuseStep 901403 = 1352105) B1352105
theorem B3654683 : Blo 900574 3654683 := bstep (se 1 (by rfl) ⟨2741012, by rfl⟩ : syracuseStep 3654683 = 5482025) B5482025
theorem B2574031 : Blo 900574 2574031 := bstep (se 1 (by rfl) ⟨1930523, by rfl⟩ : syracuseStep 2574031 = 3861047) B3861047
theorem B2972143 : Blo 900574 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B7725851 : Blo 900574 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B3041279 : Blo 900574 3041279 := bstep (se 1 (by rfl) ⟨2280959, by rfl⟩ : syracuseStep 3041279 = 4561919) B4561919
theorem B2027627 : Blo 900574 2027627 := bstep (se 1 (by rfl) ⟨1520720, by rfl⟩ : syracuseStep 2027627 = 3041441) B3041441
theorem B3862687 : Blo 900574 3862687 := bstep (se 1 (by rfl) ⟨2897015, by rfl⟩ : syracuseStep 3862687 = 5794031) B5794031
theorem B98890469 : Blo 900574 98890469 := bstep (se 4 (by rfl) ⟨9270981, by rfl⟩ : syracuseStep 98890469 = 18541963) B18541963
theorem B9244379 : Blo 900574 9244379 := bstep (se 1 (by rfl) ⟨6933284, by rfl⟩ : syracuseStep 9244379 = 13866569) B13866569
theorem B5150249 : Blo 900574 5150249 := bstep (se 2 (by rfl) ⟨1931343, by rfl⟩ : syracuseStep 5150249 = 3862687) B3862687
theorem B5150567 : Blo 900574 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B1351751 : Blo 900574 1351751 := bstep (se 1 (by rfl) ⟨1013813, by rfl⟩ : syracuseStep 1351751 = 2027627) B2027627
theorem B1354559 : Blo 900574 1354559 := bstep (se 1 (by rfl) ⟨1015919, by rfl⟩ : syracuseStep 1354559 = 2031839) B2031839
theorem B2436455 : Blo 900574 2436455 := bstep (se 1 (by rfl) ⟨1827341, by rfl⟩ : syracuseStep 2436455 = 3654683) B3654683
theorem B1355897 : Blo 900574 1355897 := bstep (se 2 (by rfl) ⟨508461, by rfl⟩ : syracuseStep 1355897 = 1016923) B1016923
theorem B901447 : Blo 900574 901447 := bstep (se 1 (by rfl) ⟨676085, by rfl⟩ : syracuseStep 901447 = 1352171) B1352171
theorem B902655 : Blo 900574 902655 := bstep (se 1 (by rfl) ⟨676991, by rfl⟩ : syracuseStep 902655 = 1353983) B1353983
theorem B3432041 : Blo 900574 3432041 := bstep (se 2 (by rfl) ⟨1287015, by rfl⟩ : syracuseStep 3432041 = 2574031) B2574031
theorem B2027519 : Blo 900574 2027519 := bstep (se 1 (by rfl) ⟨1520639, by rfl⟩ : syracuseStep 2027519 = 3041279) B3041279
theorem B2257147 : Blo 900574 2257147 := bstep (se 1 (by rfl) ⟨1692860, by rfl⟩ : syracuseStep 2257147 = 3385721) B3385721
theorem B65926979 : Blo 900574 65926979 := bstep (se 1 (by rfl) ⟨49445234, by rfl⟩ : syracuseStep 65926979 = 98890469) B98890469
theorem B3962857 : Blo 900574 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B5283809 : Blo 900574 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B1351679 : Blo 900574 1351679 := bstep (se 1 (by rfl) ⟨1013759, by rfl⟩ : syracuseStep 1351679 = 2027519) B2027519
theorem B43951319 : Blo 900574 43951319 := bstep (se 1 (by rfl) ⟨32963489, by rfl⟩ : syracuseStep 43951319 = 65926979) B65926979
theorem B24651677 : Blo 900574 24651677 := bstep (se 3 (by rfl) ⟨4622189, by rfl⟩ : syracuseStep 24651677 = 9244379) B9244379
theorem B901167 : Blo 900574 901167 := bstep (se 1 (by rfl) ⟨675875, by rfl⟩ : syracuseStep 901167 = 1351751) B1351751
theorem B903039 : Blo 900574 903039 := bstep (se 1 (by rfl) ⟨677279, by rfl⟩ : syracuseStep 903039 = 1354559) B1354559
theorem B1624303 : Blo 900574 1624303 := bstep (se 1 (by rfl) ⟨1218227, by rfl⟩ : syracuseStep 1624303 = 2436455) B2436455
theorem B903931 : Blo 900574 903931 := bstep (se 1 (by rfl) ⟨677948, by rfl⟩ : syracuseStep 903931 = 1355897) B1355897
theorem B3433499 : Blo 900574 3433499 := bstep (se 1 (by rfl) ⟨2575124, by rfl⟩ : syracuseStep 3433499 = 5150249) B5150249
theorem B3433711 : Blo 900574 3433711 := bstep (se 1 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 3433711 = 5150567) B5150567
theorem B2288027 : Blo 900574 2288027 := bstep (se 1 (by rfl) ⟨1716020, by rfl⟩ : syracuseStep 2288027 = 3432041) B3432041
theorem B3009529 : Blo 900574 3009529 := bstep (se 2 (by rfl) ⟨1128573, by rfl⟩ : syracuseStep 3009529 = 2257147) B2257147
theorem B29300879 : Blo 900574 29300879 := bstep (se 1 (by rfl) ⟨21975659, by rfl⟩ : syracuseStep 29300879 = 43951319) B43951319
theorem B8662949 : Blo 900574 8662949 := bstep (se 4 (by rfl) ⟨812151, by rfl⟩ : syracuseStep 8662949 = 1624303) B1624303
theorem B4012705 : Blo 900574 4012705 := bstep (se 2 (by rfl) ⟨1504764, by rfl⟩ : syracuseStep 4012705 = 3009529) B3009529
theorem B3522539 : Blo 900574 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B901119 : Blo 900574 901119 := bstep (se 1 (by rfl) ⟨675839, by rfl⟩ : syracuseStep 901119 = 1351679) B1351679
theorem B16434451 : Blo 900574 16434451 := bstep (se 1 (by rfl) ⟨12325838, by rfl⟩ : syracuseStep 16434451 = 24651677) B24651677
theorem B1525351 : Blo 900574 1525351 := bstep (se 1 (by rfl) ⟨1144013, by rfl⟩ : syracuseStep 1525351 = 2288027) B2288027
theorem B4578281 : Blo 900574 4578281 := bstep (se 2 (by rfl) ⟨1716855, by rfl⟩ : syracuseStep 4578281 = 3433711) B3433711
theorem B2288999 : Blo 900574 2288999 := bstep (se 1 (by rfl) ⟨1716749, by rfl⟩ : syracuseStep 2288999 = 3433499) B3433499
theorem B2033801 : Blo 900574 2033801 := bstep (se 2 (by rfl) ⟨762675, by rfl⟩ : syracuseStep 2033801 = 1525351) B1525351
theorem B19533919 : Blo 900574 19533919 := bstep (se 1 (by rfl) ⟨14650439, by rfl⟩ : syracuseStep 19533919 = 29300879) B29300879
theorem B3052187 : Blo 900574 3052187 := bstep (se 1 (by rfl) ⟨2289140, by rfl⟩ : syracuseStep 3052187 = 4578281) B4578281
theorem B5775299 : Blo 900574 5775299 := bstep (se 1 (by rfl) ⟨4331474, by rfl⟩ : syracuseStep 5775299 = 8662949) B8662949
theorem B5350273 : Blo 900574 5350273 := bstep (se 2 (by rfl) ⟨2006352, by rfl⟩ : syracuseStep 5350273 = 4012705) B4012705
theorem B1525999 : Blo 900574 1525999 := bstep (se 1 (by rfl) ⟨1144499, by rfl⟩ : syracuseStep 1525999 = 2288999) B2288999
theorem B2348359 : Blo 900574 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B21912601 : Blo 900574 21912601 := bstep (se 2 (by rfl) ⟨8217225, by rfl⟩ : syracuseStep 21912601 = 16434451) B16434451
theorem B2034665 : Blo 900574 2034665 := bstep (se 2 (by rfl) ⟨762999, by rfl⟩ : syracuseStep 2034665 = 1525999) B1525999
theorem B2034791 : Blo 900574 2034791 := bstep (se 1 (by rfl) ⟨1526093, by rfl⟩ : syracuseStep 2034791 = 3052187) B3052187
theorem B12524581 : Blo 900574 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B1355867 : Blo 900574 1355867 := bstep (se 1 (by rfl) ⟨1016900, by rfl⟩ : syracuseStep 1355867 = 2033801) B2033801
theorem B3850199 : Blo 900574 3850199 := bstep (se 1 (by rfl) ⟨2887649, by rfl⟩ : syracuseStep 3850199 = 5775299) B5775299
theorem B29216801 : Blo 900574 29216801 := bstep (se 2 (by rfl) ⟨10956300, by rfl⟩ : syracuseStep 29216801 = 21912601) B21912601
theorem B28534789 : Blo 900574 28534789 := bstep (se 4 (by rfl) ⟨2675136, by rfl⟩ : syracuseStep 28534789 = 5350273) B5350273
theorem B26045225 : Blo 900574 26045225 := bstep (se 2 (by rfl) ⟨9766959, by rfl⟩ : syracuseStep 26045225 = 19533919) B19533919
theorem B38046385 : Blo 900574 38046385 := bstep (se 2 (by rfl) ⟨14267394, by rfl⟩ : syracuseStep 38046385 = 28534789) B28534789
theorem B2566799 : Blo 900574 2566799 := bstep (se 1 (by rfl) ⟨1925099, by rfl⟩ : syracuseStep 2566799 = 3850199) B3850199
theorem B1356443 : Blo 900574 1356443 := bstep (se 1 (by rfl) ⟨1017332, by rfl⟩ : syracuseStep 1356443 = 2034665) B2034665
theorem B1356527 : Blo 900574 1356527 := bstep (se 1 (by rfl) ⟨1017395, by rfl⟩ : syracuseStep 1356527 = 2034791) B2034791
theorem B19477867 : Blo 900574 19477867 := bstep (se 1 (by rfl) ⟨14608400, by rfl⟩ : syracuseStep 19477867 = 29216801) B29216801
theorem B903911 : Blo 900574 903911 := bstep (se 1 (by rfl) ⟨677933, by rfl⟩ : syracuseStep 903911 = 1355867) B1355867
theorem B16699441 : Blo 900574 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B17363483 : Blo 900574 17363483 := bstep (se 1 (by rfl) ⟨13022612, by rfl⟩ : syracuseStep 17363483 = 26045225) B26045225
theorem B50728513 : Blo 900574 50728513 := bstep (se 2 (by rfl) ⟨19023192, by rfl⟩ : syracuseStep 50728513 = 38046385) B38046385
theorem B1711199 : Blo 900574 1711199 := bstep (se 1 (by rfl) ⟨1283399, by rfl⟩ : syracuseStep 1711199 = 2566799) B2566799
theorem B11575655 : Blo 900574 11575655 := bstep (se 1 (by rfl) ⟨8681741, by rfl⟩ : syracuseStep 11575655 = 17363483) B17363483
theorem B22265921 : Blo 900574 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B25970489 : Blo 900574 25970489 := bstep (se 2 (by rfl) ⟨9738933, by rfl⟩ : syracuseStep 25970489 = 19477867) B19477867
theorem B904295 : Blo 900574 904295 := bstep (se 1 (by rfl) ⟨678221, by rfl⟩ : syracuseStep 904295 = 1356443) B1356443
theorem B904351 : Blo 900574 904351 := bstep (se 1 (by rfl) ⟨678263, by rfl⟩ : syracuseStep 904351 = 1356527) B1356527
theorem B14843947 : Blo 900574 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B67638017 : Blo 900574 67638017 := bstep (se 2 (by rfl) ⟨25364256, by rfl⟩ : syracuseStep 67638017 = 50728513) B50728513
theorem B17313659 : Blo 900574 17313659 := bstep (se 1 (by rfl) ⟨12985244, by rfl⟩ : syracuseStep 17313659 = 25970489) B25970489
theorem B7717103 : Blo 900574 7717103 := bstep (se 1 (by rfl) ⟨5787827, by rfl⟩ : syracuseStep 7717103 = 11575655) B11575655
theorem B1140799 : Blo 900574 1140799 := bstep (se 1 (by rfl) ⟨855599, by rfl⟩ : syracuseStep 1140799 = 1711199) B1711199
theorem B19791929 : Blo 900574 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B5144735 : Blo 900574 5144735 := bstep (se 1 (by rfl) ⟨3858551, by rfl⟩ : syracuseStep 5144735 = 7717103) B7717103
theorem B45092011 : Blo 900574 45092011 := bstep (se 1 (by rfl) ⟨33819008, by rfl⟩ : syracuseStep 45092011 = 67638017) B67638017
theorem B11542439 : Blo 900574 11542439 := bstep (se 1 (by rfl) ⟨8656829, by rfl⟩ : syracuseStep 11542439 = 17313659) B17313659
theorem B1521065 : Blo 900574 1521065 := bstep (se 2 (by rfl) ⟨570399, by rfl⟩ : syracuseStep 1521065 = 1140799) B1140799
theorem B13194619 : Blo 900574 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B3429823 : Blo 900574 3429823 := bstep (se 1 (by rfl) ⟨2572367, by rfl⟩ : syracuseStep 3429823 = 5144735) B5144735
theorem B60122681 : Blo 900574 60122681 := bstep (se 2 (by rfl) ⟨22546005, by rfl⟩ : syracuseStep 60122681 = 45092011) B45092011
theorem B7694959 : Blo 900574 7694959 := bstep (se 1 (by rfl) ⟨5771219, by rfl⟩ : syracuseStep 7694959 = 11542439) B11542439
theorem B1014043 : Blo 900574 1014043 := bstep (se 1 (by rfl) ⟨760532, by rfl⟩ : syracuseStep 1014043 = 1521065) B1521065
theorem B10259945 : Blo 900574 10259945 := bstep (se 2 (by rfl) ⟨3847479, by rfl⟩ : syracuseStep 10259945 = 7694959) B7694959
theorem B40081787 : Blo 900574 40081787 := bstep (se 1 (by rfl) ⟨30061340, by rfl⟩ : syracuseStep 40081787 = 60122681) B60122681
theorem B1352057 : Blo 900574 1352057 := bstep (se 2 (by rfl) ⟨507021, by rfl⟩ : syracuseStep 1352057 = 1014043) B1014043
theorem B4573097 : Blo 900574 4573097 := bstep (se 2 (by rfl) ⟨1714911, by rfl⟩ : syracuseStep 4573097 = 3429823) B3429823
theorem B70371301 : Blo 900574 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B3048731 : Blo 900574 3048731 := bstep (se 1 (by rfl) ⟨2286548, by rfl⟩ : syracuseStep 3048731 = 4573097) B4573097
theorem B93828401 : Blo 900574 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B26721191 : Blo 900574 26721191 := bstep (se 1 (by rfl) ⟨20040893, by rfl⟩ : syracuseStep 26721191 = 40081787) B40081787
theorem B901371 : Blo 900574 901371 := bstep (se 1 (by rfl) ⟨676028, by rfl⟩ : syracuseStep 901371 = 1352057) B1352057
theorem B6839963 : Blo 900574 6839963 := bstep (se 1 (by rfl) ⟨5129972, by rfl⟩ : syracuseStep 6839963 = 10259945) B10259945
theorem B2032487 : Blo 900574 2032487 := bstep (se 1 (by rfl) ⟨1524365, by rfl⟩ : syracuseStep 2032487 = 3048731) B3048731
theorem B4559975 : Blo 900574 4559975 := bstep (se 1 (by rfl) ⟨3419981, by rfl⟩ : syracuseStep 4559975 = 6839963) B6839963
theorem B17814127 : Blo 900574 17814127 := bstep (se 1 (by rfl) ⟨13360595, by rfl⟩ : syracuseStep 17814127 = 26721191) B26721191
theorem B62552267 : Blo 900574 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B1354991 : Blo 900574 1354991 := bstep (se 1 (by rfl) ⟨1016243, by rfl⟩ : syracuseStep 1354991 = 2032487) B2032487
theorem B41701511 : Blo 900574 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B3039983 : Blo 900574 3039983 := bstep (se 1 (by rfl) ⟨2279987, by rfl⟩ : syracuseStep 3039983 = 4559975) B4559975
theorem B23752169 : Blo 900574 23752169 := bstep (se 2 (by rfl) ⟨8907063, by rfl⟩ : syracuseStep 23752169 = 17814127) B17814127
theorem B15834779 : Blo 900574 15834779 := bstep (se 1 (by rfl) ⟨11876084, by rfl⟩ : syracuseStep 15834779 = 23752169) B23752169
theorem B903327 : Blo 900574 903327 := bstep (se 1 (by rfl) ⟨677495, by rfl⟩ : syracuseStep 903327 = 1354991) B1354991
theorem B111204029 : Blo 900574 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B2026655 : Blo 900574 2026655 := bstep (se 1 (by rfl) ⟨1519991, by rfl⟩ : syracuseStep 2026655 = 3039983) B3039983
theorem B10556519 : Blo 900574 10556519 := bstep (se 1 (by rfl) ⟨7917389, by rfl⟩ : syracuseStep 10556519 = 15834779) B15834779
theorem B1351103 : Blo 900574 1351103 := bstep (se 1 (by rfl) ⟨1013327, by rfl⟩ : syracuseStep 1351103 = 2026655) B2026655
theorem B296544077 : Blo 900574 296544077 := bstep (se 3 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 296544077 = 111204029) B111204029
theorem B197696051 : Blo 900574 197696051 := bstep (se 1 (by rfl) ⟨148272038, by rfl⟩ : syracuseStep 197696051 = 296544077) B296544077
theorem B112602869 : Blo 900574 112602869 := bstep (se 5 (by rfl) ⟨5278259, by rfl⟩ : syracuseStep 112602869 = 10556519) B10556519
theorem B900735 : Blo 900574 900735 := bstep (se 1 (by rfl) ⟨675551, by rfl⟩ : syracuseStep 900735 = 1351103) B1351103
theorem B131797367 : Blo 900574 131797367 := bstep (se 1 (by rfl) ⟨98848025, by rfl⟩ : syracuseStep 131797367 = 197696051) B197696051
theorem B75068579 : Blo 900574 75068579 := bstep (se 1 (by rfl) ⟨56301434, by rfl⟩ : syracuseStep 75068579 = 112602869) B112602869
theorem B200182877 : Blo 900574 200182877 := bstep (se 3 (by rfl) ⟨37534289, by rfl⟩ : syracuseStep 200182877 = 75068579) B75068579
theorem B87864911 : Blo 900574 87864911 := bstep (se 1 (by rfl) ⟨65898683, by rfl⟩ : syracuseStep 87864911 = 131797367) B131797367
theorem B58576607 : Blo 900574 58576607 := bstep (se 1 (by rfl) ⟨43932455, by rfl⟩ : syracuseStep 58576607 = 87864911) B87864911
theorem B133455251 : Blo 900574 133455251 := bstep (se 1 (by rfl) ⟨100091438, by rfl⟩ : syracuseStep 133455251 = 200182877) B200182877
theorem B88970167 : Blo 900574 88970167 := bstep (se 1 (by rfl) ⟨66727625, by rfl⟩ : syracuseStep 88970167 = 133455251) B133455251
theorem B39051071 : Blo 900574 39051071 := bstep (se 1 (by rfl) ⟨29288303, by rfl⟩ : syracuseStep 39051071 = 58576607) B58576607
theorem B118626889 : Blo 900574 118626889 := bstep (se 2 (by rfl) ⟨44485083, by rfl⟩ : syracuseStep 118626889 = 88970167) B88970167
theorem B26034047 : Blo 900574 26034047 := bstep (se 1 (by rfl) ⟨19525535, by rfl⟩ : syracuseStep 26034047 = 39051071) B39051071
theorem B17356031 : Blo 900574 17356031 := bstep (se 1 (by rfl) ⟨13017023, by rfl⟩ : syracuseStep 17356031 = 26034047) B26034047
theorem B158169185 : Blo 900574 158169185 := bstep (se 2 (by rfl) ⟨59313444, by rfl⟩ : syracuseStep 158169185 = 118626889) B118626889
theorem B11570687 : Blo 900574 11570687 := bstep (se 1 (by rfl) ⟨8678015, by rfl⟩ : syracuseStep 11570687 = 17356031) B17356031
theorem B105446123 : Blo 900574 105446123 := bstep (se 1 (by rfl) ⟨79084592, by rfl⟩ : syracuseStep 105446123 = 158169185) B158169185
theorem B70297415 : Blo 900574 70297415 := bstep (se 1 (by rfl) ⟨52723061, by rfl⟩ : syracuseStep 70297415 = 105446123) B105446123
theorem B7713791 : Blo 900574 7713791 := bstep (se 1 (by rfl) ⟨5785343, by rfl⟩ : syracuseStep 7713791 = 11570687) B11570687
theorem B46864943 : Blo 900574 46864943 := bstep (se 1 (by rfl) ⟨35148707, by rfl⟩ : syracuseStep 46864943 = 70297415) B70297415
theorem B5142527 : Blo 900574 5142527 := bstep (se 1 (by rfl) ⟨3856895, by rfl⟩ : syracuseStep 5142527 = 7713791) B7713791
theorem B31243295 : Blo 900574 31243295 := bstep (se 1 (by rfl) ⟨23432471, by rfl⟩ : syracuseStep 31243295 = 46864943) B46864943
theorem B3428351 : Blo 900574 3428351 := bstep (se 1 (by rfl) ⟨2571263, by rfl⟩ : syracuseStep 3428351 = 5142527) B5142527
theorem B20828863 : Blo 900574 20828863 := bstep (se 1 (by rfl) ⟨15621647, by rfl⟩ : syracuseStep 20828863 = 31243295) B31243295
theorem B2285567 : Blo 900574 2285567 := bstep (se 1 (by rfl) ⟨1714175, by rfl⟩ : syracuseStep 2285567 = 3428351) B3428351
theorem B1523711 : Blo 900574 1523711 := bstep (se 1 (by rfl) ⟨1142783, by rfl⟩ : syracuseStep 1523711 = 2285567) B2285567
theorem B27771817 : Blo 900574 27771817 := bstep (se 2 (by rfl) ⟨10414431, by rfl⟩ : syracuseStep 27771817 = 20828863) B20828863
theorem B37029089 : Blo 900574 37029089 := bstep (se 2 (by rfl) ⟨13885908, by rfl⟩ : syracuseStep 37029089 = 27771817) B27771817
theorem B1015807 : Blo 900574 1015807 := bstep (se 1 (by rfl) ⟨761855, by rfl⟩ : syracuseStep 1015807 = 1523711) B1523711
theorem B1354409 : Blo 900574 1354409 := bstep (se 2 (by rfl) ⟨507903, by rfl⟩ : syracuseStep 1354409 = 1015807) B1015807
theorem B24686059 : Blo 900574 24686059 := bstep (se 1 (by rfl) ⟨18514544, by rfl⟩ : syracuseStep 24686059 = 37029089) B37029089
theorem B32914745 : Blo 900574 32914745 := bstep (se 2 (by rfl) ⟨12343029, by rfl⟩ : syracuseStep 32914745 = 24686059) B24686059
theorem B902939 : Blo 900574 902939 := bstep (se 1 (by rfl) ⟨677204, by rfl⟩ : syracuseStep 902939 = 1354409) B1354409
theorem B21943163 : Blo 900574 21943163 := bstep (se 1 (by rfl) ⟨16457372, by rfl⟩ : syracuseStep 21943163 = 32914745) B32914745
theorem B14628775 : Blo 900574 14628775 := bstep (se 1 (by rfl) ⟨10971581, by rfl⟩ : syracuseStep 14628775 = 21943163) B21943163
theorem B19505033 : Blo 900574 19505033 := bstep (se 2 (by rfl) ⟨7314387, by rfl⟩ : syracuseStep 19505033 = 14628775) B14628775
theorem B13003355 : Blo 900574 13003355 := bstep (se 1 (by rfl) ⟨9752516, by rfl⟩ : syracuseStep 13003355 = 19505033) B19505033
theorem B8668903 : Blo 900574 8668903 := bstep (se 1 (by rfl) ⟨6501677, by rfl⟩ : syracuseStep 8668903 = 13003355) B13003355
theorem B11558537 : Blo 900574 11558537 := bstep (se 2 (by rfl) ⟨4334451, by rfl⟩ : syracuseStep 11558537 = 8668903) B8668903
theorem B7705691 : Blo 900574 7705691 := bstep (se 1 (by rfl) ⟨5779268, by rfl⟩ : syracuseStep 7705691 = 11558537) B11558537
theorem B5137127 : Blo 900574 5137127 := bstep (se 1 (by rfl) ⟨3852845, by rfl⟩ : syracuseStep 5137127 = 7705691) B7705691
theorem B3424751 : Blo 900574 3424751 := bstep (se 1 (by rfl) ⟨2568563, by rfl⟩ : syracuseStep 3424751 = 5137127) B5137127
theorem B2283167 : Blo 900574 2283167 := bstep (se 1 (by rfl) ⟨1712375, by rfl⟩ : syracuseStep 2283167 = 3424751) B3424751
theorem B1522111 : Blo 900574 1522111 := bstep (se 1 (by rfl) ⟨1141583, by rfl⟩ : syracuseStep 1522111 = 2283167) B2283167
theorem B2029481 : Blo 900574 2029481 := bstep (se 2 (by rfl) ⟨761055, by rfl⟩ : syracuseStep 2029481 = 1522111) B1522111
theorem B1352987 : Blo 900574 1352987 := bstep (se 1 (by rfl) ⟨1014740, by rfl⟩ : syracuseStep 1352987 = 2029481) B2029481
theorem B901991 : Blo 900574 901991 := bstep (se 1 (by rfl) ⟨676493, by rfl⟩ : syracuseStep 901991 = 1352987) B1352987

theorem C0 (j : ℕ) (h1 : 225143 ≤ j) (h2 : j ≤ 225842) : Blo 900574 (4 * j + 3) := by
  interval_cases j
  · exact B900575
  · exact B900579
  · exact B900583
  · exact B900587
  · exact B900591
  · exact B900595
  · exact B900599
  · exact B900603
  · exact B900607
  · exact B900611
  · exact B900615
  · exact B900619
  · exact B900623
  · exact B900627
  · exact B900631
  · exact B900635
  · exact B900639
  · exact B900643
  · exact B900647
  · exact B900651
  · exact B900655
  · exact B900659
  · exact B900663
  · exact B900667
  · exact B900671
  · exact B900675
  · exact B900679
  · exact B900683
  · exact B900687
  · exact B900691
  · exact B900695
  · exact B900699
  · exact B900703
  · exact B900707
  · exact B900711
  · exact B900715
  · exact B900719
  · exact B900723
  · exact B900727
  · exact B900731
  · exact B900735
  · exact B900739
  · exact B900743
  · exact B900747
  · exact B900751
  · exact B900755
  · exact B900759
  · exact B900763
  · exact B900767
  · exact B900771
  · exact B900775
  · exact B900779
  · exact B900783
  · exact B900787
  · exact B900791
  · exact B900795
  · exact B900799
  · exact B900803
  · exact B900807
  · exact B900811
  · exact B900815
  · exact B900819
  · exact B900823
  · exact B900827
  · exact B900831
  · exact B900835
  · exact B900839
  · exact B900843
  · exact B900847
  · exact B900851
  · exact B900855
  · exact B900859
  · exact B900863
  · exact B900867
  · exact B900871
  · exact B900875
  · exact B900879
  · exact B900883
  · exact B900887
  · exact B900891
  · exact B900895
  · exact B900899
  · exact B900903
  · exact B900907
  · exact B900911
  · exact B900915
  · exact B900919
  · exact B900923
  · exact B900927
  · exact B900931
  · exact B900935
  · exact B900939
  · exact B900943
  · exact B900947
  · exact B900951
  · exact B900955
  · exact B900959
  · exact B900963
  · exact B900967
  · exact B900971
  · exact B900975
  · exact B900979
  · exact B900983
  · exact B900987
  · exact B900991
  · exact B900995
  · exact B900999
  · exact B901003
  · exact B901007
  · exact B901011
  · exact B901015
  · exact B901019
  · exact B901023
  · exact B901027
  · exact B901031
  · exact B901035
  · exact B901039
  · exact B901043
  · exact B901047
  · exact B901051
  · exact B901055
  · exact B901059
  · exact B901063
  · exact B901067
  · exact B901071
  · exact B901075
  · exact B901079
  · exact B901083
  · exact B901087
  · exact B901091
  · exact B901095
  · exact B901099
  · exact B901103
  · exact B901107
  · exact B901111
  · exact B901115
  · exact B901119
  · exact B901123
  · exact B901127
  · exact B901131
  · exact B901135
  · exact B901139
  · exact B901143
  · exact B901147
  · exact B901151
  · exact B901155
  · exact B901159
  · exact B901163
  · exact B901167
  · exact B901171
  · exact B901175
  · exact B901179
  · exact B901183
  · exact B901187
  · exact B901191
  · exact B901195
  · exact B901199
  · exact B901203
  · exact B901207
  · exact B901211
  · exact B901215
  · exact B901219
  · exact B901223
  · exact B901227
  · exact B901231
  · exact B901235
  · exact B901239
  · exact B901243
  · exact B901247
  · exact B901251
  · exact B901255
  · exact B901259
  · exact B901263
  · exact B901267
  · exact B901271
  · exact B901275
  · exact B901279
  · exact B901283
  · exact B901287
  · exact B901291
  · exact B901295
  · exact B901299
  · exact B901303
  · exact B901307
  · exact B901311
  · exact B901315
  · exact B901319
  · exact B901323
  · exact B901327
  · exact B901331
  · exact B901335
  · exact B901339
  · exact B901343
  · exact B901347
  · exact B901351
  · exact B901355
  · exact B901359
  · exact B901363
  · exact B901367
  · exact B901371
  · exact B901375
  · exact B901379
  · exact B901383
  · exact B901387
  · exact B901391
  · exact B901395
  · exact B901399
  · exact B901403
  · exact B901407
  · exact B901411
  · exact B901415
  · exact B901419
  · exact B901423
  · exact B901427
  · exact B901431
  · exact B901435
  · exact B901439
  · exact B901443
  · exact B901447
  · exact B901451
  · exact B901455
  · exact B901459
  · exact B901463
  · exact B901467
  · exact B901471
  · exact B901475
  · exact B901479
  · exact B901483
  · exact B901487
  · exact B901491
  · exact B901495
  · exact B901499
  · exact B901503
  · exact B901507
  · exact B901511
  · exact B901515
  · exact B901519
  · exact B901523
  · exact B901527
  · exact B901531
  · exact B901535
  · exact B901539
  · exact B901543
  · exact B901547
  · exact B901551
  · exact B901555
  · exact B901559
  · exact B901563
  · exact B901567
  · exact B901571
  · exact B901575
  · exact B901579
  · exact B901583
  · exact B901587
  · exact B901591
  · exact B901595
  · exact B901599
  · exact B901603
  · exact B901607
  · exact B901611
  · exact B901615
  · exact B901619
  · exact B901623
  · exact B901627
  · exact B901631
  · exact B901635
  · exact B901639
  · exact B901643
  · exact B901647
  · exact B901651
  · exact B901655
  · exact B901659
  · exact B901663
  · exact B901667
  · exact B901671
  · exact B901675
  · exact B901679
  · exact B901683
  · exact B901687
  · exact B901691
  · exact B901695
  · exact B901699
  · exact B901703
  · exact B901707
  · exact B901711
  · exact B901715
  · exact B901719
  · exact B901723
  · exact B901727
  · exact B901731
  · exact B901735
  · exact B901739
  · exact B901743
  · exact B901747
  · exact B901751
  · exact B901755
  · exact B901759
  · exact B901763
  · exact B901767
  · exact B901771
  · exact B901775
  · exact B901779
  · exact B901783
  · exact B901787
  · exact B901791
  · exact B901795
  · exact B901799
  · exact B901803
  · exact B901807
  · exact B901811
  · exact B901815
  · exact B901819
  · exact B901823
  · exact B901827
  · exact B901831
  · exact B901835
  · exact B901839
  · exact B901843
  · exact B901847
  · exact B901851
  · exact B901855
  · exact B901859
  · exact B901863
  · exact B901867
  · exact B901871
  · exact B901875
  · exact B901879
  · exact B901883
  · exact B901887
  · exact B901891
  · exact B901895
  · exact B901899
  · exact B901903
  · exact B901907
  · exact B901911
  · exact B901915
  · exact B901919
  · exact B901923
  · exact B901927
  · exact B901931
  · exact B901935
  · exact B901939
  · exact B901943
  · exact B901947
  · exact B901951
  · exact B901955
  · exact B901959
  · exact B901963
  · exact B901967
  · exact B901971
  · exact B901975
  · exact B901979
  · exact B901983
  · exact B901987
  · exact B901991
  · exact B901995
  · exact B901999
  · exact B902003
  · exact B902007
  · exact B902011
  · exact B902015
  · exact B902019
  · exact B902023
  · exact B902027
  · exact B902031
  · exact B902035
  · exact B902039
  · exact B902043
  · exact B902047
  · exact B902051
  · exact B902055
  · exact B902059
  · exact B902063
  · exact B902067
  · exact B902071
  · exact B902075
  · exact B902079
  · exact B902083
  · exact B902087
  · exact B902091
  · exact B902095
  · exact B902099
  · exact B902103
  · exact B902107
  · exact B902111
  · exact B902115
  · exact B902119
  · exact B902123
  · exact B902127
  · exact B902131
  · exact B902135
  · exact B902139
  · exact B902143
  · exact B902147
  · exact B902151
  · exact B902155
  · exact B902159
  · exact B902163
  · exact B902167
  · exact B902171
  · exact B902175
  · exact B902179
  · exact B902183
  · exact B902187
  · exact B902191
  · exact B902195
  · exact B902199
  · exact B902203
  · exact B902207
  · exact B902211
  · exact B902215
  · exact B902219
  · exact B902223
  · exact B902227
  · exact B902231
  · exact B902235
  · exact B902239
  · exact B902243
  · exact B902247
  · exact B902251
  · exact B902255
  · exact B902259
  · exact B902263
  · exact B902267
  · exact B902271
  · exact B902275
  · exact B902279
  · exact B902283
  · exact B902287
  · exact B902291
  · exact B902295
  · exact B902299
  · exact B902303
  · exact B902307
  · exact B902311
  · exact B902315
  · exact B902319
  · exact B902323
  · exact B902327
  · exact B902331
  · exact B902335
  · exact B902339
  · exact B902343
  · exact B902347
  · exact B902351
  · exact B902355
  · exact B902359
  · exact B902363
  · exact B902367
  · exact B902371
  · exact B902375
  · exact B902379
  · exact B902383
  · exact B902387
  · exact B902391
  · exact B902395
  · exact B902399
  · exact B902403
  · exact B902407
  · exact B902411
  · exact B902415
  · exact B902419
  · exact B902423
  · exact B902427
  · exact B902431
  · exact B902435
  · exact B902439
  · exact B902443
  · exact B902447
  · exact B902451
  · exact B902455
  · exact B902459
  · exact B902463
  · exact B902467
  · exact B902471
  · exact B902475
  · exact B902479
  · exact B902483
  · exact B902487
  · exact B902491
  · exact B902495
  · exact B902499
  · exact B902503
  · exact B902507
  · exact B902511
  · exact B902515
  · exact B902519
  · exact B902523
  · exact B902527
  · exact B902531
  · exact B902535
  · exact B902539
  · exact B902543
  · exact B902547
  · exact B902551
  · exact B902555
  · exact B902559
  · exact B902563
  · exact B902567
  · exact B902571
  · exact B902575
  · exact B902579
  · exact B902583
  · exact B902587
  · exact B902591
  · exact B902595
  · exact B902599
  · exact B902603
  · exact B902607
  · exact B902611
  · exact B902615
  · exact B902619
  · exact B902623
  · exact B902627
  · exact B902631
  · exact B902635
  · exact B902639
  · exact B902643
  · exact B902647
  · exact B902651
  · exact B902655
  · exact B902659
  · exact B902663
  · exact B902667
  · exact B902671
  · exact B902675
  · exact B902679
  · exact B902683
  · exact B902687
  · exact B902691
  · exact B902695
  · exact B902699
  · exact B902703
  · exact B902707
  · exact B902711
  · exact B902715
  · exact B902719
  · exact B902723
  · exact B902727
  · exact B902731
  · exact B902735
  · exact B902739
  · exact B902743
  · exact B902747
  · exact B902751
  · exact B902755
  · exact B902759
  · exact B902763
  · exact B902767
  · exact B902771
  · exact B902775
  · exact B902779
  · exact B902783
  · exact B902787
  · exact B902791
  · exact B902795
  · exact B902799
  · exact B902803
  · exact B902807
  · exact B902811
  · exact B902815
  · exact B902819
  · exact B902823
  · exact B902827
  · exact B902831
  · exact B902835
  · exact B902839
  · exact B902843
  · exact B902847
  · exact B902851
  · exact B902855
  · exact B902859
  · exact B902863
  · exact B902867
  · exact B902871
  · exact B902875
  · exact B902879
  · exact B902883
  · exact B902887
  · exact B902891
  · exact B902895
  · exact B902899
  · exact B902903
  · exact B902907
  · exact B902911
  · exact B902915
  · exact B902919
  · exact B902923
  · exact B902927
  · exact B902931
  · exact B902935
  · exact B902939
  · exact B902943
  · exact B902947
  · exact B902951
  · exact B902955
  · exact B902959
  · exact B902963
  · exact B902967
  · exact B902971
  · exact B902975
  · exact B902979
  · exact B902983
  · exact B902987
  · exact B902991
  · exact B902995
  · exact B902999
  · exact B903003
  · exact B903007
  · exact B903011
  · exact B903015
  · exact B903019
  · exact B903023
  · exact B903027
  · exact B903031
  · exact B903035
  · exact B903039
  · exact B903043
  · exact B903047
  · exact B903051
  · exact B903055
  · exact B903059
  · exact B903063
  · exact B903067
  · exact B903071
  · exact B903075
  · exact B903079
  · exact B903083
  · exact B903087
  · exact B903091
  · exact B903095
  · exact B903099
  · exact B903103
  · exact B903107
  · exact B903111
  · exact B903115
  · exact B903119
  · exact B903123
  · exact B903127
  · exact B903131
  · exact B903135
  · exact B903139
  · exact B903143
  · exact B903147
  · exact B903151
  · exact B903155
  · exact B903159
  · exact B903163
  · exact B903167
  · exact B903171
  · exact B903175
  · exact B903179
  · exact B903183
  · exact B903187
  · exact B903191
  · exact B903195
  · exact B903199
  · exact B903203
  · exact B903207
  · exact B903211
  · exact B903215
  · exact B903219
  · exact B903223
  · exact B903227
  · exact B903231
  · exact B903235
  · exact B903239
  · exact B903243
  · exact B903247
  · exact B903251
  · exact B903255
  · exact B903259
  · exact B903263
  · exact B903267
  · exact B903271
  · exact B903275
  · exact B903279
  · exact B903283
  · exact B903287
  · exact B903291
  · exact B903295
  · exact B903299
  · exact B903303
  · exact B903307
  · exact B903311
  · exact B903315
  · exact B903319
  · exact B903323
  · exact B903327
  · exact B903331
  · exact B903335
  · exact B903339
  · exact B903343
  · exact B903347
  · exact B903351
  · exact B903355
  · exact B903359
  · exact B903363
  · exact B903367
  · exact B903371

theorem C1 (j : ℕ) (h1 : 225843 ≤ j) (h2 : j ≤ 226142) : Blo 900574 (4 * j + 3) := by
  interval_cases j
  · exact B903375
  · exact B903379
  · exact B903383
  · exact B903387
  · exact B903391
  · exact B903395
  · exact B903399
  · exact B903403
  · exact B903407
  · exact B903411
  · exact B903415
  · exact B903419
  · exact B903423
  · exact B903427
  · exact B903431
  · exact B903435
  · exact B903439
  · exact B903443
  · exact B903447
  · exact B903451
  · exact B903455
  · exact B903459
  · exact B903463
  · exact B903467
  · exact B903471
  · exact B903475
  · exact B903479
  · exact B903483
  · exact B903487
  · exact B903491
  · exact B903495
  · exact B903499
  · exact B903503
  · exact B903507
  · exact B903511
  · exact B903515
  · exact B903519
  · exact B903523
  · exact B903527
  · exact B903531
  · exact B903535
  · exact B903539
  · exact B903543
  · exact B903547
  · exact B903551
  · exact B903555
  · exact B903559
  · exact B903563
  · exact B903567
  · exact B903571
  · exact B903575
  · exact B903579
  · exact B903583
  · exact B903587
  · exact B903591
  · exact B903595
  · exact B903599
  · exact B903603
  · exact B903607
  · exact B903611
  · exact B903615
  · exact B903619
  · exact B903623
  · exact B903627
  · exact B903631
  · exact B903635
  · exact B903639
  · exact B903643
  · exact B903647
  · exact B903651
  · exact B903655
  · exact B903659
  · exact B903663
  · exact B903667
  · exact B903671
  · exact B903675
  · exact B903679
  · exact B903683
  · exact B903687
  · exact B903691
  · exact B903695
  · exact B903699
  · exact B903703
  · exact B903707
  · exact B903711
  · exact B903715
  · exact B903719
  · exact B903723
  · exact B903727
  · exact B903731
  · exact B903735
  · exact B903739
  · exact B903743
  · exact B903747
  · exact B903751
  · exact B903755
  · exact B903759
  · exact B903763
  · exact B903767
  · exact B903771
  · exact B903775
  · exact B903779
  · exact B903783
  · exact B903787
  · exact B903791
  · exact B903795
  · exact B903799
  · exact B903803
  · exact B903807
  · exact B903811
  · exact B903815
  · exact B903819
  · exact B903823
  · exact B903827
  · exact B903831
  · exact B903835
  · exact B903839
  · exact B903843
  · exact B903847
  · exact B903851
  · exact B903855
  · exact B903859
  · exact B903863
  · exact B903867
  · exact B903871
  · exact B903875
  · exact B903879
  · exact B903883
  · exact B903887
  · exact B903891
  · exact B903895
  · exact B903899
  · exact B903903
  · exact B903907
  · exact B903911
  · exact B903915
  · exact B903919
  · exact B903923
  · exact B903927
  · exact B903931
  · exact B903935
  · exact B903939
  · exact B903943
  · exact B903947
  · exact B903951
  · exact B903955
  · exact B903959
  · exact B903963
  · exact B903967
  · exact B903971
  · exact B903975
  · exact B903979
  · exact B903983
  · exact B903987
  · exact B903991
  · exact B903995
  · exact B903999
  · exact B904003
  · exact B904007
  · exact B904011
  · exact B904015
  · exact B904019
  · exact B904023
  · exact B904027
  · exact B904031
  · exact B904035
  · exact B904039
  · exact B904043
  · exact B904047
  · exact B904051
  · exact B904055
  · exact B904059
  · exact B904063
  · exact B904067
  · exact B904071
  · exact B904075
  · exact B904079
  · exact B904083
  · exact B904087
  · exact B904091
  · exact B904095
  · exact B904099
  · exact B904103
  · exact B904107
  · exact B904111
  · exact B904115
  · exact B904119
  · exact B904123
  · exact B904127
  · exact B904131
  · exact B904135
  · exact B904139
  · exact B904143
  · exact B904147
  · exact B904151
  · exact B904155
  · exact B904159
  · exact B904163
  · exact B904167
  · exact B904171
  · exact B904175
  · exact B904179
  · exact B904183
  · exact B904187
  · exact B904191
  · exact B904195
  · exact B904199
  · exact B904203
  · exact B904207
  · exact B904211
  · exact B904215
  · exact B904219
  · exact B904223
  · exact B904227
  · exact B904231
  · exact B904235
  · exact B904239
  · exact B904243
  · exact B904247
  · exact B904251
  · exact B904255
  · exact B904259
  · exact B904263
  · exact B904267
  · exact B904271
  · exact B904275
  · exact B904279
  · exact B904283
  · exact B904287
  · exact B904291
  · exact B904295
  · exact B904299
  · exact B904303
  · exact B904307
  · exact B904311
  · exact B904315
  · exact B904319
  · exact B904323
  · exact B904327
  · exact B904331
  · exact B904335
  · exact B904339
  · exact B904343
  · exact B904347
  · exact B904351
  · exact B904355
  · exact B904359
  · exact B904363
  · exact B904367
  · exact B904371
  · exact B904375
  · exact B904379
  · exact B904383
  · exact B904387
  · exact B904391
  · exact B904395
  · exact B904399
  · exact B904403
  · exact B904407
  · exact B904411
  · exact B904415
  · exact B904419
  · exact B904423
  · exact B904427
  · exact B904431
  · exact B904435
  · exact B904439
  · exact B904443
  · exact B904447
  · exact B904451
  · exact B904455
  · exact B904459
  · exact B904463
  · exact B904467
  · exact B904471
  · exact B904475
  · exact B904479
  · exact B904483
  · exact B904487
  · exact B904491
  · exact B904495
  · exact B904499
  · exact B904503
  · exact B904507
  · exact B904511
  · exact B904515
  · exact B904519
  · exact B904523
  · exact B904527
  · exact B904531
  · exact B904535
  · exact B904539
  · exact B904543
  · exact B904547
  · exact B904551
  · exact B904555
  · exact B904559
  · exact B904563
  · exact B904567
  · exact B904571

theorem solution (m : ℕ) (hlo : 900574 ≤ m) (hhi : m ≤ 904574) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 225143 ≤ j := by omega
    have hj2 : j ≤ 226142 := by omega
    have hb : Blo 900574 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 225843 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
