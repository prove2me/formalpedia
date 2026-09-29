-- Prove2me | solution 1 for syracuse_descends_range_1617007_1619007
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:12:47.064957+00:00
-- url     : https://prove2.me/submissions/3b957f5e-86b0-45c7-ad1f-e04fc5cd3dcb

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


theorem B3457093 : Blo 1617007 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B2048105 : Blo 1617007 2048105 := bbase (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) (by norm_num)
theorem B4096109 : Blo 1617007 4096109 := bbase (se 3 (by rfl) ⟨768020, by rfl⟩ : syracuseStep 4096109 = 1536041) (by norm_num)
theorem B7774325 : Blo 1617007 7774325 := bbase (se 5 (by rfl) ⟨364421, by rfl⟩ : syracuseStep 7774325 = 728843) (by norm_num)
theorem B6144133 : Blo 1617007 6144133 := bbase (se 4 (by rfl) ⟨576012, by rfl⟩ : syracuseStep 6144133 = 1152025) (by norm_num)
theorem B1728649 : Blo 1617007 1728649 := bbase (se 2 (by rfl) ⟨648243, by rfl⟩ : syracuseStep 1728649 = 1296487) (by norm_num)
theorem B2048161 : Blo 1617007 2048161 := bbase (se 2 (by rfl) ⟨768060, by rfl⟩ : syracuseStep 2048161 = 1536121) (by norm_num)
theorem B3072181 : Blo 1617007 3072181 := bbase (se 5 (by rfl) ⟨144008, by rfl⟩ : syracuseStep 3072181 = 288017) (by norm_num)
theorem B1728721 : Blo 1617007 1728721 := bbase (se 2 (by rfl) ⟨648270, by rfl⟩ : syracuseStep 1728721 = 1296541) (by norm_num)
theorem B3457237 : Blo 1617007 3457237 := bbase (se 7 (by rfl) ⟨40514, by rfl⟩ : syracuseStep 3457237 = 81029) (by norm_num)
theorem B2048257 : Blo 1617007 2048257 := bbase (se 2 (by rfl) ⟨768096, by rfl⟩ : syracuseStep 2048257 = 1536193) (by norm_num)
theorem B3072325 : Blo 1617007 3072325 := bbase (se 4 (by rfl) ⟨288030, by rfl⟩ : syracuseStep 3072325 = 576061) (by norm_num)
theorem B3326285 : Blo 1617007 3326285 := bbase (se 3 (by rfl) ⟨623678, by rfl⟩ : syracuseStep 3326285 = 1247357) (by norm_num)
theorem B5833109 : Blo 1617007 5833109 := bbase (se 6 (by rfl) ⟨136713, by rfl⟩ : syracuseStep 5833109 = 273427) (by norm_num)
theorem B13304213 : Blo 1617007 13304213 := bbase (se 6 (by rfl) ⟨311817, by rfl⟩ : syracuseStep 13304213 = 623635) (by norm_num)
theorem B2048429 : Blo 1617007 2048429 := bbase (se 3 (by rfl) ⟨384080, by rfl⟩ : syracuseStep 2048429 = 768161) (by norm_num)
theorem B6144437 : Blo 1617007 6144437 := bbase (se 5 (by rfl) ⟨288020, by rfl⟩ : syracuseStep 6144437 = 576041) (by norm_num)
theorem B4096453 : Blo 1617007 4096453 := bbase (se 4 (by rfl) ⟨384042, by rfl⟩ : syracuseStep 4096453 = 768085) (by norm_num)
theorem B3072485 : Blo 1617007 3072485 := bbase (se 4 (by rfl) ⟨288045, by rfl⟩ : syracuseStep 3072485 = 576091) (by norm_num)
theorem B2048485 : Blo 1617007 2048485 := bbase (se 4 (by rfl) ⟨192045, by rfl⟩ : syracuseStep 2048485 = 384091) (by norm_num)
theorem B8192501 : Blo 1617007 8192501 := bbase (se 5 (by rfl) ⟨384023, by rfl⟩ : syracuseStep 8192501 = 768047) (by norm_num)
theorem B1819165 : Blo 1617007 1819165 := bbase (se 3 (by rfl) ⟨341093, by rfl⟩ : syracuseStep 1819165 = 682187) (by norm_num)
theorem B2302501 : Blo 1617007 2302501 := bbase (se 4 (by rfl) ⟨215859, by rfl⟩ : syracuseStep 2302501 = 431719) (by norm_num)
theorem B4096565 : Blo 1617007 4096565 := bbase (se 5 (by rfl) ⟨192026, by rfl⟩ : syracuseStep 4096565 = 384053) (by norm_num)
theorem B1819201 : Blo 1617007 1819201 := bbase (se 2 (by rfl) ⟨682200, by rfl⟩ : syracuseStep 1819201 = 1364401) (by norm_num)
theorem B2048581 : Blo 1617007 2048581 := bbase (se 4 (by rfl) ⟨192054, by rfl⟩ : syracuseStep 2048581 = 384109) (by norm_num)
theorem B3457613 : Blo 1617007 3457613 := bbase (se 3 (by rfl) ⟨648302, by rfl⟩ : syracuseStep 3457613 = 1296605) (by norm_num)
theorem B1819237 : Blo 1617007 1819237 := bbase (se 4 (by rfl) ⟨170553, by rfl⟩ : syracuseStep 1819237 = 341107) (by norm_num)
theorem B3072629 : Blo 1617007 3072629 := bbase (se 5 (by rfl) ⟨144029, by rfl⟩ : syracuseStep 3072629 = 288059) (by norm_num)
theorem B3326581 : Blo 1617007 3326581 := bbase (se 5 (by rfl) ⟨155933, by rfl⟩ : syracuseStep 3326581 = 311867) (by norm_num)
theorem B1819273 : Blo 1617007 1819273 := bbase (se 2 (by rfl) ⟨682227, by rfl⟩ : syracuseStep 1819273 = 1364455) (by norm_num)
theorem B2425517 : Blo 1617007 2425517 := bbase (se 3 (by rfl) ⟨454784, by rfl⟩ : syracuseStep 2425517 = 909569) (by norm_num)
theorem B1819309 : Blo 1617007 1819309 := bbase (se 3 (by rfl) ⟨341120, by rfl⟩ : syracuseStep 1819309 = 682241) (by norm_num)
theorem B2425541 : Blo 1617007 2425541 := bbase (se 4 (by rfl) ⟨227394, by rfl⟩ : syracuseStep 2425541 = 454789) (by norm_num)
theorem B1819345 : Blo 1617007 1819345 := bbase (se 2 (by rfl) ⟨682254, by rfl⟩ : syracuseStep 1819345 = 1364509) (by norm_num)
theorem B2425565 : Blo 1617007 2425565 := bbase (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) (by norm_num)
theorem B2048753 : Blo 1617007 2048753 := bbase (se 2 (by rfl) ⟨768282, by rfl⟩ : syracuseStep 2048753 = 1536565) (by norm_num)
theorem B2425589 : Blo 1617007 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B1819381 : Blo 1617007 1819381 := bbase (se 5 (by rfl) ⟨85283, by rfl⟩ : syracuseStep 1819381 = 170567) (by norm_num)
theorem B4096757 : Blo 1617007 4096757 := bbase (se 5 (by rfl) ⟨192035, by rfl⟩ : syracuseStep 4096757 = 384071) (by norm_num)
theorem B2425613 : Blo 1617007 2425613 := bbase (se 3 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 2425613 = 909605) (by norm_num)
theorem B1819417 : Blo 1617007 1819417 := bbase (se 2 (by rfl) ⟨682281, by rfl⟩ : syracuseStep 1819417 = 1364563) (by norm_num)
theorem B2728741 : Blo 1617007 2728741 := bbase (se 4 (by rfl) ⟨255819, by rfl⟩ : syracuseStep 2728741 = 511639) (by norm_num)
theorem B2425637 : Blo 1617007 2425637 := bbase (se 4 (by rfl) ⟨227403, by rfl⟩ : syracuseStep 2425637 = 454807) (by norm_num)
theorem B2048809 : Blo 1617007 2048809 := bbase (se 2 (by rfl) ⟨768303, by rfl⟩ : syracuseStep 2048809 = 1536607) (by norm_num)
theorem B2425661 : Blo 1617007 2425661 := bbase (se 3 (by rfl) ⟨454811, by rfl⟩ : syracuseStep 2425661 = 909623) (by norm_num)
theorem B1819453 : Blo 1617007 1819453 := bbase (se 3 (by rfl) ⟨341147, by rfl⟩ : syracuseStep 1819453 = 682295) (by norm_num)
theorem B2425685 : Blo 1617007 2425685 := bbase (se 9 (by rfl) ⟨7106, by rfl⟩ : syracuseStep 2425685 = 14213) (by norm_num)
theorem B1819489 : Blo 1617007 1819489 := bbase (se 2 (by rfl) ⟨682308, by rfl⟩ : syracuseStep 1819489 = 1364617) (by norm_num)
theorem B2425709 : Blo 1617007 2425709 := bbase (se 3 (by rfl) ⟨454820, by rfl⟩ : syracuseStep 2425709 = 909641) (by norm_num)
theorem B2728829 : Blo 1617007 2728829 := bbase (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) (by norm_num)
theorem B2425733 : Blo 1617007 2425733 := bbase (se 4 (by rfl) ⟨227412, by rfl⟩ : syracuseStep 2425733 = 454825) (by norm_num)
theorem B1819525 : Blo 1617007 1819525 := bbase (se 4 (by rfl) ⟨170580, by rfl⟩ : syracuseStep 1819525 = 341161) (by norm_num)
theorem B2048905 : Blo 1617007 2048905 := bbase (se 2 (by rfl) ⟨768339, by rfl⟩ : syracuseStep 2048905 = 1536679) (by norm_num)
theorem B3072917 : Blo 1617007 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B1639321 : Blo 1617007 1639321 := bbase (se 2 (by rfl) ⟨614745, by rfl⟩ : syracuseStep 1639321 = 1229491) (by norm_num)
theorem B2425757 : Blo 1617007 2425757 := bbase (se 3 (by rfl) ⟨454829, by rfl⟩ : syracuseStep 2425757 = 909659) (by norm_num)
theorem B2302877 : Blo 1617007 2302877 := bbase (se 3 (by rfl) ⟨431789, by rfl⟩ : syracuseStep 2302877 = 863579) (by norm_num)
theorem B1819561 : Blo 1617007 1819561 := bbase (se 2 (by rfl) ⟨682335, by rfl⟩ : syracuseStep 1819561 = 1364671) (by norm_num)
theorem B2425781 : Blo 1617007 2425781 := bbase (se 5 (by rfl) ⟨113708, by rfl⟩ : syracuseStep 2425781 = 227417) (by norm_num)
theorem B2425805 : Blo 1617007 2425805 := bbase (se 3 (by rfl) ⟨454838, by rfl⟩ : syracuseStep 2425805 = 909677) (by norm_num)
theorem B1819597 : Blo 1617007 1819597 := bbase (se 3 (by rfl) ⟨341174, by rfl⟩ : syracuseStep 1819597 = 682349) (by norm_num)
theorem B2917333 : Blo 1617007 2917333 := bbase (se 7 (by rfl) ⟨34187, by rfl⟩ : syracuseStep 2917333 = 68375) (by norm_num)
theorem B2425829 : Blo 1617007 2425829 := bbase (se 4 (by rfl) ⟨227421, by rfl⟩ : syracuseStep 2425829 = 454843) (by norm_num)
theorem B1819633 : Blo 1617007 1819633 := bbase (se 2 (by rfl) ⟨682362, by rfl⟩ : syracuseStep 1819633 = 1364725) (by norm_num)
theorem B2728957 : Blo 1617007 2728957 := bbase (se 3 (by rfl) ⟨511679, by rfl⟩ : syracuseStep 2728957 = 1023359) (by norm_num)
theorem B2425853 : Blo 1617007 2425853 := bbase (se 3 (by rfl) ⟨454847, by rfl⟩ : syracuseStep 2425853 = 909695) (by norm_num)
theorem B3638285 : Blo 1617007 3638285 := bbase (se 3 (by rfl) ⟨682178, by rfl⟩ : syracuseStep 3638285 = 1364357) (by norm_num)
theorem B2425877 : Blo 1617007 2425877 := bbase (se 6 (by rfl) ⟨56856, by rfl⟩ : syracuseStep 2425877 = 113713) (by norm_num)
theorem B1819669 : Blo 1617007 1819669 := bbase (se 6 (by rfl) ⟨42648, by rfl⟩ : syracuseStep 1819669 = 85297) (by norm_num)
theorem B2425901 : Blo 1617007 2425901 := bbase (se 3 (by rfl) ⟨454856, by rfl⟩ : syracuseStep 2425901 = 909713) (by norm_num)
theorem B3073069 : Blo 1617007 3073069 := bbase (se 3 (by rfl) ⟨576200, by rfl⟩ : syracuseStep 3073069 = 1152401) (by norm_num)
theorem B1819705 : Blo 1617007 1819705 := bbase (se 2 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 1819705 = 1364779) (by norm_num)
theorem B2425925 : Blo 1617007 2425925 := bbase (se 4 (by rfl) ⟨227430, by rfl⟩ : syracuseStep 2425925 = 454861) (by norm_num)
theorem B1942601 : Blo 1617007 1942601 := bbase (se 2 (by rfl) ⟨728475, by rfl⟩ : syracuseStep 1942601 = 1456951) (by norm_num)
theorem B4097101 : Blo 1617007 4097101 := bbase (se 3 (by rfl) ⟨768206, by rfl⟩ : syracuseStep 4097101 = 1536413) (by norm_num)
theorem B3638357 : Blo 1617007 3638357 := bbase (se 8 (by rfl) ⟨21318, by rfl⟩ : syracuseStep 3638357 = 42637) (by norm_num)
theorem B2729045 : Blo 1617007 2729045 := bbase (se 8 (by rfl) ⟨15990, by rfl⟩ : syracuseStep 2729045 = 31981) (by norm_num)
theorem B2425949 : Blo 1617007 2425949 := bbase (se 3 (by rfl) ⟨454865, by rfl⟩ : syracuseStep 2425949 = 909731) (by norm_num)
theorem B1819741 : Blo 1617007 1819741 := bbase (se 3 (by rfl) ⟨341201, by rfl⟩ : syracuseStep 1819741 = 682403) (by norm_num)
theorem B2425973 : Blo 1617007 2425973 := bbase (se 5 (by rfl) ⟨113717, by rfl⟩ : syracuseStep 2425973 = 227435) (by norm_num)
theorem B1819777 : Blo 1617007 1819777 := bbase (se 2 (by rfl) ⟨682416, by rfl⟩ : syracuseStep 1819777 = 1364833) (by norm_num)
theorem B2425997 : Blo 1617007 2425997 := bbase (se 3 (by rfl) ⟨454874, by rfl⟩ : syracuseStep 2425997 = 909749) (by norm_num)
theorem B3638429 : Blo 1617007 3638429 := bbase (se 3 (by rfl) ⟨682205, by rfl⟩ : syracuseStep 3638429 = 1364411) (by norm_num)
theorem B2426021 : Blo 1617007 2426021 := bbase (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) (by norm_num)
theorem B1819813 : Blo 1617007 1819813 := bbase (se 4 (by rfl) ⟨170607, by rfl⟩ : syracuseStep 1819813 = 341215) (by norm_num)
theorem B1942697 : Blo 1617007 1942697 := bbase (se 2 (by rfl) ⟨728511, by rfl⟩ : syracuseStep 1942697 = 1457023) (by norm_num)
theorem B1942717 : Blo 1617007 1942717 := bbase (se 3 (by rfl) ⟨364259, by rfl⟩ : syracuseStep 1942717 = 728519) (by norm_num)
theorem B2426045 : Blo 1617007 2426045 := bbase (se 3 (by rfl) ⟨454883, by rfl⟩ : syracuseStep 2426045 = 909767) (by norm_num)
theorem B4097213 : Blo 1617007 4097213 := bbase (se 3 (by rfl) ⟨768227, by rfl⟩ : syracuseStep 4097213 = 1536455) (by norm_num)
theorem B1819849 : Blo 1617007 1819849 := bbase (se 2 (by rfl) ⟨682443, by rfl⟩ : syracuseStep 1819849 = 1364887) (by norm_num)
theorem B2729173 : Blo 1617007 2729173 := bbase (se 7 (by rfl) ⟨31982, by rfl⟩ : syracuseStep 2729173 = 63965) (by norm_num)
theorem B2426069 : Blo 1617007 2426069 := bbase (se 7 (by rfl) ⟨28430, by rfl⟩ : syracuseStep 2426069 = 56861) (by norm_num)
theorem B3638501 : Blo 1617007 3638501 := bbase (se 4 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 3638501 = 682219) (by norm_num)
theorem B2426093 : Blo 1617007 2426093 := bbase (se 3 (by rfl) ⟨454892, by rfl⟩ : syracuseStep 2426093 = 909785) (by norm_num)
theorem B1819885 : Blo 1617007 1819885 := bbase (se 3 (by rfl) ⟨341228, by rfl⟩ : syracuseStep 1819885 = 682457) (by norm_num)
theorem B2426117 : Blo 1617007 2426117 := bbase (se 4 (by rfl) ⟨227448, by rfl⟩ : syracuseStep 2426117 = 454897) (by norm_num)
theorem B1819921 : Blo 1617007 1819921 := bbase (se 2 (by rfl) ⟨682470, by rfl⟩ : syracuseStep 1819921 = 1364941) (by norm_num)
theorem B2426141 : Blo 1617007 2426141 := bbase (se 3 (by rfl) ⟨454901, by rfl⟩ : syracuseStep 2426141 = 909803) (by norm_num)
theorem B3638573 : Blo 1617007 3638573 := bbase (se 3 (by rfl) ⟨682232, by rfl⟩ : syracuseStep 3638573 = 1364465) (by norm_num)
theorem B2729261 : Blo 1617007 2729261 := bbase (se 3 (by rfl) ⟨511736, by rfl⟩ : syracuseStep 2729261 = 1023473) (by norm_num)
theorem B2426165 : Blo 1617007 2426165 := bbase (se 5 (by rfl) ⟨113726, by rfl⟩ : syracuseStep 2426165 = 227453) (by norm_num)
theorem B1819957 : Blo 1617007 1819957 := bbase (se 5 (by rfl) ⟨85310, by rfl⟩ : syracuseStep 1819957 = 170621) (by norm_num)
theorem B1942861 : Blo 1617007 1942861 := bbase (se 3 (by rfl) ⟨364286, by rfl⟩ : syracuseStep 1942861 = 728573) (by norm_num)
theorem B2426189 : Blo 1617007 2426189 := bbase (se 3 (by rfl) ⟨454910, by rfl⟩ : syracuseStep 2426189 = 909821) (by norm_num)
theorem B1819993 : Blo 1617007 1819993 := bbase (se 2 (by rfl) ⟨682497, by rfl⟩ : syracuseStep 1819993 = 1364995) (by norm_num)
theorem B3073373 : Blo 1617007 3073373 := bbase (se 3 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 3073373 = 1152515) (by norm_num)
theorem B2426213 : Blo 1617007 2426213 := bbase (se 4 (by rfl) ⟨227457, by rfl⟩ : syracuseStep 2426213 = 454915) (by norm_num)
theorem B5907829 : Blo 1617007 5907829 := bbase (se 5 (by rfl) ⟨276929, by rfl⟩ : syracuseStep 5907829 = 553859) (by norm_num)
theorem B3638645 : Blo 1617007 3638645 := bbase (se 5 (by rfl) ⟨170561, by rfl⟩ : syracuseStep 3638645 = 341123) (by norm_num)
theorem B9340277 : Blo 1617007 9340277 := bbase (se 5 (by rfl) ⟨437825, by rfl⟩ : syracuseStep 9340277 = 875651) (by norm_num)
theorem B2426237 : Blo 1617007 2426237 := bbase (se 3 (by rfl) ⟨454919, by rfl⟩ : syracuseStep 2426237 = 909839) (by norm_num)
theorem B1820029 : Blo 1617007 1820029 := bbase (se 3 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 1820029 = 682511) (by norm_num)
theorem B4097405 : Blo 1617007 4097405 := bbase (se 3 (by rfl) ⟨768263, by rfl⟩ : syracuseStep 4097405 = 1536527) (by norm_num)
theorem B2426261 : Blo 1617007 2426261 := bbase (se 6 (by rfl) ⟨56865, by rfl⟩ : syracuseStep 2426261 = 113731) (by norm_num)
theorem B1820065 : Blo 1617007 1820065 := bbase (se 2 (by rfl) ⟨682524, by rfl⟩ : syracuseStep 1820065 = 1365049) (by norm_num)
theorem B2729389 : Blo 1617007 2729389 := bbase (se 3 (by rfl) ⟨511760, by rfl⟩ : syracuseStep 2729389 = 1023521) (by norm_num)
theorem B2426285 : Blo 1617007 2426285 := bbase (se 3 (by rfl) ⟨454928, by rfl⟩ : syracuseStep 2426285 = 909857) (by norm_num)
theorem B3638717 : Blo 1617007 3638717 := bbase (se 3 (by rfl) ⟨682259, by rfl⟩ : syracuseStep 3638717 = 1364519) (by norm_num)
theorem B2426309 : Blo 1617007 2426309 := bbase (se 4 (by rfl) ⟨227466, by rfl⟩ : syracuseStep 2426309 = 454933) (by norm_num)
theorem B1820101 : Blo 1617007 1820101 := bbase (se 4 (by rfl) ⟨170634, by rfl⟩ : syracuseStep 1820101 = 341269) (by norm_num)
theorem B18433493 : Blo 1617007 18433493 := bbase (se 7 (by rfl) ⟨216017, by rfl⟩ : syracuseStep 18433493 = 432035) (by norm_num)
theorem B2426333 : Blo 1617007 2426333 := bbase (se 3 (by rfl) ⟨454937, by rfl⟩ : syracuseStep 2426333 = 909875) (by norm_num)
theorem B1820137 : Blo 1617007 1820137 := bbase (se 2 (by rfl) ⟨682551, by rfl⟩ : syracuseStep 1820137 = 1365103) (by norm_num)
theorem B2426357 : Blo 1617007 2426357 := bbase (se 5 (by rfl) ⟨113735, by rfl⟩ : syracuseStep 2426357 = 227471) (by norm_num)
theorem B3638789 : Blo 1617007 3638789 := bbase (se 4 (by rfl) ⟨341136, by rfl⟩ : syracuseStep 3638789 = 682273) (by norm_num)
theorem B2729477 : Blo 1617007 2729477 := bbase (se 4 (by rfl) ⟨255888, by rfl⟩ : syracuseStep 2729477 = 511777) (by norm_num)
theorem B2426381 : Blo 1617007 2426381 := bbase (se 3 (by rfl) ⟨454946, by rfl⟩ : syracuseStep 2426381 = 909893) (by norm_num)
theorem B1820173 : Blo 1617007 1820173 := bbase (se 3 (by rfl) ⟨341282, by rfl⟩ : syracuseStep 1820173 = 682565) (by norm_num)
theorem B2426405 : Blo 1617007 2426405 := bbase (se 4 (by rfl) ⟨227475, by rfl⟩ : syracuseStep 2426405 = 454951) (by norm_num)
theorem B1820209 : Blo 1617007 1820209 := bbase (se 2 (by rfl) ⟨682578, by rfl⟩ : syracuseStep 1820209 = 1365157) (by norm_num)
theorem B2459189 : Blo 1617007 2459189 := bbase (se 5 (by rfl) ⟨115274, by rfl⟩ : syracuseStep 2459189 = 230549) (by norm_num)
theorem B2426429 : Blo 1617007 2426429 := bbase (se 3 (by rfl) ⟨454955, by rfl⟩ : syracuseStep 2426429 = 909911) (by norm_num)
theorem B3638861 : Blo 1617007 3638861 := bbase (se 3 (by rfl) ⟨682286, by rfl⟩ : syracuseStep 3638861 = 1364573) (by norm_num)
theorem B2426453 : Blo 1617007 2426453 := bbase (se 8 (by rfl) ⟨14217, by rfl⟩ : syracuseStep 2426453 = 28435) (by norm_num)
theorem B1820245 : Blo 1617007 1820245 := bbase (se 8 (by rfl) ⟨10665, by rfl⟩ : syracuseStep 1820245 = 21331) (by norm_num)
theorem B5457509 : Blo 1617007 5457509 := bbase (se 4 (by rfl) ⟨511641, by rfl⟩ : syracuseStep 5457509 = 1023283) (by norm_num)
theorem B3688037 : Blo 1617007 3688037 := bbase (se 4 (by rfl) ⟨345753, by rfl⟩ : syracuseStep 3688037 = 691507) (by norm_num)
theorem B2426477 : Blo 1617007 2426477 := bbase (se 3 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 2426477 = 909929) (by norm_num)
theorem B1820281 : Blo 1617007 1820281 := bbase (se 2 (by rfl) ⟨682605, by rfl⟩ : syracuseStep 1820281 = 1365211) (by norm_num)
theorem B2729605 : Blo 1617007 2729605 := bbase (se 4 (by rfl) ⟨255900, by rfl⟩ : syracuseStep 2729605 = 511801) (by norm_num)
theorem B2426501 : Blo 1617007 2426501 := bbase (se 4 (by rfl) ⟨227484, by rfl⟩ : syracuseStep 2426501 = 454969) (by norm_num)
theorem B3638933 : Blo 1617007 3638933 := bbase (se 6 (by rfl) ⟨85287, by rfl⟩ : syracuseStep 3638933 = 170575) (by norm_num)
theorem B2426525 : Blo 1617007 2426525 := bbase (se 3 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 2426525 = 909947) (by norm_num)
theorem B1820317 : Blo 1617007 1820317 := bbase (se 3 (by rfl) ⟨341309, by rfl⟩ : syracuseStep 1820317 = 682619) (by norm_num)
theorem B2426549 : Blo 1617007 2426549 := bbase (se 5 (by rfl) ⟨113744, by rfl⟩ : syracuseStep 2426549 = 227489) (by norm_num)
theorem B1820353 : Blo 1617007 1820353 := bbase (se 2 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 1820353 = 1365265) (by norm_num)
theorem B2426573 : Blo 1617007 2426573 := bbase (se 3 (by rfl) ⟨454982, by rfl⟩ : syracuseStep 2426573 = 909965) (by norm_num)
theorem B4097749 : Blo 1617007 4097749 := bbase (se 7 (by rfl) ⟨48020, by rfl⟩ : syracuseStep 4097749 = 96041) (by norm_num)
theorem B3639005 : Blo 1617007 3639005 := bbase (se 3 (by rfl) ⟨682313, by rfl⟩ : syracuseStep 3639005 = 1364627) (by norm_num)
theorem B2729693 : Blo 1617007 2729693 := bbase (se 3 (by rfl) ⟨511817, by rfl⟩ : syracuseStep 2729693 = 1023635) (by norm_num)
theorem B2426597 : Blo 1617007 2426597 := bbase (se 4 (by rfl) ⟨227493, by rfl⟩ : syracuseStep 2426597 = 454987) (by norm_num)
theorem B1820389 : Blo 1617007 1820389 := bbase (se 4 (by rfl) ⟨170661, by rfl⟩ : syracuseStep 1820389 = 341323) (by norm_num)
theorem B2426621 : Blo 1617007 2426621 := bbase (se 3 (by rfl) ⟨454991, by rfl⟩ : syracuseStep 2426621 = 909983) (by norm_num)
theorem B8193797 : Blo 1617007 8193797 := bbase (se 4 (by rfl) ⟨768168, by rfl⟩ : syracuseStep 8193797 = 1536337) (by norm_num)
theorem B1820425 : Blo 1617007 1820425 := bbase (se 2 (by rfl) ⟨682659, by rfl⟩ : syracuseStep 1820425 = 1365319) (by norm_num)
theorem B2426645 : Blo 1617007 2426645 := bbase (se 6 (by rfl) ⟨56874, by rfl⟩ : syracuseStep 2426645 = 113749) (by norm_num)
theorem B3639077 : Blo 1617007 3639077 := bbase (se 4 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 3639077 = 682327) (by norm_num)
theorem B2426669 : Blo 1617007 2426669 := bbase (se 3 (by rfl) ⟨455000, by rfl⟩ : syracuseStep 2426669 = 910001) (by norm_num)
theorem B1820461 : Blo 1617007 1820461 := bbase (se 3 (by rfl) ⟨341336, by rfl⟩ : syracuseStep 1820461 = 682673) (by norm_num)
theorem B11667253 : Blo 1617007 11667253 := bbase (se 5 (by rfl) ⟨546902, by rfl⟩ : syracuseStep 11667253 = 1093805) (by norm_num)
theorem B5834549 : Blo 1617007 5834549 := bbase (se 5 (by rfl) ⟨273494, by rfl⟩ : syracuseStep 5834549 = 546989) (by norm_num)
theorem B2426693 : Blo 1617007 2426693 := bbase (se 4 (by rfl) ⟨227502, by rfl⟩ : syracuseStep 2426693 = 455005) (by norm_num)
theorem B4097861 : Blo 1617007 4097861 := bbase (se 4 (by rfl) ⟨384174, by rfl⟩ : syracuseStep 4097861 = 768349) (by norm_num)
theorem B1820497 : Blo 1617007 1820497 := bbase (se 2 (by rfl) ⟨682686, by rfl⟩ : syracuseStep 1820497 = 1365373) (by norm_num)
theorem B2729821 : Blo 1617007 2729821 := bbase (se 3 (by rfl) ⟨511841, by rfl⟩ : syracuseStep 2729821 = 1023683) (by norm_num)
theorem B2426717 : Blo 1617007 2426717 := bbase (se 3 (by rfl) ⟨455009, by rfl⟩ : syracuseStep 2426717 = 910019) (by norm_num)
theorem B3639149 : Blo 1617007 3639149 := bbase (se 3 (by rfl) ⟨682340, by rfl⟩ : syracuseStep 3639149 = 1364681) (by norm_num)
theorem B2426741 : Blo 1617007 2426741 := bbase (se 5 (by rfl) ⟨113753, by rfl⟩ : syracuseStep 2426741 = 227507) (by norm_num)
theorem B1820533 : Blo 1617007 1820533 := bbase (se 5 (by rfl) ⟨85337, by rfl⟩ : syracuseStep 1820533 = 170675) (by norm_num)
theorem B2074505 : Blo 1617007 2074505 := bbase (se 2 (by rfl) ⟨777939, by rfl⟩ : syracuseStep 2074505 = 1555879) (by norm_num)
theorem B2426765 : Blo 1617007 2426765 := bbase (se 3 (by rfl) ⟨455018, by rfl⟩ : syracuseStep 2426765 = 910037) (by norm_num)
theorem B1820569 : Blo 1617007 1820569 := bbase (se 2 (by rfl) ⟨682713, by rfl⟩ : syracuseStep 1820569 = 1365427) (by norm_num)
theorem B2426789 : Blo 1617007 2426789 := bbase (se 4 (by rfl) ⟨227511, by rfl⟩ : syracuseStep 2426789 = 455023) (by norm_num)
theorem B3639221 : Blo 1617007 3639221 := bbase (se 5 (by rfl) ⟨170588, by rfl⟩ : syracuseStep 3639221 = 341177) (by norm_num)
theorem B2729909 : Blo 1617007 2729909 := bbase (se 5 (by rfl) ⟨127964, by rfl⟩ : syracuseStep 2729909 = 255929) (by norm_num)
theorem B2426813 : Blo 1617007 2426813 := bbase (se 3 (by rfl) ⟨455027, by rfl⟩ : syracuseStep 2426813 = 910055) (by norm_num)
theorem B1820605 : Blo 1617007 1820605 := bbase (se 3 (by rfl) ⟨341363, by rfl⟩ : syracuseStep 1820605 = 682727) (by norm_num)
theorem B2426837 : Blo 1617007 2426837 := bbase (se 7 (by rfl) ⟨28439, by rfl⟩ : syracuseStep 2426837 = 56879) (by norm_num)
theorem B1820641 : Blo 1617007 1820641 := bbase (se 2 (by rfl) ⟨682740, by rfl⟩ : syracuseStep 1820641 = 1365481) (by norm_num)
theorem B2426861 : Blo 1617007 2426861 := bbase (se 3 (by rfl) ⟨455036, by rfl⟩ : syracuseStep 2426861 = 910073) (by norm_num)
theorem B3639293 : Blo 1617007 3639293 := bbase (se 3 (by rfl) ⟨682367, by rfl⟩ : syracuseStep 3639293 = 1364735) (by norm_num)
theorem B2426885 : Blo 1617007 2426885 := bbase (se 4 (by rfl) ⟨227520, by rfl⟩ : syracuseStep 2426885 = 455041) (by norm_num)
theorem B1820677 : Blo 1617007 1820677 := bbase (se 4 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 1820677 = 341377) (by norm_num)
theorem B4098053 : Blo 1617007 4098053 := bbase (se 4 (by rfl) ⟨384192, by rfl⟩ : syracuseStep 4098053 = 768385) (by norm_num)
theorem B5457941 : Blo 1617007 5457941 := bbase (se 6 (by rfl) ⟨127920, by rfl⟩ : syracuseStep 5457941 = 255841) (by norm_num)
theorem B9218069 : Blo 1617007 9218069 := bbase (se 6 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 9218069 = 432097) (by norm_num)
theorem B2426909 : Blo 1617007 2426909 := bbase (se 3 (by rfl) ⟨455045, by rfl⟩ : syracuseStep 2426909 = 910091) (by norm_num)
theorem B1820713 : Blo 1617007 1820713 := bbase (se 2 (by rfl) ⟨682767, by rfl⟩ : syracuseStep 1820713 = 1365535) (by norm_num)
theorem B1640497 : Blo 1617007 1640497 := bbase (se 2 (by rfl) ⟨615186, by rfl⟩ : syracuseStep 1640497 = 1230373) (by norm_num)
theorem B2730037 : Blo 1617007 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B2426933 : Blo 1617007 2426933 := bbase (se 5 (by rfl) ⟨113762, by rfl⟩ : syracuseStep 2426933 = 227525) (by norm_num)
theorem B1640513 : Blo 1617007 1640513 := bbase (se 2 (by rfl) ⟨615192, by rfl⟩ : syracuseStep 1640513 = 1230385) (by norm_num)
theorem B3639365 : Blo 1617007 3639365 := bbase (se 4 (by rfl) ⟨341190, by rfl⟩ : syracuseStep 3639365 = 682381) (by norm_num)
theorem B2426957 : Blo 1617007 2426957 := bbase (se 3 (by rfl) ⟨455054, by rfl⟩ : syracuseStep 2426957 = 910109) (by norm_num)
theorem B1820749 : Blo 1617007 1820749 := bbase (se 3 (by rfl) ⟨341390, by rfl⟩ : syracuseStep 1820749 = 682781) (by norm_num)
theorem B2426981 : Blo 1617007 2426981 := bbase (se 4 (by rfl) ⟨227529, by rfl⟩ : syracuseStep 2426981 = 455059) (by norm_num)
theorem B1820785 : Blo 1617007 1820785 := bbase (se 2 (by rfl) ⟨682794, by rfl⟩ : syracuseStep 1820785 = 1365589) (by norm_num)
theorem B6228085 : Blo 1617007 6228085 := bbase (se 5 (by rfl) ⟨291941, by rfl⟩ : syracuseStep 6228085 = 583883) (by norm_num)
theorem B2427005 : Blo 1617007 2427005 := bbase (se 3 (by rfl) ⟨455063, by rfl⟩ : syracuseStep 2427005 = 910127) (by norm_num)
theorem B4606085 : Blo 1617007 4606085 := bbase (se 4 (by rfl) ⟨431820, by rfl⟩ : syracuseStep 4606085 = 863641) (by norm_num)
theorem B3639437 : Blo 1617007 3639437 := bbase (se 3 (by rfl) ⟨682394, by rfl⟩ : syracuseStep 3639437 = 1364789) (by norm_num)
theorem B2730125 : Blo 1617007 2730125 := bbase (se 3 (by rfl) ⟨511898, by rfl⟩ : syracuseStep 2730125 = 1023797) (by norm_num)
theorem B2427029 : Blo 1617007 2427029 := bbase (se 6 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 2427029 = 113767) (by norm_num)
theorem B1820821 : Blo 1617007 1820821 := bbase (se 6 (by rfl) ⟨42675, by rfl⟩ : syracuseStep 1820821 = 85351) (by norm_num)
theorem B2427053 : Blo 1617007 2427053 := bbase (se 3 (by rfl) ⟨455072, by rfl⟩ : syracuseStep 2427053 = 910145) (by norm_num)
theorem B1820857 : Blo 1617007 1820857 := bbase (se 2 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 1820857 = 1365643) (by norm_num)
theorem B2427077 : Blo 1617007 2427077 := bbase (se 4 (by rfl) ⟨227538, by rfl⟩ : syracuseStep 2427077 = 455077) (by norm_num)
theorem B3639509 : Blo 1617007 3639509 := bbase (se 7 (by rfl) ⟨42650, by rfl⟩ : syracuseStep 3639509 = 85301) (by norm_num)
theorem B44902613 : Blo 1617007 44902613 := bbase (se 7 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 44902613 = 1052405) (by norm_num)
theorem B2427101 : Blo 1617007 2427101 := bbase (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) (by norm_num)
theorem B1820893 : Blo 1617007 1820893 := bbase (se 3 (by rfl) ⟨341417, by rfl⟩ : syracuseStep 1820893 = 682835) (by norm_num)
theorem B2427125 : Blo 1617007 2427125 := bbase (se 5 (by rfl) ⟨113771, by rfl⟩ : syracuseStep 2427125 = 227543) (by norm_num)
theorem B8751349 : Blo 1617007 8751349 := bbase (se 5 (by rfl) ⟨410219, by rfl⟩ : syracuseStep 8751349 = 820439) (by norm_num)
theorem B1820929 : Blo 1617007 1820929 := bbase (se 2 (by rfl) ⟨682848, by rfl⟩ : syracuseStep 1820929 = 1365697) (by norm_num)
theorem B2730253 : Blo 1617007 2730253 := bbase (se 3 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 2730253 = 1023845) (by norm_num)
theorem B2427149 : Blo 1617007 2427149 := bbase (se 3 (by rfl) ⟨455090, by rfl⟩ : syracuseStep 2427149 = 910181) (by norm_num)
theorem B2074901 : Blo 1617007 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B3639581 : Blo 1617007 3639581 := bbase (se 3 (by rfl) ⟨682421, by rfl⟩ : syracuseStep 3639581 = 1364843) (by norm_num)
theorem B2427173 : Blo 1617007 2427173 := bbase (se 4 (by rfl) ⟨227547, by rfl⟩ : syracuseStep 2427173 = 455095) (by norm_num)
theorem B1820965 : Blo 1617007 1820965 := bbase (se 4 (by rfl) ⟨170715, by rfl⟩ : syracuseStep 1820965 = 341431) (by norm_num)
theorem B2304301 : Blo 1617007 2304301 := bbase (se 3 (by rfl) ⟨432056, by rfl⟩ : syracuseStep 2304301 = 864113) (by norm_num)
theorem B2427197 : Blo 1617007 2427197 := bbase (se 3 (by rfl) ⟨455099, by rfl⟩ : syracuseStep 2427197 = 910199) (by norm_num)
theorem B2591045 : Blo 1617007 2591045 := bbase (se 4 (by rfl) ⟨242910, by rfl⟩ : syracuseStep 2591045 = 485821) (by norm_num)
theorem B1821001 : Blo 1617007 1821001 := bbase (se 2 (by rfl) ⟨682875, by rfl⟩ : syracuseStep 1821001 = 1365751) (by norm_num)
theorem B2427221 : Blo 1617007 2427221 := bbase (se 10 (by rfl) ⟨3555, by rfl⟩ : syracuseStep 2427221 = 7111) (by norm_num)
theorem B3639653 : Blo 1617007 3639653 := bbase (se 4 (by rfl) ⟨341217, by rfl⟩ : syracuseStep 3639653 = 682435) (by norm_num)
theorem B2730341 : Blo 1617007 2730341 := bbase (se 4 (by rfl) ⟨255969, by rfl⟩ : syracuseStep 2730341 = 511939) (by norm_num)
theorem B2427245 : Blo 1617007 2427245 := bbase (se 3 (by rfl) ⟨455108, by rfl⟩ : syracuseStep 2427245 = 910217) (by norm_num)
theorem B1821037 : Blo 1617007 1821037 := bbase (se 3 (by rfl) ⟨341444, by rfl⟩ : syracuseStep 1821037 = 682889) (by norm_num)
theorem B2427269 : Blo 1617007 2427269 := bbase (se 4 (by rfl) ⟨227556, by rfl⟩ : syracuseStep 2427269 = 455113) (by norm_num)
theorem B1821073 : Blo 1617007 1821073 := bbase (se 2 (by rfl) ⟨682902, by rfl⟩ : syracuseStep 1821073 = 1365805) (by norm_num)
theorem B12290453 : Blo 1617007 12290453 := bbase (se 6 (by rfl) ⟨288057, by rfl⟩ : syracuseStep 12290453 = 576115) (by norm_num)
theorem B2427293 : Blo 1617007 2427293 := bbase (se 3 (by rfl) ⟨455117, by rfl⟩ : syracuseStep 2427293 = 910235) (by norm_num)
theorem B3639725 : Blo 1617007 3639725 := bbase (se 3 (by rfl) ⟨682448, by rfl⟩ : syracuseStep 3639725 = 1364897) (by norm_num)
theorem B2427317 : Blo 1617007 2427317 := bbase (se 5 (by rfl) ⟨113780, by rfl⟩ : syracuseStep 2427317 = 227561) (by norm_num)
theorem B1821109 : Blo 1617007 1821109 := bbase (se 5 (by rfl) ⟨85364, by rfl⟩ : syracuseStep 1821109 = 170729) (by norm_num)
theorem B5458373 : Blo 1617007 5458373 := bbase (se 4 (by rfl) ⟨511722, by rfl⟩ : syracuseStep 5458373 = 1023445) (by norm_num)
theorem B2427341 : Blo 1617007 2427341 := bbase (se 3 (by rfl) ⟨455126, by rfl⟩ : syracuseStep 2427341 = 910253) (by norm_num)
theorem B1821145 : Blo 1617007 1821145 := bbase (se 2 (by rfl) ⟨682929, by rfl⟩ : syracuseStep 1821145 = 1365859) (by norm_num)
theorem B2730469 : Blo 1617007 2730469 := bbase (se 4 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 2730469 = 511963) (by norm_num)
theorem B2427365 : Blo 1617007 2427365 := bbase (se 4 (by rfl) ⟨227565, by rfl⟩ : syracuseStep 2427365 = 455131) (by norm_num)
theorem B3639797 : Blo 1617007 3639797 := bbase (se 5 (by rfl) ⟨170615, by rfl⟩ : syracuseStep 3639797 = 341231) (by norm_num)
theorem B6146549 : Blo 1617007 6146549 := bbase (se 5 (by rfl) ⟨288119, by rfl⟩ : syracuseStep 6146549 = 576239) (by norm_num)
theorem B2427389 : Blo 1617007 2427389 := bbase (se 3 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 2427389 = 910271) (by norm_num)
theorem B1821181 : Blo 1617007 1821181 := bbase (se 3 (by rfl) ⟨341471, by rfl⟩ : syracuseStep 1821181 = 682943) (by norm_num)
theorem B2591237 : Blo 1617007 2591237 := bbase (se 4 (by rfl) ⟨242928, by rfl⟩ : syracuseStep 2591237 = 485857) (by norm_num)
theorem B2427413 : Blo 1617007 2427413 := bbase (se 6 (by rfl) ⟨56892, by rfl⟩ : syracuseStep 2427413 = 113785) (by norm_num)
theorem B1821217 : Blo 1617007 1821217 := bbase (se 2 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 1821217 = 1365913) (by norm_num)
theorem B2427437 : Blo 1617007 2427437 := bbase (se 3 (by rfl) ⟨455144, by rfl⟩ : syracuseStep 2427437 = 910289) (by norm_num)
theorem B3639869 : Blo 1617007 3639869 := bbase (se 3 (by rfl) ⟨682475, by rfl⟩ : syracuseStep 3639869 = 1364951) (by norm_num)
theorem B2730557 : Blo 1617007 2730557 := bbase (se 3 (by rfl) ⟨511979, by rfl⟩ : syracuseStep 2730557 = 1023959) (by norm_num)
theorem B2427461 : Blo 1617007 2427461 := bbase (se 4 (by rfl) ⟨227574, by rfl⟩ : syracuseStep 2427461 = 455149) (by norm_num)
theorem B1821253 : Blo 1617007 1821253 := bbase (se 4 (by rfl) ⟨170742, by rfl⟩ : syracuseStep 1821253 = 341485) (by norm_num)
theorem B2427485 : Blo 1617007 2427485 := bbase (se 3 (by rfl) ⟨455153, by rfl⟩ : syracuseStep 2427485 = 910307) (by norm_num)
theorem B1641061 : Blo 1617007 1641061 := bbase (se 4 (by rfl) ⟨153849, by rfl⟩ : syracuseStep 1641061 = 307699) (by norm_num)
theorem B1821289 : Blo 1617007 1821289 := bbase (se 2 (by rfl) ⟨682983, by rfl⟩ : syracuseStep 1821289 = 1365967) (by norm_num)
theorem B1845869 : Blo 1617007 1845869 := bbase (se 3 (by rfl) ⟨346100, by rfl⟩ : syracuseStep 1845869 = 692201) (by norm_num)
theorem B3689077 : Blo 1617007 3689077 := bbase (se 5 (by rfl) ⟨172925, by rfl⟩ : syracuseStep 3689077 = 345851) (by norm_num)
theorem B2427509 : Blo 1617007 2427509 := bbase (se 5 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 2427509 = 227579) (by norm_num)
theorem B2075269 : Blo 1617007 2075269 := bbase (se 4 (by rfl) ⟨194556, by rfl⟩ : syracuseStep 2075269 = 389113) (by norm_num)
theorem B3639941 : Blo 1617007 3639941 := bbase (se 4 (by rfl) ⟨341244, by rfl⟩ : syracuseStep 3639941 = 682489) (by norm_num)
theorem B2591365 : Blo 1617007 2591365 := bbase (se 4 (by rfl) ⟨242940, by rfl⟩ : syracuseStep 2591365 = 485881) (by norm_num)
theorem B2427533 : Blo 1617007 2427533 := bbase (se 3 (by rfl) ⟨455162, by rfl⟩ : syracuseStep 2427533 = 910325) (by norm_num)
theorem B1821325 : Blo 1617007 1821325 := bbase (se 3 (by rfl) ⟨341498, by rfl⟩ : syracuseStep 1821325 = 682997) (by norm_num)
theorem B2427557 : Blo 1617007 2427557 := bbase (se 4 (by rfl) ⟨227583, by rfl⟩ : syracuseStep 2427557 = 455167) (by norm_num)
theorem B1821361 : Blo 1617007 1821361 := bbase (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) (by norm_num)
theorem B6908597 : Blo 1617007 6908597 := bbase (se 5 (by rfl) ⟨323840, by rfl⟩ : syracuseStep 6908597 = 647681) (by norm_num)
theorem B2730685 : Blo 1617007 2730685 := bbase (se 3 (by rfl) ⟨512003, by rfl⟩ : syracuseStep 2730685 = 1024007) (by norm_num)
theorem B2427581 : Blo 1617007 2427581 := bbase (se 3 (by rfl) ⟨455171, by rfl⟩ : syracuseStep 2427581 = 910343) (by norm_num)
theorem B3640013 : Blo 1617007 3640013 := bbase (se 3 (by rfl) ⟨682502, by rfl⟩ : syracuseStep 3640013 = 1365005) (by norm_num)
theorem B15551189 : Blo 1617007 15551189 := bbase (se 7 (by rfl) ⟨182240, by rfl⟩ : syracuseStep 15551189 = 364481) (by norm_num)
theorem B2427605 : Blo 1617007 2427605 := bbase (se 7 (by rfl) ⟨28448, by rfl⟩ : syracuseStep 2427605 = 56897) (by norm_num)
theorem B2427629 : Blo 1617007 2427629 := bbase (se 3 (by rfl) ⟨455180, by rfl⟩ : syracuseStep 2427629 = 910361) (by norm_num)
theorem B2427653 : Blo 1617007 2427653 := bbase (se 4 (by rfl) ⟨227592, by rfl⟩ : syracuseStep 2427653 = 455185) (by norm_num)
theorem B3640085 : Blo 1617007 3640085 := bbase (se 6 (by rfl) ⟨85314, by rfl⟩ : syracuseStep 3640085 = 170629) (by norm_num)
theorem B2730773 : Blo 1617007 2730773 := bbase (se 6 (by rfl) ⟨64002, by rfl⟩ : syracuseStep 2730773 = 128005) (by norm_num)
theorem B6146837 : Blo 1617007 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B2427677 : Blo 1617007 2427677 := bbase (se 3 (by rfl) ⟨455189, by rfl⟩ : syracuseStep 2427677 = 910379) (by norm_num)
theorem B4606757 : Blo 1617007 4606757 := bbase (se 4 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 4606757 = 863767) (by norm_num)
theorem B12282677 : Blo 1617007 12282677 := bbase (se 5 (by rfl) ⟨575750, by rfl⟩ : syracuseStep 12282677 = 1151501) (by norm_num)
theorem B2427701 : Blo 1617007 2427701 := bbase (se 5 (by rfl) ⟨113798, by rfl⟩ : syracuseStep 2427701 = 227597) (by norm_num)
theorem B7777093 : Blo 1617007 7777093 := bbase (se 4 (by rfl) ⟨729102, by rfl⟩ : syracuseStep 7777093 = 1458205) (by norm_num)
theorem B2427725 : Blo 1617007 2427725 := bbase (se 3 (by rfl) ⟨455198, by rfl⟩ : syracuseStep 2427725 = 910397) (by norm_num)
theorem B3640157 : Blo 1617007 3640157 := bbase (se 3 (by rfl) ⟨682529, by rfl⟩ : syracuseStep 3640157 = 1365059) (by norm_num)
theorem B2427749 : Blo 1617007 2427749 := bbase (se 4 (by rfl) ⟨227601, by rfl⟩ : syracuseStep 2427749 = 455203) (by norm_num)
theorem B5458805 : Blo 1617007 5458805 := bbase (se 5 (by rfl) ⟨255881, by rfl⟩ : syracuseStep 5458805 = 511763) (by norm_num)
theorem B5909365 : Blo 1617007 5909365 := bbase (se 5 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 5909365 = 554003) (by norm_num)
theorem B2427773 : Blo 1617007 2427773 := bbase (se 3 (by rfl) ⟨455207, by rfl⟩ : syracuseStep 2427773 = 910415) (by norm_num)
theorem B2304893 : Blo 1617007 2304893 := bbase (se 3 (by rfl) ⟨432167, by rfl⟩ : syracuseStep 2304893 = 864335) (by norm_num)
theorem B2730901 : Blo 1617007 2730901 := bbase (se 6 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 2730901 = 128011) (by norm_num)
theorem B2427797 : Blo 1617007 2427797 := bbase (se 6 (by rfl) ⟨56901, by rfl⟩ : syracuseStep 2427797 = 113803) (by norm_num)
theorem B3640229 : Blo 1617007 3640229 := bbase (se 4 (by rfl) ⟨341271, by rfl⟩ : syracuseStep 3640229 = 682543) (by norm_num)
theorem B2427821 : Blo 1617007 2427821 := bbase (se 3 (by rfl) ⟨455216, by rfl⟩ : syracuseStep 2427821 = 910433) (by norm_num)
theorem B2427845 : Blo 1617007 2427845 := bbase (se 4 (by rfl) ⟨227610, by rfl⟩ : syracuseStep 2427845 = 455221) (by norm_num)
theorem B2304973 : Blo 1617007 2304973 := bbase (se 3 (by rfl) ⟨432182, by rfl⟩ : syracuseStep 2304973 = 864365) (by norm_num)
theorem B11979733 : Blo 1617007 11979733 := bbase (se 7 (by rfl) ⟨140387, by rfl⟩ : syracuseStep 11979733 = 280775) (by norm_num)
theorem B13822933 : Blo 1617007 13822933 := bbase (se 7 (by rfl) ⟨161987, by rfl⟩ : syracuseStep 13822933 = 323975) (by norm_num)
theorem B2427869 : Blo 1617007 2427869 := bbase (se 3 (by rfl) ⟨455225, by rfl⟩ : syracuseStep 2427869 = 910451) (by norm_num)
theorem B3640301 : Blo 1617007 3640301 := bbase (se 3 (by rfl) ⟨682556, by rfl⟩ : syracuseStep 3640301 = 1365113) (by norm_num)
theorem B2730989 : Blo 1617007 2730989 := bbase (se 3 (by rfl) ⟨512060, by rfl⟩ : syracuseStep 2730989 = 1024121) (by norm_num)
theorem B2427893 : Blo 1617007 2427893 := bbase (se 5 (by rfl) ⟨113807, by rfl⟩ : syracuseStep 2427893 = 227615) (by norm_num)
theorem B2427917 : Blo 1617007 2427917 := bbase (se 3 (by rfl) ⟨455234, by rfl⟩ : syracuseStep 2427917 = 910469) (by norm_num)
theorem B8195093 : Blo 1617007 8195093 := bbase (se 6 (by rfl) ⟨192072, by rfl⟩ : syracuseStep 8195093 = 384145) (by norm_num)
theorem B2427941 : Blo 1617007 2427941 := bbase (se 4 (by rfl) ⟨227619, by rfl⟩ : syracuseStep 2427941 = 455239) (by norm_num)
theorem B3640373 : Blo 1617007 3640373 := bbase (se 5 (by rfl) ⟨170642, by rfl⟩ : syracuseStep 3640373 = 341285) (by norm_num)
theorem B2427965 : Blo 1617007 2427965 := bbase (se 3 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 2427965 = 910487) (by norm_num)
theorem B2305093 : Blo 1617007 2305093 := bbase (se 4 (by rfl) ⟨216102, by rfl⟩ : syracuseStep 2305093 = 432205) (by norm_num)
theorem B1944653 : Blo 1617007 1944653 := bbase (se 3 (by rfl) ⟨364622, by rfl⟩ : syracuseStep 1944653 = 729245) (by norm_num)
theorem B8744021 : Blo 1617007 8744021 := bbase (se 8 (by rfl) ⟨51234, by rfl⟩ : syracuseStep 8744021 = 102469) (by norm_num)
theorem B2427989 : Blo 1617007 2427989 := bbase (se 8 (by rfl) ⟨14226, by rfl⟩ : syracuseStep 2427989 = 28453) (by norm_num)
theorem B2731117 : Blo 1617007 2731117 := bbase (se 3 (by rfl) ⟨512084, by rfl⟩ : syracuseStep 2731117 = 1024169) (by norm_num)
theorem B2428013 : Blo 1617007 2428013 := bbase (se 3 (by rfl) ⟨455252, by rfl⟩ : syracuseStep 2428013 = 910505) (by norm_num)
theorem B3640445 : Blo 1617007 3640445 := bbase (se 3 (by rfl) ⟨682583, by rfl⟩ : syracuseStep 3640445 = 1365167) (by norm_num)
theorem B2428037 : Blo 1617007 2428037 := bbase (se 4 (by rfl) ⟨227628, by rfl⟩ : syracuseStep 2428037 = 455257) (by norm_num)
theorem B2428061 : Blo 1617007 2428061 := bbase (se 3 (by rfl) ⟨455261, by rfl⟩ : syracuseStep 2428061 = 910523) (by norm_num)
theorem B2305189 : Blo 1617007 2305189 := bbase (se 4 (by rfl) ⟨216111, by rfl⟩ : syracuseStep 2305189 = 432223) (by norm_num)
theorem B2428085 : Blo 1617007 2428085 := bbase (se 5 (by rfl) ⟨113816, by rfl⟩ : syracuseStep 2428085 = 227633) (by norm_num)
theorem B3640517 : Blo 1617007 3640517 := bbase (se 4 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 3640517 = 682597) (by norm_num)
theorem B2731205 : Blo 1617007 2731205 := bbase (se 4 (by rfl) ⟨256050, by rfl⟩ : syracuseStep 2731205 = 512101) (by norm_num)
theorem B2428109 : Blo 1617007 2428109 := bbase (se 3 (by rfl) ⟨455270, by rfl⟩ : syracuseStep 2428109 = 910541) (by norm_num)
theorem B4607189 : Blo 1617007 4607189 := bbase (se 7 (by rfl) ⟨53990, by rfl⟩ : syracuseStep 4607189 = 107981) (by norm_num)
theorem B2428133 : Blo 1617007 2428133 := bbase (se 4 (by rfl) ⟨227637, by rfl⟩ : syracuseStep 2428133 = 455275) (by norm_num)
theorem B2428157 : Blo 1617007 2428157 := bbase (se 3 (by rfl) ⟨455279, by rfl⟩ : syracuseStep 2428157 = 910559) (by norm_num)
theorem B2592005 : Blo 1617007 2592005 := bbase (se 4 (by rfl) ⟨243000, by rfl⟩ : syracuseStep 2592005 = 486001) (by norm_num)
theorem B3640589 : Blo 1617007 3640589 := bbase (se 3 (by rfl) ⟨682610, by rfl⟩ : syracuseStep 3640589 = 1365221) (by norm_num)
theorem B2428181 : Blo 1617007 2428181 := bbase (se 6 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 2428181 = 113821) (by norm_num)
theorem B5459237 : Blo 1617007 5459237 := bbase (se 4 (by rfl) ⟨511803, by rfl⟩ : syracuseStep 5459237 = 1023607) (by norm_num)
theorem B2428205 : Blo 1617007 2428205 := bbase (se 3 (by rfl) ⟨455288, by rfl⟩ : syracuseStep 2428205 = 910577) (by norm_num)
theorem B2731333 : Blo 1617007 2731333 := bbase (se 4 (by rfl) ⟨256062, by rfl⟩ : syracuseStep 2731333 = 512125) (by norm_num)
theorem B2428229 : Blo 1617007 2428229 := bbase (se 4 (by rfl) ⟨227646, by rfl⟩ : syracuseStep 2428229 = 455293) (by norm_num)
theorem B3640661 : Blo 1617007 3640661 := bbase (se 11 (by rfl) ⟨2666, by rfl⟩ : syracuseStep 3640661 = 5333) (by norm_num)
theorem B2428253 : Blo 1617007 2428253 := bbase (se 3 (by rfl) ⟨455297, by rfl⟩ : syracuseStep 2428253 = 910595) (by norm_num)
theorem B2428277 : Blo 1617007 2428277 := bbase (se 5 (by rfl) ⟨113825, by rfl⟩ : syracuseStep 2428277 = 227651) (by norm_num)
theorem B2428301 : Blo 1617007 2428301 := bbase (se 3 (by rfl) ⟨455306, by rfl⟩ : syracuseStep 2428301 = 910613) (by norm_num)
theorem B1944985 : Blo 1617007 1944985 := bbase (se 2 (by rfl) ⟨729369, by rfl⟩ : syracuseStep 1944985 = 1458739) (by norm_num)
theorem B3640733 : Blo 1617007 3640733 := bbase (se 3 (by rfl) ⟨682637, by rfl⟩ : syracuseStep 3640733 = 1365275) (by norm_num)
theorem B2731421 : Blo 1617007 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B2428325 : Blo 1617007 2428325 := bbase (se 4 (by rfl) ⟨227655, by rfl⟩ : syracuseStep 2428325 = 455311) (by norm_num)
theorem B8187317 : Blo 1617007 8187317 := bbase (se 5 (by rfl) ⟨383780, by rfl⟩ : syracuseStep 8187317 = 767561) (by norm_num)
theorem B2428349 : Blo 1617007 2428349 := bbase (se 3 (by rfl) ⟨455315, by rfl⟩ : syracuseStep 2428349 = 910631) (by norm_num)
theorem B5180885 : Blo 1617007 5180885 := bbase (se 7 (by rfl) ⟨60713, by rfl⟩ : syracuseStep 5180885 = 121427) (by norm_num)
theorem B2428373 : Blo 1617007 2428373 := bbase (se 7 (by rfl) ⟨28457, by rfl⟩ : syracuseStep 2428373 = 56915) (by norm_num)
theorem B3640805 : Blo 1617007 3640805 := bbase (se 4 (by rfl) ⟨341325, by rfl⟩ : syracuseStep 3640805 = 682651) (by norm_num)
theorem B2428397 : Blo 1617007 2428397 := bbase (se 3 (by rfl) ⟨455324, by rfl⟩ : syracuseStep 2428397 = 910649) (by norm_num)
theorem B2428421 : Blo 1617007 2428421 := bbase (se 4 (by rfl) ⟨227664, by rfl⟩ : syracuseStep 2428421 = 455329) (by norm_num)
theorem B2731549 : Blo 1617007 2731549 := bbase (se 3 (by rfl) ⟨512165, by rfl⟩ : syracuseStep 2731549 = 1024331) (by norm_num)
theorem B2428445 : Blo 1617007 2428445 := bbase (se 3 (by rfl) ⟨455333, by rfl⟩ : syracuseStep 2428445 = 910667) (by norm_num)
theorem B3640877 : Blo 1617007 3640877 := bbase (se 3 (by rfl) ⟨682664, by rfl⟩ : syracuseStep 3640877 = 1365329) (by norm_num)
theorem B2428469 : Blo 1617007 2428469 := bbase (se 5 (by rfl) ⟨113834, by rfl⟩ : syracuseStep 2428469 = 227669) (by norm_num)
theorem B2428493 : Blo 1617007 2428493 := bbase (se 3 (by rfl) ⟨455342, by rfl⟩ : syracuseStep 2428493 = 910685) (by norm_num)
theorem B3640949 : Blo 1617007 3640949 := bbase (se 5 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 3640949 = 341339) (by norm_num)
theorem B2731637 : Blo 1617007 2731637 := bbase (se 5 (by rfl) ⟨128045, by rfl⟩ : syracuseStep 2731637 = 256091) (by norm_num)
theorem B3641021 : Blo 1617007 3641021 := bbase (se 3 (by rfl) ⟨682691, by rfl⟩ : syracuseStep 3641021 = 1365383) (by norm_num)
theorem B2592461 : Blo 1617007 2592461 := bbase (se 3 (by rfl) ⟨486086, by rfl⟩ : syracuseStep 2592461 = 972173) (by norm_num)
theorem B5459669 : Blo 1617007 5459669 := bbase (se 7 (by rfl) ⟨63980, by rfl⟩ : syracuseStep 5459669 = 127961) (by norm_num)
theorem B2731765 : Blo 1617007 2731765 := bbase (se 5 (by rfl) ⟨128051, by rfl⟩ : syracuseStep 2731765 = 256103) (by norm_num)
theorem B3641093 : Blo 1617007 3641093 := bbase (se 4 (by rfl) ⟨341352, by rfl⟩ : syracuseStep 3641093 = 682705) (by norm_num)
theorem B3641165 : Blo 1617007 3641165 := bbase (se 3 (by rfl) ⟨682718, by rfl⟩ : syracuseStep 3641165 = 1365437) (by norm_num)
theorem B2731853 : Blo 1617007 2731853 := bbase (se 3 (by rfl) ⟨512222, by rfl⟩ : syracuseStep 2731853 = 1024445) (by norm_num)
theorem B3501949 : Blo 1617007 3501949 := bbase (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) (by norm_num)
theorem B3641237 : Blo 1617007 3641237 := bbase (se 6 (by rfl) ⟨85341, by rfl⟩ : syracuseStep 3641237 = 170683) (by norm_num)
theorem B2592685 : Blo 1617007 2592685 := bbase (se 3 (by rfl) ⟨486128, by rfl⟩ : syracuseStep 2592685 = 972257) (by norm_num)
theorem B4607941 : Blo 1617007 4607941 := bbase (se 4 (by rfl) ⟨431994, by rfl⟩ : syracuseStep 4607941 = 863989) (by norm_num)
theorem B2731981 : Blo 1617007 2731981 := bbase (se 3 (by rfl) ⟨512246, by rfl⟩ : syracuseStep 2731981 = 1024493) (by norm_num)
theorem B3641309 : Blo 1617007 3641309 := bbase (se 3 (by rfl) ⟨682745, by rfl⟩ : syracuseStep 3641309 = 1365491) (by norm_num)
theorem B2699245 : Blo 1617007 2699245 := bbase (se 3 (by rfl) ⟨506108, by rfl⟩ : syracuseStep 2699245 = 1012217) (by norm_num)
theorem B2592749 : Blo 1617007 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B3641381 : Blo 1617007 3641381 := bbase (se 4 (by rfl) ⟨341379, by rfl⟩ : syracuseStep 3641381 = 682759) (by norm_num)
theorem B2732069 : Blo 1617007 2732069 := bbase (se 4 (by rfl) ⟨256131, by rfl⟩ : syracuseStep 2732069 = 512263) (by norm_num)
theorem B1970257 : Blo 1617007 1970257 := bbase (se 2 (by rfl) ⟨738846, by rfl⟩ : syracuseStep 1970257 = 1477693) (by norm_num)
theorem B3641453 : Blo 1617007 3641453 := bbase (se 3 (by rfl) ⟨682772, by rfl⟩ : syracuseStep 3641453 = 1365545) (by norm_num)
theorem B2592877 : Blo 1617007 2592877 := bbase (se 3 (by rfl) ⟨486164, by rfl⟩ : syracuseStep 2592877 = 972329) (by norm_num)
theorem B5460101 : Blo 1617007 5460101 := bbase (se 4 (by rfl) ⟨511884, by rfl⟩ : syracuseStep 5460101 = 1023769) (by norm_num)
theorem B3641525 : Blo 1617007 3641525 := bbase (se 5 (by rfl) ⟨170696, by rfl⟩ : syracuseStep 3641525 = 341393) (by norm_num)
theorem B9834709 : Blo 1617007 9834709 := bbase (se 7 (by rfl) ⟨115250, by rfl⟩ : syracuseStep 9834709 = 230501) (by norm_num)
theorem B5181653 : Blo 1617007 5181653 := bbase (se 7 (by rfl) ⟨60722, by rfl⟩ : syracuseStep 5181653 = 121445) (by norm_num)
theorem B3641597 : Blo 1617007 3641597 := bbase (se 3 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 3641597 = 1365599) (by norm_num)
theorem B12144917 : Blo 1617007 12144917 := bbase (se 6 (by rfl) ⟨284646, by rfl⟩ : syracuseStep 12144917 = 569293) (by norm_num)
theorem B3641669 : Blo 1617007 3641669 := bbase (se 4 (by rfl) ⟨341406, by rfl⟩ : syracuseStep 3641669 = 682813) (by norm_num)
theorem B1970509 : Blo 1617007 1970509 := bbase (se 3 (by rfl) ⟨369470, by rfl⟩ : syracuseStep 1970509 = 738941) (by norm_num)
theorem B6140245 : Blo 1617007 6140245 := bbase (se 10 (by rfl) ⟨8994, by rfl⟩ : syracuseStep 6140245 = 17989) (by norm_num)
theorem B3887461 : Blo 1617007 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B3641741 : Blo 1617007 3641741 := bbase (se 3 (by rfl) ⟨682826, by rfl⟩ : syracuseStep 3641741 = 1365653) (by norm_num)
theorem B5829013 : Blo 1617007 5829013 := bbase (se 6 (by rfl) ⟨136617, by rfl⟩ : syracuseStep 5829013 = 273235) (by norm_num)
theorem B3887509 : Blo 1617007 3887509 := bbase (se 6 (by rfl) ⟨91113, by rfl⟩ : syracuseStep 3887509 = 182227) (by norm_num)
theorem B6910373 : Blo 1617007 6910373 := bbase (se 4 (by rfl) ⟨647847, by rfl⟩ : syracuseStep 6910373 = 1295695) (by norm_num)
theorem B4919717 : Blo 1617007 4919717 := bbase (se 4 (by rfl) ⟨461223, by rfl⟩ : syracuseStep 4919717 = 922447) (by norm_num)
theorem B3641813 : Blo 1617007 3641813 := bbase (se 7 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 3641813 = 85355) (by norm_num)
theorem B3641885 : Blo 1617007 3641885 := bbase (se 3 (by rfl) ⟨682853, by rfl⟩ : syracuseStep 3641885 = 1365707) (by norm_num)
theorem B5460533 : Blo 1617007 5460533 := bbase (se 5 (by rfl) ⟨255962, by rfl⟩ : syracuseStep 5460533 = 511925) (by norm_num)
theorem B3641957 : Blo 1617007 3641957 := bbase (se 4 (by rfl) ⟨341433, by rfl⟩ : syracuseStep 3641957 = 682867) (by norm_num)
theorem B6140549 : Blo 1617007 6140549 := bbase (se 4 (by rfl) ⟨575676, by rfl⟩ : syracuseStep 6140549 = 1151353) (by norm_num)
theorem B3642029 : Blo 1617007 3642029 := bbase (se 3 (by rfl) ⟨682880, by rfl⟩ : syracuseStep 3642029 = 1365761) (by norm_num)
theorem B8188613 : Blo 1617007 8188613 := bbase (se 4 (by rfl) ⟨767682, by rfl⟩ : syracuseStep 8188613 = 1535365) (by norm_num)
theorem B5182165 : Blo 1617007 5182165 := bbase (se 7 (by rfl) ⟨60728, by rfl⟩ : syracuseStep 5182165 = 121457) (by norm_num)
theorem B11072213 : Blo 1617007 11072213 := bbase (se 7 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 11072213 = 259505) (by norm_num)
theorem B7377637 : Blo 1617007 7377637 := bbase (se 4 (by rfl) ⟨691653, by rfl⟩ : syracuseStep 7377637 = 1383307) (by norm_num)
theorem B3642101 : Blo 1617007 3642101 := bbase (se 5 (by rfl) ⟨170723, by rfl⟩ : syracuseStep 3642101 = 341447) (by norm_num)
theorem B5911349 : Blo 1617007 5911349 := bbase (se 5 (by rfl) ⟨277094, by rfl⟩ : syracuseStep 5911349 = 554189) (by norm_num)
theorem B3642173 : Blo 1617007 3642173 := bbase (se 3 (by rfl) ⟨682907, by rfl⟩ : syracuseStep 3642173 = 1365815) (by norm_num)
theorem B3642245 : Blo 1617007 3642245 := bbase (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) (by norm_num)
theorem B6230917 : Blo 1617007 6230917 := bbase (se 4 (by rfl) ⟨584148, by rfl⟩ : syracuseStep 6230917 = 1168297) (by norm_num)
theorem B13824917 : Blo 1617007 13824917 := bbase (se 6 (by rfl) ⟨324021, by rfl⟩ : syracuseStep 13824917 = 648043) (by norm_num)
theorem B3642317 : Blo 1617007 3642317 := bbase (se 3 (by rfl) ⟨682934, by rfl⟩ : syracuseStep 3642317 = 1365869) (by norm_num)
theorem B5460965 : Blo 1617007 5460965 := bbase (se 4 (by rfl) ⟨511965, by rfl⟩ : syracuseStep 5460965 = 1023931) (by norm_num)
theorem B3888125 : Blo 1617007 3888125 := bbase (se 3 (by rfl) ⟨729023, by rfl⟩ : syracuseStep 3888125 = 1458047) (by norm_num)
theorem B3642389 : Blo 1617007 3642389 := bbase (se 6 (by rfl) ⟨85368, by rfl⟩ : syracuseStep 3642389 = 170737) (by norm_num)
theorem B3642461 : Blo 1617007 3642461 := bbase (se 3 (by rfl) ⟨682961, by rfl⟩ : syracuseStep 3642461 = 1365923) (by norm_num)
theorem B2765957 : Blo 1617007 2765957 := bbase (se 4 (by rfl) ⟨259308, by rfl⟩ : syracuseStep 2765957 = 518617) (by norm_num)
theorem B3454093 : Blo 1617007 3454093 := bbase (se 3 (by rfl) ⟨647642, by rfl⟩ : syracuseStep 3454093 = 1295285) (by norm_num)
theorem B3642533 : Blo 1617007 3642533 := bbase (se 4 (by rfl) ⟨341487, by rfl⟩ : syracuseStep 3642533 = 682975) (by norm_num)
theorem B3642605 : Blo 1617007 3642605 := bbase (se 3 (by rfl) ⟨682988, by rfl⟩ : syracuseStep 3642605 = 1365977) (by norm_num)
theorem B4093213 : Blo 1617007 4093213 := bbase (se 3 (by rfl) ⟨767477, by rfl⟩ : syracuseStep 4093213 = 1534955) (by norm_num)
theorem B3642677 : Blo 1617007 3642677 := bbase (se 5 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 3642677 = 341501) (by norm_num)
theorem B3888469 : Blo 1617007 3888469 := bbase (se 17 (by rfl) ⟨44, by rfl⟩ : syracuseStep 3888469 = 89) (by norm_num)
theorem B3642749 : Blo 1617007 3642749 := bbase (se 3 (by rfl) ⟨683015, by rfl⟩ : syracuseStep 3642749 = 1366031) (by norm_num)
theorem B6911365 : Blo 1617007 6911365 := bbase (se 4 (by rfl) ⟨647940, by rfl⟩ : syracuseStep 6911365 = 1295881) (by norm_num)
theorem B4093325 : Blo 1617007 4093325 := bbase (se 3 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 4093325 = 1534997) (by norm_num)
theorem B5461397 : Blo 1617007 5461397 := bbase (se 6 (by rfl) ⟨128001, by rfl⟩ : syracuseStep 5461397 = 256003) (by norm_num)
theorem B3888701 : Blo 1617007 3888701 := bbase (se 3 (by rfl) ⟨729131, by rfl⟩ : syracuseStep 3888701 = 1458263) (by norm_num)
theorem B4093517 : Blo 1617007 4093517 := bbase (se 3 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 4093517 = 1535069) (by norm_num)
theorem B92272213 : Blo 1617007 92272213 := bbase (se 8 (by rfl) ⟨540657, by rfl⟩ : syracuseStep 92272213 = 1081315) (by norm_num)
theorem B3454589 : Blo 1617007 3454589 := bbase (se 3 (by rfl) ⟨647735, by rfl⟩ : syracuseStep 3454589 = 1295471) (by norm_num)
theorem B7198373 : Blo 1617007 7198373 := bbase (se 4 (by rfl) ⟨674847, by rfl⟩ : syracuseStep 7198373 = 1349695) (by norm_num)
theorem B3888893 : Blo 1617007 3888893 := bbase (se 3 (by rfl) ⟨729167, by rfl⟩ : syracuseStep 3888893 = 1458335) (by norm_num)
theorem B5461829 : Blo 1617007 5461829 := bbase (se 4 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 5461829 = 1024093) (by norm_num)
theorem B5830501 : Blo 1617007 5830501 := bbase (se 4 (by rfl) ⟨546609, by rfl⟩ : syracuseStep 5830501 = 1093219) (by norm_num)
theorem B1775473 : Blo 1617007 1775473 := bbase (se 2 (by rfl) ⟨665802, by rfl⟩ : syracuseStep 1775473 = 1331605) (by norm_num)
theorem B16824181 : Blo 1617007 16824181 := bbase (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) (by norm_num)
theorem B7378805 : Blo 1617007 7378805 := bbase (se 5 (by rfl) ⟨345881, by rfl⟩ : syracuseStep 7378805 = 691763) (by norm_num)
theorem B4093861 : Blo 1617007 4093861 := bbase (se 4 (by rfl) ⟨383799, by rfl⟩ : syracuseStep 4093861 = 767599) (by norm_num)
theorem B8189909 : Blo 1617007 8189909 := bbase (se 7 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 8189909 = 191951) (by norm_num)
theorem B6559717 : Blo 1617007 6559717 := bbase (se 4 (by rfl) ⟨614973, by rfl⟩ : syracuseStep 6559717 = 1229947) (by norm_num)
theorem B4093973 : Blo 1617007 4093973 := bbase (se 6 (by rfl) ⟨95952, by rfl⟩ : syracuseStep 4093973 = 191905) (by norm_num)
theorem B3889181 : Blo 1617007 3889181 := bbase (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) (by norm_num)
theorem B2627749 : Blo 1617007 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B4094165 : Blo 1617007 4094165 := bbase (se 7 (by rfl) ⟨47978, by rfl⟩ : syracuseStep 4094165 = 95957) (by norm_num)
theorem B5462261 : Blo 1617007 5462261 := bbase (se 5 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 5462261 = 512087) (by norm_num)
theorem B3070237 : Blo 1617007 3070237 := bbase (se 3 (by rfl) ⟨575669, by rfl⟩ : syracuseStep 3070237 = 1151339) (by norm_num)
theorem B9845077 : Blo 1617007 9845077 := bbase (se 10 (by rfl) ⟨14421, by rfl⟩ : syracuseStep 9845077 = 28843) (by norm_num)
theorem B2185589 : Blo 1617007 2185589 := bbase (se 5 (by rfl) ⟨102449, by rfl⟩ : syracuseStep 2185589 = 204899) (by norm_num)
theorem B2914709 : Blo 1617007 2914709 := bbase (se 6 (by rfl) ⟨68313, by rfl⟩ : syracuseStep 2914709 = 136627) (by norm_num)
theorem B5183909 : Blo 1617007 5183909 := bbase (se 4 (by rfl) ⟨485991, by rfl⟩ : syracuseStep 5183909 = 971983) (by norm_num)
theorem B3070381 : Blo 1617007 3070381 := bbase (se 3 (by rfl) ⟨575696, by rfl⟩ : syracuseStep 3070381 = 1151393) (by norm_num)
theorem B3455453 : Blo 1617007 3455453 := bbase (se 3 (by rfl) ⟨647897, by rfl⟩ : syracuseStep 3455453 = 1295795) (by norm_num)
theorem B4094509 : Blo 1617007 4094509 := bbase (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) (by norm_num)
theorem B2046541 : Blo 1617007 2046541 := bbase (se 3 (by rfl) ⟨383726, by rfl⟩ : syracuseStep 2046541 = 767453) (by norm_num)
theorem B3070541 : Blo 1617007 3070541 := bbase (se 3 (by rfl) ⟨575726, by rfl⟩ : syracuseStep 3070541 = 1151453) (by norm_num)
theorem B4668005 : Blo 1617007 4668005 := bbase (se 4 (by rfl) ⟨437625, by rfl⟩ : syracuseStep 4668005 = 875251) (by norm_num)
theorem B1727077 : Blo 1617007 1727077 := bbase (se 4 (by rfl) ⟨161913, by rfl⟩ : syracuseStep 1727077 = 323827) (by norm_num)
theorem B5184101 : Blo 1617007 5184101 := bbase (se 4 (by rfl) ⟨486009, by rfl⟩ : syracuseStep 5184101 = 972019) (by norm_num)
theorem B3455597 : Blo 1617007 3455597 := bbase (se 3 (by rfl) ⟨647924, by rfl⟩ : syracuseStep 3455597 = 1295849) (by norm_num)
theorem B4094621 : Blo 1617007 4094621 := bbase (se 3 (by rfl) ⟨767741, by rfl⟩ : syracuseStep 4094621 = 1535483) (by norm_num)
theorem B5462693 : Blo 1617007 5462693 := bbase (se 4 (by rfl) ⟨512127, by rfl⟩ : syracuseStep 5462693 = 1024255) (by norm_num)
theorem B2046637 : Blo 1617007 2046637 := bbase (se 3 (by rfl) ⟨383744, by rfl⟩ : syracuseStep 2046637 = 767489) (by norm_num)
theorem B6142661 : Blo 1617007 6142661 := bbase (se 4 (by rfl) ⟨575874, by rfl⟩ : syracuseStep 6142661 = 1151749) (by norm_num)
theorem B3070685 : Blo 1617007 3070685 := bbase (se 3 (by rfl) ⟨575753, by rfl⟩ : syracuseStep 3070685 = 1151507) (by norm_num)
theorem B199162709 : Blo 1617007 199162709 := bbase (se 9 (by rfl) ⟨583484, by rfl⟩ : syracuseStep 199162709 = 1166969) (by norm_num)
theorem B2046809 : Blo 1617007 2046809 := bbase (se 2 (by rfl) ⟨767553, by rfl⟩ : syracuseStep 2046809 = 1535107) (by norm_num)
theorem B4094813 : Blo 1617007 4094813 := bbase (se 3 (by rfl) ⟨767777, by rfl⟩ : syracuseStep 4094813 = 1535555) (by norm_num)
theorem B2046865 : Blo 1617007 2046865 := bbase (se 2 (by rfl) ⟨767574, by rfl⟩ : syracuseStep 2046865 = 1535149) (by norm_num)
theorem B7773077 : Blo 1617007 7773077 := bbase (se 6 (by rfl) ⟨182181, by rfl⟩ : syracuseStep 7773077 = 364363) (by norm_num)
theorem B8305573 : Blo 1617007 8305573 := bbase (se 4 (by rfl) ⟨778647, by rfl⟩ : syracuseStep 8305573 = 1557295) (by norm_num)
theorem B1727453 : Blo 1617007 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B6142949 : Blo 1617007 6142949 := bbase (se 4 (by rfl) ⟨575901, by rfl⟩ : syracuseStep 6142949 = 1151803) (by norm_num)
theorem B2046961 : Blo 1617007 2046961 := bbase (se 2 (by rfl) ⟨767610, by rfl⟩ : syracuseStep 2046961 = 1535221) (by norm_num)
theorem B3070973 : Blo 1617007 3070973 := bbase (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) (by norm_num)
theorem B3111949 : Blo 1617007 3111949 := bbase (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) (by norm_num)
theorem B1727525 : Blo 1617007 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B5463125 : Blo 1617007 5463125 := bbase (se 8 (by rfl) ⟨32010, by rfl⟩ : syracuseStep 5463125 = 64021) (by norm_num)
theorem B3071125 : Blo 1617007 3071125 := bbase (se 6 (by rfl) ⟨71979, by rfl⟩ : syracuseStep 3071125 = 143959) (by norm_num)
theorem B2047133 : Blo 1617007 2047133 := bbase (se 3 (by rfl) ⟨383837, by rfl⟩ : syracuseStep 2047133 = 767675) (by norm_num)
theorem B4095157 : Blo 1617007 4095157 := bbase (se 5 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 4095157 = 383921) (by norm_num)
theorem B13327541 : Blo 1617007 13327541 := bbase (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) (by norm_num)
theorem B2047189 : Blo 1617007 2047189 := bbase (se 7 (by rfl) ⟨23990, by rfl⟩ : syracuseStep 2047189 = 47981) (by norm_num)
theorem B1727713 : Blo 1617007 1727713 := bbase (se 2 (by rfl) ⟨647892, by rfl⟩ : syracuseStep 1727713 = 1295785) (by norm_num)
theorem B8191205 : Blo 1617007 8191205 := bbase (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) (by norm_num)
theorem B4095269 : Blo 1617007 4095269 := bbase (se 4 (by rfl) ⟨383931, by rfl⟩ : syracuseStep 4095269 = 767863) (by norm_num)
theorem B2047285 : Blo 1617007 2047285 := bbase (se 5 (by rfl) ⟨95966, by rfl⟩ : syracuseStep 2047285 = 191933) (by norm_num)
theorem B3456341 : Blo 1617007 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B1727897 : Blo 1617007 1727897 := bbase (se 2 (by rfl) ⟨647961, by rfl⟩ : syracuseStep 1727897 = 1295923) (by norm_num)
theorem B3071429 : Blo 1617007 3071429 := bbase (se 4 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 3071429 = 575893) (by norm_num)
theorem B2047457 : Blo 1617007 2047457 := bbase (se 2 (by rfl) ⟨767796, by rfl⟩ : syracuseStep 2047457 = 1535593) (by norm_num)
theorem B4095461 : Blo 1617007 4095461 := bbase (se 4 (by rfl) ⟨383949, by rfl⟩ : syracuseStep 4095461 = 767899) (by norm_num)
theorem B7380485 : Blo 1617007 7380485 := bbase (se 4 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 7380485 = 1383841) (by norm_num)
theorem B5463557 : Blo 1617007 5463557 := bbase (se 4 (by rfl) ⟨512208, by rfl⟩ : syracuseStep 5463557 = 1024417) (by norm_num)
theorem B2047513 : Blo 1617007 2047513 := bbase (se 2 (by rfl) ⟨767817, by rfl⟩ : syracuseStep 2047513 = 1535635) (by norm_num)
theorem B1998361 : Blo 1617007 1998361 := bbase (se 2 (by rfl) ⟨749385, by rfl⟩ : syracuseStep 1998361 = 1498771) (by norm_num)
theorem B3939877 : Blo 1617007 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B10362485 : Blo 1617007 10362485 := bbase (se 5 (by rfl) ⟨485741, by rfl⟩ : syracuseStep 10362485 = 971483) (by norm_num)
theorem B2047609 : Blo 1617007 2047609 := bbase (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) (by norm_num)
theorem B2186941 : Blo 1617007 2186941 := bbase (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) (by norm_num)
theorem B2047781 : Blo 1617007 2047781 := bbase (se 4 (by rfl) ⟨191979, by rfl⟩ : syracuseStep 2047781 = 383959) (by norm_num)
theorem B4095805 : Blo 1617007 4095805 := bbase (se 3 (by rfl) ⟨767963, by rfl⟩ : syracuseStep 4095805 = 1535927) (by norm_num)
theorem B2047837 : Blo 1617007 2047837 := bbase (se 3 (by rfl) ⟨383969, by rfl⟩ : syracuseStep 2047837 = 767939) (by norm_num)
theorem B6225781 : Blo 1617007 6225781 := bbase (se 5 (by rfl) ⟨291833, by rfl⟩ : syracuseStep 6225781 = 583667) (by norm_num)
theorem B4095917 : Blo 1617007 4095917 := bbase (se 3 (by rfl) ⟨767984, by rfl⟩ : syracuseStep 4095917 = 1535969) (by norm_num)
theorem B5463989 : Blo 1617007 5463989 := bbase (se 5 (by rfl) ⟨256124, by rfl⟩ : syracuseStep 5463989 = 512249) (by norm_num)
theorem B2047933 : Blo 1617007 2047933 := bbase (se 3 (by rfl) ⟨383987, by rfl⟩ : syracuseStep 2047933 = 767975) (by norm_num)
theorem B2187221 : Blo 1617007 2187221 := bbase (se 7 (by rfl) ⟨25631, by rfl⟩ : syracuseStep 2187221 = 51263) (by norm_num)
theorem B27648053 : Blo 1617007 27648053 := bstep (se 5 (by rfl) ⟨1296002, by rfl⟩ : syracuseStep 27648053 = 2592005) B2592005
theorem B2187329 : Blo 1617007 2187329 := bstep (se 2 (by rfl) ⟨820248, by rfl⟩ : syracuseStep 2187329 = 1640497) B1640497
theorem B16597061 : Blo 1617007 16597061 := bstep (se 4 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 16597061 = 3111949) B3111949
theorem B10371149 : Blo 1617007 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B10657925 : Blo 1617007 10657925 := bstep (se 4 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 10657925 = 1998361) B1998361
theorem B3457169 : Blo 1617007 3457169 := bstep (se 2 (by rfl) ⟨1296438, by rfl⟩ : syracuseStep 3457169 = 2592877) B2592877
theorem B4374701 : Blo 1617007 4374701 := bstep (se 3 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 4374701 = 1640513) B1640513
theorem B8192177 : Blo 1617007 8192177 := bstep (se 2 (by rfl) ⟨3072066, by rfl⟩ : syracuseStep 8192177 = 6144133) B6144133
theorem B4096241 : Blo 1617007 4096241 := bstep (se 2 (by rfl) ⟨1536090, by rfl⟩ : syracuseStep 4096241 = 3072181) B3072181
theorem B4096291 : Blo 1617007 4096291 := bstep (se 1 (by rfl) ⟨3072218, by rfl⟩ : syracuseStep 4096291 = 6144437) B6144437
theorem B2048323 : Blo 1617007 2048323 := bstep (se 1 (by rfl) ⟨1536242, by rfl⟩ : syracuseStep 2048323 = 3072485) B3072485
theorem B3072401 : Blo 1617007 3072401 := bstep (se 2 (by rfl) ⟨1152150, by rfl⟩ : syracuseStep 3072401 = 2304301) B2304301
theorem B2048419 : Blo 1617007 2048419 := bstep (se 1 (by rfl) ⟨1536314, by rfl⟩ : syracuseStep 2048419 = 3072629) B3072629
theorem B4096433 : Blo 1617007 4096433 := bstep (se 2 (by rfl) ⟨1536162, by rfl⟩ : syracuseStep 4096433 = 3072325) B3072325
theorem B7381475 : Blo 1617007 7381475 := bstep (se 1 (by rfl) ⟨5536106, by rfl⟩ : syracuseStep 7381475 = 11072213) B11072213
theorem B34972181 : Blo 1617007 34972181 := bstep (se 6 (by rfl) ⟨819660, by rfl⟩ : syracuseStep 34972181 = 1639321) B1639321
theorem B63054389 : Blo 1617007 63054389 := bstep (se 5 (by rfl) ⟨2955674, by rfl⟩ : syracuseStep 63054389 = 5911349) B5911349
theorem B1819219 : Blo 1617007 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B9216611 : Blo 1617007 9216611 := bstep (se 1 (by rfl) ⟨6912458, by rfl⟩ : syracuseStep 9216611 = 13824917) B13824917
theorem B2425523 : Blo 1617007 2425523 := bstep (se 1 (by rfl) ⟨1819142, by rfl⟩ : syracuseStep 2425523 = 3638285) B3638285
theorem B2425553 : Blo 1617007 2425553 := bstep (se 2 (by rfl) ⟨909582, by rfl⟩ : syracuseStep 2425553 = 1819165) B1819165
theorem B2425571 : Blo 1617007 2425571 := bstep (se 1 (by rfl) ⟨1819178, by rfl⟩ : syracuseStep 2425571 = 3638357) B3638357
theorem B1819363 : Blo 1617007 1819363 := bstep (se 1 (by rfl) ⟨1364522, by rfl⟩ : syracuseStep 1819363 = 2729045) B2729045
theorem B2425601 : Blo 1617007 2425601 := bstep (se 2 (by rfl) ⟨909600, by rfl⟩ : syracuseStep 2425601 = 1819201) B1819201
theorem B2728721 : Blo 1617007 2728721 := bstep (se 2 (by rfl) ⟨1023270, by rfl⟩ : syracuseStep 2728721 = 2046541) B2046541
theorem B2425619 : Blo 1617007 2425619 := bstep (se 1 (by rfl) ⟨1819214, by rfl⟩ : syracuseStep 2425619 = 3638429) B3638429
theorem B2425649 : Blo 1617007 2425649 := bstep (se 2 (by rfl) ⟨909618, by rfl⟩ : syracuseStep 2425649 = 1819237) B1819237
theorem B2302769 : Blo 1617007 2302769 := bstep (se 2 (by rfl) ⟨863538, by rfl⟩ : syracuseStep 2302769 = 1727077) B1727077
theorem B2188081 : Blo 1617007 2188081 := bstep (se 2 (by rfl) ⟨820530, by rfl⟩ : syracuseStep 2188081 = 1641061) B1641061
theorem B20742965 : Blo 1617007 20742965 := bstep (se 5 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 20742965 = 1944653) B1944653
theorem B2425667 : Blo 1617007 2425667 := bstep (se 1 (by rfl) ⟨1819250, by rfl⟩ : syracuseStep 2425667 = 3638501) B3638501
theorem B2425697 : Blo 1617007 2425697 := bstep (se 2 (by rfl) ⟨909636, by rfl⟩ : syracuseStep 2425697 = 1819273) B1819273
theorem B2425715 : Blo 1617007 2425715 := bstep (se 1 (by rfl) ⟨1819286, by rfl⟩ : syracuseStep 2425715 = 3638573) B3638573
theorem B1819507 : Blo 1617007 1819507 := bstep (se 1 (by rfl) ⟨1364630, by rfl⟩ : syracuseStep 1819507 = 2729261) B2729261
theorem B2728849 : Blo 1617007 2728849 := bstep (se 2 (by rfl) ⟨1023318, by rfl⟩ : syracuseStep 2728849 = 2046637) B2046637
theorem B2425745 : Blo 1617007 2425745 := bstep (se 2 (by rfl) ⟨909654, by rfl⟩ : syracuseStep 2425745 = 1819309) B1819309
theorem B2048915 : Blo 1617007 2048915 := bstep (se 1 (by rfl) ⟨1536686, by rfl⟩ : syracuseStep 2048915 = 3073373) B3073373
theorem B2425763 : Blo 1617007 2425763 := bstep (se 1 (by rfl) ⟨1819322, by rfl⟩ : syracuseStep 2425763 = 3638645) B3638645
theorem B2728883 : Blo 1617007 2728883 := bstep (se 1 (by rfl) ⟨2046662, by rfl⟩ : syracuseStep 2728883 = 4093325) B4093325
theorem B2425793 : Blo 1617007 2425793 := bstep (se 2 (by rfl) ⟨909672, by rfl⟩ : syracuseStep 2425793 = 1819345) B1819345
theorem B2425811 : Blo 1617007 2425811 := bstep (se 1 (by rfl) ⟨1819358, by rfl⟩ : syracuseStep 2425811 = 3638717) B3638717
theorem B12288995 : Blo 1617007 12288995 := bstep (se 1 (by rfl) ⟨9216746, by rfl⟩ : syracuseStep 12288995 = 18433493) B18433493
theorem B2425841 : Blo 1617007 2425841 := bstep (se 2 (by rfl) ⟨909690, by rfl⟩ : syracuseStep 2425841 = 1819381) B1819381
theorem B2425859 : Blo 1617007 2425859 := bstep (se 1 (by rfl) ⟨1819394, by rfl⟩ : syracuseStep 2425859 = 3638789) B3638789
theorem B1819651 : Blo 1617007 1819651 := bstep (se 1 (by rfl) ⟨1364738, by rfl⟩ : syracuseStep 1819651 = 2729477) B2729477
theorem B2425889 : Blo 1617007 2425889 := bstep (se 2 (by rfl) ⟨909708, by rfl⟩ : syracuseStep 2425889 = 1819417) B1819417
theorem B1639459 : Blo 1617007 1639459 := bstep (se 1 (by rfl) ⟨1229594, by rfl⟩ : syracuseStep 1639459 = 2459189) B2459189
theorem B3638321 : Blo 1617007 3638321 := bstep (se 2 (by rfl) ⟨1364370, by rfl⟩ : syracuseStep 3638321 = 2728741) B2728741
theorem B2729011 : Blo 1617007 2729011 := bstep (se 1 (by rfl) ⟨2046758, by rfl⟩ : syracuseStep 2729011 = 4093517) B4093517
theorem B2425907 : Blo 1617007 2425907 := bstep (se 1 (by rfl) ⟨1819430, by rfl⟩ : syracuseStep 2425907 = 3638861) B3638861
theorem B3638339 : Blo 1617007 3638339 := bstep (se 1 (by rfl) ⟨2728754, by rfl⟩ : syracuseStep 3638339 = 5457509) B5457509
theorem B2458691 : Blo 1617007 2458691 := bstep (se 1 (by rfl) ⟨1844018, by rfl⟩ : syracuseStep 2458691 = 3688037) B3688037
theorem B2425937 : Blo 1617007 2425937 := bstep (se 2 (by rfl) ⟨909726, by rfl⟩ : syracuseStep 2425937 = 1819453) B1819453
theorem B2425955 : Blo 1617007 2425955 := bstep (se 1 (by rfl) ⟨1819466, by rfl⟩ : syracuseStep 2425955 = 3638933) B3638933
theorem B2425985 : Blo 1617007 2425985 := bstep (se 2 (by rfl) ⟨909744, by rfl⟩ : syracuseStep 2425985 = 1819489) B1819489
theorem B2426003 : Blo 1617007 2426003 := bstep (se 1 (by rfl) ⟨1819502, by rfl⟩ : syracuseStep 2426003 = 3639005) B3639005
theorem B1819795 : Blo 1617007 1819795 := bstep (se 1 (by rfl) ⟨1364846, by rfl⟩ : syracuseStep 1819795 = 2729693) B2729693
theorem B2426033 : Blo 1617007 2426033 := bstep (se 2 (by rfl) ⟨909762, by rfl⟩ : syracuseStep 2426033 = 1819525) B1819525
theorem B8307889 : Blo 1617007 8307889 := bstep (se 2 (by rfl) ⟨3115458, by rfl⟩ : syracuseStep 8307889 = 6230917) B6230917
theorem B2729153 : Blo 1617007 2729153 := bstep (se 2 (by rfl) ⟨1023432, by rfl⟩ : syracuseStep 2729153 = 2046865) B2046865
theorem B2426051 : Blo 1617007 2426051 := bstep (se 1 (by rfl) ⟨1819538, by rfl⟩ : syracuseStep 2426051 = 3639077) B3639077
theorem B2426081 : Blo 1617007 2426081 := bstep (se 2 (by rfl) ⟨909780, by rfl⟩ : syracuseStep 2426081 = 1819561) B1819561
theorem B2426099 : Blo 1617007 2426099 := bstep (se 1 (by rfl) ⟨1819574, by rfl⟩ : syracuseStep 2426099 = 3639149) B3639149
theorem B2426129 : Blo 1617007 2426129 := bstep (se 2 (by rfl) ⟨909798, by rfl⟩ : syracuseStep 2426129 = 1819597) B1819597
theorem B3073297 : Blo 1617007 3073297 := bstep (se 2 (by rfl) ⟨1152486, by rfl⟩ : syracuseStep 3073297 = 2304973) B2304973
theorem B2426147 : Blo 1617007 2426147 := bstep (se 1 (by rfl) ⟨1819610, by rfl⟩ : syracuseStep 2426147 = 3639221) B3639221
theorem B1819939 : Blo 1617007 1819939 := bstep (se 1 (by rfl) ⟨1364954, by rfl⟩ : syracuseStep 1819939 = 2729909) B2729909
theorem B2729281 : Blo 1617007 2729281 := bstep (se 2 (by rfl) ⟨1023480, by rfl⟩ : syracuseStep 2729281 = 2046961) B2046961
theorem B2426177 : Blo 1617007 2426177 := bstep (se 2 (by rfl) ⟨909816, by rfl⟩ : syracuseStep 2426177 = 1819633) B1819633
theorem B3638609 : Blo 1617007 3638609 := bstep (se 2 (by rfl) ⟨1364478, by rfl⟩ : syracuseStep 3638609 = 2728957) B2728957
theorem B2426195 : Blo 1617007 2426195 := bstep (se 1 (by rfl) ⟨1819646, by rfl⟩ : syracuseStep 2426195 = 3639293) B3639293
theorem B3638627 : Blo 1617007 3638627 := bstep (se 1 (by rfl) ⟨2728970, by rfl⟩ : syracuseStep 3638627 = 5457941) B5457941
theorem B2729315 : Blo 1617007 2729315 := bstep (se 1 (by rfl) ⟨2046986, by rfl⟩ : syracuseStep 2729315 = 4093973) B4093973
theorem B6145379 : Blo 1617007 6145379 := bstep (se 1 (by rfl) ⟨4609034, by rfl⟩ : syracuseStep 6145379 = 9218069) B9218069
theorem B2426225 : Blo 1617007 2426225 := bstep (se 2 (by rfl) ⟨909834, by rfl⟩ : syracuseStep 2426225 = 1819669) B1819669
theorem B2426243 : Blo 1617007 2426243 := bstep (se 1 (by rfl) ⟨1819682, by rfl⟩ : syracuseStep 2426243 = 3639365) B3639365
theorem B4097425 : Blo 1617007 4097425 := bstep (se 2 (by rfl) ⟨1536534, by rfl⟩ : syracuseStep 4097425 = 3073069) B3073069
theorem B2426273 : Blo 1617007 2426273 := bstep (se 2 (by rfl) ⟨909852, by rfl⟩ : syracuseStep 2426273 = 1819705) B1819705
theorem B3073457 : Blo 1617007 3073457 := bstep (se 2 (by rfl) ⟨1152546, by rfl⟩ : syracuseStep 3073457 = 2305093) B2305093
theorem B2426291 : Blo 1617007 2426291 := bstep (se 1 (by rfl) ⟨1819718, by rfl⟩ : syracuseStep 2426291 = 3639437) B3639437
theorem B1820083 : Blo 1617007 1820083 := bstep (se 1 (by rfl) ⟨1365062, by rfl⟩ : syracuseStep 1820083 = 2730125) B2730125
theorem B2426321 : Blo 1617007 2426321 := bstep (se 2 (by rfl) ⟨909870, by rfl⟩ : syracuseStep 2426321 = 1819741) B1819741
theorem B2729443 : Blo 1617007 2729443 := bstep (se 1 (by rfl) ⟨2047082, by rfl⟩ : syracuseStep 2729443 = 4094165) B4094165
theorem B2426339 : Blo 1617007 2426339 := bstep (se 1 (by rfl) ⟨1819754, by rfl⟩ : syracuseStep 2426339 = 3639509) B3639509
theorem B2426369 : Blo 1617007 2426369 := bstep (se 2 (by rfl) ⟨909888, by rfl⟩ : syracuseStep 2426369 = 1819777) B1819777
theorem B2426387 : Blo 1617007 2426387 := bstep (se 1 (by rfl) ⟨1819790, by rfl⟩ : syracuseStep 2426387 = 3639581) B3639581
theorem B2426417 : Blo 1617007 2426417 := bstep (se 2 (by rfl) ⟨909906, by rfl⟩ : syracuseStep 2426417 = 1819813) B1819813
theorem B2426435 : Blo 1617007 2426435 := bstep (se 1 (by rfl) ⟨1819826, by rfl⟩ : syracuseStep 2426435 = 3639653) B3639653
theorem B1820227 : Blo 1617007 1820227 := bstep (se 1 (by rfl) ⟨1365170, by rfl⟩ : syracuseStep 1820227 = 2730341) B2730341
theorem B2590289 : Blo 1617007 2590289 := bstep (se 2 (by rfl) ⟨971358, by rfl⟩ : syracuseStep 2590289 = 1942717) B1942717
theorem B2426465 : Blo 1617007 2426465 := bstep (se 2 (by rfl) ⟨909924, by rfl⟩ : syracuseStep 2426465 = 1819849) B1819849
theorem B8193635 : Blo 1617007 8193635 := bstep (se 1 (by rfl) ⟨6145226, by rfl⟩ : syracuseStep 8193635 = 12290453) B12290453
theorem B3638897 : Blo 1617007 3638897 := bstep (se 2 (by rfl) ⟨1364586, by rfl⟩ : syracuseStep 3638897 = 2729173) B2729173
theorem B2729585 : Blo 1617007 2729585 := bstep (se 2 (by rfl) ⟨1023594, by rfl⟩ : syracuseStep 2729585 = 2047189) B2047189
theorem B2426483 : Blo 1617007 2426483 := bstep (se 1 (by rfl) ⟨1819862, by rfl⟩ : syracuseStep 2426483 = 3639725) B3639725
theorem B3638915 : Blo 1617007 3638915 := bstep (se 1 (by rfl) ⟨2729186, by rfl⟩ : syracuseStep 3638915 = 5458373) B5458373
theorem B2426513 : Blo 1617007 2426513 := bstep (se 2 (by rfl) ⟨909942, by rfl⟩ : syracuseStep 2426513 = 1819885) B1819885
theorem B2303635 : Blo 1617007 2303635 := bstep (se 1 (by rfl) ⟨1727726, by rfl⟩ : syracuseStep 2303635 = 3455453) B3455453
theorem B2426531 : Blo 1617007 2426531 := bstep (se 1 (by rfl) ⟨1819898, by rfl⟩ : syracuseStep 2426531 = 3639797) B3639797
theorem B4097699 : Blo 1617007 4097699 := bstep (se 1 (by rfl) ⟨3073274, by rfl⟩ : syracuseStep 4097699 = 6146549) B6146549
theorem B2426561 : Blo 1617007 2426561 := bstep (se 2 (by rfl) ⟨909960, by rfl⟩ : syracuseStep 2426561 = 1819921) B1819921
theorem B5457617 : Blo 1617007 5457617 := bstep (se 2 (by rfl) ⟨2046606, by rfl⟩ : syracuseStep 5457617 = 4093213) B4093213
theorem B2426579 : Blo 1617007 2426579 := bstep (se 1 (by rfl) ⟨1819934, by rfl⟩ : syracuseStep 2426579 = 3639869) B3639869
theorem B1820371 : Blo 1617007 1820371 := bstep (se 1 (by rfl) ⟨1365278, by rfl⟩ : syracuseStep 1820371 = 2730557) B2730557
theorem B2729713 : Blo 1617007 2729713 := bstep (se 2 (by rfl) ⟨1023642, by rfl⟩ : syracuseStep 2729713 = 2047285) B2047285
theorem B2426609 : Blo 1617007 2426609 := bstep (se 2 (by rfl) ⟨909978, by rfl⟩ : syracuseStep 2426609 = 1819957) B1819957
theorem B2303731 : Blo 1617007 2303731 := bstep (se 1 (by rfl) ⟨1727798, by rfl⟩ : syracuseStep 2303731 = 3455597) B3455597
theorem B2426627 : Blo 1617007 2426627 := bstep (se 1 (by rfl) ⟨1819970, by rfl⟩ : syracuseStep 2426627 = 3639941) B3639941
theorem B19195661 : Blo 1617007 19195661 := bstep (se 3 (by rfl) ⟨3599186, by rfl⟩ : syracuseStep 19195661 = 7198373) B7198373
theorem B2590481 : Blo 1617007 2590481 := bstep (se 2 (by rfl) ⟨971430, by rfl⟩ : syracuseStep 2590481 = 1942861) B1942861
theorem B2729747 : Blo 1617007 2729747 := bstep (se 1 (by rfl) ⟨2047310, by rfl⟩ : syracuseStep 2729747 = 4094621) B4094621
theorem B2426657 : Blo 1617007 2426657 := bstep (se 2 (by rfl) ⟨909996, by rfl⟩ : syracuseStep 2426657 = 1819993) B1819993
theorem B4605731 : Blo 1617007 4605731 := bstep (se 1 (by rfl) ⟨3454298, by rfl⟩ : syracuseStep 4605731 = 6908597) B6908597
theorem B2426675 : Blo 1617007 2426675 := bstep (se 1 (by rfl) ⟨1820006, by rfl⟩ : syracuseStep 2426675 = 3640013) B3640013
theorem B2426705 : Blo 1617007 2426705 := bstep (se 2 (by rfl) ⟨910014, by rfl⟩ : syracuseStep 2426705 = 1820029) B1820029
theorem B2426723 : Blo 1617007 2426723 := bstep (se 1 (by rfl) ⟨1820042, by rfl⟩ : syracuseStep 2426723 = 3640085) B3640085
theorem B1820515 : Blo 1617007 1820515 := bstep (se 1 (by rfl) ⟨1365386, by rfl⟩ : syracuseStep 1820515 = 2730773) B2730773
theorem B4097891 : Blo 1617007 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B2426753 : Blo 1617007 2426753 := bstep (se 2 (by rfl) ⟨910032, by rfl⟩ : syracuseStep 2426753 = 1820065) B1820065
theorem B3639185 : Blo 1617007 3639185 := bstep (se 2 (by rfl) ⟨1364694, by rfl⟩ : syracuseStep 3639185 = 2729389) B2729389
theorem B2729875 : Blo 1617007 2729875 := bstep (se 1 (by rfl) ⟨2047406, by rfl⟩ : syracuseStep 2729875 = 4094813) B4094813
theorem B2426771 : Blo 1617007 2426771 := bstep (se 1 (by rfl) ⟨1820078, by rfl⟩ : syracuseStep 2426771 = 3640157) B3640157
theorem B3639203 : Blo 1617007 3639203 := bstep (se 1 (by rfl) ⟨2729402, by rfl⟩ : syracuseStep 3639203 = 5458805) B5458805
theorem B2426801 : Blo 1617007 2426801 := bstep (se 2 (by rfl) ⟨910050, by rfl⟩ : syracuseStep 2426801 = 1820101) B1820101
theorem B2426819 : Blo 1617007 2426819 := bstep (se 1 (by rfl) ⟨1820114, by rfl⟩ : syracuseStep 2426819 = 3640229) B3640229
theorem B2426849 : Blo 1617007 2426849 := bstep (se 2 (by rfl) ⟨910068, by rfl⟩ : syracuseStep 2426849 = 1820137) B1820137
theorem B2426867 : Blo 1617007 2426867 := bstep (se 1 (by rfl) ⟨1820150, by rfl⟩ : syracuseStep 2426867 = 3640301) B3640301
theorem B1820659 : Blo 1617007 1820659 := bstep (se 1 (by rfl) ⟨1365494, by rfl⟩ : syracuseStep 1820659 = 2730989) B2730989
theorem B2426897 : Blo 1617007 2426897 := bstep (se 2 (by rfl) ⟨910086, by rfl⟩ : syracuseStep 2426897 = 1820173) B1820173
theorem B2730017 : Blo 1617007 2730017 := bstep (se 2 (by rfl) ⟨1023756, by rfl⟩ : syracuseStep 2730017 = 2047513) B2047513
theorem B2426915 : Blo 1617007 2426915 := bstep (se 1 (by rfl) ⟨1820186, by rfl⟩ : syracuseStep 2426915 = 3640373) B3640373
theorem B5253169 : Blo 1617007 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B2426945 : Blo 1617007 2426945 := bstep (se 2 (by rfl) ⟨910104, by rfl⟩ : syracuseStep 2426945 = 1820209) B1820209
theorem B2426963 : Blo 1617007 2426963 := bstep (se 1 (by rfl) ⟨1820222, by rfl⟩ : syracuseStep 2426963 = 3640445) B3640445
theorem B2426993 : Blo 1617007 2426993 := bstep (se 2 (by rfl) ⟨910122, by rfl⟩ : syracuseStep 2426993 = 1820245) B1820245
theorem B123029617 : Blo 1617007 123029617 := bstep (se 2 (by rfl) ⟨46136106, by rfl⟩ : syracuseStep 123029617 = 92272213) B92272213
theorem B2427011 : Blo 1617007 2427011 := bstep (se 1 (by rfl) ⟨1820258, by rfl⟩ : syracuseStep 2427011 = 3640517) B3640517
theorem B1820803 : Blo 1617007 1820803 := bstep (se 1 (by rfl) ⟨1365602, by rfl⟩ : syracuseStep 1820803 = 2731205) B2731205
theorem B15558797 : Blo 1617007 15558797 := bstep (se 3 (by rfl) ⟨2917274, by rfl⟩ : syracuseStep 15558797 = 5834549) B5834549
theorem B2730145 : Blo 1617007 2730145 := bstep (se 2 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 2730145 = 2047609) B2047609
theorem B2427041 : Blo 1617007 2427041 := bstep (se 2 (by rfl) ⟨910140, by rfl⟩ : syracuseStep 2427041 = 1820281) B1820281
theorem B3639473 : Blo 1617007 3639473 := bstep (se 2 (by rfl) ⟨1364802, by rfl⟩ : syracuseStep 3639473 = 2729605) B2729605
theorem B2427059 : Blo 1617007 2427059 := bstep (se 1 (by rfl) ⟨1820294, by rfl⟩ : syracuseStep 2427059 = 3640589) B3640589
theorem B3639491 : Blo 1617007 3639491 := bstep (se 1 (by rfl) ⟨2729618, by rfl⟩ : syracuseStep 3639491 = 5459237) B5459237
theorem B2730179 : Blo 1617007 2730179 := bstep (se 1 (by rfl) ⟨2047634, by rfl⟩ : syracuseStep 2730179 = 4095269) B4095269
theorem B2427089 : Blo 1617007 2427089 := bstep (se 2 (by rfl) ⟨910158, by rfl⟩ : syracuseStep 2427089 = 1820317) B1820317
theorem B2427107 : Blo 1617007 2427107 := bstep (se 1 (by rfl) ⟨1820330, by rfl⟩ : syracuseStep 2427107 = 3640661) B3640661
theorem B2304227 : Blo 1617007 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B5458157 : Blo 1617007 5458157 := bstep (se 3 (by rfl) ⟨1023404, by rfl⟩ : syracuseStep 5458157 = 2046809) B2046809
theorem B2427137 : Blo 1617007 2427137 := bstep (se 2 (by rfl) ⟨910176, by rfl⟩ : syracuseStep 2427137 = 1820353) B1820353
theorem B2427155 : Blo 1617007 2427155 := bstep (se 1 (by rfl) ⟨1820366, by rfl⟩ : syracuseStep 2427155 = 3640733) B3640733
theorem B1820947 : Blo 1617007 1820947 := bstep (se 1 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 1820947 = 2731421) B2731421
theorem B5458211 : Blo 1617007 5458211 := bstep (se 1 (by rfl) ⟨4093658, by rfl⟩ : syracuseStep 5458211 = 8187317) B8187317
theorem B2427185 : Blo 1617007 2427185 := bstep (se 2 (by rfl) ⟨910194, by rfl⟩ : syracuseStep 2427185 = 1820389) B1820389
theorem B2730307 : Blo 1617007 2730307 := bstep (se 1 (by rfl) ⟨2047730, by rfl⟩ : syracuseStep 2730307 = 4095461) B4095461
theorem B2427203 : Blo 1617007 2427203 := bstep (se 1 (by rfl) ⟨1820402, by rfl⟩ : syracuseStep 2427203 = 3640805) B3640805
theorem B6146381 : Blo 1617007 6146381 := bstep (se 3 (by rfl) ⟨1152446, by rfl⟩ : syracuseStep 6146381 = 2304893) B2304893
theorem B2427233 : Blo 1617007 2427233 := bstep (se 2 (by rfl) ⟨910212, by rfl⟩ : syracuseStep 2427233 = 1820425) B1820425
theorem B5532013 : Blo 1617007 5532013 := bstep (se 3 (by rfl) ⟨1037252, by rfl⟩ : syracuseStep 5532013 = 2074505) B2074505
theorem B2427251 : Blo 1617007 2427251 := bstep (se 1 (by rfl) ⟨1820438, by rfl⟩ : syracuseStep 2427251 = 3640877) B3640877
theorem B8194445 : Blo 1617007 8194445 := bstep (se 3 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 8194445 = 3072917) B3072917
theorem B2427281 : Blo 1617007 2427281 := bstep (se 2 (by rfl) ⟨910230, by rfl⟩ : syracuseStep 2427281 = 1820461) B1820461
theorem B6908323 : Blo 1617007 6908323 := bstep (se 1 (by rfl) ⟨5181242, by rfl⟩ : syracuseStep 6908323 = 10362485) B10362485
theorem B2427299 : Blo 1617007 2427299 := bstep (se 1 (by rfl) ⟨1820474, by rfl⟩ : syracuseStep 2427299 = 3640949) B3640949
theorem B1821091 : Blo 1617007 1821091 := bstep (se 1 (by rfl) ⟨1365818, by rfl⟩ : syracuseStep 1821091 = 2731637) B2731637
theorem B2427329 : Blo 1617007 2427329 := bstep (se 2 (by rfl) ⟨910248, by rfl⟩ : syracuseStep 2427329 = 1820497) B1820497
theorem B3639761 : Blo 1617007 3639761 := bstep (se 2 (by rfl) ⟨1364910, by rfl⟩ : syracuseStep 3639761 = 2729821) B2729821
theorem B2730449 : Blo 1617007 2730449 := bstep (se 2 (by rfl) ⟨1023918, by rfl⟩ : syracuseStep 2730449 = 2047837) B2047837
theorem B2427347 : Blo 1617007 2427347 := bstep (se 1 (by rfl) ⟨1820510, by rfl⟩ : syracuseStep 2427347 = 3641021) B3641021
theorem B3639779 : Blo 1617007 3639779 := bstep (se 1 (by rfl) ⟨2729834, by rfl⟩ : syracuseStep 3639779 = 5459669) B5459669
theorem B22432241 : Blo 1617007 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B8301041 : Blo 1617007 8301041 := bstep (se 2 (by rfl) ⟨3112890, by rfl⟩ : syracuseStep 8301041 = 6225781) B6225781
theorem B2427377 : Blo 1617007 2427377 := bstep (se 2 (by rfl) ⟨910266, by rfl⟩ : syracuseStep 2427377 = 1820533) B1820533
theorem B2427395 : Blo 1617007 2427395 := bstep (se 1 (by rfl) ⟨1820546, by rfl⟩ : syracuseStep 2427395 = 3641093) B3641093
theorem B2427425 : Blo 1617007 2427425 := bstep (se 2 (by rfl) ⟨910284, by rfl⟩ : syracuseStep 2427425 = 1820569) B1820569
theorem B5458481 : Blo 1617007 5458481 := bstep (se 2 (by rfl) ⟨2046930, by rfl⟩ : syracuseStep 5458481 = 4093861) B4093861
theorem B2427443 : Blo 1617007 2427443 := bstep (se 1 (by rfl) ⟨1820582, by rfl⟩ : syracuseStep 2427443 = 3641165) B3641165
theorem B1821235 : Blo 1617007 1821235 := bstep (se 1 (by rfl) ⟨1365926, by rfl⟩ : syracuseStep 1821235 = 2731853) B2731853
theorem B14395973 : Blo 1617007 14395973 := bstep (se 4 (by rfl) ⟨1349622, by rfl⟩ : syracuseStep 14395973 = 2699245) B2699245
theorem B4606541 : Blo 1617007 4606541 := bstep (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) B1727453
theorem B2730577 : Blo 1617007 2730577 := bstep (se 2 (by rfl) ⟨1023966, by rfl⟩ : syracuseStep 2730577 = 2047933) B2047933
theorem B2427473 : Blo 1617007 2427473 := bstep (se 2 (by rfl) ⟨910302, by rfl⟩ : syracuseStep 2427473 = 1820605) B1820605
theorem B2427491 : Blo 1617007 2427491 := bstep (se 1 (by rfl) ⟨1820618, by rfl⟩ : syracuseStep 2427491 = 3641237) B3641237
theorem B2730611 : Blo 1617007 2730611 := bstep (se 1 (by rfl) ⟨2047958, by rfl⟩ : syracuseStep 2730611 = 4095917) B4095917
theorem B2427521 : Blo 1617007 2427521 := bstep (se 2 (by rfl) ⟨910320, by rfl⟩ : syracuseStep 2427521 = 1820641) B1820641
theorem B2427539 : Blo 1617007 2427539 := bstep (se 1 (by rfl) ⟨1820654, by rfl⟩ : syracuseStep 2427539 = 3641309) B3641309
theorem B2427569 : Blo 1617007 2427569 := bstep (se 2 (by rfl) ⟨910338, by rfl⟩ : syracuseStep 2427569 = 1820677) B1820677
theorem B2427587 : Blo 1617007 2427587 := bstep (se 1 (by rfl) ⟨1820690, by rfl⟩ : syracuseStep 2427587 = 3641381) B3641381
theorem B1821379 : Blo 1617007 1821379 := bstep (se 1 (by rfl) ⟨1366034, by rfl⟩ : syracuseStep 1821379 = 2732069) B2732069
theorem B2427617 : Blo 1617007 2427617 := bstep (se 2 (by rfl) ⟨910356, by rfl⟩ : syracuseStep 2427617 = 1820713) B1820713
theorem B3640049 : Blo 1617007 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B2730739 : Blo 1617007 2730739 := bstep (se 1 (by rfl) ⟨2048054, by rfl⟩ : syracuseStep 2730739 = 4096109) B4096109
theorem B2427635 : Blo 1617007 2427635 := bstep (se 1 (by rfl) ⟨1820726, by rfl⟩ : syracuseStep 2427635 = 3641453) B3641453
theorem B3640067 : Blo 1617007 3640067 := bstep (se 1 (by rfl) ⟨2730050, by rfl⟩ : syracuseStep 3640067 = 5460101) B5460101
theorem B4606733 : Blo 1617007 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B2427665 : Blo 1617007 2427665 := bstep (se 2 (by rfl) ⟨910374, by rfl⟩ : syracuseStep 2427665 = 1820749) B1820749
theorem B2427683 : Blo 1617007 2427683 := bstep (se 1 (by rfl) ⟨1820762, by rfl⟩ : syracuseStep 2427683 = 3641525) B3641525
theorem B2427713 : Blo 1617007 2427713 := bstep (se 2 (by rfl) ⟨910392, by rfl⟩ : syracuseStep 2427713 = 1820785) B1820785
theorem B2427731 : Blo 1617007 2427731 := bstep (se 1 (by rfl) ⟨1820798, by rfl⟩ : syracuseStep 2427731 = 3641597) B3641597
theorem B2304865 : Blo 1617007 2304865 := bstep (se 2 (by rfl) ⟨864324, by rfl⟩ : syracuseStep 2304865 = 1728649) B1728649
theorem B8096611 : Blo 1617007 8096611 := bstep (se 1 (by rfl) ⟨6072458, by rfl⟩ : syracuseStep 8096611 = 12144917) B12144917
theorem B5180269 : Blo 1617007 5180269 := bstep (se 3 (by rfl) ⟨971300, by rfl⟩ : syracuseStep 5180269 = 1942601) B1942601
theorem B2427761 : Blo 1617007 2427761 := bstep (se 2 (by rfl) ⟨910410, by rfl⟩ : syracuseStep 2427761 = 1820821) B1820821
theorem B2730881 : Blo 1617007 2730881 := bstep (se 2 (by rfl) ⟨1024080, by rfl⟩ : syracuseStep 2730881 = 2048161) B2048161
theorem B2427779 : Blo 1617007 2427779 := bstep (se 1 (by rfl) ⟨1820834, by rfl⟩ : syracuseStep 2427779 = 3641669) B3641669
theorem B2427809 : Blo 1617007 2427809 := bstep (se 2 (by rfl) ⟨910428, by rfl⟩ : syracuseStep 2427809 = 1820857) B1820857
theorem B2427827 : Blo 1617007 2427827 := bstep (se 1 (by rfl) ⟨1820870, by rfl⟩ : syracuseStep 2427827 = 3641741) B3641741
theorem B2427857 : Blo 1617007 2427857 := bstep (se 2 (by rfl) ⟨910446, by rfl⟩ : syracuseStep 2427857 = 1820893) B1820893
theorem B2427875 : Blo 1617007 2427875 := bstep (se 1 (by rfl) ⟨1820906, by rfl⟩ : syracuseStep 2427875 = 3641813) B3641813
theorem B11668465 : Blo 1617007 11668465 := bstep (se 2 (by rfl) ⟨4375674, by rfl⟩ : syracuseStep 11668465 = 8751349) B8751349
theorem B2731009 : Blo 1617007 2731009 := bstep (se 2 (by rfl) ⟨1024128, by rfl⟩ : syracuseStep 2731009 = 2048257) B2048257
theorem B2427905 : Blo 1617007 2427905 := bstep (se 2 (by rfl) ⟨910464, by rfl⟩ : syracuseStep 2427905 = 1820929) B1820929
theorem B3640337 : Blo 1617007 3640337 := bstep (se 2 (by rfl) ⟨1365126, by rfl⟩ : syracuseStep 3640337 = 2730253) B2730253
theorem B2427923 : Blo 1617007 2427923 := bstep (se 1 (by rfl) ⟨1820942, by rfl⟩ : syracuseStep 2427923 = 3641885) B3641885
theorem B3640355 : Blo 1617007 3640355 := bstep (se 1 (by rfl) ⟨2730266, by rfl⟩ : syracuseStep 3640355 = 5460533) B5460533
theorem B2731043 : Blo 1617007 2731043 := bstep (se 1 (by rfl) ⟨2048282, by rfl⟩ : syracuseStep 2731043 = 4096565) B4096565
theorem B2427953 : Blo 1617007 2427953 := bstep (se 2 (by rfl) ⟨910482, by rfl⟩ : syracuseStep 2427953 = 1820965) B1820965
theorem B2427971 : Blo 1617007 2427971 := bstep (se 1 (by rfl) ⟨1820978, by rfl⟩ : syracuseStep 2427971 = 3641957) B3641957
theorem B5459021 : Blo 1617007 5459021 := bstep (se 3 (by rfl) ⟨1023566, by rfl⟩ : syracuseStep 5459021 = 2047133) B2047133
theorem B2428001 : Blo 1617007 2428001 := bstep (se 2 (by rfl) ⟨910500, by rfl⟩ : syracuseStep 2428001 = 1821001) B1821001
theorem B5180525 : Blo 1617007 5180525 := bstep (se 3 (by rfl) ⟨971348, by rfl⟩ : syracuseStep 5180525 = 1942697) B1942697
theorem B8186993 : Blo 1617007 8186993 := bstep (se 2 (by rfl) ⟨3070122, by rfl⟩ : syracuseStep 8186993 = 6140245) B6140245
theorem B13126769 : Blo 1617007 13126769 := bstep (se 2 (by rfl) ⟨4922538, by rfl⟩ : syracuseStep 13126769 = 9845077) B9845077
theorem B1617011 : Blo 1617007 1617011 := bstep (se 1 (by rfl) ⟨1212758, by rfl⟩ : syracuseStep 1617011 = 2425517) B2425517
theorem B2428019 : Blo 1617007 2428019 := bstep (se 1 (by rfl) ⟨1821014, by rfl⟩ : syracuseStep 2428019 = 3642029) B3642029
theorem B1617027 : Blo 1617007 1617027 := bstep (se 1 (by rfl) ⟨1212770, by rfl⟩ : syracuseStep 1617027 = 2425541) B2425541
theorem B5459075 : Blo 1617007 5459075 := bstep (se 1 (by rfl) ⟨4094306, by rfl⟩ : syracuseStep 5459075 = 8188613) B8188613
theorem B1617043 : Blo 1617007 1617043 := bstep (se 1 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 1617043 = 2425565) B2425565
theorem B2428049 : Blo 1617007 2428049 := bstep (se 2 (by rfl) ⟨910518, by rfl⟩ : syracuseStep 2428049 = 1821037) B1821037
theorem B1617059 : Blo 1617007 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B2731171 : Blo 1617007 2731171 := bstep (se 1 (by rfl) ⟨2048378, by rfl⟩ : syracuseStep 2731171 = 4096757) B4096757
theorem B2428067 : Blo 1617007 2428067 := bstep (se 1 (by rfl) ⟨1821050, by rfl⟩ : syracuseStep 2428067 = 3642101) B3642101
theorem B1617075 : Blo 1617007 1617075 := bstep (se 1 (by rfl) ⟨1212806, by rfl⟩ : syracuseStep 1617075 = 2425613) B2425613
theorem B2428097 : Blo 1617007 2428097 := bstep (se 2 (by rfl) ⟨910536, by rfl⟩ : syracuseStep 2428097 = 1821073) B1821073
theorem B1617091 : Blo 1617007 1617091 := bstep (se 1 (by rfl) ⟨1212818, by rfl⟩ : syracuseStep 1617091 = 2425637) B2425637
theorem B1617107 : Blo 1617007 1617107 := bstep (se 1 (by rfl) ⟨1212830, by rfl⟩ : syracuseStep 1617107 = 2425661) B2425661
theorem B2428115 : Blo 1617007 2428115 := bstep (se 1 (by rfl) ⟨1821086, by rfl⟩ : syracuseStep 2428115 = 3642173) B3642173
theorem B1617123 : Blo 1617007 1617123 := bstep (se 1 (by rfl) ⟨1212842, by rfl⟩ : syracuseStep 1617123 = 2425685) B2425685
theorem B2428145 : Blo 1617007 2428145 := bstep (se 2 (by rfl) ⟨910554, by rfl⟩ : syracuseStep 2428145 = 1821109) B1821109
theorem B1617139 : Blo 1617007 1617139 := bstep (se 1 (by rfl) ⟨1212854, by rfl⟩ : syracuseStep 1617139 = 2425709) B2425709
theorem B1617155 : Blo 1617007 1617155 := bstep (se 1 (by rfl) ⟨1212866, by rfl⟩ : syracuseStep 1617155 = 2425733) B2425733
theorem B2428163 : Blo 1617007 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B1617171 : Blo 1617007 1617171 := bstep (se 1 (by rfl) ⟨1212878, by rfl⟩ : syracuseStep 1617171 = 2425757) B2425757
theorem B2428193 : Blo 1617007 2428193 := bstep (se 2 (by rfl) ⟨910572, by rfl⟩ : syracuseStep 2428193 = 1821145) B1821145
theorem B1617187 : Blo 1617007 1617187 := bstep (se 1 (by rfl) ⟨1212890, by rfl⟩ : syracuseStep 1617187 = 2425781) B2425781
theorem B3640625 : Blo 1617007 3640625 := bstep (se 2 (by rfl) ⟨1365234, by rfl⟩ : syracuseStep 3640625 = 2730469) B2730469
theorem B2731313 : Blo 1617007 2731313 := bstep (se 2 (by rfl) ⟨1024242, by rfl⟩ : syracuseStep 2731313 = 2048485) B2048485
theorem B1617203 : Blo 1617007 1617203 := bstep (se 1 (by rfl) ⟨1212902, by rfl⟩ : syracuseStep 1617203 = 2425805) B2425805
theorem B2428211 : Blo 1617007 2428211 := bstep (se 1 (by rfl) ⟨1821158, by rfl⟩ : syracuseStep 2428211 = 3642317) B3642317
theorem B1617219 : Blo 1617007 1617219 := bstep (se 1 (by rfl) ⟨1212914, by rfl⟩ : syracuseStep 1617219 = 2425829) B2425829
theorem B3640643 : Blo 1617007 3640643 := bstep (se 1 (by rfl) ⟨2730482, by rfl⟩ : syracuseStep 3640643 = 5460965) B5460965
theorem B2428241 : Blo 1617007 2428241 := bstep (se 2 (by rfl) ⟨910590, by rfl⟩ : syracuseStep 2428241 = 1821181) B1821181
theorem B1617235 : Blo 1617007 1617235 := bstep (se 1 (by rfl) ⟨1212926, by rfl⟩ : syracuseStep 1617235 = 2425853) B2425853
theorem B2592083 : Blo 1617007 2592083 := bstep (se 1 (by rfl) ⟨1944062, by rfl⟩ : syracuseStep 2592083 = 3888125) B3888125
theorem B1617251 : Blo 1617007 1617251 := bstep (se 1 (by rfl) ⟨1212938, by rfl⟩ : syracuseStep 1617251 = 2425877) B2425877
theorem B2428259 : Blo 1617007 2428259 := bstep (se 1 (by rfl) ⟨1821194, by rfl⟩ : syracuseStep 2428259 = 3642389) B3642389
theorem B1617267 : Blo 1617007 1617267 := bstep (se 1 (by rfl) ⟨1212950, by rfl⟩ : syracuseStep 1617267 = 2425901) B2425901
theorem B2428289 : Blo 1617007 2428289 := bstep (se 2 (by rfl) ⟨910608, by rfl⟩ : syracuseStep 2428289 = 1821217) B1821217
theorem B1617283 : Blo 1617007 1617283 := bstep (se 1 (by rfl) ⟨1212962, by rfl⟩ : syracuseStep 1617283 = 2425925) B2425925
theorem B5533069 : Blo 1617007 5533069 := bstep (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) B2074901
theorem B5459345 : Blo 1617007 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1617299 : Blo 1617007 1617299 := bstep (se 1 (by rfl) ⟨1212974, by rfl⟩ : syracuseStep 1617299 = 2425949) B2425949
theorem B2428307 : Blo 1617007 2428307 := bstep (se 1 (by rfl) ⟨1821230, by rfl⟩ : syracuseStep 2428307 = 3642461) B3642461
theorem B1617315 : Blo 1617007 1617315 := bstep (se 1 (by rfl) ⟨1212986, by rfl⟩ : syracuseStep 1617315 = 2425973) B2425973
theorem B2731441 : Blo 1617007 2731441 := bstep (se 2 (by rfl) ⟨1024290, by rfl⟩ : syracuseStep 2731441 = 2048581) B2048581
theorem B2428337 : Blo 1617007 2428337 := bstep (se 2 (by rfl) ⟨910626, by rfl⟩ : syracuseStep 2428337 = 1821253) B1821253
theorem B1617331 : Blo 1617007 1617331 := bstep (se 1 (by rfl) ⟨1212998, by rfl⟩ : syracuseStep 1617331 = 2425997) B2425997
theorem B1617347 : Blo 1617007 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B2428355 : Blo 1617007 2428355 := bstep (se 1 (by rfl) ⟨1821266, by rfl⟩ : syracuseStep 2428355 = 3642533) B3642533
theorem B1617363 : Blo 1617007 1617363 := bstep (se 1 (by rfl) ⟨1213022, by rfl⟩ : syracuseStep 1617363 = 2426045) B2426045
theorem B2731475 : Blo 1617007 2731475 := bstep (se 1 (by rfl) ⟨2048606, by rfl⟩ : syracuseStep 2731475 = 4097213) B4097213
theorem B2428385 : Blo 1617007 2428385 := bstep (se 2 (by rfl) ⟨910644, by rfl⟩ : syracuseStep 2428385 = 1821289) B1821289
theorem B1617379 : Blo 1617007 1617379 := bstep (se 1 (by rfl) ⟨1213034, by rfl⟩ : syracuseStep 1617379 = 2426069) B2426069
theorem B4918769 : Blo 1617007 4918769 := bstep (se 2 (by rfl) ⟨1844538, by rfl⟩ : syracuseStep 4918769 = 3689077) B3689077
theorem B4435441 : Blo 1617007 4435441 := bstep (se 2 (by rfl) ⟨1663290, by rfl⟩ : syracuseStep 4435441 = 3326581) B3326581
theorem B1617395 : Blo 1617007 1617395 := bstep (se 1 (by rfl) ⟨1213046, by rfl⟩ : syracuseStep 1617395 = 2426093) B2426093
theorem B2428403 : Blo 1617007 2428403 := bstep (se 1 (by rfl) ⟨1821302, by rfl⟩ : syracuseStep 2428403 = 3642605) B3642605
theorem B1617411 : Blo 1617007 1617411 := bstep (se 1 (by rfl) ⟨1213058, by rfl⟩ : syracuseStep 1617411 = 2426117) B2426117
theorem B2428433 : Blo 1617007 2428433 := bstep (se 2 (by rfl) ⟨910662, by rfl⟩ : syracuseStep 2428433 = 1821325) B1821325
theorem B1617427 : Blo 1617007 1617427 := bstep (se 1 (by rfl) ⟨1213070, by rfl⟩ : syracuseStep 1617427 = 2426141) B2426141
theorem B1617443 : Blo 1617007 1617443 := bstep (se 1 (by rfl) ⟨1213082, by rfl⟩ : syracuseStep 1617443 = 2426165) B2426165
theorem B2428451 : Blo 1617007 2428451 := bstep (se 1 (by rfl) ⟨1821338, by rfl⟩ : syracuseStep 2428451 = 3642677) B3642677
theorem B1617459 : Blo 1617007 1617459 := bstep (se 1 (by rfl) ⟨1213094, by rfl⟩ : syracuseStep 1617459 = 2426189) B2426189
theorem B1617475 : Blo 1617007 1617475 := bstep (se 1 (by rfl) ⟨1213106, by rfl⟩ : syracuseStep 1617475 = 2426213) B2426213
theorem B2428481 : Blo 1617007 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B3640913 : Blo 1617007 3640913 := bstep (se 2 (by rfl) ⟨1365342, by rfl⟩ : syracuseStep 3640913 = 2730685) B2730685
theorem B1617491 : Blo 1617007 1617491 := bstep (se 1 (by rfl) ⟨1213118, by rfl⟩ : syracuseStep 1617491 = 2426237) B2426237
theorem B2731603 : Blo 1617007 2731603 := bstep (se 1 (by rfl) ⟨2048702, by rfl⟩ : syracuseStep 2731603 = 4097405) B4097405
theorem B2428499 : Blo 1617007 2428499 := bstep (se 1 (by rfl) ⟨1821374, by rfl⟩ : syracuseStep 2428499 = 3642749) B3642749
theorem B1617507 : Blo 1617007 1617507 := bstep (se 1 (by rfl) ⟨1213130, by rfl⟩ : syracuseStep 1617507 = 2426261) B2426261
theorem B3640931 : Blo 1617007 3640931 := bstep (se 1 (by rfl) ⟨2730698, by rfl⟩ : syracuseStep 3640931 = 5461397) B5461397
theorem B6909553 : Blo 1617007 6909553 := bstep (se 2 (by rfl) ⟨2591082, by rfl⟩ : syracuseStep 6909553 = 5182165) B5182165
theorem B1617523 : Blo 1617007 1617523 := bstep (se 1 (by rfl) ⟨1213142, by rfl⟩ : syracuseStep 1617523 = 2426285) B2426285
theorem B1617539 : Blo 1617007 1617539 := bstep (se 1 (by rfl) ⟨1213154, by rfl⟩ : syracuseStep 1617539 = 2426309) B2426309
theorem B5828237 : Blo 1617007 5828237 := bstep (se 3 (by rfl) ⟨1092794, by rfl⟩ : syracuseStep 5828237 = 2185589) B2185589
theorem B1617555 : Blo 1617007 1617555 := bstep (se 1 (by rfl) ⟨1213166, by rfl⟩ : syracuseStep 1617555 = 2426333) B2426333
theorem B1617571 : Blo 1617007 1617571 := bstep (se 1 (by rfl) ⟨1213178, by rfl⟩ : syracuseStep 1617571 = 2426357) B2426357
theorem B1617587 : Blo 1617007 1617587 := bstep (se 1 (by rfl) ⟨1213190, by rfl⟩ : syracuseStep 1617587 = 2426381) B2426381
theorem B1617603 : Blo 1617007 1617603 := bstep (se 1 (by rfl) ⟨1213202, by rfl⟩ : syracuseStep 1617603 = 2426405) B2426405
theorem B1617619 : Blo 1617007 1617619 := bstep (se 1 (by rfl) ⟨1213214, by rfl⟩ : syracuseStep 1617619 = 2426429) B2426429
theorem B2592467 : Blo 1617007 2592467 := bstep (se 1 (by rfl) ⟨1944350, by rfl⟩ : syracuseStep 2592467 = 3888701) B3888701
theorem B1617635 : Blo 1617007 1617635 := bstep (se 1 (by rfl) ⟨1213226, by rfl⟩ : syracuseStep 1617635 = 2426453) B2426453
theorem B2731745 : Blo 1617007 2731745 := bstep (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) B2048809
theorem B4607725 : Blo 1617007 4607725 := bstep (se 3 (by rfl) ⟨863948, by rfl⟩ : syracuseStep 4607725 = 1727897) B1727897
theorem B1617651 : Blo 1617007 1617651 := bstep (se 1 (by rfl) ⟨1213238, by rfl⟩ : syracuseStep 1617651 = 2426477) B2426477
theorem B1617667 : Blo 1617007 1617667 := bstep (se 1 (by rfl) ⟨1213250, by rfl⟩ : syracuseStep 1617667 = 2426501) B2426501
theorem B9219845 : Blo 1617007 9219845 := bstep (se 4 (by rfl) ⟨864360, by rfl⟩ : syracuseStep 9219845 = 1728721) B1728721
theorem B18427661 : Blo 1617007 18427661 := bstep (se 3 (by rfl) ⟨3455186, by rfl⟩ : syracuseStep 18427661 = 6910373) B6910373
theorem B13119245 : Blo 1617007 13119245 := bstep (se 3 (by rfl) ⟨2459858, by rfl⟩ : syracuseStep 13119245 = 4919717) B4919717
theorem B1617683 : Blo 1617007 1617683 := bstep (se 1 (by rfl) ⟨1213262, by rfl⟩ : syracuseStep 1617683 = 2426525) B2426525
theorem B1617699 : Blo 1617007 1617699 := bstep (se 1 (by rfl) ⟨1213274, by rfl⟩ : syracuseStep 1617699 = 2426549) B2426549
theorem B1617715 : Blo 1617007 1617715 := bstep (se 1 (by rfl) ⟨1213286, by rfl⟩ : syracuseStep 1617715 = 2426573) B2426573
theorem B1617731 : Blo 1617007 1617731 := bstep (se 1 (by rfl) ⟨1213298, by rfl⟩ : syracuseStep 1617731 = 2426597) B2426597
theorem B1617747 : Blo 1617007 1617747 := bstep (se 1 (by rfl) ⟨1213310, by rfl⟩ : syracuseStep 1617747 = 2426621) B2426621
theorem B2592595 : Blo 1617007 2592595 := bstep (se 1 (by rfl) ⟨1944446, by rfl⟩ : syracuseStep 2592595 = 3888893) B3888893
theorem B2731873 : Blo 1617007 2731873 := bstep (se 2 (by rfl) ⟨1024452, by rfl⟩ : syracuseStep 2731873 = 2048905) B2048905
theorem B1617763 : Blo 1617007 1617763 := bstep (se 1 (by rfl) ⟨1213322, by rfl⟩ : syracuseStep 1617763 = 2426645) B2426645
theorem B3641201 : Blo 1617007 3641201 := bstep (se 2 (by rfl) ⟨1365450, by rfl⟩ : syracuseStep 3641201 = 2730901) B2730901
theorem B1617779 : Blo 1617007 1617779 := bstep (se 1 (by rfl) ⟨1213334, by rfl⟩ : syracuseStep 1617779 = 2426669) B2426669
theorem B1617795 : Blo 1617007 1617795 := bstep (se 1 (by rfl) ⟨1213346, by rfl⟩ : syracuseStep 1617795 = 2426693) B2426693
theorem B3641219 : Blo 1617007 3641219 := bstep (se 1 (by rfl) ⟨2730914, by rfl⟩ : syracuseStep 3641219 = 5461829) B5461829
theorem B2731907 : Blo 1617007 2731907 := bstep (se 1 (by rfl) ⟨2048930, by rfl⟩ : syracuseStep 2731907 = 4097861) B4097861
theorem B1617811 : Blo 1617007 1617811 := bstep (se 1 (by rfl) ⟨1213358, by rfl⟩ : syracuseStep 1617811 = 2426717) B2426717
theorem B4919203 : Blo 1617007 4919203 := bstep (se 1 (by rfl) ⟨3689402, by rfl⟩ : syracuseStep 4919203 = 7378805) B7378805
theorem B1617827 : Blo 1617007 1617827 := bstep (se 1 (by rfl) ⟨1213370, by rfl⟩ : syracuseStep 1617827 = 2426741) B2426741
theorem B5459885 : Blo 1617007 5459885 := bstep (se 3 (by rfl) ⟨1023728, by rfl⟩ : syracuseStep 5459885 = 2047457) B2047457
theorem B1617843 : Blo 1617007 1617843 := bstep (se 1 (by rfl) ⟨1213382, by rfl⟩ : syracuseStep 1617843 = 2426765) B2426765
theorem B1617859 : Blo 1617007 1617859 := bstep (se 1 (by rfl) ⟨1213394, by rfl⟩ : syracuseStep 1617859 = 2426789) B2426789
theorem B1617875 : Blo 1617007 1617875 := bstep (se 1 (by rfl) ⟨1213406, by rfl⟩ : syracuseStep 1617875 = 2426813) B2426813
theorem B5459939 : Blo 1617007 5459939 := bstep (se 1 (by rfl) ⟨4094954, by rfl⟩ : syracuseStep 5459939 = 8189909) B8189909
theorem B1617891 : Blo 1617007 1617891 := bstep (se 1 (by rfl) ⟨1213418, by rfl⟩ : syracuseStep 1617891 = 2426837) B2426837
theorem B1617907 : Blo 1617007 1617907 := bstep (se 1 (by rfl) ⟨1213430, by rfl⟩ : syracuseStep 1617907 = 2426861) B2426861
theorem B1617923 : Blo 1617007 1617923 := bstep (se 1 (by rfl) ⟨1213442, by rfl⟩ : syracuseStep 1617923 = 2426885) B2426885
theorem B2732035 : Blo 1617007 2732035 := bstep (se 1 (by rfl) ⟨2049026, by rfl⟩ : syracuseStep 2732035 = 4098053) B4098053
theorem B1617939 : Blo 1617007 1617939 := bstep (se 1 (by rfl) ⟨1213454, by rfl⟩ : syracuseStep 1617939 = 2426909) B2426909
theorem B1617955 : Blo 1617007 1617955 := bstep (se 1 (by rfl) ⟨1213466, by rfl⟩ : syracuseStep 1617955 = 2426933) B2426933
theorem B1617971 : Blo 1617007 1617971 := bstep (se 1 (by rfl) ⟨1213478, by rfl⟩ : syracuseStep 1617971 = 2426957) B2426957
theorem B29503541 : Blo 1617007 29503541 := bstep (se 5 (by rfl) ⟨1382978, by rfl⟩ : syracuseStep 29503541 = 2765957) B2765957
theorem B1617987 : Blo 1617007 1617987 := bstep (se 1 (by rfl) ⟨1213490, by rfl⟩ : syracuseStep 1617987 = 2426981) B2426981
theorem B1618003 : Blo 1617007 1618003 := bstep (se 1 (by rfl) ⟨1213502, by rfl⟩ : syracuseStep 1618003 = 2427005) B2427005
theorem B1618019 : Blo 1617007 1618019 := bstep (se 1 (by rfl) ⟨1213514, by rfl⟩ : syracuseStep 1618019 = 2427029) B2427029
theorem B1618035 : Blo 1617007 1618035 := bstep (se 1 (by rfl) ⟨1213526, by rfl⟩ : syracuseStep 1618035 = 2427053) B2427053
theorem B1618051 : Blo 1617007 1618051 := bstep (se 1 (by rfl) ⟨1213538, by rfl⟩ : syracuseStep 1618051 = 2427077) B2427077
theorem B3641489 : Blo 1617007 3641489 := bstep (se 2 (by rfl) ⟨1365558, by rfl⟩ : syracuseStep 3641489 = 2731117) B2731117
theorem B1618067 : Blo 1617007 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B1618083 : Blo 1617007 1618083 := bstep (se 1 (by rfl) ⟨1213562, by rfl⟩ : syracuseStep 1618083 = 2427125) B2427125
theorem B3641507 : Blo 1617007 3641507 := bstep (se 1 (by rfl) ⟨2731130, by rfl⟩ : syracuseStep 3641507 = 5462261) B5462261
theorem B1618099 : Blo 1617007 1618099 := bstep (se 1 (by rfl) ⟨1213574, by rfl⟩ : syracuseStep 1618099 = 2427149) B2427149
theorem B1618115 : Blo 1617007 1618115 := bstep (se 1 (by rfl) ⟨1213586, by rfl⟩ : syracuseStep 1618115 = 2427173) B2427173
theorem B9220301 : Blo 1617007 9220301 := bstep (se 3 (by rfl) ⟨1728806, by rfl⟩ : syracuseStep 9220301 = 3457613) B3457613
theorem B1618131 : Blo 1617007 1618131 := bstep (se 1 (by rfl) ⟨1213598, by rfl⟩ : syracuseStep 1618131 = 2427197) B2427197
theorem B1618147 : Blo 1617007 1618147 := bstep (se 1 (by rfl) ⟨1213610, by rfl⟩ : syracuseStep 1618147 = 2427221) B2427221
theorem B5460209 : Blo 1617007 5460209 := bstep (se 2 (by rfl) ⟨2047578, by rfl⟩ : syracuseStep 5460209 = 4095157) B4095157
theorem B1618163 : Blo 1617007 1618163 := bstep (se 1 (by rfl) ⟨1213622, by rfl⟩ : syracuseStep 1618163 = 2427245) B2427245
theorem B1618179 : Blo 1617007 1618179 := bstep (se 1 (by rfl) ⟨1213634, by rfl⟩ : syracuseStep 1618179 = 2427269) B2427269
theorem B13824269 : Blo 1617007 13824269 := bstep (se 3 (by rfl) ⟨2592050, by rfl⟩ : syracuseStep 13824269 = 5184101) B5184101
theorem B1618195 : Blo 1617007 1618195 := bstep (se 1 (by rfl) ⟨1213646, by rfl⟩ : syracuseStep 1618195 = 2427293) B2427293
theorem B1618211 : Blo 1617007 1618211 := bstep (se 1 (by rfl) ⟨1213658, by rfl⟩ : syracuseStep 1618211 = 2427317) B2427317
theorem B1618227 : Blo 1617007 1618227 := bstep (se 1 (by rfl) ⟨1213670, by rfl⟩ : syracuseStep 1618227 = 2427341) B2427341
theorem B1618243 : Blo 1617007 1618243 := bstep (se 1 (by rfl) ⟨1213682, by rfl⟩ : syracuseStep 1618243 = 2427365) B2427365
theorem B9212237 : Blo 1617007 9212237 := bstep (se 3 (by rfl) ⟨1727294, by rfl⟩ : syracuseStep 9212237 = 3454589) B3454589
theorem B1618259 : Blo 1617007 1618259 := bstep (se 1 (by rfl) ⟨1213694, by rfl⟩ : syracuseStep 1618259 = 2427389) B2427389
theorem B1618275 : Blo 1617007 1618275 := bstep (se 1 (by rfl) ⟨1213706, by rfl⟩ : syracuseStep 1618275 = 2427413) B2427413
theorem B1618291 : Blo 1617007 1618291 := bstep (se 1 (by rfl) ⟨1213718, by rfl⟩ : syracuseStep 1618291 = 2427437) B2427437
theorem B1618307 : Blo 1617007 1618307 := bstep (se 1 (by rfl) ⟨1213730, by rfl⟩ : syracuseStep 1618307 = 2427461) B2427461
theorem B1618323 : Blo 1617007 1618323 := bstep (se 1 (by rfl) ⟨1213742, by rfl⟩ : syracuseStep 1618323 = 2427485) B2427485
theorem B1618339 : Blo 1617007 1618339 := bstep (se 1 (by rfl) ⟨1213754, by rfl⟩ : syracuseStep 1618339 = 2427509) B2427509
theorem B3641777 : Blo 1617007 3641777 := bstep (se 2 (by rfl) ⟨1365666, by rfl⟩ : syracuseStep 3641777 = 2731333) B2731333
theorem B1618355 : Blo 1617007 1618355 := bstep (se 1 (by rfl) ⟨1213766, by rfl⟩ : syracuseStep 1618355 = 2427533) B2427533
theorem B1618371 : Blo 1617007 1618371 := bstep (se 1 (by rfl) ⟨1213778, by rfl⟩ : syracuseStep 1618371 = 2427557) B2427557
theorem B3641795 : Blo 1617007 3641795 := bstep (se 1 (by rfl) ⟨2731346, by rfl⟩ : syracuseStep 3641795 = 5462693) B5462693
theorem B20738501 : Blo 1617007 20738501 := bstep (se 4 (by rfl) ⟨1944234, by rfl⟩ : syracuseStep 20738501 = 3888469) B3888469
theorem B1618387 : Blo 1617007 1618387 := bstep (se 1 (by rfl) ⟨1213790, by rfl⟩ : syracuseStep 1618387 = 2427581) B2427581
theorem B10367459 : Blo 1617007 10367459 := bstep (se 1 (by rfl) ⟨7775594, by rfl⟩ : syracuseStep 10367459 = 15551189) B15551189
theorem B1618403 : Blo 1617007 1618403 := bstep (se 1 (by rfl) ⟨1213802, by rfl⟩ : syracuseStep 1618403 = 2427605) B2427605
theorem B7877105 : Blo 1617007 7877105 := bstep (se 2 (by rfl) ⟨2953914, by rfl⟩ : syracuseStep 7877105 = 5907829) B5907829
theorem B1618419 : Blo 1617007 1618419 := bstep (se 1 (by rfl) ⟨1213814, by rfl⟩ : syracuseStep 1618419 = 2427629) B2427629
theorem B1618435 : Blo 1617007 1618435 := bstep (se 1 (by rfl) ⟨1213826, by rfl⟩ : syracuseStep 1618435 = 2427653) B2427653
theorem B1618451 : Blo 1617007 1618451 := bstep (se 1 (by rfl) ⟨1213838, by rfl⟩ : syracuseStep 1618451 = 2427677) B2427677
theorem B2593313 : Blo 1617007 2593313 := bstep (se 2 (by rfl) ⟨972492, by rfl⟩ : syracuseStep 2593313 = 1944985) B1944985
theorem B8188451 : Blo 1617007 8188451 := bstep (se 1 (by rfl) ⟨6141338, by rfl⟩ : syracuseStep 8188451 = 12282677) B12282677
theorem B1618467 : Blo 1617007 1618467 := bstep (se 1 (by rfl) ⟨1213850, by rfl⟩ : syracuseStep 1618467 = 2427701) B2427701
theorem B1618483 : Blo 1617007 1618483 := bstep (se 1 (by rfl) ⟨1213862, by rfl⟩ : syracuseStep 1618483 = 2427725) B2427725
theorem B1618499 : Blo 1617007 1618499 := bstep (se 1 (by rfl) ⟨1213874, by rfl⟩ : syracuseStep 1618499 = 2427749) B2427749
theorem B1618515 : Blo 1617007 1618515 := bstep (se 1 (by rfl) ⟨1213886, by rfl⟩ : syracuseStep 1618515 = 2427773) B2427773
theorem B5182051 : Blo 1617007 5182051 := bstep (se 1 (by rfl) ⟨3886538, by rfl⟩ : syracuseStep 5182051 = 7773077) B7773077
theorem B1618531 : Blo 1617007 1618531 := bstep (se 1 (by rfl) ⟨1213898, by rfl⟩ : syracuseStep 1618531 = 2427797) B2427797
theorem B1618547 : Blo 1617007 1618547 := bstep (se 1 (by rfl) ⟨1213910, by rfl⟩ : syracuseStep 1618547 = 2427821) B2427821
theorem B1618563 : Blo 1617007 1618563 := bstep (se 1 (by rfl) ⟨1213922, by rfl⟩ : syracuseStep 1618563 = 2427845) B2427845
theorem B1618579 : Blo 1617007 1618579 := bstep (se 1 (by rfl) ⟨1213934, by rfl⟩ : syracuseStep 1618579 = 2427869) B2427869
theorem B1618595 : Blo 1617007 1618595 := bstep (se 1 (by rfl) ⟨1213946, by rfl⟩ : syracuseStep 1618595 = 2427893) B2427893
theorem B1618611 : Blo 1617007 1618611 := bstep (se 1 (by rfl) ⟨1213958, by rfl⟩ : syracuseStep 1618611 = 2427917) B2427917
theorem B1618627 : Blo 1617007 1618627 := bstep (se 1 (by rfl) ⟨1213970, by rfl⟩ : syracuseStep 1618627 = 2427941) B2427941
theorem B3642065 : Blo 1617007 3642065 := bstep (se 2 (by rfl) ⟨1365774, by rfl⟩ : syracuseStep 3642065 = 2731549) B2731549
theorem B1618643 : Blo 1617007 1618643 := bstep (se 1 (by rfl) ⟨1213982, by rfl⟩ : syracuseStep 1618643 = 2427965) B2427965
theorem B5829347 : Blo 1617007 5829347 := bstep (se 1 (by rfl) ⟨4372010, by rfl⟩ : syracuseStep 5829347 = 8744021) B8744021
theorem B1618659 : Blo 1617007 1618659 := bstep (se 1 (by rfl) ⟨1213994, by rfl⟩ : syracuseStep 1618659 = 2427989) B2427989
theorem B3642083 : Blo 1617007 3642083 := bstep (se 1 (by rfl) ⟨2731562, by rfl⟩ : syracuseStep 3642083 = 5463125) B5463125
theorem B1618675 : Blo 1617007 1618675 := bstep (se 1 (by rfl) ⟨1214006, by rfl⟩ : syracuseStep 1618675 = 2428013) B2428013
theorem B1618691 : Blo 1617007 1618691 := bstep (se 1 (by rfl) ⟨1214018, by rfl⟩ : syracuseStep 1618691 = 2428037) B2428037
theorem B5460749 : Blo 1617007 5460749 := bstep (se 3 (by rfl) ⟨1023890, by rfl⟩ : syracuseStep 5460749 = 2047781) B2047781
theorem B1618707 : Blo 1617007 1618707 := bstep (se 1 (by rfl) ⟨1214030, by rfl⟩ : syracuseStep 1618707 = 2428061) B2428061
theorem B8885027 : Blo 1617007 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B1618723 : Blo 1617007 1618723 := bstep (se 1 (by rfl) ⟨1214042, by rfl⟩ : syracuseStep 1618723 = 2428085) B2428085
theorem B1618739 : Blo 1617007 1618739 := bstep (se 1 (by rfl) ⟨1214054, by rfl⟩ : syracuseStep 1618739 = 2428109) B2428109
theorem B5460803 : Blo 1617007 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B1618755 : Blo 1617007 1618755 := bstep (se 1 (by rfl) ⟨1214066, by rfl⟩ : syracuseStep 1618755 = 2428133) B2428133
theorem B1618771 : Blo 1617007 1618771 := bstep (se 1 (by rfl) ⟨1214078, by rfl⟩ : syracuseStep 1618771 = 2428157) B2428157
theorem B1618787 : Blo 1617007 1618787 := bstep (se 1 (by rfl) ⟨1214090, by rfl⟩ : syracuseStep 1618787 = 2428181) B2428181
theorem B1618803 : Blo 1617007 1618803 := bstep (se 1 (by rfl) ⟨1214102, by rfl⟩ : syracuseStep 1618803 = 2428205) B2428205
theorem B1618819 : Blo 1617007 1618819 := bstep (se 1 (by rfl) ⟨1214114, by rfl⟩ : syracuseStep 1618819 = 2428229) B2428229
theorem B1618835 : Blo 1617007 1618835 := bstep (se 1 (by rfl) ⟨1214126, by rfl⟩ : syracuseStep 1618835 = 2428253) B2428253
theorem B1618851 : Blo 1617007 1618851 := bstep (se 1 (by rfl) ⟨1214138, by rfl⟩ : syracuseStep 1618851 = 2428277) B2428277
theorem B1618867 : Blo 1617007 1618867 := bstep (se 1 (by rfl) ⟨1214150, by rfl⟩ : syracuseStep 1618867 = 2428301) B2428301
theorem B1618883 : Blo 1617007 1618883 := bstep (se 1 (by rfl) ⟨1214162, by rfl⟩ : syracuseStep 1618883 = 2428325) B2428325
theorem B1618899 : Blo 1617007 1618899 := bstep (se 1 (by rfl) ⟨1214174, by rfl⟩ : syracuseStep 1618899 = 2428349) B2428349
theorem B3453923 : Blo 1617007 3453923 := bstep (se 1 (by rfl) ⟨2590442, by rfl⟩ : syracuseStep 3453923 = 5180885) B5180885
theorem B1618915 : Blo 1617007 1618915 := bstep (se 1 (by rfl) ⟨1214186, by rfl⟩ : syracuseStep 1618915 = 2428373) B2428373
theorem B3642353 : Blo 1617007 3642353 := bstep (se 2 (by rfl) ⟨1365882, by rfl⟩ : syracuseStep 3642353 = 2731765) B2731765
theorem B1618931 : Blo 1617007 1618931 := bstep (se 1 (by rfl) ⟨1214198, by rfl⟩ : syracuseStep 1618931 = 2428397) B2428397
theorem B4920323 : Blo 1617007 4920323 := bstep (se 1 (by rfl) ⟨3690242, by rfl⟩ : syracuseStep 4920323 = 7380485) B7380485
theorem B3642371 : Blo 1617007 3642371 := bstep (se 1 (by rfl) ⟨2731778, by rfl⟩ : syracuseStep 3642371 = 5463557) B5463557
theorem B1618947 : Blo 1617007 1618947 := bstep (se 1 (by rfl) ⟨1214210, by rfl⟩ : syracuseStep 1618947 = 2428421) B2428421
theorem B1618963 : Blo 1617007 1618963 := bstep (se 1 (by rfl) ⟨1214222, by rfl⟩ : syracuseStep 1618963 = 2428445) B2428445
theorem B1618979 : Blo 1617007 1618979 := bstep (se 1 (by rfl) ⟨1214234, by rfl⟩ : syracuseStep 1618979 = 2428469) B2428469
theorem B1618995 : Blo 1617007 1618995 := bstep (se 1 (by rfl) ⟨1214246, by rfl⟩ : syracuseStep 1618995 = 2428493) B2428493
theorem B6141005 : Blo 1617007 6141005 := bstep (se 3 (by rfl) ⟨1151438, by rfl⟩ : syracuseStep 6141005 = 2302877) B2302877
theorem B5461073 : Blo 1617007 5461073 := bstep (se 2 (by rfl) ⟨2047902, by rfl⟩ : syracuseStep 5461073 = 4095805) B4095805
theorem B3642641 : Blo 1617007 3642641 := bstep (se 2 (by rfl) ⟨1365990, by rfl⟩ : syracuseStep 3642641 = 2731981) B2731981
theorem B3642659 : Blo 1617007 3642659 := bstep (se 1 (by rfl) ⟨2731994, by rfl⟩ : syracuseStep 3642659 = 5463989) B5463989
theorem B8746289 : Blo 1617007 8746289 := bstep (se 2 (by rfl) ⟨3279858, by rfl⟩ : syracuseStep 8746289 = 6559717) B6559717
theorem B8189261 : Blo 1617007 8189261 := bstep (se 3 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 8189261 = 3070973) B3070973
theorem B5182883 : Blo 1617007 5182883 := bstep (se 1 (by rfl) ⟨3887162, by rfl⟩ : syracuseStep 5182883 = 7774325) B7774325
theorem B4609457 : Blo 1617007 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B2627009 : Blo 1617007 2627009 := bstep (se 2 (by rfl) ⟨985128, by rfl⟩ : syracuseStep 2627009 = 1970257) B1970257
theorem B3454435 : Blo 1617007 3454435 := bstep (se 1 (by rfl) ⟨2590826, by rfl⟩ : syracuseStep 3454435 = 5181653) B5181653
theorem B8304113 : Blo 1617007 8304113 := bstep (se 2 (by rfl) ⟨3114042, by rfl⟩ : syracuseStep 8304113 = 6228085) B6228085
theorem B3503665 : Blo 1617007 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B3888739 : Blo 1617007 3888739 := bstep (se 1 (by rfl) ⟨2916554, by rfl⟩ : syracuseStep 3888739 = 5833109) B5833109
theorem B8869475 : Blo 1617007 8869475 := bstep (se 1 (by rfl) ⟨6652106, by rfl⟩ : syracuseStep 8869475 = 13304213) B13304213
theorem B5461613 : Blo 1617007 5461613 := bstep (se 3 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 5461613 = 2048105) B2048105
theorem B13112945 : Blo 1617007 13112945 := bstep (se 2 (by rfl) ⟨4917354, by rfl⟩ : syracuseStep 13112945 = 9834709) B9834709
theorem B4609649 : Blo 1617007 4609649 := bstep (se 2 (by rfl) ⟨1728618, by rfl⟩ : syracuseStep 4609649 = 3457237) B3457237
theorem B5461667 : Blo 1617007 5461667 := bstep (se 1 (by rfl) ⟨4096250, by rfl⟩ : syracuseStep 5461667 = 8192501) B8192501
theorem B4093649 : Blo 1617007 4093649 := bstep (se 2 (by rfl) ⟨1535118, by rfl⟩ : syracuseStep 4093649 = 3070237) B3070237
theorem B4093699 : Blo 1617007 4093699 := bstep (se 1 (by rfl) ⟨3070274, by rfl⟩ : syracuseStep 4093699 = 6140549) B6140549
theorem B2627345 : Blo 1617007 2627345 := bstep (se 2 (by rfl) ⟨985254, by rfl⟩ : syracuseStep 2627345 = 1970509) B1970509
theorem B5183281 : Blo 1617007 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B5183345 : Blo 1617007 5183345 := bstep (se 2 (by rfl) ⟨1943754, by rfl⟩ : syracuseStep 5183345 = 3887509) B3887509
theorem B119740301 : Blo 1617007 119740301 := bstep (se 3 (by rfl) ⟨22451306, by rfl⟩ : syracuseStep 119740301 = 44902613) B44902613
theorem B4093841 : Blo 1617007 4093841 := bstep (se 2 (by rfl) ⟨1535190, by rfl⟩ : syracuseStep 4093841 = 3070381) B3070381
theorem B5461937 : Blo 1617007 5461937 := bstep (se 2 (by rfl) ⟨2048226, by rfl⟩ : syracuseStep 5461937 = 4096453) B4096453
theorem B3070001 : Blo 1617007 3070001 := bstep (se 2 (by rfl) ⟨1151250, by rfl⟩ : syracuseStep 3070001 = 2302501) B2302501
theorem B18421829 : Blo 1617007 18421829 := bstep (se 4 (by rfl) ⟨1727046, by rfl⟩ : syracuseStep 18421829 = 3454093) B3454093
theorem B2767025 : Blo 1617007 2767025 := bstep (se 2 (by rfl) ⟨1037634, by rfl⟩ : syracuseStep 2767025 = 2075269) B2075269
theorem B3455153 : Blo 1617007 3455153 := bstep (se 2 (by rfl) ⟨1295682, by rfl⟩ : syracuseStep 3455153 = 2591365) B2591365
theorem B12294341 : Blo 1617007 12294341 := bstep (se 4 (by rfl) ⟨1152594, by rfl⟩ : syracuseStep 12294341 = 2305189) B2305189
theorem B8870093 : Blo 1617007 8870093 := bstep (se 3 (by rfl) ⟨1663142, by rfl⟩ : syracuseStep 8870093 = 3326285) B3326285
theorem B9836849 : Blo 1617007 9836849 := bstep (se 2 (by rfl) ⟨3688818, by rfl⟩ : syracuseStep 9836849 = 7377637) B7377637
theorem B7772557 : Blo 1617007 7772557 := bstep (se 3 (by rfl) ⟨1457354, by rfl⟩ : syracuseStep 7772557 = 2914709) B2914709
theorem B10369457 : Blo 1617007 10369457 := bstep (se 2 (by rfl) ⟨3888546, by rfl⟩ : syracuseStep 10369457 = 7777093) B7777093
theorem B5462477 : Blo 1617007 5462477 := bstep (se 3 (by rfl) ⟨1024214, by rfl⟩ : syracuseStep 5462477 = 2048429) B2048429
theorem B7879153 : Blo 1617007 7879153 := bstep (se 2 (by rfl) ⟨2954682, by rfl⟩ : syracuseStep 7879153 = 5909365) B5909365
theorem B5462531 : Blo 1617007 5462531 := bstep (se 1 (by rfl) ⟨4096898, by rfl⟩ : syracuseStep 5462531 = 8193797) B8193797
theorem B9214469 : Blo 1617007 9214469 := bstep (se 4 (by rfl) ⟨863856, by rfl⟩ : syracuseStep 9214469 = 1727713) B1727713
theorem B11074097 : Blo 1617007 11074097 := bstep (se 2 (by rfl) ⟨4152786, by rfl⟩ : syracuseStep 11074097 = 8305573) B8305573
theorem B99629621 : Blo 1617007 99629621 := bstep (se 5 (by rfl) ⟨4670138, by rfl⟩ : syracuseStep 99629621 = 9340277) B9340277
theorem B15972977 : Blo 1617007 15972977 := bstep (se 2 (by rfl) ⟨5989866, by rfl⟩ : syracuseStep 15972977 = 11979733) B11979733
theorem B18430577 : Blo 1617007 18430577 := bstep (se 2 (by rfl) ⟨6911466, by rfl⟩ : syracuseStep 18430577 = 13822933) B13822933
theorem B3889777 : Blo 1617007 3889777 := bstep (se 2 (by rfl) ⟨1458666, by rfl⟩ : syracuseStep 3889777 = 2917333) B2917333
theorem B3070723 : Blo 1617007 3070723 := bstep (se 1 (by rfl) ⟨2303042, by rfl⟩ : syracuseStep 3070723 = 4606085) B4606085
theorem B5462801 : Blo 1617007 5462801 := bstep (se 2 (by rfl) ⟨2048550, by rfl⟩ : syracuseStep 5462801 = 4097101) B4097101
theorem B4094833 : Blo 1617007 4094833 := bstep (se 2 (by rfl) ⟨1535562, by rfl⟩ : syracuseStep 4094833 = 3071125) B3071125
theorem B1727363 : Blo 1617007 1727363 := bstep (se 1 (by rfl) ⟨1295522, by rfl⟩ : syracuseStep 1727363 = 2591045) B2591045
theorem B3455939 : Blo 1617007 3455939 := bstep (se 1 (by rfl) ⟨2591954, by rfl⟩ : syracuseStep 3455939 = 5183909) B5183909
theorem B4922317 : Blo 1617007 4922317 := bstep (se 3 (by rfl) ⟨922934, by rfl⟩ : syracuseStep 4922317 = 1845869) B1845869
theorem B1727491 : Blo 1617007 1727491 := bstep (se 1 (by rfl) ⟨1295618, by rfl⟩ : syracuseStep 1727491 = 2591237) B2591237
theorem B2047027 : Blo 1617007 2047027 := bstep (se 1 (by rfl) ⟨1535270, by rfl⟩ : syracuseStep 2047027 = 3070541) B3070541
theorem B3112003 : Blo 1617007 3112003 := bstep (se 1 (by rfl) ⟨2334002, by rfl⟩ : syracuseStep 3112003 = 4668005) B4668005
theorem B4095107 : Blo 1617007 4095107 := bstep (se 1 (by rfl) ⟨3071330, by rfl⟩ : syracuseStep 4095107 = 6142661) B6142661
theorem B2047123 : Blo 1617007 2047123 := bstep (se 1 (by rfl) ⟨1535342, by rfl⟩ : syracuseStep 2047123 = 3070685) B3070685
theorem B9215153 : Blo 1617007 9215153 := bstep (se 2 (by rfl) ⟨3455682, by rfl⟩ : syracuseStep 9215153 = 6911365) B6911365
theorem B3071171 : Blo 1617007 3071171 := bstep (se 1 (by rfl) ⟨2303378, by rfl⟩ : syracuseStep 3071171 = 4606757) B4606757
theorem B132775139 : Blo 1617007 132775139 := bstep (se 1 (by rfl) ⟨99581354, by rfl⟩ : syracuseStep 132775139 = 199162709) B199162709
theorem B9469189 : Blo 1617007 9469189 := bstep (se 4 (by rfl) ⟨887736, by rfl⟩ : syracuseStep 9469189 = 1775473) B1775473
theorem B5463341 : Blo 1617007 5463341 := bstep (se 3 (by rfl) ⟨1024376, by rfl⟩ : syracuseStep 5463341 = 2048753) B2048753
theorem B4095299 : Blo 1617007 4095299 := bstep (se 1 (by rfl) ⟨3071474, by rfl⟩ : syracuseStep 4095299 = 6142949) B6142949
theorem B5463395 : Blo 1617007 5463395 := bstep (se 1 (by rfl) ⟨4097546, by rfl⟩ : syracuseStep 5463395 = 8195093) B8195093
theorem B31088069 : Blo 1617007 31088069 := bstep (se 4 (by rfl) ⟨2914506, by rfl⟩ : syracuseStep 31088069 = 5829013) B5829013
theorem B3071459 : Blo 1617007 3071459 := bstep (se 1 (by rfl) ⟨2303594, by rfl⟩ : syracuseStep 3071459 = 4607189) B4607189
theorem B2915921 : Blo 1617007 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B5463665 : Blo 1617007 5463665 := bstep (se 2 (by rfl) ⟨2048874, by rfl⟩ : syracuseStep 5463665 = 4097749) B4097749
theorem B2047619 : Blo 1617007 2047619 := bstep (se 1 (by rfl) ⟨1535714, by rfl⟩ : syracuseStep 2047619 = 3071429) B3071429
theorem B15556337 : Blo 1617007 15556337 := bstep (se 2 (by rfl) ⟨5833626, by rfl⟩ : syracuseStep 15556337 = 11667253) B11667253
theorem B7774001 : Blo 1617007 7774001 := bstep (se 2 (by rfl) ⟨2915250, by rfl⟩ : syracuseStep 7774001 = 5830501) B5830501
theorem B1728307 : Blo 1617007 1728307 := bstep (se 1 (by rfl) ⟨1296230, by rfl⟩ : syracuseStep 1728307 = 2592461) B2592461
theorem B4669265 : Blo 1617007 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B5832589 : Blo 1617007 5832589 := bstep (se 3 (by rfl) ⟨1093610, by rfl⟩ : syracuseStep 5832589 = 2187221) B2187221
theorem B3456913 : Blo 1617007 3456913 := bstep (se 2 (by rfl) ⟨1296342, by rfl⟩ : syracuseStep 3456913 = 2592685) B2592685
theorem B6143921 : Blo 1617007 6143921 := bstep (se 2 (by rfl) ⟨2303970, by rfl⟩ : syracuseStep 6143921 = 4607941) B4607941
theorem B6913997 : Blo 1617007 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B18432035 : Blo 1617007 18432035 := bstep (se 1 (by rfl) ⟨13824026, by rfl⟩ : syracuseStep 18432035 = 27648053) B27648053
theorem B6914099 : Blo 1617007 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B7004225 : Blo 1617007 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B2916467 : Blo 1617007 2916467 := bstep (se 1 (by rfl) ⟨2187350, by rfl⟩ : syracuseStep 2916467 = 4374701) B4374701
theorem B78676109 : Blo 1617007 78676109 := bstep (se 3 (by rfl) ⟨14751770, by rfl⟩ : syracuseStep 78676109 = 29503541) B29503541
theorem B9216179 : Blo 1617007 9216179 := bstep (se 1 (by rfl) ⟨6912134, by rfl⟩ : syracuseStep 9216179 = 13824269) B13824269
theorem B2048267 : Blo 1617007 2048267 := bstep (se 1 (by rfl) ⟨1536200, by rfl⟩ : syracuseStep 2048267 = 3072401) B3072401
theorem B5251403 : Blo 1617007 5251403 := bstep (se 1 (by rfl) ⟨3938552, by rfl⟩ : syracuseStep 5251403 = 7877105) B7877105
theorem B23314787 : Blo 1617007 23314787 := bstep (se 1 (by rfl) ⟨17486090, by rfl⟩ : syracuseStep 23314787 = 34972181) B34972181
theorem B16597349 : Blo 1617007 16597349 := bstep (se 4 (by rfl) ⟨1556001, by rfl⟩ : syracuseStep 16597349 = 3112003) B3112003
theorem B1728875 : Blo 1617007 1728875 := bstep (se 1 (by rfl) ⟨1296656, by rfl⟩ : syracuseStep 1728875 = 2593313) B2593313
theorem B6144407 : Blo 1617007 6144407 := bstep (se 1 (by rfl) ⟨4608305, by rfl⟩ : syracuseStep 6144407 = 9216611) B9216611
theorem B1819147 : Blo 1617007 1819147 := bstep (se 1 (by rfl) ⟨1364360, by rfl⟩ : syracuseStep 1819147 = 2728721) B2728721
theorem B10363409 : Blo 1617007 10363409 := bstep (se 2 (by rfl) ⟨3886278, by rfl⟩ : syracuseStep 10363409 = 7772557) B7772557
theorem B5923351 : Blo 1617007 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B13828643 : Blo 1617007 13828643 := bstep (se 1 (by rfl) ⟨10371482, by rfl⟩ : syracuseStep 13828643 = 20742965) B20742965
theorem B6144605 : Blo 1617007 6144605 := bstep (se 3 (by rfl) ⟨1152113, by rfl⟩ : syracuseStep 6144605 = 2304227) B2304227
theorem B1819255 : Blo 1617007 1819255 := bstep (se 1 (by rfl) ⟨1364441, by rfl⟩ : syracuseStep 1819255 = 2728883) B2728883
theorem B2302615 : Blo 1617007 2302615 := bstep (se 1 (by rfl) ⟨1726961, by rfl⟩ : syracuseStep 2302615 = 3453923) B3453923
theorem B8192663 : Blo 1617007 8192663 := bstep (se 1 (by rfl) ⟨6144497, by rfl⟩ : syracuseStep 8192663 = 12288995) B12288995
theorem B23331509 : Blo 1617007 23331509 := bstep (se 5 (by rfl) ⟨1093664, by rfl⟩ : syracuseStep 23331509 = 2187329) B2187329
theorem B2425547 : Blo 1617007 2425547 := bstep (se 1 (by rfl) ⟨1819160, by rfl⟩ : syracuseStep 2425547 = 3638321) B3638321
theorem B2425559 : Blo 1617007 2425559 := bstep (se 1 (by rfl) ⟨1819169, by rfl⟩ : syracuseStep 2425559 = 3638339) B3638339
theorem B1639127 : Blo 1617007 1639127 := bstep (se 1 (by rfl) ⟨1229345, by rfl⟩ : syracuseStep 1639127 = 2458691) B2458691
theorem B2425625 : Blo 1617007 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B1819435 : Blo 1617007 1819435 := bstep (se 1 (by rfl) ⟨1364576, by rfl⟩ : syracuseStep 1819435 = 2729153) B2729153
theorem B26231597 : Blo 1617007 26231597 := bstep (se 3 (by rfl) ⟨4918424, by rfl⟩ : syracuseStep 26231597 = 9836849) B9836849
theorem B5186369 : Blo 1617007 5186369 := bstep (se 2 (by rfl) ⟨1944888, by rfl⟩ : syracuseStep 5186369 = 3889777) B3889777
theorem B2425739 : Blo 1617007 2425739 := bstep (se 1 (by rfl) ⟨1819304, by rfl⟩ : syracuseStep 2425739 = 3638609) B3638609
theorem B2425751 : Blo 1617007 2425751 := bstep (se 1 (by rfl) ⟨1819313, by rfl⟩ : syracuseStep 2425751 = 3638627) B3638627
theorem B1819543 : Blo 1617007 1819543 := bstep (se 1 (by rfl) ⟨1364657, by rfl⟩ : syracuseStep 1819543 = 2729315) B2729315
theorem B4096919 : Blo 1617007 4096919 := bstep (se 1 (by rfl) ⟨3072689, by rfl⟩ : syracuseStep 4096919 = 6145379) B6145379
theorem B3072971 : Blo 1617007 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B2048971 : Blo 1617007 2048971 := bstep (se 1 (by rfl) ⟨1536728, by rfl⟩ : syracuseStep 2048971 = 3073457) B3073457
theorem B2425817 : Blo 1617007 2425817 := bstep (se 2 (by rfl) ⟨909681, by rfl⟩ : syracuseStep 2425817 = 1819363) B1819363
theorem B2917441 : Blo 1617007 2917441 := bstep (se 2 (by rfl) ⟨1094040, by rfl⟩ : syracuseStep 2917441 = 2188081) B2188081
theorem B8741963 : Blo 1617007 8741963 := bstep (se 1 (by rfl) ⟨6556472, by rfl⟩ : syracuseStep 8741963 = 13112945) B13112945
theorem B2425931 : Blo 1617007 2425931 := bstep (se 1 (by rfl) ⟨1819448, by rfl⟩ : syracuseStep 2425931 = 3638897) B3638897
theorem B1819723 : Blo 1617007 1819723 := bstep (se 1 (by rfl) ⟨1364792, by rfl⟩ : syracuseStep 1819723 = 2729585) B2729585
theorem B2425943 : Blo 1617007 2425943 := bstep (se 1 (by rfl) ⟨1819457, by rfl⟩ : syracuseStep 2425943 = 3638915) B3638915
theorem B3073153 : Blo 1617007 3073153 := bstep (se 2 (by rfl) ⟨1152432, by rfl⟩ : syracuseStep 3073153 = 2304865) B2304865
theorem B3638411 : Blo 1617007 3638411 := bstep (se 1 (by rfl) ⟨2728808, by rfl⟩ : syracuseStep 3638411 = 5457617) B5457617
theorem B2729099 : Blo 1617007 2729099 := bstep (se 1 (by rfl) ⟨2046824, by rfl⟩ : syracuseStep 2729099 = 4093649) B4093649
theorem B6907025 : Blo 1617007 6907025 := bstep (se 2 (by rfl) ⟨2590134, by rfl⟩ : syracuseStep 6907025 = 5180269) B5180269
theorem B2426009 : Blo 1617007 2426009 := bstep (se 2 (by rfl) ⟨909753, by rfl⟩ : syracuseStep 2426009 = 1819507) B1819507
theorem B1819831 : Blo 1617007 1819831 := bstep (se 1 (by rfl) ⟨1364873, by rfl⟩ : syracuseStep 1819831 = 2729747) B2729747
theorem B3638465 : Blo 1617007 3638465 := bstep (se 2 (by rfl) ⟨1364424, by rfl⟩ : syracuseStep 3638465 = 2728849) B2728849
theorem B2729227 : Blo 1617007 2729227 := bstep (se 1 (by rfl) ⟨2046920, by rfl⟩ : syracuseStep 2729227 = 4093841) B4093841
theorem B2426123 : Blo 1617007 2426123 := bstep (se 1 (by rfl) ⟨1819592, by rfl⟩ : syracuseStep 2426123 = 3639185) B3639185
theorem B6563089 : Blo 1617007 6563089 := bstep (se 2 (by rfl) ⟨2461158, by rfl⟩ : syracuseStep 6563089 = 4922317) B4922317
theorem B2426135 : Blo 1617007 2426135 := bstep (se 1 (by rfl) ⟨1819601, by rfl⟩ : syracuseStep 2426135 = 3639203) B3639203
theorem B15557953 : Blo 1617007 15557953 := bstep (se 2 (by rfl) ⟨5834232, by rfl⟩ : syracuseStep 15557953 = 11668465) B11668465
theorem B2426201 : Blo 1617007 2426201 := bstep (se 2 (by rfl) ⟨909825, by rfl⟩ : syracuseStep 2426201 = 1819651) B1819651
theorem B2303321 : Blo 1617007 2303321 := bstep (se 2 (by rfl) ⟨863745, by rfl⟩ : syracuseStep 2303321 = 1727491) B1727491
theorem B1820011 : Blo 1617007 1820011 := bstep (se 1 (by rfl) ⟨1365008, by rfl⟩ : syracuseStep 1820011 = 2730017) B2730017
theorem B12281219 : Blo 1617007 12281219 := bstep (se 1 (by rfl) ⟨9210914, by rfl⟩ : syracuseStep 12281219 = 18421829) B18421829
theorem B3638681 : Blo 1617007 3638681 := bstep (se 2 (by rfl) ⟨1364505, by rfl⟩ : syracuseStep 3638681 = 2729011) B2729011
theorem B2729369 : Blo 1617007 2729369 := bstep (se 2 (by rfl) ⟨1023513, by rfl⟩ : syracuseStep 2729369 = 2047027) B2047027
theorem B10372531 : Blo 1617007 10372531 := bstep (se 1 (by rfl) ⟨7779398, by rfl⟩ : syracuseStep 10372531 = 15558797) B15558797
theorem B2426315 : Blo 1617007 2426315 := bstep (se 1 (by rfl) ⟨1819736, by rfl⟩ : syracuseStep 2426315 = 3639473) B3639473
theorem B2303435 : Blo 1617007 2303435 := bstep (se 1 (by rfl) ⟨1727576, by rfl⟩ : syracuseStep 2303435 = 3455153) B3455153
theorem B2426327 : Blo 1617007 2426327 := bstep (se 1 (by rfl) ⟨1819745, by rfl⟩ : syracuseStep 2426327 = 3639491) B3639491
theorem B1820119 : Blo 1617007 1820119 := bstep (se 1 (by rfl) ⟨1365089, by rfl⟩ : syracuseStep 1820119 = 2730179) B2730179
theorem B3638771 : Blo 1617007 3638771 := bstep (se 1 (by rfl) ⟨2729078, by rfl⟩ : syracuseStep 3638771 = 5458157) B5458157
theorem B38389261 : Blo 1617007 38389261 := bstep (se 3 (by rfl) ⟨7197986, by rfl⟩ : syracuseStep 38389261 = 14395973) B14395973
theorem B3638807 : Blo 1617007 3638807 := bstep (se 1 (by rfl) ⟨2729105, by rfl⟩ : syracuseStep 3638807 = 5458211) B5458211
theorem B2729497 : Blo 1617007 2729497 := bstep (se 2 (by rfl) ⟨1023561, by rfl⟩ : syracuseStep 2729497 = 2047123) B2047123
theorem B2426393 : Blo 1617007 2426393 := bstep (se 2 (by rfl) ⟨909897, by rfl⟩ : syracuseStep 2426393 = 1819795) B1819795
theorem B4097587 : Blo 1617007 4097587 := bstep (se 1 (by rfl) ⟨3073190, by rfl⟩ : syracuseStep 4097587 = 6146381) B6146381
theorem B9217637 : Blo 1617007 9217637 := bstep (se 4 (by rfl) ⟨864153, by rfl⟩ : syracuseStep 9217637 = 1728307) B1728307
theorem B2426507 : Blo 1617007 2426507 := bstep (se 1 (by rfl) ⟨1819880, by rfl⟩ : syracuseStep 2426507 = 3639761) B3639761
theorem B1820299 : Blo 1617007 1820299 := bstep (se 1 (by rfl) ⟨1365224, by rfl⟩ : syracuseStep 1820299 = 2730449) B2730449
theorem B2426519 : Blo 1617007 2426519 := bstep (se 1 (by rfl) ⟨1819889, by rfl⟩ : syracuseStep 2426519 = 3639779) B3639779
theorem B4097729 : Blo 1617007 4097729 := bstep (se 2 (by rfl) ⟨1536648, by rfl⟩ : syracuseStep 4097729 = 3073297) B3073297
theorem B3638987 : Blo 1617007 3638987 := bstep (se 1 (by rfl) ⟨2729240, by rfl⟩ : syracuseStep 3638987 = 5458481) B5458481
theorem B2426585 : Blo 1617007 2426585 := bstep (se 2 (by rfl) ⟨909969, by rfl⟩ : syracuseStep 2426585 = 1819939) B1819939
theorem B1820407 : Blo 1617007 1820407 := bstep (se 1 (by rfl) ⟨1365305, by rfl⟩ : syracuseStep 1820407 = 2730611) B2730611
theorem B3639041 : Blo 1617007 3639041 := bstep (se 2 (by rfl) ⟨1364640, by rfl⟩ : syracuseStep 3639041 = 2729281) B2729281
theorem B2426699 : Blo 1617007 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B2426711 : Blo 1617007 2426711 := bstep (se 1 (by rfl) ⟨1820033, by rfl⟩ : syracuseStep 2426711 = 3640067) B3640067
theorem B2426777 : Blo 1617007 2426777 := bstep (se 2 (by rfl) ⟨910041, by rfl⟩ : syracuseStep 2426777 = 1820083) B1820083
theorem B1820587 : Blo 1617007 1820587 := bstep (se 1 (by rfl) ⟨1365440, by rfl⟩ : syracuseStep 1820587 = 2730881) B2730881
theorem B2303959 : Blo 1617007 2303959 := bstep (se 1 (by rfl) ⟨1727969, by rfl⟩ : syracuseStep 2303959 = 3455939) B3455939
theorem B4605913 : Blo 1617007 4605913 := bstep (se 2 (by rfl) ⟨1727217, by rfl⟩ : syracuseStep 4605913 = 3454435) B3454435
theorem B3639257 : Blo 1617007 3639257 := bstep (se 2 (by rfl) ⟨1364721, by rfl⟩ : syracuseStep 3639257 = 2729443) B2729443
theorem B2426891 : Blo 1617007 2426891 := bstep (se 1 (by rfl) ⟨1820168, by rfl⟩ : syracuseStep 2426891 = 3640337) B3640337
theorem B2426903 : Blo 1617007 2426903 := bstep (se 1 (by rfl) ⟨1820177, by rfl⟩ : syracuseStep 2426903 = 3640355) B3640355
theorem B1820695 : Blo 1617007 1820695 := bstep (se 1 (by rfl) ⟨1365521, by rfl⟩ : syracuseStep 1820695 = 2731043) B2731043
theorem B6907949 : Blo 1617007 6907949 := bstep (se 3 (by rfl) ⟨1295240, by rfl⟩ : syracuseStep 6907949 = 2590481) B2590481
theorem B3639347 : Blo 1617007 3639347 := bstep (se 1 (by rfl) ⟨2729510, by rfl⟩ : syracuseStep 3639347 = 5459021) B5459021
theorem B4671553 : Blo 1617007 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B5457995 : Blo 1617007 5457995 := bstep (se 1 (by rfl) ⟨4093496, by rfl⟩ : syracuseStep 5457995 = 8186993) B8186993
theorem B8751179 : Blo 1617007 8751179 := bstep (se 1 (by rfl) ⟨6563384, by rfl⟩ : syracuseStep 8751179 = 13126769) B13126769
theorem B3639383 : Blo 1617007 3639383 := bstep (se 1 (by rfl) ⟨2729537, by rfl⟩ : syracuseStep 3639383 = 5459075) B5459075
theorem B2730071 : Blo 1617007 2730071 := bstep (se 1 (by rfl) ⟨2047553, by rfl⟩ : syracuseStep 2730071 = 4095107) B4095107
theorem B2426969 : Blo 1617007 2426969 := bstep (se 2 (by rfl) ⟨910113, by rfl⟩ : syracuseStep 2426969 = 1820227) B1820227
theorem B88516759 : Blo 1617007 88516759 := bstep (se 1 (by rfl) ⟨66387569, by rfl⟩ : syracuseStep 88516759 = 132775139) B132775139
theorem B2427083 : Blo 1617007 2427083 := bstep (se 1 (by rfl) ⟨1820312, by rfl⟩ : syracuseStep 2427083 = 3640625) B3640625
theorem B1820875 : Blo 1617007 1820875 := bstep (se 1 (by rfl) ⟨1365656, by rfl⟩ : syracuseStep 1820875 = 2731313) B2731313
theorem B2730199 : Blo 1617007 2730199 := bstep (se 1 (by rfl) ⟨2047649, by rfl⟩ : syracuseStep 2730199 = 4095299) B4095299
theorem B2427095 : Blo 1617007 2427095 := bstep (se 1 (by rfl) ⟨1820321, by rfl⟩ : syracuseStep 2427095 = 3640643) B3640643
theorem B3639563 : Blo 1617007 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B2427161 : Blo 1617007 2427161 := bstep (se 2 (by rfl) ⟨910185, by rfl⟩ : syracuseStep 2427161 = 1820371) B1820371
theorem B1820983 : Blo 1617007 1820983 := bstep (se 1 (by rfl) ⟨1365737, by rfl⟩ : syracuseStep 1820983 = 2731475) B2731475
theorem B3639617 : Blo 1617007 3639617 := bstep (se 2 (by rfl) ⟨1364856, by rfl⟩ : syracuseStep 3639617 = 2729713) B2729713
theorem B3279179 : Blo 1617007 3279179 := bstep (se 1 (by rfl) ⟨2459384, by rfl⟩ : syracuseStep 3279179 = 4918769) B4918769
theorem B5458265 : Blo 1617007 5458265 := bstep (se 2 (by rfl) ⟨2046849, by rfl⟩ : syracuseStep 5458265 = 4093699) B4093699
theorem B4606301 : Blo 1617007 4606301 := bstep (se 3 (by rfl) ⟨863681, by rfl⟩ : syracuseStep 4606301 = 1727363) B1727363
theorem B1943947 : Blo 1617007 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B2427275 : Blo 1617007 2427275 := bstep (se 1 (by rfl) ⟨1820456, by rfl⟩ : syracuseStep 2427275 = 3640913) B3640913
theorem B2427287 : Blo 1617007 2427287 := bstep (se 1 (by rfl) ⟨1820465, by rfl⟩ : syracuseStep 2427287 = 3640931) B3640931
theorem B3885491 : Blo 1617007 3885491 := bstep (se 1 (by rfl) ⟨2914118, by rfl⟩ : syracuseStep 3885491 = 5828237) B5828237
theorem B2427353 : Blo 1617007 2427353 := bstep (se 2 (by rfl) ⟨910257, by rfl⟩ : syracuseStep 2427353 = 1820515) B1820515
theorem B1821163 : Blo 1617007 1821163 := bstep (se 1 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 1821163 = 2731745) B2731745
theorem B6146563 : Blo 1617007 6146563 := bstep (se 1 (by rfl) ⟨4609922, by rfl⟩ : syracuseStep 6146563 = 9219845) B9219845
theorem B7776785 : Blo 1617007 7776785 := bstep (se 2 (by rfl) ⟨2916294, by rfl⟩ : syracuseStep 7776785 = 5832589) B5832589
theorem B3639833 : Blo 1617007 3639833 := bstep (se 2 (by rfl) ⟨1364937, by rfl⟩ : syracuseStep 3639833 = 2729875) B2729875
theorem B2427467 : Blo 1617007 2427467 := bstep (se 1 (by rfl) ⟨1820600, by rfl⟩ : syracuseStep 2427467 = 3641201) B3641201
theorem B2427479 : Blo 1617007 2427479 := bstep (se 1 (by rfl) ⟨1820609, by rfl⟩ : syracuseStep 2427479 = 3641219) B3641219
theorem B1821271 : Blo 1617007 1821271 := bstep (se 1 (by rfl) ⟨1365953, by rfl⟩ : syracuseStep 1821271 = 2731907) B2731907
theorem B3639923 : Blo 1617007 3639923 := bstep (se 1 (by rfl) ⟨2729942, by rfl⟩ : syracuseStep 3639923 = 5459885) B5459885
theorem B3639959 : Blo 1617007 3639959 := bstep (se 1 (by rfl) ⟨2729969, by rfl⟩ : syracuseStep 3639959 = 5459939) B5459939
theorem B2427545 : Blo 1617007 2427545 := bstep (se 2 (by rfl) ⟨910329, by rfl⟩ : syracuseStep 2427545 = 1820659) B1820659
theorem B7105283 : Blo 1617007 7105283 := bstep (se 1 (by rfl) ⟨5328962, by rfl⟩ : syracuseStep 7105283 = 10657925) B10657925
theorem B2427659 : Blo 1617007 2427659 := bstep (se 1 (by rfl) ⟨1820744, by rfl⟩ : syracuseStep 2427659 = 3641489) B3641489
theorem B2304779 : Blo 1617007 2304779 := bstep (se 1 (by rfl) ⟨1728584, by rfl⟩ : syracuseStep 2304779 = 3457169) B3457169
theorem B2427671 : Blo 1617007 2427671 := bstep (se 1 (by rfl) ⟨1820753, by rfl⟩ : syracuseStep 2427671 = 3641507) B3641507
theorem B8186669 : Blo 1617007 8186669 := bstep (se 3 (by rfl) ⟨1535000, by rfl⟩ : syracuseStep 8186669 = 3070001) B3070001
theorem B6146867 : Blo 1617007 6146867 := bstep (se 1 (by rfl) ⟨4610150, by rfl⟩ : syracuseStep 6146867 = 9220301) B9220301
theorem B164039489 : Blo 1617007 164039489 := bstep (se 2 (by rfl) ⟨61514808, by rfl⟩ : syracuseStep 164039489 = 123029617) B123029617
theorem B3640139 : Blo 1617007 3640139 := bstep (se 1 (by rfl) ⟨2730104, by rfl⟩ : syracuseStep 3640139 = 5460209) B5460209
theorem B2730827 : Blo 1617007 2730827 := bstep (se 1 (by rfl) ⟨2048120, by rfl⟩ : syracuseStep 2730827 = 4096241) B4096241
theorem B2427737 : Blo 1617007 2427737 := bstep (se 2 (by rfl) ⟨910401, by rfl⟩ : syracuseStep 2427737 = 1820803) B1820803
theorem B8743781 : Blo 1617007 8743781 := bstep (se 4 (by rfl) ⟨819729, by rfl⟩ : syracuseStep 8743781 = 1639459) B1639459
theorem B3640193 : Blo 1617007 3640193 := bstep (se 2 (by rfl) ⟨1365072, by rfl⟩ : syracuseStep 3640193 = 2730145) B2730145
theorem B2730955 : Blo 1617007 2730955 := bstep (se 1 (by rfl) ⟨2048216, by rfl⟩ : syracuseStep 2730955 = 4096433) B4096433
theorem B2427851 : Blo 1617007 2427851 := bstep (se 1 (by rfl) ⟨1820888, by rfl⟩ : syracuseStep 2427851 = 3641777) B3641777
theorem B2427863 : Blo 1617007 2427863 := bstep (se 1 (by rfl) ⟨1820897, by rfl⟩ : syracuseStep 2427863 = 3641795) B3641795
theorem B5458967 : Blo 1617007 5458967 := bstep (se 1 (by rfl) ⟨4094225, by rfl⟩ : syracuseStep 5458967 = 8188451) B8188451
theorem B2427929 : Blo 1617007 2427929 := bstep (se 2 (by rfl) ⟨910473, by rfl⟩ : syracuseStep 2427929 = 1820947) B1820947
theorem B42036259 : Blo 1617007 42036259 := bstep (se 1 (by rfl) ⟨31527194, by rfl⟩ : syracuseStep 42036259 = 63054389) B63054389
theorem B3640409 : Blo 1617007 3640409 := bstep (se 2 (by rfl) ⟨1365153, by rfl⟩ : syracuseStep 3640409 = 2730307) B2730307
theorem B2731097 : Blo 1617007 2731097 := bstep (se 2 (by rfl) ⟨1024161, by rfl⟩ : syracuseStep 2731097 = 2048323) B2048323
theorem B1617015 : Blo 1617007 1617015 := bstep (se 1 (by rfl) ⟨1212761, by rfl⟩ : syracuseStep 1617015 = 2425523) B2425523
theorem B1617035 : Blo 1617007 1617035 := bstep (se 1 (by rfl) ⟨1212776, by rfl⟩ : syracuseStep 1617035 = 2425553) B2425553
theorem B2428043 : Blo 1617007 2428043 := bstep (se 1 (by rfl) ⟨1821032, by rfl⟩ : syracuseStep 2428043 = 3642065) B3642065
theorem B7376017 : Blo 1617007 7376017 := bstep (se 2 (by rfl) ⟨2766006, by rfl⟩ : syracuseStep 7376017 = 5532013) B5532013
theorem B1617047 : Blo 1617007 1617047 := bstep (se 1 (by rfl) ⟨1212785, by rfl⟩ : syracuseStep 1617047 = 2425571) B2425571
theorem B3886231 : Blo 1617007 3886231 := bstep (se 1 (by rfl) ⟨2914673, by rfl⟩ : syracuseStep 3886231 = 5829347) B5829347
theorem B2428055 : Blo 1617007 2428055 := bstep (se 1 (by rfl) ⟨1821041, by rfl⟩ : syracuseStep 2428055 = 3642083) B3642083
theorem B1617067 : Blo 1617007 1617067 := bstep (se 1 (by rfl) ⟨1212800, by rfl⟩ : syracuseStep 1617067 = 2425601) B2425601
theorem B3640499 : Blo 1617007 3640499 := bstep (se 1 (by rfl) ⟨2730374, by rfl⟩ : syracuseStep 3640499 = 5460749) B5460749
theorem B1617079 : Blo 1617007 1617079 := bstep (se 1 (by rfl) ⟨1212809, by rfl⟩ : syracuseStep 1617079 = 2425619) B2425619
theorem B1617099 : Blo 1617007 1617099 := bstep (se 1 (by rfl) ⟨1212824, by rfl⟩ : syracuseStep 1617099 = 2425649) B2425649
theorem B1617111 : Blo 1617007 1617111 := bstep (se 1 (by rfl) ⟨1212833, by rfl⟩ : syracuseStep 1617111 = 2425667) B2425667
theorem B3640535 : Blo 1617007 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B9211097 : Blo 1617007 9211097 := bstep (se 2 (by rfl) ⟨3454161, by rfl⟩ : syracuseStep 9211097 = 6908323) B6908323
theorem B2731225 : Blo 1617007 2731225 := bstep (se 2 (by rfl) ⟨1024209, by rfl⟩ : syracuseStep 2731225 = 2048419) B2048419
theorem B2428121 : Blo 1617007 2428121 := bstep (se 2 (by rfl) ⟨910545, by rfl⟩ : syracuseStep 2428121 = 1821091) B1821091
theorem B1617131 : Blo 1617007 1617131 := bstep (se 1 (by rfl) ⟨1212848, by rfl⟩ : syracuseStep 1617131 = 2425697) B2425697
theorem B1617143 : Blo 1617007 1617143 := bstep (se 1 (by rfl) ⟨1212857, by rfl⟩ : syracuseStep 1617143 = 2425715) B2425715
theorem B1617163 : Blo 1617007 1617163 := bstep (se 1 (by rfl) ⟨1212872, by rfl⟩ : syracuseStep 1617163 = 2425745) B2425745
theorem B1617175 : Blo 1617007 1617175 := bstep (se 1 (by rfl) ⟨1212881, by rfl⟩ : syracuseStep 1617175 = 2425763) B2425763
theorem B1617195 : Blo 1617007 1617195 := bstep (se 1 (by rfl) ⟨1212896, by rfl⟩ : syracuseStep 1617195 = 2425793) B2425793
theorem B1617207 : Blo 1617007 1617207 := bstep (se 1 (by rfl) ⟨1212905, by rfl⟩ : syracuseStep 1617207 = 2425811) B2425811
theorem B10505537 : Blo 1617007 10505537 := bstep (se 2 (by rfl) ⟨3939576, by rfl⟩ : syracuseStep 10505537 = 7879153) B7879153
theorem B1617227 : Blo 1617007 1617227 := bstep (se 1 (by rfl) ⟨1212920, by rfl⟩ : syracuseStep 1617227 = 2425841) B2425841
theorem B2428235 : Blo 1617007 2428235 := bstep (se 1 (by rfl) ⟨1821176, by rfl⟩ : syracuseStep 2428235 = 3642353) B3642353
theorem B1617239 : Blo 1617007 1617239 := bstep (se 1 (by rfl) ⟨1212929, by rfl⟩ : syracuseStep 1617239 = 2425859) B2425859
theorem B2428247 : Blo 1617007 2428247 := bstep (se 1 (by rfl) ⟨1821185, by rfl⟩ : syracuseStep 2428247 = 3642371) B3642371
theorem B1617259 : Blo 1617007 1617259 := bstep (se 1 (by rfl) ⟨1212944, by rfl⟩ : syracuseStep 1617259 = 2425889) B2425889
theorem B1617271 : Blo 1617007 1617271 := bstep (se 1 (by rfl) ⟨1212953, by rfl⟩ : syracuseStep 1617271 = 2425907) B2425907
theorem B1617291 : Blo 1617007 1617291 := bstep (se 1 (by rfl) ⟨1212968, by rfl⟩ : syracuseStep 1617291 = 2425937) B2425937
theorem B3640715 : Blo 1617007 3640715 := bstep (se 1 (by rfl) ⟨2730536, by rfl⟩ : syracuseStep 3640715 = 5461073) B5461073
theorem B1617303 : Blo 1617007 1617303 := bstep (se 1 (by rfl) ⟨1212977, by rfl⟩ : syracuseStep 1617303 = 2425955) B2425955
theorem B2428313 : Blo 1617007 2428313 := bstep (se 2 (by rfl) ⟨910617, by rfl⟩ : syracuseStep 2428313 = 1821235) B1821235
theorem B1617323 : Blo 1617007 1617323 := bstep (se 1 (by rfl) ⟨1212992, by rfl⟩ : syracuseStep 1617323 = 2425985) B2425985
theorem B1617335 : Blo 1617007 1617335 := bstep (se 1 (by rfl) ⟨1213001, by rfl⟩ : syracuseStep 1617335 = 2426003) B2426003
theorem B3640769 : Blo 1617007 3640769 := bstep (se 2 (by rfl) ⟨1365288, by rfl⟩ : syracuseStep 3640769 = 2730577) B2730577
theorem B1617355 : Blo 1617007 1617355 := bstep (se 1 (by rfl) ⟨1213016, by rfl⟩ : syracuseStep 1617355 = 2426033) B2426033
theorem B1617367 : Blo 1617007 1617367 := bstep (se 1 (by rfl) ⟨1213025, by rfl⟩ : syracuseStep 1617367 = 2426051) B2426051
theorem B6909401 : Blo 1617007 6909401 := bstep (se 2 (by rfl) ⟨2591025, by rfl⟩ : syracuseStep 6909401 = 5182051) B5182051
theorem B1617387 : Blo 1617007 1617387 := bstep (se 1 (by rfl) ⟨1213040, by rfl⟩ : syracuseStep 1617387 = 2426081) B2426081
theorem B1617399 : Blo 1617007 1617399 := bstep (se 1 (by rfl) ⟨1213049, by rfl⟩ : syracuseStep 1617399 = 2426099) B2426099
theorem B1617419 : Blo 1617007 1617419 := bstep (se 1 (by rfl) ⟨1213064, by rfl⟩ : syracuseStep 1617419 = 2426129) B2426129
theorem B2428427 : Blo 1617007 2428427 := bstep (se 1 (by rfl) ⟨1821320, by rfl⟩ : syracuseStep 2428427 = 3642641) B3642641
theorem B1617431 : Blo 1617007 1617431 := bstep (se 1 (by rfl) ⟨1213073, by rfl⟩ : syracuseStep 1617431 = 2426147) B2426147
theorem B2428439 : Blo 1617007 2428439 := bstep (se 1 (by rfl) ⟨1821329, by rfl⟩ : syracuseStep 2428439 = 3642659) B3642659
theorem B1617451 : Blo 1617007 1617451 := bstep (se 1 (by rfl) ⟨1213088, by rfl⟩ : syracuseStep 1617451 = 2426177) B2426177
theorem B5459507 : Blo 1617007 5459507 := bstep (se 1 (by rfl) ⟨4094630, by rfl⟩ : syracuseStep 5459507 = 8189261) B8189261
theorem B1617463 : Blo 1617007 1617463 := bstep (se 1 (by rfl) ⟨1213097, by rfl⟩ : syracuseStep 1617463 = 2426195) B2426195
theorem B1617483 : Blo 1617007 1617483 := bstep (se 1 (by rfl) ⟨1213112, by rfl⟩ : syracuseStep 1617483 = 2426225) B2426225
theorem B1617495 : Blo 1617007 1617495 := bstep (se 1 (by rfl) ⟨1213121, by rfl⟩ : syracuseStep 1617495 = 2426243) B2426243
theorem B2428505 : Blo 1617007 2428505 := bstep (se 2 (by rfl) ⟨910689, by rfl⟩ : syracuseStep 2428505 = 1821379) B1821379
theorem B1617515 : Blo 1617007 1617515 := bstep (se 1 (by rfl) ⟨1213136, by rfl⟩ : syracuseStep 1617515 = 2426273) B2426273
theorem B1617527 : Blo 1617007 1617527 := bstep (se 1 (by rfl) ⟨1213145, by rfl⟩ : syracuseStep 1617527 = 2426291) B2426291
theorem B1617547 : Blo 1617007 1617547 := bstep (se 1 (by rfl) ⟨1213160, by rfl⟩ : syracuseStep 1617547 = 2426321) B2426321
theorem B1617559 : Blo 1617007 1617559 := bstep (se 1 (by rfl) ⟨1213169, by rfl⟩ : syracuseStep 1617559 = 2426339) B2426339
theorem B3640985 : Blo 1617007 3640985 := bstep (se 2 (by rfl) ⟨1365369, by rfl⟩ : syracuseStep 3640985 = 2730739) B2730739
theorem B1617579 : Blo 1617007 1617579 := bstep (se 1 (by rfl) ⟨1213184, by rfl⟩ : syracuseStep 1617579 = 2426369) B2426369
theorem B1617591 : Blo 1617007 1617591 := bstep (se 1 (by rfl) ⟨1213193, by rfl⟩ : syracuseStep 1617591 = 2426387) B2426387
theorem B1617611 : Blo 1617007 1617611 := bstep (se 1 (by rfl) ⟨1213208, by rfl⟩ : syracuseStep 1617611 = 2426417) B2426417
theorem B1617623 : Blo 1617007 1617623 := bstep (se 1 (by rfl) ⟨1213217, by rfl⟩ : syracuseStep 1617623 = 2426435) B2426435
theorem B1617643 : Blo 1617007 1617643 := bstep (se 1 (by rfl) ⟨1213232, by rfl⟩ : syracuseStep 1617643 = 2426465) B2426465
theorem B3641075 : Blo 1617007 3641075 := bstep (se 1 (by rfl) ⟨2730806, by rfl⟩ : syracuseStep 3641075 = 5461613) B5461613
theorem B1617655 : Blo 1617007 1617655 := bstep (se 1 (by rfl) ⟨1213241, by rfl⟩ : syracuseStep 1617655 = 2426483) B2426483
theorem B1617675 : Blo 1617007 1617675 := bstep (se 1 (by rfl) ⟨1213256, by rfl⟩ : syracuseStep 1617675 = 2426513) B2426513
theorem B1617687 : Blo 1617007 1617687 := bstep (se 1 (by rfl) ⟨1213265, by rfl⟩ : syracuseStep 1617687 = 2426531) B2426531
theorem B3641111 : Blo 1617007 3641111 := bstep (se 1 (by rfl) ⟨2730833, by rfl⟩ : syracuseStep 3641111 = 5461667) B5461667
theorem B2731799 : Blo 1617007 2731799 := bstep (se 1 (by rfl) ⟨2048849, by rfl⟩ : syracuseStep 2731799 = 4097699) B4097699
theorem B1617707 : Blo 1617007 1617707 := bstep (se 1 (by rfl) ⟨1213280, by rfl⟩ : syracuseStep 1617707 = 2426561) B2426561
theorem B1617719 : Blo 1617007 1617719 := bstep (se 1 (by rfl) ⟨1213289, by rfl⟩ : syracuseStep 1617719 = 2426579) B2426579
theorem B5459777 : Blo 1617007 5459777 := bstep (se 2 (by rfl) ⟨2047416, by rfl⟩ : syracuseStep 5459777 = 4094833) B4094833
theorem B1617739 : Blo 1617007 1617739 := bstep (se 1 (by rfl) ⟨1213304, by rfl⟩ : syracuseStep 1617739 = 2426609) B2426609
theorem B1617751 : Blo 1617007 1617751 := bstep (se 1 (by rfl) ⟨1213313, by rfl⟩ : syracuseStep 1617751 = 2426627) B2426627
theorem B1617771 : Blo 1617007 1617771 := bstep (se 1 (by rfl) ⟨1213328, by rfl⟩ : syracuseStep 1617771 = 2426657) B2426657
theorem B1617783 : Blo 1617007 1617783 := bstep (se 1 (by rfl) ⟨1213337, by rfl⟩ : syracuseStep 1617783 = 2426675) B2426675
theorem B1617803 : Blo 1617007 1617803 := bstep (se 1 (by rfl) ⟨1213352, by rfl⟩ : syracuseStep 1617803 = 2426705) B2426705
theorem B1617815 : Blo 1617007 1617815 := bstep (se 1 (by rfl) ⟨1213361, by rfl⟩ : syracuseStep 1617815 = 2426723) B2426723
theorem B2731927 : Blo 1617007 2731927 := bstep (se 1 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 2731927 = 4097891) B4097891
theorem B1617835 : Blo 1617007 1617835 := bstep (se 1 (by rfl) ⟨1213376, by rfl⟩ : syracuseStep 1617835 = 2426753) B2426753
theorem B79826867 : Blo 1617007 79826867 := bstep (se 1 (by rfl) ⟨59870150, by rfl⟩ : syracuseStep 79826867 = 119740301) B119740301
theorem B1617847 : Blo 1617007 1617847 := bstep (se 1 (by rfl) ⟨1213385, by rfl⟩ : syracuseStep 1617847 = 2426771) B2426771
theorem B1617867 : Blo 1617007 1617867 := bstep (se 1 (by rfl) ⟨1213400, by rfl⟩ : syracuseStep 1617867 = 2426801) B2426801
theorem B3641291 : Blo 1617007 3641291 := bstep (se 1 (by rfl) ⟨2730968, by rfl⟩ : syracuseStep 3641291 = 5461937) B5461937
theorem B1617879 : Blo 1617007 1617879 := bstep (se 1 (by rfl) ⟨1213409, by rfl⟩ : syracuseStep 1617879 = 2426819) B2426819
theorem B1617899 : Blo 1617007 1617899 := bstep (se 1 (by rfl) ⟨1213424, by rfl⟩ : syracuseStep 1617899 = 2426849) B2426849
theorem B1617911 : Blo 1617007 1617911 := bstep (se 1 (by rfl) ⟨1213433, by rfl⟩ : syracuseStep 1617911 = 2426867) B2426867
theorem B3641345 : Blo 1617007 3641345 := bstep (se 2 (by rfl) ⟨1365504, by rfl⟩ : syracuseStep 3641345 = 2731009) B2731009
theorem B1617931 : Blo 1617007 1617931 := bstep (se 1 (by rfl) ⟨1213448, by rfl⟩ : syracuseStep 1617931 = 2426897) B2426897
theorem B1617943 : Blo 1617007 1617943 := bstep (se 1 (by rfl) ⟨1213457, by rfl⟩ : syracuseStep 1617943 = 2426915) B2426915
theorem B1617963 : Blo 1617007 1617963 := bstep (se 1 (by rfl) ⟨1213472, by rfl⟩ : syracuseStep 1617963 = 2426945) B2426945
theorem B1617975 : Blo 1617007 1617975 := bstep (se 1 (by rfl) ⟨1213481, by rfl⟩ : syracuseStep 1617975 = 2426963) B2426963
theorem B1617995 : Blo 1617007 1617995 := bstep (se 1 (by rfl) ⟨1213496, by rfl⟩ : syracuseStep 1617995 = 2426993) B2426993
theorem B1618007 : Blo 1617007 1618007 := bstep (se 1 (by rfl) ⟨1213505, by rfl⟩ : syracuseStep 1618007 = 2427011) B2427011
theorem B1618027 : Blo 1617007 1618027 := bstep (se 1 (by rfl) ⟨1213520, by rfl⟩ : syracuseStep 1618027 = 2427041) B2427041
theorem B1618039 : Blo 1617007 1618039 := bstep (se 1 (by rfl) ⟨1213529, by rfl⟩ : syracuseStep 1618039 = 2427059) B2427059
theorem B8196227 : Blo 1617007 8196227 := bstep (se 1 (by rfl) ⟨6147170, by rfl⟩ : syracuseStep 8196227 = 12294341) B12294341
theorem B1618059 : Blo 1617007 1618059 := bstep (se 1 (by rfl) ⟨1213544, by rfl⟩ : syracuseStep 1618059 = 2427089) B2427089
theorem B1618071 : Blo 1617007 1618071 := bstep (se 1 (by rfl) ⟨1213553, by rfl⟩ : syracuseStep 1618071 = 2427107) B2427107
theorem B1618091 : Blo 1617007 1618091 := bstep (se 1 (by rfl) ⟨1213568, by rfl⟩ : syracuseStep 1618091 = 2427137) B2427137
theorem B1618103 : Blo 1617007 1618103 := bstep (se 1 (by rfl) ⟨1213577, by rfl⟩ : syracuseStep 1618103 = 2427155) B2427155
theorem B1618123 : Blo 1617007 1618123 := bstep (se 1 (by rfl) ⟨1213592, by rfl⟩ : syracuseStep 1618123 = 2427185) B2427185
theorem B1618135 : Blo 1617007 1618135 := bstep (se 1 (by rfl) ⟨1213601, by rfl⟩ : syracuseStep 1618135 = 2427203) B2427203
theorem B3641561 : Blo 1617007 3641561 := bstep (se 2 (by rfl) ⟨1365585, by rfl⟩ : syracuseStep 3641561 = 2731171) B2731171
theorem B1618155 : Blo 1617007 1618155 := bstep (se 1 (by rfl) ⟨1213616, by rfl⟩ : syracuseStep 1618155 = 2427233) B2427233
theorem B1618167 : Blo 1617007 1618167 := bstep (se 1 (by rfl) ⟨1213625, by rfl⟩ : syracuseStep 1618167 = 2427251) B2427251
theorem B1618187 : Blo 1617007 1618187 := bstep (se 1 (by rfl) ⟨1213640, by rfl⟩ : syracuseStep 1618187 = 2427281) B2427281
theorem B1618199 : Blo 1617007 1618199 := bstep (se 1 (by rfl) ⟨1213649, by rfl⟩ : syracuseStep 1618199 = 2427299) B2427299
theorem B1618219 : Blo 1617007 1618219 := bstep (se 1 (by rfl) ⟨1213664, by rfl⟩ : syracuseStep 1618219 = 2427329) B2427329
theorem B42594605 : Blo 1617007 42594605 := bstep (se 3 (by rfl) ⟨7986488, by rfl⟩ : syracuseStep 42594605 = 15972977) B15972977
theorem B12292397 : Blo 1617007 12292397 := bstep (se 3 (by rfl) ⟨2304824, by rfl⟩ : syracuseStep 12292397 = 4609649) B4609649
theorem B3641651 : Blo 1617007 3641651 := bstep (se 1 (by rfl) ⟨2731238, by rfl⟩ : syracuseStep 3641651 = 5462477) B5462477
theorem B1618231 : Blo 1617007 1618231 := bstep (se 1 (by rfl) ⟨1213673, by rfl⟩ : syracuseStep 1618231 = 2427347) B2427347
theorem B14954827 : Blo 1617007 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B5534027 : Blo 1617007 5534027 := bstep (se 1 (by rfl) ⟨4150520, by rfl⟩ : syracuseStep 5534027 = 8301041) B8301041
theorem B1618251 : Blo 1617007 1618251 := bstep (se 1 (by rfl) ⟨1213688, by rfl⟩ : syracuseStep 1618251 = 2427377) B2427377
theorem B1618263 : Blo 1617007 1618263 := bstep (se 1 (by rfl) ⟨1213697, by rfl⟩ : syracuseStep 1618263 = 2427395) B2427395
theorem B3641687 : Blo 1617007 3641687 := bstep (se 1 (by rfl) ⟨2731265, by rfl⟩ : syracuseStep 3641687 = 5462531) B5462531
theorem B5460317 : Blo 1617007 5460317 := bstep (se 3 (by rfl) ⟨1023809, by rfl⟩ : syracuseStep 5460317 = 2047619) B2047619
theorem B1618283 : Blo 1617007 1618283 := bstep (se 1 (by rfl) ⟨1213712, by rfl⟩ : syracuseStep 1618283 = 2427425) B2427425
theorem B1618295 : Blo 1617007 1618295 := bstep (se 1 (by rfl) ⟨1213721, by rfl⟩ : syracuseStep 1618295 = 2427443) B2427443
theorem B1618315 : Blo 1617007 1618315 := bstep (se 1 (by rfl) ⟨1213736, by rfl⟩ : syracuseStep 1618315 = 2427473) B2427473
theorem B1618327 : Blo 1617007 1618327 := bstep (se 1 (by rfl) ⟨1213745, by rfl⟩ : syracuseStep 1618327 = 2427491) B2427491
theorem B1618347 : Blo 1617007 1618347 := bstep (se 1 (by rfl) ⟨1213760, by rfl⟩ : syracuseStep 1618347 = 2427521) B2427521
theorem B1618359 : Blo 1617007 1618359 := bstep (se 1 (by rfl) ⟨1213769, by rfl⟩ : syracuseStep 1618359 = 2427539) B2427539
theorem B1618379 : Blo 1617007 1618379 := bstep (se 1 (by rfl) ⟨1213784, by rfl⟩ : syracuseStep 1618379 = 2427569) B2427569
theorem B1618391 : Blo 1617007 1618391 := bstep (se 1 (by rfl) ⟨1213793, by rfl⟩ : syracuseStep 1618391 = 2427587) B2427587
theorem B1618411 : Blo 1617007 1618411 := bstep (se 1 (by rfl) ⟨1213808, by rfl⟩ : syracuseStep 1618411 = 2427617) B2427617
theorem B1618423 : Blo 1617007 1618423 := bstep (se 1 (by rfl) ⟨1213817, by rfl⟩ : syracuseStep 1618423 = 2427635) B2427635
theorem B1618443 : Blo 1617007 1618443 := bstep (se 1 (by rfl) ⟨1213832, by rfl⟩ : syracuseStep 1618443 = 2427665) B2427665
theorem B3641867 : Blo 1617007 3641867 := bstep (se 1 (by rfl) ⟨2731400, by rfl⟩ : syracuseStep 3641867 = 5462801) B5462801
theorem B7377425 : Blo 1617007 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B1618455 : Blo 1617007 1618455 := bstep (se 1 (by rfl) ⟨1213841, by rfl⟩ : syracuseStep 1618455 = 2427683) B2427683
theorem B1618475 : Blo 1617007 1618475 := bstep (se 1 (by rfl) ⟨1213856, by rfl⟩ : syracuseStep 1618475 = 2427713) B2427713
theorem B1618487 : Blo 1617007 1618487 := bstep (se 1 (by rfl) ⟨1213865, by rfl⟩ : syracuseStep 1618487 = 2427731) B2427731
theorem B3641921 : Blo 1617007 3641921 := bstep (se 2 (by rfl) ⟨1365720, by rfl⟩ : syracuseStep 3641921 = 2731441) B2731441
theorem B1618507 : Blo 1617007 1618507 := bstep (se 1 (by rfl) ⟨1213880, by rfl⟩ : syracuseStep 1618507 = 2427761) B2427761
theorem B1618519 : Blo 1617007 1618519 := bstep (se 1 (by rfl) ⟨1213889, by rfl⟩ : syracuseStep 1618519 = 2427779) B2427779
theorem B1618539 : Blo 1617007 1618539 := bstep (se 1 (by rfl) ⟨1213904, by rfl⟩ : syracuseStep 1618539 = 2427809) B2427809
theorem B1618551 : Blo 1617007 1618551 := bstep (se 1 (by rfl) ⟨1213913, by rfl⟩ : syracuseStep 1618551 = 2427827) B2427827
theorem B1618571 : Blo 1617007 1618571 := bstep (se 1 (by rfl) ⟨1213928, by rfl⟩ : syracuseStep 1618571 = 2427857) B2427857
theorem B1618583 : Blo 1617007 1618583 := bstep (se 1 (by rfl) ⟨1213937, by rfl⟩ : syracuseStep 1618583 = 2427875) B2427875
theorem B1618603 : Blo 1617007 1618603 := bstep (se 1 (by rfl) ⟨1213952, by rfl⟩ : syracuseStep 1618603 = 2427905) B2427905
theorem B1618615 : Blo 1617007 1618615 := bstep (se 1 (by rfl) ⟨1213961, by rfl⟩ : syracuseStep 1618615 = 2427923) B2427923
theorem B1618635 : Blo 1617007 1618635 := bstep (se 1 (by rfl) ⟨1213976, by rfl⟩ : syracuseStep 1618635 = 2427953) B2427953
theorem B12284621 : Blo 1617007 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B51188429 : Blo 1617007 51188429 := bstep (se 3 (by rfl) ⟨9597830, by rfl⟩ : syracuseStep 51188429 = 19195661) B19195661
theorem B1618647 : Blo 1617007 1618647 := bstep (se 1 (by rfl) ⟨1213985, by rfl⟩ : syracuseStep 1618647 = 2427971) B2427971
theorem B1618667 : Blo 1617007 1618667 := bstep (se 1 (by rfl) ⟨1214000, by rfl⟩ : syracuseStep 1618667 = 2428001) B2428001
theorem B3453683 : Blo 1617007 3453683 := bstep (se 1 (by rfl) ⟨2590262, by rfl⟩ : syracuseStep 3453683 = 5180525) B5180525
theorem B1618679 : Blo 1617007 1618679 := bstep (se 1 (by rfl) ⟨1214009, by rfl⟩ : syracuseStep 1618679 = 2428019) B2428019
theorem B1618699 : Blo 1617007 1618699 := bstep (se 1 (by rfl) ⟨1214024, by rfl⟩ : syracuseStep 1618699 = 2428049) B2428049
theorem B1618711 : Blo 1617007 1618711 := bstep (se 1 (by rfl) ⟨1214033, by rfl⟩ : syracuseStep 1618711 = 2428067) B2428067
theorem B3642137 : Blo 1617007 3642137 := bstep (se 2 (by rfl) ⟨1365801, by rfl⟩ : syracuseStep 3642137 = 2731603) B2731603
theorem B1618731 : Blo 1617007 1618731 := bstep (se 1 (by rfl) ⟨1214048, by rfl⟩ : syracuseStep 1618731 = 2428097) B2428097
theorem B6140717 : Blo 1617007 6140717 := bstep (se 3 (by rfl) ⟨1151384, by rfl⟩ : syracuseStep 6140717 = 2302769) B2302769
theorem B1618743 : Blo 1617007 1618743 := bstep (se 1 (by rfl) ⟨1214057, by rfl⟩ : syracuseStep 1618743 = 2428115) B2428115
theorem B9212737 : Blo 1617007 9212737 := bstep (se 2 (by rfl) ⟨3454776, by rfl⟩ : syracuseStep 9212737 = 6909553) B6909553
theorem B1618763 : Blo 1617007 1618763 := bstep (se 1 (by rfl) ⟨1214072, by rfl⟩ : syracuseStep 1618763 = 2428145) B2428145
theorem B1618775 : Blo 1617007 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B1618795 : Blo 1617007 1618795 := bstep (se 1 (by rfl) ⟨1214096, by rfl⟩ : syracuseStep 1618795 = 2428193) B2428193
theorem B3642227 : Blo 1617007 3642227 := bstep (se 1 (by rfl) ⟨2731670, by rfl⟩ : syracuseStep 3642227 = 5463341) B5463341
theorem B1618807 : Blo 1617007 1618807 := bstep (se 1 (by rfl) ⟨1214105, by rfl⟩ : syracuseStep 1618807 = 2428211) B2428211
theorem B1618827 : Blo 1617007 1618827 := bstep (se 1 (by rfl) ⟨1214120, by rfl⟩ : syracuseStep 1618827 = 2428241) B2428241
theorem B3642263 : Blo 1617007 3642263 := bstep (se 1 (by rfl) ⟨2731697, by rfl⟩ : syracuseStep 3642263 = 5463395) B5463395
theorem B1618839 : Blo 1617007 1618839 := bstep (se 1 (by rfl) ⟨1214129, by rfl⟩ : syracuseStep 1618839 = 2428259) B2428259
theorem B1618859 : Blo 1617007 1618859 := bstep (se 1 (by rfl) ⟨1214144, by rfl⟩ : syracuseStep 1618859 = 2428289) B2428289
theorem B1618871 : Blo 1617007 1618871 := bstep (se 1 (by rfl) ⟨1214153, by rfl⟩ : syracuseStep 1618871 = 2428307) B2428307
theorem B1618891 : Blo 1617007 1618891 := bstep (se 1 (by rfl) ⟨1214168, by rfl⟩ : syracuseStep 1618891 = 2428337) B2428337
theorem B1618903 : Blo 1617007 1618903 := bstep (se 1 (by rfl) ⟨1214177, by rfl⟩ : syracuseStep 1618903 = 2428355) B2428355
theorem B1618923 : Blo 1617007 1618923 := bstep (se 1 (by rfl) ⟨1214192, by rfl⟩ : syracuseStep 1618923 = 2428385) B2428385
theorem B1618935 : Blo 1617007 1618935 := bstep (se 1 (by rfl) ⟨1214201, by rfl⟩ : syracuseStep 1618935 = 2428403) B2428403
theorem B1618955 : Blo 1617007 1618955 := bstep (se 1 (by rfl) ⟨1214216, by rfl⟩ : syracuseStep 1618955 = 2428433) B2428433
theorem B1618967 : Blo 1617007 1618967 := bstep (se 1 (by rfl) ⟨1214225, by rfl⟩ : syracuseStep 1618967 = 2428451) B2428451
theorem B1618987 : Blo 1617007 1618987 := bstep (se 1 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 1618987 = 2428481) B2428481
theorem B1618999 : Blo 1617007 1618999 := bstep (se 1 (by rfl) ⟨1214249, by rfl⟩ : syracuseStep 1618999 = 2428499) B2428499
theorem B6911041 : Blo 1617007 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B3642443 : Blo 1617007 3642443 := bstep (se 1 (by rfl) ⟨2731832, by rfl⟩ : syracuseStep 3642443 = 5463665) B5463665
theorem B3642497 : Blo 1617007 3642497 := bstep (se 2 (by rfl) ⟨1365936, by rfl⟩ : syracuseStep 3642497 = 2731873) B2731873
theorem B12285107 : Blo 1617007 12285107 := bstep (se 1 (by rfl) ⟨9213830, by rfl⟩ : syracuseStep 12285107 = 18427661) B18427661
theorem B8746163 : Blo 1617007 8746163 := bstep (se 1 (by rfl) ⟨6559622, by rfl⟩ : syracuseStep 8746163 = 13119245) B13119245
theorem B4609217 : Blo 1617007 4609217 := bstep (se 2 (by rfl) ⟨1728456, by rfl⟩ : syracuseStep 4609217 = 3456913) B3456913
theorem B5182667 : Blo 1617007 5182667 := bstep (se 1 (by rfl) ⟨3887000, by rfl⟩ : syracuseStep 5182667 = 7774001) B7774001
theorem B6558937 : Blo 1617007 6558937 := bstep (se 2 (by rfl) ⟨2459601, by rfl⟩ : syracuseStep 6558937 = 4919203) B4919203
theorem B23655685 : Blo 1617007 23655685 := bstep (se 4 (by rfl) ⟨2217720, by rfl⟩ : syracuseStep 23655685 = 4435441) B4435441
theorem B4609331 : Blo 1617007 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B3642713 : Blo 1617007 3642713 := bstep (se 2 (by rfl) ⟨1366017, by rfl⟩ : syracuseStep 3642713 = 2732035) B2732035
theorem B13120861 : Blo 1617007 13120861 := bstep (se 3 (by rfl) ⟨2460161, by rfl⟩ : syracuseStep 13120861 = 4920323) B4920323
theorem B11064707 : Blo 1617007 11064707 := bstep (se 1 (by rfl) ⟨8298530, by rfl⟩ : syracuseStep 11064707 = 16597061) B16597061
theorem B5461451 : Blo 1617007 5461451 := bstep (se 1 (by rfl) ⟨4096088, by rfl⟩ : syracuseStep 5461451 = 8192177) B8192177
theorem B6141491 : Blo 1617007 6141491 := bstep (se 1 (by rfl) ⟨4606118, by rfl⟩ : syracuseStep 6141491 = 9212237) B9212237
theorem B13825667 : Blo 1617007 13825667 := bstep (se 1 (by rfl) ⟨10369250, by rfl⟩ : syracuseStep 13825667 = 20738501) B20738501
theorem B6911639 : Blo 1617007 6911639 := bstep (se 1 (by rfl) ⟨5183729, by rfl⟩ : syracuseStep 6911639 = 10367459) B10367459
theorem B4920983 : Blo 1617007 4920983 := bstep (se 1 (by rfl) ⟨3690737, by rfl⟩ : syracuseStep 4920983 = 7381475) B7381475
theorem B5461721 : Blo 1617007 5461721 := bstep (se 2 (by rfl) ⟨2048145, by rfl⟩ : syracuseStep 5461721 = 4096291) B4096291
theorem B7378733 : Blo 1617007 7378733 := bstep (se 3 (by rfl) ⟨1383512, by rfl⟩ : syracuseStep 7378733 = 2767025) B2767025
theorem B4094003 : Blo 1617007 4094003 := bstep (se 1 (by rfl) ⟨3070502, by rfl⟩ : syracuseStep 4094003 = 6141005) B6141005
theorem B5830859 : Blo 1617007 5830859 := bstep (se 1 (by rfl) ⟨4373144, by rfl⟩ : syracuseStep 5830859 = 8746289) B8746289
theorem B44308741 : Blo 1617007 44308741 := bstep (se 4 (by rfl) ⟨4153944, by rfl⟩ : syracuseStep 44308741 = 8307889) B8307889
theorem B3455255 : Blo 1617007 3455255 := bstep (se 1 (by rfl) ⟨2591441, by rfl⟩ : syracuseStep 3455255 = 5182883) B5182883
theorem B1751339 : Blo 1617007 1751339 := bstep (se 1 (by rfl) ⟨1313504, by rfl⟩ : syracuseStep 1751339 = 2627009) B2627009
theorem B5536075 : Blo 1617007 5536075 := bstep (se 1 (by rfl) ⟨4152056, by rfl⟩ : syracuseStep 5536075 = 8304113) B8304113
theorem B4094297 : Blo 1617007 4094297 := bstep (se 2 (by rfl) ⟨1535361, by rfl⟩ : syracuseStep 4094297 = 3070723) B3070723
theorem B1726859 : Blo 1617007 1726859 := bstep (se 1 (by rfl) ⟨1295144, by rfl⟩ : syracuseStep 1726859 = 2590289) B2590289
theorem B5462423 : Blo 1617007 5462423 := bstep (se 1 (by rfl) ⟨4096817, by rfl⟩ : syracuseStep 5462423 = 8193635) B8193635
theorem B5912983 : Blo 1617007 5912983 := bstep (se 1 (by rfl) ⟨4434737, by rfl⟩ : syracuseStep 5912983 = 8869475) B8869475
theorem B10795481 : Blo 1617007 10795481 := bstep (se 2 (by rfl) ⟨4048305, by rfl⟩ : syracuseStep 10795481 = 8096611) B8096611
theorem B1751563 : Blo 1617007 1751563 := bstep (se 1 (by rfl) ⟨1313672, by rfl⟩ : syracuseStep 1751563 = 2627345) B2627345
theorem B3070487 : Blo 1617007 3070487 := bstep (se 1 (by rfl) ⟨2302865, by rfl⟩ : syracuseStep 3070487 = 4605731) B4605731
theorem B3455563 : Blo 1617007 3455563 := bstep (se 1 (by rfl) ⟨2591672, by rfl⟩ : syracuseStep 3455563 = 5183345) B5183345
theorem B8190557 : Blo 1617007 8190557 := bstep (se 3 (by rfl) ⟨1535729, by rfl⟩ : syracuseStep 8190557 = 3071459) B3071459
theorem B12286565 : Blo 1617007 12286565 := bstep (se 4 (by rfl) ⟨1151865, by rfl⟩ : syracuseStep 12286565 = 2303731) B2303731
theorem B50502341 : Blo 1617007 50502341 := bstep (se 4 (by rfl) ⟨4734594, by rfl⟩ : syracuseStep 50502341 = 9469189) B9469189
theorem B29530925 : Blo 1617007 29530925 := bstep (se 3 (by rfl) ⟨5537048, by rfl⟩ : syracuseStep 29530925 = 11074097) B11074097
theorem B5913395 : Blo 1617007 5913395 := bstep (se 1 (by rfl) ⟨4435046, by rfl⟩ : syracuseStep 5913395 = 8870093) B8870093
theorem B5462963 : Blo 1617007 5462963 := bstep (se 1 (by rfl) ⟨4097222, by rfl⟩ : syracuseStep 5462963 = 8194445) B8194445
theorem B6912971 : Blo 1617007 6912971 := bstep (se 1 (by rfl) ⟨5184728, by rfl⟩ : syracuseStep 6912971 = 10369457) B10369457
theorem B6142979 : Blo 1617007 6142979 := bstep (se 1 (by rfl) ⟨4607234, by rfl⟩ : syracuseStep 6142979 = 9214469) B9214469
theorem B66419747 : Blo 1617007 66419747 := bstep (se 1 (by rfl) ⟨49814810, by rfl⟩ : syracuseStep 66419747 = 99629621) B99629621
theorem B3071027 : Blo 1617007 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B12287051 : Blo 1617007 12287051 := bstep (se 1 (by rfl) ⟨9215288, by rfl⟩ : syracuseStep 12287051 = 18430577) B18430577
theorem B5463233 : Blo 1617007 5463233 := bstep (se 2 (by rfl) ⟨2048712, by rfl⟩ : syracuseStep 5463233 = 4097425) B4097425
theorem B6143435 : Blo 1617007 6143435 := bstep (se 1 (by rfl) ⟨4607576, by rfl⟩ : syracuseStep 6143435 = 9215153) B9215153
theorem B2047447 : Blo 1617007 2047447 := bstep (se 1 (by rfl) ⟨1535585, by rfl⟩ : syracuseStep 2047447 = 3071171) B3071171
theorem B5184985 : Blo 1617007 5184985 := bstep (se 2 (by rfl) ⟨1944369, by rfl⟩ : syracuseStep 5184985 = 3888739) B3888739
theorem B3071513 : Blo 1617007 3071513 := bstep (se 2 (by rfl) ⟨1151817, by rfl⟩ : syracuseStep 3071513 = 2303635) B2303635
theorem B1728055 : Blo 1617007 1728055 := bstep (se 1 (by rfl) ⟨1296041, by rfl⟩ : syracuseStep 1728055 = 2592083) B2592083
theorem B20725379 : Blo 1617007 20725379 := bstep (se 1 (by rfl) ⟨15544034, by rfl⟩ : syracuseStep 20725379 = 31088069) B31088069
theorem B6143633 : Blo 1617007 6143633 := bstep (se 2 (by rfl) ⟨2303862, by rfl⟩ : syracuseStep 6143633 = 4607725) B4607725
theorem B5463773 : Blo 1617007 5463773 := bstep (se 3 (by rfl) ⟨1024457, by rfl⟩ : syracuseStep 5463773 = 2048915) B2048915
theorem B3456793 : Blo 1617007 3456793 := bstep (se 2 (by rfl) ⟨1296297, by rfl⟩ : syracuseStep 3456793 = 2592595) B2592595
theorem B1728311 : Blo 1617007 1728311 := bstep (se 1 (by rfl) ⟨1296233, by rfl⟩ : syracuseStep 1728311 = 2592467) B2592467
theorem B10370891 : Blo 1617007 10370891 := bstep (se 1 (by rfl) ⟨7778168, by rfl⟩ : syracuseStep 10370891 = 15556337) B15556337
theorem B3112843 : Blo 1617007 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B4095947 : Blo 1617007 4095947 := bstep (se 1 (by rfl) ⟨3071960, by rfl⟩ : syracuseStep 4095947 = 6143921) B6143921
theorem B12288023 : Blo 1617007 12288023 := bstep (se 1 (by rfl) ⟨9216017, by rfl⟩ : syracuseStep 12288023 = 18432035) B18432035
theorem B4669483 : Blo 1617007 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B5464151 : Blo 1617007 5464151 := bstep (se 1 (by rfl) ⟨4098113, by rfl⟩ : syracuseStep 5464151 = 8196227) B8196227
theorem B6144119 : Blo 1617007 6144119 := bstep (se 1 (by rfl) ⟨4608089, by rfl⟩ : syracuseStep 6144119 = 9216179) B9216179
theorem B118022345 : Blo 1617007 118022345 := bstep (se 2 (by rfl) ⟨44258379, by rfl⟩ : syracuseStep 118022345 = 88516759) B88516759
theorem B4096271 : Blo 1617007 4096271 := bstep (se 1 (by rfl) ⟨3072203, by rfl⟩ : syracuseStep 4096271 = 6144407) B6144407
theorem B4096403 : Blo 1617007 4096403 := bstep (se 1 (by rfl) ⟨3072302, by rfl⟩ : syracuseStep 4096403 = 6144605) B6144605
theorem B19939769 : Blo 1617007 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B7381433 : Blo 1617007 7381433 := bstep (se 2 (by rfl) ⟨2768037, by rfl⟩ : syracuseStep 7381433 = 5536075) B5536075
theorem B3457579 : Blo 1617007 3457579 := bstep (se 1 (by rfl) ⟨2593184, by rfl⟩ : syracuseStep 3457579 = 5186369) B5186369
theorem B2048647 : Blo 1617007 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B2425529 : Blo 1617007 2425529 := bstep (se 2 (by rfl) ⟨909573, by rfl⟩ : syracuseStep 2425529 = 1819147) B1819147
theorem B2425607 : Blo 1617007 2425607 := bstep (se 1 (by rfl) ⟨1819205, by rfl⟩ : syracuseStep 2425607 = 3638411) B3638411
theorem B1819399 : Blo 1617007 1819399 := bstep (se 1 (by rfl) ⟨1364549, by rfl⟩ : syracuseStep 1819399 = 2729099) B2729099
theorem B4604683 : Blo 1617007 4604683 := bstep (se 1 (by rfl) ⟨3453512, by rfl⟩ : syracuseStep 4604683 = 6907025) B6907025
theorem B4670237 : Blo 1617007 4670237 := bstep (se 3 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 4670237 = 1751339) B1751339
theorem B2425643 : Blo 1617007 2425643 := bstep (se 1 (by rfl) ⟨1819232, by rfl⟩ : syracuseStep 2425643 = 3638465) B3638465
theorem B3072811 : Blo 1617007 3072811 := bstep (se 1 (by rfl) ⟨2304608, by rfl⟩ : syracuseStep 3072811 = 4609217) B4609217
theorem B2425673 : Blo 1617007 2425673 := bstep (se 2 (by rfl) ⟨909627, by rfl⟩ : syracuseStep 2425673 = 1819255) B1819255
theorem B3072887 : Blo 1617007 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B2425787 : Blo 1617007 2425787 := bstep (se 1 (by rfl) ⟨1819340, by rfl⟩ : syracuseStep 2425787 = 3638681) B3638681
theorem B1819579 : Blo 1617007 1819579 := bstep (se 1 (by rfl) ⟨1364684, by rfl⟩ : syracuseStep 1819579 = 2729369) B2729369
theorem B2425847 : Blo 1617007 2425847 := bstep (se 1 (by rfl) ⟨1819385, by rfl⟩ : syracuseStep 2425847 = 3638771) B3638771
theorem B2425871 : Blo 1617007 2425871 := bstep (se 1 (by rfl) ⟨1819403, by rfl⟩ : syracuseStep 2425871 = 3638807) B3638807
theorem B4604957 : Blo 1617007 4604957 := bstep (se 3 (by rfl) ⟨863429, by rfl⟩ : syracuseStep 4604957 = 1726859) B1726859
theorem B2425913 : Blo 1617007 2425913 := bstep (se 2 (by rfl) ⟨909717, by rfl⟩ : syracuseStep 2425913 = 1819435) B1819435
theorem B6145091 : Blo 1617007 6145091 := bstep (se 1 (by rfl) ⟨4608818, by rfl⟩ : syracuseStep 6145091 = 9217637) B9217637
theorem B9217111 : Blo 1617007 9217111 := bstep (se 1 (by rfl) ⟨6912833, by rfl⟩ : syracuseStep 9217111 = 13825667) B13825667
theorem B34980997 : Blo 1617007 34980997 := bstep (se 4 (by rfl) ⟨3279468, by rfl⟩ : syracuseStep 34980997 = 6558937) B6558937
theorem B2425991 : Blo 1617007 2425991 := bstep (se 1 (by rfl) ⟨1819493, by rfl⟩ : syracuseStep 2425991 = 3638987) B3638987
theorem B2426027 : Blo 1617007 2426027 := bstep (se 1 (by rfl) ⟨1819520, by rfl⟩ : syracuseStep 2426027 = 3639041) B3639041
theorem B2426057 : Blo 1617007 2426057 := bstep (se 2 (by rfl) ⟨909771, by rfl⟩ : syracuseStep 2426057 = 1819543) B1819543
theorem B2426171 : Blo 1617007 2426171 := bstep (se 1 (by rfl) ⟨1819628, by rfl⟩ : syracuseStep 2426171 = 3639257) B3639257
theorem B4605299 : Blo 1617007 4605299 := bstep (se 1 (by rfl) ⟨3453974, by rfl⟩ : syracuseStep 4605299 = 6907949) B6907949
theorem B2729335 : Blo 1617007 2729335 := bstep (se 1 (by rfl) ⟨2047001, by rfl⟩ : syracuseStep 2729335 = 4094003) B4094003
theorem B2426231 : Blo 1617007 2426231 := bstep (se 1 (by rfl) ⟨1819673, by rfl⟩ : syracuseStep 2426231 = 3639347) B3639347
theorem B3638663 : Blo 1617007 3638663 := bstep (se 1 (by rfl) ⟨2728997, by rfl⟩ : syracuseStep 3638663 = 5457995) B5457995
theorem B5834119 : Blo 1617007 5834119 := bstep (se 1 (by rfl) ⟨4375589, by rfl⟩ : syracuseStep 5834119 = 8751179) B8751179
theorem B2426255 : Blo 1617007 2426255 := bstep (se 1 (by rfl) ⟨1819691, by rfl⟩ : syracuseStep 2426255 = 3639383) B3639383
theorem B1820047 : Blo 1617007 1820047 := bstep (se 1 (by rfl) ⟨1365035, by rfl⟩ : syracuseStep 1820047 = 2730071) B2730071
theorem B2426297 : Blo 1617007 2426297 := bstep (se 2 (by rfl) ⟨909861, by rfl⟩ : syracuseStep 2426297 = 1819723) B1819723
theorem B4097537 : Blo 1617007 4097537 := bstep (se 2 (by rfl) ⟨1536576, by rfl⟩ : syracuseStep 4097537 = 3073153) B3073153
theorem B2426375 : Blo 1617007 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B2426411 : Blo 1617007 2426411 := bstep (se 1 (by rfl) ⟨1819808, by rfl⟩ : syracuseStep 2426411 = 3639617) B3639617
theorem B3638843 : Blo 1617007 3638843 := bstep (se 1 (by rfl) ⟨2729132, by rfl⟩ : syracuseStep 3638843 = 5458265) B5458265
theorem B2729531 : Blo 1617007 2729531 := bstep (se 1 (by rfl) ⟨2047148, by rfl⟩ : syracuseStep 2729531 = 4094297) B4094297
theorem B2426441 : Blo 1617007 2426441 := bstep (se 2 (by rfl) ⟨909915, by rfl⟩ : syracuseStep 2426441 = 1819831) B1819831
theorem B2590327 : Blo 1617007 2590327 := bstep (se 1 (by rfl) ⟨1942745, by rfl⟩ : syracuseStep 2590327 = 3885491) B3885491
theorem B31540913 : Blo 1617007 31540913 := bstep (se 2 (by rfl) ⟨11827842, by rfl⟩ : syracuseStep 31540913 = 23655685) B23655685
theorem B3638969 : Blo 1617007 3638969 := bstep (se 2 (by rfl) ⟨1364613, by rfl⟩ : syracuseStep 3638969 = 2729227) B2729227
theorem B2426555 : Blo 1617007 2426555 := bstep (se 1 (by rfl) ⟨1819916, by rfl⟩ : syracuseStep 2426555 = 3639833) B3639833
theorem B2426615 : Blo 1617007 2426615 := bstep (se 1 (by rfl) ⟨1819961, by rfl⟩ : syracuseStep 2426615 = 3639923) B3639923
theorem B20743937 : Blo 1617007 20743937 := bstep (se 2 (by rfl) ⟨7778976, by rfl⟩ : syracuseStep 20743937 = 15557953) B15557953
theorem B2426639 : Blo 1617007 2426639 := bstep (se 1 (by rfl) ⟨1819979, by rfl⟩ : syracuseStep 2426639 = 3639959) B3639959
theorem B2426681 : Blo 1617007 2426681 := bstep (se 2 (by rfl) ⟨910005, by rfl⟩ : syracuseStep 2426681 = 1820011) B1820011
theorem B4736855 : Blo 1617007 4736855 := bstep (se 1 (by rfl) ⟨3552641, by rfl⟩ : syracuseStep 4736855 = 7105283) B7105283
theorem B5457779 : Blo 1617007 5457779 := bstep (se 1 (by rfl) ⟨4093334, by rfl⟩ : syracuseStep 5457779 = 8186669) B8186669
theorem B19687283 : Blo 1617007 19687283 := bstep (se 1 (by rfl) ⟨14765462, by rfl⟩ : syracuseStep 19687283 = 29530925) B29530925
theorem B3942263 : Blo 1617007 3942263 := bstep (se 1 (by rfl) ⟨2956697, by rfl⟩ : syracuseStep 3942263 = 5913395) B5913395
theorem B4097911 : Blo 1617007 4097911 := bstep (se 1 (by rfl) ⟨3073433, by rfl⟩ : syracuseStep 4097911 = 6146867) B6146867
theorem B2426759 : Blo 1617007 2426759 := bstep (se 1 (by rfl) ⟨1820069, by rfl⟩ : syracuseStep 2426759 = 3640139) B3640139
theorem B1820551 : Blo 1617007 1820551 := bstep (se 1 (by rfl) ⟨1365413, by rfl⟩ : syracuseStep 1820551 = 2730827) B2730827
theorem B13830041 : Blo 1617007 13830041 := bstep (se 2 (by rfl) ⟨5186265, by rfl⟩ : syracuseStep 13830041 = 10372531) B10372531
theorem B2426795 : Blo 1617007 2426795 := bstep (se 1 (by rfl) ⟨1820096, by rfl⟩ : syracuseStep 2426795 = 3640193) B3640193
theorem B2729929 : Blo 1617007 2729929 := bstep (se 2 (by rfl) ⟨1023723, by rfl⟩ : syracuseStep 2729929 = 2047447) B2047447
theorem B2426825 : Blo 1617007 2426825 := bstep (se 2 (by rfl) ⟨910059, by rfl⟩ : syracuseStep 2426825 = 1820119) B1820119
theorem B9209821 : Blo 1617007 9209821 := bstep (se 3 (by rfl) ⟨1726841, by rfl⟩ : syracuseStep 9209821 = 3453683) B3453683
theorem B3639311 : Blo 1617007 3639311 := bstep (se 1 (by rfl) ⟨2729483, by rfl⟩ : syracuseStep 3639311 = 5458967) B5458967
theorem B51185681 : Blo 1617007 51185681 := bstep (se 2 (by rfl) ⟨19194630, by rfl⟩ : syracuseStep 51185681 = 38389261) B38389261
theorem B44279831 : Blo 1617007 44279831 := bstep (se 1 (by rfl) ⟨33209873, by rfl⟩ : syracuseStep 44279831 = 66419747) B66419747
theorem B6146077 : Blo 1617007 6146077 := bstep (se 3 (by rfl) ⟨1152389, by rfl⟩ : syracuseStep 6146077 = 2304779) B2304779
theorem B3639329 : Blo 1617007 3639329 := bstep (se 2 (by rfl) ⟨1364748, by rfl⟩ : syracuseStep 3639329 = 2729497) B2729497
theorem B2426939 : Blo 1617007 2426939 := bstep (se 1 (by rfl) ⟨1820204, by rfl⟩ : syracuseStep 2426939 = 3640409) B3640409
theorem B1820731 : Blo 1617007 1820731 := bstep (se 1 (by rfl) ⟨1365548, by rfl⟩ : syracuseStep 1820731 = 2731097) B2731097
theorem B2304073 : Blo 1617007 2304073 := bstep (se 2 (by rfl) ⟨864027, by rfl⟩ : syracuseStep 2304073 = 1728055) B1728055
theorem B2426999 : Blo 1617007 2426999 := bstep (se 1 (by rfl) ⟨1820249, by rfl⟩ : syracuseStep 2426999 = 3640499) B3640499
theorem B2427023 : Blo 1617007 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B2427065 : Blo 1617007 2427065 := bstep (se 2 (by rfl) ⟨910149, by rfl⟩ : syracuseStep 2427065 = 1820299) B1820299
theorem B2427143 : Blo 1617007 2427143 := bstep (se 1 (by rfl) ⟨1820357, by rfl⟩ : syracuseStep 2427143 = 3640715) B3640715
theorem B2427179 : Blo 1617007 2427179 := bstep (se 1 (by rfl) ⟨1820384, by rfl⟩ : syracuseStep 2427179 = 3640769) B3640769
theorem B4606267 : Blo 1617007 4606267 := bstep (se 1 (by rfl) ⟨3454700, by rfl⟩ : syracuseStep 4606267 = 6909401) B6909401
theorem B2427209 : Blo 1617007 2427209 := bstep (se 2 (by rfl) ⟨910203, by rfl⟩ : syracuseStep 2427209 = 1820407) B1820407
theorem B3639671 : Blo 1617007 3639671 := bstep (se 1 (by rfl) ⟨2729753, by rfl⟩ : syracuseStep 3639671 = 5459507) B5459507
theorem B2427323 : Blo 1617007 2427323 := bstep (se 1 (by rfl) ⟨1820492, by rfl⟩ : syracuseStep 2427323 = 3640985) B3640985
theorem B2427383 : Blo 1617007 2427383 := bstep (se 1 (by rfl) ⟨1820537, by rfl⟩ : syracuseStep 2427383 = 3641075) B3641075
theorem B2427407 : Blo 1617007 2427407 := bstep (se 1 (by rfl) ⟨1820555, by rfl⟩ : syracuseStep 2427407 = 3641111) B3641111
theorem B1821199 : Blo 1617007 1821199 := bstep (se 1 (by rfl) ⟨1365899, by rfl⟩ : syracuseStep 1821199 = 2731799) B2731799
theorem B3639851 : Blo 1617007 3639851 := bstep (se 1 (by rfl) ⟨2729888, by rfl⟩ : syracuseStep 3639851 = 5459777) B5459777
theorem B2427449 : Blo 1617007 2427449 := bstep (se 2 (by rfl) ⟨910293, by rfl⟩ : syracuseStep 2427449 = 1820587) B1820587
theorem B53217911 : Blo 1617007 53217911 := bstep (se 1 (by rfl) ⟨39913433, by rfl⟩ : syracuseStep 53217911 = 79826867) B79826867
theorem B2730631 : Blo 1617007 2730631 := bstep (se 1 (by rfl) ⟨2047973, by rfl⟩ : syracuseStep 2730631 = 4095947) B4095947
theorem B2427527 : Blo 1617007 2427527 := bstep (se 1 (by rfl) ⟨1820645, by rfl⟩ : syracuseStep 2427527 = 3641291) B3641291
theorem B2427563 : Blo 1617007 2427563 := bstep (se 1 (by rfl) ⟨1820672, by rfl⟩ : syracuseStep 2427563 = 3641345) B3641345
theorem B2427593 : Blo 1617007 2427593 := bstep (se 2 (by rfl) ⟨910347, by rfl⟩ : syracuseStep 2427593 = 1820695) B1820695
theorem B9341669 : Blo 1617007 9341669 := bstep (se 4 (by rfl) ⟨875781, by rfl⟩ : syracuseStep 9341669 = 1751563) B1751563
theorem B6228737 : Blo 1617007 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B31591205 : Blo 1617007 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B2427707 : Blo 1617007 2427707 := bstep (se 1 (by rfl) ⟨1820780, by rfl⟩ : syracuseStep 2427707 = 3641561) B3641561
theorem B28396403 : Blo 1617007 28396403 := bstep (se 1 (by rfl) ⟨21297302, by rfl⟩ : syracuseStep 28396403 = 42594605) B42594605
theorem B8194931 : Blo 1617007 8194931 := bstep (se 1 (by rfl) ⟨6146198, by rfl⟩ : syracuseStep 8194931 = 12292397) B12292397
theorem B2427767 : Blo 1617007 2427767 := bstep (se 1 (by rfl) ⟨1820825, by rfl⟩ : syracuseStep 2427767 = 3641651) B3641651
theorem B3689351 : Blo 1617007 3689351 := bstep (se 1 (by rfl) ⟨2767013, by rfl⟩ : syracuseStep 3689351 = 5534027) B5534027
theorem B2427791 : Blo 1617007 2427791 := bstep (se 1 (by rfl) ⟨1820843, by rfl⟩ : syracuseStep 2427791 = 3641687) B3641687
theorem B3640211 : Blo 1617007 3640211 := bstep (se 1 (by rfl) ⟨2730158, by rfl⟩ : syracuseStep 3640211 = 5460317) B5460317
theorem B15543191 : Blo 1617007 15543191 := bstep (se 1 (by rfl) ⟨11657393, by rfl⟩ : syracuseStep 15543191 = 23314787) B23314787
theorem B2427833 : Blo 1617007 2427833 := bstep (se 2 (by rfl) ⟨910437, by rfl⟩ : syracuseStep 2427833 = 1820875) B1820875
theorem B3640265 : Blo 1617007 3640265 := bstep (se 2 (by rfl) ⟨1365099, by rfl⟩ : syracuseStep 3640265 = 2730199) B2730199
theorem B15559685 : Blo 1617007 15559685 := bstep (se 4 (by rfl) ⟨1458720, by rfl⟩ : syracuseStep 15559685 = 2917441) B2917441
theorem B2427911 : Blo 1617007 2427911 := bstep (se 1 (by rfl) ⟨1820933, by rfl⟩ : syracuseStep 2427911 = 3641867) B3641867
theorem B4918283 : Blo 1617007 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B6908939 : Blo 1617007 6908939 := bstep (se 1 (by rfl) ⟨5181704, by rfl⟩ : syracuseStep 6908939 = 10363409) B10363409
theorem B9219095 : Blo 1617007 9219095 := bstep (se 1 (by rfl) ⟨6914321, by rfl⟩ : syracuseStep 9219095 = 13828643) B13828643
theorem B2427947 : Blo 1617007 2427947 := bstep (se 1 (by rfl) ⟨1820960, by rfl⟩ : syracuseStep 2427947 = 3641921) B3641921
theorem B2427977 : Blo 1617007 2427977 := bstep (se 2 (by rfl) ⟨910491, by rfl⟩ : syracuseStep 2427977 = 1820983) B1820983
theorem B1617031 : Blo 1617007 1617031 := bstep (se 1 (by rfl) ⟨1212773, by rfl⟩ : syracuseStep 1617031 = 2425547) B2425547
theorem B1617039 : Blo 1617007 1617039 := bstep (se 1 (by rfl) ⟨1212779, by rfl⟩ : syracuseStep 1617039 = 2425559) B2425559
theorem B2591929 : Blo 1617007 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B1617083 : Blo 1617007 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B2428091 : Blo 1617007 2428091 := bstep (se 1 (by rfl) ⟨1821068, by rfl⟩ : syracuseStep 2428091 = 3642137) B3642137
theorem B2428151 : Blo 1617007 2428151 := bstep (se 1 (by rfl) ⟨1821113, by rfl⟩ : syracuseStep 2428151 = 3642227) B3642227
theorem B1617159 : Blo 1617007 1617159 := bstep (se 1 (by rfl) ⟨1212869, by rfl⟩ : syracuseStep 1617159 = 2425739) B2425739
theorem B1617167 : Blo 1617007 1617167 := bstep (se 1 (by rfl) ⟨1212875, by rfl⟩ : syracuseStep 1617167 = 2425751) B2425751
theorem B2731279 : Blo 1617007 2731279 := bstep (se 1 (by rfl) ⟨2048459, by rfl⟩ : syracuseStep 2731279 = 4096919) B4096919
theorem B2428175 : Blo 1617007 2428175 := bstep (se 1 (by rfl) ⟨1821131, by rfl⟩ : syracuseStep 2428175 = 3642263) B3642263
theorem B2428217 : Blo 1617007 2428217 := bstep (se 2 (by rfl) ⟨910581, by rfl⟩ : syracuseStep 2428217 = 1821163) B1821163
theorem B1617211 : Blo 1617007 1617211 := bstep (se 1 (by rfl) ⟨1212908, by rfl⟩ : syracuseStep 1617211 = 2425817) B2425817
theorem B8195417 : Blo 1617007 8195417 := bstep (se 2 (by rfl) ⟨3073281, by rfl⟩ : syracuseStep 8195417 = 6146563) B6146563
theorem B1617287 : Blo 1617007 1617287 := bstep (se 1 (by rfl) ⟨1212965, by rfl⟩ : syracuseStep 1617287 = 2425931) B2425931
theorem B2428295 : Blo 1617007 2428295 := bstep (se 1 (by rfl) ⟨1821221, by rfl⟩ : syracuseStep 2428295 = 3642443) B3642443
theorem B1617295 : Blo 1617007 1617295 := bstep (se 1 (by rfl) ⟨1212971, by rfl⟩ : syracuseStep 1617295 = 2425943) B2425943
theorem B2428331 : Blo 1617007 2428331 := bstep (se 1 (by rfl) ⟨1821248, by rfl⟩ : syracuseStep 2428331 = 3642497) B3642497
theorem B4607417 : Blo 1617007 4607417 := bstep (se 2 (by rfl) ⟨1727781, by rfl⟩ : syracuseStep 4607417 = 3455563) B3455563
theorem B1617339 : Blo 1617007 1617339 := bstep (se 1 (by rfl) ⟨1213004, by rfl⟩ : syracuseStep 1617339 = 2426009) B2426009
theorem B2428361 : Blo 1617007 2428361 := bstep (se 2 (by rfl) ⟨910635, by rfl⟩ : syracuseStep 2428361 = 1821271) B1821271
theorem B1617415 : Blo 1617007 1617415 := bstep (se 1 (by rfl) ⟨1213061, by rfl⟩ : syracuseStep 1617415 = 2426123) B2426123
theorem B1617423 : Blo 1617007 1617423 := bstep (se 1 (by rfl) ⟨1213067, by rfl⟩ : syracuseStep 1617423 = 2426135) B2426135
theorem B14003741 : Blo 1617007 14003741 := bstep (se 3 (by rfl) ⟨2625701, by rfl⟩ : syracuseStep 14003741 = 5251403) B5251403
theorem B1617467 : Blo 1617007 1617467 := bstep (se 1 (by rfl) ⟨1213100, by rfl⟩ : syracuseStep 1617467 = 2426201) B2426201
theorem B2428475 : Blo 1617007 2428475 := bstep (se 1 (by rfl) ⟨1821356, by rfl⟩ : syracuseStep 2428475 = 3642713) B3642713
theorem B7376471 : Blo 1617007 7376471 := bstep (se 1 (by rfl) ⟨5532353, by rfl⟩ : syracuseStep 7376471 = 11064707) B11064707
theorem B8187479 : Blo 1617007 8187479 := bstep (se 1 (by rfl) ⟨6140609, by rfl⟩ : syracuseStep 8187479 = 12281219) B12281219
theorem B1617543 : Blo 1617007 1617543 := bstep (se 1 (by rfl) ⟨1213157, by rfl⟩ : syracuseStep 1617543 = 2426315) B2426315
theorem B3640967 : Blo 1617007 3640967 := bstep (se 1 (by rfl) ⟨2730725, by rfl⟩ : syracuseStep 3640967 = 5461451) B5461451
theorem B1617551 : Blo 1617007 1617551 := bstep (se 1 (by rfl) ⟨1213163, by rfl⟩ : syracuseStep 1617551 = 2426327) B2426327
theorem B1617595 : Blo 1617007 1617595 := bstep (se 1 (by rfl) ⟨1213196, by rfl⟩ : syracuseStep 1617595 = 2426393) B2426393
theorem B12283649 : Blo 1617007 12283649 := bstep (se 2 (by rfl) ⟨4606368, by rfl⟩ : syracuseStep 12283649 = 9212737) B9212737
theorem B1617671 : Blo 1617007 1617671 := bstep (se 1 (by rfl) ⟨1213253, by rfl⟩ : syracuseStep 1617671 = 2426507) B2426507
theorem B1617679 : Blo 1617007 1617679 := bstep (se 1 (by rfl) ⟨1213259, by rfl⟩ : syracuseStep 1617679 = 2426519) B2426519
theorem B4607759 : Blo 1617007 4607759 := bstep (se 1 (by rfl) ⟨3455819, by rfl⟩ : syracuseStep 4607759 = 6911639) B6911639
theorem B3280655 : Blo 1617007 3280655 := bstep (se 1 (by rfl) ⟨2460491, by rfl⟩ : syracuseStep 3280655 = 4920983) B4920983
theorem B2731819 : Blo 1617007 2731819 := bstep (se 1 (by rfl) ⟨2048864, by rfl⟩ : syracuseStep 2731819 = 4097729) B4097729
theorem B1617723 : Blo 1617007 1617723 := bstep (se 1 (by rfl) ⟨1213292, by rfl⟩ : syracuseStep 1617723 = 2426585) B2426585
theorem B3641147 : Blo 1617007 3641147 := bstep (se 1 (by rfl) ⟨2730860, by rfl⟩ : syracuseStep 3641147 = 5461721) B5461721
theorem B31108981 : Blo 1617007 31108981 := bstep (se 5 (by rfl) ⟨1458233, by rfl⟩ : syracuseStep 31108981 = 2916467) B2916467
theorem B1617799 : Blo 1617007 1617799 := bstep (se 1 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 1617799 = 2426699) B2426699
theorem B1617807 : Blo 1617007 1617807 := bstep (se 1 (by rfl) ⟨1213355, by rfl⟩ : syracuseStep 1617807 = 2426711) B2426711
theorem B3641273 : Blo 1617007 3641273 := bstep (se 2 (by rfl) ⟨1365477, by rfl⟩ : syracuseStep 3641273 = 2730955) B2730955
theorem B2731961 : Blo 1617007 2731961 := bstep (se 2 (by rfl) ⟨1024485, by rfl⟩ : syracuseStep 2731961 = 2048971) B2048971
theorem B1617851 : Blo 1617007 1617851 := bstep (se 1 (by rfl) ⟨1213388, by rfl⟩ : syracuseStep 1617851 = 2426777) B2426777
theorem B1617927 : Blo 1617007 1617927 := bstep (se 1 (by rfl) ⟨1213445, by rfl⟩ : syracuseStep 1617927 = 2426891) B2426891
theorem B1617935 : Blo 1617007 1617935 := bstep (se 1 (by rfl) ⟨1213451, by rfl⟩ : syracuseStep 1617935 = 2426903) B2426903
theorem B1617979 : Blo 1617007 1617979 := bstep (se 1 (by rfl) ⟨1213484, by rfl⟩ : syracuseStep 1617979 = 2426969) B2426969
theorem B8187965 : Blo 1617007 8187965 := bstep (se 3 (by rfl) ⟨1535243, by rfl⟩ : syracuseStep 8187965 = 3070487) B3070487
theorem B3887239 : Blo 1617007 3887239 := bstep (se 1 (by rfl) ⟨2915429, by rfl⟩ : syracuseStep 3887239 = 5830859) B5830859
theorem B1618055 : Blo 1617007 1618055 := bstep (se 1 (by rfl) ⟨1213541, by rfl⟩ : syracuseStep 1618055 = 2427083) B2427083
theorem B1618063 : Blo 1617007 1618063 := bstep (se 1 (by rfl) ⟨1213547, by rfl⟩ : syracuseStep 1618063 = 2427095) B2427095
theorem B1618107 : Blo 1617007 1618107 := bstep (se 1 (by rfl) ⟨1213580, by rfl⟩ : syracuseStep 1618107 = 2427161) B2427161
theorem B9834689 : Blo 1617007 9834689 := bstep (se 2 (by rfl) ⟨3688008, by rfl⟩ : syracuseStep 9834689 = 7376017) B7376017
theorem B5181641 : Blo 1617007 5181641 := bstep (se 2 (by rfl) ⟨1943115, by rfl⟩ : syracuseStep 5181641 = 3886231) B3886231
theorem B1618183 : Blo 1617007 1618183 := bstep (se 1 (by rfl) ⟨1213637, by rfl⟩ : syracuseStep 1618183 = 2427275) B2427275
theorem B1618191 : Blo 1617007 1618191 := bstep (se 1 (by rfl) ⟨1213643, by rfl⟩ : syracuseStep 1618191 = 2427287) B2427287
theorem B3641615 : Blo 1617007 3641615 := bstep (se 1 (by rfl) ⟨2731211, by rfl⟩ : syracuseStep 3641615 = 5462423) B5462423
theorem B3641633 : Blo 1617007 3641633 := bstep (se 2 (by rfl) ⟨1365612, by rfl⟩ : syracuseStep 3641633 = 2731225) B2731225
theorem B7196987 : Blo 1617007 7196987 := bstep (se 1 (by rfl) ⟨5397740, by rfl⟩ : syracuseStep 7196987 = 10795481) B10795481
theorem B1618235 : Blo 1617007 1618235 := bstep (se 1 (by rfl) ⟨1213676, by rfl⟩ : syracuseStep 1618235 = 2427353) B2427353
theorem B1618311 : Blo 1617007 1618311 := bstep (se 1 (by rfl) ⟨1213733, by rfl⟩ : syracuseStep 1618311 = 2427467) B2427467
theorem B1618319 : Blo 1617007 1618319 := bstep (se 1 (by rfl) ⟨1213739, by rfl⟩ : syracuseStep 1618319 = 2427479) B2427479
theorem B5460371 : Blo 1617007 5460371 := bstep (se 1 (by rfl) ⟨4095278, by rfl⟩ : syracuseStep 5460371 = 8190557) B8190557
theorem B1618363 : Blo 1617007 1618363 := bstep (se 1 (by rfl) ⟨1213772, by rfl⟩ : syracuseStep 1618363 = 2427545) B2427545
theorem B17494481 : Blo 1617007 17494481 := bstep (se 2 (by rfl) ⟨6560430, by rfl⟩ : syracuseStep 17494481 = 13120861) B13120861
theorem B1618439 : Blo 1617007 1618439 := bstep (se 1 (by rfl) ⟨1213829, by rfl⟩ : syracuseStep 1618439 = 2427659) B2427659
theorem B1618447 : Blo 1617007 1618447 := bstep (se 1 (by rfl) ⟨1213835, by rfl⟩ : syracuseStep 1618447 = 2427671) B2427671
theorem B109359659 : Blo 1617007 109359659 := bstep (se 1 (by rfl) ⟨82019744, by rfl⟩ : syracuseStep 109359659 = 164039489) B164039489
theorem B1618491 : Blo 1617007 1618491 := bstep (se 1 (by rfl) ⟨1213868, by rfl⟩ : syracuseStep 1618491 = 2427737) B2427737
theorem B4371005 : Blo 1617007 4371005 := bstep (se 3 (by rfl) ⟨819563, by rfl⟩ : syracuseStep 4371005 = 1639127) B1639127
theorem B5829187 : Blo 1617007 5829187 := bstep (se 1 (by rfl) ⟨4371890, by rfl⟩ : syracuseStep 5829187 = 8743781) B8743781
theorem B3641975 : Blo 1617007 3641975 := bstep (se 1 (by rfl) ⟨2731481, by rfl⟩ : syracuseStep 3641975 = 5462963) B5462963
theorem B4608647 : Blo 1617007 4608647 := bstep (se 1 (by rfl) ⟨3456485, by rfl⟩ : syracuseStep 4608647 = 6912971) B6912971
theorem B1618567 : Blo 1617007 1618567 := bstep (se 1 (by rfl) ⟨1213925, by rfl⟩ : syracuseStep 1618567 = 2427851) B2427851
theorem B1618575 : Blo 1617007 1618575 := bstep (se 1 (by rfl) ⟨1213931, by rfl⟩ : syracuseStep 1618575 = 2427863) B2427863
theorem B1618619 : Blo 1617007 1618619 := bstep (se 1 (by rfl) ⟨1213964, by rfl⟩ : syracuseStep 1618619 = 2427929) B2427929
theorem B1618695 : Blo 1617007 1618695 := bstep (se 1 (by rfl) ⟨1214021, by rfl⟩ : syracuseStep 1618695 = 2428043) B2428043
theorem B1618703 : Blo 1617007 1618703 := bstep (se 1 (by rfl) ⟨1214027, by rfl⟩ : syracuseStep 1618703 = 2428055) B2428055
theorem B31535909 : Blo 1617007 31535909 := bstep (se 4 (by rfl) ⟨2956491, by rfl⟩ : syracuseStep 31535909 = 5912983) B5912983
theorem B3642155 : Blo 1617007 3642155 := bstep (se 1 (by rfl) ⟨2731616, by rfl⟩ : syracuseStep 3642155 = 5463233) B5463233
theorem B6140731 : Blo 1617007 6140731 := bstep (se 1 (by rfl) ⟨4605548, by rfl⟩ : syracuseStep 6140731 = 9211097) B9211097
theorem B1618747 : Blo 1617007 1618747 := bstep (se 1 (by rfl) ⟨1214060, by rfl⟩ : syracuseStep 1618747 = 2428121) B2428121
theorem B4608829 : Blo 1617007 4608829 := bstep (se 3 (by rfl) ⟨864155, by rfl⟩ : syracuseStep 4608829 = 1728311) B1728311
theorem B1618823 : Blo 1617007 1618823 := bstep (se 1 (by rfl) ⟨1214117, by rfl⟩ : syracuseStep 1618823 = 2428235) B2428235
theorem B1618831 : Blo 1617007 1618831 := bstep (se 1 (by rfl) ⟨1214123, by rfl⟩ : syracuseStep 1618831 = 2428247) B2428247
theorem B1618875 : Blo 1617007 1618875 := bstep (se 1 (by rfl) ⟨1214156, by rfl⟩ : syracuseStep 1618875 = 2428313) B2428313
theorem B1618951 : Blo 1617007 1618951 := bstep (se 1 (by rfl) ⟨1214213, by rfl⟩ : syracuseStep 1618951 = 2428427) B2428427
theorem B1618959 : Blo 1617007 1618959 := bstep (se 1 (by rfl) ⟨1214219, by rfl⟩ : syracuseStep 1618959 = 2428439) B2428439
theorem B4609057 : Blo 1617007 4609057 := bstep (se 2 (by rfl) ⟨1728396, by rfl⟩ : syracuseStep 4609057 = 3456793) B3456793
theorem B1619003 : Blo 1617007 1619003 := bstep (se 1 (by rfl) ⟨1214252, by rfl⟩ : syracuseStep 1619003 = 2428505) B2428505
theorem B13816919 : Blo 1617007 13816919 := bstep (se 1 (by rfl) ⟨10362689, by rfl⟩ : syracuseStep 13816919 = 20725379) B20725379
theorem B3642515 : Blo 1617007 3642515 := bstep (se 1 (by rfl) ⟨2731886, by rfl⟩ : syracuseStep 3642515 = 5463773) B5463773
theorem B4150457 : Blo 1617007 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B3642569 : Blo 1617007 3642569 := bstep (se 2 (by rfl) ⟨1365963, by rfl⟩ : syracuseStep 3642569 = 2731927) B2731927
theorem B6141217 : Blo 1617007 6141217 := bstep (se 2 (by rfl) ⟨2302956, by rfl⟩ : syracuseStep 6141217 = 4605913) B4605913
theorem B4609399 : Blo 1617007 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B52450739 : Blo 1617007 52450739 := bstep (se 1 (by rfl) ⟨39338054, by rfl⟩ : syracuseStep 52450739 = 78676109) B78676109
theorem B23311901 : Blo 1617007 23311901 := bstep (se 3 (by rfl) ⟨4370981, by rfl⟩ : syracuseStep 23311901 = 8741963) B8741963
theorem B11064899 : Blo 1617007 11064899 := bstep (se 1 (by rfl) ⟨8298674, by rfl⟩ : syracuseStep 11064899 = 16597349) B16597349
theorem B59078321 : Blo 1617007 59078321 := bstep (se 2 (by rfl) ⟨22154370, by rfl⟩ : syracuseStep 59078321 = 44308741) B44308741
theorem B5461775 : Blo 1617007 5461775 := bstep (se 1 (by rfl) ⟨4096331, by rfl⟩ : syracuseStep 5461775 = 8192663) B8192663
theorem B15554339 : Blo 1617007 15554339 := bstep (se 1 (by rfl) ⟨11665754, by rfl⟩ : syracuseStep 15554339 = 23331509) B23331509
theorem B8189747 : Blo 1617007 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B34125619 : Blo 1617007 34125619 := bstep (se 1 (by rfl) ⟨25594214, by rfl⟩ : syracuseStep 34125619 = 51188429) B51188429
theorem B4093811 : Blo 1617007 4093811 := bstep (se 1 (by rfl) ⟨3070358, by rfl⟩ : syracuseStep 4093811 = 6140717) B6140717
theorem B17487731 : Blo 1617007 17487731 := bstep (se 1 (by rfl) ⟨13115798, by rfl⟩ : syracuseStep 17487731 = 26231597) B26231597
theorem B5462045 : Blo 1617007 5462045 := bstep (se 3 (by rfl) ⟨1024133, by rfl⟩ : syracuseStep 5462045 = 2048267) B2048267
theorem B9214013 : Blo 1617007 9214013 := bstep (se 3 (by rfl) ⟨1727627, by rfl⟩ : syracuseStep 9214013 = 3455255) B3455255
theorem B8190071 : Blo 1617007 8190071 := bstep (se 1 (by rfl) ⟨6142553, by rfl⟩ : syracuseStep 8190071 = 12285107) B12285107
theorem B5830775 : Blo 1617007 5830775 := bstep (se 1 (by rfl) ⟨4373081, by rfl⟩ : syracuseStep 5830775 = 8746163) B8746163
theorem B3455111 : Blo 1617007 3455111 := bstep (se 1 (by rfl) ⟨2591333, by rfl⟩ : syracuseStep 3455111 = 5182667) B5182667
theorem B3070153 : Blo 1617007 3070153 := bstep (se 2 (by rfl) ⟨1151307, by rfl⟩ : syracuseStep 3070153 = 2302615) B2302615
theorem B6142189 : Blo 1617007 6142189 := bstep (se 3 (by rfl) ⟨1151660, by rfl⟩ : syracuseStep 6142189 = 2303321) B2303321
theorem B4610333 : Blo 1617007 4610333 := bstep (se 3 (by rfl) ⟨864437, by rfl⟩ : syracuseStep 4610333 = 1728875) B1728875
theorem B4094327 : Blo 1617007 4094327 := bstep (se 1 (by rfl) ⟨3070745, by rfl⟩ : syracuseStep 4094327 = 6141491) B6141491
theorem B6142493 : Blo 1617007 6142493 := bstep (se 3 (by rfl) ⟨1151717, by rfl⟩ : syracuseStep 6142493 = 2303435) B2303435
theorem B56048345 : Blo 1617007 56048345 := bstep (se 2 (by rfl) ⟨21018129, by rfl⟩ : syracuseStep 56048345 = 42036259) B42036259
theorem B9214721 : Blo 1617007 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B35003141 : Blo 1617007 35003141 := bstep (se 4 (by rfl) ⟨3281544, by rfl⟩ : syracuseStep 35003141 = 6563089) B6563089
theorem B2186119 : Blo 1617007 2186119 := bstep (se 1 (by rfl) ⟨1639589, by rfl⟩ : syracuseStep 2186119 = 3279179) B3279179
theorem B3070867 : Blo 1617007 3070867 := bstep (se 1 (by rfl) ⟨2303150, by rfl⟩ : syracuseStep 3070867 = 4606301) B4606301
theorem B5184523 : Blo 1617007 5184523 := bstep (se 1 (by rfl) ⟨3888392, by rfl⟩ : syracuseStep 5184523 = 7776785) B7776785
theorem B8191043 : Blo 1617007 8191043 := bstep (se 1 (by rfl) ⟨6143282, by rfl⟩ : syracuseStep 8191043 = 12286565) B12286565
theorem B33668227 : Blo 1617007 33668227 := bstep (se 1 (by rfl) ⟨25251170, by rfl⟩ : syracuseStep 33668227 = 50502341) B50502341
theorem B6913313 : Blo 1617007 6913313 := bstep (se 2 (by rfl) ⟨2592492, by rfl⟩ : syracuseStep 6913313 = 5184985) B5184985
theorem B4095319 : Blo 1617007 4095319 := bstep (se 1 (by rfl) ⟨3071489, by rfl⟩ : syracuseStep 4095319 = 6142979) B6142979
theorem B2047351 : Blo 1617007 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B8191367 : Blo 1617007 8191367 := bstep (se 1 (by rfl) ⟨6143525, by rfl⟩ : syracuseStep 8191367 = 12287051) B12287051
theorem B5463449 : Blo 1617007 5463449 := bstep (se 2 (by rfl) ⟨2048793, by rfl⟩ : syracuseStep 5463449 = 4097587) B4097587
theorem B19676621 : Blo 1617007 19676621 := bstep (se 3 (by rfl) ⟨3689366, by rfl⟩ : syracuseStep 19676621 = 7378733) B7378733
theorem B7003691 : Blo 1617007 7003691 := bstep (se 1 (by rfl) ⟨5252768, by rfl⟩ : syracuseStep 7003691 = 10505537) B10505537
theorem B4095623 : Blo 1617007 4095623 := bstep (se 1 (by rfl) ⟨3071717, by rfl⟩ : syracuseStep 4095623 = 6143435) B6143435
theorem B2047675 : Blo 1617007 2047675 := bstep (se 1 (by rfl) ⟨1535756, by rfl⟩ : syracuseStep 2047675 = 3071513) B3071513
theorem B4095755 : Blo 1617007 4095755 := bstep (se 1 (by rfl) ⟨3071816, by rfl⟩ : syracuseStep 4095755 = 6143633) B6143633
theorem B6913927 : Blo 1617007 6913927 := bstep (se 1 (by rfl) ⟨5185445, by rfl⟩ : syracuseStep 6913927 = 10370891) B10370891
theorem B3071945 : Blo 1617007 3071945 := bstep (se 2 (by rfl) ⟨1151979, by rfl⟩ : syracuseStep 3071945 = 2303959) B2303959
theorem B8192015 : Blo 1617007 8192015 := bstep (se 1 (by rfl) ⟨6144011, by rfl⟩ : syracuseStep 8192015 = 12288023) B12288023
theorem B6225977 : Blo 1617007 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B4096079 : Blo 1617007 4096079 := bstep (se 1 (by rfl) ⟨3072059, by rfl⟩ : syracuseStep 4096079 = 6144119) B6144119
theorem B3072097 : Blo 1617007 3072097 := bstep (se 2 (by rfl) ⟨1152036, by rfl⟩ : syracuseStep 3072097 = 2304073) B2304073
theorem B3072431 : Blo 1617007 3072431 := bstep (se 1 (by rfl) ⟨2304323, by rfl⟩ : syracuseStep 3072431 = 4608647) B4608647
theorem B3113491 : Blo 1617007 3113491 := bstep (se 1 (by rfl) ⟨2335118, by rfl⟩ : syracuseStep 3113491 = 4670237) B4670237
theorem B2048591 : Blo 1617007 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B4096727 : Blo 1617007 4096727 := bstep (se 1 (by rfl) ⟨3072545, by rfl⟩ : syracuseStep 4096727 = 6145091) B6145091
theorem B2425775 : Blo 1617007 2425775 := bstep (se 1 (by rfl) ⟨1819331, by rfl⟩ : syracuseStep 2425775 = 3638663) B3638663
theorem B2425865 : Blo 1617007 2425865 := bstep (se 2 (by rfl) ⟨909699, by rfl⟩ : syracuseStep 2425865 = 1819399) B1819399
theorem B15541267 : Blo 1617007 15541267 := bstep (se 1 (by rfl) ⟨11655950, by rfl⟩ : syracuseStep 15541267 = 23311901) B23311901
theorem B2425895 : Blo 1617007 2425895 := bstep (se 1 (by rfl) ⟨1819421, by rfl⟩ : syracuseStep 2425895 = 3638843) B3638843
theorem B1819687 : Blo 1617007 1819687 := bstep (se 1 (by rfl) ⟨1364765, by rfl⟩ : syracuseStep 1819687 = 2729531) B2729531
theorem B4097081 : Blo 1617007 4097081 := bstep (se 2 (by rfl) ⟨1536405, by rfl⟩ : syracuseStep 4097081 = 3072811) B3072811
theorem B6145105 : Blo 1617007 6145105 := bstep (se 2 (by rfl) ⟨2304414, by rfl⟩ : syracuseStep 6145105 = 4608829) B4608829
theorem B2425979 : Blo 1617007 2425979 := bstep (se 1 (by rfl) ⟨1819484, by rfl⟩ : syracuseStep 2425979 = 3638969) B3638969
theorem B13829291 : Blo 1617007 13829291 := bstep (se 1 (by rfl) ⟨10371968, by rfl⟩ : syracuseStep 13829291 = 20743937) B20743937
theorem B3638519 : Blo 1617007 3638519 := bstep (se 1 (by rfl) ⟨2728889, by rfl⟩ : syracuseStep 3638519 = 5457779) B5457779
theorem B2729207 : Blo 1617007 2729207 := bstep (se 1 (by rfl) ⟨2046905, by rfl⟩ : syracuseStep 2729207 = 4093811) B4093811
theorem B2426105 : Blo 1617007 2426105 := bstep (se 2 (by rfl) ⟨909789, by rfl⟩ : syracuseStep 2426105 = 1819579) B1819579
theorem B11658487 : Blo 1617007 11658487 := bstep (se 1 (by rfl) ⟨8743865, by rfl⟩ : syracuseStep 11658487 = 17487731) B17487731
theorem B13124855 : Blo 1617007 13124855 := bstep (se 1 (by rfl) ⟨9843641, by rfl⟩ : syracuseStep 13124855 = 19687283) B19687283
theorem B2426207 : Blo 1617007 2426207 := bstep (se 1 (by rfl) ⟨1819655, by rfl⟩ : syracuseStep 2426207 = 3639311) B3639311
theorem B2426219 : Blo 1617007 2426219 := bstep (se 1 (by rfl) ⟨1819664, by rfl⟩ : syracuseStep 2426219 = 3639329) B3639329
theorem B6145409 : Blo 1617007 6145409 := bstep (se 2 (by rfl) ⟨2304528, by rfl⟩ : syracuseStep 6145409 = 4609057) B4609057
theorem B2303407 : Blo 1617007 2303407 := bstep (se 1 (by rfl) ⟨1727555, by rfl⟩ : syracuseStep 2303407 = 3455111) B3455111
theorem B12289481 : Blo 1617007 12289481 := bstep (se 2 (by rfl) ⟨4608555, by rfl⟩ : syracuseStep 12289481 = 9217111) B9217111
theorem B3073555 : Blo 1617007 3073555 := bstep (se 1 (by rfl) ⟨2305166, by rfl⟩ : syracuseStep 3073555 = 4610333) B4610333
theorem B2729551 : Blo 1617007 2729551 := bstep (se 1 (by rfl) ⟨2047163, by rfl⟩ : syracuseStep 2729551 = 4094327) B4094327
theorem B2426447 : Blo 1617007 2426447 := bstep (se 1 (by rfl) ⟨1819835, by rfl⟩ : syracuseStep 2426447 = 3639671) B3639671
theorem B2426567 : Blo 1617007 2426567 := bstep (se 1 (by rfl) ⟨1819925, by rfl⟩ : syracuseStep 2426567 = 3639851) B3639851
theorem B37365563 : Blo 1617007 37365563 := bstep (se 1 (by rfl) ⟨28024172, by rfl⟩ : syracuseStep 37365563 = 56048345) B56048345
theorem B6227779 : Blo 1617007 6227779 := bstep (se 1 (by rfl) ⟨4670834, by rfl⟩ : syracuseStep 6227779 = 9341669) B9341669
theorem B3639113 : Blo 1617007 3639113 := bstep (se 2 (by rfl) ⟨1364667, by rfl⟩ : syracuseStep 3639113 = 2729335) B2729335
theorem B2729801 : Blo 1617007 2729801 := bstep (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) B2047351
theorem B6145865 : Blo 1617007 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B2426729 : Blo 1617007 2426729 := bstep (se 2 (by rfl) ⟨910023, by rfl⟩ : syracuseStep 2426729 = 1820047) B1820047
theorem B2459567 : Blo 1617007 2459567 := bstep (se 1 (by rfl) ⟨1844675, by rfl⟩ : syracuseStep 2459567 = 3689351) B3689351
theorem B2426807 : Blo 1617007 2426807 := bstep (se 1 (by rfl) ⟨1820105, by rfl⟩ : syracuseStep 2426807 = 3640211) B3640211
theorem B2426843 : Blo 1617007 2426843 := bstep (se 1 (by rfl) ⟨1820132, by rfl⟩ : syracuseStep 2426843 = 3640265) B3640265
theorem B10373123 : Blo 1617007 10373123 := bstep (se 1 (by rfl) ⟨7779842, by rfl⟩ : syracuseStep 10373123 = 15559685) B15559685
theorem B3278855 : Blo 1617007 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B4605959 : Blo 1617007 4605959 := bstep (se 1 (by rfl) ⟨3454469, by rfl⟩ : syracuseStep 4605959 = 6908939) B6908939
theorem B6146063 : Blo 1617007 6146063 := bstep (se 1 (by rfl) ⟨4609547, by rfl⟩ : syracuseStep 6146063 = 9219095) B9219095
theorem B2730233 : Blo 1617007 2730233 := bstep (se 2 (by rfl) ⟨1023837, by rfl⟩ : syracuseStep 2730233 = 2047675) B2047675
theorem B13117747 : Blo 1617007 13117747 := bstep (se 1 (by rfl) ⟨9838310, by rfl⟩ : syracuseStep 13117747 = 19676621) B19676621
theorem B4917647 : Blo 1617007 4917647 := bstep (se 1 (by rfl) ⟨3688235, by rfl⟩ : syracuseStep 4917647 = 7376471) B7376471
theorem B5458319 : Blo 1617007 5458319 := bstep (se 1 (by rfl) ⟨4093739, by rfl⟩ : syracuseStep 5458319 = 8187479) B8187479
theorem B45500825 : Blo 1617007 45500825 := bstep (se 2 (by rfl) ⟨17062809, by rfl⟩ : syracuseStep 45500825 = 34125619) B34125619
theorem B2730415 : Blo 1617007 2730415 := bstep (se 1 (by rfl) ⟨2047811, by rfl⟩ : syracuseStep 2730415 = 4095623) B4095623
theorem B2427311 : Blo 1617007 2427311 := bstep (se 1 (by rfl) ⟨1820483, by rfl⟩ : syracuseStep 2427311 = 3640967) B3640967
theorem B41478641 : Blo 1617007 41478641 := bstep (se 2 (by rfl) ⟨15554490, by rfl⟩ : syracuseStep 41478641 = 31108981) B31108981
theorem B2730503 : Blo 1617007 2730503 := bstep (se 1 (by rfl) ⟨2047877, by rfl⟩ : syracuseStep 2730503 = 4095755) B4095755
theorem B2427401 : Blo 1617007 2427401 := bstep (se 2 (by rfl) ⟨910275, by rfl⟩ : syracuseStep 2427401 = 1820551) B1820551
theorem B9218569 : Blo 1617007 9218569 := bstep (se 2 (by rfl) ⟨3456963, by rfl⟩ : syracuseStep 9218569 = 6913927) B6913927
theorem B2427431 : Blo 1617007 2427431 := bstep (se 1 (by rfl) ⟨1820573, by rfl⟩ : syracuseStep 2427431 = 3641147) B3641147
theorem B3639905 : Blo 1617007 3639905 := bstep (se 2 (by rfl) ⟨1364964, by rfl⟩ : syracuseStep 3639905 = 2729929) B2729929
theorem B2427515 : Blo 1617007 2427515 := bstep (se 1 (by rfl) ⟨1820636, by rfl⟩ : syracuseStep 2427515 = 3641273) B3641273
theorem B1821307 : Blo 1617007 1821307 := bstep (se 1 (by rfl) ⟨1365980, by rfl⟩ : syracuseStep 1821307 = 2731961) B2731961
theorem B8194769 : Blo 1617007 8194769 := bstep (se 2 (by rfl) ⟨3073038, by rfl⟩ : syracuseStep 8194769 = 6146077) B6146077
theorem B5458643 : Blo 1617007 5458643 := bstep (se 1 (by rfl) ⟨4093982, by rfl⟩ : syracuseStep 5458643 = 8187965) B8187965
theorem B2427641 : Blo 1617007 2427641 := bstep (se 2 (by rfl) ⟨910365, by rfl⟩ : syracuseStep 2427641 = 1820731) B1820731
theorem B6556459 : Blo 1617007 6556459 := bstep (se 1 (by rfl) ⟨4917344, by rfl⟩ : syracuseStep 6556459 = 9834689) B9834689
theorem B2730847 : Blo 1617007 2730847 := bstep (se 1 (by rfl) ⟨2048135, by rfl⟩ : syracuseStep 2730847 = 4096271) B4096271
theorem B2427743 : Blo 1617007 2427743 := bstep (se 1 (by rfl) ⟨1820807, by rfl⟩ : syracuseStep 2427743 = 3641615) B3641615
theorem B2427755 : Blo 1617007 2427755 := bstep (se 1 (by rfl) ⟨1820816, by rfl⟩ : syracuseStep 2427755 = 3641633) B3641633
theorem B3640247 : Blo 1617007 3640247 := bstep (se 1 (by rfl) ⟨2730185, by rfl⟩ : syracuseStep 3640247 = 5460371) B5460371
theorem B2730935 : Blo 1617007 2730935 := bstep (se 1 (by rfl) ⟨2048201, by rfl⟩ : syracuseStep 2730935 = 4096403) B4096403
theorem B2427983 : Blo 1617007 2427983 := bstep (se 1 (by rfl) ⟨1820987, by rfl⟩ : syracuseStep 2427983 = 3641975) B3641975
theorem B1617019 : Blo 1617007 1617019 := bstep (se 1 (by rfl) ⟨1212764, by rfl⟩ : syracuseStep 1617019 = 2425529) B2425529
theorem B1617071 : Blo 1617007 1617071 := bstep (se 1 (by rfl) ⟨1212803, by rfl⟩ : syracuseStep 1617071 = 2425607) B2425607
theorem B21023939 : Blo 1617007 21023939 := bstep (se 1 (by rfl) ⟨15767954, by rfl⟩ : syracuseStep 21023939 = 31535909) B31535909
theorem B1617095 : Blo 1617007 1617095 := bstep (se 1 (by rfl) ⟨1212821, by rfl⟩ : syracuseStep 1617095 = 2425643) B2425643
theorem B2428103 : Blo 1617007 2428103 := bstep (se 1 (by rfl) ⟨1821077, by rfl⟩ : syracuseStep 2428103 = 3642155) B3642155
theorem B1617115 : Blo 1617007 1617115 := bstep (se 1 (by rfl) ⟨1212836, by rfl⟩ : syracuseStep 1617115 = 2425673) B2425673
theorem B1617191 : Blo 1617007 1617191 := bstep (se 1 (by rfl) ⟨1212893, by rfl⟩ : syracuseStep 1617191 = 2425787) B2425787
theorem B1617231 : Blo 1617007 1617231 := bstep (se 1 (by rfl) ⟨1212923, by rfl⟩ : syracuseStep 1617231 = 2425847) B2425847
theorem B1617247 : Blo 1617007 1617247 := bstep (se 1 (by rfl) ⟨1212935, by rfl⟩ : syracuseStep 1617247 = 2425871) B2425871
theorem B179563877 : Blo 1617007 179563877 := bstep (se 4 (by rfl) ⟨16834113, by rfl⟩ : syracuseStep 179563877 = 33668227) B33668227
theorem B2428265 : Blo 1617007 2428265 := bstep (se 2 (by rfl) ⟨910599, by rfl⟩ : syracuseStep 2428265 = 1821199) B1821199
theorem B1617275 : Blo 1617007 1617275 := bstep (se 1 (by rfl) ⟨1212956, by rfl⟩ : syracuseStep 1617275 = 2425913) B2425913
theorem B9211279 : Blo 1617007 9211279 := bstep (se 1 (by rfl) ⟨6908459, by rfl⟩ : syracuseStep 9211279 = 13816919) B13816919
theorem B1617327 : Blo 1617007 1617327 := bstep (se 1 (by rfl) ⟨1212995, by rfl⟩ : syracuseStep 1617327 = 2425991) B2425991
theorem B2428343 : Blo 1617007 2428343 := bstep (se 1 (by rfl) ⟨1821257, by rfl⟩ : syracuseStep 2428343 = 3642515) B3642515
theorem B1617351 : Blo 1617007 1617351 := bstep (se 1 (by rfl) ⟨1213013, by rfl⟩ : syracuseStep 1617351 = 2426027) B2426027
theorem B1617371 : Blo 1617007 1617371 := bstep (se 1 (by rfl) ⟨1213028, by rfl⟩ : syracuseStep 1617371 = 2426057) B2426057
theorem B2428379 : Blo 1617007 2428379 := bstep (se 1 (by rfl) ⟨1821284, by rfl⟩ : syracuseStep 2428379 = 3642569) B3642569
theorem B3640841 : Blo 1617007 3640841 := bstep (se 2 (by rfl) ⟨1365315, by rfl⟩ : syracuseStep 3640841 = 2730631) B2730631
theorem B2731529 : Blo 1617007 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B1617447 : Blo 1617007 1617447 := bstep (se 1 (by rfl) ⟨1213085, by rfl⟩ : syracuseStep 1617447 = 2426171) B2426171
theorem B1617487 : Blo 1617007 1617487 := bstep (se 1 (by rfl) ⟨1213115, by rfl⟩ : syracuseStep 1617487 = 2426231) B2426231
theorem B1617503 : Blo 1617007 1617503 := bstep (se 1 (by rfl) ⟨1213127, by rfl⟩ : syracuseStep 1617503 = 2426255) B2426255
theorem B34967159 : Blo 1617007 34967159 := bstep (se 1 (by rfl) ⟨26225369, by rfl⟩ : syracuseStep 34967159 = 52450739) B52450739
theorem B1617531 : Blo 1617007 1617531 := bstep (se 1 (by rfl) ⟨1213148, by rfl⟩ : syracuseStep 1617531 = 2426297) B2426297
theorem B2731691 : Blo 1617007 2731691 := bstep (se 1 (by rfl) ⟨2048768, by rfl⟩ : syracuseStep 2731691 = 4097537) B4097537
theorem B1617583 : Blo 1617007 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B6139577 : Blo 1617007 6139577 := bstep (se 2 (by rfl) ⟨2302341, by rfl⟩ : syracuseStep 6139577 = 4604683) B4604683
theorem B1617607 : Blo 1617007 1617607 := bstep (se 1 (by rfl) ⟨1213205, by rfl⟩ : syracuseStep 1617607 = 2426411) B2426411
theorem B7376599 : Blo 1617007 7376599 := bstep (se 1 (by rfl) ⟨5532449, by rfl⟩ : syracuseStep 7376599 = 11064899) B11064899
theorem B1617627 : Blo 1617007 1617627 := bstep (se 1 (by rfl) ⟨1213220, by rfl⟩ : syracuseStep 1617627 = 2426441) B2426441
theorem B8187641 : Blo 1617007 8187641 := bstep (se 2 (by rfl) ⟨3070365, by rfl⟩ : syracuseStep 8187641 = 6140731) B6140731
theorem B1617703 : Blo 1617007 1617703 := bstep (se 1 (by rfl) ⟨1213277, by rfl⟩ : syracuseStep 1617703 = 2426555) B2426555
theorem B1617743 : Blo 1617007 1617743 := bstep (se 1 (by rfl) ⟨1213307, by rfl⟩ : syracuseStep 1617743 = 2426615) B2426615
theorem B1617759 : Blo 1617007 1617759 := bstep (se 1 (by rfl) ⟨1213319, by rfl⟩ : syracuseStep 1617759 = 2426639) B2426639
theorem B3641183 : Blo 1617007 3641183 := bstep (se 1 (by rfl) ⟨2730887, by rfl⟩ : syracuseStep 3641183 = 5461775) B5461775
theorem B5459831 : Blo 1617007 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B1617787 : Blo 1617007 1617787 := bstep (se 1 (by rfl) ⟨1213340, by rfl⟩ : syracuseStep 1617787 = 2426681) B2426681
theorem B3157903 : Blo 1617007 3157903 := bstep (se 1 (by rfl) ⟨2368427, by rfl⟩ : syracuseStep 3157903 = 4736855) B4736855
theorem B1617839 : Blo 1617007 1617839 := bstep (se 1 (by rfl) ⟨1213379, by rfl⟩ : syracuseStep 1617839 = 2426759) B2426759
theorem B9220027 : Blo 1617007 9220027 := bstep (se 1 (by rfl) ⟨6915020, by rfl⟩ : syracuseStep 9220027 = 13830041) B13830041
theorem B1617863 : Blo 1617007 1617863 := bstep (se 1 (by rfl) ⟨1213397, by rfl⟩ : syracuseStep 1617863 = 2426795) B2426795
theorem B1617883 : Blo 1617007 1617883 := bstep (se 1 (by rfl) ⟨1213412, by rfl⟩ : syracuseStep 1617883 = 2426825) B2426825
theorem B34123787 : Blo 1617007 34123787 := bstep (se 1 (by rfl) ⟨25592840, by rfl⟩ : syracuseStep 34123787 = 51185681) B51185681
theorem B29519887 : Blo 1617007 29519887 := bstep (se 1 (by rfl) ⟨22139915, by rfl⟩ : syracuseStep 29519887 = 44279831) B44279831
theorem B3641363 : Blo 1617007 3641363 := bstep (se 1 (by rfl) ⟨2731022, by rfl⟩ : syracuseStep 3641363 = 5462045) B5462045
theorem B1617959 : Blo 1617007 1617959 := bstep (se 1 (by rfl) ⟨1213469, by rfl⟩ : syracuseStep 1617959 = 2426939) B2426939
theorem B5460047 : Blo 1617007 5460047 := bstep (se 1 (by rfl) ⟨4095035, by rfl⟩ : syracuseStep 5460047 = 8190071) B8190071
theorem B3887183 : Blo 1617007 3887183 := bstep (se 1 (by rfl) ⟨2915387, by rfl⟩ : syracuseStep 3887183 = 5830775) B5830775
theorem B1617999 : Blo 1617007 1617999 := bstep (se 1 (by rfl) ⟨1213499, by rfl⟩ : syracuseStep 1617999 = 2426999) B2426999
theorem B1618015 : Blo 1617007 1618015 := bstep (se 1 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 1618015 = 2427023) B2427023
theorem B1618043 : Blo 1617007 1618043 := bstep (se 1 (by rfl) ⟨1213532, by rfl⟩ : syracuseStep 1618043 = 2427065) B2427065
theorem B1618095 : Blo 1617007 1618095 := bstep (se 1 (by rfl) ⟨1213571, by rfl⟩ : syracuseStep 1618095 = 2427143) B2427143
theorem B46641329 : Blo 1617007 46641329 := bstep (se 2 (by rfl) ⟨17490498, by rfl⟩ : syracuseStep 46641329 = 34980997) B34980997
theorem B1618119 : Blo 1617007 1618119 := bstep (se 1 (by rfl) ⟨1213589, by rfl⟩ : syracuseStep 1618119 = 2427179) B2427179
theorem B1618139 : Blo 1617007 1618139 := bstep (se 1 (by rfl) ⟨1213604, by rfl⟩ : syracuseStep 1618139 = 2427209) B2427209
theorem B1618215 : Blo 1617007 1618215 := bstep (se 1 (by rfl) ⟨1213661, by rfl⟩ : syracuseStep 1618215 = 2427323) B2427323
theorem B141914429 : Blo 1617007 141914429 := bstep (se 3 (by rfl) ⟨26608955, by rfl⟩ : syracuseStep 141914429 = 53217911) B53217911
theorem B1618255 : Blo 1617007 1618255 := bstep (se 1 (by rfl) ⟨1213691, by rfl⟩ : syracuseStep 1618255 = 2427383) B2427383
theorem B1618271 : Blo 1617007 1618271 := bstep (se 1 (by rfl) ⟨1213703, by rfl⟩ : syracuseStep 1618271 = 2427407) B2427407
theorem B3641705 : Blo 1617007 3641705 := bstep (se 2 (by rfl) ⟨1365639, by rfl⟩ : syracuseStep 3641705 = 2731279) B2731279
theorem B1618299 : Blo 1617007 1618299 := bstep (se 1 (by rfl) ⟨1213724, by rfl⟩ : syracuseStep 1618299 = 2427449) B2427449
theorem B8188289 : Blo 1617007 8188289 := bstep (se 2 (by rfl) ⟨3070608, by rfl⟩ : syracuseStep 8188289 = 6141217) B6141217
theorem B1618351 : Blo 1617007 1618351 := bstep (se 1 (by rfl) ⟨1213763, by rfl⟩ : syracuseStep 1618351 = 2427527) B2427527
theorem B1618375 : Blo 1617007 1618375 := bstep (se 1 (by rfl) ⟨1213781, by rfl⟩ : syracuseStep 1618375 = 2427563) B2427563
theorem B5460425 : Blo 1617007 5460425 := bstep (se 2 (by rfl) ⟨2047659, by rfl⟩ : syracuseStep 5460425 = 4095319) B4095319
theorem B1618395 : Blo 1617007 1618395 := bstep (se 1 (by rfl) ⟨1213796, by rfl⟩ : syracuseStep 1618395 = 2427593) B2427593
theorem B23335427 : Blo 1617007 23335427 := bstep (se 1 (by rfl) ⟨17501570, by rfl⟩ : syracuseStep 23335427 = 35003141) B35003141
theorem B7778825 : Blo 1617007 7778825 := bstep (se 2 (by rfl) ⟨2917059, by rfl⟩ : syracuseStep 7778825 = 5834119) B5834119
theorem B1618471 : Blo 1617007 1618471 := bstep (se 1 (by rfl) ⟨1213853, by rfl⟩ : syracuseStep 1618471 = 2427707) B2427707
theorem B1618511 : Blo 1617007 1618511 := bstep (se 1 (by rfl) ⟨1213883, by rfl⟩ : syracuseStep 1618511 = 2427767) B2427767
theorem B1618527 : Blo 1617007 1618527 := bstep (se 1 (by rfl) ⟨1213895, by rfl⟩ : syracuseStep 1618527 = 2427791) B2427791
theorem B1618555 : Blo 1617007 1618555 := bstep (se 1 (by rfl) ⟨1213916, by rfl⟩ : syracuseStep 1618555 = 2427833) B2427833
theorem B1618607 : Blo 1617007 1618607 := bstep (se 1 (by rfl) ⟨1213955, by rfl⟩ : syracuseStep 1618607 = 2427911) B2427911
theorem B1618631 : Blo 1617007 1618631 := bstep (se 1 (by rfl) ⟨1213973, by rfl⟩ : syracuseStep 1618631 = 2427947) B2427947
theorem B5460695 : Blo 1617007 5460695 := bstep (se 1 (by rfl) ⟨4095521, by rfl⟩ : syracuseStep 5460695 = 8191043) B8191043
theorem B1618651 : Blo 1617007 1618651 := bstep (se 1 (by rfl) ⟨1213988, by rfl⟩ : syracuseStep 1618651 = 2427977) B2427977
theorem B1618727 : Blo 1617007 1618727 := bstep (se 1 (by rfl) ⟨1214045, by rfl⟩ : syracuseStep 1618727 = 2428091) B2428091
theorem B3453769 : Blo 1617007 3453769 := bstep (se 2 (by rfl) ⟨1295163, by rfl⟩ : syracuseStep 3453769 = 2590327) B2590327
theorem B1618767 : Blo 1617007 1618767 := bstep (se 1 (by rfl) ⟨1214075, by rfl⟩ : syracuseStep 1618767 = 2428151) B2428151
theorem B1618783 : Blo 1617007 1618783 := bstep (se 1 (by rfl) ⟨1214087, by rfl⟩ : syracuseStep 1618783 = 2428175) B2428175
theorem B4608875 : Blo 1617007 4608875 := bstep (se 1 (by rfl) ⟨3456656, by rfl⟩ : syracuseStep 4608875 = 6913313) B6913313
theorem B1618811 : Blo 1617007 1618811 := bstep (se 1 (by rfl) ⟨1214108, by rfl⟩ : syracuseStep 1618811 = 2428217) B2428217
theorem B5460911 : Blo 1617007 5460911 := bstep (se 1 (by rfl) ⟨4095683, by rfl⟩ : syracuseStep 5460911 = 8191367) B8191367
theorem B1618863 : Blo 1617007 1618863 := bstep (se 1 (by rfl) ⟨1214147, by rfl⟩ : syracuseStep 1618863 = 2428295) B2428295
theorem B3642299 : Blo 1617007 3642299 := bstep (se 1 (by rfl) ⟨2731724, by rfl⟩ : syracuseStep 3642299 = 5463449) B5463449
theorem B1618887 : Blo 1617007 1618887 := bstep (se 1 (by rfl) ⟨1214165, by rfl⟩ : syracuseStep 1618887 = 2428331) B2428331
theorem B1618907 : Blo 1617007 1618907 := bstep (se 1 (by rfl) ⟨1214180, by rfl⟩ : syracuseStep 1618907 = 2428361) B2428361
theorem B9335827 : Blo 1617007 9335827 := bstep (se 1 (by rfl) ⟨7001870, by rfl⟩ : syracuseStep 9335827 = 14003741) B14003741
theorem B1618983 : Blo 1617007 1618983 := bstep (se 1 (by rfl) ⟨1214237, by rfl⟩ : syracuseStep 1618983 = 2428475) B2428475
theorem B3642425 : Blo 1617007 3642425 := bstep (se 2 (by rfl) ⟨1365909, by rfl⟩ : syracuseStep 3642425 = 2731819) B2731819
theorem B8189099 : Blo 1617007 8189099 := bstep (se 1 (by rfl) ⟨6141824, by rfl⟩ : syracuseStep 8189099 = 12283649) B12283649
theorem B3642767 : Blo 1617007 3642767 := bstep (se 1 (by rfl) ⟨2732075, by rfl⟩ : syracuseStep 3642767 = 5464151) B5464151
theorem B78681563 : Blo 1617007 78681563 := bstep (se 1 (by rfl) ⟨59011172, by rfl⟩ : syracuseStep 78681563 = 118022345) B118022345
theorem B3454427 : Blo 1617007 3454427 := bstep (se 1 (by rfl) ⟨2590820, by rfl⟩ : syracuseStep 3454427 = 5181641) B5181641
theorem B5182985 : Blo 1617007 5182985 := bstep (se 2 (by rfl) ⟨1943619, by rfl⟩ : syracuseStep 5182985 = 3887239) B3887239
theorem B4797991 : Blo 1617007 4797991 := bstep (se 1 (by rfl) ⟨3598493, by rfl⟩ : syracuseStep 4797991 = 7196987) B7196987
theorem B4093537 : Blo 1617007 4093537 := bstep (se 2 (by rfl) ⟨1535076, by rfl⟩ : syracuseStep 4093537 = 3070153) B3070153
theorem B13293179 : Blo 1617007 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B4920955 : Blo 1617007 4920955 := bstep (se 1 (by rfl) ⟨3690716, by rfl⟩ : syracuseStep 4920955 = 7381433) B7381433
theorem B11662987 : Blo 1617007 11662987 := bstep (se 1 (by rfl) ⟨8747240, by rfl⟩ : syracuseStep 11662987 = 17494481) B17494481
theorem B8189585 : Blo 1617007 8189585 := bstep (se 2 (by rfl) ⟨3071094, by rfl⟩ : syracuseStep 8189585 = 6142189) B6142189
theorem B2914003 : Blo 1617007 2914003 := bstep (se 1 (by rfl) ⟨2185502, by rfl⟩ : syracuseStep 2914003 = 4371005) B4371005
theorem B6141689 : Blo 1617007 6141689 := bstep (se 2 (by rfl) ⟨2303133, by rfl⟩ : syracuseStep 6141689 = 4606267) B4606267
theorem B3069971 : Blo 1617007 3069971 := bstep (se 1 (by rfl) ⟨2302478, by rfl⟩ : syracuseStep 3069971 = 4604957) B4604957
theorem B4610105 : Blo 1617007 4610105 := bstep (se 2 (by rfl) ⟨1728789, by rfl⟩ : syracuseStep 4610105 = 3457579) B3457579
theorem B7772249 : Blo 1617007 7772249 := bstep (se 2 (by rfl) ⟨2914593, by rfl⟩ : syracuseStep 7772249 = 5829187) B5829187
theorem B2766971 : Blo 1617007 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B3070199 : Blo 1617007 3070199 := bstep (se 1 (by rfl) ⟨2302649, by rfl⟩ : syracuseStep 3070199 = 4605299) B4605299
theorem B21027275 : Blo 1617007 21027275 := bstep (se 1 (by rfl) ⟨15770456, by rfl⟩ : syracuseStep 21027275 = 31540913) B31540913
theorem B39385547 : Blo 1617007 39385547 := bstep (se 1 (by rfl) ⟨29539160, by rfl⟩ : syracuseStep 39385547 = 59078321) B59078321
theorem B2914825 : Blo 1617007 2914825 := bstep (se 2 (by rfl) ⟨1093059, by rfl⟩ : syracuseStep 2914825 = 2186119) B2186119
theorem B10369559 : Blo 1617007 10369559 := bstep (se 1 (by rfl) ⟨7777169, by rfl⟩ : syracuseStep 10369559 = 15554339) B15554339
theorem B4094489 : Blo 1617007 4094489 := bstep (se 2 (by rfl) ⟨1535433, by rfl⟩ : syracuseStep 4094489 = 3070867) B3070867
theorem B2628175 : Blo 1617007 2628175 := bstep (se 1 (by rfl) ⟨1971131, by rfl⟩ : syracuseStep 2628175 = 3942263) B3942263
theorem B6912697 : Blo 1617007 6912697 := bstep (se 2 (by rfl) ⟨2592261, by rfl⟩ : syracuseStep 6912697 = 5184523) B5184523
theorem B6142675 : Blo 1617007 6142675 := bstep (se 1 (by rfl) ⟨4607006, by rfl⟩ : syracuseStep 6142675 = 9214013) B9214013
theorem B291625757 : Blo 1617007 291625757 := bstep (se 3 (by rfl) ⟨54679829, by rfl⟩ : syracuseStep 291625757 = 109359659) B109359659
theorem B3455905 : Blo 1617007 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B4094995 : Blo 1617007 4094995 := bstep (se 1 (by rfl) ⟨3071246, by rfl⟩ : syracuseStep 4094995 = 6142493) B6142493
theorem B6143147 : Blo 1617007 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B4152491 : Blo 1617007 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B21060803 : Blo 1617007 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B18930935 : Blo 1617007 18930935 := bstep (se 1 (by rfl) ⟨14198201, by rfl⟩ : syracuseStep 18930935 = 28396403) B28396403
theorem B5463287 : Blo 1617007 5463287 := bstep (se 1 (by rfl) ⟨4097465, by rfl⟩ : syracuseStep 5463287 = 8194931) B8194931
theorem B10362127 : Blo 1617007 10362127 := bstep (se 1 (by rfl) ⟨7771595, by rfl⟩ : syracuseStep 10362127 = 15543191) B15543191
theorem B5463611 : Blo 1617007 5463611 := bstep (se 1 (by rfl) ⟨4097708, by rfl⟩ : syracuseStep 5463611 = 8195417) B8195417
theorem B3071611 : Blo 1617007 3071611 := bstep (se 1 (by rfl) ⟨2303708, by rfl⟩ : syracuseStep 3071611 = 4607417) B4607417
theorem B4669127 : Blo 1617007 4669127 := bstep (se 1 (by rfl) ⟨3501845, by rfl⟩ : syracuseStep 4669127 = 7003691) B7003691
theorem B5463881 : Blo 1617007 5463881 := bstep (se 2 (by rfl) ⟨2048955, by rfl⟩ : syracuseStep 5463881 = 4097911) B4097911
theorem B3071839 : Blo 1617007 3071839 := bstep (se 1 (by rfl) ⟨2303879, by rfl⟩ : syracuseStep 3071839 = 4607759) B4607759
theorem B2187103 : Blo 1617007 2187103 := bstep (se 1 (by rfl) ⟨1640327, by rfl⟩ : syracuseStep 2187103 = 3280655) B3280655
theorem B8191853 : Blo 1617007 8191853 := bstep (se 3 (by rfl) ⟨1535972, by rfl⟩ : syracuseStep 8191853 = 3071945) B3071945
theorem B12279761 : Blo 1617007 12279761 := bstep (se 2 (by rfl) ⟨4604910, by rfl⟩ : syracuseStep 12279761 = 9209821) B9209821
theorem B22749191 : Blo 1617007 22749191 := bstep (se 1 (by rfl) ⟨17061893, by rfl⟩ : syracuseStep 22749191 = 34123787) B34123787
theorem B4096129 : Blo 1617007 4096129 := bstep (se 2 (by rfl) ⟨1536048, by rfl⟩ : syracuseStep 4096129 = 3072097) B3072097
theorem B94609619 : Blo 1617007 94609619 := bstep (se 1 (by rfl) ⟨70957214, by rfl⟩ : syracuseStep 94609619 = 141914429) B141914429
theorem B15556951 : Blo 1617007 15556951 := bstep (se 1 (by rfl) ⟨11667713, by rfl⟩ : syracuseStep 15556951 = 23335427) B23335427
theorem B5185883 : Blo 1617007 5185883 := bstep (se 1 (by rfl) ⟨3889412, by rfl⟩ : syracuseStep 5185883 = 7778825) B7778825
theorem B17490329 : Blo 1617007 17490329 := bstep (se 2 (by rfl) ⟨6558873, by rfl⟩ : syracuseStep 17490329 = 13117747) B13117747
theorem B3072583 : Blo 1617007 3072583 := bstep (se 1 (by rfl) ⟨2304437, by rfl⟩ : syracuseStep 3072583 = 4608875) B4608875
theorem B2425679 : Blo 1617007 2425679 := bstep (se 1 (by rfl) ⟨1819259, by rfl⟩ : syracuseStep 2425679 = 3638519) B3638519
theorem B1819471 : Blo 1617007 1819471 := bstep (se 1 (by rfl) ⟨1364603, by rfl⟩ : syracuseStep 1819471 = 2729207) B2729207
theorem B8749903 : Blo 1617007 8749903 := bstep (se 1 (by rfl) ⟨6562427, by rfl⟩ : syracuseStep 8749903 = 13124855) B13124855
theorem B9216929 : Blo 1617007 9216929 := bstep (se 2 (by rfl) ⟨3456348, by rfl⟩ : syracuseStep 9216929 = 6912697) B6912697
theorem B4096939 : Blo 1617007 4096939 := bstep (se 1 (by rfl) ⟨3072704, by rfl⟩ : syracuseStep 4096939 = 6145409) B6145409
theorem B8192987 : Blo 1617007 8192987 := bstep (se 1 (by rfl) ⟨6144740, by rfl⟩ : syracuseStep 8192987 = 12289481) B12289481
theorem B52454375 : Blo 1617007 52454375 := bstep (se 1 (by rfl) ⟨39340781, by rfl⟩ : syracuseStep 52454375 = 78681563) B78681563
theorem B8741945 : Blo 1617007 8741945 := bstep (se 2 (by rfl) ⟨3278229, by rfl⟩ : syracuseStep 8741945 = 6556459) B6556459
theorem B4605025 : Blo 1617007 4605025 := bstep (se 2 (by rfl) ⟨1726884, by rfl⟩ : syracuseStep 4605025 = 3453769) B3453769
theorem B8193149 : Blo 1617007 8193149 := bstep (se 3 (by rfl) ⟨1536215, by rfl⟩ : syracuseStep 8193149 = 3072431) B3072431
theorem B2426075 : Blo 1617007 2426075 := bstep (se 1 (by rfl) ⟨1819556, by rfl⟩ : syracuseStep 2426075 = 3639113) B3639113
theorem B1819867 : Blo 1617007 1819867 := bstep (se 1 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 1819867 = 2729801) B2729801
theorem B4097243 : Blo 1617007 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B1639711 : Blo 1617007 1639711 := bstep (se 1 (by rfl) ⟨1229783, by rfl⟩ : syracuseStep 1639711 = 2459567) B2459567
theorem B6915415 : Blo 1617007 6915415 := bstep (se 1 (by rfl) ⟨5186561, by rfl⟩ : syracuseStep 6915415 = 10373123) B10373123
theorem B4097375 : Blo 1617007 4097375 := bstep (se 1 (by rfl) ⟨3073031, by rfl⟩ : syracuseStep 4097375 = 6146063) B6146063
theorem B13821293 : Blo 1617007 13821293 := bstep (se 3 (by rfl) ⟨2591492, by rfl⟩ : syracuseStep 13821293 = 5182985) B5182985
theorem B3073403 : Blo 1617007 3073403 := bstep (se 1 (by rfl) ⟨2305052, by rfl⟩ : syracuseStep 3073403 = 4610105) B4610105
theorem B2426249 : Blo 1617007 2426249 := bstep (se 2 (by rfl) ⟨909843, by rfl⟩ : syracuseStep 2426249 = 1819687) B1819687
theorem B8193473 : Blo 1617007 8193473 := bstep (se 2 (by rfl) ⟨3072552, by rfl⟩ : syracuseStep 8193473 = 6145105) B6145105
theorem B1820155 : Blo 1617007 1820155 := bstep (se 1 (by rfl) ⟨1365116, by rfl⟩ : syracuseStep 1820155 = 2730233) B2730233
theorem B3278431 : Blo 1617007 3278431 := bstep (se 1 (by rfl) ⟨2458823, by rfl⟩ : syracuseStep 3278431 = 4917647) B4917647
theorem B3638879 : Blo 1617007 3638879 := bstep (se 1 (by rfl) ⟨2729159, by rfl⟩ : syracuseStep 3638879 = 5458319) B5458319
theorem B14018183 : Blo 1617007 14018183 := bstep (se 1 (by rfl) ⟨10513637, by rfl⟩ : syracuseStep 14018183 = 21027275) B21027275
theorem B26257031 : Blo 1617007 26257031 := bstep (se 1 (by rfl) ⟨19692773, by rfl⟩ : syracuseStep 26257031 = 39385547) B39385547
theorem B1820335 : Blo 1617007 1820335 := bstep (se 1 (by rfl) ⟨1365251, by rfl⟩ : syracuseStep 1820335 = 2730503) B2730503
theorem B2729659 : Blo 1617007 2729659 := bstep (se 1 (by rfl) ⟨2047244, by rfl⟩ : syracuseStep 2729659 = 4094489) B4094489
theorem B2426603 : Blo 1617007 2426603 := bstep (se 1 (by rfl) ⟨1819952, by rfl⟩ : syracuseStep 2426603 = 3639905) B3639905
theorem B3639095 : Blo 1617007 3639095 := bstep (se 1 (by rfl) ⟨2729321, by rfl⟩ : syracuseStep 3639095 = 5458643) B5458643
theorem B12281705 : Blo 1617007 12281705 := bstep (se 2 (by rfl) ⟨4605639, by rfl⟩ : syracuseStep 12281705 = 9211279) B9211279
theorem B2426831 : Blo 1617007 2426831 := bstep (se 1 (by rfl) ⟨1820123, by rfl⟩ : syracuseStep 2426831 = 3640247) B3640247
theorem B1820623 : Blo 1617007 1820623 := bstep (se 1 (by rfl) ⟨1365467, by rfl⟩ : syracuseStep 1820623 = 2730935) B2730935
theorem B4098073 : Blo 1617007 4098073 := bstep (se 2 (by rfl) ⟨1536777, by rfl⟩ : syracuseStep 4098073 = 3073555) B3073555
theorem B3639401 : Blo 1617007 3639401 := bstep (se 2 (by rfl) ⟨1364775, by rfl⟩ : syracuseStep 3639401 = 2729551) B2729551
theorem B5458049 : Blo 1617007 5458049 := bstep (se 2 (by rfl) ⟨2046768, by rfl⟩ : syracuseStep 5458049 = 4093537) B4093537
theorem B15550649 : Blo 1617007 15550649 := bstep (se 2 (by rfl) ⟨5831493, by rfl⟩ : syracuseStep 15550649 = 11662987) B11662987
theorem B3885337 : Blo 1617007 3885337 := bstep (se 2 (by rfl) ⟨1457001, by rfl⟩ : syracuseStep 3885337 = 2914003) B2914003
theorem B2427227 : Blo 1617007 2427227 := bstep (se 1 (by rfl) ⟨1820420, by rfl⟩ : syracuseStep 2427227 = 3640841) B3640841
theorem B1821019 : Blo 1617007 1821019 := bstep (se 1 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 1821019 = 2731529) B2731529
theorem B1821127 : Blo 1617007 1821127 := bstep (se 1 (by rfl) ⟨1365845, by rfl⟩ : syracuseStep 1821127 = 2731691) B2731691
theorem B5458427 : Blo 1617007 5458427 := bstep (se 1 (by rfl) ⟨4093820, by rfl⟩ : syracuseStep 5458427 = 8187641) B8187641
theorem B2427455 : Blo 1617007 2427455 := bstep (se 1 (by rfl) ⟨1820591, by rfl⟩ : syracuseStep 2427455 = 3641183) B3641183
theorem B3639887 : Blo 1617007 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B8186507 : Blo 1617007 8186507 := bstep (se 1 (by rfl) ⟨6139880, by rfl⟩ : syracuseStep 8186507 = 12279761) B12279761
theorem B2427575 : Blo 1617007 2427575 := bstep (se 1 (by rfl) ⟨1820681, by rfl⟩ : syracuseStep 2427575 = 3641363) B3641363
theorem B3640031 : Blo 1617007 3640031 := bstep (se 1 (by rfl) ⟨2730023, by rfl⟩ : syracuseStep 3640031 = 5460047) B5460047
theorem B2591455 : Blo 1617007 2591455 := bstep (se 1 (by rfl) ⟨1943591, by rfl⟩ : syracuseStep 2591455 = 3887183) B3887183
theorem B2730719 : Blo 1617007 2730719 := bstep (se 1 (by rfl) ⟨2048039, by rfl⟩ : syracuseStep 2730719 = 4096079) B4096079
theorem B2427803 : Blo 1617007 2427803 := bstep (se 1 (by rfl) ⟨1820852, by rfl⟩ : syracuseStep 2427803 = 3641705) B3641705
theorem B5458859 : Blo 1617007 5458859 := bstep (se 1 (by rfl) ⟨4094144, by rfl⟩ : syracuseStep 5458859 = 8188289) B8188289
theorem B3640283 : Blo 1617007 3640283 := bstep (se 1 (by rfl) ⟨2730212, by rfl⟩ : syracuseStep 3640283 = 5460425) B5460425
theorem B3640463 : Blo 1617007 3640463 := bstep (se 1 (by rfl) ⟨2730347, by rfl⟩ : syracuseStep 3640463 = 5460695) B5460695
theorem B2731151 : Blo 1617007 2731151 := bstep (se 1 (by rfl) ⟨2048363, by rfl⟩ : syracuseStep 2731151 = 4096727) B4096727
theorem B3640553 : Blo 1617007 3640553 := bstep (se 2 (by rfl) ⟨1365207, by rfl⟩ : syracuseStep 3640553 = 2730415) B2730415
theorem B1617183 : Blo 1617007 1617183 := bstep (se 1 (by rfl) ⟨1212887, by rfl⟩ : syracuseStep 1617183 = 2425775) B2425775
theorem B3640607 : Blo 1617007 3640607 := bstep (se 1 (by rfl) ⟨2730455, by rfl⟩ : syracuseStep 3640607 = 5460911) B5460911
theorem B2428199 : Blo 1617007 2428199 := bstep (se 1 (by rfl) ⟨1821149, by rfl⟩ : syracuseStep 2428199 = 3642299) B3642299
theorem B1617243 : Blo 1617007 1617243 := bstep (se 1 (by rfl) ⟨1212932, by rfl⟩ : syracuseStep 1617243 = 2425865) B2425865
theorem B3886433 : Blo 1617007 3886433 := bstep (se 2 (by rfl) ⟨1457412, by rfl⟩ : syracuseStep 3886433 = 2914825) B2914825
theorem B12291425 : Blo 1617007 12291425 := bstep (se 2 (by rfl) ⟨4609284, by rfl⟩ : syracuseStep 12291425 = 9218569) B9218569
theorem B1617263 : Blo 1617007 1617263 := bstep (se 1 (by rfl) ⟨1212947, by rfl⟩ : syracuseStep 1617263 = 2425895) B2425895
theorem B2731387 : Blo 1617007 2731387 := bstep (se 1 (by rfl) ⟨2048540, by rfl⟩ : syracuseStep 2731387 = 4097081) B4097081
theorem B2428283 : Blo 1617007 2428283 := bstep (se 1 (by rfl) ⟨1821212, by rfl⟩ : syracuseStep 2428283 = 3642425) B3642425
theorem B1617319 : Blo 1617007 1617319 := bstep (se 1 (by rfl) ⟨1212989, by rfl⟩ : syracuseStep 1617319 = 2425979) B2425979
theorem B5459399 : Blo 1617007 5459399 := bstep (se 1 (by rfl) ⟨4094549, by rfl⟩ : syracuseStep 5459399 = 8189099) B8189099
theorem B9219527 : Blo 1617007 9219527 := bstep (se 1 (by rfl) ⟨6914645, by rfl⟩ : syracuseStep 9219527 = 13829291) B13829291
theorem B2428409 : Blo 1617007 2428409 := bstep (se 2 (by rfl) ⟨910653, by rfl⟩ : syracuseStep 2428409 = 1821307) B1821307
theorem B1617403 : Blo 1617007 1617403 := bstep (se 1 (by rfl) ⟨1213052, by rfl⟩ : syracuseStep 1617403 = 2426105) B2426105
theorem B1617471 : Blo 1617007 1617471 := bstep (se 1 (by rfl) ⟨1213103, by rfl⟩ : syracuseStep 1617471 = 2426207) B2426207
theorem B1617479 : Blo 1617007 1617479 := bstep (se 1 (by rfl) ⟨1213109, by rfl⟩ : syracuseStep 1617479 = 2426219) B2426219
theorem B2428511 : Blo 1617007 2428511 := bstep (se 1 (by rfl) ⟨1821383, by rfl⟩ : syracuseStep 2428511 = 3642767) B3642767
theorem B1617631 : Blo 1617007 1617631 := bstep (se 1 (by rfl) ⟨1213223, by rfl⟩ : syracuseStep 1617631 = 2426447) B2426447
theorem B121335533 : Blo 1617007 121335533 := bstep (se 3 (by rfl) ⟨22750412, by rfl⟩ : syracuseStep 121335533 = 45500825) B45500825
theorem B5459723 : Blo 1617007 5459723 := bstep (se 1 (by rfl) ⟨4094792, by rfl⟩ : syracuseStep 5459723 = 8189585) B8189585
theorem B39341861 : Blo 1617007 39341861 := bstep (se 4 (by rfl) ⟨3688299, by rfl⟩ : syracuseStep 39341861 = 7376599) B7376599
theorem B3641129 : Blo 1617007 3641129 := bstep (se 2 (by rfl) ⟨1365423, by rfl⟩ : syracuseStep 3641129 = 2730847) B2730847
theorem B1617711 : Blo 1617007 1617711 := bstep (se 1 (by rfl) ⟨1213283, by rfl⟩ : syracuseStep 1617711 = 2426567) B2426567
theorem B4607873 : Blo 1617007 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B1617819 : Blo 1617007 1617819 := bstep (se 1 (by rfl) ⟨1213364, by rfl⟩ : syracuseStep 1617819 = 2426729) B2426729
theorem B9211805 : Blo 1617007 9211805 := bstep (se 3 (by rfl) ⟨1727213, by rfl⟩ : syracuseStep 9211805 = 3454427) B3454427
theorem B1617871 : Blo 1617007 1617871 := bstep (se 1 (by rfl) ⟨1213403, by rfl⟩ : syracuseStep 1617871 = 2426807) B2426807
theorem B1617895 : Blo 1617007 1617895 := bstep (se 1 (by rfl) ⟨1213421, by rfl⟩ : syracuseStep 1617895 = 2426843) B2426843
theorem B20721689 : Blo 1617007 20721689 := bstep (se 2 (by rfl) ⟨7770633, by rfl⟩ : syracuseStep 20721689 = 15541267) B15541267
theorem B12447769 : Blo 1617007 12447769 := bstep (se 2 (by rfl) ⟨4667913, by rfl⟩ : syracuseStep 12447769 = 9335827) B9335827
theorem B5459993 : Blo 1617007 5459993 := bstep (se 2 (by rfl) ⟨2047497, by rfl⟩ : syracuseStep 5459993 = 4094995) B4094995
theorem B5181499 : Blo 1617007 5181499 := bstep (se 1 (by rfl) ⟨3886124, by rfl⟩ : syracuseStep 5181499 = 7772249) B7772249
theorem B1618207 : Blo 1617007 1618207 := bstep (se 1 (by rfl) ⟨1213655, by rfl⟩ : syracuseStep 1618207 = 2427311) B2427311
theorem B15544649 : Blo 1617007 15544649 := bstep (se 2 (by rfl) ⟨5829243, by rfl⟩ : syracuseStep 15544649 = 11658487) B11658487
theorem B27652427 : Blo 1617007 27652427 := bstep (se 1 (by rfl) ⟨20739320, by rfl⟩ : syracuseStep 27652427 = 41478641) B41478641
theorem B1618267 : Blo 1617007 1618267 := bstep (se 1 (by rfl) ⟨1213700, by rfl⟩ : syracuseStep 1618267 = 2427401) B2427401
theorem B13816169 : Blo 1617007 13816169 := bstep (se 2 (by rfl) ⟨5181063, by rfl⟩ : syracuseStep 13816169 = 10362127) B10362127
theorem B1618287 : Blo 1617007 1618287 := bstep (se 1 (by rfl) ⟨1213715, by rfl⟩ : syracuseStep 1618287 = 2427431) B2427431
theorem B1618343 : Blo 1617007 1618343 := bstep (se 1 (by rfl) ⟨1213757, by rfl⟩ : syracuseStep 1618343 = 2427515) B2427515
theorem B1618427 : Blo 1617007 1618427 := bstep (se 1 (by rfl) ⟨1213820, by rfl⟩ : syracuseStep 1618427 = 2427641) B2427641
theorem B194417171 : Blo 1617007 194417171 := bstep (se 1 (by rfl) ⟨145812878, by rfl⟩ : syracuseStep 194417171 = 291625757) B291625757
theorem B1618495 : Blo 1617007 1618495 := bstep (se 1 (by rfl) ⟨1213871, by rfl⟩ : syracuseStep 1618495 = 2427743) B2427743
theorem B1618503 : Blo 1617007 1618503 := bstep (se 1 (by rfl) ⟨1213877, by rfl⟩ : syracuseStep 1618503 = 2427755) B2427755
theorem B1618655 : Blo 1617007 1618655 := bstep (se 1 (by rfl) ⟨1213991, by rfl⟩ : syracuseStep 1618655 = 2427983) B2427983
theorem B1618735 : Blo 1617007 1618735 := bstep (se 1 (by rfl) ⟨1214051, by rfl⟩ : syracuseStep 1618735 = 2428103) B2428103
theorem B12620623 : Blo 1617007 12620623 := bstep (se 1 (by rfl) ⟨9465467, by rfl⟩ : syracuseStep 12620623 = 18930935) B18930935
theorem B3642191 : Blo 1617007 3642191 := bstep (se 1 (by rfl) ⟨2731643, by rfl⟩ : syracuseStep 3642191 = 5463287) B5463287
theorem B1618843 : Blo 1617007 1618843 := bstep (se 1 (by rfl) ⟨1214132, by rfl⟩ : syracuseStep 1618843 = 2428265) B2428265
theorem B1618895 : Blo 1617007 1618895 := bstep (se 1 (by rfl) ⟨1214171, by rfl⟩ : syracuseStep 1618895 = 2428343) B2428343
theorem B1618919 : Blo 1617007 1618919 := bstep (se 1 (by rfl) ⟨1214189, by rfl⟩ : syracuseStep 1618919 = 2428379) B2428379
theorem B3642407 : Blo 1617007 3642407 := bstep (se 1 (by rfl) ⟨2731805, by rfl⟩ : syracuseStep 3642407 = 5463611) B5463611
theorem B23311439 : Blo 1617007 23311439 := bstep (se 1 (by rfl) ⟨17483579, by rfl⟩ : syracuseStep 23311439 = 34967159) B34967159
theorem B8303705 : Blo 1617007 8303705 := bstep (se 2 (by rfl) ⟨3113889, by rfl⟩ : syracuseStep 8303705 = 6227779) B6227779
theorem B4093051 : Blo 1617007 4093051 := bstep (se 1 (by rfl) ⟨3069788, by rfl⟩ : syracuseStep 4093051 = 6139577) B6139577
theorem B3642587 : Blo 1617007 3642587 := bstep (se 1 (by rfl) ⟨2731940, by rfl⟩ : syracuseStep 3642587 = 5463881) B5463881
theorem B5461235 : Blo 1617007 5461235 := bstep (se 1 (by rfl) ⟨4095926, by rfl⟩ : syracuseStep 5461235 = 8191853) B8191853
theorem B12293369 : Blo 1617007 12293369 := bstep (se 2 (by rfl) ⟨4610013, by rfl⟩ : syracuseStep 12293369 = 9220027) B9220027
theorem B5461343 : Blo 1617007 5461343 := bstep (se 1 (by rfl) ⟨4096007, by rfl⟩ : syracuseStep 5461343 = 8192015) B8192015
theorem B39359849 : Blo 1617007 39359849 := bstep (se 2 (by rfl) ⟨14759943, by rfl⟩ : syracuseStep 39359849 = 29519887) B29519887
theorem B4150651 : Blo 1617007 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B31094219 : Blo 1617007 31094219 := bstep (se 1 (by rfl) ⟨23320664, by rfl⟩ : syracuseStep 31094219 = 46641329) B46641329
theorem B7378589 : Blo 1617007 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B26245093 : Blo 1617007 26245093 := bstep (se 4 (by rfl) ⟨2460477, by rfl⟩ : syracuseStep 26245093 = 4920955) B4920955
theorem B4151321 : Blo 1617007 4151321 := bstep (se 2 (by rfl) ⟨1556745, by rfl⟩ : syracuseStep 4151321 = 3113491) B3113491
theorem B3504233 : Blo 1617007 3504233 := bstep (se 2 (by rfl) ⟨1314087, by rfl⟩ : syracuseStep 3504233 = 2628175) B2628175
theorem B8190233 : Blo 1617007 8190233 := bstep (se 2 (by rfl) ⟨3071337, by rfl⟩ : syracuseStep 8190233 = 6142675) B6142675
theorem B8862119 : Blo 1617007 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B4094459 : Blo 1617007 4094459 := bstep (se 1 (by rfl) ⟨3070844, by rfl⟩ : syracuseStep 4094459 = 6141689) B6141689
theorem B24910375 : Blo 1617007 24910375 := bstep (se 1 (by rfl) ⟨18682781, by rfl⟩ : syracuseStep 24910375 = 37365563) B37365563
theorem B2185903 : Blo 1617007 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B3070639 : Blo 1617007 3070639 := bstep (se 1 (by rfl) ⟨2302979, by rfl⟩ : syracuseStep 3070639 = 4605959) B4605959
theorem B2046647 : Blo 1617007 2046647 := bstep (se 1 (by rfl) ⟨1534985, by rfl⟩ : syracuseStep 2046647 = 3069971) B3069971
theorem B2046799 : Blo 1617007 2046799 := bstep (se 1 (by rfl) ⟨1535099, by rfl⟩ : syracuseStep 2046799 = 3070199) B3070199
theorem B5462909 : Blo 1617007 5462909 := bstep (se 3 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 5462909 = 2048591) B2048591
theorem B6913039 : Blo 1617007 6913039 := bstep (se 1 (by rfl) ⟨5184779, by rfl⟩ : syracuseStep 6913039 = 10369559) B10369559
theorem B5463179 : Blo 1617007 5463179 := bstep (se 1 (by rfl) ⟨4097384, by rfl⟩ : syracuseStep 5463179 = 8194769) B8194769
theorem B3071209 : Blo 1617007 3071209 := bstep (se 2 (by rfl) ⟨1151703, by rfl⟩ : syracuseStep 3071209 = 2303407) B2303407
theorem B6397321 : Blo 1617007 6397321 := bstep (se 2 (by rfl) ⟨2398995, by rfl⟩ : syracuseStep 6397321 = 4797991) B4797991
theorem B4095431 : Blo 1617007 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B2768327 : Blo 1617007 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B14040535 : Blo 1617007 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B14015959 : Blo 1617007 14015959 := bstep (se 1 (by rfl) ⟨10511969, by rfl⟩ : syracuseStep 14015959 = 21023939) B21023939
theorem B4095481 : Blo 1617007 4095481 := bstep (se 2 (by rfl) ⟨1535805, by rfl⟩ : syracuseStep 4095481 = 3071611) B3071611
theorem B119709251 : Blo 1617007 119709251 := bstep (se 1 (by rfl) ⟨89781938, by rfl⟩ : syracuseStep 119709251 = 179563877) B179563877
theorem B4095785 : Blo 1617007 4095785 := bstep (se 2 (by rfl) ⟨1535919, by rfl⟩ : syracuseStep 4095785 = 3071839) B3071839
theorem B2916137 : Blo 1617007 2916137 := bstep (se 2 (by rfl) ⟨1093551, by rfl⟩ : syracuseStep 2916137 = 2187103) B2187103
theorem B3112751 : Blo 1617007 3112751 := bstep (se 1 (by rfl) ⟨2334563, by rfl⟩ : syracuseStep 3112751 = 4669127) B4669127
theorem B4210537 : Blo 1617007 4210537 := bstep (se 2 (by rfl) ⟨1578951, by rfl⟩ : syracuseStep 4210537 = 3157903) B3157903
theorem B16597025 : Blo 1617007 16597025 := bstep (se 2 (by rfl) ⟨6223884, by rfl⟩ : syracuseStep 16597025 = 12447769) B12447769
theorem B5464097 : Blo 1617007 5464097 := bstep (se 2 (by rfl) ⟨2049036, by rfl⟩ : syracuseStep 5464097 = 4098073) B4098073
theorem B3457255 : Blo 1617007 3457255 := bstep (se 1 (by rfl) ⟨2592941, by rfl⟩ : syracuseStep 3457255 = 5185883) B5185883
theorem B20742601 : Blo 1617007 20742601 := bstep (se 2 (by rfl) ⟨7778475, by rfl⟩ : syracuseStep 20742601 = 15556951) B15556951
theorem B6144619 : Blo 1617007 6144619 := bstep (se 1 (by rfl) ⟨4608464, by rfl⟩ : syracuseStep 6144619 = 9216929) B9216929
theorem B15540959 : Blo 1617007 15540959 := bstep (se 1 (by rfl) ⟨11655719, by rfl⟩ : syracuseStep 15540959 = 23311439) B23311439
theorem B4096777 : Blo 1617007 4096777 := bstep (se 2 (by rfl) ⟨1536291, by rfl⟩ : syracuseStep 4096777 = 3072583) B3072583
theorem B41452397 : Blo 1617007 41452397 := bstep (se 3 (by rfl) ⟨7772324, by rfl⟩ : syracuseStep 41452397 = 15544649) B15544649
theorem B2425919 : Blo 1617007 2425919 := bstep (se 1 (by rfl) ⟨1819439, by rfl⟩ : syracuseStep 2425919 = 3638879) B3638879
theorem B2729065 : Blo 1617007 2729065 := bstep (se 2 (by rfl) ⟨1023399, by rfl⟩ : syracuseStep 2729065 = 2046799) B2046799
theorem B2425961 : Blo 1617007 2425961 := bstep (se 2 (by rfl) ⟨909735, by rfl⟩ : syracuseStep 2425961 = 1819471) B1819471
theorem B16827497 : Blo 1617007 16827497 := bstep (se 2 (by rfl) ⟨6310311, by rfl⟩ : syracuseStep 16827497 = 12620623) B12620623
theorem B11666537 : Blo 1617007 11666537 := bstep (se 2 (by rfl) ⟨4374951, by rfl⟩ : syracuseStep 11666537 = 8749903) B8749903
theorem B2426063 : Blo 1617007 2426063 := bstep (se 1 (by rfl) ⟨1819547, by rfl⟩ : syracuseStep 2426063 = 3639095) B3639095
theorem B9217385 : Blo 1617007 9217385 := bstep (se 2 (by rfl) ⟨3456519, by rfl⟩ : syracuseStep 9217385 = 6913039) B6913039
theorem B2426267 : Blo 1617007 2426267 := bstep (se 1 (by rfl) ⟨1819700, by rfl⟩ : syracuseStep 2426267 = 3639401) B3639401
theorem B2336155 : Blo 1617007 2336155 := bstep (se 1 (by rfl) ⟨1752116, by rfl⟩ : syracuseStep 2336155 = 3504233) B3504233
theorem B3638699 : Blo 1617007 3638699 := bstep (se 1 (by rfl) ⟨2729024, by rfl⟩ : syracuseStep 3638699 = 5458049) B5458049
theorem B5457401 : Blo 1617007 5457401 := bstep (se 2 (by rfl) ⟨2046525, by rfl⟩ : syracuseStep 5457401 = 4093051) B4093051
theorem B5908079 : Blo 1617007 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B2426489 : Blo 1617007 2426489 := bstep (se 2 (by rfl) ⟨909933, by rfl⟩ : syracuseStep 2426489 = 1819867) B1819867
theorem B3638951 : Blo 1617007 3638951 := bstep (se 1 (by rfl) ⟨2729213, by rfl⟩ : syracuseStep 3638951 = 5458427) B5458427
theorem B2729639 : Blo 1617007 2729639 := bstep (se 1 (by rfl) ⟨2047229, by rfl⟩ : syracuseStep 2729639 = 4094459) B4094459
theorem B2426591 : Blo 1617007 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B5457671 : Blo 1617007 5457671 := bstep (se 1 (by rfl) ⟨4093253, by rfl⟩ : syracuseStep 5457671 = 8186507) B8186507
theorem B5457725 : Blo 1617007 5457725 := bstep (se 3 (by rfl) ⟨1023323, by rfl⟩ : syracuseStep 5457725 = 2046647) B2046647
theorem B2426687 : Blo 1617007 2426687 := bstep (se 1 (by rfl) ⟨1820015, by rfl⟩ : syracuseStep 2426687 = 3640031) B3640031
theorem B1820479 : Blo 1617007 1820479 := bstep (se 1 (by rfl) ⟨1365359, by rfl⟩ : syracuseStep 1820479 = 2730719) B2730719
theorem B8529761 : Blo 1617007 8529761 := bstep (se 2 (by rfl) ⟨3198660, by rfl⟩ : syracuseStep 8529761 = 6397321) B6397321
theorem B3639239 : Blo 1617007 3639239 := bstep (se 1 (by rfl) ⟨2729429, by rfl⟩ : syracuseStep 3639239 = 5458859) B5458859
theorem B18720713 : Blo 1617007 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B2426855 : Blo 1617007 2426855 := bstep (se 1 (by rfl) ⟨1820141, by rfl⟩ : syracuseStep 2426855 = 3640283) B3640283
theorem B2426873 : Blo 1617007 2426873 := bstep (se 2 (by rfl) ⟨910077, by rfl⟩ : syracuseStep 2426873 = 1820155) B1820155
theorem B2426975 : Blo 1617007 2426975 := bstep (se 1 (by rfl) ⟨1820231, by rfl⟩ : syracuseStep 2426975 = 3640463) B3640463
theorem B1820767 : Blo 1617007 1820767 := bstep (se 1 (by rfl) ⟨1365575, by rfl⟩ : syracuseStep 1820767 = 2731151) B2731151
theorem B2427035 : Blo 1617007 2427035 := bstep (se 1 (by rfl) ⟨1820276, by rfl⟩ : syracuseStep 2427035 = 3640553) B3640553
theorem B2427071 : Blo 1617007 2427071 := bstep (se 1 (by rfl) ⟨1820303, by rfl⟩ : syracuseStep 2427071 = 3640607) B3640607
theorem B2427113 : Blo 1617007 2427113 := bstep (se 2 (by rfl) ⟨910167, by rfl⟩ : syracuseStep 2427113 = 1820335) B1820335
theorem B2590955 : Blo 1617007 2590955 := bstep (se 1 (by rfl) ⟨1943216, by rfl⟩ : syracuseStep 2590955 = 3886433) B3886433
theorem B8194283 : Blo 1617007 8194283 := bstep (se 1 (by rfl) ⟨6145712, by rfl⟩ : syracuseStep 8194283 = 12291425) B12291425
theorem B3639545 : Blo 1617007 3639545 := bstep (se 2 (by rfl) ⟨1364829, by rfl⟩ : syracuseStep 3639545 = 2729659) B2729659
theorem B3639599 : Blo 1617007 3639599 := bstep (se 1 (by rfl) ⟨2729699, by rfl⟩ : syracuseStep 3639599 = 5459399) B5459399
theorem B2730287 : Blo 1617007 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B1845551 : Blo 1617007 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B6146351 : Blo 1617007 6146351 := bstep (se 1 (by rfl) ⟨4609763, by rfl⟩ : syracuseStep 6146351 = 9219527) B9219527
theorem B5614049 : Blo 1617007 5614049 := bstep (se 2 (by rfl) ⟨2105268, by rfl⟩ : syracuseStep 5614049 = 4210537) B4210537
theorem B80890355 : Blo 1617007 80890355 := bstep (se 1 (by rfl) ⟨60667766, by rfl⟩ : syracuseStep 80890355 = 121335533) B121335533
theorem B3639815 : Blo 1617007 3639815 := bstep (se 1 (by rfl) ⟨2729861, by rfl⟩ : syracuseStep 3639815 = 5459723) B5459723
theorem B2730523 : Blo 1617007 2730523 := bstep (se 1 (by rfl) ⟨2047892, by rfl⟩ : syracuseStep 2730523 = 4095785) B4095785
theorem B1944091 : Blo 1617007 1944091 := bstep (se 1 (by rfl) ⟨1458068, by rfl⟩ : syracuseStep 1944091 = 2916137) B2916137
theorem B2427419 : Blo 1617007 2427419 := bstep (se 1 (by rfl) ⟨1820564, by rfl⟩ : syracuseStep 2427419 = 3641129) B3641129
theorem B2075167 : Blo 1617007 2075167 := bstep (se 1 (by rfl) ⟨1556375, by rfl⟩ : syracuseStep 2075167 = 3112751) B3112751
theorem B2427497 : Blo 1617007 2427497 := bstep (se 2 (by rfl) ⟨910311, by rfl⟩ : syracuseStep 2427497 = 1820623) B1820623
theorem B15166127 : Blo 1617007 15166127 := bstep (se 1 (by rfl) ⟨11374595, by rfl⟩ : syracuseStep 15166127 = 22749191) B22749191
theorem B13814459 : Blo 1617007 13814459 := bstep (se 1 (by rfl) ⟨10360844, by rfl⟩ : syracuseStep 13814459 = 20721689) B20721689
theorem B3639995 : Blo 1617007 3639995 := bstep (se 1 (by rfl) ⟨2729996, by rfl⟩ : syracuseStep 3639995 = 5459993) B5459993
theorem B6908665 : Blo 1617007 6908665 := bstep (se 2 (by rfl) ⟨2590749, by rfl⟩ : syracuseStep 6908665 = 5181499) B5181499
theorem B63073079 : Blo 1617007 63073079 := bstep (se 1 (by rfl) ⟨47304809, by rfl⟩ : syracuseStep 63073079 = 94609619) B94609619
theorem B18434951 : Blo 1617007 18434951 := bstep (se 1 (by rfl) ⟨13826213, by rfl⟩ : syracuseStep 18434951 = 27652427) B27652427
theorem B9210779 : Blo 1617007 9210779 := bstep (se 1 (by rfl) ⟨6908084, by rfl⟩ : syracuseStep 9210779 = 13816169) B13816169
theorem B11660219 : Blo 1617007 11660219 := bstep (se 1 (by rfl) ⟨8745164, by rfl⟩ : syracuseStep 11660219 = 17490329) B17490329
theorem B5180449 : Blo 1617007 5180449 := bstep (se 2 (by rfl) ⟨1942668, by rfl⟩ : syracuseStep 5180449 = 3885337) B3885337
theorem B2428025 : Blo 1617007 2428025 := bstep (se 2 (by rfl) ⟨910509, by rfl⟩ : syracuseStep 2428025 = 1821019) B1821019
theorem B1617119 : Blo 1617007 1617119 := bstep (se 1 (by rfl) ⟨1212839, by rfl⟩ : syracuseStep 1617119 = 2425679) B2425679
theorem B2428127 : Blo 1617007 2428127 := bstep (se 1 (by rfl) ⟨1821095, by rfl⟩ : syracuseStep 2428127 = 3642191) B3642191
theorem B2428169 : Blo 1617007 2428169 := bstep (se 2 (by rfl) ⟨910563, by rfl⟩ : syracuseStep 2428169 = 1821127) B1821127
theorem B2428271 : Blo 1617007 2428271 := bstep (se 1 (by rfl) ⟨1821203, by rfl⟩ : syracuseStep 2428271 = 3642407) B3642407
theorem B5827963 : Blo 1617007 5827963 := bstep (se 1 (by rfl) ⟨4370972, by rfl⟩ : syracuseStep 5827963 = 8741945) B8741945
theorem B33213833 : Blo 1617007 33213833 := bstep (se 2 (by rfl) ⟨12455187, by rfl⟩ : syracuseStep 33213833 = 24910375) B24910375
theorem B1617383 : Blo 1617007 1617383 := bstep (se 1 (by rfl) ⟨1213037, by rfl⟩ : syracuseStep 1617383 = 2426075) B2426075
theorem B2731495 : Blo 1617007 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B2428391 : Blo 1617007 2428391 := bstep (se 1 (by rfl) ⟨1821293, by rfl⟩ : syracuseStep 2428391 = 3642587) B3642587
theorem B3640823 : Blo 1617007 3640823 := bstep (se 1 (by rfl) ⟨2730617, by rfl⟩ : syracuseStep 3640823 = 5461235) B5461235
theorem B8195579 : Blo 1617007 8195579 := bstep (se 1 (by rfl) ⟨6146684, by rfl⟩ : syracuseStep 8195579 = 12293369) B12293369
theorem B3640895 : Blo 1617007 3640895 := bstep (se 1 (by rfl) ⟨2730671, by rfl⟩ : syracuseStep 3640895 = 5461343) B5461343
theorem B2731583 : Blo 1617007 2731583 := bstep (se 1 (by rfl) ⟨2048687, by rfl⟩ : syracuseStep 2731583 = 4097375) B4097375
theorem B1617499 : Blo 1617007 1617499 := bstep (se 1 (by rfl) ⟨1213124, by rfl⟩ : syracuseStep 1617499 = 2426249) B2426249
theorem B104959597 : Blo 1617007 104959597 := bstep (se 3 (by rfl) ⟨19679924, by rfl⟩ : syracuseStep 104959597 = 39359849) B39359849
theorem B20729479 : Blo 1617007 20729479 := bstep (se 1 (by rfl) ⟨15547109, by rfl⟩ : syracuseStep 20729479 = 31094219) B31094219
theorem B8195741 : Blo 1617007 8195741 := bstep (se 3 (by rfl) ⟨1536701, by rfl⟩ : syracuseStep 8195741 = 3073403) B3073403
theorem B4919059 : Blo 1617007 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B1617735 : Blo 1617007 1617735 := bstep (se 1 (by rfl) ⟨1213301, by rfl⟩ : syracuseStep 1617735 = 2426603) B2426603
theorem B8187803 : Blo 1617007 8187803 := bstep (se 1 (by rfl) ⟨6140852, by rfl⟩ : syracuseStep 8187803 = 12281705) B12281705
theorem B1617887 : Blo 1617007 1617887 := bstep (se 1 (by rfl) ⟨1213415, by rfl⟩ : syracuseStep 1617887 = 2426831) B2426831
theorem B10367099 : Blo 1617007 10367099 := bstep (se 1 (by rfl) ⟨7775324, by rfl⟩ : syracuseStep 10367099 = 15550649) B15550649
theorem B6140033 : Blo 1617007 6140033 := bstep (se 2 (by rfl) ⟨2302512, by rfl⟩ : syracuseStep 6140033 = 4605025) B4605025
theorem B5460155 : Blo 1617007 5460155 := bstep (se 1 (by rfl) ⟨4095116, by rfl⟩ : syracuseStep 5460155 = 8190233) B8190233
theorem B1618151 : Blo 1617007 1618151 := bstep (se 1 (by rfl) ⟨1213613, by rfl⟩ : syracuseStep 1618151 = 2427227) B2427227
theorem B1618303 : Blo 1617007 1618303 := bstep (se 1 (by rfl) ⟨1213727, by rfl⟩ : syracuseStep 1618303 = 2427455) B2427455
theorem B9220553 : Blo 1617007 9220553 := bstep (se 2 (by rfl) ⟨3457707, by rfl⟩ : syracuseStep 9220553 = 6915415) B6915415
theorem B1618383 : Blo 1617007 1618383 := bstep (se 1 (by rfl) ⟨1213787, by rfl⟩ : syracuseStep 1618383 = 2427575) B2427575
theorem B5534201 : Blo 1617007 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B3641849 : Blo 1617007 3641849 := bstep (se 2 (by rfl) ⟨1365693, by rfl⟩ : syracuseStep 3641849 = 2731387) B2731387
theorem B3641939 : Blo 1617007 3641939 := bstep (se 1 (by rfl) ⟨2731454, by rfl⟩ : syracuseStep 3641939 = 5462909) B5462909
theorem B1618535 : Blo 1617007 1618535 := bstep (se 1 (by rfl) ⟨1213901, by rfl⟩ : syracuseStep 1618535 = 2427803) B2427803
theorem B5460641 : Blo 1617007 5460641 := bstep (se 2 (by rfl) ⟨2047740, by rfl⟩ : syracuseStep 5460641 = 4095481) B4095481
theorem B3642119 : Blo 1617007 3642119 := bstep (se 1 (by rfl) ⟨2731589, by rfl⟩ : syracuseStep 3642119 = 5463179) B5463179
theorem B4371241 : Blo 1617007 4371241 := bstep (se 2 (by rfl) ⟨1639215, by rfl⟩ : syracuseStep 4371241 = 3278431) B3278431
theorem B1618799 : Blo 1617007 1618799 := bstep (se 1 (by rfl) ⟨1214099, by rfl⟩ : syracuseStep 1618799 = 2428199) B2428199
theorem B1618855 : Blo 1617007 1618855 := bstep (se 1 (by rfl) ⟨1214141, by rfl⟩ : syracuseStep 1618855 = 2428283) B2428283
theorem B1618939 : Blo 1617007 1618939 := bstep (se 1 (by rfl) ⟨1214204, by rfl⟩ : syracuseStep 1618939 = 2428409) B2428409
theorem B1619007 : Blo 1617007 1619007 := bstep (se 1 (by rfl) ⟨1214255, by rfl⟩ : syracuseStep 1619007 = 2428511) B2428511
theorem B26227907 : Blo 1617007 26227907 := bstep (se 1 (by rfl) ⟨19670930, by rfl⟩ : syracuseStep 26227907 = 39341861) B39341861
theorem B6141203 : Blo 1617007 6141203 := bstep (se 1 (by rfl) ⟨4605902, by rfl⟩ : syracuseStep 6141203 = 9211805) B9211805
theorem B34993457 : Blo 1617007 34993457 := bstep (se 2 (by rfl) ⟨13122546, by rfl⟩ : syracuseStep 34993457 = 26245093) B26245093
theorem B5461505 : Blo 1617007 5461505 := bstep (se 2 (by rfl) ⟨2048064, by rfl⟩ : syracuseStep 5461505 = 4096129) B4096129
theorem B129611447 : Blo 1617007 129611447 := bstep (se 1 (by rfl) ⟨97208585, by rfl⟩ : syracuseStep 129611447 = 194417171) B194417171
theorem B5461991 : Blo 1617007 5461991 := bstep (se 1 (by rfl) ⟨4096493, by rfl⟩ : syracuseStep 5461991 = 8192987) B8192987
theorem B34969583 : Blo 1617007 34969583 := bstep (se 1 (by rfl) ⟨26227187, by rfl⟩ : syracuseStep 34969583 = 52454375) B52454375
theorem B5535803 : Blo 1617007 5535803 := bstep (se 1 (by rfl) ⟨4151852, by rfl⟩ : syracuseStep 5535803 = 8303705) B8303705
theorem B5462099 : Blo 1617007 5462099 := bstep (se 1 (by rfl) ⟨4096574, by rfl⟩ : syracuseStep 5462099 = 8193149) B8193149
theorem B2914537 : Blo 1617007 2914537 := bstep (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) B2185903
theorem B4094185 : Blo 1617007 4094185 := bstep (se 2 (by rfl) ⟨1535319, by rfl⟩ : syracuseStep 4094185 = 3070639) B3070639
theorem B9214195 : Blo 1617007 9214195 := bstep (se 1 (by rfl) ⟨6910646, by rfl⟩ : syracuseStep 9214195 = 13821293) B13821293
theorem B3455273 : Blo 1617007 3455273 := bstep (se 2 (by rfl) ⟨1295727, by rfl⟩ : syracuseStep 3455273 = 2591455) B2591455
theorem B5462315 : Blo 1617007 5462315 := bstep (se 1 (by rfl) ⟨4096736, by rfl⟩ : syracuseStep 5462315 = 8193473) B8193473
theorem B9345455 : Blo 1617007 9345455 := bstep (se 1 (by rfl) ⟨7009091, by rfl⟩ : syracuseStep 9345455 = 14018183) B14018183
theorem B17504687 : Blo 1617007 17504687 := bstep (se 1 (by rfl) ⟨13128515, by rfl⟩ : syracuseStep 17504687 = 26257031) B26257031
theorem B5462585 : Blo 1617007 5462585 := bstep (se 2 (by rfl) ⟨2048469, by rfl⟩ : syracuseStep 5462585 = 4096939) B4096939
theorem B2767547 : Blo 1617007 2767547 := bstep (se 1 (by rfl) ⟨2075660, by rfl⟩ : syracuseStep 2767547 = 4151321) B4151321
theorem B4094945 : Blo 1617007 4094945 := bstep (se 2 (by rfl) ⟨1535604, by rfl⟩ : syracuseStep 4094945 = 3071209) B3071209
theorem B2186281 : Blo 1617007 2186281 := bstep (se 2 (by rfl) ⟨819855, by rfl⟩ : syracuseStep 2186281 = 1639711) B1639711
theorem B79806167 : Blo 1617007 79806167 := bstep (se 1 (by rfl) ⟨59854625, by rfl⟩ : syracuseStep 79806167 = 119709251) B119709251
theorem B74751781 : Blo 1617007 74751781 := bstep (se 4 (by rfl) ⟨7007979, by rfl⟩ : syracuseStep 74751781 = 14015959) B14015959
theorem B3071915 : Blo 1617007 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B27656801 : Blo 1617007 27656801 := bstep (se 2 (by rfl) ⟨10371300, by rfl⟩ : syracuseStep 27656801 = 20742601) B20742601
theorem B8192825 : Blo 1617007 8192825 := bstep (se 2 (by rfl) ⟨3072309, by rfl⟩ : syracuseStep 8192825 = 6144619) B6144619
theorem B6144923 : Blo 1617007 6144923 := bstep (se 1 (by rfl) ⟨4608692, by rfl⟩ : syracuseStep 6144923 = 9217385) B9217385
theorem B2425799 : Blo 1617007 2425799 := bstep (se 1 (by rfl) ⟨1819349, by rfl⟩ : syracuseStep 2425799 = 3638699) B3638699
theorem B3638267 : Blo 1617007 3638267 := bstep (se 1 (by rfl) ⟨2728700, by rfl⟩ : syracuseStep 3638267 = 5457401) B5457401
theorem B2425967 : Blo 1617007 2425967 := bstep (se 1 (by rfl) ⟨1819475, by rfl⟩ : syracuseStep 2425967 = 3638951) B3638951
theorem B1819759 : Blo 1617007 1819759 := bstep (se 1 (by rfl) ⟨1364819, by rfl⟩ : syracuseStep 1819759 = 2729639) B2729639
theorem B3638447 : Blo 1617007 3638447 := bstep (se 1 (by rfl) ⟨2728835, by rfl⟩ : syracuseStep 3638447 = 5457671) B5457671
theorem B3638483 : Blo 1617007 3638483 := bstep (se 1 (by rfl) ⟨2728862, by rfl⟩ : syracuseStep 3638483 = 5457725) B5457725
theorem B5686507 : Blo 1617007 5686507 := bstep (se 1 (by rfl) ⟨4264880, by rfl⟩ : syracuseStep 5686507 = 8529761) B8529761
theorem B2426159 : Blo 1617007 2426159 := bstep (se 1 (by rfl) ⟨1819619, by rfl⟩ : syracuseStep 2426159 = 3639239) B3639239
theorem B6907265 : Blo 1617007 6907265 := bstep (se 2 (by rfl) ⟨2590224, by rfl⟩ : syracuseStep 6907265 = 5180449) B5180449
theorem B3638753 : Blo 1617007 3638753 := bstep (se 2 (by rfl) ⟨1364532, by rfl⟩ : syracuseStep 3638753 = 2729065) B2729065
theorem B2426363 : Blo 1617007 2426363 := bstep (se 1 (by rfl) ⟨1819772, by rfl⟩ : syracuseStep 2426363 = 3639545) B3639545
theorem B2303515 : Blo 1617007 2303515 := bstep (se 1 (by rfl) ⟨1727636, by rfl⟩ : syracuseStep 2303515 = 3455273) B3455273
theorem B2426399 : Blo 1617007 2426399 := bstep (se 1 (by rfl) ⟨1819799, by rfl⟩ : syracuseStep 2426399 = 3639599) B3639599
theorem B1820191 : Blo 1617007 1820191 := bstep (se 1 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 1820191 = 2730287) B2730287
theorem B4097567 : Blo 1617007 4097567 := bstep (se 1 (by rfl) ⟨3073175, by rfl⟩ : syracuseStep 4097567 = 6146351) B6146351
theorem B2426543 : Blo 1617007 2426543 := bstep (se 1 (by rfl) ⟨1819907, by rfl⟩ : syracuseStep 2426543 = 3639815) B3639815
theorem B9209639 : Blo 1617007 9209639 := bstep (se 1 (by rfl) ⟨6907229, by rfl⟩ : syracuseStep 9209639 = 13814459) B13814459
theorem B2426663 : Blo 1617007 2426663 := bstep (se 1 (by rfl) ⟨1819997, by rfl⟩ : syracuseStep 2426663 = 3639995) B3639995
theorem B1845031 : Blo 1617007 1845031 := bstep (se 1 (by rfl) ⟨1383773, by rfl⟩ : syracuseStep 1845031 = 2767547) B2767547
theorem B12289967 : Blo 1617007 12289967 := bstep (se 1 (by rfl) ⟨9217475, by rfl⟩ : syracuseStep 12289967 = 18434951) B18434951
theorem B2729963 : Blo 1617007 2729963 := bstep (se 1 (by rfl) ⟨2047472, by rfl⟩ : syracuseStep 2729963 = 4094945) B4094945
theorem B139946129 : Blo 1617007 139946129 := bstep (se 2 (by rfl) ⟨52479798, by rfl⟩ : syracuseStep 139946129 = 104959597) B104959597
theorem B2427215 : Blo 1617007 2427215 := bstep (se 1 (by rfl) ⟨1820411, by rfl⟩ : syracuseStep 2427215 = 3640823) B3640823
theorem B2427263 : Blo 1617007 2427263 := bstep (se 1 (by rfl) ⟨1820447, by rfl⟩ : syracuseStep 2427263 = 3640895) B3640895
theorem B1821055 : Blo 1617007 1821055 := bstep (se 1 (by rfl) ⟨1365791, by rfl⟩ : syracuseStep 1821055 = 2731583) B2731583
theorem B2427305 : Blo 1617007 2427305 := bstep (se 2 (by rfl) ⟨910239, by rfl⟩ : syracuseStep 2427305 = 1820479) B1820479
theorem B5458535 : Blo 1617007 5458535 := bstep (se 1 (by rfl) ⟨4093901, by rfl⟩ : syracuseStep 5458535 = 8187803) B8187803
theorem B3640103 : Blo 1617007 3640103 := bstep (se 1 (by rfl) ⟨2730077, by rfl⟩ : syracuseStep 3640103 = 5460155) B5460155
theorem B2427689 : Blo 1617007 2427689 := bstep (se 2 (by rfl) ⟨910383, by rfl⟩ : syracuseStep 2427689 = 1820767) B1820767
theorem B6147035 : Blo 1617007 6147035 := bstep (se 1 (by rfl) ⟨4610276, by rfl⟩ : syracuseStep 6147035 = 9220553) B9220553
theorem B3886049 : Blo 1617007 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B5458913 : Blo 1617007 5458913 := bstep (se 2 (by rfl) ⟨2047092, by rfl⟩ : syracuseStep 5458913 = 4094185) B4094185
theorem B2427899 : Blo 1617007 2427899 := bstep (se 1 (by rfl) ⟨1820924, by rfl⟩ : syracuseStep 2427899 = 3641849) B3641849
theorem B2427959 : Blo 1617007 2427959 := bstep (se 1 (by rfl) ⟨1820969, by rfl⟩ : syracuseStep 2427959 = 3641939) B3641939
theorem B3640427 : Blo 1617007 3640427 := bstep (se 1 (by rfl) ⟨2730320, by rfl⟩ : syracuseStep 3640427 = 5460641) B5460641
theorem B2428079 : Blo 1617007 2428079 := bstep (se 1 (by rfl) ⟨1821059, by rfl⟩ : syracuseStep 2428079 = 3642119) B3642119
theorem B27634931 : Blo 1617007 27634931 := bstep (se 1 (by rfl) ⟨20726198, by rfl⟩ : syracuseStep 27634931 = 41452397) B41452397
theorem B3640697 : Blo 1617007 3640697 := bstep (se 2 (by rfl) ⟨1365261, by rfl⟩ : syracuseStep 3640697 = 2730523) B2730523
theorem B1617279 : Blo 1617007 1617279 := bstep (se 1 (by rfl) ⟨1212959, by rfl⟩ : syracuseStep 1617279 = 2425919) B2425919
theorem B1617307 : Blo 1617007 1617307 := bstep (se 1 (by rfl) ⟨1212980, by rfl⟩ : syracuseStep 1617307 = 2425961) B2425961
theorem B11218331 : Blo 1617007 11218331 := bstep (se 1 (by rfl) ⟨8413748, by rfl⟩ : syracuseStep 11218331 = 16827497) B16827497
theorem B7777691 : Blo 1617007 7777691 := bstep (se 1 (by rfl) ⟨5833268, by rfl⟩ : syracuseStep 7777691 = 11666537) B11666537
theorem B17485271 : Blo 1617007 17485271 := bstep (se 1 (by rfl) ⟨13113953, by rfl⟩ : syracuseStep 17485271 = 26227907) B26227907
theorem B1617375 : Blo 1617007 1617375 := bstep (se 1 (by rfl) ⟨1213031, by rfl⟩ : syracuseStep 1617375 = 2426063) B2426063
theorem B1617511 : Blo 1617007 1617511 := bstep (se 1 (by rfl) ⟨1213133, by rfl⟩ : syracuseStep 1617511 = 2426267) B2426267
theorem B9211553 : Blo 1617007 9211553 := bstep (se 2 (by rfl) ⟨3454332, by rfl⟩ : syracuseStep 9211553 = 6908665) B6908665
theorem B3641003 : Blo 1617007 3641003 := bstep (se 1 (by rfl) ⟨2730752, by rfl⟩ : syracuseStep 3641003 = 5461505) B5461505
theorem B5828321 : Blo 1617007 5828321 := bstep (se 2 (by rfl) ⟨2185620, by rfl⟩ : syracuseStep 5828321 = 4371241) B4371241
theorem B1617659 : Blo 1617007 1617659 := bstep (se 1 (by rfl) ⟨1213244, by rfl⟩ : syracuseStep 1617659 = 2426489) B2426489
theorem B1617727 : Blo 1617007 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B1617791 : Blo 1617007 1617791 := bstep (se 1 (by rfl) ⟨1213343, by rfl⟩ : syracuseStep 1617791 = 2426687) B2426687
theorem B12480475 : Blo 1617007 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B14757869 : Blo 1617007 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B1617903 : Blo 1617007 1617903 := bstep (se 1 (by rfl) ⟨1213427, by rfl⟩ : syracuseStep 1617903 = 2426855) B2426855
theorem B3641327 : Blo 1617007 3641327 := bstep (se 1 (by rfl) ⟨2730995, by rfl⟩ : syracuseStep 3641327 = 5461991) B5461991
theorem B1617915 : Blo 1617007 1617915 := bstep (se 1 (by rfl) ⟨1213436, by rfl⟩ : syracuseStep 1617915 = 2426873) B2426873
theorem B3690535 : Blo 1617007 3690535 := bstep (se 1 (by rfl) ⟨2767901, by rfl⟩ : syracuseStep 3690535 = 5535803) B5535803
theorem B3641399 : Blo 1617007 3641399 := bstep (se 1 (by rfl) ⟨2731049, by rfl⟩ : syracuseStep 3641399 = 5462099) B5462099
theorem B1617983 : Blo 1617007 1617983 := bstep (se 1 (by rfl) ⟨1213487, by rfl⟩ : syracuseStep 1617983 = 2426975) B2426975
theorem B1618023 : Blo 1617007 1618023 := bstep (se 1 (by rfl) ⟨1213517, by rfl⟩ : syracuseStep 1618023 = 2427035) B2427035
theorem B1618047 : Blo 1617007 1618047 := bstep (se 1 (by rfl) ⟨1213535, by rfl⟩ : syracuseStep 1618047 = 2427071) B2427071
theorem B1618075 : Blo 1617007 1618075 := bstep (se 1 (by rfl) ⟨1213556, by rfl⟩ : syracuseStep 1618075 = 2427113) B2427113
theorem B3641543 : Blo 1617007 3641543 := bstep (se 1 (by rfl) ⟨2731157, by rfl⟩ : syracuseStep 3641543 = 5462315) B5462315
theorem B6230303 : Blo 1617007 6230303 := bstep (se 1 (by rfl) ⟨4672727, by rfl⟩ : syracuseStep 6230303 = 9345455) B9345455
theorem B11669791 : Blo 1617007 11669791 := bstep (se 1 (by rfl) ⟨8752343, by rfl⟩ : syracuseStep 11669791 = 17504687) B17504687
theorem B1618279 : Blo 1617007 1618279 := bstep (se 1 (by rfl) ⟨1213709, by rfl⟩ : syracuseStep 1618279 = 2427419) B2427419
theorem B3641723 : Blo 1617007 3641723 := bstep (se 1 (by rfl) ⟨2731292, by rfl⟩ : syracuseStep 3641723 = 5462585) B5462585
theorem B1618331 : Blo 1617007 1618331 := bstep (se 1 (by rfl) ⟨1213748, by rfl⟩ : syracuseStep 1618331 = 2427497) B2427497
theorem B7770617 : Blo 1617007 7770617 := bstep (se 2 (by rfl) ⟨2913981, by rfl⟩ : syracuseStep 7770617 = 5827963) B5827963
theorem B6140519 : Blo 1617007 6140519 := bstep (se 1 (by rfl) ⟨4605389, by rfl⟩ : syracuseStep 6140519 = 9210779) B9210779
theorem B3641993 : Blo 1617007 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B1618683 : Blo 1617007 1618683 := bstep (se 1 (by rfl) ⟨1214012, by rfl⟩ : syracuseStep 1618683 = 2428025) B2428025
theorem B1618751 : Blo 1617007 1618751 := bstep (se 1 (by rfl) ⟨1214063, by rfl⟩ : syracuseStep 1618751 = 2428127) B2428127
theorem B1618779 : Blo 1617007 1618779 := bstep (se 1 (by rfl) ⟨1214084, by rfl⟩ : syracuseStep 1618779 = 2428169) B2428169
theorem B1618847 : Blo 1617007 1618847 := bstep (se 1 (by rfl) ⟨1214135, by rfl⟩ : syracuseStep 1618847 = 2428271) B2428271
theorem B1618927 : Blo 1617007 1618927 := bstep (se 1 (by rfl) ⟨1214195, by rfl⟩ : syracuseStep 1618927 = 2428391) B2428391
theorem B6558745 : Blo 1617007 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B99669041 : Blo 1617007 99669041 := bstep (se 2 (by rfl) ⟨37375890, by rfl⟩ : syracuseStep 99669041 = 74751781) B74751781
theorem B53204111 : Blo 1617007 53204111 := bstep (se 1 (by rfl) ⟨39903083, by rfl⟩ : syracuseStep 53204111 = 79806167) B79806167
theorem B11064683 : Blo 1617007 11064683 := bstep (se 1 (by rfl) ⟨8298512, by rfl⟩ : syracuseStep 11064683 = 16597025) B16597025
theorem B3642731 : Blo 1617007 3642731 := bstep (se 1 (by rfl) ⟨2732048, by rfl⟩ : syracuseStep 3642731 = 5464097) B5464097
theorem B6911399 : Blo 1617007 6911399 := bstep (se 1 (by rfl) ⟨5183549, by rfl⟩ : syracuseStep 6911399 = 10367099) B10367099
theorem B4093355 : Blo 1617007 4093355 := bstep (se 1 (by rfl) ⟨3070016, by rfl⟩ : syracuseStep 4093355 = 6140033) B6140033
theorem B10368485 : Blo 1617007 10368485 := bstep (se 4 (by rfl) ⟨972045, by rfl⟩ : syracuseStep 10368485 = 1944091) B1944091
theorem B4609673 : Blo 1617007 4609673 := bstep (se 2 (by rfl) ⟨1728627, by rfl⟩ : syracuseStep 4609673 = 3457255) B3457255
theorem B12285593 : Blo 1617007 12285593 := bstep (se 2 (by rfl) ⟨4607097, by rfl⟩ : syracuseStep 12285593 = 9214195) B9214195
theorem B10360639 : Blo 1617007 10360639 := bstep (se 1 (by rfl) ⟨7770479, by rfl⟩ : syracuseStep 10360639 = 15540959) B15540959
theorem B2766889 : Blo 1617007 2766889 := bstep (se 2 (by rfl) ⟨1037583, by rfl⟩ : syracuseStep 2766889 = 2075167) B2075167
theorem B4921469 : Blo 1617007 4921469 := bstep (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) B1845551
theorem B4094135 : Blo 1617007 4094135 := bstep (se 1 (by rfl) ⟨3070601, by rfl⟩ : syracuseStep 4094135 = 6141203) B6141203
theorem B23328971 : Blo 1617007 23328971 := bstep (se 1 (by rfl) ⟨17496728, by rfl⟩ : syracuseStep 23328971 = 34993457) B34993457
theorem B5462369 : Blo 1617007 5462369 := bstep (se 2 (by rfl) ⟨2048388, by rfl⟩ : syracuseStep 5462369 = 4096777) B4096777
theorem B3938719 : Blo 1617007 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B86407631 : Blo 1617007 86407631 := bstep (se 1 (by rfl) ⟨64805723, by rfl⟩ : syracuseStep 86407631 = 129611447) B129611447
theorem B23313055 : Blo 1617007 23313055 := bstep (se 1 (by rfl) ⟨17484791, by rfl⟩ : syracuseStep 23313055 = 34969583) B34969583
theorem B2915041 : Blo 1617007 2915041 := bstep (se 2 (by rfl) ⟨1093140, by rfl⟩ : syracuseStep 2915041 = 2186281) B2186281
theorem B1727303 : Blo 1617007 1727303 := bstep (se 1 (by rfl) ⟨1295477, by rfl⟩ : syracuseStep 1727303 = 2590955) B2590955
theorem B5462855 : Blo 1617007 5462855 := bstep (se 1 (by rfl) ⟨4097141, by rfl⟩ : syracuseStep 5462855 = 8194283) B8194283
theorem B3742699 : Blo 1617007 3742699 := bstep (se 1 (by rfl) ⟨2807024, by rfl⟩ : syracuseStep 3742699 = 5614049) B5614049
theorem B53926903 : Blo 1617007 53926903 := bstep (se 1 (by rfl) ⟨40445177, by rfl⟩ : syracuseStep 53926903 = 80890355) B80890355
theorem B40443005 : Blo 1617007 40443005 := bstep (se 3 (by rfl) ⟨7583063, by rfl⟩ : syracuseStep 40443005 = 15166127) B15166127
theorem B42048719 : Blo 1617007 42048719 := bstep (se 1 (by rfl) ⟨31536539, by rfl⟩ : syracuseStep 42048719 = 63073079) B63073079
theorem B7773479 : Blo 1617007 7773479 := bstep (se 1 (by rfl) ⟨5830109, by rfl⟩ : syracuseStep 7773479 = 11660219) B11660219
theorem B12459493 : Blo 1617007 12459493 := bstep (se 4 (by rfl) ⟨1168077, by rfl⟩ : syracuseStep 12459493 = 2336155) B2336155
theorem B27639305 : Blo 1617007 27639305 := bstep (se 2 (by rfl) ⟨10364739, by rfl⟩ : syracuseStep 27639305 = 20729479) B20729479
theorem B22142555 : Blo 1617007 22142555 := bstep (se 1 (by rfl) ⟨16606916, by rfl⟩ : syracuseStep 22142555 = 33213833) B33213833
theorem B5463719 : Blo 1617007 5463719 := bstep (se 1 (by rfl) ⟨4097789, by rfl⟩ : syracuseStep 5463719 = 8195579) B8195579
theorem B5463827 : Blo 1617007 5463827 := bstep (se 1 (by rfl) ⟨4097870, by rfl⟩ : syracuseStep 5463827 = 8195741) B8195741
theorem B2047943 : Blo 1617007 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B4153535 : Blo 1617007 4153535 := bstep (se 1 (by rfl) ⟨3115151, by rfl⟩ : syracuseStep 4153535 = 6230303) B6230303
theorem B5251625 : Blo 1617007 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B4096615 : Blo 1617007 4096615 := bstep (se 1 (by rfl) ⟨3072461, by rfl⟩ : syracuseStep 4096615 = 6144923) B6144923
theorem B2425511 : Blo 1617007 2425511 := bstep (se 1 (by rfl) ⟨1819133, by rfl⟩ : syracuseStep 2425511 = 3638267) B3638267
theorem B66446027 : Blo 1617007 66446027 := bstep (se 1 (by rfl) ⟨49834520, by rfl⟩ : syracuseStep 66446027 = 99669041) B99669041
theorem B2425631 : Blo 1617007 2425631 := bstep (se 1 (by rfl) ⟨1819223, by rfl⟩ : syracuseStep 2425631 = 3638447) B3638447
theorem B2425655 : Blo 1617007 2425655 := bstep (se 1 (by rfl) ⟨1819241, by rfl⟩ : syracuseStep 2425655 = 3638483) B3638483
theorem B4604843 : Blo 1617007 4604843 := bstep (se 1 (by rfl) ⟨3453632, by rfl⟩ : syracuseStep 4604843 = 6907265) B6907265
theorem B2728903 : Blo 1617007 2728903 := bstep (se 1 (by rfl) ⟨2046677, by rfl⟩ : syracuseStep 2728903 = 4093355) B4093355
theorem B2425835 : Blo 1617007 2425835 := bstep (se 1 (by rfl) ⟨1819376, by rfl⟩ : syracuseStep 2425835 = 3638753) B3638753
theorem B3073115 : Blo 1617007 3073115 := bstep (se 1 (by rfl) ⟨2304836, by rfl⟩ : syracuseStep 3073115 = 4609673) B4609673
theorem B8193311 : Blo 1617007 8193311 := bstep (se 1 (by rfl) ⟨6144983, by rfl⟩ : syracuseStep 8193311 = 12289967) B12289967
theorem B4990265 : Blo 1617007 4990265 := bstep (se 2 (by rfl) ⟨1871349, by rfl⟩ : syracuseStep 4990265 = 3742699) B3742699
theorem B1819975 : Blo 1617007 1819975 := bstep (se 1 (by rfl) ⟨1364981, by rfl⟩ : syracuseStep 1819975 = 2729963) B2729963
theorem B2729423 : Blo 1617007 2729423 := bstep (se 1 (by rfl) ⟨2047067, by rfl⟩ : syracuseStep 2729423 = 4094135) B4094135
theorem B2426345 : Blo 1617007 2426345 := bstep (se 2 (by rfl) ⟨909879, by rfl⟩ : syracuseStep 2426345 = 1819759) B1819759
theorem B3639023 : Blo 1617007 3639023 := bstep (se 1 (by rfl) ⟨2729267, by rfl⟩ : syracuseStep 3639023 = 5458535) B5458535
theorem B2426735 : Blo 1617007 2426735 := bstep (se 1 (by rfl) ⟨1820051, by rfl⟩ : syracuseStep 2426735 = 3640103) B3640103
theorem B15542189 : Blo 1617007 15542189 := bstep (se 3 (by rfl) ⟨2914160, by rfl⟩ : syracuseStep 15542189 = 5828321) B5828321
theorem B4098023 : Blo 1617007 4098023 := bstep (se 1 (by rfl) ⟨3073517, by rfl⟩ : syracuseStep 4098023 = 6147035) B6147035
theorem B2590699 : Blo 1617007 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B3639275 : Blo 1617007 3639275 := bstep (se 1 (by rfl) ⟨2729456, by rfl⟩ : syracuseStep 3639275 = 5458913) B5458913
theorem B2426921 : Blo 1617007 2426921 := bstep (se 2 (by rfl) ⟨910095, by rfl⟩ : syracuseStep 2426921 = 1820191) B1820191
theorem B2426951 : Blo 1617007 2426951 := bstep (se 1 (by rfl) ⟨1820213, by rfl⟩ : syracuseStep 2426951 = 3640427) B3640427
theorem B26962003 : Blo 1617007 26962003 := bstep (se 1 (by rfl) ⟨20221502, by rfl⟩ : syracuseStep 26962003 = 40443005) B40443005
theorem B4606141 : Blo 1617007 4606141 := bstep (se 3 (by rfl) ⟨863651, by rfl⟩ : syracuseStep 4606141 = 1727303) B1727303
theorem B2427131 : Blo 1617007 2427131 := bstep (se 1 (by rfl) ⟨1820348, by rfl⟩ : syracuseStep 2427131 = 3640697) B3640697
theorem B18426203 : Blo 1617007 18426203 := bstep (se 1 (by rfl) ⟨13819652, by rfl⟩ : syracuseStep 18426203 = 27639305) B27639305
theorem B2460041 : Blo 1617007 2460041 := bstep (se 2 (by rfl) ⟨922515, by rfl⟩ : syracuseStep 2460041 = 1845031) B1845031
theorem B13814185 : Blo 1617007 13814185 := bstep (se 2 (by rfl) ⟨5180319, by rfl⟩ : syracuseStep 13814185 = 10360639) B10360639
theorem B2427335 : Blo 1617007 2427335 := bstep (se 1 (by rfl) ⟨1820501, by rfl⟩ : syracuseStep 2427335 = 3641003) B3641003
theorem B16640633 : Blo 1617007 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B2427551 : Blo 1617007 2427551 := bstep (se 1 (by rfl) ⟨1820663, by rfl⟩ : syracuseStep 2427551 = 3641327) B3641327
theorem B2427599 : Blo 1617007 2427599 := bstep (se 1 (by rfl) ⟨1820699, by rfl⟩ : syracuseStep 2427599 = 3641399) B3641399
theorem B3689185 : Blo 1617007 3689185 := bstep (se 2 (by rfl) ⟨1383444, by rfl⟩ : syracuseStep 3689185 = 2766889) B2766889
theorem B2427695 : Blo 1617007 2427695 := bstep (se 1 (by rfl) ⟨1820771, by rfl⟩ : syracuseStep 2427695 = 3641543) B3641543
theorem B2427815 : Blo 1617007 2427815 := bstep (se 1 (by rfl) ⟨1820861, by rfl⟩ : syracuseStep 2427815 = 3641723) B3641723
theorem B5180411 : Blo 1617007 5180411 := bstep (se 1 (by rfl) ⟨3885308, by rfl⟩ : syracuseStep 5180411 = 7770617) B7770617
theorem B15559721 : Blo 1617007 15559721 := bstep (se 2 (by rfl) ⟨5834895, by rfl⟩ : syracuseStep 15559721 = 11669791) B11669791
theorem B2427995 : Blo 1617007 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B2428073 : Blo 1617007 2428073 := bstep (se 2 (by rfl) ⟨910527, by rfl⟩ : syracuseStep 2428073 = 1821055) B1821055
theorem B1617199 : Blo 1617007 1617199 := bstep (se 1 (by rfl) ⟨1212899, by rfl⟩ : syracuseStep 1617199 = 2425799) B2425799
theorem B1617311 : Blo 1617007 1617311 := bstep (se 1 (by rfl) ⟨1212983, by rfl⟩ : syracuseStep 1617311 = 2425967) B2425967
theorem B1617439 : Blo 1617007 1617439 := bstep (se 1 (by rfl) ⟨1213079, by rfl⟩ : syracuseStep 1617439 = 2426159) B2426159
theorem B31084073 : Blo 1617007 31084073 := bstep (se 2 (by rfl) ⟨11656527, by rfl⟩ : syracuseStep 31084073 = 23313055) B23313055
theorem B7376455 : Blo 1617007 7376455 := bstep (se 1 (by rfl) ⟨5532341, by rfl⟩ : syracuseStep 7376455 = 11064683) B11064683
theorem B2428487 : Blo 1617007 2428487 := bstep (se 1 (by rfl) ⟨1821365, by rfl⟩ : syracuseStep 2428487 = 3642731) B3642731
theorem B4607599 : Blo 1617007 4607599 := bstep (se 1 (by rfl) ⟨3455699, by rfl⟩ : syracuseStep 4607599 = 6911399) B6911399
theorem B3886721 : Blo 1617007 3886721 := bstep (se 2 (by rfl) ⟨1457520, by rfl⟩ : syracuseStep 3886721 = 2915041) B2915041
theorem B1617575 : Blo 1617007 1617575 := bstep (se 1 (by rfl) ⟨1213181, by rfl⟩ : syracuseStep 1617575 = 2426363) B2426363
theorem B1617599 : Blo 1617007 1617599 := bstep (se 1 (by rfl) ⟨1213199, by rfl⟩ : syracuseStep 1617599 = 2426399) B2426399
theorem B2731711 : Blo 1617007 2731711 := bstep (se 1 (by rfl) ⟨2048783, by rfl⟩ : syracuseStep 2731711 = 4097567) B4097567
theorem B1617695 : Blo 1617007 1617695 := bstep (se 1 (by rfl) ⟨1213271, by rfl⟩ : syracuseStep 1617695 = 2426543) B2426543
theorem B6139759 : Blo 1617007 6139759 := bstep (se 1 (by rfl) ⟨4604819, by rfl⟩ : syracuseStep 6139759 = 9209639) B9209639
theorem B1617775 : Blo 1617007 1617775 := bstep (se 1 (by rfl) ⟨1213331, by rfl⟩ : syracuseStep 1617775 = 2426663) B2426663
theorem B8744993 : Blo 1617007 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B3280979 : Blo 1617007 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B15552647 : Blo 1617007 15552647 := bstep (se 1 (by rfl) ⟨11664485, by rfl⟩ : syracuseStep 15552647 = 23328971) B23328971
theorem B1618143 : Blo 1617007 1618143 := bstep (se 1 (by rfl) ⟨1213607, by rfl⟩ : syracuseStep 1618143 = 2427215) B2427215
theorem B3641579 : Blo 1617007 3641579 := bstep (se 1 (by rfl) ⟨2731184, by rfl⟩ : syracuseStep 3641579 = 5462369) B5462369
theorem B1618175 : Blo 1617007 1618175 := bstep (se 1 (by rfl) ⟨1213631, by rfl⟩ : syracuseStep 1618175 = 2427263) B2427263
theorem B1618203 : Blo 1617007 1618203 := bstep (se 1 (by rfl) ⟨1213652, by rfl⟩ : syracuseStep 1618203 = 2427305) B2427305
theorem B7582009 : Blo 1617007 7582009 := bstep (se 2 (by rfl) ⟨2843253, by rfl⟩ : syracuseStep 7582009 = 5686507) B5686507
theorem B1618459 : Blo 1617007 1618459 := bstep (se 1 (by rfl) ⟨1213844, by rfl⟩ : syracuseStep 1618459 = 2427689) B2427689
theorem B3641903 : Blo 1617007 3641903 := bstep (se 1 (by rfl) ⟨2731427, by rfl⟩ : syracuseStep 3641903 = 5462855) B5462855
theorem B1618599 : Blo 1617007 1618599 := bstep (se 1 (by rfl) ⟨1213949, by rfl⟩ : syracuseStep 1618599 = 2427899) B2427899
theorem B1618639 : Blo 1617007 1618639 := bstep (se 1 (by rfl) ⟨1213979, by rfl⟩ : syracuseStep 1618639 = 2427959) B2427959
theorem B1618719 : Blo 1617007 1618719 := bstep (se 1 (by rfl) ⟨1214039, by rfl⟩ : syracuseStep 1618719 = 2428079) B2428079
theorem B5182319 : Blo 1617007 5182319 := bstep (se 1 (by rfl) ⟨3886739, by rfl⟩ : syracuseStep 5182319 = 7773479) B7773479
theorem B6141035 : Blo 1617007 6141035 := bstep (se 1 (by rfl) ⟨4605776, by rfl⟩ : syracuseStep 6141035 = 9211553) B9211553
theorem B3642479 : Blo 1617007 3642479 := bstep (se 1 (by rfl) ⟨2731859, by rfl⟩ : syracuseStep 3642479 = 5463719) B5463719
theorem B3642551 : Blo 1617007 3642551 := bstep (se 1 (by rfl) ⟨2731913, by rfl⟩ : syracuseStep 3642551 = 5463827) B5463827
theorem B5461181 : Blo 1617007 5461181 := bstep (se 3 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 5461181 = 2047943) B2047943
theorem B287610149 : Blo 1617007 287610149 := bstep (se 4 (by rfl) ⟨26963451, by rfl⟩ : syracuseStep 287610149 = 53926903) B53926903
theorem B4920713 : Blo 1617007 4920713 := bstep (se 2 (by rfl) ⟨1845267, by rfl⟩ : syracuseStep 4920713 = 3690535) B3690535
theorem B18437867 : Blo 1617007 18437867 := bstep (se 1 (by rfl) ⟨13828400, by rfl⟩ : syracuseStep 18437867 = 27656801) B27656801
theorem B4093679 : Blo 1617007 4093679 := bstep (se 1 (by rfl) ⟨3070259, by rfl⟩ : syracuseStep 4093679 = 6140519) B6140519
theorem B5461883 : Blo 1617007 5461883 := bstep (se 1 (by rfl) ⟨4096412, by rfl⟩ : syracuseStep 5461883 = 8192825) B8192825
theorem B35469407 : Blo 1617007 35469407 := bstep (se 1 (by rfl) ⟨26602055, by rfl⟩ : syracuseStep 35469407 = 53204111) B53204111
theorem B6912323 : Blo 1617007 6912323 := bstep (se 1 (by rfl) ⟨5184242, by rfl⟩ : syracuseStep 6912323 = 10368485) B10368485
theorem B8190395 : Blo 1617007 8190395 := bstep (se 1 (by rfl) ⟨6142796, by rfl⟩ : syracuseStep 8190395 = 12285593) B12285593
theorem B93297419 : Blo 1617007 93297419 := bstep (se 1 (by rfl) ⟨69973064, by rfl⟩ : syracuseStep 93297419 = 139946129) B139946129
theorem B57605087 : Blo 1617007 57605087 := bstep (se 1 (by rfl) ⟨43203815, by rfl⟩ : syracuseStep 57605087 = 86407631) B86407631
theorem B16612657 : Blo 1617007 16612657 := bstep (se 2 (by rfl) ⟨6229746, by rfl⟩ : syracuseStep 16612657 = 12459493) B12459493
theorem B3071353 : Blo 1617007 3071353 := bstep (se 2 (by rfl) ⟨1151757, by rfl⟩ : syracuseStep 3071353 = 2303515) B2303515
theorem B28032479 : Blo 1617007 28032479 := bstep (se 1 (by rfl) ⟨21024359, by rfl⟩ : syracuseStep 28032479 = 42048719) B42048719
theorem B18423287 : Blo 1617007 18423287 := bstep (se 1 (by rfl) ⟨13817465, by rfl⟩ : syracuseStep 18423287 = 27634931) B27634931
theorem B7478887 : Blo 1617007 7478887 := bstep (se 1 (by rfl) ⟨5609165, by rfl⟩ : syracuseStep 7478887 = 11218331) B11218331
theorem B5185127 : Blo 1617007 5185127 := bstep (se 1 (by rfl) ⟨3888845, by rfl⟩ : syracuseStep 5185127 = 7777691) B7777691
theorem B11656847 : Blo 1617007 11656847 := bstep (se 1 (by rfl) ⟨8742635, by rfl⟩ : syracuseStep 11656847 = 17485271) B17485271
theorem B14761703 : Blo 1617007 14761703 := bstep (se 1 (by rfl) ⟨11071277, by rfl⟩ : syracuseStep 14761703 = 22142555) B22142555
theorem B9838579 : Blo 1617007 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B2187319 : Blo 1617007 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B2769023 : Blo 1617007 2769023 := bstep (se 1 (by rfl) ⟨2076767, by rfl⟩ : syracuseStep 2769023 = 4153535) B4153535
theorem B10109345 : Blo 1617007 10109345 := bstep (se 2 (by rfl) ⟨3791004, by rfl⟩ : syracuseStep 10109345 = 7582009) B7582009
theorem B2048743 : Blo 1617007 2048743 := bstep (se 1 (by rfl) ⟨1536557, by rfl⟩ : syracuseStep 2048743 = 3073115) B3073115
theorem B766960397 : Blo 1617007 766960397 := bstep (se 3 (by rfl) ⟨143805074, by rfl⟩ : syracuseStep 766960397 = 287610149) B287610149
theorem B3326843 : Blo 1617007 3326843 := bstep (se 1 (by rfl) ⟨2495132, by rfl⟩ : syracuseStep 3326843 = 4990265) B4990265
theorem B1819615 : Blo 1617007 1819615 := bstep (se 1 (by rfl) ⟨1364711, by rfl⟩ : syracuseStep 1819615 = 2729423) B2729423
theorem B2729119 : Blo 1617007 2729119 := bstep (se 1 (by rfl) ⟨2046839, by rfl⟩ : syracuseStep 2729119 = 4093679) B4093679
theorem B2426015 : Blo 1617007 2426015 := bstep (se 1 (by rfl) ⟨1819511, by rfl⟩ : syracuseStep 2426015 = 3639023) B3639023
theorem B3638537 : Blo 1617007 3638537 := bstep (se 2 (by rfl) ⟨1364451, by rfl⟩ : syracuseStep 3638537 = 2728903) B2728903
theorem B2426183 : Blo 1617007 2426183 := bstep (se 1 (by rfl) ⟨1819637, by rfl⟩ : syracuseStep 2426183 = 3639275) B3639275
theorem B1640027 : Blo 1617007 1640027 := bstep (se 1 (by rfl) ⟨1230020, by rfl⟩ : syracuseStep 1640027 = 2460041) B2460041
theorem B11093755 : Blo 1617007 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B2426633 : Blo 1617007 2426633 := bstep (se 2 (by rfl) ⟨909987, by rfl⟩ : syracuseStep 2426633 = 1819975) B1819975
theorem B10373147 : Blo 1617007 10373147 := bstep (se 1 (by rfl) ⟨7779860, by rfl⟩ : syracuseStep 10373147 = 15559721) B15559721
theorem B9971849 : Blo 1617007 9971849 := bstep (se 2 (by rfl) ⟨3739443, by rfl⟩ : syracuseStep 9971849 = 7478887) B7478887
theorem B18688319 : Blo 1617007 18688319 := bstep (se 1 (by rfl) ⟨14016239, by rfl⟩ : syracuseStep 18688319 = 28032479) B28032479
theorem B12282191 : Blo 1617007 12282191 := bstep (se 1 (by rfl) ⟨9211643, by rfl⟩ : syracuseStep 12282191 = 18423287) B18423287
theorem B2591147 : Blo 1617007 2591147 := bstep (se 1 (by rfl) ⟨1943360, by rfl⟩ : syracuseStep 2591147 = 3886721) B3886721
theorem B8186345 : Blo 1617007 8186345 := bstep (se 2 (by rfl) ⟨3069879, by rfl⟩ : syracuseStep 8186345 = 6139759) B6139759
theorem B9841135 : Blo 1617007 9841135 := bstep (se 1 (by rfl) ⟨7380851, by rfl⟩ : syracuseStep 9841135 = 14761703) B14761703
theorem B13118105 : Blo 1617007 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B2427719 : Blo 1617007 2427719 := bstep (se 1 (by rfl) ⟨1820789, by rfl⟩ : syracuseStep 2427719 = 3641579) B3641579
theorem B3501083 : Blo 1617007 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B2427935 : Blo 1617007 2427935 := bstep (se 1 (by rfl) ⟨1820951, by rfl⟩ : syracuseStep 2427935 = 3641903) B3641903
theorem B143797349 : Blo 1617007 143797349 := bstep (se 4 (by rfl) ⟨13481001, by rfl⟩ : syracuseStep 143797349 = 26962003) B26962003
theorem B1617007 : Blo 1617007 1617007 := bstep (se 1 (by rfl) ⟨1212755, by rfl⟩ : syracuseStep 1617007 = 2425511) B2425511
theorem B44297351 : Blo 1617007 44297351 := bstep (se 1 (by rfl) ⟨33223013, by rfl⟩ : syracuseStep 44297351 = 66446027) B66446027
theorem B1617087 : Blo 1617007 1617087 := bstep (se 1 (by rfl) ⟨1212815, by rfl⟩ : syracuseStep 1617087 = 2425631) B2425631
theorem B1617103 : Blo 1617007 1617103 := bstep (se 1 (by rfl) ⟨1212827, by rfl⟩ : syracuseStep 1617103 = 2425655) B2425655
theorem B18418913 : Blo 1617007 18418913 := bstep (se 2 (by rfl) ⟨6907092, by rfl⟩ : syracuseStep 18418913 = 13814185) B13814185
theorem B1617223 : Blo 1617007 1617223 := bstep (se 1 (by rfl) ⟨1212917, by rfl⟩ : syracuseStep 1617223 = 2425835) B2425835
theorem B2428319 : Blo 1617007 2428319 := bstep (se 1 (by rfl) ⟨1821239, by rfl⟩ : syracuseStep 2428319 = 3642479) B3642479
theorem B2428367 : Blo 1617007 2428367 := bstep (se 1 (by rfl) ⟨1821275, by rfl⟩ : syracuseStep 2428367 = 3642551) B3642551
theorem B3640787 : Blo 1617007 3640787 := bstep (se 1 (by rfl) ⟨2730590, by rfl⟩ : syracuseStep 3640787 = 5461181) B5461181
theorem B3280475 : Blo 1617007 3280475 := bstep (se 1 (by rfl) ⟨2460356, by rfl⟩ : syracuseStep 3280475 = 4920713) B4920713
theorem B4918913 : Blo 1617007 4918913 := bstep (se 2 (by rfl) ⟨1844592, by rfl⟩ : syracuseStep 4918913 = 3689185) B3689185
theorem B1617563 : Blo 1617007 1617563 := bstep (se 1 (by rfl) ⟨1213172, by rfl⟩ : syracuseStep 1617563 = 2426345) B2426345
theorem B12291911 : Blo 1617007 12291911 := bstep (se 1 (by rfl) ⟨9218933, by rfl⟩ : syracuseStep 12291911 = 18437867) B18437867
theorem B1617823 : Blo 1617007 1617823 := bstep (se 1 (by rfl) ⟨1213367, by rfl⟩ : syracuseStep 1617823 = 2426735) B2426735
theorem B3641255 : Blo 1617007 3641255 := bstep (se 1 (by rfl) ⟨2730941, by rfl⟩ : syracuseStep 3641255 = 5461883) B5461883
theorem B2732015 : Blo 1617007 2732015 := bstep (se 1 (by rfl) ⟨2049011, by rfl⟩ : syracuseStep 2732015 = 4098023) B4098023
theorem B1617947 : Blo 1617007 1617947 := bstep (se 1 (by rfl) ⟨1213460, by rfl⟩ : syracuseStep 1617947 = 2426921) B2426921
theorem B1617967 : Blo 1617007 1617967 := bstep (se 1 (by rfl) ⟨1213475, by rfl⟩ : syracuseStep 1617967 = 2426951) B2426951
theorem B23646271 : Blo 1617007 23646271 := bstep (se 1 (by rfl) ⟨17734703, by rfl⟩ : syracuseStep 23646271 = 35469407) B35469407
theorem B1618087 : Blo 1617007 1618087 := bstep (se 1 (by rfl) ⟨1213565, by rfl⟩ : syracuseStep 1618087 = 2427131) B2427131
theorem B4608215 : Blo 1617007 4608215 := bstep (se 1 (by rfl) ⟨3456161, by rfl⟩ : syracuseStep 4608215 = 6912323) B6912323
theorem B12284135 : Blo 1617007 12284135 := bstep (se 1 (by rfl) ⟨9213101, by rfl⟩ : syracuseStep 12284135 = 18426203) B18426203
theorem B88600837 : Blo 1617007 88600837 := bstep (se 4 (by rfl) ⟨8306328, by rfl⟩ : syracuseStep 88600837 = 16612657) B16612657
theorem B5460263 : Blo 1617007 5460263 := bstep (se 1 (by rfl) ⟨4095197, by rfl⟩ : syracuseStep 5460263 = 8190395) B8190395
theorem B1618223 : Blo 1617007 1618223 := bstep (se 1 (by rfl) ⟨1213667, by rfl⟩ : syracuseStep 1618223 = 2427335) B2427335
theorem B1618367 : Blo 1617007 1618367 := bstep (se 1 (by rfl) ⟨1213775, by rfl⟩ : syracuseStep 1618367 = 2427551) B2427551
theorem B1618399 : Blo 1617007 1618399 := bstep (se 1 (by rfl) ⟨1213799, by rfl⟩ : syracuseStep 1618399 = 2427599) B2427599
theorem B62198279 : Blo 1617007 62198279 := bstep (se 1 (by rfl) ⟨46648709, by rfl⟩ : syracuseStep 62198279 = 93297419) B93297419
theorem B1618463 : Blo 1617007 1618463 := bstep (se 1 (by rfl) ⟨1213847, by rfl⟩ : syracuseStep 1618463 = 2427695) B2427695
theorem B1618543 : Blo 1617007 1618543 := bstep (se 1 (by rfl) ⟨1213907, by rfl⟩ : syracuseStep 1618543 = 2427815) B2427815
theorem B3453607 : Blo 1617007 3453607 := bstep (se 1 (by rfl) ⟨2590205, by rfl⟩ : syracuseStep 3453607 = 5180411) B5180411
theorem B1618663 : Blo 1617007 1618663 := bstep (se 1 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 1618663 = 2427995) B2427995
theorem B9835273 : Blo 1617007 9835273 := bstep (se 2 (by rfl) ⟨3688227, by rfl⟩ : syracuseStep 9835273 = 7376455) B7376455
theorem B1618715 : Blo 1617007 1618715 := bstep (se 1 (by rfl) ⟨1214036, by rfl⟩ : syracuseStep 1618715 = 2428073) B2428073
theorem B3642281 : Blo 1617007 3642281 := bstep (se 2 (by rfl) ⟨1365855, by rfl⟩ : syracuseStep 3642281 = 2731711) B2731711
theorem B20722715 : Blo 1617007 20722715 := bstep (se 1 (by rfl) ⟨15542036, by rfl⟩ : syracuseStep 20722715 = 31084073) B31084073
theorem B1618991 : Blo 1617007 1618991 := bstep (se 1 (by rfl) ⟨1214243, by rfl⟩ : syracuseStep 1618991 = 2428487) B2428487
theorem B7771231 : Blo 1617007 7771231 := bstep (se 1 (by rfl) ⟨5828423, by rfl⟩ : syracuseStep 7771231 = 11656847) B11656847
theorem B3454265 : Blo 1617007 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B5829995 : Blo 1617007 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B10368431 : Blo 1617007 10368431 := bstep (se 1 (by rfl) ⟨7776323, by rfl⟩ : syracuseStep 10368431 = 15552647) B15552647
theorem B6141521 : Blo 1617007 6141521 := bstep (se 2 (by rfl) ⟨2303070, by rfl⟩ : syracuseStep 6141521 = 4606141) B4606141
theorem B3069895 : Blo 1617007 3069895 := bstep (se 1 (by rfl) ⟨2302421, by rfl⟩ : syracuseStep 3069895 = 4604843) B4604843
theorem B4094023 : Blo 1617007 4094023 := bstep (se 1 (by rfl) ⟨3070517, by rfl⟩ : syracuseStep 4094023 = 6141035) B6141035
theorem B5462153 : Blo 1617007 5462153 := bstep (se 2 (by rfl) ⟨2048307, by rfl⟩ : syracuseStep 5462153 = 4096615) B4096615
theorem B5462207 : Blo 1617007 5462207 := bstep (se 1 (by rfl) ⟨4096655, by rfl⟩ : syracuseStep 5462207 = 8193311) B8193311
theorem B10361459 : Blo 1617007 10361459 := bstep (se 1 (by rfl) ⟨7771094, by rfl⟩ : syracuseStep 10361459 = 15542189) B15542189
theorem B4095137 : Blo 1617007 4095137 := bstep (se 2 (by rfl) ⟨1535676, by rfl⟩ : syracuseStep 4095137 = 3071353) B3071353
theorem B38403391 : Blo 1617007 38403391 := bstep (se 1 (by rfl) ⟨28802543, by rfl⟩ : syracuseStep 38403391 = 57605087) B57605087
theorem B6143465 : Blo 1617007 6143465 := bstep (se 2 (by rfl) ⟨2303799, by rfl⟩ : syracuseStep 6143465 = 4607599) B4607599
theorem B13819517 : Blo 1617007 13819517 := bstep (se 3 (by rfl) ⟨2591159, by rfl⟩ : syracuseStep 13819517 = 5182319) B5182319
theorem B3456751 : Blo 1617007 3456751 := bstep (se 1 (by rfl) ⟨2592563, by rfl⟩ : syracuseStep 3456751 = 5185127) B5185127
theorem B2916425 : Blo 1617007 2916425 := bstep (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) B2187319
theorem B3072143 : Blo 1617007 3072143 := bstep (se 1 (by rfl) ⟨2304107, by rfl⟩ : syracuseStep 3072143 = 4608215) B4608215
theorem B26591597 : Blo 1617007 26591597 := bstep (se 3 (by rfl) ⟨4985924, by rfl⟩ : syracuseStep 26591597 = 9971849) B9971849
theorem B2425691 : Blo 1617007 2425691 := bstep (se 1 (by rfl) ⟨1819268, by rfl⟩ : syracuseStep 2425691 = 3638537) B3638537
theorem B2302843 : Blo 1617007 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B4604809 : Blo 1617007 4604809 := bstep (se 2 (by rfl) ⟨1726803, by rfl⟩ : syracuseStep 4604809 = 3453607) B3453607
theorem B2426153 : Blo 1617007 2426153 := bstep (se 2 (by rfl) ⟨909807, by rfl⟩ : syracuseStep 2426153 = 1819615) B1819615
theorem B6915431 : Blo 1617007 6915431 := bstep (se 1 (by rfl) ⟨5186573, by rfl⟩ : syracuseStep 6915431 = 10373147) B10373147
theorem B3638825 : Blo 1617007 3638825 := bstep (se 2 (by rfl) ⟨1364559, by rfl⟩ : syracuseStep 3638825 = 2729119) B2729119
theorem B5457563 : Blo 1617007 5457563 := bstep (se 1 (by rfl) ⟨4093172, by rfl⟩ : syracuseStep 5457563 = 8186345) B8186345
theorem B95864899 : Blo 1617007 95864899 := bstep (se 1 (by rfl) ⟨71898674, by rfl⟩ : syracuseStep 95864899 = 143797349) B143797349
theorem B2730091 : Blo 1617007 2730091 := bstep (se 1 (by rfl) ⟨2047568, by rfl⟩ : syracuseStep 2730091 = 4095137) B4095137
theorem B2427191 : Blo 1617007 2427191 := bstep (se 1 (by rfl) ⟨1820393, by rfl⟩ : syracuseStep 2427191 = 3640787) B3640787
theorem B3279275 : Blo 1617007 3279275 := bstep (se 1 (by rfl) ⟨2459456, by rfl⟩ : syracuseStep 3279275 = 4918913) B4918913
theorem B8194607 : Blo 1617007 8194607 := bstep (se 1 (by rfl) ⟨6145955, by rfl⟩ : syracuseStep 8194607 = 12291911) B12291911
theorem B2427503 : Blo 1617007 2427503 := bstep (se 1 (by rfl) ⟨1820627, by rfl⟩ : syracuseStep 2427503 = 3641255) B3641255
theorem B1821343 : Blo 1617007 1821343 := bstep (se 1 (by rfl) ⟨1366007, by rfl⟩ : syracuseStep 1821343 = 2732015) B2732015
theorem B5458697 : Blo 1617007 5458697 := bstep (se 2 (by rfl) ⟨2047011, by rfl⟩ : syracuseStep 5458697 = 4094023) B4094023
theorem B3640175 : Blo 1617007 3640175 := bstep (se 1 (by rfl) ⟨2730131, by rfl⟩ : syracuseStep 3640175 = 5460263) B5460263
theorem B7384061 : Blo 1617007 7384061 := bstep (se 3 (by rfl) ⟨1384511, by rfl⟩ : syracuseStep 7384061 = 2769023) B2769023
theorem B511306931 : Blo 1617007 511306931 := bstep (se 1 (by rfl) ⟨383480198, by rfl⟩ : syracuseStep 511306931 = 766960397) B766960397
theorem B2428187 : Blo 1617007 2428187 := bstep (se 1 (by rfl) ⟨1821140, by rfl⟩ : syracuseStep 2428187 = 3642281) B3642281
theorem B13815143 : Blo 1617007 13815143 := bstep (se 1 (by rfl) ⟨10361357, by rfl⟩ : syracuseStep 13815143 = 20722715) B20722715
theorem B1617343 : Blo 1617007 1617343 := bstep (se 1 (by rfl) ⟨1213007, by rfl⟩ : syracuseStep 1617343 = 2426015) B2426015
theorem B1617455 : Blo 1617007 1617455 := bstep (se 1 (by rfl) ⟨1213091, by rfl⟩ : syracuseStep 1617455 = 2426183) B2426183
theorem B2731657 : Blo 1617007 2731657 := bstep (se 2 (by rfl) ⟨1024371, by rfl⟩ : syracuseStep 2731657 = 2048743) B2048743
theorem B6909725 : Blo 1617007 6909725 := bstep (se 3 (by rfl) ⟨1295573, by rfl⟩ : syracuseStep 6909725 = 2591147) B2591147
theorem B1617755 : Blo 1617007 1617755 := bstep (se 1 (by rfl) ⟨1213316, by rfl⟩ : syracuseStep 1617755 = 2426633) B2426633
theorem B3641435 : Blo 1617007 3641435 := bstep (se 1 (by rfl) ⟨2731076, by rfl⟩ : syracuseStep 3641435 = 5462153) B5462153
theorem B3641471 : Blo 1617007 3641471 := bstep (se 1 (by rfl) ⟨2731103, by rfl⟩ : syracuseStep 3641471 = 5462207) B5462207
theorem B8188127 : Blo 1617007 8188127 := bstep (se 1 (by rfl) ⟨6141095, by rfl⟩ : syracuseStep 8188127 = 12282191) B12282191
theorem B51204521 : Blo 1617007 51204521 := bstep (se 2 (by rfl) ⟨19201695, by rfl⟩ : syracuseStep 51204521 = 38403391) B38403391
theorem B8745403 : Blo 1617007 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B1618479 : Blo 1617007 1618479 := bstep (se 1 (by rfl) ⟨1213859, by rfl⟩ : syracuseStep 1618479 = 2427719) B2427719
theorem B1618623 : Blo 1617007 1618623 := bstep (se 1 (by rfl) ⟨1213967, by rfl⟩ : syracuseStep 1618623 = 2427935) B2427935
theorem B1618879 : Blo 1617007 1618879 := bstep (se 1 (by rfl) ⟨1214159, by rfl⟩ : syracuseStep 1618879 = 2428319) B2428319
theorem B1618911 : Blo 1617007 1618911 := bstep (se 1 (by rfl) ⟨1214183, by rfl⟩ : syracuseStep 1618911 = 2428367) B2428367
theorem B4609001 : Blo 1617007 4609001 := bstep (se 2 (by rfl) ⟨1728375, by rfl⟩ : syracuseStep 4609001 = 3456751) B3456751
theorem B14791673 : Blo 1617007 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B9213011 : Blo 1617007 9213011 := bstep (se 1 (by rfl) ⟨6909758, by rfl⟩ : syracuseStep 9213011 = 13819517) B13819517
theorem B4093193 : Blo 1617007 4093193 := bstep (se 2 (by rfl) ⟨1534947, by rfl⟩ : syracuseStep 4093193 = 3069895) B3069895
theorem B9336221 : Blo 1617007 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B31528361 : Blo 1617007 31528361 := bstep (se 2 (by rfl) ⟨11823135, by rfl⟩ : syracuseStep 31528361 = 23646271) B23646271
theorem B8189423 : Blo 1617007 8189423 := bstep (se 1 (by rfl) ⟨6142067, by rfl⟩ : syracuseStep 8189423 = 12284135) B12284135
theorem B41465519 : Blo 1617007 41465519 := bstep (se 1 (by rfl) ⟨31099139, by rfl⟩ : syracuseStep 41465519 = 62198279) B62198279
theorem B118134449 : Blo 1617007 118134449 := bstep (se 2 (by rfl) ⟨44300418, by rfl⟩ : syracuseStep 118134449 = 88600837) B88600837
theorem B13121513 : Blo 1617007 13121513 := bstep (se 2 (by rfl) ⟨4920567, by rfl⟩ : syracuseStep 13121513 = 9841135) B9841135
theorem B15546653 : Blo 1617007 15546653 := bstep (se 3 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 15546653 = 5829995) B5829995
theorem B6912287 : Blo 1617007 6912287 := bstep (se 1 (by rfl) ⟨5184215, by rfl⟩ : syracuseStep 6912287 = 10368431) B10368431
theorem B13113697 : Blo 1617007 13113697 := bstep (se 2 (by rfl) ⟨4917636, by rfl⟩ : syracuseStep 13113697 = 9835273) B9835273
theorem B4094347 : Blo 1617007 4094347 := bstep (se 1 (by rfl) ⟨3070760, by rfl⟩ : syracuseStep 4094347 = 6141521) B6141521
theorem B26958253 : Blo 1617007 26958253 := bstep (se 3 (by rfl) ⟨5054672, by rfl⟩ : syracuseStep 26958253 = 10109345) B10109345
theorem B10361641 : Blo 1617007 10361641 := bstep (se 2 (by rfl) ⟨3885615, by rfl⟩ : syracuseStep 10361641 = 7771231) B7771231
theorem B12458879 : Blo 1617007 12458879 := bstep (se 1 (by rfl) ⟨9344159, by rfl⟩ : syracuseStep 12458879 = 18688319) B18688319
theorem B4373405 : Blo 1617007 4373405 := bstep (se 3 (by rfl) ⟨820013, by rfl⟩ : syracuseStep 4373405 = 1640027) B1640027
theorem B27630557 : Blo 1617007 27630557 := bstep (se 3 (by rfl) ⟨5180729, by rfl⟩ : syracuseStep 27630557 = 10361459) B10361459
theorem B29531567 : Blo 1617007 29531567 := bstep (se 1 (by rfl) ⟨22148675, by rfl⟩ : syracuseStep 29531567 = 44297351) B44297351
theorem B12279275 : Blo 1617007 12279275 := bstep (se 1 (by rfl) ⟨9209456, by rfl⟩ : syracuseStep 12279275 = 18418913) B18418913
theorem B4095643 : Blo 1617007 4095643 := bstep (se 1 (by rfl) ⟨3071732, by rfl⟩ : syracuseStep 4095643 = 6143465) B6143465
theorem B8871581 : Blo 1617007 8871581 := bstep (se 3 (by rfl) ⟨1663421, by rfl⟩ : syracuseStep 8871581 = 3326843) B3326843
theorem B2186983 : Blo 1617007 2186983 := bstep (se 1 (by rfl) ⟨1640237, by rfl⟩ : syracuseStep 2186983 = 3280475) B3280475
theorem B127819865 : Blo 1617007 127819865 := bstep (se 2 (by rfl) ⟨47932449, by rfl⟩ : syracuseStep 127819865 = 95864899) B95864899
theorem B2048095 : Blo 1617007 2048095 := bstep (se 1 (by rfl) ⟨1536071, by rfl⟩ : syracuseStep 2048095 = 3072143) B3072143
theorem B17727731 : Blo 1617007 17727731 := bstep (se 1 (by rfl) ⟨13295798, by rfl⟩ : syracuseStep 17727731 = 26591597) B26591597
theorem B3072667 : Blo 1617007 3072667 := bstep (se 1 (by rfl) ⟨2304500, by rfl⟩ : syracuseStep 3072667 = 4609001) B4609001
theorem B2728795 : Blo 1617007 2728795 := bstep (se 1 (by rfl) ⟨2046596, by rfl⟩ : syracuseStep 2728795 = 4093193) B4093193
theorem B2425883 : Blo 1617007 2425883 := bstep (se 1 (by rfl) ⟨1819412, by rfl⟩ : syracuseStep 2425883 = 3638825) B3638825
theorem B3638375 : Blo 1617007 3638375 := bstep (se 1 (by rfl) ⟨2728781, by rfl⟩ : syracuseStep 3638375 = 5457563) B5457563
theorem B136545389 : Blo 1617007 136545389 := bstep (se 3 (by rfl) ⟨25602260, by rfl⟩ : syracuseStep 136545389 = 51204521) B51204521
theorem B10364435 : Blo 1617007 10364435 := bstep (se 1 (by rfl) ⟨7773326, by rfl⟩ : syracuseStep 10364435 = 15546653) B15546653
theorem B3639131 : Blo 1617007 3639131 := bstep (se 1 (by rfl) ⟨2729348, by rfl⟩ : syracuseStep 3639131 = 5458697) B5458697
theorem B2426783 : Blo 1617007 2426783 := bstep (se 1 (by rfl) ⟨1820087, by rfl⟩ : syracuseStep 2426783 = 3640175) B3640175
theorem B340871287 : Blo 1617007 340871287 := bstep (se 1 (by rfl) ⟨255653465, by rfl⟩ : syracuseStep 340871287 = 511306931) B511306931
theorem B9210095 : Blo 1617007 9210095 := bstep (se 1 (by rfl) ⟨6907571, by rfl⟩ : syracuseStep 9210095 = 13815143) B13815143
theorem B19687711 : Blo 1617007 19687711 := bstep (se 1 (by rfl) ⟨14765783, by rfl⟩ : syracuseStep 19687711 = 29531567) B29531567
theorem B8186183 : Blo 1617007 8186183 := bstep (se 1 (by rfl) ⟨6139637, by rfl⟩ : syracuseStep 8186183 = 12279275) B12279275
theorem B4606483 : Blo 1617007 4606483 := bstep (se 1 (by rfl) ⟨3454862, by rfl⟩ : syracuseStep 4606483 = 6909725) B6909725
theorem B2427623 : Blo 1617007 2427623 := bstep (se 1 (by rfl) ⟨1820717, by rfl⟩ : syracuseStep 2427623 = 3641435) B3641435
theorem B2427647 : Blo 1617007 2427647 := bstep (se 1 (by rfl) ⟨1820735, by rfl⟩ : syracuseStep 2427647 = 3641471) B3641471
theorem B3640121 : Blo 1617007 3640121 := bstep (se 2 (by rfl) ⟨1365045, by rfl⟩ : syracuseStep 3640121 = 2730091) B2730091
theorem B5458751 : Blo 1617007 5458751 := bstep (se 1 (by rfl) ⟨4094063, by rfl⟩ : syracuseStep 5458751 = 8188127) B8188127
theorem B7777133 : Blo 1617007 7777133 := bstep (se 3 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 7777133 = 2916425) B2916425
theorem B17484929 : Blo 1617007 17484929 := bstep (se 2 (by rfl) ⟨6556848, by rfl⟩ : syracuseStep 17484929 = 13113697) B13113697
theorem B5459129 : Blo 1617007 5459129 := bstep (se 2 (by rfl) ⟨2047173, by rfl⟩ : syracuseStep 5459129 = 4094347) B4094347
theorem B1617127 : Blo 1617007 1617127 := bstep (se 1 (by rfl) ⟨1212845, by rfl⟩ : syracuseStep 1617127 = 2425691) B2425691
theorem B11660537 : Blo 1617007 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B1617435 : Blo 1617007 1617435 := bstep (se 1 (by rfl) ⟨1213076, by rfl⟩ : syracuseStep 1617435 = 2426153) B2426153
theorem B2428457 : Blo 1617007 2428457 := bstep (se 2 (by rfl) ⟨910671, by rfl⟩ : syracuseStep 2428457 = 1821343) B1821343
theorem B5459615 : Blo 1617007 5459615 := bstep (se 1 (by rfl) ⟨4094711, by rfl⟩ : syracuseStep 5459615 = 8189423) B8189423
theorem B13815521 : Blo 1617007 13815521 := bstep (se 2 (by rfl) ⟨5180820, by rfl⟩ : syracuseStep 13815521 = 10361641) B10361641
theorem B27643679 : Blo 1617007 27643679 := bstep (se 1 (by rfl) ⟨20732759, by rfl⟩ : syracuseStep 27643679 = 41465519) B41465519
theorem B6139745 : Blo 1617007 6139745 := bstep (se 2 (by rfl) ⟨2302404, by rfl⟩ : syracuseStep 6139745 = 4604809) B4604809
theorem B4608191 : Blo 1617007 4608191 := bstep (se 1 (by rfl) ⟨3456143, by rfl⟩ : syracuseStep 4608191 = 6912287) B6912287
theorem B1618127 : Blo 1617007 1618127 := bstep (se 1 (by rfl) ⟨1213595, by rfl⟩ : syracuseStep 1618127 = 2427191) B2427191
theorem B1618335 : Blo 1617007 1618335 := bstep (se 1 (by rfl) ⟨1213751, by rfl⟩ : syracuseStep 1618335 = 2427503) B2427503
theorem B18420371 : Blo 1617007 18420371 := bstep (se 1 (by rfl) ⟨13815278, by rfl⟩ : syracuseStep 18420371 = 27630557) B27630557
theorem B3642209 : Blo 1617007 3642209 := bstep (se 2 (by rfl) ⟨1365828, by rfl⟩ : syracuseStep 3642209 = 2731657) B2731657
theorem B1618791 : Blo 1617007 1618791 := bstep (se 1 (by rfl) ⟨1214093, by rfl⟩ : syracuseStep 1618791 = 2428187) B2428187
theorem B5460857 : Blo 1617007 5460857 := bstep (se 2 (by rfl) ⟨2047821, by rfl⟩ : syracuseStep 5460857 = 4095643) B4095643
theorem B35944337 : Blo 1617007 35944337 := bstep (se 2 (by rfl) ⟨13479126, by rfl⟩ : syracuseStep 35944337 = 26958253) B26958253
theorem B9861115 : Blo 1617007 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B6142007 : Blo 1617007 6142007 := bstep (se 1 (by rfl) ⟨4606505, by rfl⟩ : syracuseStep 6142007 = 9213011) B9213011
theorem B4610287 : Blo 1617007 4610287 := bstep (se 1 (by rfl) ⟨3457715, by rfl⟩ : syracuseStep 4610287 = 6915431) B6915431
theorem B6224147 : Blo 1617007 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B21018907 : Blo 1617007 21018907 := bstep (se 1 (by rfl) ⟨15764180, by rfl⟩ : syracuseStep 21018907 = 31528361) B31528361
theorem B78756299 : Blo 1617007 78756299 := bstep (se 1 (by rfl) ⟨59067224, by rfl⟩ : syracuseStep 78756299 = 118134449) B118134449
theorem B3070457 : Blo 1617007 3070457 := bstep (se 2 (by rfl) ⟨1151421, by rfl⟩ : syracuseStep 3070457 = 2302843) B2302843
theorem B11663909 : Blo 1617007 11663909 := bstep (se 4 (by rfl) ⟨1093491, by rfl⟩ : syracuseStep 11663909 = 2186983) B2186983
theorem B8747675 : Blo 1617007 8747675 := bstep (se 1 (by rfl) ⟨6560756, by rfl⟩ : syracuseStep 8747675 = 13121513) B13121513
theorem B2186183 : Blo 1617007 2186183 := bstep (se 1 (by rfl) ⟨1639637, by rfl⟩ : syracuseStep 2186183 = 3279275) B3279275
theorem B5463071 : Blo 1617007 5463071 := bstep (se 1 (by rfl) ⟨4097303, by rfl⟩ : syracuseStep 5463071 = 8194607) B8194607
theorem B8305919 : Blo 1617007 8305919 := bstep (se 1 (by rfl) ⟨6229439, by rfl⟩ : syracuseStep 8305919 = 12458879) B12458879
theorem B2915603 : Blo 1617007 2915603 := bstep (se 1 (by rfl) ⟨2186702, by rfl⟩ : syracuseStep 2915603 = 4373405) B4373405
theorem B4922707 : Blo 1617007 4922707 := bstep (se 1 (by rfl) ⟨3692030, by rfl⟩ : syracuseStep 4922707 = 7384061) B7384061
theorem B5914387 : Blo 1617007 5914387 := bstep (se 1 (by rfl) ⟨4435790, by rfl⟩ : syracuseStep 5914387 = 8871581) B8871581
theorem B85213243 : Blo 1617007 85213243 := bstep (se 1 (by rfl) ⟨63909932, by rfl⟩ : syracuseStep 85213243 = 127819865) B127819865
theorem B28025209 : Blo 1617007 28025209 := bstep (se 2 (by rfl) ⟨10509453, by rfl⟩ : syracuseStep 28025209 = 21018907) B21018907
theorem B12280247 : Blo 1617007 12280247 := bstep (se 1 (by rfl) ⟨9210185, by rfl⟩ : syracuseStep 12280247 = 18420371) B18420371
theorem B12288509 : Blo 1617007 12288509 := bstep (se 3 (by rfl) ⟨2304095, by rfl⟩ : syracuseStep 12288509 = 4608191) B4608191
theorem B2425583 : Blo 1617007 2425583 := bstep (se 1 (by rfl) ⟨1819187, by rfl⟩ : syracuseStep 2425583 = 3638375) B3638375
theorem B91030259 : Blo 1617007 91030259 := bstep (se 1 (by rfl) ⟨68272694, by rfl⟩ : syracuseStep 91030259 = 136545389) B136545389
theorem B4096889 : Blo 1617007 4096889 := bstep (se 2 (by rfl) ⟨1536333, by rfl⟩ : syracuseStep 4096889 = 3072667) B3072667
theorem B3638393 : Blo 1617007 3638393 := bstep (se 2 (by rfl) ⟨1364397, by rfl⟩ : syracuseStep 3638393 = 2728795) B2728795
theorem B2426087 : Blo 1617007 2426087 := bstep (se 1 (by rfl) ⟨1819565, by rfl⟩ : syracuseStep 2426087 = 3639131) B3639131
theorem B5457455 : Blo 1617007 5457455 := bstep (se 1 (by rfl) ⟨4093091, by rfl⟩ : syracuseStep 5457455 = 8186183) B8186183
theorem B52504199 : Blo 1617007 52504199 := bstep (se 1 (by rfl) ⟨39378149, by rfl⟩ : syracuseStep 52504199 = 78756299) B78756299
theorem B7775939 : Blo 1617007 7775939 := bstep (se 1 (by rfl) ⟨5831954, by rfl⟩ : syracuseStep 7775939 = 11663909) B11663909
theorem B6563609 : Blo 1617007 6563609 := bstep (se 2 (by rfl) ⟨2461353, by rfl⟩ : syracuseStep 6563609 = 4922707) B4922707
theorem B2426747 : Blo 1617007 2426747 := bstep (se 1 (by rfl) ⟨1820060, by rfl⟩ : syracuseStep 2426747 = 3640121) B3640121
theorem B3639167 : Blo 1617007 3639167 := bstep (se 1 (by rfl) ⟨2729375, by rfl⟩ : syracuseStep 3639167 = 5458751) B5458751
theorem B3639419 : Blo 1617007 3639419 := bstep (se 1 (by rfl) ⟨2729564, by rfl⟩ : syracuseStep 3639419 = 5459129) B5459129
theorem B1943735 : Blo 1617007 1943735 := bstep (se 1 (by rfl) ⟨1457801, by rfl⟩ : syracuseStep 1943735 = 2915603) B2915603
theorem B3639743 : Blo 1617007 3639743 := bstep (se 1 (by rfl) ⟨2729807, by rfl⟩ : syracuseStep 3639743 = 5459615) B5459615
theorem B9210347 : Blo 1617007 9210347 := bstep (se 1 (by rfl) ⟨6907760, by rfl⟩ : syracuseStep 9210347 = 13815521) B13815521
theorem B2730793 : Blo 1617007 2730793 := bstep (se 2 (by rfl) ⟨1024047, by rfl⟩ : syracuseStep 2730793 = 2048095) B2048095
theorem B454495049 : Blo 1617007 454495049 := bstep (se 2 (by rfl) ⟨170435643, by rfl⟩ : syracuseStep 454495049 = 340871287) B340871287
theorem B6147049 : Blo 1617007 6147049 := bstep (se 2 (by rfl) ⟨2305143, by rfl⟩ : syracuseStep 6147049 = 4610287) B4610287
theorem B26250281 : Blo 1617007 26250281 := bstep (se 2 (by rfl) ⟨9843855, by rfl⟩ : syracuseStep 26250281 = 19687711) B19687711
theorem B2428139 : Blo 1617007 2428139 := bstep (se 1 (by rfl) ⟨1821104, by rfl⟩ : syracuseStep 2428139 = 3642209) B3642209
theorem B3640571 : Blo 1617007 3640571 := bstep (se 1 (by rfl) ⟨2730428, by rfl⟩ : syracuseStep 3640571 = 5460857) B5460857
theorem B1617255 : Blo 1617007 1617255 := bstep (se 1 (by rfl) ⟨1212941, by rfl⟩ : syracuseStep 1617255 = 2425883) B2425883
theorem B6909623 : Blo 1617007 6909623 := bstep (se 1 (by rfl) ⟨5182217, by rfl⟩ : syracuseStep 6909623 = 10364435) B10364435
theorem B1617855 : Blo 1617007 1617855 := bstep (se 1 (by rfl) ⟨1213391, by rfl⟩ : syracuseStep 1617855 = 2426783) B2426783
theorem B6140063 : Blo 1617007 6140063 := bstep (se 1 (by rfl) ⟨4605047, by rfl⟩ : syracuseStep 6140063 = 9210095) B9210095
theorem B4149431 : Blo 1617007 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B1618415 : Blo 1617007 1618415 := bstep (se 1 (by rfl) ⟨1213811, by rfl⟩ : syracuseStep 1618415 = 2427623) B2427623
theorem B1618431 : Blo 1617007 1618431 := bstep (se 1 (by rfl) ⟨1213823, by rfl⟩ : syracuseStep 1618431 = 2427647) B2427647
theorem B3642047 : Blo 1617007 3642047 := bstep (se 1 (by rfl) ⟨2731535, by rfl⟩ : syracuseStep 3642047 = 5463071) B5463071
theorem B7885849 : Blo 1617007 7885849 := bstep (se 2 (by rfl) ⟨2957193, by rfl⟩ : syracuseStep 7885849 = 5914387) B5914387
theorem B1618971 : Blo 1617007 1618971 := bstep (se 1 (by rfl) ⟨1214228, by rfl⟩ : syracuseStep 1618971 = 2428457) B2428457
theorem B95851565 : Blo 1617007 95851565 := bstep (se 3 (by rfl) ⟨17972168, by rfl⟩ : syracuseStep 95851565 = 35944337) B35944337
theorem B5829821 : Blo 1617007 5829821 := bstep (se 3 (by rfl) ⟨1093091, by rfl⟩ : syracuseStep 5829821 = 2186183) B2186183
theorem B18429119 : Blo 1617007 18429119 := bstep (se 1 (by rfl) ⟨13821839, by rfl⟩ : syracuseStep 18429119 = 27643679) B27643679
theorem B4093163 : Blo 1617007 4093163 := bstep (se 1 (by rfl) ⟨3069872, by rfl⟩ : syracuseStep 4093163 = 6139745) B6139745
theorem B11818487 : Blo 1617007 11818487 := bstep (se 1 (by rfl) ⟨8863865, by rfl⟩ : syracuseStep 11818487 = 17727731) B17727731
theorem B31094765 : Blo 1617007 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B6141977 : Blo 1617007 6141977 := bstep (se 2 (by rfl) ⟨2303241, by rfl⟩ : syracuseStep 6141977 = 4606483) B4606483
theorem B4094671 : Blo 1617007 4094671 := bstep (se 1 (by rfl) ⟨3071003, by rfl⟩ : syracuseStep 4094671 = 6142007) B6142007
theorem B2046971 : Blo 1617007 2046971 := bstep (se 1 (by rfl) ⟨1535228, by rfl⟩ : syracuseStep 2046971 = 3070457) B3070457
theorem B5831783 : Blo 1617007 5831783 := bstep (se 1 (by rfl) ⟨4373837, by rfl⟩ : syracuseStep 5831783 = 8747675) B8747675
theorem B5184755 : Blo 1617007 5184755 := bstep (se 1 (by rfl) ⟨3888566, by rfl⟩ : syracuseStep 5184755 = 7777133) B7777133
theorem B11656619 : Blo 1617007 11656619 := bstep (se 1 (by rfl) ⟨8742464, by rfl⟩ : syracuseStep 11656619 = 17484929) B17484929
theorem B5537279 : Blo 1617007 5537279 := bstep (se 1 (by rfl) ⟨4152959, by rfl⟩ : syracuseStep 5537279 = 8305919) B8305919
theorem B13148153 : Blo 1617007 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B8192339 : Blo 1617007 8192339 := bstep (se 1 (by rfl) ⟨6144254, by rfl⟩ : syracuseStep 8192339 = 12288509) B12288509
theorem B60686839 : Blo 1617007 60686839 := bstep (se 1 (by rfl) ⟨45515129, by rfl⟩ : syracuseStep 60686839 = 91030259) B91030259
theorem B2425595 : Blo 1617007 2425595 := bstep (se 1 (by rfl) ⟨1819196, by rfl⟩ : syracuseStep 2425595 = 3638393) B3638393
theorem B2728775 : Blo 1617007 2728775 := bstep (se 1 (by rfl) ⟨2046581, by rfl⟩ : syracuseStep 2728775 = 4093163) B4093163
theorem B3638303 : Blo 1617007 3638303 := bstep (se 1 (by rfl) ⟨2728727, by rfl⟩ : syracuseStep 3638303 = 5457455) B5457455
theorem B4375739 : Blo 1617007 4375739 := bstep (se 1 (by rfl) ⟨3281804, by rfl⟩ : syracuseStep 4375739 = 6563609) B6563609
theorem B2426111 : Blo 1617007 2426111 := bstep (se 1 (by rfl) ⟨1819583, by rfl⟩ : syracuseStep 2426111 = 3639167) B3639167
theorem B2426279 : Blo 1617007 2426279 := bstep (se 1 (by rfl) ⟨1819709, by rfl⟩ : syracuseStep 2426279 = 3639419) B3639419
theorem B2426495 : Blo 1617007 2426495 := bstep (se 1 (by rfl) ⟨1819871, by rfl⟩ : syracuseStep 2426495 = 3639743) B3639743
theorem B20735837 : Blo 1617007 20735837 := bstep (se 3 (by rfl) ⟨3887969, by rfl⟩ : syracuseStep 20735837 = 7775939) B7775939
theorem B17500187 : Blo 1617007 17500187 := bstep (se 1 (by rfl) ⟨13125140, by rfl⟩ : syracuseStep 17500187 = 26250281) B26250281
theorem B2427047 : Blo 1617007 2427047 := bstep (se 1 (by rfl) ⟨1820285, by rfl⟩ : syracuseStep 2427047 = 3640571) B3640571
theorem B4606415 : Blo 1617007 4606415 := bstep (se 1 (by rfl) ⟨3454811, by rfl⟩ : syracuseStep 4606415 = 6909623) B6909623
theorem B5458589 : Blo 1617007 5458589 := bstep (se 3 (by rfl) ⟨1023485, by rfl⟩ : syracuseStep 5458589 = 2046971) B2046971
theorem B113617657 : Blo 1617007 113617657 := bstep (se 2 (by rfl) ⟨42606621, by rfl⟩ : syracuseStep 113617657 = 85213243) B85213243
theorem B8186831 : Blo 1617007 8186831 := bstep (se 1 (by rfl) ⟨6140123, by rfl⟩ : syracuseStep 8186831 = 12280247) B12280247
theorem B2428031 : Blo 1617007 2428031 := bstep (se 1 (by rfl) ⟨1821023, by rfl⟩ : syracuseStep 2428031 = 3642047) B3642047
theorem B1617055 : Blo 1617007 1617055 := bstep (se 1 (by rfl) ⟨1212791, by rfl⟩ : syracuseStep 1617055 = 2425583) B2425583
theorem B2731259 : Blo 1617007 2731259 := bstep (se 1 (by rfl) ⟨2048444, by rfl⟩ : syracuseStep 2731259 = 4096889) B4096889
theorem B63901043 : Blo 1617007 63901043 := bstep (se 1 (by rfl) ⟨47925782, by rfl⟩ : syracuseStep 63901043 = 95851565) B95851565
theorem B3886547 : Blo 1617007 3886547 := bstep (se 1 (by rfl) ⟨2914910, by rfl⟩ : syracuseStep 3886547 = 5829821) B5829821
theorem B1617391 : Blo 1617007 1617391 := bstep (se 1 (by rfl) ⟨1213043, by rfl⟩ : syracuseStep 1617391 = 2426087) B2426087
theorem B5459561 : Blo 1617007 5459561 := bstep (se 2 (by rfl) ⟨2047335, by rfl⟩ : syracuseStep 5459561 = 4094671) B4094671
theorem B3641057 : Blo 1617007 3641057 := bstep (se 2 (by rfl) ⟨1365396, by rfl⟩ : syracuseStep 3641057 = 2730793) B2730793
theorem B1617831 : Blo 1617007 1617831 := bstep (se 1 (by rfl) ⟨1213373, by rfl⟩ : syracuseStep 1617831 = 2426747) B2426747
theorem B8196065 : Blo 1617007 8196065 := bstep (se 2 (by rfl) ⟨3073524, by rfl⟩ : syracuseStep 8196065 = 6147049) B6147049
theorem B20729843 : Blo 1617007 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B14766077 : Blo 1617007 14766077 := bstep (se 3 (by rfl) ⟨2768639, by rfl⟩ : syracuseStep 14766077 = 5537279) B5537279
theorem B10514465 : Blo 1617007 10514465 := bstep (se 2 (by rfl) ⟨3942924, by rfl⟩ : syracuseStep 10514465 = 7885849) B7885849
theorem B6140231 : Blo 1617007 6140231 := bstep (se 1 (by rfl) ⟨4605173, by rfl⟩ : syracuseStep 6140231 = 9210347) B9210347
theorem B149467781 : Blo 1617007 149467781 := bstep (se 4 (by rfl) ⟨14012604, by rfl⟩ : syracuseStep 149467781 = 28025209) B28025209
theorem B3887855 : Blo 1617007 3887855 := bstep (se 1 (by rfl) ⟨2915891, by rfl⟩ : syracuseStep 3887855 = 5831783) B5831783
theorem B1618759 : Blo 1617007 1618759 := bstep (se 1 (by rfl) ⟨1214069, by rfl⟩ : syracuseStep 1618759 = 2428139) B2428139
theorem B7771079 : Blo 1617007 7771079 := bstep (se 1 (by rfl) ⟨5828309, by rfl⟩ : syracuseStep 7771079 = 11656619) B11656619
theorem B4093375 : Blo 1617007 4093375 := bstep (se 1 (by rfl) ⟨3070031, by rfl⟩ : syracuseStep 4093375 = 6140063) B6140063
theorem B2766287 : Blo 1617007 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B5183293 : Blo 1617007 5183293 := bstep (se 3 (by rfl) ⟨971867, by rfl⟩ : syracuseStep 5183293 = 1943735) B1943735
theorem B12286079 : Blo 1617007 12286079 := bstep (se 1 (by rfl) ⟨9214559, by rfl⟩ : syracuseStep 12286079 = 18429119) B18429119
theorem B7878991 : Blo 1617007 7878991 := bstep (se 1 (by rfl) ⟨5909243, by rfl⟩ : syracuseStep 7878991 = 11818487) B11818487
theorem B35002799 : Blo 1617007 35002799 := bstep (se 1 (by rfl) ⟨26252099, by rfl⟩ : syracuseStep 35002799 = 52504199) B52504199
theorem B4094651 : Blo 1617007 4094651 := bstep (se 1 (by rfl) ⟨3070988, by rfl⟩ : syracuseStep 4094651 = 6141977) B6141977
theorem B302996699 : Blo 1617007 302996699 := bstep (se 1 (by rfl) ⟨227247524, by rfl⟩ : syracuseStep 302996699 = 454495049) B454495049
theorem B3456503 : Blo 1617007 3456503 := bstep (se 1 (by rfl) ⟨2592377, by rfl⟩ : syracuseStep 3456503 = 5184755) B5184755
theorem B8765435 : Blo 1617007 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B1819183 : Blo 1617007 1819183 := bstep (se 1 (by rfl) ⟨1364387, by rfl⟩ : syracuseStep 1819183 = 2728775) B2728775
theorem B2425535 : Blo 1617007 2425535 := bstep (se 1 (by rfl) ⟨1819151, by rfl⟩ : syracuseStep 2425535 = 3638303) B3638303
theorem B1844191 : Blo 1617007 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B10364125 : Blo 1617007 10364125 := bstep (se 3 (by rfl) ⟨1943273, by rfl⟩ : syracuseStep 10364125 = 3886547) B3886547
theorem B11666791 : Blo 1617007 11666791 := bstep (se 1 (by rfl) ⟨8750093, by rfl⟩ : syracuseStep 11666791 = 17500187) B17500187
theorem B3639059 : Blo 1617007 3639059 := bstep (se 1 (by rfl) ⟨2729294, by rfl⟩ : syracuseStep 3639059 = 5458589) B5458589
theorem B2729767 : Blo 1617007 2729767 := bstep (se 1 (by rfl) ⟨2047325, by rfl⟩ : syracuseStep 2729767 = 4094651) B4094651
theorem B5457833 : Blo 1617007 5457833 := bstep (se 2 (by rfl) ⟨2046687, by rfl⟩ : syracuseStep 5457833 = 4093375) B4093375
theorem B5457887 : Blo 1617007 5457887 := bstep (se 1 (by rfl) ⟨4093415, by rfl⟩ : syracuseStep 5457887 = 8186831) B8186831
theorem B1820839 : Blo 1617007 1820839 := bstep (se 1 (by rfl) ⟨1365629, by rfl⟩ : syracuseStep 1820839 = 2731259) B2731259
theorem B42600695 : Blo 1617007 42600695 := bstep (se 1 (by rfl) ⟨31950521, by rfl⟩ : syracuseStep 42600695 = 63901043) B63901043
theorem B2304335 : Blo 1617007 2304335 := bstep (se 1 (by rfl) ⟨1728251, by rfl⟩ : syracuseStep 2304335 = 3456503) B3456503
theorem B3639707 : Blo 1617007 3639707 := bstep (se 1 (by rfl) ⟨2729780, by rfl⟩ : syracuseStep 3639707 = 5459561) B5459561
theorem B2427371 : Blo 1617007 2427371 := bstep (se 1 (by rfl) ⟨1820528, by rfl⟩ : syracuseStep 2427371 = 3641057) B3641057
theorem B5843623 : Blo 1617007 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B10505321 : Blo 1617007 10505321 := bstep (se 2 (by rfl) ⟨3939495, by rfl⟩ : syracuseStep 10505321 = 7878991) B7878991
theorem B11668637 : Blo 1617007 11668637 := bstep (se 3 (by rfl) ⟨2187869, by rfl⟩ : syracuseStep 11668637 = 4375739) B4375739
theorem B2591903 : Blo 1617007 2591903 := bstep (se 1 (by rfl) ⟨1943927, by rfl⟩ : syracuseStep 2591903 = 3887855) B3887855
theorem B1617063 : Blo 1617007 1617063 := bstep (se 1 (by rfl) ⟨1212797, by rfl⟩ : syracuseStep 1617063 = 2425595) B2425595
theorem B5180719 : Blo 1617007 5180719 := bstep (se 1 (by rfl) ⟨3885539, by rfl⟩ : syracuseStep 5180719 = 7771079) B7771079
theorem B1617407 : Blo 1617007 1617407 := bstep (se 1 (by rfl) ⟨1213055, by rfl⟩ : syracuseStep 1617407 = 2426111) B2426111
theorem B1617519 : Blo 1617007 1617519 := bstep (se 1 (by rfl) ⟨1213139, by rfl⟩ : syracuseStep 1617519 = 2426279) B2426279
theorem B1617663 : Blo 1617007 1617663 := bstep (se 1 (by rfl) ⟨1213247, by rfl⟩ : syracuseStep 1617663 = 2426495) B2426495
theorem B13823891 : Blo 1617007 13823891 := bstep (se 1 (by rfl) ⟨10367918, by rfl⟩ : syracuseStep 13823891 = 20735837) B20735837
theorem B1618031 : Blo 1617007 1618031 := bstep (se 1 (by rfl) ⟨1213523, by rfl⟩ : syracuseStep 1618031 = 2427047) B2427047
theorem B23335199 : Blo 1617007 23335199 := bstep (se 1 (by rfl) ⟨17501399, by rfl⟩ : syracuseStep 23335199 = 35002799) B35002799
theorem B1618687 : Blo 1617007 1618687 := bstep (se 1 (by rfl) ⟨1214015, by rfl⟩ : syracuseStep 1618687 = 2428031) B2428031
theorem B6911057 : Blo 1617007 6911057 := bstep (se 2 (by rfl) ⟨2591646, by rfl⟩ : syracuseStep 6911057 = 5183293) B5183293
theorem B323663141 : Blo 1617007 323663141 := bstep (se 4 (by rfl) ⟨30343419, by rfl⟩ : syracuseStep 323663141 = 60686839) B60686839
theorem B39376205 : Blo 1617007 39376205 := bstep (se 3 (by rfl) ⟨7383038, by rfl⟩ : syracuseStep 39376205 = 14766077) B14766077
theorem B7009643 : Blo 1617007 7009643 := bstep (se 1 (by rfl) ⟨5257232, by rfl⟩ : syracuseStep 7009643 = 10514465) B10514465
theorem B4093487 : Blo 1617007 4093487 := bstep (se 1 (by rfl) ⟨3070115, by rfl⟩ : syracuseStep 4093487 = 6140231) B6140231
theorem B5461559 : Blo 1617007 5461559 := bstep (se 1 (by rfl) ⟨4096169, by rfl⟩ : syracuseStep 5461559 = 8192339) B8192339
theorem B605960837 : Blo 1617007 605960837 := bstep (se 4 (by rfl) ⟨56808828, by rfl⟩ : syracuseStep 605960837 = 113617657) B113617657
theorem B8190719 : Blo 1617007 8190719 := bstep (se 1 (by rfl) ⟨6143039, by rfl⟩ : syracuseStep 8190719 = 12286079) B12286079
theorem B3070943 : Blo 1617007 3070943 := bstep (se 1 (by rfl) ⟨2303207, by rfl⟩ : syracuseStep 3070943 = 4606415) B4606415
theorem B398580749 : Blo 1617007 398580749 := bstep (se 3 (by rfl) ⟨74733890, by rfl⟩ : syracuseStep 398580749 = 149467781) B149467781
theorem B201997799 : Blo 1617007 201997799 := bstep (se 1 (by rfl) ⟨151498349, by rfl⟩ : syracuseStep 201997799 = 302996699) B302996699
theorem B5464043 : Blo 1617007 5464043 := bstep (se 1 (by rfl) ⟨4098032, by rfl⟩ : syracuseStep 5464043 = 8196065) B8196065
theorem B13819895 : Blo 1617007 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B15556799 : Blo 1617007 15556799 := bstep (se 1 (by rfl) ⟨11667599, by rfl⟩ : syracuseStep 15556799 = 23335199) B23335199
theorem B2425577 : Blo 1617007 2425577 := bstep (se 2 (by rfl) ⟨909591, by rfl⟩ : syracuseStep 2425577 = 1819183) B1819183
theorem B6144893 : Blo 1617007 6144893 := bstep (se 3 (by rfl) ⟨1152167, by rfl⟩ : syracuseStep 6144893 = 2304335) B2304335
theorem B7791497 : Blo 1617007 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B2728991 : Blo 1617007 2728991 := bstep (se 1 (by rfl) ⟨2046743, by rfl⟩ : syracuseStep 2728991 = 4093487) B4093487
theorem B2426039 : Blo 1617007 2426039 := bstep (se 1 (by rfl) ⟨1819529, by rfl⟩ : syracuseStep 2426039 = 3639059) B3639059
theorem B3638555 : Blo 1617007 3638555 := bstep (se 1 (by rfl) ⟨2728916, by rfl⟩ : syracuseStep 3638555 = 5457833) B5457833
theorem B2458921 : Blo 1617007 2458921 := bstep (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) B1844191
theorem B3638591 : Blo 1617007 3638591 := bstep (se 1 (by rfl) ⟨2728943, by rfl⟩ : syracuseStep 3638591 = 5457887) B5457887
theorem B2426471 : Blo 1617007 2426471 := bstep (se 1 (by rfl) ⟨1819853, by rfl⟩ : syracuseStep 2426471 = 3639707) B3639707
theorem B6907625 : Blo 1617007 6907625 := bstep (se 2 (by rfl) ⟨2590359, by rfl⟩ : syracuseStep 6907625 = 5180719) B5180719
theorem B403973891 : Blo 1617007 403973891 := bstep (se 1 (by rfl) ⟨302980418, by rfl⟩ : syracuseStep 403973891 = 605960837) B605960837
theorem B3639689 : Blo 1617007 3639689 := bstep (se 2 (by rfl) ⟨1364883, by rfl⟩ : syracuseStep 3639689 = 2729767) B2729767
theorem B2427785 : Blo 1617007 2427785 := bstep (se 2 (by rfl) ⟨910419, by rfl⟩ : syracuseStep 2427785 = 1820839) B1820839
theorem B1617023 : Blo 1617007 1617023 := bstep (se 1 (by rfl) ⟨1212767, by rfl⟩ : syracuseStep 1617023 = 2425535) B2425535
theorem B113601853 : Blo 1617007 113601853 := bstep (se 3 (by rfl) ⟨21300347, by rfl⟩ : syracuseStep 113601853 = 42600695) B42600695
theorem B4607371 : Blo 1617007 4607371 := bstep (se 1 (by rfl) ⟨3455528, by rfl⟩ : syracuseStep 4607371 = 6911057) B6911057
theorem B26250803 : Blo 1617007 26250803 := bstep (se 1 (by rfl) ⟨19688102, by rfl⟩ : syracuseStep 26250803 = 39376205) B39376205
theorem B4673095 : Blo 1617007 4673095 := bstep (se 1 (by rfl) ⟨3504821, by rfl⟩ : syracuseStep 4673095 = 7009643) B7009643
theorem B3641039 : Blo 1617007 3641039 := bstep (se 1 (by rfl) ⟨2730779, by rfl⟩ : syracuseStep 3641039 = 5461559) B5461559
theorem B1618247 : Blo 1617007 1618247 := bstep (se 1 (by rfl) ⟨1213685, by rfl⟩ : syracuseStep 1618247 = 2427371) B2427371
theorem B5460479 : Blo 1617007 5460479 := bstep (se 1 (by rfl) ⟨4095359, by rfl⟩ : syracuseStep 5460479 = 8190719) B8190719
theorem B265720499 : Blo 1617007 265720499 := bstep (se 1 (by rfl) ⟨199290374, by rfl⟩ : syracuseStep 265720499 = 398580749) B398580749
theorem B7779091 : Blo 1617007 7779091 := bstep (se 1 (by rfl) ⟨5834318, by rfl⟩ : syracuseStep 7779091 = 11668637) B11668637
theorem B134665199 : Blo 1617007 134665199 := bstep (se 1 (by rfl) ⟨100998899, by rfl⟩ : syracuseStep 134665199 = 201997799) B201997799
theorem B3642695 : Blo 1617007 3642695 := bstep (se 1 (by rfl) ⟨2732021, by rfl⟩ : syracuseStep 3642695 = 5464043) B5464043
theorem B9213263 : Blo 1617007 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B215775427 : Blo 1617007 215775427 := bstep (se 1 (by rfl) ⟨161831570, by rfl⟩ : syracuseStep 215775427 = 323663141) B323663141
theorem B13818833 : Blo 1617007 13818833 := bstep (se 2 (by rfl) ⟨5182062, by rfl⟩ : syracuseStep 13818833 = 10364125) B10364125
theorem B15555721 : Blo 1617007 15555721 := bstep (se 2 (by rfl) ⟨5833395, by rfl⟩ : syracuseStep 15555721 = 11666791) B11666791
theorem B2047295 : Blo 1617007 2047295 := bstep (se 1 (by rfl) ⟨1535471, by rfl⟩ : syracuseStep 2047295 = 3070943) B3070943
theorem B7003547 : Blo 1617007 7003547 := bstep (se 1 (by rfl) ⟨5252660, by rfl⟩ : syracuseStep 7003547 = 10505321) B10505321
theorem B1727935 : Blo 1617007 1727935 := bstep (se 1 (by rfl) ⟨1295951, by rfl⟩ : syracuseStep 1727935 = 2591903) B2591903
theorem B9215927 : Blo 1617007 9215927 := bstep (se 1 (by rfl) ⟨6911945, by rfl⟩ : syracuseStep 9215927 = 13823891) B13823891
theorem B10371199 : Blo 1617007 10371199 := bstep (se 1 (by rfl) ⟨7778399, by rfl⟩ : syracuseStep 10371199 = 15556799) B15556799
theorem B4096595 : Blo 1617007 4096595 := bstep (se 1 (by rfl) ⟨3072446, by rfl⟩ : syracuseStep 4096595 = 6144893) B6144893
theorem B5194331 : Blo 1617007 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B89776799 : Blo 1617007 89776799 := bstep (se 1 (by rfl) ⟨67332599, by rfl⟩ : syracuseStep 89776799 = 134665199) B134665199
theorem B1819327 : Blo 1617007 1819327 := bstep (se 1 (by rfl) ⟨1364495, by rfl⟩ : syracuseStep 1819327 = 2728991) B2728991
theorem B2425703 : Blo 1617007 2425703 := bstep (se 1 (by rfl) ⟨1819277, by rfl⟩ : syracuseStep 2425703 = 3638555) B3638555
theorem B2425727 : Blo 1617007 2425727 := bstep (se 1 (by rfl) ⟨1819295, by rfl⟩ : syracuseStep 2425727 = 3638591) B3638591
theorem B10372121 : Blo 1617007 10372121 := bstep (se 2 (by rfl) ⟨3889545, by rfl⟩ : syracuseStep 10372121 = 7779091) B7779091
theorem B4605083 : Blo 1617007 4605083 := bstep (se 1 (by rfl) ⟨3453812, by rfl⟩ : syracuseStep 4605083 = 6907625) B6907625
theorem B2426459 : Blo 1617007 2426459 := bstep (se 1 (by rfl) ⟨1819844, by rfl⟩ : syracuseStep 2426459 = 3639689) B3639689
theorem B3278561 : Blo 1617007 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B17500535 : Blo 1617007 17500535 := bstep (se 1 (by rfl) ⟨13125401, by rfl⟩ : syracuseStep 17500535 = 26250803) B26250803
theorem B2427359 : Blo 1617007 2427359 := bstep (se 1 (by rfl) ⟨1820519, by rfl⟩ : syracuseStep 2427359 = 3641039) B3641039
theorem B3640319 : Blo 1617007 3640319 := bstep (se 1 (by rfl) ⟨2730239, by rfl⟩ : syracuseStep 3640319 = 5460479) B5460479
theorem B24923173 : Blo 1617007 24923173 := bstep (se 4 (by rfl) ⟨2336547, by rfl⟩ : syracuseStep 24923173 = 4673095) B4673095
theorem B177146999 : Blo 1617007 177146999 := bstep (se 1 (by rfl) ⟨132860249, by rfl⟩ : syracuseStep 177146999 = 265720499) B265720499
theorem B1617051 : Blo 1617007 1617051 := bstep (se 1 (by rfl) ⟨1212788, by rfl⟩ : syracuseStep 1617051 = 2425577) B2425577
theorem B1617359 : Blo 1617007 1617359 := bstep (se 1 (by rfl) ⟨1213019, by rfl⟩ : syracuseStep 1617359 = 2426039) B2426039
theorem B5459453 : Blo 1617007 5459453 := bstep (se 3 (by rfl) ⟨1023647, by rfl⟩ : syracuseStep 5459453 = 2047295) B2047295
theorem B2428463 : Blo 1617007 2428463 := bstep (se 1 (by rfl) ⟨1821347, by rfl⟩ : syracuseStep 2428463 = 3642695) B3642695
theorem B1617647 : Blo 1617007 1617647 := bstep (se 1 (by rfl) ⟨1213235, by rfl⟩ : syracuseStep 1617647 = 2426471) B2426471
theorem B269315927 : Blo 1617007 269315927 := bstep (se 1 (by rfl) ⟨201986945, by rfl⟩ : syracuseStep 269315927 = 403973891) B403973891
theorem B1618523 : Blo 1617007 1618523 := bstep (se 1 (by rfl) ⟨1213892, by rfl⟩ : syracuseStep 1618523 = 2427785) B2427785
theorem B9212555 : Blo 1617007 9212555 := bstep (se 1 (by rfl) ⟨6909416, by rfl⟩ : syracuseStep 9212555 = 13818833) B13818833
theorem B287700569 : Blo 1617007 287700569 := bstep (se 2 (by rfl) ⟨107887713, by rfl⟩ : syracuseStep 287700569 = 215775427) B215775427
theorem B6142175 : Blo 1617007 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B20740961 : Blo 1617007 20740961 := bstep (se 2 (by rfl) ⟨7777860, by rfl⟩ : syracuseStep 20740961 = 15555721) B15555721
theorem B151469137 : Blo 1617007 151469137 := bstep (se 2 (by rfl) ⟨56800926, by rfl⟩ : syracuseStep 151469137 = 113601853) B113601853
theorem B6143161 : Blo 1617007 6143161 := bstep (se 2 (by rfl) ⟨2303685, by rfl⟩ : syracuseStep 6143161 = 4607371) B4607371
theorem B4669031 : Blo 1617007 4669031 := bstep (se 1 (by rfl) ⟨3501773, by rfl⟩ : syracuseStep 4669031 = 7003547) B7003547
theorem B9215653 : Blo 1617007 9215653 := bstep (se 4 (by rfl) ⟨863967, by rfl⟩ : syracuseStep 9215653 = 1727935) B1727935
theorem B6143951 : Blo 1617007 6143951 := bstep (se 1 (by rfl) ⟨4607963, by rfl⟩ : syracuseStep 6143951 = 9215927) B9215927
theorem B13828265 : Blo 1617007 13828265 := bstep (se 2 (by rfl) ⟨5185599, by rfl⟩ : syracuseStep 13828265 = 10371199) B10371199
theorem B59851199 : Blo 1617007 59851199 := bstep (se 1 (by rfl) ⟨44888399, by rfl⟩ : syracuseStep 59851199 = 89776799) B89776799
theorem B6914747 : Blo 1617007 6914747 := bstep (se 1 (by rfl) ⟨5186060, by rfl⟩ : syracuseStep 6914747 = 10372121) B10372121
theorem B2425769 : Blo 1617007 2425769 := bstep (se 2 (by rfl) ⟨909663, by rfl⟩ : syracuseStep 2425769 = 1819327) B1819327
theorem B191800379 : Blo 1617007 191800379 := bstep (se 1 (by rfl) ⟨143850284, by rfl⟩ : syracuseStep 191800379 = 287700569) B287700569
theorem B201958849 : Blo 1617007 201958849 := bstep (se 2 (by rfl) ⟨75734568, by rfl⟩ : syracuseStep 201958849 = 151469137) B151469137
theorem B11667023 : Blo 1617007 11667023 := bstep (se 1 (by rfl) ⟨8750267, by rfl⟩ : syracuseStep 11667023 = 17500535) B17500535
theorem B8742829 : Blo 1617007 8742829 := bstep (se 3 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 8742829 = 3278561) B3278561
theorem B2426879 : Blo 1617007 2426879 := bstep (se 1 (by rfl) ⟨1820159, by rfl⟩ : syracuseStep 2426879 = 3640319) B3640319
theorem B118097999 : Blo 1617007 118097999 := bstep (se 1 (by rfl) ⟨88573499, by rfl⟩ : syracuseStep 118097999 = 177146999) B177146999
theorem B3639635 : Blo 1617007 3639635 := bstep (se 1 (by rfl) ⟨2729726, by rfl⟩ : syracuseStep 3639635 = 5459453) B5459453
theorem B2731063 : Blo 1617007 2731063 := bstep (se 1 (by rfl) ⟨2048297, by rfl⟩ : syracuseStep 2731063 = 4096595) B4096595
theorem B1617135 : Blo 1617007 1617135 := bstep (se 1 (by rfl) ⟨1212851, by rfl⟩ : syracuseStep 1617135 = 2425703) B2425703
theorem B1617151 : Blo 1617007 1617151 := bstep (se 1 (by rfl) ⟨1212863, by rfl⟩ : syracuseStep 1617151 = 2425727) B2425727
theorem B1617639 : Blo 1617007 1617639 := bstep (se 1 (by rfl) ⟨1213229, by rfl⟩ : syracuseStep 1617639 = 2426459) B2426459
theorem B33230897 : Blo 1617007 33230897 := bstep (se 2 (by rfl) ⟨12461586, by rfl⟩ : syracuseStep 33230897 = 24923173) B24923173
theorem B1618239 : Blo 1617007 1618239 := bstep (se 1 (by rfl) ⟨1213679, by rfl⟩ : syracuseStep 1618239 = 2427359) B2427359
theorem B1618975 : Blo 1617007 1618975 := bstep (se 1 (by rfl) ⟨1214231, by rfl⟩ : syracuseStep 1618975 = 2428463) B2428463
theorem B3462887 : Blo 1617007 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B6141703 : Blo 1617007 6141703 := bstep (se 1 (by rfl) ⟨4606277, by rfl⟩ : syracuseStep 6141703 = 9212555) B9212555
theorem B3070055 : Blo 1617007 3070055 := bstep (se 1 (by rfl) ⟨2302541, by rfl⟩ : syracuseStep 3070055 = 4605083) B4605083
theorem B4094783 : Blo 1617007 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B8190881 : Blo 1617007 8190881 := bstep (se 2 (by rfl) ⟨3071580, by rfl⟩ : syracuseStep 8190881 = 6143161) B6143161
theorem B13827307 : Blo 1617007 13827307 := bstep (se 1 (by rfl) ⟨10370480, by rfl⟩ : syracuseStep 13827307 = 20740961) B20740961
theorem B12287537 : Blo 1617007 12287537 := bstep (se 2 (by rfl) ⟨4607826, by rfl⟩ : syracuseStep 12287537 = 9215653) B9215653
theorem B3112687 : Blo 1617007 3112687 := bstep (se 1 (by rfl) ⟨2334515, by rfl⟩ : syracuseStep 3112687 = 4669031) B4669031
theorem B179543951 : Blo 1617007 179543951 := bstep (se 1 (by rfl) ⟨134657963, by rfl⟩ : syracuseStep 179543951 = 269315927) B269315927
theorem B4095967 : Blo 1617007 4095967 := bstep (se 1 (by rfl) ⟨3071975, by rfl⟩ : syracuseStep 4095967 = 6143951) B6143951
theorem B2426423 : Blo 1617007 2426423 := bstep (se 1 (by rfl) ⟨1819817, by rfl⟩ : syracuseStep 2426423 = 3639635) B3639635
theorem B2729855 : Blo 1617007 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B119695967 : Blo 1617007 119695967 := bstep (se 1 (by rfl) ⟨89771975, by rfl⟩ : syracuseStep 119695967 = 179543951) B179543951
theorem B22153931 : Blo 1617007 22153931 := bstep (se 1 (by rfl) ⟨16615448, by rfl⟩ : syracuseStep 22153931 = 33230897) B33230897
theorem B9218843 : Blo 1617007 9218843 := bstep (se 1 (by rfl) ⟨6914132, by rfl⟩ : syracuseStep 9218843 = 13828265) B13828265
theorem B1617179 : Blo 1617007 1617179 := bstep (se 1 (by rfl) ⟨1212884, by rfl⟩ : syracuseStep 1617179 = 2425769) B2425769
theorem B7778015 : Blo 1617007 7778015 := bstep (se 1 (by rfl) ⟨5833511, by rfl⟩ : syracuseStep 7778015 = 11667023) B11667023
theorem B1617919 : Blo 1617007 1617919 := bstep (se 1 (by rfl) ⟨1213439, by rfl⟩ : syracuseStep 1617919 = 2426879) B2426879
theorem B3641417 : Blo 1617007 3641417 := bstep (se 2 (by rfl) ⟨1365531, by rfl⟩ : syracuseStep 3641417 = 2731063) B2731063
theorem B18436409 : Blo 1617007 18436409 := bstep (se 2 (by rfl) ⟨6913653, by rfl⟩ : syracuseStep 18436409 = 13827307) B13827307
theorem B5460587 : Blo 1617007 5460587 := bstep (se 1 (by rfl) ⟨4095440, by rfl⟩ : syracuseStep 5460587 = 8190881) B8190881
theorem B4150249 : Blo 1617007 4150249 := bstep (se 2 (by rfl) ⟨1556343, by rfl⟩ : syracuseStep 4150249 = 3112687) B3112687
theorem B8188937 : Blo 1617007 8188937 := bstep (se 2 (by rfl) ⟨3070851, by rfl⟩ : syracuseStep 8188937 = 6141703) B6141703
theorem B5461289 : Blo 1617007 5461289 := bstep (se 2 (by rfl) ⟨2047983, by rfl⟩ : syracuseStep 5461289 = 4095967) B4095967
theorem B39900799 : Blo 1617007 39900799 := bstep (se 1 (by rfl) ⟨29925599, by rfl⟩ : syracuseStep 39900799 = 59851199) B59851199
theorem B127866919 : Blo 1617007 127866919 := bstep (se 1 (by rfl) ⟨95900189, by rfl⟩ : syracuseStep 127866919 = 191800379) B191800379
theorem B2308591 : Blo 1617007 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B78731999 : Blo 1617007 78731999 := bstep (se 1 (by rfl) ⟨59048999, by rfl⟩ : syracuseStep 78731999 = 118097999) B118097999
theorem B2046703 : Blo 1617007 2046703 := bstep (se 1 (by rfl) ⟨1535027, by rfl⟩ : syracuseStep 2046703 = 3070055) B3070055
theorem B18439325 : Blo 1617007 18439325 := bstep (se 3 (by rfl) ⟨3457373, by rfl⟩ : syracuseStep 18439325 = 6914747) B6914747
theorem B269278465 : Blo 1617007 269278465 := bstep (se 2 (by rfl) ⟨100979424, by rfl⟩ : syracuseStep 269278465 = 201958849) B201958849
theorem B8191691 : Blo 1617007 8191691 := bstep (se 1 (by rfl) ⟨6143768, by rfl⟩ : syracuseStep 8191691 = 12287537) B12287537
theorem B11657105 : Blo 1617007 11657105 := bstep (se 2 (by rfl) ⟨4371414, by rfl⟩ : syracuseStep 11657105 = 8742829) B8742829
theorem B2728937 : Blo 1617007 2728937 := bstep (se 2 (by rfl) ⟨1023351, by rfl⟩ : syracuseStep 2728937 = 2046703) B2046703
theorem B1819903 : Blo 1617007 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B52487999 : Blo 1617007 52487999 := bstep (se 1 (by rfl) ⟨39365999, by rfl⟩ : syracuseStep 52487999 = 78731999) B78731999
theorem B6145895 : Blo 1617007 6145895 := bstep (se 1 (by rfl) ⟨4609421, by rfl⟩ : syracuseStep 6145895 = 9218843) B9218843
theorem B53201065 : Blo 1617007 53201065 := bstep (se 2 (by rfl) ⟨19950399, by rfl⟩ : syracuseStep 53201065 = 39900799) B39900799
theorem B2427611 : Blo 1617007 2427611 := bstep (se 1 (by rfl) ⟨1820708, by rfl⟩ : syracuseStep 2427611 = 3641417) B3641417
theorem B12290939 : Blo 1617007 12290939 := bstep (se 1 (by rfl) ⟨9218204, by rfl⟩ : syracuseStep 12290939 = 18436409) B18436409
theorem B3640391 : Blo 1617007 3640391 := bstep (se 1 (by rfl) ⟨2730293, by rfl⟩ : syracuseStep 3640391 = 5460587) B5460587
theorem B5459291 : Blo 1617007 5459291 := bstep (se 1 (by rfl) ⟨4094468, by rfl⟩ : syracuseStep 5459291 = 8188937) B8188937
theorem B3640859 : Blo 1617007 3640859 := bstep (se 1 (by rfl) ⟨2730644, by rfl⟩ : syracuseStep 3640859 = 5461289) B5461289
theorem B1617615 : Blo 1617007 1617615 := bstep (se 1 (by rfl) ⟨1213211, by rfl⟩ : syracuseStep 1617615 = 2426423) B2426423
theorem B12292883 : Blo 1617007 12292883 := bstep (se 1 (by rfl) ⟨9219662, by rfl⟩ : syracuseStep 12292883 = 18439325) B18439325
theorem B5461127 : Blo 1617007 5461127 := bstep (se 1 (by rfl) ⟨4095845, by rfl⟩ : syracuseStep 5461127 = 8191691) B8191691
theorem B7771403 : Blo 1617007 7771403 := bstep (se 1 (by rfl) ⟨5828552, by rfl⟩ : syracuseStep 7771403 = 11657105) B11657105
theorem B170489225 : Blo 1617007 170489225 := bstep (se 2 (by rfl) ⟨63933459, by rfl⟩ : syracuseStep 170489225 = 127866919) B127866919
theorem B359037953 : Blo 1617007 359037953 := bstep (se 2 (by rfl) ⟨134639232, by rfl⟩ : syracuseStep 359037953 = 269278465) B269278465
theorem B79797311 : Blo 1617007 79797311 := bstep (se 1 (by rfl) ⟨59847983, by rfl⟩ : syracuseStep 79797311 = 119695967) B119695967
theorem B14769287 : Blo 1617007 14769287 := bstep (se 1 (by rfl) ⟨11076965, by rfl⟩ : syracuseStep 14769287 = 22153931) B22153931
theorem B88538645 : Blo 1617007 88538645 := bstep (se 6 (by rfl) ⟨2075124, by rfl⟩ : syracuseStep 88538645 = 4150249) B4150249
theorem B5185343 : Blo 1617007 5185343 := bstep (se 1 (by rfl) ⟨3889007, by rfl⟩ : syracuseStep 5185343 = 7778015) B7778015
theorem B12312485 : Blo 1617007 12312485 := bstep (se 4 (by rfl) ⟨1154295, by rfl⟩ : syracuseStep 12312485 = 2308591) B2308591
theorem B70934753 : Blo 1617007 70934753 := bstep (se 2 (by rfl) ⟨26600532, by rfl⟩ : syracuseStep 70934753 = 53201065) B53201065
theorem B1819291 : Blo 1617007 1819291 := bstep (se 1 (by rfl) ⟨1364468, by rfl⟩ : syracuseStep 1819291 = 2728937) B2728937
theorem B4097263 : Blo 1617007 4097263 := bstep (se 1 (by rfl) ⟨3072947, by rfl⟩ : syracuseStep 4097263 = 6145895) B6145895
theorem B2426537 : Blo 1617007 2426537 := bstep (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) B1819903
theorem B8193959 : Blo 1617007 8193959 := bstep (se 1 (by rfl) ⟨6145469, by rfl⟩ : syracuseStep 8193959 = 12290939) B12290939
theorem B2426927 : Blo 1617007 2426927 := bstep (se 1 (by rfl) ⟨1820195, by rfl⟩ : syracuseStep 2426927 = 3640391) B3640391
theorem B3639527 : Blo 1617007 3639527 := bstep (se 1 (by rfl) ⟨2729645, by rfl⟩ : syracuseStep 3639527 = 5459291) B5459291
theorem B59025763 : Blo 1617007 59025763 := bstep (se 1 (by rfl) ⟨44269322, by rfl⟩ : syracuseStep 59025763 = 88538645) B88538645
theorem B2427239 : Blo 1617007 2427239 := bstep (se 1 (by rfl) ⟨1820429, by rfl⟩ : syracuseStep 2427239 = 3640859) B3640859
theorem B8195255 : Blo 1617007 8195255 := bstep (se 1 (by rfl) ⟨6146441, by rfl⟩ : syracuseStep 8195255 = 12292883) B12292883
theorem B3640751 : Blo 1617007 3640751 := bstep (se 1 (by rfl) ⟨2730563, by rfl⟩ : syracuseStep 3640751 = 5461127) B5461127
theorem B5180935 : Blo 1617007 5180935 := bstep (se 1 (by rfl) ⟨3885701, by rfl⟩ : syracuseStep 5180935 = 7771403) B7771403
theorem B34991999 : Blo 1617007 34991999 := bstep (se 1 (by rfl) ⟨26243999, by rfl⟩ : syracuseStep 34991999 = 52487999) B52487999
theorem B1618407 : Blo 1617007 1618407 := bstep (se 1 (by rfl) ⟨1213805, by rfl⟩ : syracuseStep 1618407 = 2427611) B2427611
theorem B239358635 : Blo 1617007 239358635 := bstep (se 1 (by rfl) ⟨179518976, by rfl⟩ : syracuseStep 239358635 = 359037953) B359037953
theorem B454637933 : Blo 1617007 454637933 := bstep (se 3 (by rfl) ⟨85244612, by rfl⟩ : syracuseStep 454637933 = 170489225) B170489225
theorem B53198207 : Blo 1617007 53198207 := bstep (se 1 (by rfl) ⟨39898655, by rfl⟩ : syracuseStep 53198207 = 79797311) B79797311
theorem B9846191 : Blo 1617007 9846191 := bstep (se 1 (by rfl) ⟨7384643, by rfl⟩ : syracuseStep 9846191 = 14769287) B14769287
theorem B13827581 : Blo 1617007 13827581 := bstep (se 3 (by rfl) ⟨2592671, by rfl⟩ : syracuseStep 13827581 = 5185343) B5185343
theorem B8208323 : Blo 1617007 8208323 := bstep (se 1 (by rfl) ⟨6156242, by rfl⟩ : syracuseStep 8208323 = 12312485) B12312485
theorem B159572423 : Blo 1617007 159572423 := bstep (se 1 (by rfl) ⟨119679317, by rfl⟩ : syracuseStep 159572423 = 239358635) B239358635
theorem B78701017 : Blo 1617007 78701017 := bstep (se 2 (by rfl) ⟨29512881, by rfl⟩ : syracuseStep 78701017 = 59025763) B59025763
theorem B2425721 : Blo 1617007 2425721 := bstep (se 2 (by rfl) ⟨909645, by rfl⟩ : syracuseStep 2425721 = 1819291) B1819291
theorem B2426351 : Blo 1617007 2426351 := bstep (se 1 (by rfl) ⟨1819763, by rfl⟩ : syracuseStep 2426351 = 3639527) B3639527
theorem B6907913 : Blo 1617007 6907913 := bstep (se 2 (by rfl) ⟨2590467, by rfl⟩ : syracuseStep 6907913 = 5180935) B5180935
theorem B35465471 : Blo 1617007 35465471 := bstep (se 1 (by rfl) ⟨26599103, by rfl⟩ : syracuseStep 35465471 = 53198207) B53198207
theorem B2427167 : Blo 1617007 2427167 := bstep (se 1 (by rfl) ⟨1820375, by rfl⟩ : syracuseStep 2427167 = 3640751) B3640751
theorem B6564127 : Blo 1617007 6564127 := bstep (se 1 (by rfl) ⟨4923095, by rfl⟩ : syracuseStep 6564127 = 9846191) B9846191
theorem B9218387 : Blo 1617007 9218387 := bstep (se 1 (by rfl) ⟨6913790, by rfl⟩ : syracuseStep 9218387 = 13827581) B13827581
theorem B1617691 : Blo 1617007 1617691 := bstep (se 1 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 1617691 = 2426537) B2426537
theorem B1617951 : Blo 1617007 1617951 := bstep (se 1 (by rfl) ⟨1213463, by rfl⟩ : syracuseStep 1617951 = 2426927) B2426927
theorem B1618159 : Blo 1617007 1618159 := bstep (se 1 (by rfl) ⟨1213619, by rfl⟩ : syracuseStep 1618159 = 2427239) B2427239
theorem B303091955 : Blo 1617007 303091955 := bstep (se 1 (by rfl) ⟨227318966, by rfl⟩ : syracuseStep 303091955 = 454637933) B454637933
theorem B23327999 : Blo 1617007 23327999 := bstep (se 1 (by rfl) ⟨17495999, by rfl⟩ : syracuseStep 23327999 = 34991999) B34991999
theorem B47289835 : Blo 1617007 47289835 := bstep (se 1 (by rfl) ⟨35467376, by rfl⟩ : syracuseStep 47289835 = 70934753) B70934753
theorem B5462639 : Blo 1617007 5462639 := bstep (se 1 (by rfl) ⟨4096979, by rfl⟩ : syracuseStep 5462639 = 8193959) B8193959
theorem B5463017 : Blo 1617007 5463017 := bstep (se 2 (by rfl) ⟨2048631, by rfl⟩ : syracuseStep 5463017 = 4097263) B4097263
theorem B5463503 : Blo 1617007 5463503 := bstep (se 1 (by rfl) ⟨4097627, by rfl⟩ : syracuseStep 5463503 = 8195255) B8195255
theorem B5472215 : Blo 1617007 5472215 := bstep (se 1 (by rfl) ⟨4104161, by rfl⟩ : syracuseStep 5472215 = 8208323) B8208323
theorem B106381615 : Blo 1617007 106381615 := bstep (se 1 (by rfl) ⟨79786211, by rfl⟩ : syracuseStep 106381615 = 159572423) B159572423
theorem B4605275 : Blo 1617007 4605275 := bstep (se 1 (by rfl) ⟨3453956, by rfl⟩ : syracuseStep 4605275 = 6907913) B6907913
theorem B23643647 : Blo 1617007 23643647 := bstep (se 1 (by rfl) ⟨17732735, by rfl⟩ : syracuseStep 23643647 = 35465471) B35465471
theorem B6145591 : Blo 1617007 6145591 := bstep (se 1 (by rfl) ⟨4609193, by rfl⟩ : syracuseStep 6145591 = 9218387) B9218387
theorem B3648143 : Blo 1617007 3648143 := bstep (se 1 (by rfl) ⟨2736107, by rfl⟩ : syracuseStep 3648143 = 5472215) B5472215
theorem B8752169 : Blo 1617007 8752169 := bstep (se 2 (by rfl) ⟨3282063, by rfl⟩ : syracuseStep 8752169 = 6564127) B6564127
theorem B1617147 : Blo 1617007 1617147 := bstep (se 1 (by rfl) ⟨1212860, by rfl⟩ : syracuseStep 1617147 = 2425721) B2425721
theorem B104934689 : Blo 1617007 104934689 := bstep (se 2 (by rfl) ⟨39350508, by rfl⟩ : syracuseStep 104934689 = 78701017) B78701017
theorem B15551999 : Blo 1617007 15551999 := bstep (se 1 (by rfl) ⟨11663999, by rfl⟩ : syracuseStep 15551999 = 23327999) B23327999
theorem B1617567 : Blo 1617007 1617567 := bstep (se 1 (by rfl) ⟨1213175, by rfl⟩ : syracuseStep 1617567 = 2426351) B2426351
theorem B1618111 : Blo 1617007 1618111 := bstep (se 1 (by rfl) ⟨1213583, by rfl⟩ : syracuseStep 1618111 = 2427167) B2427167
theorem B3641759 : Blo 1617007 3641759 := bstep (se 1 (by rfl) ⟨2731319, by rfl⟩ : syracuseStep 3641759 = 5462639) B5462639
theorem B3642011 : Blo 1617007 3642011 := bstep (se 1 (by rfl) ⟨2731508, by rfl⟩ : syracuseStep 3642011 = 5463017) B5463017
theorem B3642335 : Blo 1617007 3642335 := bstep (se 1 (by rfl) ⟨2731751, by rfl⟩ : syracuseStep 3642335 = 5463503) B5463503
theorem B202061303 : Blo 1617007 202061303 := bstep (se 1 (by rfl) ⟨151545977, by rfl⟩ : syracuseStep 202061303 = 303091955) B303091955
theorem B63053113 : Blo 1617007 63053113 := bstep (se 2 (by rfl) ⟨23644917, by rfl⟩ : syracuseStep 63053113 = 47289835) B47289835
theorem B23339117 : Blo 1617007 23339117 := bstep (se 3 (by rfl) ⟨4376084, by rfl⟩ : syracuseStep 23339117 = 8752169) B8752169
theorem B12280733 : Blo 1617007 12280733 := bstep (se 3 (by rfl) ⟨2302637, by rfl⟩ : syracuseStep 12280733 = 4605275) B4605275
theorem B15762431 : Blo 1617007 15762431 := bstep (se 1 (by rfl) ⟨11821823, by rfl⟩ : syracuseStep 15762431 = 23643647) B23643647
theorem B8194121 : Blo 1617007 8194121 := bstep (se 2 (by rfl) ⟨3072795, by rfl⟩ : syracuseStep 8194121 = 6145591) B6145591
theorem B2427839 : Blo 1617007 2427839 := bstep (se 1 (by rfl) ⟨1820879, by rfl⟩ : syracuseStep 2427839 = 3641759) B3641759
theorem B2428007 : Blo 1617007 2428007 := bstep (se 1 (by rfl) ⟨1821005, by rfl⟩ : syracuseStep 2428007 = 3642011) B3642011
theorem B2428223 : Blo 1617007 2428223 := bstep (se 1 (by rfl) ⟨1821167, by rfl⟩ : syracuseStep 2428223 = 3642335) B3642335
theorem B9728381 : Blo 1617007 9728381 := bstep (se 3 (by rfl) ⟨1824071, by rfl⟩ : syracuseStep 9728381 = 3648143) B3648143
theorem B84070817 : Blo 1617007 84070817 := bstep (se 2 (by rfl) ⟨31526556, by rfl⟩ : syracuseStep 84070817 = 63053113) B63053113
theorem B69956459 : Blo 1617007 69956459 := bstep (se 1 (by rfl) ⟨52467344, by rfl⟩ : syracuseStep 69956459 = 104934689) B104934689
theorem B10367999 : Blo 1617007 10367999 := bstep (se 1 (by rfl) ⟨7775999, by rfl⟩ : syracuseStep 10367999 = 15551999) B15551999
theorem B141842153 : Blo 1617007 141842153 := bstep (se 2 (by rfl) ⟨53190807, by rfl⟩ : syracuseStep 141842153 = 106381615) B106381615
theorem B134707535 : Blo 1617007 134707535 := bstep (se 1 (by rfl) ⟨101030651, by rfl⟩ : syracuseStep 134707535 = 202061303) B202061303
theorem B46637639 : Blo 1617007 46637639 := bstep (se 1 (by rfl) ⟨34978229, by rfl⟩ : syracuseStep 46637639 = 69956459) B69956459
theorem B94561435 : Blo 1617007 94561435 := bstep (se 1 (by rfl) ⟨70921076, by rfl⟩ : syracuseStep 94561435 = 141842153) B141842153
theorem B62237645 : Blo 1617007 62237645 := bstep (se 3 (by rfl) ⟨11669558, by rfl⟩ : syracuseStep 62237645 = 23339117) B23339117
theorem B8187155 : Blo 1617007 8187155 := bstep (se 1 (by rfl) ⟨6140366, by rfl⟩ : syracuseStep 8187155 = 12280733) B12280733
theorem B89805023 : Blo 1617007 89805023 := bstep (se 1 (by rfl) ⟨67353767, by rfl⟩ : syracuseStep 89805023 = 134707535) B134707535
theorem B1618559 : Blo 1617007 1618559 := bstep (se 1 (by rfl) ⟨1213919, by rfl⟩ : syracuseStep 1618559 = 2427839) B2427839
theorem B1618671 : Blo 1617007 1618671 := bstep (se 1 (by rfl) ⟨1214003, by rfl⟩ : syracuseStep 1618671 = 2428007) B2428007
theorem B1618815 : Blo 1617007 1618815 := bstep (se 1 (by rfl) ⟨1214111, by rfl⟩ : syracuseStep 1618815 = 2428223) B2428223
theorem B56047211 : Blo 1617007 56047211 := bstep (se 1 (by rfl) ⟨42035408, by rfl⟩ : syracuseStep 56047211 = 84070817) B84070817
theorem B10508287 : Blo 1617007 10508287 := bstep (se 1 (by rfl) ⟨7881215, by rfl⟩ : syracuseStep 10508287 = 15762431) B15762431
theorem B6911999 : Blo 1617007 6911999 := bstep (se 1 (by rfl) ⟨5183999, by rfl⟩ : syracuseStep 6911999 = 10367999) B10367999
theorem B25942349 : Blo 1617007 25942349 := bstep (se 3 (by rfl) ⟨4864190, by rfl⟩ : syracuseStep 25942349 = 9728381) B9728381
theorem B5462747 : Blo 1617007 5462747 := bstep (se 1 (by rfl) ⟨4097060, by rfl⟩ : syracuseStep 5462747 = 8194121) B8194121
theorem B37364807 : Blo 1617007 37364807 := bstep (se 1 (by rfl) ⟨28023605, by rfl⟩ : syracuseStep 37364807 = 56047211) B56047211
theorem B17294899 : Blo 1617007 17294899 := bstep (se 1 (by rfl) ⟨12971174, by rfl⟩ : syracuseStep 17294899 = 25942349) B25942349
theorem B5458103 : Blo 1617007 5458103 := bstep (se 1 (by rfl) ⟨4093577, by rfl⟩ : syracuseStep 5458103 = 8187155) B8187155
theorem B14011049 : Blo 1617007 14011049 := bstep (se 2 (by rfl) ⟨5254143, by rfl⟩ : syracuseStep 14011049 = 10508287) B10508287
theorem B59870015 : Blo 1617007 59870015 := bstep (se 1 (by rfl) ⟨44902511, by rfl⟩ : syracuseStep 59870015 = 89805023) B89805023
theorem B31091759 : Blo 1617007 31091759 := bstep (se 1 (by rfl) ⟨23318819, by rfl⟩ : syracuseStep 31091759 = 46637639) B46637639
theorem B504327653 : Blo 1617007 504327653 := bstep (se 4 (by rfl) ⟨47280717, by rfl⟩ : syracuseStep 504327653 = 94561435) B94561435
theorem B4607999 : Blo 1617007 4607999 := bstep (se 1 (by rfl) ⟨3455999, by rfl⟩ : syracuseStep 4607999 = 6911999) B6911999
theorem B3641831 : Blo 1617007 3641831 := bstep (se 1 (by rfl) ⟨2731373, by rfl⟩ : syracuseStep 3641831 = 5462747) B5462747
theorem B41491763 : Blo 1617007 41491763 := bstep (se 1 (by rfl) ⟨31118822, by rfl⟩ : syracuseStep 41491763 = 62237645) B62237645
theorem B3638735 : Blo 1617007 3638735 := bstep (se 1 (by rfl) ⟨2729051, by rfl⟩ : syracuseStep 3638735 = 5458103) B5458103
theorem B9340699 : Blo 1617007 9340699 := bstep (se 1 (by rfl) ⟨7005524, by rfl⟩ : syracuseStep 9340699 = 14011049) B14011049
theorem B39913343 : Blo 1617007 39913343 := bstep (se 1 (by rfl) ⟨29935007, by rfl⟩ : syracuseStep 39913343 = 59870015) B59870015
theorem B20727839 : Blo 1617007 20727839 := bstep (se 1 (by rfl) ⟨15545879, by rfl⟩ : syracuseStep 20727839 = 31091759) B31091759
theorem B336218435 : Blo 1617007 336218435 := bstep (se 1 (by rfl) ⟨252163826, by rfl⟩ : syracuseStep 336218435 = 504327653) B504327653
theorem B2427887 : Blo 1617007 2427887 := bstep (se 1 (by rfl) ⟨1820915, by rfl⟩ : syracuseStep 2427887 = 3641831) B3641831
theorem B27661175 : Blo 1617007 27661175 := bstep (se 1 (by rfl) ⟨20745881, by rfl⟩ : syracuseStep 27661175 = 41491763) B41491763
theorem B3071999 : Blo 1617007 3071999 := bstep (se 1 (by rfl) ⟨2303999, by rfl⟩ : syracuseStep 3071999 = 4607999) B4607999
theorem B24909871 : Blo 1617007 24909871 := bstep (se 1 (by rfl) ⟨18682403, by rfl⟩ : syracuseStep 24909871 = 37364807) B37364807
theorem B23059865 : Blo 1617007 23059865 := bstep (se 2 (by rfl) ⟨8647449, by rfl⟩ : syracuseStep 23059865 = 17294899) B17294899
theorem B18440783 : Blo 1617007 18440783 := bstep (se 1 (by rfl) ⟨13830587, by rfl⟩ : syracuseStep 18440783 = 27661175) B27661175
theorem B2425823 : Blo 1617007 2425823 := bstep (se 1 (by rfl) ⟨1819367, by rfl⟩ : syracuseStep 2425823 = 3638735) B3638735
theorem B26608895 : Blo 1617007 26608895 := bstep (se 1 (by rfl) ⟨19956671, by rfl⟩ : syracuseStep 26608895 = 39913343) B39913343
theorem B12454265 : Blo 1617007 12454265 := bstep (se 2 (by rfl) ⟨4670349, by rfl⟩ : syracuseStep 12454265 = 9340699) B9340699
theorem B33213161 : Blo 1617007 33213161 := bstep (se 2 (by rfl) ⟨12454935, by rfl⟩ : syracuseStep 33213161 = 24909871) B24909871
theorem B224145623 : Blo 1617007 224145623 := bstep (se 1 (by rfl) ⟨168109217, by rfl⟩ : syracuseStep 224145623 = 336218435) B336218435
theorem B1618591 : Blo 1617007 1618591 := bstep (se 1 (by rfl) ⟨1213943, by rfl⟩ : syracuseStep 1618591 = 2427887) B2427887
theorem B15373243 : Blo 1617007 15373243 := bstep (se 1 (by rfl) ⟨11529932, by rfl⟩ : syracuseStep 15373243 = 23059865) B23059865
theorem B13818559 : Blo 1617007 13818559 := bstep (se 1 (by rfl) ⟨10363919, by rfl⟩ : syracuseStep 13818559 = 20727839) B20727839
theorem B2047999 : Blo 1617007 2047999 := bstep (se 1 (by rfl) ⟨1535999, by rfl⟩ : syracuseStep 2047999 = 3071999) B3071999
theorem B149430415 : Blo 1617007 149430415 := bstep (se 1 (by rfl) ⟨112072811, by rfl⟩ : syracuseStep 149430415 = 224145623) B224145623
theorem B18424745 : Blo 1617007 18424745 := bstep (se 2 (by rfl) ⟨6909279, by rfl⟩ : syracuseStep 18424745 = 13818559) B13818559
theorem B20497657 : Blo 1617007 20497657 := bstep (se 2 (by rfl) ⟨7686621, by rfl⟩ : syracuseStep 20497657 = 15373243) B15373243
theorem B2730665 : Blo 1617007 2730665 := bstep (se 2 (by rfl) ⟨1023999, by rfl⟩ : syracuseStep 2730665 = 2047999) B2047999
theorem B1617215 : Blo 1617007 1617215 := bstep (se 1 (by rfl) ⟨1212911, by rfl⟩ : syracuseStep 1617215 = 2425823) B2425823
theorem B17739263 : Blo 1617007 17739263 := bstep (se 1 (by rfl) ⟨13304447, by rfl⟩ : syracuseStep 17739263 = 26608895) B26608895
theorem B8302843 : Blo 1617007 8302843 := bstep (se 1 (by rfl) ⟨6227132, by rfl⟩ : syracuseStep 8302843 = 12454265) B12454265
theorem B12293855 : Blo 1617007 12293855 := bstep (se 1 (by rfl) ⟨9220391, by rfl⟩ : syracuseStep 12293855 = 18440783) B18440783
theorem B22142107 : Blo 1617007 22142107 := bstep (se 1 (by rfl) ⟨16606580, by rfl⟩ : syracuseStep 22142107 = 33213161) B33213161
theorem B27330209 : Blo 1617007 27330209 := bstep (se 2 (by rfl) ⟨10248828, by rfl⟩ : syracuseStep 27330209 = 20497657) B20497657
theorem B1820443 : Blo 1617007 1820443 := bstep (se 1 (by rfl) ⟨1365332, by rfl⟩ : syracuseStep 1820443 = 2730665) B2730665
theorem B199240553 : Blo 1617007 199240553 := bstep (se 2 (by rfl) ⟨74715207, by rfl⟩ : syracuseStep 199240553 = 149430415) B149430415
theorem B12283163 : Blo 1617007 12283163 := bstep (se 1 (by rfl) ⟨9212372, by rfl⟩ : syracuseStep 12283163 = 18424745) B18424745
theorem B8195903 : Blo 1617007 8195903 := bstep (se 1 (by rfl) ⟨6146927, by rfl⟩ : syracuseStep 8195903 = 12293855) B12293855
theorem B44281829 : Blo 1617007 44281829 := bstep (se 4 (by rfl) ⟨4151421, by rfl⟩ : syracuseStep 44281829 = 8302843) B8302843
theorem B11826175 : Blo 1617007 11826175 := bstep (se 1 (by rfl) ⟨8869631, by rfl⟩ : syracuseStep 11826175 = 17739263) B17739263
theorem B29522809 : Blo 1617007 29522809 := bstep (se 2 (by rfl) ⟨11071053, by rfl⟩ : syracuseStep 29522809 = 22142107) B22142107
theorem B18220139 : Blo 1617007 18220139 := bstep (se 1 (by rfl) ⟨13665104, by rfl⟩ : syracuseStep 18220139 = 27330209) B27330209
theorem B39363745 : Blo 1617007 39363745 := bstep (se 2 (by rfl) ⟨14761404, by rfl⟩ : syracuseStep 39363745 = 29522809) B29522809
theorem B132827035 : Blo 1617007 132827035 := bstep (se 1 (by rfl) ⟨99620276, by rfl⟩ : syracuseStep 132827035 = 199240553) B199240553
theorem B2427257 : Blo 1617007 2427257 := bstep (se 2 (by rfl) ⟨910221, by rfl⟩ : syracuseStep 2427257 = 1820443) B1820443
theorem B8188775 : Blo 1617007 8188775 := bstep (se 1 (by rfl) ⟨6141581, by rfl⟩ : syracuseStep 8188775 = 12283163) B12283163
theorem B29521219 : Blo 1617007 29521219 := bstep (se 1 (by rfl) ⟨22140914, by rfl⟩ : syracuseStep 29521219 = 44281829) B44281829
theorem B15768233 : Blo 1617007 15768233 := bstep (se 2 (by rfl) ⟨5913087, by rfl⟩ : syracuseStep 15768233 = 11826175) B11826175
theorem B5463935 : Blo 1617007 5463935 := bstep (se 1 (by rfl) ⟨4097951, by rfl⟩ : syracuseStep 5463935 = 8195903) B8195903
theorem B10512155 : Blo 1617007 10512155 := bstep (se 1 (by rfl) ⟨7884116, by rfl⟩ : syracuseStep 10512155 = 15768233) B15768233
theorem B5459183 : Blo 1617007 5459183 := bstep (se 1 (by rfl) ⟨4094387, by rfl⟩ : syracuseStep 5459183 = 8188775) B8188775
theorem B1618171 : Blo 1617007 1618171 := bstep (se 1 (by rfl) ⟨1213628, by rfl⟩ : syracuseStep 1618171 = 2427257) B2427257
theorem B3642623 : Blo 1617007 3642623 := bstep (se 1 (by rfl) ⟨2731967, by rfl⟩ : syracuseStep 3642623 = 5463935) B5463935
theorem B12146759 : Blo 1617007 12146759 := bstep (se 1 (by rfl) ⟨9110069, by rfl⟩ : syracuseStep 12146759 = 18220139) B18220139
theorem B52484993 : Blo 1617007 52484993 := bstep (se 2 (by rfl) ⟨19681872, by rfl⟩ : syracuseStep 52484993 = 39363745) B39363745
theorem B39361625 : Blo 1617007 39361625 := bstep (se 2 (by rfl) ⟨14760609, by rfl⟩ : syracuseStep 39361625 = 29521219) B29521219
theorem B177102713 : Blo 1617007 177102713 := bstep (se 2 (by rfl) ⟨66413517, by rfl⟩ : syracuseStep 177102713 = 132827035) B132827035
theorem B34989995 : Blo 1617007 34989995 := bstep (se 1 (by rfl) ⟨26242496, by rfl⟩ : syracuseStep 34989995 = 52484993) B52484993
theorem B26241083 : Blo 1617007 26241083 := bstep (se 1 (by rfl) ⟨19680812, by rfl⟩ : syracuseStep 26241083 = 39361625) B39361625
theorem B3639455 : Blo 1617007 3639455 := bstep (se 1 (by rfl) ⟨2729591, by rfl⟩ : syracuseStep 3639455 = 5459183) B5459183
theorem B2428415 : Blo 1617007 2428415 := bstep (se 1 (by rfl) ⟨1821311, by rfl⟩ : syracuseStep 2428415 = 3642623) B3642623
theorem B7008103 : Blo 1617007 7008103 := bstep (se 1 (by rfl) ⟨5256077, by rfl⟩ : syracuseStep 7008103 = 10512155) B10512155
theorem B8097839 : Blo 1617007 8097839 := bstep (se 1 (by rfl) ⟨6073379, by rfl⟩ : syracuseStep 8097839 = 12146759) B12146759
theorem B118068475 : Blo 1617007 118068475 := bstep (se 1 (by rfl) ⟨88551356, by rfl⟩ : syracuseStep 118068475 = 177102713) B177102713
theorem B5398559 : Blo 1617007 5398559 := bstep (se 1 (by rfl) ⟨4048919, by rfl⟩ : syracuseStep 5398559 = 8097839) B8097839
theorem B2426303 : Blo 1617007 2426303 := bstep (se 1 (by rfl) ⟨1819727, by rfl⟩ : syracuseStep 2426303 = 3639455) B3639455
theorem B23326663 : Blo 1617007 23326663 := bstep (se 1 (by rfl) ⟨17494997, by rfl⟩ : syracuseStep 23326663 = 34989995) B34989995
theorem B17494055 : Blo 1617007 17494055 := bstep (se 1 (by rfl) ⟨13120541, by rfl⟩ : syracuseStep 17494055 = 26241083) B26241083
theorem B37376549 : Blo 1617007 37376549 := bstep (se 4 (by rfl) ⟨3504051, by rfl⟩ : syracuseStep 37376549 = 7008103) B7008103
theorem B1618943 : Blo 1617007 1618943 := bstep (se 1 (by rfl) ⟨1214207, by rfl⟩ : syracuseStep 1618943 = 2428415) B2428415
theorem B157424633 : Blo 1617007 157424633 := bstep (se 2 (by rfl) ⟨59034237, by rfl⟩ : syracuseStep 157424633 = 118068475) B118068475
theorem B104949755 : Blo 1617007 104949755 := bstep (se 1 (by rfl) ⟨78712316, by rfl⟩ : syracuseStep 104949755 = 157424633) B157424633
theorem B3599039 : Blo 1617007 3599039 := bstep (se 1 (by rfl) ⟨2699279, by rfl⟩ : syracuseStep 3599039 = 5398559) B5398559
theorem B1617535 : Blo 1617007 1617535 := bstep (se 1 (by rfl) ⟨1213151, by rfl⟩ : syracuseStep 1617535 = 2426303) B2426303
theorem B31102217 : Blo 1617007 31102217 := bstep (se 2 (by rfl) ⟨11663331, by rfl⟩ : syracuseStep 31102217 = 23326663) B23326663
theorem B11662703 : Blo 1617007 11662703 := bstep (se 1 (by rfl) ⟨8747027, by rfl⟩ : syracuseStep 11662703 = 17494055) B17494055
theorem B24917699 : Blo 1617007 24917699 := bstep (se 1 (by rfl) ⟨18688274, by rfl⟩ : syracuseStep 24917699 = 37376549) B37376549
theorem B20734811 : Blo 1617007 20734811 := bstep (se 1 (by rfl) ⟨15551108, by rfl⟩ : syracuseStep 20734811 = 31102217) B31102217
theorem B7775135 : Blo 1617007 7775135 := bstep (se 1 (by rfl) ⟨5831351, by rfl⟩ : syracuseStep 7775135 = 11662703) B11662703
theorem B9597437 : Blo 1617007 9597437 := bstep (se 3 (by rfl) ⟨1799519, by rfl⟩ : syracuseStep 9597437 = 3599039) B3599039
theorem B16611799 : Blo 1617007 16611799 := bstep (se 1 (by rfl) ⟨12458849, by rfl⟩ : syracuseStep 16611799 = 24917699) B24917699
theorem B69966503 : Blo 1617007 69966503 := bstep (se 1 (by rfl) ⟨52474877, by rfl⟩ : syracuseStep 69966503 = 104949755) B104949755
theorem B6398291 : Blo 1617007 6398291 := bstep (se 1 (by rfl) ⟨4798718, by rfl⟩ : syracuseStep 6398291 = 9597437) B9597437
theorem B13823207 : Blo 1617007 13823207 := bstep (se 1 (by rfl) ⟨10367405, by rfl⟩ : syracuseStep 13823207 = 20734811) B20734811
theorem B5183423 : Blo 1617007 5183423 := bstep (se 1 (by rfl) ⟨3887567, by rfl⟩ : syracuseStep 5183423 = 7775135) B7775135
theorem B22149065 : Blo 1617007 22149065 := bstep (se 2 (by rfl) ⟨8305899, by rfl⟩ : syracuseStep 22149065 = 16611799) B16611799
theorem B46644335 : Blo 1617007 46644335 := bstep (se 1 (by rfl) ⟨34983251, by rfl⟩ : syracuseStep 46644335 = 69966503) B69966503
theorem B17062109 : Blo 1617007 17062109 := bstep (se 3 (by rfl) ⟨3199145, by rfl⟩ : syracuseStep 17062109 = 6398291) B6398291
theorem B3455615 : Blo 1617007 3455615 := bstep (se 1 (by rfl) ⟨2591711, by rfl⟩ : syracuseStep 3455615 = 5183423) B5183423
theorem B31096223 : Blo 1617007 31096223 := bstep (se 1 (by rfl) ⟨23322167, by rfl⟩ : syracuseStep 31096223 = 46644335) B46644335
theorem B9215471 : Blo 1617007 9215471 := bstep (se 1 (by rfl) ⟨6911603, by rfl⟩ : syracuseStep 9215471 = 13823207) B13823207
theorem B59064173 : Blo 1617007 59064173 := bstep (se 3 (by rfl) ⟨11074532, by rfl⟩ : syracuseStep 59064173 = 22149065) B22149065
theorem B2303743 : Blo 1617007 2303743 := bstep (se 1 (by rfl) ⟨1727807, by rfl⟩ : syracuseStep 2303743 = 3455615) B3455615
theorem B11374739 : Blo 1617007 11374739 := bstep (se 1 (by rfl) ⟨8531054, by rfl⟩ : syracuseStep 11374739 = 17062109) B17062109
theorem B20730815 : Blo 1617007 20730815 := bstep (se 1 (by rfl) ⟨15548111, by rfl⟩ : syracuseStep 20730815 = 31096223) B31096223
theorem B39376115 : Blo 1617007 39376115 := bstep (se 1 (by rfl) ⟨29532086, by rfl⟩ : syracuseStep 39376115 = 59064173) B59064173
theorem B6143647 : Blo 1617007 6143647 := bstep (se 1 (by rfl) ⟨4607735, by rfl⟩ : syracuseStep 6143647 = 9215471) B9215471
theorem B13820543 : Blo 1617007 13820543 := bstep (se 1 (by rfl) ⟨10365407, by rfl⟩ : syracuseStep 13820543 = 20730815) B20730815
theorem B26250743 : Blo 1617007 26250743 := bstep (se 1 (by rfl) ⟨19688057, by rfl⟩ : syracuseStep 26250743 = 39376115) B39376115
theorem B7583159 : Blo 1617007 7583159 := bstep (se 1 (by rfl) ⟨5687369, by rfl⟩ : syracuseStep 7583159 = 11374739) B11374739
theorem B8191529 : Blo 1617007 8191529 := bstep (se 2 (by rfl) ⟨3071823, by rfl⟩ : syracuseStep 8191529 = 6143647) B6143647
theorem B3071657 : Blo 1617007 3071657 := bstep (se 2 (by rfl) ⟨1151871, by rfl⟩ : syracuseStep 3071657 = 2303743) B2303743
theorem B5055439 : Blo 1617007 5055439 := bstep (se 1 (by rfl) ⟨3791579, by rfl⟩ : syracuseStep 5055439 = 7583159) B7583159
theorem B17500495 : Blo 1617007 17500495 := bstep (se 1 (by rfl) ⟨13125371, by rfl⟩ : syracuseStep 17500495 = 26250743) B26250743
theorem B5461019 : Blo 1617007 5461019 := bstep (se 1 (by rfl) ⟨4095764, by rfl⟩ : syracuseStep 5461019 = 8191529) B8191529
theorem B9213695 : Blo 1617007 9213695 := bstep (se 1 (by rfl) ⟨6910271, by rfl⟩ : syracuseStep 9213695 = 13820543) B13820543
theorem B2047771 : Blo 1617007 2047771 := bstep (se 1 (by rfl) ⟨1535828, by rfl⟩ : syracuseStep 2047771 = 3071657) B3071657
theorem B2730361 : Blo 1617007 2730361 := bstep (se 2 (by rfl) ⟨1023885, by rfl⟩ : syracuseStep 2730361 = 2047771) B2047771
theorem B23333993 : Blo 1617007 23333993 := bstep (se 2 (by rfl) ⟨8750247, by rfl⟩ : syracuseStep 23333993 = 17500495) B17500495
theorem B3640679 : Blo 1617007 3640679 := bstep (se 1 (by rfl) ⟨2730509, by rfl⟩ : syracuseStep 3640679 = 5461019) B5461019
theorem B6142463 : Blo 1617007 6142463 := bstep (se 1 (by rfl) ⟨4606847, by rfl⟩ : syracuseStep 6142463 = 9213695) B9213695
theorem B6740585 : Blo 1617007 6740585 := bstep (se 2 (by rfl) ⟨2527719, by rfl⟩ : syracuseStep 6740585 = 5055439) B5055439
theorem B2427119 : Blo 1617007 2427119 := bstep (se 1 (by rfl) ⟨1820339, by rfl⟩ : syracuseStep 2427119 = 3640679) B3640679
theorem B3640481 : Blo 1617007 3640481 := bstep (se 2 (by rfl) ⟨1365180, by rfl⟩ : syracuseStep 3640481 = 2730361) B2730361
theorem B4493723 : Blo 1617007 4493723 := bstep (se 1 (by rfl) ⟨3370292, by rfl⟩ : syracuseStep 4493723 = 6740585) B6740585
theorem B4094975 : Blo 1617007 4094975 := bstep (se 1 (by rfl) ⟨3071231, by rfl⟩ : syracuseStep 4094975 = 6142463) B6142463
theorem B15555995 : Blo 1617007 15555995 := bstep (se 1 (by rfl) ⟨11666996, by rfl⟩ : syracuseStep 15555995 = 23333993) B23333993
theorem B2729983 : Blo 1617007 2729983 := bstep (se 1 (by rfl) ⟨2047487, by rfl⟩ : syracuseStep 2729983 = 4094975) B4094975
theorem B2426987 : Blo 1617007 2426987 := bstep (se 1 (by rfl) ⟨1820240, by rfl⟩ : syracuseStep 2426987 = 3640481) B3640481
theorem B1618079 : Blo 1617007 1618079 := bstep (se 1 (by rfl) ⟨1213559, by rfl⟩ : syracuseStep 1618079 = 2427119) B2427119
theorem B11983261 : Blo 1617007 11983261 := bstep (se 3 (by rfl) ⟨2246861, by rfl⟩ : syracuseStep 11983261 = 4493723) B4493723
theorem B10370663 : Blo 1617007 10370663 := bstep (se 1 (by rfl) ⟨7777997, by rfl⟩ : syracuseStep 10370663 = 15555995) B15555995
theorem B3639977 : Blo 1617007 3639977 := bstep (se 2 (by rfl) ⟨1364991, by rfl⟩ : syracuseStep 3639977 = 2729983) B2729983
theorem B15977681 : Blo 1617007 15977681 := bstep (se 2 (by rfl) ⟨5991630, by rfl⟩ : syracuseStep 15977681 = 11983261) B11983261
theorem B1617991 : Blo 1617007 1617991 := bstep (se 1 (by rfl) ⟨1213493, by rfl⟩ : syracuseStep 1617991 = 2426987) B2426987
theorem B6913775 : Blo 1617007 6913775 := bstep (se 1 (by rfl) ⟨5185331, by rfl⟩ : syracuseStep 6913775 = 10370663) B10370663
theorem B2426651 : Blo 1617007 2426651 := bstep (se 1 (by rfl) ⟨1819988, by rfl⟩ : syracuseStep 2426651 = 3639977) B3639977
theorem B10651787 : Blo 1617007 10651787 := bstep (se 1 (by rfl) ⟨7988840, by rfl⟩ : syracuseStep 10651787 = 15977681) B15977681
theorem B4609183 : Blo 1617007 4609183 := bstep (se 1 (by rfl) ⟨3456887, by rfl⟩ : syracuseStep 4609183 = 6913775) B6913775
theorem B6145577 : Blo 1617007 6145577 := bstep (se 2 (by rfl) ⟨2304591, by rfl⟩ : syracuseStep 6145577 = 4609183) B4609183
theorem B1617767 : Blo 1617007 1617767 := bstep (se 1 (by rfl) ⟨1213325, by rfl⟩ : syracuseStep 1617767 = 2426651) B2426651
theorem B7101191 : Blo 1617007 7101191 := bstep (se 1 (by rfl) ⟨5325893, by rfl⟩ : syracuseStep 7101191 = 10651787) B10651787
theorem B4097051 : Blo 1617007 4097051 := bstep (se 1 (by rfl) ⟨3072788, by rfl⟩ : syracuseStep 4097051 = 6145577) B6145577
theorem B4734127 : Blo 1617007 4734127 := bstep (se 1 (by rfl) ⟨3550595, by rfl⟩ : syracuseStep 4734127 = 7101191) B7101191
theorem B2731367 : Blo 1617007 2731367 := bstep (se 1 (by rfl) ⟨2048525, by rfl⟩ : syracuseStep 2731367 = 4097051) B4097051
theorem B6312169 : Blo 1617007 6312169 := bstep (se 2 (by rfl) ⟨2367063, by rfl⟩ : syracuseStep 6312169 = 4734127) B4734127
theorem B1820911 : Blo 1617007 1820911 := bstep (se 1 (by rfl) ⟨1365683, by rfl⟩ : syracuseStep 1820911 = 2731367) B2731367
theorem B33664901 : Blo 1617007 33664901 := bstep (se 4 (by rfl) ⟨3156084, by rfl⟩ : syracuseStep 33664901 = 6312169) B6312169
theorem B2427881 : Blo 1617007 2427881 := bstep (se 2 (by rfl) ⟨910455, by rfl⟩ : syracuseStep 2427881 = 1820911) B1820911
theorem B359092277 : Blo 1617007 359092277 := bstep (se 5 (by rfl) ⟨16832450, by rfl⟩ : syracuseStep 359092277 = 33664901) B33664901
theorem B239394851 : Blo 1617007 239394851 := bstep (se 1 (by rfl) ⟨179546138, by rfl⟩ : syracuseStep 239394851 = 359092277) B359092277
theorem B1618587 : Blo 1617007 1618587 := bstep (se 1 (by rfl) ⟨1213940, by rfl⟩ : syracuseStep 1618587 = 2427881) B2427881
theorem B159596567 : Blo 1617007 159596567 := bstep (se 1 (by rfl) ⟨119697425, by rfl⟩ : syracuseStep 159596567 = 239394851) B239394851
theorem B106397711 : Blo 1617007 106397711 := bstep (se 1 (by rfl) ⟨79798283, by rfl⟩ : syracuseStep 106397711 = 159596567) B159596567
theorem B70931807 : Blo 1617007 70931807 := bstep (se 1 (by rfl) ⟨53198855, by rfl⟩ : syracuseStep 70931807 = 106397711) B106397711
theorem B47287871 : Blo 1617007 47287871 := bstep (se 1 (by rfl) ⟨35465903, by rfl⟩ : syracuseStep 47287871 = 70931807) B70931807
theorem B31525247 : Blo 1617007 31525247 := bstep (se 1 (by rfl) ⟨23643935, by rfl⟩ : syracuseStep 31525247 = 47287871) B47287871
theorem B21016831 : Blo 1617007 21016831 := bstep (se 1 (by rfl) ⟨15762623, by rfl⟩ : syracuseStep 21016831 = 31525247) B31525247
theorem B28022441 : Blo 1617007 28022441 := bstep (se 2 (by rfl) ⟨10508415, by rfl⟩ : syracuseStep 28022441 = 21016831) B21016831
theorem B74726509 : Blo 1617007 74726509 := bstep (se 3 (by rfl) ⟨14011220, by rfl⟩ : syracuseStep 74726509 = 28022441) B28022441
theorem B99635345 : Blo 1617007 99635345 := bstep (se 2 (by rfl) ⟨37363254, by rfl⟩ : syracuseStep 99635345 = 74726509) B74726509
theorem B66423563 : Blo 1617007 66423563 := bstep (se 1 (by rfl) ⟨49817672, by rfl⟩ : syracuseStep 66423563 = 99635345) B99635345
theorem B44282375 : Blo 1617007 44282375 := bstep (se 1 (by rfl) ⟨33211781, by rfl⟩ : syracuseStep 44282375 = 66423563) B66423563
theorem B29521583 : Blo 1617007 29521583 := bstep (se 1 (by rfl) ⟨22141187, by rfl⟩ : syracuseStep 29521583 = 44282375) B44282375
theorem B19681055 : Blo 1617007 19681055 := bstep (se 1 (by rfl) ⟨14760791, by rfl⟩ : syracuseStep 19681055 = 29521583) B29521583
theorem B13120703 : Blo 1617007 13120703 := bstep (se 1 (by rfl) ⟨9840527, by rfl⟩ : syracuseStep 13120703 = 19681055) B19681055
theorem B8747135 : Blo 1617007 8747135 := bstep (se 1 (by rfl) ⟨6560351, by rfl⟩ : syracuseStep 8747135 = 13120703) B13120703
theorem B5831423 : Blo 1617007 5831423 := bstep (se 1 (by rfl) ⟨4373567, by rfl⟩ : syracuseStep 5831423 = 8747135) B8747135
theorem B3887615 : Blo 1617007 3887615 := bstep (se 1 (by rfl) ⟨2915711, by rfl⟩ : syracuseStep 3887615 = 5831423) B5831423
theorem B10366973 : Blo 1617007 10366973 := bstep (se 3 (by rfl) ⟨1943807, by rfl⟩ : syracuseStep 10366973 = 3887615) B3887615
theorem B6911315 : Blo 1617007 6911315 := bstep (se 1 (by rfl) ⟨5183486, by rfl⟩ : syracuseStep 6911315 = 10366973) B10366973
theorem B4607543 : Blo 1617007 4607543 := bstep (se 1 (by rfl) ⟨3455657, by rfl⟩ : syracuseStep 4607543 = 6911315) B6911315
theorem B3071695 : Blo 1617007 3071695 := bstep (se 1 (by rfl) ⟨2303771, by rfl⟩ : syracuseStep 3071695 = 4607543) B4607543
theorem B4095593 : Blo 1617007 4095593 := bstep (se 2 (by rfl) ⟨1535847, by rfl⟩ : syracuseStep 4095593 = 3071695) B3071695
theorem B2730395 : Blo 1617007 2730395 := bstep (se 1 (by rfl) ⟨2047796, by rfl⟩ : syracuseStep 2730395 = 4095593) B4095593
theorem B1820263 : Blo 1617007 1820263 := bstep (se 1 (by rfl) ⟨1365197, by rfl⟩ : syracuseStep 1820263 = 2730395) B2730395
theorem B2427017 : Blo 1617007 2427017 := bstep (se 2 (by rfl) ⟨910131, by rfl⟩ : syracuseStep 2427017 = 1820263) B1820263
theorem B1618011 : Blo 1617007 1618011 := bstep (se 1 (by rfl) ⟨1213508, by rfl⟩ : syracuseStep 1618011 = 2427017) B2427017

theorem C0 (j : ℕ) (h1 : 404251 ≤ j) (h2 : j ≤ 404751) : Blo 1617007 (4 * j + 3) := by
  interval_cases j
  · exact B1617007
  · exact B1617011
  · exact B1617015
  · exact B1617019
  · exact B1617023
  · exact B1617027
  · exact B1617031
  · exact B1617035
  · exact B1617039
  · exact B1617043
  · exact B1617047
  · exact B1617051
  · exact B1617055
  · exact B1617059
  · exact B1617063
  · exact B1617067
  · exact B1617071
  · exact B1617075
  · exact B1617079
  · exact B1617083
  · exact B1617087
  · exact B1617091
  · exact B1617095
  · exact B1617099
  · exact B1617103
  · exact B1617107
  · exact B1617111
  · exact B1617115
  · exact B1617119
  · exact B1617123
  · exact B1617127
  · exact B1617131
  · exact B1617135
  · exact B1617139
  · exact B1617143
  · exact B1617147
  · exact B1617151
  · exact B1617155
  · exact B1617159
  · exact B1617163
  · exact B1617167
  · exact B1617171
  · exact B1617175
  · exact B1617179
  · exact B1617183
  · exact B1617187
  · exact B1617191
  · exact B1617195
  · exact B1617199
  · exact B1617203
  · exact B1617207
  · exact B1617211
  · exact B1617215
  · exact B1617219
  · exact B1617223
  · exact B1617227
  · exact B1617231
  · exact B1617235
  · exact B1617239
  · exact B1617243
  · exact B1617247
  · exact B1617251
  · exact B1617255
  · exact B1617259
  · exact B1617263
  · exact B1617267
  · exact B1617271
  · exact B1617275
  · exact B1617279
  · exact B1617283
  · exact B1617287
  · exact B1617291
  · exact B1617295
  · exact B1617299
  · exact B1617303
  · exact B1617307
  · exact B1617311
  · exact B1617315
  · exact B1617319
  · exact B1617323
  · exact B1617327
  · exact B1617331
  · exact B1617335
  · exact B1617339
  · exact B1617343
  · exact B1617347
  · exact B1617351
  · exact B1617355
  · exact B1617359
  · exact B1617363
  · exact B1617367
  · exact B1617371
  · exact B1617375
  · exact B1617379
  · exact B1617383
  · exact B1617387
  · exact B1617391
  · exact B1617395
  · exact B1617399
  · exact B1617403
  · exact B1617407
  · exact B1617411
  · exact B1617415
  · exact B1617419
  · exact B1617423
  · exact B1617427
  · exact B1617431
  · exact B1617435
  · exact B1617439
  · exact B1617443
  · exact B1617447
  · exact B1617451
  · exact B1617455
  · exact B1617459
  · exact B1617463
  · exact B1617467
  · exact B1617471
  · exact B1617475
  · exact B1617479
  · exact B1617483
  · exact B1617487
  · exact B1617491
  · exact B1617495
  · exact B1617499
  · exact B1617503
  · exact B1617507
  · exact B1617511
  · exact B1617515
  · exact B1617519
  · exact B1617523
  · exact B1617527
  · exact B1617531
  · exact B1617535
  · exact B1617539
  · exact B1617543
  · exact B1617547
  · exact B1617551
  · exact B1617555
  · exact B1617559
  · exact B1617563
  · exact B1617567
  · exact B1617571
  · exact B1617575
  · exact B1617579
  · exact B1617583
  · exact B1617587
  · exact B1617591
  · exact B1617595
  · exact B1617599
  · exact B1617603
  · exact B1617607
  · exact B1617611
  · exact B1617615
  · exact B1617619
  · exact B1617623
  · exact B1617627
  · exact B1617631
  · exact B1617635
  · exact B1617639
  · exact B1617643
  · exact B1617647
  · exact B1617651
  · exact B1617655
  · exact B1617659
  · exact B1617663
  · exact B1617667
  · exact B1617671
  · exact B1617675
  · exact B1617679
  · exact B1617683
  · exact B1617687
  · exact B1617691
  · exact B1617695
  · exact B1617699
  · exact B1617703
  · exact B1617707
  · exact B1617711
  · exact B1617715
  · exact B1617719
  · exact B1617723
  · exact B1617727
  · exact B1617731
  · exact B1617735
  · exact B1617739
  · exact B1617743
  · exact B1617747
  · exact B1617751
  · exact B1617755
  · exact B1617759
  · exact B1617763
  · exact B1617767
  · exact B1617771
  · exact B1617775
  · exact B1617779
  · exact B1617783
  · exact B1617787
  · exact B1617791
  · exact B1617795
  · exact B1617799
  · exact B1617803
  · exact B1617807
  · exact B1617811
  · exact B1617815
  · exact B1617819
  · exact B1617823
  · exact B1617827
  · exact B1617831
  · exact B1617835
  · exact B1617839
  · exact B1617843
  · exact B1617847
  · exact B1617851
  · exact B1617855
  · exact B1617859
  · exact B1617863
  · exact B1617867
  · exact B1617871
  · exact B1617875
  · exact B1617879
  · exact B1617883
  · exact B1617887
  · exact B1617891
  · exact B1617895
  · exact B1617899
  · exact B1617903
  · exact B1617907
  · exact B1617911
  · exact B1617915
  · exact B1617919
  · exact B1617923
  · exact B1617927
  · exact B1617931
  · exact B1617935
  · exact B1617939
  · exact B1617943
  · exact B1617947
  · exact B1617951
  · exact B1617955
  · exact B1617959
  · exact B1617963
  · exact B1617967
  · exact B1617971
  · exact B1617975
  · exact B1617979
  · exact B1617983
  · exact B1617987
  · exact B1617991
  · exact B1617995
  · exact B1617999
  · exact B1618003
  · exact B1618007
  · exact B1618011
  · exact B1618015
  · exact B1618019
  · exact B1618023
  · exact B1618027
  · exact B1618031
  · exact B1618035
  · exact B1618039
  · exact B1618043
  · exact B1618047
  · exact B1618051
  · exact B1618055
  · exact B1618059
  · exact B1618063
  · exact B1618067
  · exact B1618071
  · exact B1618075
  · exact B1618079
  · exact B1618083
  · exact B1618087
  · exact B1618091
  · exact B1618095
  · exact B1618099
  · exact B1618103
  · exact B1618107
  · exact B1618111
  · exact B1618115
  · exact B1618119
  · exact B1618123
  · exact B1618127
  · exact B1618131
  · exact B1618135
  · exact B1618139
  · exact B1618143
  · exact B1618147
  · exact B1618151
  · exact B1618155
  · exact B1618159
  · exact B1618163
  · exact B1618167
  · exact B1618171
  · exact B1618175
  · exact B1618179
  · exact B1618183
  · exact B1618187
  · exact B1618191
  · exact B1618195
  · exact B1618199
  · exact B1618203
  · exact B1618207
  · exact B1618211
  · exact B1618215
  · exact B1618219
  · exact B1618223
  · exact B1618227
  · exact B1618231
  · exact B1618235
  · exact B1618239
  · exact B1618243
  · exact B1618247
  · exact B1618251
  · exact B1618255
  · exact B1618259
  · exact B1618263
  · exact B1618267
  · exact B1618271
  · exact B1618275
  · exact B1618279
  · exact B1618283
  · exact B1618287
  · exact B1618291
  · exact B1618295
  · exact B1618299
  · exact B1618303
  · exact B1618307
  · exact B1618311
  · exact B1618315
  · exact B1618319
  · exact B1618323
  · exact B1618327
  · exact B1618331
  · exact B1618335
  · exact B1618339
  · exact B1618343
  · exact B1618347
  · exact B1618351
  · exact B1618355
  · exact B1618359
  · exact B1618363
  · exact B1618367
  · exact B1618371
  · exact B1618375
  · exact B1618379
  · exact B1618383
  · exact B1618387
  · exact B1618391
  · exact B1618395
  · exact B1618399
  · exact B1618403
  · exact B1618407
  · exact B1618411
  · exact B1618415
  · exact B1618419
  · exact B1618423
  · exact B1618427
  · exact B1618431
  · exact B1618435
  · exact B1618439
  · exact B1618443
  · exact B1618447
  · exact B1618451
  · exact B1618455
  · exact B1618459
  · exact B1618463
  · exact B1618467
  · exact B1618471
  · exact B1618475
  · exact B1618479
  · exact B1618483
  · exact B1618487
  · exact B1618491
  · exact B1618495
  · exact B1618499
  · exact B1618503
  · exact B1618507
  · exact B1618511
  · exact B1618515
  · exact B1618519
  · exact B1618523
  · exact B1618527
  · exact B1618531
  · exact B1618535
  · exact B1618539
  · exact B1618543
  · exact B1618547
  · exact B1618551
  · exact B1618555
  · exact B1618559
  · exact B1618563
  · exact B1618567
  · exact B1618571
  · exact B1618575
  · exact B1618579
  · exact B1618583
  · exact B1618587
  · exact B1618591
  · exact B1618595
  · exact B1618599
  · exact B1618603
  · exact B1618607
  · exact B1618611
  · exact B1618615
  · exact B1618619
  · exact B1618623
  · exact B1618627
  · exact B1618631
  · exact B1618635
  · exact B1618639
  · exact B1618643
  · exact B1618647
  · exact B1618651
  · exact B1618655
  · exact B1618659
  · exact B1618663
  · exact B1618667
  · exact B1618671
  · exact B1618675
  · exact B1618679
  · exact B1618683
  · exact B1618687
  · exact B1618691
  · exact B1618695
  · exact B1618699
  · exact B1618703
  · exact B1618707
  · exact B1618711
  · exact B1618715
  · exact B1618719
  · exact B1618723
  · exact B1618727
  · exact B1618731
  · exact B1618735
  · exact B1618739
  · exact B1618743
  · exact B1618747
  · exact B1618751
  · exact B1618755
  · exact B1618759
  · exact B1618763
  · exact B1618767
  · exact B1618771
  · exact B1618775
  · exact B1618779
  · exact B1618783
  · exact B1618787
  · exact B1618791
  · exact B1618795
  · exact B1618799
  · exact B1618803
  · exact B1618807
  · exact B1618811
  · exact B1618815
  · exact B1618819
  · exact B1618823
  · exact B1618827
  · exact B1618831
  · exact B1618835
  · exact B1618839
  · exact B1618843
  · exact B1618847
  · exact B1618851
  · exact B1618855
  · exact B1618859
  · exact B1618863
  · exact B1618867
  · exact B1618871
  · exact B1618875
  · exact B1618879
  · exact B1618883
  · exact B1618887
  · exact B1618891
  · exact B1618895
  · exact B1618899
  · exact B1618903
  · exact B1618907
  · exact B1618911
  · exact B1618915
  · exact B1618919
  · exact B1618923
  · exact B1618927
  · exact B1618931
  · exact B1618935
  · exact B1618939
  · exact B1618943
  · exact B1618947
  · exact B1618951
  · exact B1618955
  · exact B1618959
  · exact B1618963
  · exact B1618967
  · exact B1618971
  · exact B1618975
  · exact B1618979
  · exact B1618983
  · exact B1618987
  · exact B1618991
  · exact B1618995
  · exact B1618999
  · exact B1619003
  · exact B1619007

theorem solution (m : ℕ) (hlo : 1617007 ≤ m) (hhi : m ≤ 1619007) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 404251 ≤ j := by omega
    have hj2 : j ≤ 404751 := by omega
    have hb : Blo 1617007 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
