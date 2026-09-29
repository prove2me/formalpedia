-- Prove2me | solution 1 for syracuse_descends_range_750330_754330
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:16.79715+00:00
-- url     : https://prove2.me/submissions/e21f52c4-aeac-42df-934b-4891ae76c16d

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


theorem B1146893 : Blo 750330 1146893 := bbase (se 3 (by rfl) ⟨215042, by rfl⟩ : syracuseStep 1146893 = 430085) (by norm_num)
theorem B950393 : Blo 750330 950393 := bbase (se 2 (by rfl) ⟨356397, by rfl⟩ : syracuseStep 950393 = 712795) (by norm_num)
theorem B1900685 : Blo 750330 1900685 := bbase (se 3 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 1900685 = 712757) (by norm_num)
theorem B950449 : Blo 750330 950449 := bbase (se 2 (by rfl) ⟨356418, by rfl⟩ : syracuseStep 950449 = 712837) (by norm_num)
theorem B2850997 : Blo 750330 2850997 := bbase (se 5 (by rfl) ⟨133640, by rfl⟩ : syracuseStep 2850997 = 267281) (by norm_num)
theorem B950545 : Blo 750330 950545 := bbase (se 2 (by rfl) ⟨356454, by rfl⟩ : syracuseStep 950545 = 712909) (by norm_num)
theorem B4882837 : Blo 750330 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B950717 : Blo 750330 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B2851301 : Blo 750330 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B1901029 : Blo 750330 1901029 := bbase (se 4 (by rfl) ⟨178221, by rfl⟩ : syracuseStep 1901029 = 356443) (by norm_num)
theorem B950773 : Blo 750330 950773 := bbase (se 5 (by rfl) ⟨44567, by rfl⟩ : syracuseStep 950773 = 89135) (by norm_num)
theorem B3801653 : Blo 750330 3801653 := bbase (se 5 (by rfl) ⟨178202, by rfl⟩ : syracuseStep 3801653 = 356405) (by norm_num)
theorem B1901141 : Blo 750330 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B950869 : Blo 750330 950869 := bbase (se 8 (by rfl) ⟨5571, by rfl⟩ : syracuseStep 950869 = 11143) (by norm_num)
theorem B1606301 : Blo 750330 1606301 := bbase (se 3 (by rfl) ⟨301181, by rfl⟩ : syracuseStep 1606301 = 602363) (by norm_num)
theorem B951041 : Blo 750330 951041 := bbase (se 2 (by rfl) ⟨356640, by rfl⟩ : syracuseStep 951041 = 713281) (by norm_num)
theorem B1901333 : Blo 750330 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B951097 : Blo 750330 951097 := bbase (se 2 (by rfl) ⟨356661, by rfl⟩ : syracuseStep 951097 = 713323) (by norm_num)
theorem B1606549 : Blo 750330 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B951193 : Blo 750330 951193 := bbase (se 2 (by rfl) ⟨356697, by rfl⟩ : syracuseStep 951193 = 713395) (by norm_num)
theorem B3212293 : Blo 750330 3212293 := bbase (se 4 (by rfl) ⟨301152, by rfl⟩ : syracuseStep 3212293 = 602305) (by norm_num)
theorem B951365 : Blo 750330 951365 := bbase (se 4 (by rfl) ⟨89190, by rfl⟩ : syracuseStep 951365 = 178381) (by norm_num)
theorem B1901677 : Blo 750330 1901677 := bbase (se 3 (by rfl) ⟨356564, by rfl⟩ : syracuseStep 1901677 = 713129) (by norm_num)
theorem B951421 : Blo 750330 951421 := bbase (se 3 (by rfl) ⟨178391, by rfl⟩ : syracuseStep 951421 = 356783) (by norm_num)
theorem B1901789 : Blo 750330 1901789 := bbase (se 3 (by rfl) ⟨356585, by rfl⟩ : syracuseStep 1901789 = 713171) (by norm_num)
theorem B951517 : Blo 750330 951517 := bbase (se 3 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 951517 = 356819) (by norm_num)
theorem B951689 : Blo 750330 951689 := bbase (se 2 (by rfl) ⟨356883, by rfl⟩ : syracuseStep 951689 = 713767) (by norm_num)
theorem B1607053 : Blo 750330 1607053 := bbase (se 3 (by rfl) ⟨301322, by rfl⟩ : syracuseStep 1607053 = 602645) (by norm_num)
theorem B1901981 : Blo 750330 1901981 := bbase (se 3 (by rfl) ⟨356621, by rfl⟩ : syracuseStep 1901981 = 713243) (by norm_num)
theorem B951745 : Blo 750330 951745 := bbase (se 2 (by rfl) ⟨356904, by rfl⟩ : syracuseStep 951745 = 713809) (by norm_num)
theorem B1803725 : Blo 750330 1803725 := bbase (se 3 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 1803725 = 676397) (by norm_num)
theorem B951841 : Blo 750330 951841 := bbase (se 2 (by rfl) ⟨356940, by rfl⟩ : syracuseStep 951841 = 713881) (by norm_num)
theorem B1803917 : Blo 750330 1803917 := bbase (se 3 (by rfl) ⟨338234, by rfl⟩ : syracuseStep 1803917 = 676469) (by norm_num)
theorem B3049157 : Blo 750330 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B952013 : Blo 750330 952013 := bbase (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) (by norm_num)
theorem B1902325 : Blo 750330 1902325 := bbase (se 5 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 1902325 = 178343) (by norm_num)
theorem B952069 : Blo 750330 952069 := bbase (se 4 (by rfl) ⟨89256, by rfl⟩ : syracuseStep 952069 = 178513) (by norm_num)
theorem B3802949 : Blo 750330 3802949 := bbase (se 4 (by rfl) ⟨356526, by rfl⟩ : syracuseStep 3802949 = 713053) (by norm_num)
theorem B1902437 : Blo 750330 1902437 := bbase (se 4 (by rfl) ⟨178353, by rfl⟩ : syracuseStep 1902437 = 356707) (by norm_num)
theorem B952165 : Blo 750330 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B3475349 : Blo 750330 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B952337 : Blo 750330 952337 := bbase (se 2 (by rfl) ⟨357126, by rfl⟩ : syracuseStep 952337 = 714253) (by norm_num)
theorem B1902629 : Blo 750330 1902629 := bbase (se 4 (by rfl) ⟨178371, by rfl⟩ : syracuseStep 1902629 = 356743) (by norm_num)
theorem B1443901 : Blo 750330 1443901 := bbase (se 3 (by rfl) ⟨270731, by rfl⟩ : syracuseStep 1443901 = 541463) (by norm_num)
theorem B952393 : Blo 750330 952393 := bbase (se 2 (by rfl) ⟨357147, by rfl⟩ : syracuseStep 952393 = 714295) (by norm_num)
theorem B952489 : Blo 750330 952489 := bbase (se 2 (by rfl) ⟨357183, by rfl⟩ : syracuseStep 952489 = 714367) (by norm_num)
theorem B1018045 : Blo 750330 1018045 := bbase (se 3 (by rfl) ⟨190883, by rfl⟩ : syracuseStep 1018045 = 381767) (by norm_num)
theorem B1607941 : Blo 750330 1607941 := bbase (se 4 (by rfl) ⟨150744, by rfl⟩ : syracuseStep 1607941 = 301489) (by norm_num)
theorem B952661 : Blo 750330 952661 := bbase (se 10 (by rfl) ⟨1395, by rfl⟩ : syracuseStep 952661 = 2791) (by norm_num)
theorem B1902973 : Blo 750330 1902973 := bbase (se 3 (by rfl) ⟨356807, by rfl⟩ : syracuseStep 1902973 = 713615) (by norm_num)
theorem B1804685 : Blo 750330 1804685 := bbase (se 3 (by rfl) ⟨338378, by rfl⟩ : syracuseStep 1804685 = 676757) (by norm_num)
theorem B952717 : Blo 750330 952717 := bbase (se 3 (by rfl) ⟨178634, by rfl⟩ : syracuseStep 952717 = 357269) (by norm_num)
theorem B1903085 : Blo 750330 1903085 := bbase (se 3 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 1903085 = 713657) (by norm_num)
theorem B952813 : Blo 750330 952813 := bbase (se 3 (by rfl) ⟨178652, by rfl⟩ : syracuseStep 952813 = 357305) (by norm_num)
theorem B5704181 : Blo 750330 5704181 := bbase (se 5 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 5704181 = 534767) (by norm_num)
theorem B2853413 : Blo 750330 2853413 := bbase (se 4 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 2853413 = 535015) (by norm_num)
theorem B952985 : Blo 750330 952985 := bbase (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) (by norm_num)
theorem B1903277 : Blo 750330 1903277 := bbase (se 3 (by rfl) ⟨356864, by rfl⟩ : syracuseStep 1903277 = 713729) (by norm_num)
theorem B953041 : Blo 750330 953041 := bbase (se 2 (by rfl) ⟨357390, by rfl⟩ : syracuseStep 953041 = 714781) (by norm_num)
theorem B1608437 : Blo 750330 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B1018661 : Blo 750330 1018661 := bbase (se 4 (by rfl) ⟨95499, by rfl⟩ : syracuseStep 1018661 = 190999) (by norm_num)
theorem B953137 : Blo 750330 953137 := bbase (se 2 (by rfl) ⟨357426, by rfl⟩ : syracuseStep 953137 = 714853) (by norm_num)
theorem B2853701 : Blo 750330 2853701 := bbase (se 4 (by rfl) ⟨267534, by rfl⟩ : syracuseStep 2853701 = 535069) (by norm_num)
theorem B3050405 : Blo 750330 3050405 := bbase (se 4 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 3050405 = 571951) (by norm_num)
theorem B953309 : Blo 750330 953309 := bbase (se 3 (by rfl) ⟨178745, by rfl⟩ : syracuseStep 953309 = 357491) (by norm_num)
theorem B3607525 : Blo 750330 3607525 := bbase (se 4 (by rfl) ⟨338205, by rfl⟩ : syracuseStep 3607525 = 676411) (by norm_num)
theorem B1903621 : Blo 750330 1903621 := bbase (se 4 (by rfl) ⟨178464, by rfl⟩ : syracuseStep 1903621 = 356929) (by norm_num)
theorem B953365 : Blo 750330 953365 := bbase (se 6 (by rfl) ⟨22344, by rfl⟩ : syracuseStep 953365 = 44689) (by norm_num)
theorem B3804245 : Blo 750330 3804245 := bbase (se 8 (by rfl) ⟨22290, by rfl⟩ : syracuseStep 3804245 = 44581) (by norm_num)
theorem B3050597 : Blo 750330 3050597 := bbase (se 4 (by rfl) ⟨285993, by rfl⟩ : syracuseStep 3050597 = 571987) (by norm_num)
theorem B1444981 : Blo 750330 1444981 := bbase (se 5 (by rfl) ⟨67733, by rfl⟩ : syracuseStep 1444981 = 135467) (by norm_num)
theorem B1903733 : Blo 750330 1903733 := bbase (se 5 (by rfl) ⟨89237, by rfl⟩ : syracuseStep 1903733 = 178475) (by norm_num)
theorem B953461 : Blo 750330 953461 := bbase (se 5 (by rfl) ⟨44693, by rfl⟩ : syracuseStep 953461 = 89387) (by norm_num)
theorem B4295861 : Blo 750330 4295861 := bbase (se 5 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 4295861 = 402737) (by norm_num)
theorem B953633 : Blo 750330 953633 := bbase (se 2 (by rfl) ⟨357612, by rfl⟩ : syracuseStep 953633 = 715225) (by norm_num)
theorem B1903925 : Blo 750330 1903925 := bbase (se 5 (by rfl) ⟨89246, by rfl⟩ : syracuseStep 1903925 = 178493) (by norm_num)
theorem B953689 : Blo 750330 953689 := bbase (se 2 (by rfl) ⟨357633, by rfl⟩ : syracuseStep 953689 = 715267) (by norm_num)
theorem B1019245 : Blo 750330 1019245 := bbase (se 3 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 1019245 = 382217) (by norm_num)
theorem B953785 : Blo 750330 953785 := bbase (se 2 (by rfl) ⟨357669, by rfl⟩ : syracuseStep 953785 = 715339) (by norm_num)
theorem B12881429 : Blo 750330 12881429 := bbase (se 6 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 12881429 = 603817) (by norm_num)
theorem B1019413 : Blo 750330 1019413 := bbase (se 6 (by rfl) ⟨23892, by rfl⟩ : syracuseStep 1019413 = 47785) (by norm_num)
theorem B953957 : Blo 750330 953957 := bbase (se 4 (by rfl) ⟨89433, by rfl⟩ : syracuseStep 953957 = 178867) (by norm_num)
theorem B1609325 : Blo 750330 1609325 := bbase (se 3 (by rfl) ⟨301748, by rfl⟩ : syracuseStep 1609325 = 603497) (by norm_num)
theorem B1904269 : Blo 750330 1904269 := bbase (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) (by norm_num)
theorem B954013 : Blo 750330 954013 := bbase (se 3 (by rfl) ⟨178877, by rfl⟩ : syracuseStep 954013 = 357755) (by norm_num)
theorem B2035397 : Blo 750330 2035397 := bbase (se 4 (by rfl) ⟨190818, by rfl⟩ : syracuseStep 2035397 = 381637) (by norm_num)
theorem B1609445 : Blo 750330 1609445 := bbase (se 4 (by rfl) ⟨150885, by rfl⟩ : syracuseStep 1609445 = 301771) (by norm_num)
theorem B1904381 : Blo 750330 1904381 := bbase (se 3 (by rfl) ⟨357071, by rfl⟩ : syracuseStep 1904381 = 714143) (by norm_num)
theorem B954109 : Blo 750330 954109 := bbase (se 3 (by rfl) ⟨178895, by rfl⟩ : syracuseStep 954109 = 357791) (by norm_num)
theorem B8589077 : Blo 750330 8589077 := bbase (se 6 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 8589077 = 402613) (by norm_num)
theorem B954281 : Blo 750330 954281 := bbase (se 2 (by rfl) ⟨357855, by rfl⟩ : syracuseStep 954281 = 715711) (by norm_num)
theorem B3215285 : Blo 750330 3215285 := bbase (se 5 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 3215285 = 301433) (by norm_num)
theorem B1904573 : Blo 750330 1904573 := bbase (se 3 (by rfl) ⟨357107, by rfl⟩ : syracuseStep 1904573 = 714215) (by norm_num)
theorem B954337 : Blo 750330 954337 := bbase (se 2 (by rfl) ⟨357876, by rfl⟩ : syracuseStep 954337 = 715753) (by norm_num)
theorem B2854885 : Blo 750330 2854885 := bbase (se 4 (by rfl) ⟨267645, by rfl⟩ : syracuseStep 2854885 = 535291) (by norm_num)
theorem B954433 : Blo 750330 954433 := bbase (se 2 (by rfl) ⟨357912, by rfl⟩ : syracuseStep 954433 = 715825) (by norm_num)
theorem B13176917 : Blo 750330 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B7213205 : Blo 750330 7213205 := bbase (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) (by norm_num)
theorem B6426773 : Blo 750330 6426773 := bbase (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) (by norm_num)
theorem B954605 : Blo 750330 954605 := bbase (se 3 (by rfl) ⟨178988, by rfl⟩ : syracuseStep 954605 = 357977) (by norm_num)
theorem B2855189 : Blo 750330 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B1904917 : Blo 750330 1904917 := bbase (se 6 (by rfl) ⟨44646, by rfl⟩ : syracuseStep 1904917 = 89293) (by norm_num)
theorem B954661 : Blo 750330 954661 := bbase (se 4 (by rfl) ⟨89499, by rfl⟩ : syracuseStep 954661 = 178999) (by norm_num)
theorem B1610077 : Blo 750330 1610077 := bbase (se 3 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 1610077 = 603779) (by norm_num)
theorem B3805541 : Blo 750330 3805541 := bbase (se 4 (by rfl) ⟨356769, by rfl⟩ : syracuseStep 3805541 = 713539) (by norm_num)
theorem B1905029 : Blo 750330 1905029 := bbase (se 4 (by rfl) ⟨178596, by rfl⟩ : syracuseStep 1905029 = 357193) (by norm_num)
theorem B1806781 : Blo 750330 1806781 := bbase (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) (by norm_num)
theorem B1905221 : Blo 750330 1905221 := bbase (se 4 (by rfl) ⟨178614, by rfl⟩ : syracuseStep 1905221 = 357229) (by norm_num)
theorem B7246421 : Blo 750330 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B1905565 : Blo 750330 1905565 := bbase (se 3 (by rfl) ⟨357293, by rfl⟩ : syracuseStep 1905565 = 714587) (by norm_num)
theorem B3216293 : Blo 750330 3216293 := bbase (se 4 (by rfl) ⟨301527, by rfl⟩ : syracuseStep 3216293 = 603055) (by norm_num)
theorem B1741805 : Blo 750330 1741805 := bbase (se 3 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 1741805 = 653177) (by norm_num)
theorem B1905677 : Blo 750330 1905677 := bbase (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) (by norm_num)
theorem B1807397 : Blo 750330 1807397 := bbase (se 4 (by rfl) ⟨169443, by rfl⟩ : syracuseStep 1807397 = 338887) (by norm_num)
theorem B1807453 : Blo 750330 1807453 := bbase (se 3 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 1807453 = 677795) (by norm_num)
theorem B857233 : Blo 750330 857233 := bbase (se 2 (by rfl) ⟨321462, by rfl⟩ : syracuseStep 857233 = 642925) (by norm_num)
theorem B2036933 : Blo 750330 2036933 := bbase (se 4 (by rfl) ⟨190962, by rfl⟩ : syracuseStep 2036933 = 381925) (by norm_num)
theorem B1905869 : Blo 750330 1905869 := bbase (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) (by norm_num)
theorem B1610965 : Blo 750330 1610965 := bbase (se 7 (by rfl) ⟨18878, by rfl⟩ : syracuseStep 1610965 = 37757) (by norm_num)
theorem B4822517 : Blo 750330 4822517 := bbase (se 5 (by rfl) ⟨226055, by rfl⟩ : syracuseStep 4822517 = 452111) (by norm_num)
theorem B1447445 : Blo 750330 1447445 := bbase (se 6 (by rfl) ⟨33924, by rfl⟩ : syracuseStep 1447445 = 67849) (by norm_num)
theorem B1906213 : Blo 750330 1906213 := bbase (se 4 (by rfl) ⟨178707, by rfl⟩ : syracuseStep 1906213 = 357415) (by norm_num)
theorem B3806837 : Blo 750330 3806837 := bbase (se 5 (by rfl) ⟨178445, by rfl⟩ : syracuseStep 3806837 = 356891) (by norm_num)
theorem B1906325 : Blo 750330 1906325 := bbase (se 6 (by rfl) ⟨44679, by rfl⟩ : syracuseStep 1906325 = 89359) (by norm_num)
theorem B1119949 : Blo 750330 1119949 := bbase (se 3 (by rfl) ⟨209990, by rfl⟩ : syracuseStep 1119949 = 419981) (by norm_num)
theorem B857881 : Blo 750330 857881 := bbase (se 2 (by rfl) ⟨321705, by rfl⟩ : syracuseStep 857881 = 643411) (by norm_num)
theorem B1906517 : Blo 750330 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B1218461 : Blo 750330 1218461 := bbase (se 3 (by rfl) ⟨228461, by rfl⟩ : syracuseStep 1218461 = 456923) (by norm_num)
theorem B1808453 : Blo 750330 1808453 := bbase (se 4 (by rfl) ⟨169542, by rfl⟩ : syracuseStep 1808453 = 339085) (by norm_num)
theorem B1906861 : Blo 750330 1906861 := bbase (se 3 (by rfl) ⟨357536, by rfl⟩ : syracuseStep 1906861 = 715073) (by norm_num)
theorem B1906973 : Blo 750330 1906973 := bbase (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) (by norm_num)
theorem B2857301 : Blo 750330 2857301 := bbase (se 10 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 2857301 = 8371) (by norm_num)
theorem B8690005 : Blo 750330 8690005 := bbase (se 10 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 8690005 = 25459) (by norm_num)
theorem B1907165 : Blo 750330 1907165 := bbase (se 3 (by rfl) ⟨357593, by rfl⟩ : syracuseStep 1907165 = 715187) (by norm_num)
theorem B3611141 : Blo 750330 3611141 := bbase (se 4 (by rfl) ⟨338544, by rfl⟩ : syracuseStep 3611141 = 677089) (by norm_num)
theorem B2857589 : Blo 750330 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B3218069 : Blo 750330 3218069 := bbase (se 6 (by rfl) ⟨75423, by rfl⟩ : syracuseStep 3218069 = 150847) (by norm_num)
theorem B3054229 : Blo 750330 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B858893 : Blo 750330 858893 := bbase (se 3 (by rfl) ⟨161042, by rfl⟩ : syracuseStep 858893 = 322085) (by norm_num)
theorem B989977 : Blo 750330 989977 := bbase (se 2 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 989977 = 742483) (by norm_num)
theorem B1907509 : Blo 750330 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B3808133 : Blo 750330 3808133 := bbase (se 4 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 3808133 = 714025) (by norm_num)
theorem B1907621 : Blo 750330 1907621 := bbase (se 4 (by rfl) ⟨178839, by rfl⟩ : syracuseStep 1907621 = 357679) (by norm_num)
theorem B760801 : Blo 750330 760801 := bbase (se 2 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 760801 = 570601) (by norm_num)
theorem B1907813 : Blo 750330 1907813 := bbase (se 4 (by rfl) ⟨178857, by rfl⟩ : syracuseStep 1907813 = 357715) (by norm_num)
theorem B1449197 : Blo 750330 1449197 := bbase (se 3 (by rfl) ⟨271724, by rfl⟩ : syracuseStep 1449197 = 543449) (by norm_num)
theorem B2235701 : Blo 750330 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B1908157 : Blo 750330 1908157 := bbase (se 3 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 1908157 = 715559) (by norm_num)
theorem B1908269 : Blo 750330 1908269 := bbase (se 3 (by rfl) ⟨357800, by rfl⟩ : syracuseStep 1908269 = 715601) (by norm_num)
theorem B761401 : Blo 750330 761401 := bbase (se 2 (by rfl) ⟨285525, by rfl⟩ : syracuseStep 761401 = 571051) (by norm_num)
theorem B859729 : Blo 750330 859729 := bbase (se 2 (by rfl) ⟨322398, by rfl⟩ : syracuseStep 859729 = 644797) (by norm_num)
theorem B1908461 : Blo 750330 1908461 := bbase (se 3 (by rfl) ⟨357836, by rfl⟩ : syracuseStep 1908461 = 715673) (by norm_num)
theorem B1285877 : Blo 750330 1285877 := bbase (se 5 (by rfl) ⟨60275, by rfl⟩ : syracuseStep 1285877 = 120551) (by norm_num)
theorem B2858773 : Blo 750330 2858773 := bbase (se 6 (by rfl) ⟨67002, by rfl⟩ : syracuseStep 2858773 = 134005) (by norm_num)
theorem B761717 : Blo 750330 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B2138021 : Blo 750330 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B7315445 : Blo 750330 7315445 := bbase (se 5 (by rfl) ⟨342911, by rfl⟩ : syracuseStep 7315445 = 685823) (by norm_num)
theorem B2859077 : Blo 750330 2859077 := bbase (se 4 (by rfl) ⟨268038, by rfl⟩ : syracuseStep 2859077 = 536077) (by norm_num)
theorem B1908805 : Blo 750330 1908805 := bbase (se 4 (by rfl) ⟨178950, by rfl⟩ : syracuseStep 1908805 = 357901) (by norm_num)
theorem B761977 : Blo 750330 761977 := bbase (se 2 (by rfl) ⟨285741, by rfl⟩ : syracuseStep 761977 = 571483) (by norm_num)
theorem B3809429 : Blo 750330 3809429 := bbase (se 6 (by rfl) ⟨89283, by rfl⟩ : syracuseStep 3809429 = 178567) (by norm_num)
theorem B1908917 : Blo 750330 1908917 := bbase (se 5 (by rfl) ⟨89480, by rfl⟩ : syracuseStep 1908917 = 178961) (by norm_num)
theorem B3613045 : Blo 750330 3613045 := bbase (se 5 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 3613045 = 338723) (by norm_num)
theorem B1909109 : Blo 750330 1909109 := bbase (se 5 (by rfl) ⟨89489, by rfl⟩ : syracuseStep 1909109 = 178979) (by norm_num)
theorem B3613061 : Blo 750330 3613061 := bbase (se 4 (by rfl) ⟨338724, by rfl⟩ : syracuseStep 3613061 = 677449) (by norm_num)
theorem B1286533 : Blo 750330 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B1810829 : Blo 750330 1810829 := bbase (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) (by norm_num)
theorem B1352189 : Blo 750330 1352189 := bbase (se 3 (by rfl) ⟨253535, by rfl⟩ : syracuseStep 1352189 = 507071) (by norm_num)
theorem B1352261 : Blo 750330 1352261 := bbase (se 4 (by rfl) ⟨126774, by rfl⟩ : syracuseStep 1352261 = 253549) (by norm_num)
theorem B1811213 : Blo 750330 1811213 := bbase (se 3 (by rfl) ⟨339602, by rfl⟩ : syracuseStep 1811213 = 679205) (by norm_num)
theorem B6595445 : Blo 750330 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B2171845 : Blo 750330 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B1811413 : Blo 750330 1811413 := bbase (se 7 (by rfl) ⟨21227, by rfl⟩ : syracuseStep 1811413 = 42455) (by norm_num)
theorem B2139205 : Blo 750330 2139205 := bbase (se 4 (by rfl) ⟨200550, by rfl⟩ : syracuseStep 2139205 = 401101) (by norm_num)
theorem B2532437 : Blo 750330 2532437 := bbase (se 8 (by rfl) ⟨14838, by rfl⟩ : syracuseStep 2532437 = 29677) (by norm_num)
theorem B17572949 : Blo 750330 17572949 := bbase (se 8 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 17572949 = 205933) (by norm_num)
theorem B2139365 : Blo 750330 2139365 := bbase (se 4 (by rfl) ⟨200565, by rfl⟩ : syracuseStep 2139365 = 401131) (by norm_num)
theorem B763165 : Blo 750330 763165 := bbase (se 3 (by rfl) ⟨143093, by rfl⟩ : syracuseStep 763165 = 286187) (by norm_num)
theorem B1353053 : Blo 750330 1353053 := bbase (se 3 (by rfl) ⟨253697, by rfl⟩ : syracuseStep 1353053 = 507395) (by norm_num)
theorem B3810725 : Blo 750330 3810725 := bbase (se 4 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 3810725 = 714511) (by norm_num)
theorem B2139605 : Blo 750330 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2532869 : Blo 750330 2532869 := bbase (se 4 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 2532869 = 474913) (by norm_num)
theorem B2139797 : Blo 750330 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B2533301 : Blo 750330 2533301 := bbase (se 5 (by rfl) ⟨118748, by rfl⟩ : syracuseStep 2533301 = 237497) (by norm_num)
theorem B5711957 : Blo 750330 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B2861189 : Blo 750330 2861189 := bbase (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) (by norm_num)
theorem B3909941 : Blo 750330 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B2533733 : Blo 750330 2533733 := bbase (se 4 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 2533733 = 475075) (by norm_num)
theorem B1288613 : Blo 750330 1288613 := bbase (se 4 (by rfl) ⟨120807, by rfl⟩ : syracuseStep 1288613 = 241615) (by norm_num)
theorem B2861477 : Blo 750330 2861477 := bbase (se 4 (by rfl) ⟨268263, by rfl⟩ : syracuseStep 2861477 = 536527) (by norm_num)
theorem B764401 : Blo 750330 764401 := bbase (se 2 (by rfl) ⟨286650, by rfl⟩ : syracuseStep 764401 = 573301) (by norm_num)
theorem B2140789 : Blo 750330 2140789 := bbase (se 5 (by rfl) ⟨100349, by rfl⟩ : syracuseStep 2140789 = 200699) (by norm_num)
theorem B2894453 : Blo 750330 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B3812021 : Blo 750330 3812021 := bbase (se 5 (by rfl) ⟨178688, by rfl⟩ : syracuseStep 3812021 = 357377) (by norm_num)
theorem B1288901 : Blo 750330 1288901 := bbase (se 4 (by rfl) ⟨120834, by rfl⟩ : syracuseStep 1288901 = 241669) (by norm_num)
theorem B3615445 : Blo 750330 3615445 := bbase (se 7 (by rfl) ⟨42368, by rfl⟩ : syracuseStep 3615445 = 84737) (by norm_num)
theorem B2534165 : Blo 750330 2534165 := bbase (se 6 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 2534165 = 118789) (by norm_num)
theorem B1125509 : Blo 750330 1125509 := bbase (se 4 (by rfl) ⟨105516, by rfl⟩ : syracuseStep 1125509 = 211033) (by norm_num)
theorem B1715341 : Blo 750330 1715341 := bbase (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) (by norm_num)
theorem B1125533 : Blo 750330 1125533 := bbase (se 3 (by rfl) ⟨211037, by rfl⟩ : syracuseStep 1125533 = 422075) (by norm_num)
theorem B1125557 : Blo 750330 1125557 := bbase (se 5 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 1125557 = 105521) (by norm_num)
theorem B2534597 : Blo 750330 2534597 := bbase (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) (by norm_num)
theorem B1125581 : Blo 750330 1125581 := bbase (se 3 (by rfl) ⟨211046, by rfl⟩ : syracuseStep 1125581 = 422093) (by norm_num)
theorem B1125605 : Blo 750330 1125605 := bbase (se 4 (by rfl) ⟨105525, by rfl⟩ : syracuseStep 1125605 = 211051) (by norm_num)
theorem B1125629 : Blo 750330 1125629 := bbase (se 3 (by rfl) ⟨211055, by rfl⟩ : syracuseStep 1125629 = 422111) (by norm_num)
theorem B1125653 : Blo 750330 1125653 := bbase (se 6 (by rfl) ⟨26382, by rfl⟩ : syracuseStep 1125653 = 52765) (by norm_num)
theorem B1125677 : Blo 750330 1125677 := bbase (se 3 (by rfl) ⟨211064, by rfl⟩ : syracuseStep 1125677 = 422129) (by norm_num)
theorem B1125701 : Blo 750330 1125701 := bbase (se 4 (by rfl) ⟨105534, by rfl⟩ : syracuseStep 1125701 = 211069) (by norm_num)
theorem B1125725 : Blo 750330 1125725 := bbase (se 3 (by rfl) ⟨211073, by rfl⟩ : syracuseStep 1125725 = 422147) (by norm_num)
theorem B1125749 : Blo 750330 1125749 := bbase (se 5 (by rfl) ⟨52769, by rfl⟩ : syracuseStep 1125749 = 105539) (by norm_num)
theorem B1125773 : Blo 750330 1125773 := bbase (se 3 (by rfl) ⟨211082, by rfl⟩ : syracuseStep 1125773 = 422165) (by norm_num)
theorem B1125797 : Blo 750330 1125797 := bbase (se 4 (by rfl) ⟨105543, by rfl⟩ : syracuseStep 1125797 = 211087) (by norm_num)
theorem B1125821 : Blo 750330 1125821 := bbase (se 3 (by rfl) ⟨211091, by rfl⟩ : syracuseStep 1125821 = 422183) (by norm_num)
theorem B1125845 : Blo 750330 1125845 := bbase (se 7 (by rfl) ⟨13193, by rfl⟩ : syracuseStep 1125845 = 26387) (by norm_num)
theorem B1224157 : Blo 750330 1224157 := bbase (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) (by norm_num)
theorem B1125869 : Blo 750330 1125869 := bbase (se 3 (by rfl) ⟨211100, by rfl⟩ : syracuseStep 1125869 = 422201) (by norm_num)
theorem B1125893 : Blo 750330 1125893 := bbase (se 4 (by rfl) ⟨105552, by rfl⟩ : syracuseStep 1125893 = 211105) (by norm_num)
theorem B1125917 : Blo 750330 1125917 := bbase (se 3 (by rfl) ⟨211109, by rfl⟩ : syracuseStep 1125917 = 422219) (by norm_num)
theorem B1125941 : Blo 750330 1125941 := bbase (se 5 (by rfl) ⟨52778, by rfl⟩ : syracuseStep 1125941 = 105557) (by norm_num)
theorem B2862661 : Blo 750330 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B1125965 : Blo 750330 1125965 := bbase (se 3 (by rfl) ⟨211118, by rfl⟩ : syracuseStep 1125965 = 422237) (by norm_num)
theorem B1125989 : Blo 750330 1125989 := bbase (se 4 (by rfl) ⟨105561, by rfl⟩ : syracuseStep 1125989 = 211123) (by norm_num)
theorem B2535029 : Blo 750330 2535029 := bbase (se 5 (by rfl) ⟨118829, by rfl⟩ : syracuseStep 2535029 = 237659) (by norm_num)
theorem B1126013 : Blo 750330 1126013 := bbase (se 3 (by rfl) ⟨211127, by rfl⟩ : syracuseStep 1126013 = 422255) (by norm_num)
theorem B1126037 : Blo 750330 1126037 := bbase (se 6 (by rfl) ⟨26391, by rfl⟩ : syracuseStep 1126037 = 52783) (by norm_num)
theorem B1126061 : Blo 750330 1126061 := bbase (se 3 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 1126061 = 422273) (by norm_num)
theorem B1126085 : Blo 750330 1126085 := bbase (se 4 (by rfl) ⟨105570, by rfl⟩ : syracuseStep 1126085 = 211141) (by norm_num)
theorem B2141893 : Blo 750330 2141893 := bbase (se 4 (by rfl) ⟨200802, by rfl⟩ : syracuseStep 2141893 = 401605) (by norm_num)
theorem B1126109 : Blo 750330 1126109 := bbase (se 3 (by rfl) ⟨211145, by rfl⟩ : syracuseStep 1126109 = 422291) (by norm_num)
theorem B1126133 : Blo 750330 1126133 := bbase (se 5 (by rfl) ⟨52787, by rfl⟩ : syracuseStep 1126133 = 105575) (by norm_num)
theorem B1126157 : Blo 750330 1126157 := bbase (se 3 (by rfl) ⟨211154, by rfl⟩ : syracuseStep 1126157 = 422309) (by norm_num)
theorem B1126181 : Blo 750330 1126181 := bbase (se 4 (by rfl) ⟨105579, by rfl⟩ : syracuseStep 1126181 = 211159) (by norm_num)
theorem B1126205 : Blo 750330 1126205 := bbase (se 3 (by rfl) ⟨211163, by rfl⟩ : syracuseStep 1126205 = 422327) (by norm_num)
theorem B1126229 : Blo 750330 1126229 := bbase (se 9 (by rfl) ⟨3299, by rfl⟩ : syracuseStep 1126229 = 6599) (by norm_num)
theorem B1126253 : Blo 750330 1126253 := bbase (se 3 (by rfl) ⟨211172, by rfl⟩ : syracuseStep 1126253 = 422345) (by norm_num)
theorem B2862965 : Blo 750330 2862965 := bbase (se 5 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 2862965 = 268403) (by norm_num)
theorem B1126277 : Blo 750330 1126277 := bbase (se 4 (by rfl) ⟨105588, by rfl⟩ : syracuseStep 1126277 = 211177) (by norm_num)
theorem B3092357 : Blo 750330 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B1126301 : Blo 750330 1126301 := bbase (se 3 (by rfl) ⟨211181, by rfl⟩ : syracuseStep 1126301 = 422363) (by norm_num)
theorem B1126325 : Blo 750330 1126325 := bbase (se 5 (by rfl) ⟨52796, by rfl⟩ : syracuseStep 1126325 = 105593) (by norm_num)
theorem B3813317 : Blo 750330 3813317 := bbase (se 4 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 3813317 = 714997) (by norm_num)
theorem B1126349 : Blo 750330 1126349 := bbase (se 3 (by rfl) ⟨211190, by rfl⟩ : syracuseStep 1126349 = 422381) (by norm_num)
theorem B1126373 : Blo 750330 1126373 := bbase (se 4 (by rfl) ⟨105597, by rfl⟩ : syracuseStep 1126373 = 211195) (by norm_num)
theorem B1126397 : Blo 750330 1126397 := bbase (se 3 (by rfl) ⟨211199, by rfl⟩ : syracuseStep 1126397 = 422399) (by norm_num)
theorem B1126421 : Blo 750330 1126421 := bbase (se 6 (by rfl) ⟨26400, by rfl⟩ : syracuseStep 1126421 = 52801) (by norm_num)
theorem B2535461 : Blo 750330 2535461 := bbase (se 4 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 2535461 = 475399) (by norm_num)
theorem B1126445 : Blo 750330 1126445 := bbase (se 3 (by rfl) ⟨211208, by rfl⟩ : syracuseStep 1126445 = 422417) (by norm_num)
theorem B1126469 : Blo 750330 1126469 := bbase (se 4 (by rfl) ⟨105606, by rfl⟩ : syracuseStep 1126469 = 211213) (by norm_num)
theorem B1126493 : Blo 750330 1126493 := bbase (se 3 (by rfl) ⟨211217, by rfl⟩ : syracuseStep 1126493 = 422435) (by norm_num)
theorem B1126517 : Blo 750330 1126517 := bbase (se 5 (by rfl) ⟨52805, by rfl⟩ : syracuseStep 1126517 = 105611) (by norm_num)
theorem B1126541 : Blo 750330 1126541 := bbase (se 3 (by rfl) ⟨211226, by rfl⟩ : syracuseStep 1126541 = 422453) (by norm_num)
theorem B1126565 : Blo 750330 1126565 := bbase (se 4 (by rfl) ⟨105615, by rfl⟩ : syracuseStep 1126565 = 211231) (by norm_num)
theorem B1126589 : Blo 750330 1126589 := bbase (se 3 (by rfl) ⟨211235, by rfl⟩ : syracuseStep 1126589 = 422471) (by norm_num)
theorem B1126613 : Blo 750330 1126613 := bbase (se 7 (by rfl) ⟨13202, by rfl⟩ : syracuseStep 1126613 = 26405) (by norm_num)
theorem B1126637 : Blo 750330 1126637 := bbase (se 3 (by rfl) ⟨211244, by rfl⟩ : syracuseStep 1126637 = 422489) (by norm_num)
theorem B1126661 : Blo 750330 1126661 := bbase (se 4 (by rfl) ⟨105624, by rfl⟩ : syracuseStep 1126661 = 211249) (by norm_num)
theorem B1126685 : Blo 750330 1126685 := bbase (se 3 (by rfl) ⟨211253, by rfl⟩ : syracuseStep 1126685 = 422507) (by norm_num)
theorem B1126709 : Blo 750330 1126709 := bbase (se 5 (by rfl) ⟨52814, by rfl⟩ : syracuseStep 1126709 = 105629) (by norm_num)
theorem B2896181 : Blo 750330 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B1126733 : Blo 750330 1126733 := bbase (se 3 (by rfl) ⟨211262, by rfl⟩ : syracuseStep 1126733 = 422525) (by norm_num)
theorem B1126757 : Blo 750330 1126757 := bbase (se 4 (by rfl) ⟨105633, by rfl⟩ : syracuseStep 1126757 = 211267) (by norm_num)
theorem B1126781 : Blo 750330 1126781 := bbase (se 3 (by rfl) ⟨211271, by rfl⟩ : syracuseStep 1126781 = 422543) (by norm_num)
theorem B2568581 : Blo 750330 2568581 := bbase (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) (by norm_num)
theorem B1126805 : Blo 750330 1126805 := bbase (se 6 (by rfl) ⟨26409, by rfl⟩ : syracuseStep 1126805 = 52819) (by norm_num)
theorem B1126829 : Blo 750330 1126829 := bbase (se 3 (by rfl) ⟨211280, by rfl⟩ : syracuseStep 1126829 = 422561) (by norm_num)
theorem B1126853 : Blo 750330 1126853 := bbase (se 4 (by rfl) ⟨105642, by rfl⟩ : syracuseStep 1126853 = 211285) (by norm_num)
theorem B2535893 : Blo 750330 2535893 := bbase (se 7 (by rfl) ⟨29717, by rfl⟩ : syracuseStep 2535893 = 59435) (by norm_num)
theorem B5419477 : Blo 750330 5419477 := bbase (se 7 (by rfl) ⟨63509, by rfl⟩ : syracuseStep 5419477 = 127019) (by norm_num)
theorem B1126877 : Blo 750330 1126877 := bbase (se 3 (by rfl) ⟨211289, by rfl⟩ : syracuseStep 1126877 = 422579) (by norm_num)
theorem B1126901 : Blo 750330 1126901 := bbase (se 5 (by rfl) ⟨52823, by rfl⟩ : syracuseStep 1126901 = 105647) (by norm_num)
theorem B1356277 : Blo 750330 1356277 := bbase (se 5 (by rfl) ⟨63575, by rfl⟩ : syracuseStep 1356277 = 127151) (by norm_num)
theorem B1126925 : Blo 750330 1126925 := bbase (se 3 (by rfl) ⟨211298, by rfl⟩ : syracuseStep 1126925 = 422597) (by norm_num)
theorem B1126949 : Blo 750330 1126949 := bbase (se 4 (by rfl) ⟨105651, by rfl⟩ : syracuseStep 1126949 = 211303) (by norm_num)
theorem B1126973 : Blo 750330 1126973 := bbase (se 3 (by rfl) ⟨211307, by rfl⟩ : syracuseStep 1126973 = 422615) (by norm_num)
theorem B1126997 : Blo 750330 1126997 := bbase (se 8 (by rfl) ⟨6603, by rfl⟩ : syracuseStep 1126997 = 13207) (by norm_num)
theorem B1127021 : Blo 750330 1127021 := bbase (se 3 (by rfl) ⟨211316, by rfl⟩ : syracuseStep 1127021 = 422633) (by norm_num)
theorem B1127045 : Blo 750330 1127045 := bbase (se 4 (by rfl) ⟨105660, by rfl⟩ : syracuseStep 1127045 = 211321) (by norm_num)
theorem B1127069 : Blo 750330 1127069 := bbase (se 3 (by rfl) ⟨211325, by rfl⟩ : syracuseStep 1127069 = 422651) (by norm_num)
theorem B1127093 : Blo 750330 1127093 := bbase (se 5 (by rfl) ⟨52832, by rfl⟩ : syracuseStep 1127093 = 105665) (by norm_num)
theorem B1127117 : Blo 750330 1127117 := bbase (se 3 (by rfl) ⟨211334, by rfl⟩ : syracuseStep 1127117 = 422669) (by norm_num)
theorem B1127141 : Blo 750330 1127141 := bbase (se 4 (by rfl) ⟨105669, by rfl⟩ : syracuseStep 1127141 = 211339) (by norm_num)
theorem B1127165 : Blo 750330 1127165 := bbase (se 3 (by rfl) ⟨211343, by rfl⟩ : syracuseStep 1127165 = 422687) (by norm_num)
theorem B1127189 : Blo 750330 1127189 := bbase (se 6 (by rfl) ⟨26418, by rfl⟩ : syracuseStep 1127189 = 52837) (by norm_num)
theorem B1127213 : Blo 750330 1127213 := bbase (se 3 (by rfl) ⟨211352, by rfl⟩ : syracuseStep 1127213 = 422705) (by norm_num)
theorem B1127237 : Blo 750330 1127237 := bbase (se 4 (by rfl) ⟨105678, by rfl⟩ : syracuseStep 1127237 = 211357) (by norm_num)
theorem B1127261 : Blo 750330 1127261 := bbase (se 3 (by rfl) ⟨211361, by rfl⟩ : syracuseStep 1127261 = 422723) (by norm_num)
theorem B1127285 : Blo 750330 1127285 := bbase (se 5 (by rfl) ⟨52841, by rfl⟩ : syracuseStep 1127285 = 105683) (by norm_num)
theorem B2536325 : Blo 750330 2536325 := bbase (se 4 (by rfl) ⟨237780, by rfl⟩ : syracuseStep 2536325 = 475561) (by norm_num)
theorem B1127309 : Blo 750330 1127309 := bbase (se 3 (by rfl) ⟨211370, by rfl⟩ : syracuseStep 1127309 = 422741) (by norm_num)
theorem B1127333 : Blo 750330 1127333 := bbase (se 4 (by rfl) ⟨105687, by rfl⟩ : syracuseStep 1127333 = 211375) (by norm_num)
theorem B1127357 : Blo 750330 1127357 := bbase (se 3 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 1127357 = 422759) (by norm_num)
theorem B1127381 : Blo 750330 1127381 := bbase (se 7 (by rfl) ⟨13211, by rfl⟩ : syracuseStep 1127381 = 26423) (by norm_num)
theorem B1127405 : Blo 750330 1127405 := bbase (se 3 (by rfl) ⟨211388, by rfl⟩ : syracuseStep 1127405 = 422777) (by norm_num)
theorem B1127429 : Blo 750330 1127429 := bbase (se 4 (by rfl) ⟨105696, by rfl⟩ : syracuseStep 1127429 = 211393) (by norm_num)
theorem B1127453 : Blo 750330 1127453 := bbase (se 3 (by rfl) ⟨211397, by rfl⟩ : syracuseStep 1127453 = 422795) (by norm_num)
theorem B1127477 : Blo 750330 1127477 := bbase (se 5 (by rfl) ⟨52850, by rfl⟩ : syracuseStep 1127477 = 105701) (by norm_num)
theorem B1127501 : Blo 750330 1127501 := bbase (se 3 (by rfl) ⟨211406, by rfl⟩ : syracuseStep 1127501 = 422813) (by norm_num)
theorem B1029205 : Blo 750330 1029205 := bbase (se 8 (by rfl) ⟨6030, by rfl⟩ : syracuseStep 1029205 = 12061) (by norm_num)
theorem B1127525 : Blo 750330 1127525 := bbase (se 4 (by rfl) ⟨105705, by rfl⟩ : syracuseStep 1127525 = 211411) (by norm_num)
theorem B1127549 : Blo 750330 1127549 := bbase (se 3 (by rfl) ⟨211415, by rfl⟩ : syracuseStep 1127549 = 422831) (by norm_num)
theorem B1127573 : Blo 750330 1127573 := bbase (se 6 (by rfl) ⟨26427, by rfl⟩ : syracuseStep 1127573 = 52855) (by norm_num)
theorem B2143397 : Blo 750330 2143397 := bbase (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) (by norm_num)
theorem B1127597 : Blo 750330 1127597 := bbase (se 3 (by rfl) ⟨211424, by rfl⟩ : syracuseStep 1127597 = 422849) (by norm_num)
theorem B1127621 : Blo 750330 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B3814613 : Blo 750330 3814613 := bbase (se 7 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 3814613 = 89405) (by norm_num)
theorem B1127645 : Blo 750330 1127645 := bbase (se 3 (by rfl) ⟨211433, by rfl⟩ : syracuseStep 1127645 = 422867) (by norm_num)
theorem B4568309 : Blo 750330 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B1127669 : Blo 750330 1127669 := bbase (se 5 (by rfl) ⟨52859, by rfl⟩ : syracuseStep 1127669 = 105719) (by norm_num)
theorem B963833 : Blo 750330 963833 := bbase (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) (by norm_num)
theorem B1127693 : Blo 750330 1127693 := bbase (se 3 (by rfl) ⟨211442, by rfl⟩ : syracuseStep 1127693 = 422885) (by norm_num)
theorem B1127717 : Blo 750330 1127717 := bbase (se 4 (by rfl) ⟨105723, by rfl⟩ : syracuseStep 1127717 = 211447) (by norm_num)
theorem B2536757 : Blo 750330 2536757 := bbase (se 5 (by rfl) ⟨118910, by rfl⟩ : syracuseStep 2536757 = 237821) (by norm_num)
theorem B1127741 : Blo 750330 1127741 := bbase (se 3 (by rfl) ⟨211451, by rfl⟩ : syracuseStep 1127741 = 422903) (by norm_num)
theorem B1127765 : Blo 750330 1127765 := bbase (se 13 (by rfl) ⟨206, by rfl⟩ : syracuseStep 1127765 = 413) (by norm_num)
theorem B1127789 : Blo 750330 1127789 := bbase (se 3 (by rfl) ⟨211460, by rfl⟩ : syracuseStep 1127789 = 422921) (by norm_num)
theorem B1127813 : Blo 750330 1127813 := bbase (se 4 (by rfl) ⟨105732, by rfl⟩ : syracuseStep 1127813 = 211465) (by norm_num)
theorem B1127837 : Blo 750330 1127837 := bbase (se 3 (by rfl) ⟨211469, by rfl⟩ : syracuseStep 1127837 = 422939) (by norm_num)
theorem B2602405 : Blo 750330 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B1127861 : Blo 750330 1127861 := bbase (se 5 (by rfl) ⟨52868, by rfl⟩ : syracuseStep 1127861 = 105737) (by norm_num)
theorem B1127885 : Blo 750330 1127885 := bbase (se 3 (by rfl) ⟨211478, by rfl⟩ : syracuseStep 1127885 = 422957) (by norm_num)
theorem B1127909 : Blo 750330 1127909 := bbase (se 4 (by rfl) ⟨105741, by rfl⟩ : syracuseStep 1127909 = 211483) (by norm_num)
theorem B1127933 : Blo 750330 1127933 := bbase (se 3 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 1127933 = 422975) (by norm_num)
theorem B1127957 : Blo 750330 1127957 := bbase (se 6 (by rfl) ⟨26436, by rfl⟩ : syracuseStep 1127957 = 52873) (by norm_num)
theorem B1127981 : Blo 750330 1127981 := bbase (se 3 (by rfl) ⟨211496, by rfl⟩ : syracuseStep 1127981 = 422993) (by norm_num)
theorem B1128005 : Blo 750330 1128005 := bbase (se 4 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 1128005 = 211501) (by norm_num)
theorem B1128029 : Blo 750330 1128029 := bbase (se 3 (by rfl) ⟨211505, by rfl⟩ : syracuseStep 1128029 = 423011) (by norm_num)
theorem B1128053 : Blo 750330 1128053 := bbase (se 5 (by rfl) ⟨52877, by rfl⟩ : syracuseStep 1128053 = 105755) (by norm_num)
theorem B1128077 : Blo 750330 1128077 := bbase (se 3 (by rfl) ⟨211514, by rfl⟩ : syracuseStep 1128077 = 423029) (by norm_num)
theorem B1128101 : Blo 750330 1128101 := bbase (se 4 (by rfl) ⟨105759, by rfl⟩ : syracuseStep 1128101 = 211519) (by norm_num)
theorem B1357493 : Blo 750330 1357493 := bbase (se 5 (by rfl) ⟨63632, by rfl⟩ : syracuseStep 1357493 = 127265) (by norm_num)
theorem B1128125 : Blo 750330 1128125 := bbase (se 3 (by rfl) ⟨211523, by rfl⟩ : syracuseStep 1128125 = 423047) (by norm_num)
theorem B1128149 : Blo 750330 1128149 := bbase (se 7 (by rfl) ⟨13220, by rfl⟩ : syracuseStep 1128149 = 26441) (by norm_num)
theorem B2537189 : Blo 750330 2537189 := bbase (se 4 (by rfl) ⟨237861, by rfl⟩ : syracuseStep 2537189 = 475723) (by norm_num)
theorem B1128173 : Blo 750330 1128173 := bbase (se 3 (by rfl) ⟨211532, by rfl⟩ : syracuseStep 1128173 = 423065) (by norm_num)
theorem B1128197 : Blo 750330 1128197 := bbase (se 4 (by rfl) ⟨105768, by rfl⟩ : syracuseStep 1128197 = 211537) (by norm_num)
theorem B1128221 : Blo 750330 1128221 := bbase (se 3 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 1128221 = 423083) (by norm_num)
theorem B1128245 : Blo 750330 1128245 := bbase (se 5 (by rfl) ⟨52886, by rfl⟩ : syracuseStep 1128245 = 105773) (by norm_num)
theorem B3094325 : Blo 750330 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B1128269 : Blo 750330 1128269 := bbase (se 3 (by rfl) ⟨211550, by rfl⟩ : syracuseStep 1128269 = 423101) (by norm_num)
theorem B1357661 : Blo 750330 1357661 := bbase (se 3 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 1357661 = 509123) (by norm_num)
theorem B1128293 : Blo 750330 1128293 := bbase (se 4 (by rfl) ⟨105777, by rfl⟩ : syracuseStep 1128293 = 211555) (by norm_num)
theorem B1128317 : Blo 750330 1128317 := bbase (se 3 (by rfl) ⟨211559, by rfl⟩ : syracuseStep 1128317 = 423119) (by norm_num)
theorem B1128341 : Blo 750330 1128341 := bbase (se 6 (by rfl) ⟨26445, by rfl⟩ : syracuseStep 1128341 = 52891) (by norm_num)
theorem B1128365 : Blo 750330 1128365 := bbase (se 3 (by rfl) ⟨211568, by rfl⟩ : syracuseStep 1128365 = 423137) (by norm_num)
theorem B1128389 : Blo 750330 1128389 := bbase (se 4 (by rfl) ⟨105786, by rfl⟩ : syracuseStep 1128389 = 211573) (by norm_num)
theorem B1128413 : Blo 750330 1128413 := bbase (se 3 (by rfl) ⟨211577, by rfl⟩ : syracuseStep 1128413 = 423155) (by norm_num)
theorem B1128437 : Blo 750330 1128437 := bbase (se 5 (by rfl) ⟨52895, by rfl⟩ : syracuseStep 1128437 = 105791) (by norm_num)
theorem B1718261 : Blo 750330 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B1128461 : Blo 750330 1128461 := bbase (se 3 (by rfl) ⟨211586, by rfl⟩ : syracuseStep 1128461 = 423173) (by norm_num)
theorem B1128485 : Blo 750330 1128485 := bbase (se 4 (by rfl) ⟨105795, by rfl⟩ : syracuseStep 1128485 = 211591) (by norm_num)
theorem B1128509 : Blo 750330 1128509 := bbase (se 3 (by rfl) ⟨211595, by rfl⟩ : syracuseStep 1128509 = 423191) (by norm_num)
theorem B1128533 : Blo 750330 1128533 := bbase (se 8 (by rfl) ⟨6612, by rfl⟩ : syracuseStep 1128533 = 13225) (by norm_num)
theorem B1128557 : Blo 750330 1128557 := bbase (se 3 (by rfl) ⟨211604, by rfl⟩ : syracuseStep 1128557 = 423209) (by norm_num)
theorem B1128581 : Blo 750330 1128581 := bbase (se 4 (by rfl) ⟨105804, by rfl⟩ : syracuseStep 1128581 = 211609) (by norm_num)
theorem B9615509 : Blo 750330 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B2537621 : Blo 750330 2537621 := bbase (se 6 (by rfl) ⟨59475, by rfl⟩ : syracuseStep 2537621 = 118951) (by norm_num)
theorem B1128605 : Blo 750330 1128605 := bbase (se 3 (by rfl) ⟨211613, by rfl⟩ : syracuseStep 1128605 = 423227) (by norm_num)
theorem B2406581 : Blo 750330 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B1128629 : Blo 750330 1128629 := bbase (se 5 (by rfl) ⟨52904, by rfl⟩ : syracuseStep 1128629 = 105809) (by norm_num)
theorem B1128653 : Blo 750330 1128653 := bbase (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) (by norm_num)
theorem B1521877 : Blo 750330 1521877 := bbase (se 7 (by rfl) ⟨17834, by rfl⟩ : syracuseStep 1521877 = 35669) (by norm_num)
theorem B1128677 : Blo 750330 1128677 := bbase (se 4 (by rfl) ⟨105813, by rfl⟩ : syracuseStep 1128677 = 211627) (by norm_num)
theorem B1128701 : Blo 750330 1128701 := bbase (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) (by norm_num)
theorem B1128725 : Blo 750330 1128725 := bbase (se 6 (by rfl) ⟨26454, by rfl⟩ : syracuseStep 1128725 = 52909) (by norm_num)
theorem B1128749 : Blo 750330 1128749 := bbase (se 3 (by rfl) ⟨211640, by rfl⟩ : syracuseStep 1128749 = 423281) (by norm_num)
theorem B1128773 : Blo 750330 1128773 := bbase (se 4 (by rfl) ⟨105822, by rfl⟩ : syracuseStep 1128773 = 211645) (by norm_num)
theorem B1128797 : Blo 750330 1128797 := bbase (se 3 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 1128797 = 423299) (by norm_num)
theorem B1128821 : Blo 750330 1128821 := bbase (se 5 (by rfl) ⟨52913, by rfl⟩ : syracuseStep 1128821 = 105827) (by norm_num)
theorem B1128845 : Blo 750330 1128845 := bbase (se 3 (by rfl) ⟨211658, by rfl⟩ : syracuseStep 1128845 = 423317) (by norm_num)
theorem B1128869 : Blo 750330 1128869 := bbase (se 4 (by rfl) ⟨105831, by rfl⟩ : syracuseStep 1128869 = 211663) (by norm_num)
theorem B1128893 : Blo 750330 1128893 := bbase (se 3 (by rfl) ⟨211667, by rfl⟩ : syracuseStep 1128893 = 423335) (by norm_num)
theorem B1128917 : Blo 750330 1128917 := bbase (se 7 (by rfl) ⟨13229, by rfl⟩ : syracuseStep 1128917 = 26459) (by norm_num)
theorem B3815909 : Blo 750330 3815909 := bbase (se 4 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 3815909 = 715483) (by norm_num)
theorem B1128941 : Blo 750330 1128941 := bbase (se 3 (by rfl) ⟨211676, by rfl⟩ : syracuseStep 1128941 = 423353) (by norm_num)
theorem B1128965 : Blo 750330 1128965 := bbase (se 4 (by rfl) ⟨105840, by rfl⟩ : syracuseStep 1128965 = 211681) (by norm_num)
theorem B3619349 : Blo 750330 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B1128989 : Blo 750330 1128989 := bbase (se 3 (by rfl) ⟨211685, by rfl⟩ : syracuseStep 1128989 = 423371) (by norm_num)
theorem B1129013 : Blo 750330 1129013 := bbase (se 5 (by rfl) ⟨52922, by rfl⟩ : syracuseStep 1129013 = 105845) (by norm_num)
theorem B2538053 : Blo 750330 2538053 := bbase (se 4 (by rfl) ⟨237942, by rfl⟩ : syracuseStep 2538053 = 475885) (by norm_num)
theorem B1129037 : Blo 750330 1129037 := bbase (se 3 (by rfl) ⟨211694, by rfl⟩ : syracuseStep 1129037 = 423389) (by norm_num)
theorem B801361 : Blo 750330 801361 := bbase (se 2 (by rfl) ⟨300510, by rfl⟩ : syracuseStep 801361 = 601021) (by norm_num)
theorem B1129061 : Blo 750330 1129061 := bbase (se 4 (by rfl) ⟨105849, by rfl⟩ : syracuseStep 1129061 = 211699) (by norm_num)
theorem B1129085 : Blo 750330 1129085 := bbase (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) (by norm_num)
theorem B1129109 : Blo 750330 1129109 := bbase (se 6 (by rfl) ⟨26463, by rfl⟩ : syracuseStep 1129109 = 52927) (by norm_num)
theorem B801433 : Blo 750330 801433 := bbase (se 2 (by rfl) ⟨300537, by rfl⟩ : syracuseStep 801433 = 601075) (by norm_num)
theorem B1129133 : Blo 750330 1129133 := bbase (se 3 (by rfl) ⟨211712, by rfl⟩ : syracuseStep 1129133 = 423425) (by norm_num)
theorem B1129157 : Blo 750330 1129157 := bbase (se 4 (by rfl) ⟨105858, by rfl⟩ : syracuseStep 1129157 = 211717) (by norm_num)
theorem B2144981 : Blo 750330 2144981 := bbase (se 7 (by rfl) ⟨25136, by rfl⟩ : syracuseStep 2144981 = 50273) (by norm_num)
theorem B1129181 : Blo 750330 1129181 := bbase (se 3 (by rfl) ⟨211721, by rfl⟩ : syracuseStep 1129181 = 423443) (by norm_num)
theorem B1129205 : Blo 750330 1129205 := bbase (se 5 (by rfl) ⟨52931, by rfl⟩ : syracuseStep 1129205 = 105863) (by norm_num)
theorem B1129229 : Blo 750330 1129229 := bbase (se 3 (by rfl) ⟨211730, by rfl⟩ : syracuseStep 1129229 = 423461) (by norm_num)
theorem B1129253 : Blo 750330 1129253 := bbase (se 4 (by rfl) ⟨105867, by rfl⟩ : syracuseStep 1129253 = 211735) (by norm_num)
theorem B1129277 : Blo 750330 1129277 := bbase (se 3 (by rfl) ⟨211739, by rfl⟩ : syracuseStep 1129277 = 423479) (by norm_num)
theorem B801613 : Blo 750330 801613 := bbase (se 3 (by rfl) ⟨150302, by rfl⟩ : syracuseStep 801613 = 300605) (by norm_num)
theorem B1129301 : Blo 750330 1129301 := bbase (se 9 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 1129301 = 6617) (by norm_num)
theorem B1129325 : Blo 750330 1129325 := bbase (se 3 (by rfl) ⟨211748, by rfl⟩ : syracuseStep 1129325 = 423497) (by norm_num)
theorem B1129349 : Blo 750330 1129349 := bbase (se 4 (by rfl) ⟨105876, by rfl⟩ : syracuseStep 1129349 = 211753) (by norm_num)
theorem B1129373 : Blo 750330 1129373 := bbase (se 3 (by rfl) ⟨211757, by rfl⟩ : syracuseStep 1129373 = 423515) (by norm_num)
theorem B1129397 : Blo 750330 1129397 := bbase (se 5 (by rfl) ⟨52940, by rfl⟩ : syracuseStep 1129397 = 105881) (by norm_num)
theorem B1129421 : Blo 750330 1129421 := bbase (se 3 (by rfl) ⟨211766, by rfl⟩ : syracuseStep 1129421 = 423533) (by norm_num)
theorem B1129445 : Blo 750330 1129445 := bbase (se 4 (by rfl) ⟨105885, by rfl⟩ : syracuseStep 1129445 = 211771) (by norm_num)
theorem B2538485 : Blo 750330 2538485 := bbase (se 5 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 2538485 = 237983) (by norm_num)
theorem B1129469 : Blo 750330 1129469 := bbase (se 3 (by rfl) ⟨211775, by rfl⟩ : syracuseStep 1129469 = 423551) (by norm_num)
theorem B1129493 : Blo 750330 1129493 := bbase (se 6 (by rfl) ⟨26472, by rfl⟩ : syracuseStep 1129493 = 52945) (by norm_num)
theorem B1129517 : Blo 750330 1129517 := bbase (se 3 (by rfl) ⟨211784, by rfl⟩ : syracuseStep 1129517 = 423569) (by norm_num)
theorem B2407477 : Blo 750330 2407477 := bbase (se 5 (by rfl) ⟨112850, by rfl⟩ : syracuseStep 2407477 = 225701) (by norm_num)
theorem B1129541 : Blo 750330 1129541 := bbase (se 4 (by rfl) ⟨105894, by rfl⟩ : syracuseStep 1129541 = 211789) (by norm_num)
theorem B15416405 : Blo 750330 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B1129565 : Blo 750330 1129565 := bbase (se 3 (by rfl) ⟨211793, by rfl⟩ : syracuseStep 1129565 = 423587) (by norm_num)
theorem B1129589 : Blo 750330 1129589 := bbase (se 5 (by rfl) ⟨52949, by rfl⟩ : syracuseStep 1129589 = 105899) (by norm_num)
theorem B965773 : Blo 750330 965773 := bbase (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) (by norm_num)
theorem B1129613 : Blo 750330 1129613 := bbase (se 3 (by rfl) ⟨211802, by rfl⟩ : syracuseStep 1129613 = 423605) (by norm_num)
theorem B1129637 : Blo 750330 1129637 := bbase (se 4 (by rfl) ⟨105903, by rfl⟩ : syracuseStep 1129637 = 211807) (by norm_num)
theorem B1424557 : Blo 750330 1424557 := bbase (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) (by norm_num)
theorem B1129661 : Blo 750330 1129661 := bbase (se 3 (by rfl) ⟨211811, by rfl⟩ : syracuseStep 1129661 = 423623) (by norm_num)
theorem B1129685 : Blo 750330 1129685 := bbase (se 7 (by rfl) ⟨13238, by rfl⟩ : syracuseStep 1129685 = 26477) (by norm_num)
theorem B1129709 : Blo 750330 1129709 := bbase (se 3 (by rfl) ⟨211820, by rfl⟩ : syracuseStep 1129709 = 423641) (by norm_num)
theorem B1129733 : Blo 750330 1129733 := bbase (se 4 (by rfl) ⟨105912, by rfl⟩ : syracuseStep 1129733 = 211825) (by norm_num)
theorem B802057 : Blo 750330 802057 := bbase (se 2 (by rfl) ⟨300771, by rfl⟩ : syracuseStep 802057 = 601543) (by norm_num)
theorem B1129757 : Blo 750330 1129757 := bbase (se 3 (by rfl) ⟨211829, by rfl⟩ : syracuseStep 1129757 = 423659) (by norm_num)
theorem B1129781 : Blo 750330 1129781 := bbase (se 5 (by rfl) ⟨52958, by rfl⟩ : syracuseStep 1129781 = 105917) (by norm_num)
theorem B1129805 : Blo 750330 1129805 := bbase (se 3 (by rfl) ⟨211838, by rfl⟩ : syracuseStep 1129805 = 423677) (by norm_num)
theorem B1129829 : Blo 750330 1129829 := bbase (se 4 (by rfl) ⟨105921, by rfl⟩ : syracuseStep 1129829 = 211843) (by norm_num)
theorem B2145653 : Blo 750330 2145653 := bbase (se 5 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 2145653 = 201155) (by norm_num)
theorem B1129853 : Blo 750330 1129853 := bbase (se 3 (by rfl) ⟨211847, by rfl⟩ : syracuseStep 1129853 = 423695) (by norm_num)
theorem B802181 : Blo 750330 802181 := bbase (se 4 (by rfl) ⟨75204, by rfl⟩ : syracuseStep 802181 = 150409) (by norm_num)
theorem B1129877 : Blo 750330 1129877 := bbase (se 6 (by rfl) ⟨26481, by rfl⟩ : syracuseStep 1129877 = 52963) (by norm_num)
theorem B2538917 : Blo 750330 2538917 := bbase (se 4 (by rfl) ⟨238023, by rfl⟩ : syracuseStep 2538917 = 476047) (by norm_num)
theorem B1129901 : Blo 750330 1129901 := bbase (se 3 (by rfl) ⟨211856, by rfl⟩ : syracuseStep 1129901 = 423713) (by norm_num)
theorem B2407877 : Blo 750330 2407877 := bbase (se 4 (by rfl) ⟨225738, by rfl⟩ : syracuseStep 2407877 = 451477) (by norm_num)
theorem B1129925 : Blo 750330 1129925 := bbase (se 4 (by rfl) ⟨105930, by rfl⟩ : syracuseStep 1129925 = 211861) (by norm_num)
theorem B1424861 : Blo 750330 1424861 := bbase (se 3 (by rfl) ⟨267161, by rfl⟩ : syracuseStep 1424861 = 534323) (by norm_num)
theorem B1129949 : Blo 750330 1129949 := bbase (se 3 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 1129949 = 423731) (by norm_num)
theorem B1129973 : Blo 750330 1129973 := bbase (se 5 (by rfl) ⟨52967, by rfl⟩ : syracuseStep 1129973 = 105935) (by norm_num)
theorem B1129997 : Blo 750330 1129997 := bbase (se 3 (by rfl) ⟨211874, by rfl⟩ : syracuseStep 1129997 = 423749) (by norm_num)
theorem B1130021 : Blo 750330 1130021 := bbase (se 4 (by rfl) ⟨105939, by rfl⟩ : syracuseStep 1130021 = 211879) (by norm_num)
theorem B1130045 : Blo 750330 1130045 := bbase (se 3 (by rfl) ⟨211883, by rfl⟩ : syracuseStep 1130045 = 423767) (by norm_num)
theorem B1130069 : Blo 750330 1130069 := bbase (se 8 (by rfl) ⟨6621, by rfl⟩ : syracuseStep 1130069 = 13243) (by norm_num)
theorem B1130093 : Blo 750330 1130093 := bbase (se 3 (by rfl) ⟨211892, by rfl⟩ : syracuseStep 1130093 = 423785) (by norm_num)
theorem B802433 : Blo 750330 802433 := bbase (se 2 (by rfl) ⟨300912, by rfl⟩ : syracuseStep 802433 = 601825) (by norm_num)
theorem B1130117 : Blo 750330 1130117 := bbase (se 4 (by rfl) ⟨105948, by rfl⟩ : syracuseStep 1130117 = 211897) (by norm_num)
theorem B1130141 : Blo 750330 1130141 := bbase (se 3 (by rfl) ⟨211901, by rfl⟩ : syracuseStep 1130141 = 423803) (by norm_num)
theorem B1130165 : Blo 750330 1130165 := bbase (se 5 (by rfl) ⟨52976, by rfl⟩ : syracuseStep 1130165 = 105953) (by norm_num)
theorem B1130189 : Blo 750330 1130189 := bbase (se 3 (by rfl) ⟨211910, by rfl⟩ : syracuseStep 1130189 = 423821) (by norm_num)
theorem B1130213 : Blo 750330 1130213 := bbase (se 4 (by rfl) ⟨105957, by rfl⟩ : syracuseStep 1130213 = 211915) (by norm_num)
theorem B3817205 : Blo 750330 3817205 := bbase (se 5 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 3817205 = 357863) (by norm_num)
theorem B1130237 : Blo 750330 1130237 := bbase (se 3 (by rfl) ⟨211919, by rfl⟩ : syracuseStep 1130237 = 423839) (by norm_num)
theorem B1130261 : Blo 750330 1130261 := bbase (se 6 (by rfl) ⟨26490, by rfl⟩ : syracuseStep 1130261 = 52981) (by norm_num)
theorem B2146085 : Blo 750330 2146085 := bbase (se 4 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 2146085 = 402391) (by norm_num)
theorem B1130285 : Blo 750330 1130285 := bbase (se 3 (by rfl) ⟨211928, by rfl⟩ : syracuseStep 1130285 = 423857) (by norm_num)
theorem B1130309 : Blo 750330 1130309 := bbase (se 4 (by rfl) ⟨105966, by rfl⟩ : syracuseStep 1130309 = 211933) (by norm_num)
theorem B2539349 : Blo 750330 2539349 := bbase (se 9 (by rfl) ⟨7439, by rfl⟩ : syracuseStep 2539349 = 14879) (by norm_num)
theorem B1130333 : Blo 750330 1130333 := bbase (se 3 (by rfl) ⟨211937, by rfl⟩ : syracuseStep 1130333 = 423875) (by norm_num)
theorem B1130357 : Blo 750330 1130357 := bbase (se 5 (by rfl) ⟨52985, by rfl⟩ : syracuseStep 1130357 = 105971) (by norm_num)
theorem B1130381 : Blo 750330 1130381 := bbase (se 3 (by rfl) ⟨211946, by rfl⟩ : syracuseStep 1130381 = 423893) (by norm_num)
theorem B1130405 : Blo 750330 1130405 := bbase (se 4 (by rfl) ⟨105975, by rfl⟩ : syracuseStep 1130405 = 211951) (by norm_num)
theorem B1130429 : Blo 750330 1130429 := bbase (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) (by norm_num)
theorem B1130453 : Blo 750330 1130453 := bbase (se 7 (by rfl) ⟨13247, by rfl⟩ : syracuseStep 1130453 = 26495) (by norm_num)
theorem B1130477 : Blo 750330 1130477 := bbase (se 3 (by rfl) ⟨211964, by rfl⟩ : syracuseStep 1130477 = 423929) (by norm_num)
theorem B868357 : Blo 750330 868357 := bbase (se 4 (by rfl) ⟨81408, by rfl⟩ : syracuseStep 868357 = 162817) (by norm_num)
theorem B1130501 : Blo 750330 1130501 := bbase (se 4 (by rfl) ⟨105984, by rfl⟩ : syracuseStep 1130501 = 211969) (by norm_num)
theorem B1523741 : Blo 750330 1523741 := bbase (se 3 (by rfl) ⟨285701, by rfl⟩ : syracuseStep 1523741 = 571403) (by norm_num)
theorem B1130525 : Blo 750330 1130525 := bbase (se 3 (by rfl) ⟨211973, by rfl⟩ : syracuseStep 1130525 = 423947) (by norm_num)
theorem B1130549 : Blo 750330 1130549 := bbase (se 5 (by rfl) ⟨52994, by rfl⟩ : syracuseStep 1130549 = 105989) (by norm_num)
theorem B802877 : Blo 750330 802877 := bbase (se 3 (by rfl) ⟨150539, by rfl⟩ : syracuseStep 802877 = 301079) (by norm_num)
theorem B1130573 : Blo 750330 1130573 := bbase (se 3 (by rfl) ⟨211982, by rfl⟩ : syracuseStep 1130573 = 423965) (by norm_num)
theorem B1130597 : Blo 750330 1130597 := bbase (se 4 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 1130597 = 211987) (by norm_num)
theorem B1130621 : Blo 750330 1130621 := bbase (se 3 (by rfl) ⟨211991, by rfl⟩ : syracuseStep 1130621 = 423983) (by norm_num)
theorem B1130645 : Blo 750330 1130645 := bbase (se 6 (by rfl) ⟨26499, by rfl⟩ : syracuseStep 1130645 = 52999) (by norm_num)
theorem B1130669 : Blo 750330 1130669 := bbase (se 3 (by rfl) ⟨212000, by rfl⟩ : syracuseStep 1130669 = 424001) (by norm_num)
theorem B1130693 : Blo 750330 1130693 := bbase (se 4 (by rfl) ⟨106002, by rfl⟩ : syracuseStep 1130693 = 212005) (by norm_num)
theorem B1425613 : Blo 750330 1425613 := bbase (se 3 (by rfl) ⟨267302, by rfl⟩ : syracuseStep 1425613 = 534605) (by norm_num)
theorem B1130717 : Blo 750330 1130717 := bbase (se 3 (by rfl) ⟨212009, by rfl⟩ : syracuseStep 1130717 = 424019) (by norm_num)
theorem B1130741 : Blo 750330 1130741 := bbase (se 5 (by rfl) ⟨53003, by rfl⟩ : syracuseStep 1130741 = 106007) (by norm_num)
theorem B2539781 : Blo 750330 2539781 := bbase (se 4 (by rfl) ⟨238104, by rfl⟩ : syracuseStep 2539781 = 476209) (by norm_num)
theorem B1130765 : Blo 750330 1130765 := bbase (se 3 (by rfl) ⟨212018, by rfl⟩ : syracuseStep 1130765 = 424037) (by norm_num)
theorem B1130789 : Blo 750330 1130789 := bbase (se 4 (by rfl) ⟨106011, by rfl⟩ : syracuseStep 1130789 = 212023) (by norm_num)
theorem B803125 : Blo 750330 803125 := bbase (se 5 (by rfl) ⟨37646, by rfl⟩ : syracuseStep 803125 = 75293) (by norm_num)
theorem B1130813 : Blo 750330 1130813 := bbase (se 3 (by rfl) ⟨212027, by rfl⟩ : syracuseStep 1130813 = 424055) (by norm_num)
theorem B1130837 : Blo 750330 1130837 := bbase (se 10 (by rfl) ⟨1656, by rfl⟩ : syracuseStep 1130837 = 3313) (by norm_num)
theorem B1425757 : Blo 750330 1425757 := bbase (se 3 (by rfl) ⟨267329, by rfl⟩ : syracuseStep 1425757 = 534659) (by norm_num)
theorem B1130861 : Blo 750330 1130861 := bbase (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) (by norm_num)
theorem B1130885 : Blo 750330 1130885 := bbase (se 4 (by rfl) ⟨106020, by rfl⟩ : syracuseStep 1130885 = 212041) (by norm_num)
theorem B1130909 : Blo 750330 1130909 := bbase (se 3 (by rfl) ⟨212045, by rfl⟩ : syracuseStep 1130909 = 424091) (by norm_num)
theorem B1130933 : Blo 750330 1130933 := bbase (se 5 (by rfl) ⟨53012, by rfl⟩ : syracuseStep 1130933 = 106025) (by norm_num)
theorem B1130957 : Blo 750330 1130957 := bbase (se 3 (by rfl) ⟨212054, by rfl⟩ : syracuseStep 1130957 = 424109) (by norm_num)
theorem B1524197 : Blo 750330 1524197 := bbase (se 4 (by rfl) ⟨142893, by rfl⟩ : syracuseStep 1524197 = 285787) (by norm_num)
theorem B1130981 : Blo 750330 1130981 := bbase (se 4 (by rfl) ⟨106029, by rfl⟩ : syracuseStep 1130981 = 212059) (by norm_num)
theorem B3621365 : Blo 750330 3621365 := bbase (se 5 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 3621365 = 339503) (by norm_num)
theorem B1425917 : Blo 750330 1425917 := bbase (se 3 (by rfl) ⟨267359, by rfl⟩ : syracuseStep 1425917 = 534719) (by norm_num)
theorem B1131005 : Blo 750330 1131005 := bbase (se 3 (by rfl) ⟨212063, by rfl⟩ : syracuseStep 1131005 = 424127) (by norm_num)
theorem B2146837 : Blo 750330 2146837 := bbase (se 6 (by rfl) ⟨50316, by rfl⟩ : syracuseStep 2146837 = 100633) (by norm_num)
theorem B1131029 : Blo 750330 1131029 := bbase (se 6 (by rfl) ⟨26508, by rfl⟩ : syracuseStep 1131029 = 53017) (by norm_num)
theorem B1131053 : Blo 750330 1131053 := bbase (se 3 (by rfl) ⟨212072, by rfl⟩ : syracuseStep 1131053 = 424145) (by norm_num)
theorem B1131077 : Blo 750330 1131077 := bbase (se 4 (by rfl) ⟨106038, by rfl⟩ : syracuseStep 1131077 = 212077) (by norm_num)
theorem B1131101 : Blo 750330 1131101 := bbase (se 3 (by rfl) ⟨212081, by rfl⟩ : syracuseStep 1131101 = 424163) (by norm_num)
theorem B1131125 : Blo 750330 1131125 := bbase (se 5 (by rfl) ⟨53021, by rfl⟩ : syracuseStep 1131125 = 106043) (by norm_num)
theorem B1426061 : Blo 750330 1426061 := bbase (se 3 (by rfl) ⟨267386, by rfl⟩ : syracuseStep 1426061 = 534773) (by norm_num)
theorem B1131149 : Blo 750330 1131149 := bbase (se 3 (by rfl) ⟨212090, by rfl⟩ : syracuseStep 1131149 = 424181) (by norm_num)
theorem B1131173 : Blo 750330 1131173 := bbase (se 4 (by rfl) ⟨106047, by rfl⟩ : syracuseStep 1131173 = 212095) (by norm_num)
theorem B2540213 : Blo 750330 2540213 := bbase (se 5 (by rfl) ⟨119072, by rfl⟩ : syracuseStep 2540213 = 238145) (by norm_num)
theorem B1131197 : Blo 750330 1131197 := bbase (se 3 (by rfl) ⟨212099, by rfl⟩ : syracuseStep 1131197 = 424199) (by norm_num)
theorem B1131221 : Blo 750330 1131221 := bbase (se 7 (by rfl) ⟨13256, by rfl⟩ : syracuseStep 1131221 = 26513) (by norm_num)
theorem B1131245 : Blo 750330 1131245 := bbase (se 3 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 1131245 = 424217) (by norm_num)
theorem B803569 : Blo 750330 803569 := bbase (se 2 (by rfl) ⟨301338, by rfl⟩ : syracuseStep 803569 = 602677) (by norm_num)
theorem B1688309 : Blo 750330 1688309 := bbase (se 5 (by rfl) ⟨79139, by rfl⟩ : syracuseStep 1688309 = 158279) (by norm_num)
theorem B1131269 : Blo 750330 1131269 := bbase (se 4 (by rfl) ⟨106056, by rfl⟩ : syracuseStep 1131269 = 212113) (by norm_num)
theorem B1131293 : Blo 750330 1131293 := bbase (se 3 (by rfl) ⟨212117, by rfl⟩ : syracuseStep 1131293 = 424235) (by norm_num)
theorem B803629 : Blo 750330 803629 := bbase (se 3 (by rfl) ⟨150680, by rfl⟩ : syracuseStep 803629 = 301361) (by norm_num)
theorem B1131317 : Blo 750330 1131317 := bbase (se 5 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 1131317 = 106061) (by norm_num)
theorem B1688381 : Blo 750330 1688381 := bbase (se 3 (by rfl) ⟨316571, by rfl⟩ : syracuseStep 1688381 = 633143) (by norm_num)
theorem B1131341 : Blo 750330 1131341 := bbase (se 3 (by rfl) ⟨212126, by rfl⟩ : syracuseStep 1131341 = 424253) (by norm_num)
theorem B1131365 : Blo 750330 1131365 := bbase (se 4 (by rfl) ⟨106065, by rfl⟩ : syracuseStep 1131365 = 212131) (by norm_num)
theorem B1131389 : Blo 750330 1131389 := bbase (se 3 (by rfl) ⟨212135, by rfl⟩ : syracuseStep 1131389 = 424271) (by norm_num)
theorem B1688453 : Blo 750330 1688453 := bbase (se 4 (by rfl) ⟨158292, by rfl⟩ : syracuseStep 1688453 = 316585) (by norm_num)
theorem B1131413 : Blo 750330 1131413 := bbase (se 6 (by rfl) ⟨26517, by rfl⟩ : syracuseStep 1131413 = 53035) (by norm_num)
theorem B1426349 : Blo 750330 1426349 := bbase (se 3 (by rfl) ⟨267440, by rfl⟩ : syracuseStep 1426349 = 534881) (by norm_num)
theorem B1131437 : Blo 750330 1131437 := bbase (se 3 (by rfl) ⟨212144, by rfl⟩ : syracuseStep 1131437 = 424289) (by norm_num)
theorem B1131461 : Blo 750330 1131461 := bbase (se 4 (by rfl) ⟨106074, by rfl⟩ : syracuseStep 1131461 = 212149) (by norm_num)
theorem B1688525 : Blo 750330 1688525 := bbase (se 3 (by rfl) ⟨316598, by rfl⟩ : syracuseStep 1688525 = 633197) (by norm_num)
theorem B1131485 : Blo 750330 1131485 := bbase (se 3 (by rfl) ⟨212153, by rfl⟩ : syracuseStep 1131485 = 424307) (by norm_num)
theorem B3818501 : Blo 750330 3818501 := bbase (se 4 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 3818501 = 715969) (by norm_num)
theorem B1688597 : Blo 750330 1688597 := bbase (se 6 (by rfl) ⟨39576, by rfl⟩ : syracuseStep 1688597 = 79153) (by norm_num)
theorem B902189 : Blo 750330 902189 := bbase (se 3 (by rfl) ⟨169160, by rfl⟩ : syracuseStep 902189 = 338321) (by norm_num)
theorem B1426501 : Blo 750330 1426501 := bbase (se 4 (by rfl) ⟨133734, by rfl⟩ : syracuseStep 1426501 = 267469) (by norm_num)
theorem B1688669 : Blo 750330 1688669 := bbase (se 3 (by rfl) ⟨316625, by rfl⟩ : syracuseStep 1688669 = 633251) (by norm_num)
theorem B2540645 : Blo 750330 2540645 := bbase (se 4 (by rfl) ⟨238185, by rfl⟩ : syracuseStep 2540645 = 476371) (by norm_num)
theorem B803945 : Blo 750330 803945 := bbase (se 2 (by rfl) ⟨301479, by rfl⟩ : syracuseStep 803945 = 602959) (by norm_num)
theorem B869521 : Blo 750330 869521 := bbase (se 2 (by rfl) ⟨326070, by rfl⟩ : syracuseStep 869521 = 652141) (by norm_num)
theorem B1688741 : Blo 750330 1688741 := bbase (se 4 (by rfl) ⟨158319, by rfl⟩ : syracuseStep 1688741 = 316639) (by norm_num)
theorem B3261653 : Blo 750330 3261653 := bbase (se 7 (by rfl) ⟨38222, by rfl⟩ : syracuseStep 3261653 = 76445) (by norm_num)
theorem B3622117 : Blo 750330 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B902377 : Blo 750330 902377 := bbase (se 2 (by rfl) ⟨338391, by rfl⟩ : syracuseStep 902377 = 676783) (by norm_num)
theorem B1688813 : Blo 750330 1688813 := bbase (se 3 (by rfl) ⟨316652, by rfl⟩ : syracuseStep 1688813 = 633305) (by norm_num)
theorem B1688885 : Blo 750330 1688885 := bbase (se 5 (by rfl) ⟨79166, by rfl⟩ : syracuseStep 1688885 = 158333) (by norm_num)
theorem B1426805 : Blo 750330 1426805 := bbase (se 5 (by rfl) ⟨66881, by rfl⟩ : syracuseStep 1426805 = 133763) (by norm_num)
theorem B1688957 : Blo 750330 1688957 := bbase (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) (by norm_num)
theorem B902593 : Blo 750330 902593 := bbase (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) (by norm_num)
theorem B1689029 : Blo 750330 1689029 := bbase (se 4 (by rfl) ⟨158346, by rfl⟩ : syracuseStep 1689029 = 316693) (by norm_num)
theorem B1590749 : Blo 750330 1590749 := bbase (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) (by norm_num)
theorem B1689101 : Blo 750330 1689101 := bbase (se 3 (by rfl) ⟨316706, by rfl⟩ : syracuseStep 1689101 = 633413) (by norm_num)
theorem B2541077 : Blo 750330 2541077 := bbase (se 6 (by rfl) ⟨59556, by rfl⟩ : syracuseStep 2541077 = 119113) (by norm_num)
theorem B804389 : Blo 750330 804389 := bbase (se 4 (by rfl) ⟨75411, by rfl⟩ : syracuseStep 804389 = 150823) (by norm_num)
theorem B1689173 : Blo 750330 1689173 := bbase (se 8 (by rfl) ⟨9897, by rfl⟩ : syracuseStep 1689173 = 19795) (by norm_num)
theorem B804449 : Blo 750330 804449 := bbase (se 2 (by rfl) ⟨301668, by rfl⟩ : syracuseStep 804449 = 603337) (by norm_num)
theorem B1689245 : Blo 750330 1689245 := bbase (se 3 (by rfl) ⟨316733, by rfl⟩ : syracuseStep 1689245 = 633467) (by norm_num)
theorem B1525429 : Blo 750330 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B5719733 : Blo 750330 5719733 := bbase (se 5 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 5719733 = 536225) (by norm_num)
theorem B902881 : Blo 750330 902881 := bbase (se 2 (by rfl) ⟨338580, by rfl⟩ : syracuseStep 902881 = 677161) (by norm_num)
theorem B804577 : Blo 750330 804577 := bbase (se 2 (by rfl) ⟨301716, by rfl⟩ : syracuseStep 804577 = 603433) (by norm_num)
theorem B1689317 : Blo 750330 1689317 := bbase (se 4 (by rfl) ⟨158373, by rfl⟩ : syracuseStep 1689317 = 316747) (by norm_num)
theorem B15255317 : Blo 750330 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B1689389 : Blo 750330 1689389 := bbase (se 3 (by rfl) ⟨316760, by rfl⟩ : syracuseStep 1689389 = 633521) (by norm_num)
theorem B1689461 : Blo 750330 1689461 := bbase (se 5 (by rfl) ⟨79193, by rfl⟩ : syracuseStep 1689461 = 158387) (by norm_num)
theorem B2705285 : Blo 750330 2705285 := bbase (se 4 (by rfl) ⟨253620, by rfl⟩ : syracuseStep 2705285 = 507241) (by norm_num)
theorem B1689533 : Blo 750330 1689533 := bbase (se 3 (by rfl) ⟨316787, by rfl⟩ : syracuseStep 1689533 = 633575) (by norm_num)
theorem B2541509 : Blo 750330 2541509 := bbase (se 4 (by rfl) ⟨238266, by rfl⟩ : syracuseStep 2541509 = 476533) (by norm_num)
theorem B1689605 : Blo 750330 1689605 := bbase (se 4 (by rfl) ⟨158400, by rfl⟩ : syracuseStep 1689605 = 316801) (by norm_num)
theorem B1689677 : Blo 750330 1689677 := bbase (se 3 (by rfl) ⟨316814, by rfl⟩ : syracuseStep 1689677 = 633629) (by norm_num)
theorem B1427557 : Blo 750330 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B1689749 : Blo 750330 1689749 := bbase (se 6 (by rfl) ⟨39603, by rfl⟩ : syracuseStep 1689749 = 79207) (by norm_num)
theorem B1853597 : Blo 750330 1853597 := bbase (se 3 (by rfl) ⟨347549, by rfl⟩ : syracuseStep 1853597 = 695099) (by norm_num)
theorem B805021 : Blo 750330 805021 := bbase (se 3 (by rfl) ⟨150941, by rfl⟩ : syracuseStep 805021 = 301883) (by norm_num)
theorem B1525949 : Blo 750330 1525949 := bbase (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) (by norm_num)
theorem B1689821 : Blo 750330 1689821 := bbase (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) (by norm_num)
theorem B1427701 : Blo 750330 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B805141 : Blo 750330 805141 := bbase (se 6 (by rfl) ⟨18870, by rfl⟩ : syracuseStep 805141 = 37741) (by norm_num)
theorem B1526045 : Blo 750330 1526045 := bbase (se 3 (by rfl) ⟨286133, by rfl⟩ : syracuseStep 1526045 = 572267) (by norm_num)
theorem B1689893 : Blo 750330 1689893 := bbase (se 4 (by rfl) ⟨158427, by rfl⟩ : syracuseStep 1689893 = 316855) (by norm_num)
theorem B1526077 : Blo 750330 1526077 := bbase (se 3 (by rfl) ⟨286139, by rfl⟩ : syracuseStep 1526077 = 572279) (by norm_num)
theorem B1689965 : Blo 750330 1689965 := bbase (se 3 (by rfl) ⟨316868, by rfl⟩ : syracuseStep 1689965 = 633737) (by norm_num)
theorem B2541941 : Blo 750330 2541941 := bbase (se 5 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 2541941 = 238307) (by norm_num)
theorem B1427861 : Blo 750330 1427861 := bbase (se 6 (by rfl) ⟨33465, by rfl⟩ : syracuseStep 1427861 = 66931) (by norm_num)
theorem B1690037 : Blo 750330 1690037 := bbase (se 5 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 1690037 = 158441) (by norm_num)
theorem B1690109 : Blo 750330 1690109 := bbase (se 3 (by rfl) ⟨316895, by rfl⟩ : syracuseStep 1690109 = 633791) (by norm_num)
theorem B805393 : Blo 750330 805393 := bbase (se 2 (by rfl) ⟨302022, by rfl⟩ : syracuseStep 805393 = 604045) (by norm_num)
theorem B805397 : Blo 750330 805397 := bbase (se 6 (by rfl) ⟨18876, by rfl⟩ : syracuseStep 805397 = 37753) (by norm_num)
theorem B1428005 : Blo 750330 1428005 := bbase (se 4 (by rfl) ⟨133875, by rfl⟩ : syracuseStep 1428005 = 267751) (by norm_num)
theorem B1690181 : Blo 750330 1690181 := bbase (se 4 (by rfl) ⟨158454, by rfl⟩ : syracuseStep 1690181 = 316909) (by norm_num)
theorem B1690253 : Blo 750330 1690253 := bbase (se 3 (by rfl) ⟨316922, by rfl⟩ : syracuseStep 1690253 = 633845) (by norm_num)
theorem B1690325 : Blo 750330 1690325 := bbase (se 7 (by rfl) ⟨19808, by rfl⟩ : syracuseStep 1690325 = 39617) (by norm_num)
theorem B1690397 : Blo 750330 1690397 := bbase (se 3 (by rfl) ⟨316949, by rfl⟩ : syracuseStep 1690397 = 633899) (by norm_num)
theorem B2542373 : Blo 750330 2542373 := bbase (se 4 (by rfl) ⟨238347, by rfl⟩ : syracuseStep 2542373 = 476695) (by norm_num)
theorem B1428293 : Blo 750330 1428293 := bbase (se 4 (by rfl) ⟨133902, by rfl⟩ : syracuseStep 1428293 = 267805) (by norm_num)
theorem B1526597 : Blo 750330 1526597 := bbase (se 4 (by rfl) ⟨143118, by rfl⟩ : syracuseStep 1526597 = 286237) (by norm_num)
theorem B871241 : Blo 750330 871241 := bbase (se 2 (by rfl) ⟨326715, by rfl⟩ : syracuseStep 871241 = 653431) (by norm_num)
theorem B1690469 : Blo 750330 1690469 := bbase (se 4 (by rfl) ⟨158481, by rfl⟩ : syracuseStep 1690469 = 316963) (by norm_num)
theorem B7228277 : Blo 750330 7228277 := bbase (se 5 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 7228277 = 677651) (by norm_num)
theorem B1690541 : Blo 750330 1690541 := bbase (se 3 (by rfl) ⟨316976, by rfl⟩ : syracuseStep 1690541 = 633953) (by norm_num)
theorem B1428445 : Blo 750330 1428445 := bbase (se 3 (by rfl) ⟨267833, by rfl⟩ : syracuseStep 1428445 = 535667) (by norm_num)
theorem B904169 : Blo 750330 904169 := bbase (se 2 (by rfl) ⟨339063, by rfl⟩ : syracuseStep 904169 = 678127) (by norm_num)
theorem B1690613 : Blo 750330 1690613 := bbase (se 5 (by rfl) ⟨79247, by rfl⟩ : syracuseStep 1690613 = 158495) (by norm_num)
theorem B1690685 : Blo 750330 1690685 := bbase (se 3 (by rfl) ⟨317003, by rfl⟩ : syracuseStep 1690685 = 634007) (by norm_num)
theorem B1690757 : Blo 750330 1690757 := bbase (se 4 (by rfl) ⟨158508, by rfl⟩ : syracuseStep 1690757 = 317017) (by norm_num)
theorem B2411669 : Blo 750330 2411669 := bbase (se 6 (by rfl) ⟨56523, by rfl⟩ : syracuseStep 2411669 = 113047) (by norm_num)
theorem B1690829 : Blo 750330 1690829 := bbase (se 3 (by rfl) ⟨317030, by rfl⟩ : syracuseStep 1690829 = 634061) (by norm_num)
theorem B2542805 : Blo 750330 2542805 := bbase (se 7 (by rfl) ⟨29798, by rfl⟩ : syracuseStep 2542805 = 59597) (by norm_num)
theorem B1428749 : Blo 750330 1428749 := bbase (se 3 (by rfl) ⟨267890, by rfl⟩ : syracuseStep 1428749 = 535781) (by norm_num)
theorem B1690901 : Blo 750330 1690901 := bbase (se 6 (by rfl) ⟨39630, by rfl⟩ : syracuseStep 1690901 = 79261) (by norm_num)
theorem B1690973 : Blo 750330 1690973 := bbase (se 3 (by rfl) ⟨317057, by rfl⟩ : syracuseStep 1690973 = 634115) (by norm_num)
theorem B1691045 : Blo 750330 1691045 := bbase (se 4 (by rfl) ⟨158535, by rfl⟩ : syracuseStep 1691045 = 317071) (by norm_num)
theorem B1068509 : Blo 750330 1068509 := bbase (se 3 (by rfl) ⟨200345, by rfl⟩ : syracuseStep 1068509 = 400691) (by norm_num)
theorem B1691117 : Blo 750330 1691117 := bbase (se 3 (by rfl) ⟨317084, by rfl⟩ : syracuseStep 1691117 = 634169) (by norm_num)
theorem B1068589 : Blo 750330 1068589 := bbase (se 3 (by rfl) ⟨200360, by rfl⟩ : syracuseStep 1068589 = 400721) (by norm_num)
theorem B1691189 : Blo 750330 1691189 := bbase (se 5 (by rfl) ⟨79274, by rfl⟩ : syracuseStep 1691189 = 158549) (by norm_num)
theorem B904765 : Blo 750330 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B1691261 : Blo 750330 1691261 := bbase (se 3 (by rfl) ⟨317111, by rfl⟩ : syracuseStep 1691261 = 634223) (by norm_num)
theorem B2543237 : Blo 750330 2543237 := bbase (se 4 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 2543237 = 476857) (by norm_num)
theorem B904861 : Blo 750330 904861 := bbase (se 3 (by rfl) ⟨169661, by rfl⟩ : syracuseStep 904861 = 339323) (by norm_num)
theorem B1068709 : Blo 750330 1068709 := bbase (se 4 (by rfl) ⟨100191, by rfl⟩ : syracuseStep 1068709 = 200383) (by norm_num)
theorem B3428021 : Blo 750330 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B1691333 : Blo 750330 1691333 := bbase (se 4 (by rfl) ⟨158562, by rfl⟩ : syracuseStep 1691333 = 317125) (by norm_num)
theorem B1068805 : Blo 750330 1068805 := bbase (se 4 (by rfl) ⟨100200, by rfl⟩ : syracuseStep 1068805 = 200401) (by norm_num)
theorem B1691405 : Blo 750330 1691405 := bbase (se 3 (by rfl) ⟨317138, by rfl⟩ : syracuseStep 1691405 = 634277) (by norm_num)
theorem B1691477 : Blo 750330 1691477 := bbase (se 9 (by rfl) ⟨4955, by rfl⟩ : syracuseStep 1691477 = 9911) (by norm_num)
theorem B1691549 : Blo 750330 1691549 := bbase (se 3 (by rfl) ⟨317165, by rfl⟩ : syracuseStep 1691549 = 634331) (by norm_num)
theorem B1691621 : Blo 750330 1691621 := bbase (se 4 (by rfl) ⟨158589, by rfl⟩ : syracuseStep 1691621 = 317179) (by norm_num)
theorem B1429501 : Blo 750330 1429501 := bbase (se 3 (by rfl) ⟨268031, by rfl⟩ : syracuseStep 1429501 = 536063) (by norm_num)
theorem B1691693 : Blo 750330 1691693 := bbase (se 3 (by rfl) ⟨317192, by rfl⟩ : syracuseStep 1691693 = 634385) (by norm_num)
theorem B2543669 : Blo 750330 2543669 := bbase (se 5 (by rfl) ⟨119234, by rfl⟩ : syracuseStep 2543669 = 238469) (by norm_num)
theorem B1691765 : Blo 750330 1691765 := bbase (se 5 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 1691765 = 158603) (by norm_num)
theorem B1429645 : Blo 750330 1429645 := bbase (se 3 (by rfl) ⟨268058, by rfl⟩ : syracuseStep 1429645 = 536117) (by norm_num)
theorem B1691837 : Blo 750330 1691837 := bbase (se 3 (by rfl) ⟨317219, by rfl⟩ : syracuseStep 1691837 = 634439) (by norm_num)
theorem B2412757 : Blo 750330 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B1069301 : Blo 750330 1069301 := bbase (se 5 (by rfl) ⟨50123, by rfl⟩ : syracuseStep 1069301 = 100247) (by norm_num)
theorem B1691909 : Blo 750330 1691909 := bbase (se 4 (by rfl) ⟨158616, by rfl⟩ : syracuseStep 1691909 = 317233) (by norm_num)
theorem B4280597 : Blo 750330 4280597 := bbase (se 6 (by rfl) ⟨100326, by rfl⟩ : syracuseStep 4280597 = 200653) (by norm_num)
theorem B1429805 : Blo 750330 1429805 := bbase (se 3 (by rfl) ⟨268088, by rfl⟩ : syracuseStep 1429805 = 536177) (by norm_num)
theorem B1691981 : Blo 750330 1691981 := bbase (se 3 (by rfl) ⟨317246, by rfl⟩ : syracuseStep 1691981 = 634493) (by norm_num)
theorem B1692053 : Blo 750330 1692053 := bbase (se 6 (by rfl) ⟨39657, by rfl⟩ : syracuseStep 1692053 = 79315) (by norm_num)
theorem B1429949 : Blo 750330 1429949 := bbase (se 3 (by rfl) ⟨268115, by rfl⟩ : syracuseStep 1429949 = 536231) (by norm_num)
theorem B1692125 : Blo 750330 1692125 := bbase (se 3 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 1692125 = 634547) (by norm_num)
theorem B2544101 : Blo 750330 2544101 := bbase (se 4 (by rfl) ⟨238509, by rfl⟩ : syracuseStep 2544101 = 477019) (by norm_num)
theorem B1266205 : Blo 750330 1266205 := bbase (se 3 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 1266205 = 474827) (by norm_num)
theorem B1692197 : Blo 750330 1692197 := bbase (se 4 (by rfl) ⟨158643, by rfl⟩ : syracuseStep 1692197 = 317287) (by norm_num)
theorem B1692269 : Blo 750330 1692269 := bbase (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) (by norm_num)
theorem B1266293 : Blo 750330 1266293 := bbase (se 5 (by rfl) ⟨59357, by rfl⟩ : syracuseStep 1266293 = 118715) (by norm_num)
theorem B1692341 : Blo 750330 1692341 := bbase (se 5 (by rfl) ⟨79328, by rfl⟩ : syracuseStep 1692341 = 158657) (by norm_num)
theorem B1430237 : Blo 750330 1430237 := bbase (se 3 (by rfl) ⟨268169, by rfl⟩ : syracuseStep 1430237 = 536339) (by norm_num)
theorem B1266421 : Blo 750330 1266421 := bbase (se 5 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 1266421 = 118727) (by norm_num)
theorem B1692413 : Blo 750330 1692413 := bbase (se 3 (by rfl) ⟨317327, by rfl⟩ : syracuseStep 1692413 = 634655) (by norm_num)
theorem B906005 : Blo 750330 906005 := bbase (se 6 (by rfl) ⟨21234, by rfl⟩ : syracuseStep 906005 = 42469) (by norm_num)
theorem B1069853 : Blo 750330 1069853 := bbase (se 3 (by rfl) ⟨200597, by rfl⟩ : syracuseStep 1069853 = 401195) (by norm_num)
theorem B1692485 : Blo 750330 1692485 := bbase (se 4 (by rfl) ⟨158670, by rfl⟩ : syracuseStep 1692485 = 317341) (by norm_num)
theorem B1266509 : Blo 750330 1266509 := bbase (se 3 (by rfl) ⟨237470, by rfl⟩ : syracuseStep 1266509 = 474941) (by norm_num)
theorem B1430389 : Blo 750330 1430389 := bbase (se 5 (by rfl) ⟨67049, by rfl⟩ : syracuseStep 1430389 = 134099) (by norm_num)
theorem B2511749 : Blo 750330 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B1692557 : Blo 750330 1692557 := bbase (se 3 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 1692557 = 634709) (by norm_num)
theorem B2544533 : Blo 750330 2544533 := bbase (se 6 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 2544533 = 119275) (by norm_num)
theorem B1266637 : Blo 750330 1266637 := bbase (se 3 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 1266637 = 474989) (by norm_num)
theorem B1692629 : Blo 750330 1692629 := bbase (se 7 (by rfl) ⟨19835, by rfl⟩ : syracuseStep 1692629 = 39671) (by norm_num)
theorem B1692701 : Blo 750330 1692701 := bbase (se 3 (by rfl) ⟨317381, by rfl⟩ : syracuseStep 1692701 = 634763) (by norm_num)
theorem B1266725 : Blo 750330 1266725 := bbase (se 4 (by rfl) ⟨118755, by rfl⟩ : syracuseStep 1266725 = 237511) (by norm_num)
theorem B2282597 : Blo 750330 2282597 := bbase (se 4 (by rfl) ⟨213993, by rfl⟩ : syracuseStep 2282597 = 427987) (by norm_num)
theorem B1692773 : Blo 750330 1692773 := bbase (se 4 (by rfl) ⟨158697, by rfl⟩ : syracuseStep 1692773 = 317395) (by norm_num)
theorem B1266853 : Blo 750330 1266853 := bbase (se 4 (by rfl) ⟨118767, by rfl⟩ : syracuseStep 1266853 = 237535) (by norm_num)
theorem B1430693 : Blo 750330 1430693 := bbase (se 4 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 1430693 = 268255) (by norm_num)
theorem B1692845 : Blo 750330 1692845 := bbase (se 3 (by rfl) ⟨317408, by rfl⟩ : syracuseStep 1692845 = 634817) (by norm_num)
theorem B1692917 : Blo 750330 1692917 := bbase (se 5 (by rfl) ⟨79355, by rfl⟩ : syracuseStep 1692917 = 158711) (by norm_num)
theorem B1266941 : Blo 750330 1266941 := bbase (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) (by norm_num)
theorem B1692989 : Blo 750330 1692989 := bbase (se 3 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 1692989 = 634871) (by norm_num)
theorem B2544965 : Blo 750330 2544965 := bbase (se 4 (by rfl) ⟨238590, by rfl⟩ : syracuseStep 2544965 = 477181) (by norm_num)
theorem B2413925 : Blo 750330 2413925 := bbase (se 4 (by rfl) ⟨226305, by rfl⟩ : syracuseStep 2413925 = 452611) (by norm_num)
theorem B1267069 : Blo 750330 1267069 := bbase (se 3 (by rfl) ⟨237575, by rfl⟩ : syracuseStep 1267069 = 475151) (by norm_num)
theorem B1693061 : Blo 750330 1693061 := bbase (se 4 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 1693061 = 317449) (by norm_num)
theorem B4281781 : Blo 750330 4281781 := bbase (se 5 (by rfl) ⟨200708, by rfl⟩ : syracuseStep 4281781 = 401417) (by norm_num)
theorem B1693133 : Blo 750330 1693133 := bbase (se 3 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 1693133 = 634925) (by norm_num)
theorem B1267157 : Blo 750330 1267157 := bbase (se 7 (by rfl) ⟨14849, by rfl⟩ : syracuseStep 1267157 = 29699) (by norm_num)
theorem B1070605 : Blo 750330 1070605 := bbase (se 3 (by rfl) ⟨200738, by rfl⟩ : syracuseStep 1070605 = 401477) (by norm_num)
theorem B1693205 : Blo 750330 1693205 := bbase (se 6 (by rfl) ⟨39684, by rfl⟩ : syracuseStep 1693205 = 79369) (by norm_num)
theorem B1267285 : Blo 750330 1267285 := bbase (se 8 (by rfl) ⟨7425, by rfl⟩ : syracuseStep 1267285 = 14851) (by norm_num)
theorem B1693277 : Blo 750330 1693277 := bbase (se 3 (by rfl) ⟨317489, by rfl⟩ : syracuseStep 1693277 = 634979) (by norm_num)
theorem B1693349 : Blo 750330 1693349 := bbase (se 4 (by rfl) ⟨158751, by rfl⟩ : syracuseStep 1693349 = 317503) (by norm_num)
theorem B1267373 : Blo 750330 1267373 := bbase (se 3 (by rfl) ⟨237632, by rfl⟩ : syracuseStep 1267373 = 475265) (by norm_num)
theorem B1693421 : Blo 750330 1693421 := bbase (se 3 (by rfl) ⟨317516, by rfl⟩ : syracuseStep 1693421 = 635033) (by norm_num)
theorem B2545397 : Blo 750330 2545397 := bbase (se 5 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 2545397 = 238631) (by norm_num)
theorem B1267501 : Blo 750330 1267501 := bbase (se 3 (by rfl) ⟨237656, by rfl⟩ : syracuseStep 1267501 = 475313) (by norm_num)
theorem B1693493 : Blo 750330 1693493 := bbase (se 5 (by rfl) ⟨79382, by rfl⟩ : syracuseStep 1693493 = 158765) (by norm_num)
theorem B1693565 : Blo 750330 1693565 := bbase (se 3 (by rfl) ⟨317543, by rfl⟩ : syracuseStep 1693565 = 635087) (by norm_num)
theorem B1267589 : Blo 750330 1267589 := bbase (se 4 (by rfl) ⟨118836, by rfl⟩ : syracuseStep 1267589 = 237673) (by norm_num)
theorem B1431445 : Blo 750330 1431445 := bbase (se 6 (by rfl) ⟨33549, by rfl⟩ : syracuseStep 1431445 = 67099) (by norm_num)
theorem B1693637 : Blo 750330 1693637 := bbase (se 4 (by rfl) ⟨158778, by rfl⟩ : syracuseStep 1693637 = 317557) (by norm_num)
theorem B1267717 : Blo 750330 1267717 := bbase (se 4 (by rfl) ⟨118848, by rfl⟩ : syracuseStep 1267717 = 237697) (by norm_num)
theorem B1693709 : Blo 750330 1693709 := bbase (se 3 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 1693709 = 635141) (by norm_num)
theorem B1431589 : Blo 750330 1431589 := bbase (se 4 (by rfl) ⟨134211, by rfl⟩ : syracuseStep 1431589 = 268423) (by norm_num)
theorem B1693781 : Blo 750330 1693781 := bbase (se 8 (by rfl) ⟨9924, by rfl⟩ : syracuseStep 1693781 = 19849) (by norm_num)
theorem B1267805 : Blo 750330 1267805 := bbase (se 3 (by rfl) ⟨237713, by rfl⟩ : syracuseStep 1267805 = 475427) (by norm_num)
theorem B1693853 : Blo 750330 1693853 := bbase (se 3 (by rfl) ⟨317597, by rfl⟩ : syracuseStep 1693853 = 635195) (by norm_num)
theorem B2545829 : Blo 750330 2545829 := bbase (se 4 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 2545829 = 477343) (by norm_num)
theorem B1431749 : Blo 750330 1431749 := bbase (se 4 (by rfl) ⟨134226, by rfl⟩ : syracuseStep 1431749 = 268453) (by norm_num)
theorem B1202381 : Blo 750330 1202381 := bbase (se 3 (by rfl) ⟨225446, by rfl⟩ : syracuseStep 1202381 = 450893) (by norm_num)
theorem B1267933 : Blo 750330 1267933 := bbase (se 3 (by rfl) ⟨237737, by rfl⟩ : syracuseStep 1267933 = 475475) (by norm_num)
theorem B1693925 : Blo 750330 1693925 := bbase (se 4 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 1693925 = 317611) (by norm_num)
theorem B1071397 : Blo 750330 1071397 := bbase (se 4 (by rfl) ⟨100443, by rfl⟩ : syracuseStep 1071397 = 200887) (by norm_num)
theorem B1693997 : Blo 750330 1693997 := bbase (se 3 (by rfl) ⟨317624, by rfl⟩ : syracuseStep 1693997 = 635249) (by norm_num)
theorem B1268021 : Blo 750330 1268021 := bbase (se 5 (by rfl) ⟨59438, by rfl⟩ : syracuseStep 1268021 = 118877) (by norm_num)
theorem B18340181 : Blo 750330 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B1431893 : Blo 750330 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B1694069 : Blo 750330 1694069 := bbase (se 5 (by rfl) ⟨79409, by rfl⟩ : syracuseStep 1694069 = 158819) (by norm_num)
theorem B1202573 : Blo 750330 1202573 := bbase (se 3 (by rfl) ⟨225482, by rfl⟩ : syracuseStep 1202573 = 450965) (by norm_num)
theorem B1268149 : Blo 750330 1268149 := bbase (se 5 (by rfl) ⟨59444, by rfl⟩ : syracuseStep 1268149 = 118889) (by norm_num)
theorem B1694141 : Blo 750330 1694141 := bbase (se 3 (by rfl) ⟨317651, by rfl⟩ : syracuseStep 1694141 = 635303) (by norm_num)
theorem B1694213 : Blo 750330 1694213 := bbase (se 4 (by rfl) ⟨158832, by rfl⟩ : syracuseStep 1694213 = 317665) (by norm_num)
theorem B1268237 : Blo 750330 1268237 := bbase (se 3 (by rfl) ⟨237794, by rfl⟩ : syracuseStep 1268237 = 475589) (by norm_num)
theorem B2447941 : Blo 750330 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B1694285 : Blo 750330 1694285 := bbase (se 3 (by rfl) ⟨317678, by rfl⟩ : syracuseStep 1694285 = 635357) (by norm_num)
theorem B1071733 : Blo 750330 1071733 := bbase (se 5 (by rfl) ⟨50237, by rfl⟩ : syracuseStep 1071733 = 100475) (by norm_num)
theorem B1268365 : Blo 750330 1268365 := bbase (se 3 (by rfl) ⟨237818, by rfl⟩ : syracuseStep 1268365 = 475637) (by norm_num)
theorem B1694357 : Blo 750330 1694357 := bbase (se 6 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 1694357 = 79423) (by norm_num)
theorem B1694429 : Blo 750330 1694429 := bbase (se 3 (by rfl) ⟨317705, by rfl⟩ : syracuseStep 1694429 = 635411) (by norm_num)
theorem B1268453 : Blo 750330 1268453 := bbase (se 4 (by rfl) ⟨118917, by rfl⟩ : syracuseStep 1268453 = 237835) (by norm_num)
theorem B9132821 : Blo 750330 9132821 := bbase (se 6 (by rfl) ⟨214050, by rfl⟩ : syracuseStep 9132821 = 428101) (by norm_num)
theorem B1694501 : Blo 750330 1694501 := bbase (se 4 (by rfl) ⟨158859, by rfl⟩ : syracuseStep 1694501 = 317719) (by norm_num)
theorem B1071949 : Blo 750330 1071949 := bbase (se 3 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 1071949 = 401981) (by norm_num)
theorem B1268581 : Blo 750330 1268581 := bbase (se 4 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 1268581 = 237859) (by norm_num)
theorem B1694573 : Blo 750330 1694573 := bbase (se 3 (by rfl) ⟨317732, by rfl⟩ : syracuseStep 1694573 = 635465) (by norm_num)
theorem B1694645 : Blo 750330 1694645 := bbase (se 5 (by rfl) ⟨79436, by rfl⟩ : syracuseStep 1694645 = 158873) (by norm_num)
theorem B1268669 : Blo 750330 1268669 := bbase (se 3 (by rfl) ⟨237875, by rfl⟩ : syracuseStep 1268669 = 475751) (by norm_num)
theorem B1694717 : Blo 750330 1694717 := bbase (se 3 (by rfl) ⟨317759, by rfl⟩ : syracuseStep 1694717 = 635519) (by norm_num)
theorem B1268797 : Blo 750330 1268797 := bbase (se 3 (by rfl) ⟨237899, by rfl⟩ : syracuseStep 1268797 = 475799) (by norm_num)
theorem B1694789 : Blo 750330 1694789 := bbase (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) (by norm_num)
theorem B1694861 : Blo 750330 1694861 := bbase (se 3 (by rfl) ⟨317786, by rfl⟩ : syracuseStep 1694861 = 635573) (by norm_num)
theorem B1268885 : Blo 750330 1268885 := bbase (se 6 (by rfl) ⟨29739, by rfl⟩ : syracuseStep 1268885 = 59479) (by norm_num)
theorem B2415781 : Blo 750330 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1072325 : Blo 750330 1072325 := bbase (se 4 (by rfl) ⟨100530, by rfl⟩ : syracuseStep 1072325 = 201061) (by norm_num)
theorem B1694933 : Blo 750330 1694933 := bbase (se 7 (by rfl) ⟨19862, by rfl⟩ : syracuseStep 1694933 = 39725) (by norm_num)
theorem B1269013 : Blo 750330 1269013 := bbase (se 6 (by rfl) ⟨29742, by rfl⟩ : syracuseStep 1269013 = 59485) (by norm_num)
theorem B1695005 : Blo 750330 1695005 := bbase (se 3 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 1695005 = 635627) (by norm_num)
theorem B1695077 : Blo 750330 1695077 := bbase (se 4 (by rfl) ⟨158913, by rfl⟩ : syracuseStep 1695077 = 317827) (by norm_num)
theorem B1269101 : Blo 750330 1269101 := bbase (se 3 (by rfl) ⟨237956, by rfl⟩ : syracuseStep 1269101 = 475913) (by norm_num)
theorem B4283765 : Blo 750330 4283765 := bbase (se 5 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 4283765 = 401603) (by norm_num)
theorem B3431813 : Blo 750330 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B1695149 : Blo 750330 1695149 := bbase (se 3 (by rfl) ⟨317840, by rfl⟩ : syracuseStep 1695149 = 635681) (by norm_num)
theorem B3431909 : Blo 750330 3431909 := bbase (se 4 (by rfl) ⟨321741, by rfl⟩ : syracuseStep 3431909 = 643483) (by norm_num)
theorem B1269229 : Blo 750330 1269229 := bbase (se 3 (by rfl) ⟨237980, by rfl⟩ : syracuseStep 1269229 = 475961) (by norm_num)
theorem B1695221 : Blo 750330 1695221 := bbase (se 5 (by rfl) ⟨79463, by rfl⟩ : syracuseStep 1695221 = 158927) (by norm_num)
theorem B1695293 : Blo 750330 1695293 := bbase (se 3 (by rfl) ⟨317867, by rfl⟩ : syracuseStep 1695293 = 635735) (by norm_num)
theorem B1269317 : Blo 750330 1269317 := bbase (se 4 (by rfl) ⟨118998, by rfl⟩ : syracuseStep 1269317 = 237997) (by norm_num)
theorem B1695365 : Blo 750330 1695365 := bbase (se 4 (by rfl) ⟨158940, by rfl⟩ : syracuseStep 1695365 = 317881) (by norm_num)
theorem B1203893 : Blo 750330 1203893 := bbase (se 5 (by rfl) ⟨56432, by rfl⟩ : syracuseStep 1203893 = 112865) (by norm_num)
theorem B1269445 : Blo 750330 1269445 := bbase (se 4 (by rfl) ⟨119010, by rfl⟩ : syracuseStep 1269445 = 238021) (by norm_num)
theorem B1695437 : Blo 750330 1695437 := bbase (se 3 (by rfl) ⟨317894, by rfl⟩ : syracuseStep 1695437 = 635789) (by norm_num)
theorem B1695509 : Blo 750330 1695509 := bbase (se 6 (by rfl) ⟨39738, by rfl⟩ : syracuseStep 1695509 = 79477) (by norm_num)
theorem B1203989 : Blo 750330 1203989 := bbase (se 6 (by rfl) ⟨28218, by rfl⟩ : syracuseStep 1203989 = 56437) (by norm_num)
theorem B1269533 : Blo 750330 1269533 := bbase (se 3 (by rfl) ⟨238037, by rfl⟩ : syracuseStep 1269533 = 476075) (by norm_num)
theorem B1204021 : Blo 750330 1204021 := bbase (se 5 (by rfl) ⟨56438, by rfl⟩ : syracuseStep 1204021 = 112877) (by norm_num)
theorem B1630037 : Blo 750330 1630037 := bbase (se 9 (by rfl) ⟨4775, by rfl⟩ : syracuseStep 1630037 = 9551) (by norm_num)
theorem B1695581 : Blo 750330 1695581 := bbase (se 3 (by rfl) ⟨317921, by rfl⟩ : syracuseStep 1695581 = 635843) (by norm_num)
theorem B1269661 : Blo 750330 1269661 := bbase (se 3 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 1269661 = 476123) (by norm_num)
theorem B1695653 : Blo 750330 1695653 := bbase (se 4 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 1695653 = 317935) (by norm_num)
theorem B1695725 : Blo 750330 1695725 := bbase (se 3 (by rfl) ⟨317948, by rfl⟩ : syracuseStep 1695725 = 635897) (by norm_num)
theorem B1269749 : Blo 750330 1269749 := bbase (se 5 (by rfl) ⟨59519, by rfl⟩ : syracuseStep 1269749 = 119039) (by norm_num)
theorem B1695797 : Blo 750330 1695797 := bbase (se 5 (by rfl) ⟨79490, by rfl⟩ : syracuseStep 1695797 = 158981) (by norm_num)
theorem B1269877 : Blo 750330 1269877 := bbase (se 5 (by rfl) ⟨59525, by rfl⟩ : syracuseStep 1269877 = 119051) (by norm_num)
theorem B1695869 : Blo 750330 1695869 := bbase (se 3 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 1695869 = 635951) (by norm_num)
theorem B1695941 : Blo 750330 1695941 := bbase (se 4 (by rfl) ⟨158994, by rfl⟩ : syracuseStep 1695941 = 317989) (by norm_num)
theorem B1269965 : Blo 750330 1269965 := bbase (se 3 (by rfl) ⟨238118, by rfl⟩ : syracuseStep 1269965 = 476237) (by norm_num)
theorem B1696013 : Blo 750330 1696013 := bbase (se 3 (by rfl) ⟨318002, by rfl⟩ : syracuseStep 1696013 = 636005) (by norm_num)
theorem B1270093 : Blo 750330 1270093 := bbase (se 3 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 1270093 = 476285) (by norm_num)
theorem B1696085 : Blo 750330 1696085 := bbase (se 10 (by rfl) ⟨2484, by rfl⟩ : syracuseStep 1696085 = 4969) (by norm_num)
theorem B844141 : Blo 750330 844141 := bbase (se 3 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 844141 = 316553) (by norm_num)
theorem B844177 : Blo 750330 844177 := bbase (se 2 (by rfl) ⟨316566, by rfl⟩ : syracuseStep 844177 = 633133) (by norm_num)
theorem B1696157 : Blo 750330 1696157 := bbase (se 3 (by rfl) ⟨318029, by rfl⟩ : syracuseStep 1696157 = 636059) (by norm_num)
theorem B1270181 : Blo 750330 1270181 := bbase (se 4 (by rfl) ⟨119079, by rfl⟩ : syracuseStep 1270181 = 238159) (by norm_num)
theorem B844213 : Blo 750330 844213 := bbase (se 5 (by rfl) ⟨39572, by rfl⟩ : syracuseStep 844213 = 79145) (by norm_num)
theorem B844249 : Blo 750330 844249 := bbase (se 2 (by rfl) ⟨316593, by rfl⟩ : syracuseStep 844249 = 633187) (by norm_num)
theorem B1696229 : Blo 750330 1696229 := bbase (se 4 (by rfl) ⟨159021, by rfl⟩ : syracuseStep 1696229 = 318043) (by norm_num)
theorem B844285 : Blo 750330 844285 := bbase (se 3 (by rfl) ⟨158303, by rfl⟩ : syracuseStep 844285 = 316607) (by norm_num)
theorem B844321 : Blo 750330 844321 := bbase (se 2 (by rfl) ⟨316620, by rfl⟩ : syracuseStep 844321 = 633241) (by norm_num)
theorem B1270309 : Blo 750330 1270309 := bbase (se 4 (by rfl) ⟨119091, by rfl⟩ : syracuseStep 1270309 = 238183) (by norm_num)
theorem B1696301 : Blo 750330 1696301 := bbase (se 3 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 1696301 = 636113) (by norm_num)
theorem B844357 : Blo 750330 844357 := bbase (se 4 (by rfl) ⟨79158, by rfl⟩ : syracuseStep 844357 = 158317) (by norm_num)
theorem B1073749 : Blo 750330 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B844393 : Blo 750330 844393 := bbase (se 2 (by rfl) ⟨316647, by rfl⟩ : syracuseStep 844393 = 633295) (by norm_num)
theorem B1696373 : Blo 750330 1696373 := bbase (se 5 (by rfl) ⟨79517, by rfl⟩ : syracuseStep 1696373 = 159035) (by norm_num)
theorem B1270397 : Blo 750330 1270397 := bbase (se 3 (by rfl) ⟨238199, by rfl⟩ : syracuseStep 1270397 = 476399) (by norm_num)
theorem B844429 : Blo 750330 844429 := bbase (se 3 (by rfl) ⟨158330, by rfl⟩ : syracuseStep 844429 = 316661) (by norm_num)
theorem B844465 : Blo 750330 844465 := bbase (se 2 (by rfl) ⟨316674, by rfl⟩ : syracuseStep 844465 = 633349) (by norm_num)
theorem B1696445 : Blo 750330 1696445 := bbase (se 3 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 1696445 = 636167) (by norm_num)
theorem B844501 : Blo 750330 844501 := bbase (se 7 (by rfl) ⟨9896, by rfl⟩ : syracuseStep 844501 = 19793) (by norm_num)
theorem B6087413 : Blo 750330 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B844537 : Blo 750330 844537 := bbase (se 2 (by rfl) ⟨316701, by rfl⟩ : syracuseStep 844537 = 633403) (by norm_num)
theorem B1270525 : Blo 750330 1270525 := bbase (se 3 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 1270525 = 476447) (by norm_num)
theorem B1696517 : Blo 750330 1696517 := bbase (se 4 (by rfl) ⟨159048, by rfl⟩ : syracuseStep 1696517 = 318097) (by norm_num)
theorem B844573 : Blo 750330 844573 := bbase (se 3 (by rfl) ⟨158357, by rfl⟩ : syracuseStep 844573 = 316715) (by norm_num)
theorem B844609 : Blo 750330 844609 := bbase (se 2 (by rfl) ⟨316728, by rfl⟩ : syracuseStep 844609 = 633457) (by norm_num)
theorem B1696589 : Blo 750330 1696589 := bbase (se 3 (by rfl) ⟨318110, by rfl⟩ : syracuseStep 1696589 = 636221) (by norm_num)
theorem B1270613 : Blo 750330 1270613 := bbase (se 9 (by rfl) ⟨3722, by rfl⟩ : syracuseStep 1270613 = 7445) (by norm_num)
theorem B844645 : Blo 750330 844645 := bbase (se 4 (by rfl) ⟨79185, by rfl⟩ : syracuseStep 844645 = 158371) (by norm_num)
theorem B844681 : Blo 750330 844681 := bbase (se 2 (by rfl) ⟨316755, by rfl⟩ : syracuseStep 844681 = 633511) (by norm_num)
theorem B1696661 : Blo 750330 1696661 := bbase (se 6 (by rfl) ⟨39765, by rfl⟩ : syracuseStep 1696661 = 79531) (by norm_num)
theorem B844717 : Blo 750330 844717 := bbase (se 3 (by rfl) ⟨158384, by rfl⟩ : syracuseStep 844717 = 316769) (by norm_num)
theorem B844753 : Blo 750330 844753 := bbase (se 2 (by rfl) ⟨316782, by rfl⟩ : syracuseStep 844753 = 633565) (by norm_num)
theorem B1270741 : Blo 750330 1270741 := bbase (se 7 (by rfl) ⟨14891, by rfl⟩ : syracuseStep 1270741 = 29783) (by norm_num)
theorem B1696733 : Blo 750330 1696733 := bbase (se 3 (by rfl) ⟨318137, by rfl⟩ : syracuseStep 1696733 = 636275) (by norm_num)
theorem B844789 : Blo 750330 844789 := bbase (se 5 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 844789 = 79199) (by norm_num)
theorem B844825 : Blo 750330 844825 := bbase (se 2 (by rfl) ⟨316809, by rfl⟩ : syracuseStep 844825 = 633619) (by norm_num)
theorem B1696805 : Blo 750330 1696805 := bbase (se 4 (by rfl) ⟨159075, by rfl⟩ : syracuseStep 1696805 = 318151) (by norm_num)
theorem B1270829 : Blo 750330 1270829 := bbase (se 3 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 1270829 = 476561) (by norm_num)
theorem B844861 : Blo 750330 844861 := bbase (se 3 (by rfl) ⟨158411, by rfl⟩ : syracuseStep 844861 = 316823) (by norm_num)
theorem B844897 : Blo 750330 844897 := bbase (se 2 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 844897 = 633673) (by norm_num)
theorem B1696877 : Blo 750330 1696877 := bbase (se 3 (by rfl) ⟨318164, by rfl⟩ : syracuseStep 1696877 = 636329) (by norm_num)
theorem B844933 : Blo 750330 844933 := bbase (se 4 (by rfl) ⟨79212, by rfl⟩ : syracuseStep 844933 = 158425) (by norm_num)
theorem B844969 : Blo 750330 844969 := bbase (se 2 (by rfl) ⟨316863, by rfl⟩ : syracuseStep 844969 = 633727) (by norm_num)
theorem B1270957 : Blo 750330 1270957 := bbase (se 3 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 1270957 = 476609) (by norm_num)
theorem B1696949 : Blo 750330 1696949 := bbase (se 5 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 1696949 = 159089) (by norm_num)
theorem B845005 : Blo 750330 845005 := bbase (se 3 (by rfl) ⟨158438, by rfl⟩ : syracuseStep 845005 = 316877) (by norm_num)
theorem B845041 : Blo 750330 845041 := bbase (se 2 (by rfl) ⟨316890, by rfl⟩ : syracuseStep 845041 = 633781) (by norm_num)
theorem B1697021 : Blo 750330 1697021 := bbase (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) (by norm_num)
theorem B1271045 : Blo 750330 1271045 := bbase (se 4 (by rfl) ⟨119160, by rfl⟩ : syracuseStep 1271045 = 238321) (by norm_num)
theorem B845077 : Blo 750330 845077 := bbase (se 6 (by rfl) ⟨19806, by rfl⟩ : syracuseStep 845077 = 39613) (by norm_num)
theorem B5727509 : Blo 750330 5727509 := bbase (se 6 (by rfl) ⟨134238, by rfl⟩ : syracuseStep 5727509 = 268477) (by norm_num)
theorem B1205533 : Blo 750330 1205533 := bbase (se 3 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 1205533 = 452075) (by norm_num)
theorem B845113 : Blo 750330 845113 := bbase (se 2 (by rfl) ⟨316917, by rfl⟩ : syracuseStep 845113 = 633835) (by norm_num)
theorem B1697093 : Blo 750330 1697093 := bbase (se 4 (by rfl) ⟨159102, by rfl⟩ : syracuseStep 1697093 = 318205) (by norm_num)
theorem B845149 : Blo 750330 845149 := bbase (se 3 (by rfl) ⟨158465, by rfl⟩ : syracuseStep 845149 = 316931) (by norm_num)
theorem B845185 : Blo 750330 845185 := bbase (se 2 (by rfl) ⟨316944, by rfl⟩ : syracuseStep 845185 = 633889) (by norm_num)
theorem B1271173 : Blo 750330 1271173 := bbase (se 4 (by rfl) ⟨119172, by rfl⟩ : syracuseStep 1271173 = 238345) (by norm_num)
theorem B1697165 : Blo 750330 1697165 := bbase (se 3 (by rfl) ⟨318218, by rfl⟩ : syracuseStep 1697165 = 636437) (by norm_num)
theorem B845221 : Blo 750330 845221 := bbase (se 4 (by rfl) ⟨79239, by rfl⟩ : syracuseStep 845221 = 158479) (by norm_num)
theorem B845257 : Blo 750330 845257 := bbase (se 2 (by rfl) ⟨316971, by rfl⟩ : syracuseStep 845257 = 633943) (by norm_num)
theorem B1697237 : Blo 750330 1697237 := bbase (se 7 (by rfl) ⟨19889, by rfl⟩ : syracuseStep 1697237 = 39779) (by norm_num)
theorem B1271261 : Blo 750330 1271261 := bbase (se 3 (by rfl) ⟨238361, by rfl⟩ : syracuseStep 1271261 = 476723) (by norm_num)
theorem B845293 : Blo 750330 845293 := bbase (se 3 (by rfl) ⟨158492, by rfl⟩ : syracuseStep 845293 = 316985) (by norm_num)
theorem B845329 : Blo 750330 845329 := bbase (se 2 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 845329 = 633997) (by norm_num)
theorem B4285973 : Blo 750330 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B845365 : Blo 750330 845365 := bbase (se 5 (by rfl) ⟨39626, by rfl⟩ : syracuseStep 845365 = 79253) (by norm_num)
theorem B1631821 : Blo 750330 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B845401 : Blo 750330 845401 := bbase (se 2 (by rfl) ⟨317025, by rfl⟩ : syracuseStep 845401 = 634051) (by norm_num)
theorem B1271389 : Blo 750330 1271389 := bbase (se 3 (by rfl) ⟨238385, by rfl⟩ : syracuseStep 1271389 = 476771) (by norm_num)
theorem B845437 : Blo 750330 845437 := bbase (se 3 (by rfl) ⟨158519, by rfl⟩ : syracuseStep 845437 = 317039) (by norm_num)
theorem B845473 : Blo 750330 845473 := bbase (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) (by norm_num)
theorem B1271477 : Blo 750330 1271477 := bbase (se 5 (by rfl) ⟨59600, by rfl⟩ : syracuseStep 1271477 = 119201) (by norm_num)
theorem B845509 : Blo 750330 845509 := bbase (se 4 (by rfl) ⟨79266, by rfl⟩ : syracuseStep 845509 = 158533) (by norm_num)
theorem B845545 : Blo 750330 845545 := bbase (se 2 (by rfl) ⟨317079, by rfl⟩ : syracuseStep 845545 = 634159) (by norm_num)
theorem B1173253 : Blo 750330 1173253 := bbase (se 4 (by rfl) ⟨109992, by rfl⟩ : syracuseStep 1173253 = 219985) (by norm_num)
theorem B845581 : Blo 750330 845581 := bbase (se 3 (by rfl) ⟨158546, by rfl⟩ : syracuseStep 845581 = 317093) (by norm_num)
theorem B845617 : Blo 750330 845617 := bbase (se 2 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 845617 = 634213) (by norm_num)
theorem B1271605 : Blo 750330 1271605 := bbase (se 5 (by rfl) ⟨59606, by rfl⟩ : syracuseStep 1271605 = 119213) (by norm_num)
theorem B845653 : Blo 750330 845653 := bbase (se 9 (by rfl) ⟨2477, by rfl⟩ : syracuseStep 845653 = 4955) (by norm_num)
theorem B2713429 : Blo 750330 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B845689 : Blo 750330 845689 := bbase (se 2 (by rfl) ⟨317133, by rfl⟩ : syracuseStep 845689 = 634267) (by norm_num)
theorem B1271693 : Blo 750330 1271693 := bbase (se 3 (by rfl) ⟨238442, by rfl⟩ : syracuseStep 1271693 = 476885) (by norm_num)
theorem B845725 : Blo 750330 845725 := bbase (se 3 (by rfl) ⟨158573, by rfl⟩ : syracuseStep 845725 = 317147) (by norm_num)
theorem B3860405 : Blo 750330 3860405 := bbase (se 5 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 3860405 = 361913) (by norm_num)
theorem B845761 : Blo 750330 845761 := bbase (se 2 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 845761 = 634321) (by norm_num)
theorem B845797 : Blo 750330 845797 := bbase (se 4 (by rfl) ⟨79293, by rfl⟩ : syracuseStep 845797 = 158587) (by norm_num)
theorem B1206245 : Blo 750330 1206245 := bbase (se 4 (by rfl) ⟨113085, by rfl⟩ : syracuseStep 1206245 = 226171) (by norm_num)
theorem B2713589 : Blo 750330 2713589 := bbase (se 5 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 2713589 = 254399) (by norm_num)
theorem B845833 : Blo 750330 845833 := bbase (se 2 (by rfl) ⟨317187, by rfl⟩ : syracuseStep 845833 = 634375) (by norm_num)
theorem B1271821 : Blo 750330 1271821 := bbase (se 3 (by rfl) ⟨238466, by rfl⟩ : syracuseStep 1271821 = 476933) (by norm_num)
theorem B845869 : Blo 750330 845869 := bbase (se 3 (by rfl) ⟨158600, by rfl⟩ : syracuseStep 845869 = 317201) (by norm_num)
theorem B845905 : Blo 750330 845905 := bbase (se 2 (by rfl) ⟨317214, by rfl⟩ : syracuseStep 845905 = 634429) (by norm_num)
theorem B1271909 : Blo 750330 1271909 := bbase (se 4 (by rfl) ⟨119241, by rfl⟩ : syracuseStep 1271909 = 238483) (by norm_num)
theorem B845941 : Blo 750330 845941 := bbase (se 5 (by rfl) ⟨39653, by rfl⟩ : syracuseStep 845941 = 79307) (by norm_num)
theorem B845977 : Blo 750330 845977 := bbase (se 2 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 845977 = 634483) (by norm_num)
theorem B846013 : Blo 750330 846013 := bbase (se 3 (by rfl) ⟨158627, by rfl⟩ : syracuseStep 846013 = 317255) (by norm_num)
theorem B846049 : Blo 750330 846049 := bbase (se 2 (by rfl) ⟨317268, by rfl⟩ : syracuseStep 846049 = 634537) (by norm_num)
theorem B1272037 : Blo 750330 1272037 := bbase (se 4 (by rfl) ⟨119253, by rfl⟩ : syracuseStep 1272037 = 238507) (by norm_num)
theorem B6875381 : Blo 750330 6875381 := bbase (se 5 (by rfl) ⟨322283, by rfl⟩ : syracuseStep 6875381 = 644567) (by norm_num)
theorem B846085 : Blo 750330 846085 := bbase (se 4 (by rfl) ⟨79320, by rfl⟩ : syracuseStep 846085 = 158641) (by norm_num)
theorem B846121 : Blo 750330 846121 := bbase (se 2 (by rfl) ⟨317295, by rfl⟩ : syracuseStep 846121 = 634591) (by norm_num)
theorem B1272125 : Blo 750330 1272125 := bbase (se 3 (by rfl) ⟨238523, by rfl⟩ : syracuseStep 1272125 = 477047) (by norm_num)
theorem B846157 : Blo 750330 846157 := bbase (se 3 (by rfl) ⟨158654, by rfl⟩ : syracuseStep 846157 = 317309) (by norm_num)
theorem B846193 : Blo 750330 846193 := bbase (se 2 (by rfl) ⟨317322, by rfl⟩ : syracuseStep 846193 = 634645) (by norm_num)
theorem B846229 : Blo 750330 846229 := bbase (se 6 (by rfl) ⟨19833, by rfl⟩ : syracuseStep 846229 = 39667) (by norm_num)
theorem B846265 : Blo 750330 846265 := bbase (se 2 (by rfl) ⟨317349, by rfl⟩ : syracuseStep 846265 = 634699) (by norm_num)
theorem B1272253 : Blo 750330 1272253 := bbase (se 3 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 1272253 = 477095) (by norm_num)
theorem B846301 : Blo 750330 846301 := bbase (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) (by norm_num)
theorem B846337 : Blo 750330 846337 := bbase (se 2 (by rfl) ⟨317376, by rfl⟩ : syracuseStep 846337 = 634753) (by norm_num)
theorem B1272341 : Blo 750330 1272341 := bbase (se 6 (by rfl) ⟨29820, by rfl⟩ : syracuseStep 1272341 = 59641) (by norm_num)
theorem B846373 : Blo 750330 846373 := bbase (se 4 (by rfl) ⟨79347, by rfl⟩ : syracuseStep 846373 = 158695) (by norm_num)
theorem B846409 : Blo 750330 846409 := bbase (se 2 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 846409 = 634807) (by norm_num)
theorem B846445 : Blo 750330 846445 := bbase (se 3 (by rfl) ⟨158708, by rfl⟩ : syracuseStep 846445 = 317417) (by norm_num)
theorem B1206917 : Blo 750330 1206917 := bbase (se 4 (by rfl) ⟨113148, by rfl⟩ : syracuseStep 1206917 = 226297) (by norm_num)
theorem B846481 : Blo 750330 846481 := bbase (se 2 (by rfl) ⟨317430, by rfl⟩ : syracuseStep 846481 = 634861) (by norm_num)
theorem B1927829 : Blo 750330 1927829 := bbase (se 6 (by rfl) ⟨45183, by rfl⟩ : syracuseStep 1927829 = 90367) (by norm_num)
theorem B1272469 : Blo 750330 1272469 := bbase (se 6 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 1272469 = 59647) (by norm_num)
theorem B846517 : Blo 750330 846517 := bbase (se 5 (by rfl) ⟨39680, by rfl⟩ : syracuseStep 846517 = 79361) (by norm_num)
theorem B846553 : Blo 750330 846553 := bbase (se 2 (by rfl) ⟨317457, by rfl⟩ : syracuseStep 846553 = 634915) (by norm_num)
theorem B1272557 : Blo 750330 1272557 := bbase (se 3 (by rfl) ⟨238604, by rfl⟩ : syracuseStep 1272557 = 477209) (by norm_num)
theorem B846589 : Blo 750330 846589 := bbase (se 3 (by rfl) ⟨158735, by rfl⟩ : syracuseStep 846589 = 317471) (by norm_num)
theorem B846625 : Blo 750330 846625 := bbase (se 2 (by rfl) ⟨317484, by rfl⟩ : syracuseStep 846625 = 634969) (by norm_num)
theorem B813889 : Blo 750330 813889 := bbase (se 2 (by rfl) ⟨305208, by rfl⟩ : syracuseStep 813889 = 610417) (by norm_num)
theorem B846661 : Blo 750330 846661 := bbase (se 4 (by rfl) ⟨79374, by rfl⟩ : syracuseStep 846661 = 158749) (by norm_num)
theorem B2321237 : Blo 750330 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B846697 : Blo 750330 846697 := bbase (se 2 (by rfl) ⟨317511, by rfl⟩ : syracuseStep 846697 = 635023) (by norm_num)
theorem B1272685 : Blo 750330 1272685 := bbase (se 3 (by rfl) ⟨238628, by rfl⟩ : syracuseStep 1272685 = 477257) (by norm_num)
theorem B846733 : Blo 750330 846733 := bbase (se 3 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 846733 = 317525) (by norm_num)
theorem B2288533 : Blo 750330 2288533 := bbase (se 6 (by rfl) ⟨53637, by rfl⟩ : syracuseStep 2288533 = 107275) (by norm_num)
theorem B813997 : Blo 750330 813997 := bbase (se 3 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 813997 = 305249) (by norm_num)
theorem B846769 : Blo 750330 846769 := bbase (se 2 (by rfl) ⟨317538, by rfl⟩ : syracuseStep 846769 = 635077) (by norm_num)
theorem B1272773 : Blo 750330 1272773 := bbase (se 4 (by rfl) ⟨119322, by rfl⟩ : syracuseStep 1272773 = 238645) (by norm_num)
theorem B846805 : Blo 750330 846805 := bbase (se 7 (by rfl) ⟨9923, by rfl⟩ : syracuseStep 846805 = 19847) (by norm_num)
theorem B846841 : Blo 750330 846841 := bbase (se 2 (by rfl) ⟨317565, by rfl⟩ : syracuseStep 846841 = 635131) (by norm_num)
theorem B846877 : Blo 750330 846877 := bbase (se 3 (by rfl) ⟨158789, by rfl⟩ : syracuseStep 846877 = 317579) (by norm_num)
theorem B846913 : Blo 750330 846913 := bbase (se 2 (by rfl) ⟨317592, by rfl⟩ : syracuseStep 846913 = 635185) (by norm_num)
theorem B1272901 : Blo 750330 1272901 := bbase (se 4 (by rfl) ⟨119334, by rfl⟩ : syracuseStep 1272901 = 238669) (by norm_num)
theorem B846949 : Blo 750330 846949 := bbase (se 4 (by rfl) ⟨79401, by rfl⟩ : syracuseStep 846949 = 158803) (by norm_num)
theorem B1207429 : Blo 750330 1207429 := bbase (se 4 (by rfl) ⟨113196, by rfl⟩ : syracuseStep 1207429 = 226393) (by norm_num)
theorem B846985 : Blo 750330 846985 := bbase (se 2 (by rfl) ⟨317619, by rfl⟩ : syracuseStep 846985 = 635239) (by norm_num)
theorem B847021 : Blo 750330 847021 := bbase (se 3 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 847021 = 317633) (by norm_num)
theorem B847057 : Blo 750330 847057 := bbase (se 2 (by rfl) ⟨317646, by rfl⟩ : syracuseStep 847057 = 635293) (by norm_num)
theorem B847093 : Blo 750330 847093 := bbase (se 5 (by rfl) ⟨39707, by rfl⟩ : syracuseStep 847093 = 79415) (by norm_num)
theorem B847129 : Blo 750330 847129 := bbase (se 2 (by rfl) ⟨317673, by rfl⟩ : syracuseStep 847129 = 635347) (by norm_num)
theorem B847165 : Blo 750330 847165 := bbase (se 3 (by rfl) ⟨158843, by rfl⟩ : syracuseStep 847165 = 317687) (by norm_num)
theorem B847201 : Blo 750330 847201 := bbase (se 2 (by rfl) ⟨317700, by rfl⟩ : syracuseStep 847201 = 635401) (by norm_num)
theorem B847237 : Blo 750330 847237 := bbase (se 4 (by rfl) ⟨79428, by rfl⟩ : syracuseStep 847237 = 158857) (by norm_num)
theorem B847273 : Blo 750330 847273 := bbase (se 2 (by rfl) ⟨317727, by rfl⟩ : syracuseStep 847273 = 635455) (by norm_num)
theorem B847309 : Blo 750330 847309 := bbase (se 3 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 847309 = 317741) (by norm_num)
theorem B847345 : Blo 750330 847345 := bbase (se 2 (by rfl) ⟨317754, by rfl⟩ : syracuseStep 847345 = 635509) (by norm_num)
theorem B3141109 : Blo 750330 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B847381 : Blo 750330 847381 := bbase (se 6 (by rfl) ⟨19860, by rfl⟩ : syracuseStep 847381 = 39721) (by norm_num)
theorem B847417 : Blo 750330 847417 := bbase (se 2 (by rfl) ⟨317781, by rfl⟩ : syracuseStep 847417 = 635563) (by norm_num)
theorem B1207885 : Blo 750330 1207885 := bbase (se 3 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 1207885 = 452957) (by norm_num)
theorem B847453 : Blo 750330 847453 := bbase (se 3 (by rfl) ⟨158897, by rfl⟩ : syracuseStep 847453 = 317795) (by norm_num)
theorem B1142381 : Blo 750330 1142381 := bbase (se 3 (by rfl) ⟨214196, by rfl⟩ : syracuseStep 1142381 = 428393) (by norm_num)
theorem B847489 : Blo 750330 847489 := bbase (se 2 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 847489 = 635617) (by norm_num)
theorem B847525 : Blo 750330 847525 := bbase (se 4 (by rfl) ⟨79455, by rfl⟩ : syracuseStep 847525 = 158911) (by norm_num)
theorem B847561 : Blo 750330 847561 := bbase (se 2 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 847561 = 635671) (by norm_num)
theorem B847597 : Blo 750330 847597 := bbase (se 3 (by rfl) ⟨158924, by rfl⟩ : syracuseStep 847597 = 317849) (by norm_num)
theorem B847633 : Blo 750330 847633 := bbase (se 2 (by rfl) ⟨317862, by rfl⟩ : syracuseStep 847633 = 635725) (by norm_num)
theorem B847669 : Blo 750330 847669 := bbase (se 5 (by rfl) ⟨39734, by rfl⟩ : syracuseStep 847669 = 79469) (by norm_num)
theorem B847705 : Blo 750330 847705 := bbase (se 2 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 847705 = 635779) (by norm_num)
theorem B847741 : Blo 750330 847741 := bbase (se 3 (by rfl) ⟨158951, by rfl⟩ : syracuseStep 847741 = 317903) (by norm_num)
theorem B847777 : Blo 750330 847777 := bbase (se 2 (by rfl) ⟨317916, by rfl⟩ : syracuseStep 847777 = 635833) (by norm_num)
theorem B847813 : Blo 750330 847813 := bbase (se 4 (by rfl) ⟨79482, by rfl⟩ : syracuseStep 847813 = 158965) (by norm_num)
theorem B847849 : Blo 750330 847849 := bbase (se 2 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 847849 = 635887) (by norm_num)
theorem B847885 : Blo 750330 847885 := bbase (se 3 (by rfl) ⟨158978, by rfl⟩ : syracuseStep 847885 = 317957) (by norm_num)
theorem B2289701 : Blo 750330 2289701 := bbase (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) (by norm_num)
theorem B847921 : Blo 750330 847921 := bbase (se 2 (by rfl) ⟨317970, by rfl⟩ : syracuseStep 847921 = 635941) (by norm_num)
theorem B3207221 : Blo 750330 3207221 := bbase (se 5 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 3207221 = 300677) (by norm_num)
theorem B847957 : Blo 750330 847957 := bbase (se 8 (by rfl) ⟨4968, by rfl⟩ : syracuseStep 847957 = 9937) (by norm_num)
theorem B847993 : Blo 750330 847993 := bbase (se 2 (by rfl) ⟨317997, by rfl⟩ : syracuseStep 847993 = 635995) (by norm_num)
theorem B15429781 : Blo 750330 15429781 := bbase (se 6 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 15429781 = 723271) (by norm_num)
theorem B848029 : Blo 750330 848029 := bbase (se 3 (by rfl) ⟨159005, by rfl⟩ : syracuseStep 848029 = 318011) (by norm_num)
theorem B848065 : Blo 750330 848065 := bbase (se 2 (by rfl) ⟨318024, by rfl⟩ : syracuseStep 848065 = 636049) (by norm_num)
theorem B848101 : Blo 750330 848101 := bbase (se 4 (by rfl) ⟨79509, by rfl⟩ : syracuseStep 848101 = 159019) (by norm_num)
theorem B848137 : Blo 750330 848137 := bbase (se 2 (by rfl) ⟨318051, by rfl⟩ : syracuseStep 848137 = 636103) (by norm_num)
theorem B6418709 : Blo 750330 6418709 := bbase (se 6 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 6418709 = 300877) (by norm_num)
theorem B848173 : Blo 750330 848173 := bbase (se 3 (by rfl) ⟨159032, by rfl⟩ : syracuseStep 848173 = 318065) (by norm_num)
theorem B848209 : Blo 750330 848209 := bbase (se 2 (by rfl) ⟨318078, by rfl⟩ : syracuseStep 848209 = 636157) (by norm_num)
theorem B3207509 : Blo 750330 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B848245 : Blo 750330 848245 := bbase (se 5 (by rfl) ⟨39761, by rfl⟩ : syracuseStep 848245 = 79523) (by norm_num)
theorem B848281 : Blo 750330 848281 := bbase (se 2 (by rfl) ⟨318105, by rfl⟩ : syracuseStep 848281 = 636211) (by norm_num)
theorem B848317 : Blo 750330 848317 := bbase (se 3 (by rfl) ⟨159059, by rfl⟩ : syracuseStep 848317 = 318119) (by norm_num)
theorem B848353 : Blo 750330 848353 := bbase (se 2 (by rfl) ⟨318132, by rfl⟩ : syracuseStep 848353 = 636265) (by norm_num)
theorem B1143293 : Blo 750330 1143293 := bbase (se 3 (by rfl) ⟨214367, by rfl⟩ : syracuseStep 1143293 = 428735) (by norm_num)
theorem B848389 : Blo 750330 848389 := bbase (se 4 (by rfl) ⟨79536, by rfl⟩ : syracuseStep 848389 = 159073) (by norm_num)
theorem B848425 : Blo 750330 848425 := bbase (se 2 (by rfl) ⟨318159, by rfl⟩ : syracuseStep 848425 = 636319) (by norm_num)
theorem B848461 : Blo 750330 848461 := bbase (se 3 (by rfl) ⟨159086, by rfl⟩ : syracuseStep 848461 = 318173) (by norm_num)
theorem B848497 : Blo 750330 848497 := bbase (se 2 (by rfl) ⟨318186, by rfl⟩ : syracuseStep 848497 = 636373) (by norm_num)
theorem B848533 : Blo 750330 848533 := bbase (se 6 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 848533 = 39775) (by norm_num)
theorem B5436085 : Blo 750330 5436085 := bbase (se 5 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 5436085 = 509633) (by norm_num)
theorem B848569 : Blo 750330 848569 := bbase (se 2 (by rfl) ⟨318213, by rfl⟩ : syracuseStep 848569 = 636427) (by norm_num)
theorem B2716357 : Blo 750330 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B848605 : Blo 750330 848605 := bbase (se 3 (by rfl) ⟨159113, by rfl⟩ : syracuseStep 848605 = 318227) (by norm_num)
theorem B783145 : Blo 750330 783145 := bbase (se 2 (by rfl) ⟨293679, by rfl⟩ : syracuseStep 783145 = 587359) (by norm_num)
theorem B2716517 : Blo 750330 2716517 := bbase (se 4 (by rfl) ⟨254673, by rfl⟩ : syracuseStep 2716517 = 509347) (by norm_num)
theorem B914377 : Blo 750330 914377 := bbase (se 2 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 914377 = 685783) (by norm_num)
theorem B1602517 : Blo 750330 1602517 := bbase (se 7 (by rfl) ⟨18779, by rfl⟩ : syracuseStep 1602517 = 37559) (by norm_num)
theorem B3208261 : Blo 750330 3208261 := bbase (se 4 (by rfl) ⟨300774, by rfl⟩ : syracuseStep 3208261 = 601549) (by norm_num)
theorem B1143877 : Blo 750330 1143877 := bbase (se 4 (by rfl) ⟨107238, by rfl⟩ : syracuseStep 1143877 = 214477) (by norm_num)
theorem B1602661 : Blo 750330 1602661 := bbase (se 4 (by rfl) ⟨150249, by rfl⟩ : syracuseStep 1602661 = 300499) (by norm_num)
theorem B1144133 : Blo 750330 1144133 := bbase (se 4 (by rfl) ⟨107262, by rfl⟩ : syracuseStep 1144133 = 214525) (by norm_num)
theorem B3437909 : Blo 750330 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B1603037 : Blo 750330 1603037 := bbase (se 3 (by rfl) ⟨300569, by rfl⟩ : syracuseStep 1603037 = 601139) (by norm_num)
theorem B784069 : Blo 750330 784069 := bbase (se 4 (by rfl) ⟨73506, by rfl⟩ : syracuseStep 784069 = 147013) (by norm_num)
theorem B3208997 : Blo 750330 3208997 := bbase (se 4 (by rfl) ⟨300843, by rfl⟩ : syracuseStep 3208997 = 601687) (by norm_num)
theorem B1603405 : Blo 750330 1603405 := bbase (se 3 (by rfl) ⟨300638, by rfl⟩ : syracuseStep 1603405 = 601277) (by norm_num)
theorem B1046405 : Blo 750330 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B3799061 : Blo 750330 3799061 := bbase (se 6 (by rfl) ⟨89040, by rfl⟩ : syracuseStep 3799061 = 178081) (by norm_num)
theorem B1931381 : Blo 750330 1931381 := bbase (se 5 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 1931381 = 181067) (by norm_num)
theorem B2029861 : Blo 750330 2029861 := bbase (se 4 (by rfl) ⟨190299, by rfl⟩ : syracuseStep 2029861 = 380599) (by norm_num)
theorem B2292181 : Blo 750330 2292181 := bbase (se 7 (by rfl) ⟨26861, by rfl⟩ : syracuseStep 2292181 = 53723) (by norm_num)
theorem B2849525 : Blo 750330 2849525 := bbase (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) (by norm_num)
theorem B1899389 : Blo 750330 1899389 := bbase (se 3 (by rfl) ⟨356135, by rfl⟩ : syracuseStep 1899389 = 712271) (by norm_num)
theorem B2849813 : Blo 750330 2849813 := bbase (se 6 (by rfl) ⟨66792, by rfl⟩ : syracuseStep 2849813 = 133585) (by norm_num)
theorem B1899733 : Blo 750330 1899733 := bbase (se 7 (by rfl) ⟨22262, by rfl⟩ : syracuseStep 1899733 = 44525) (by norm_num)
theorem B3800357 : Blo 750330 3800357 := bbase (se 4 (by rfl) ⟨356283, by rfl⟩ : syracuseStep 3800357 = 712567) (by norm_num)
theorem B1604909 : Blo 750330 1604909 := bbase (se 3 (by rfl) ⟨300920, by rfl⟩ : syracuseStep 1604909 = 601841) (by norm_num)
theorem B1015093 : Blo 750330 1015093 := bbase (se 5 (by rfl) ⟨47582, by rfl⟩ : syracuseStep 1015093 = 95165) (by norm_num)
theorem B1899845 : Blo 750330 1899845 := bbase (se 4 (by rfl) ⟨178110, by rfl⟩ : syracuseStep 1899845 = 356221) (by norm_num)
theorem B1605053 : Blo 750330 1605053 := bbase (se 3 (by rfl) ⟨300947, by rfl⟩ : syracuseStep 1605053 = 601895) (by norm_num)
theorem B949745 : Blo 750330 949745 := bbase (se 2 (by rfl) ⟨356154, by rfl⟩ : syracuseStep 949745 = 712309) (by norm_num)
theorem B1900037 : Blo 750330 1900037 := bbase (se 4 (by rfl) ⟨178128, by rfl⟩ : syracuseStep 1900037 = 356257) (by norm_num)
theorem B949801 : Blo 750330 949801 := bbase (se 2 (by rfl) ⟨356175, by rfl⟩ : syracuseStep 949801 = 712351) (by norm_num)
theorem B1146469 : Blo 750330 1146469 := bbase (se 4 (by rfl) ⟨107481, by rfl⟩ : syracuseStep 1146469 = 214963) (by norm_num)
theorem B949897 : Blo 750330 949897 := bbase (se 2 (by rfl) ⟨356211, by rfl⟩ : syracuseStep 949897 = 712423) (by norm_num)
theorem B2293397 : Blo 750330 2293397 := bbase (se 6 (by rfl) ⟨53751, by rfl⟩ : syracuseStep 2293397 = 107503) (by norm_num)
theorem B917149 : Blo 750330 917149 := bbase (se 3 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 917149 = 343931) (by norm_num)
theorem B1605413 : Blo 750330 1605413 := bbase (se 4 (by rfl) ⟨150507, by rfl⟩ : syracuseStep 1605413 = 301015) (by norm_num)
theorem B950069 : Blo 750330 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B1834805 : Blo 750330 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B1900381 : Blo 750330 1900381 := bbase (se 3 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 1900381 = 712643) (by norm_num)
theorem B950125 : Blo 750330 950125 := bbase (se 3 (by rfl) ⟨178148, by rfl⟩ : syracuseStep 950125 = 356297) (by norm_num)
theorem B1146773 : Blo 750330 1146773 := bbase (se 6 (by rfl) ⟨26877, by rfl⟩ : syracuseStep 1146773 = 53755) (by norm_num)
theorem B950221 : Blo 750330 950221 := bbase (se 3 (by rfl) ⟨178166, by rfl⟩ : syracuseStep 950221 = 356333) (by norm_num)
theorem B1900493 : Blo 750330 1900493 := bbase (se 3 (by rfl) ⟨356342, by rfl⟩ : syracuseStep 1900493 = 712685) (by norm_num)
theorem B4816853 : Blo 750330 4816853 := bbase (se 7 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 4816853 = 112895) (by norm_num)
theorem B753667 : Blo 750330 753667 := bstep (se 1 (by rfl) ⟨565250, by rfl⟩ : syracuseStep 753667 = 1130501) B1130501
theorem B753683 : Blo 750330 753683 := bstep (se 1 (by rfl) ⟨565262, by rfl⟩ : syracuseStep 753683 = 1130525) B1130525
theorem B753699 : Blo 750330 753699 := bstep (se 1 (by rfl) ⟨565274, by rfl⟩ : syracuseStep 753699 = 1130549) B1130549
theorem B753715 : Blo 750330 753715 := bstep (se 1 (by rfl) ⟨565286, by rfl⟩ : syracuseStep 753715 = 1130573) B1130573
theorem B753731 : Blo 750330 753731 := bstep (se 1 (by rfl) ⟨565298, by rfl⟩ : syracuseStep 753731 = 1130597) B1130597
theorem B753747 : Blo 750330 753747 := bstep (se 1 (by rfl) ⟨565310, by rfl⟩ : syracuseStep 753747 = 1130621) B1130621
theorem B753763 : Blo 750330 753763 := bstep (se 1 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 753763 = 1130645) B1130645
theorem B753779 : Blo 750330 753779 := bstep (se 1 (by rfl) ⟨565334, by rfl⟩ : syracuseStep 753779 = 1130669) B1130669
theorem B753795 : Blo 750330 753795 := bstep (se 1 (by rfl) ⟨565346, by rfl⟩ : syracuseStep 753795 = 1130693) B1130693
theorem B753811 : Blo 750330 753811 := bstep (se 1 (by rfl) ⟨565358, by rfl⟩ : syracuseStep 753811 = 1130717) B1130717
theorem B1015969 : Blo 750330 1015969 := bstep (se 2 (by rfl) ⟨380988, by rfl⟩ : syracuseStep 1015969 = 761977) B761977
theorem B753827 : Blo 750330 753827 := bstep (se 1 (by rfl) ⟨565370, by rfl⟩ : syracuseStep 753827 = 1130741) B1130741
theorem B753843 : Blo 750330 753843 := bstep (se 1 (by rfl) ⟨565382, by rfl⟩ : syracuseStep 753843 = 1130765) B1130765
theorem B753859 : Blo 750330 753859 := bstep (se 1 (by rfl) ⟨565394, by rfl⟩ : syracuseStep 753859 = 1130789) B1130789
theorem B753875 : Blo 750330 753875 := bstep (se 1 (by rfl) ⟨565406, by rfl⟩ : syracuseStep 753875 = 1130813) B1130813
theorem B753891 : Blo 750330 753891 := bstep (se 1 (by rfl) ⟨565418, by rfl⟩ : syracuseStep 753891 = 1130837) B1130837
theorem B3801329 : Blo 750330 3801329 := bstep (se 2 (by rfl) ⟨1425498, by rfl⟩ : syracuseStep 3801329 = 2850997) B2850997
theorem B753907 : Blo 750330 753907 := bstep (se 1 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 753907 = 1130861) B1130861
theorem B753923 : Blo 750330 753923 := bstep (se 1 (by rfl) ⟨565442, by rfl⟩ : syracuseStep 753923 = 1130885) B1130885
theorem B1900817 : Blo 750330 1900817 := bstep (se 2 (by rfl) ⟨712806, by rfl⟩ : syracuseStep 1900817 = 1425613) B1425613
theorem B753939 : Blo 750330 753939 := bstep (se 1 (by rfl) ⟨565454, by rfl⟩ : syracuseStep 753939 = 1130909) B1130909
theorem B753955 : Blo 750330 753955 := bstep (se 1 (by rfl) ⟨565466, by rfl⟩ : syracuseStep 753955 = 1130933) B1130933
theorem B753971 : Blo 750330 753971 := bstep (se 1 (by rfl) ⟨565478, by rfl⟩ : syracuseStep 753971 = 1130957) B1130957
theorem B16253237 : Blo 750330 16253237 := bstep (se 5 (by rfl) ⟨761870, by rfl⟩ : syracuseStep 16253237 = 1523741) B1523741
theorem B1900867 : Blo 750330 1900867 := bstep (se 1 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 1900867 = 2851301) B2851301
theorem B753987 : Blo 750330 753987 := bstep (se 1 (by rfl) ⟨565490, by rfl⟩ : syracuseStep 753987 = 1130981) B1130981
theorem B950611 : Blo 750330 950611 := bstep (se 1 (by rfl) ⟨712958, by rfl⟩ : syracuseStep 950611 = 1425917) B1425917
theorem B754003 : Blo 750330 754003 := bstep (se 1 (by rfl) ⟨565502, by rfl⟩ : syracuseStep 754003 = 1131005) B1131005
theorem B754019 : Blo 750330 754019 := bstep (se 1 (by rfl) ⟨565514, by rfl⟩ : syracuseStep 754019 = 1131029) B1131029
theorem B754035 : Blo 750330 754035 := bstep (se 1 (by rfl) ⟨565526, by rfl⟩ : syracuseStep 754035 = 1131053) B1131053
theorem B754051 : Blo 750330 754051 := bstep (se 1 (by rfl) ⟨565538, by rfl⟩ : syracuseStep 754051 = 1131077) B1131077
theorem B754067 : Blo 750330 754067 := bstep (se 1 (by rfl) ⟨565550, by rfl⟩ : syracuseStep 754067 = 1131101) B1131101
theorem B754083 : Blo 750330 754083 := bstep (se 1 (by rfl) ⟨565562, by rfl⟩ : syracuseStep 754083 = 1131125) B1131125
theorem B950707 : Blo 750330 950707 := bstep (se 1 (by rfl) ⟨713030, by rfl⟩ : syracuseStep 950707 = 1426061) B1426061
theorem B754099 : Blo 750330 754099 := bstep (se 1 (by rfl) ⟨565574, by rfl⟩ : syracuseStep 754099 = 1131149) B1131149
theorem B754115 : Blo 750330 754115 := bstep (se 1 (by rfl) ⟨565586, by rfl⟩ : syracuseStep 754115 = 1131173) B1131173
theorem B1901009 : Blo 750330 1901009 := bstep (se 2 (by rfl) ⟨712878, by rfl⟩ : syracuseStep 1901009 = 1425757) B1425757
theorem B754131 : Blo 750330 754131 := bstep (se 1 (by rfl) ⟨565598, by rfl⟩ : syracuseStep 754131 = 1131197) B1131197
theorem B754147 : Blo 750330 754147 := bstep (se 1 (by rfl) ⟨565610, by rfl⟩ : syracuseStep 754147 = 1131221) B1131221
theorem B4817393 : Blo 750330 4817393 := bstep (se 2 (by rfl) ⟨1806522, by rfl⟩ : syracuseStep 4817393 = 3613045) B3613045
theorem B754163 : Blo 750330 754163 := bstep (se 1 (by rfl) ⟨565622, by rfl⟩ : syracuseStep 754163 = 1131245) B1131245
theorem B754179 : Blo 750330 754179 := bstep (se 1 (by rfl) ⟨565634, by rfl⟩ : syracuseStep 754179 = 1131269) B1131269
theorem B754195 : Blo 750330 754195 := bstep (se 1 (by rfl) ⟨565646, by rfl⟩ : syracuseStep 754195 = 1131293) B1131293
theorem B754211 : Blo 750330 754211 := bstep (se 1 (by rfl) ⟨565658, by rfl⟩ : syracuseStep 754211 = 1131317) B1131317
theorem B754227 : Blo 750330 754227 := bstep (se 1 (by rfl) ⟨565670, by rfl⟩ : syracuseStep 754227 = 1131341) B1131341
theorem B754243 : Blo 750330 754243 := bstep (se 1 (by rfl) ⟨565682, by rfl⟩ : syracuseStep 754243 = 1131365) B1131365
theorem B754259 : Blo 750330 754259 := bstep (se 1 (by rfl) ⟨565694, by rfl⟩ : syracuseStep 754259 = 1131389) B1131389
theorem B754275 : Blo 750330 754275 := bstep (se 1 (by rfl) ⟨565706, by rfl⟩ : syracuseStep 754275 = 1131413) B1131413
theorem B754291 : Blo 750330 754291 := bstep (se 1 (by rfl) ⟨565718, by rfl⟩ : syracuseStep 754291 = 1131437) B1131437
theorem B754307 : Blo 750330 754307 := bstep (se 1 (by rfl) ⟨565730, by rfl⟩ : syracuseStep 754307 = 1131461) B1131461
theorem B2851469 : Blo 750330 2851469 := bstep (se 3 (by rfl) ⟨534650, by rfl⟩ : syracuseStep 2851469 = 1069301) B1069301
theorem B754323 : Blo 750330 754323 := bstep (se 1 (by rfl) ⟨565742, by rfl⟩ : syracuseStep 754323 = 1131485) B1131485
theorem B4293445 : Blo 750330 4293445 := bstep (se 4 (by rfl) ⟨402510, by rfl⟩ : syracuseStep 4293445 = 805021) B805021
theorem B951203 : Blo 750330 951203 := bstep (se 1 (by rfl) ⟨713402, by rfl⟩ : syracuseStep 951203 = 1426805) B1426805
theorem B2032771 : Blo 750330 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B4064525 : Blo 750330 4064525 := bstep (se 3 (by rfl) ⟨762098, by rfl⟩ : syracuseStep 4064525 = 1524197) B1524197
theorem B3048781 : Blo 750330 3048781 := bstep (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) B1143293
theorem B2852273 : Blo 750330 2852273 := bstep (se 2 (by rfl) ⟨1069602, by rfl⟩ : syracuseStep 2852273 = 2139205) B2139205
theorem B1902001 : Blo 750330 1902001 := bstep (se 2 (by rfl) ⟨713250, by rfl⟩ : syracuseStep 1902001 = 1426501) B1426501
theorem B1017299 : Blo 750330 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B3606029 : Blo 750330 3606029 := bstep (se 3 (by rfl) ⟨676130, by rfl⟩ : syracuseStep 3606029 = 1352261) B1352261
theorem B951907 : Blo 750330 951907 := bstep (se 1 (by rfl) ⟨713930, by rfl⟩ : syracuseStep 951907 = 1427861) B1427861
theorem B3802787 : Blo 750330 3802787 := bstep (se 1 (by rfl) ⟨2852090, by rfl⟩ : syracuseStep 3802787 = 5704181) B5704181
theorem B1902275 : Blo 750330 1902275 := bstep (se 1 (by rfl) ⟨1426706, by rfl⟩ : syracuseStep 1902275 = 2853413) B2853413
theorem B952003 : Blo 750330 952003 := bstep (se 1 (by rfl) ⟨714002, by rfl⟩ : syracuseStep 952003 = 1428005) B1428005
theorem B1607377 : Blo 750330 1607377 := bstep (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) B1205533
theorem B1902467 : Blo 750330 1902467 := bstep (se 1 (by rfl) ⟨1426850, by rfl⟩ : syracuseStep 1902467 = 2853701) B2853701
theorem B1017731 : Blo 750330 1017731 := bstep (se 1 (by rfl) ⟨763298, by rfl⟩ : syracuseStep 1017731 = 1526597) B1526597
theorem B4818851 : Blo 750330 4818851 := bstep (se 1 (by rfl) ⟨3614138, by rfl⟩ : syracuseStep 4818851 = 7228277) B7228277
theorem B2033603 : Blo 750330 2033603 := bstep (se 1 (by rfl) ⟨1525202, by rfl⟩ : syracuseStep 2033603 = 3050405) B3050405
theorem B2033731 : Blo 750330 2033731 := bstep (se 1 (by rfl) ⟨1525298, by rfl⟩ : syracuseStep 2033731 = 3050597) B3050597
theorem B2852941 : Blo 750330 2852941 := bstep (se 3 (by rfl) ⟨534926, by rfl⟩ : syracuseStep 2852941 = 1069853) B1069853
theorem B1607779 : Blo 750330 1607779 := bstep (se 1 (by rfl) ⟨1205834, by rfl⟩ : syracuseStep 1607779 = 2411669) B2411669
theorem B952499 : Blo 750330 952499 := bstep (se 1 (by rfl) ⟨714374, by rfl⟩ : syracuseStep 952499 = 1428749) B1428749
theorem B2033905 : Blo 750330 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B8587619 : Blo 750330 8587619 := bstep (se 1 (by rfl) ⟨6440714, by rfl⟩ : syracuseStep 8587619 = 12881429) B12881429
theorem B12224965 : Blo 750330 12224965 := bstep (se 4 (by rfl) ⟨1146090, by rfl⟩ : syracuseStep 12224965 = 2292181) B2292181
theorem B3803597 : Blo 750330 3803597 := bstep (se 3 (by rfl) ⟨713174, by rfl⟩ : syracuseStep 3803597 = 1426349) B1426349
theorem B8784611 : Blo 750330 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B4295429 : Blo 750330 4295429 := bstep (se 4 (by rfl) ⟨402696, by rfl⟩ : syracuseStep 4295429 = 805393) B805393
theorem B1903409 : Blo 750330 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B2853731 : Blo 750330 2853731 := bstep (se 1 (by rfl) ⟨2140298, by rfl⟩ : syracuseStep 2853731 = 4280597) B4280597
theorem B1903459 : Blo 750330 1903459 := bstep (se 1 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 1903459 = 2855189) B2855189
theorem B953203 : Blo 750330 953203 := bstep (se 1 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 953203 = 1429805) B1429805
theorem B953299 : Blo 750330 953299 := bstep (se 1 (by rfl) ⟨714974, by rfl⟩ : syracuseStep 953299 = 1429949) B1429949
theorem B1903601 : Blo 750330 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B2034769 : Blo 750330 2034769 := bstep (se 2 (by rfl) ⟨763038, by rfl⟩ : syracuseStep 2034769 = 1526077) B1526077
theorem B1674499 : Blo 750330 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B1019201 : Blo 750330 1019201 := bstep (se 2 (by rfl) ⟨382200, by rfl⟩ : syracuseStep 1019201 = 764401) B764401
theorem B953795 : Blo 750330 953795 := bstep (se 1 (by rfl) ⟨715346, by rfl⟩ : syracuseStep 953795 = 1430693) B1430693
theorem B16289221 : Blo 750330 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B2854385 : Blo 750330 2854385 := bstep (se 2 (by rfl) ⟨1070394, by rfl⟩ : syracuseStep 2854385 = 2140789) B2140789
theorem B1609283 : Blo 750330 1609283 := bstep (se 1 (by rfl) ⟨1206962, by rfl⟩ : syracuseStep 1609283 = 2413925) B2413925
theorem B4820593 : Blo 750330 4820593 := bstep (se 2 (by rfl) ⟨1807722, by rfl⟩ : syracuseStep 4820593 = 3615445) B3615445
theorem B3215011 : Blo 750330 3215011 := bstep (se 1 (by rfl) ⟨2411258, by rfl⟩ : syracuseStep 3215011 = 4822517) B4822517
theorem B1085185 : Blo 750330 1085185 := bstep (se 2 (by rfl) ⟨406944, by rfl⟩ : syracuseStep 1085185 = 813889) B813889
theorem B3051377 : Blo 750330 3051377 := bstep (se 2 (by rfl) ⟨1144266, by rfl⟩ : syracuseStep 3051377 = 2288533) B2288533
theorem B1085329 : Blo 750330 1085329 := bstep (se 2 (by rfl) ⟨406998, by rfl⟩ : syracuseStep 1085329 = 813997) B813997
theorem B1904593 : Blo 750330 1904593 := bstep (se 2 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 1904593 = 1428445) B1428445
theorem B36606005 : Blo 750330 36606005 := bstep (se 5 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 36606005 = 3431813) B3431813
theorem B954499 : Blo 750330 954499 := bstep (se 1 (by rfl) ⟨715874, by rfl⟩ : syracuseStep 954499 = 1431749) B1431749
theorem B1904867 : Blo 750330 1904867 := bstep (se 1 (by rfl) ⟨1428650, by rfl⟩ : syracuseStep 1904867 = 2857301) B2857301
theorem B12226787 : Blo 750330 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B954595 : Blo 750330 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B23892245 : Blo 750330 23892245 := bstep (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) B1119949
theorem B5706125 : Blo 750330 5706125 := bstep (se 3 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 5706125 = 2139797) B2139797
theorem B1905059 : Blo 750330 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B1610513 : Blo 750330 1610513 := bstep (se 2 (by rfl) ⟨603942, by rfl⟩ : syracuseStep 1610513 = 1207885) B1207885
theorem B2855843 : Blo 750330 2855843 := bstep (se 1 (by rfl) ⟨2141882, by rfl⟩ : syracuseStep 2855843 = 4283765) B4283765
theorem B2855857 : Blo 750330 2855857 := bstep (se 2 (by rfl) ⟨1070946, by rfl⟩ : syracuseStep 2855857 = 2141893) B2141893
theorem B7214093 : Blo 750330 7214093 := bstep (se 3 (by rfl) ⟨1352642, by rfl⟩ : syracuseStep 7214093 = 2705285) B2705285
theorem B2790413 : Blo 750330 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B3249229 : Blo 750330 3249229 := bstep (se 3 (by rfl) ⟨609230, by rfl⟩ : syracuseStep 3249229 = 1218461) B1218461
theorem B857251 : Blo 750330 857251 := bstep (se 1 (by rfl) ⟨642938, by rfl⟩ : syracuseStep 857251 = 1285877) B1285877
theorem B1086691 : Blo 750330 1086691 := bstep (se 1 (by rfl) ⟨815018, by rfl⟩ : syracuseStep 1086691 = 1630037) B1630037
theorem B3806513 : Blo 750330 3806513 := bstep (se 2 (by rfl) ⟨1427442, by rfl⟩ : syracuseStep 3806513 = 2854885) B2854885
theorem B1906001 : Blo 750330 1906001 := bstep (se 2 (by rfl) ⟨714750, by rfl⟩ : syracuseStep 1906001 = 1429501) B1429501
theorem B1906051 : Blo 750330 1906051 := bstep (se 1 (by rfl) ⟨1429538, by rfl⟩ : syracuseStep 1906051 = 2859077) B2859077
theorem B4822541 : Blo 750330 4822541 := bstep (se 3 (by rfl) ⟨904226, by rfl⟩ : syracuseStep 4822541 = 1808453) B1808453
theorem B1906193 : Blo 750330 1906193 := bstep (se 2 (by rfl) ⟨714822, by rfl⟩ : syracuseStep 1906193 = 1429645) B1429645
theorem B3217009 : Blo 750330 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B9639749 : Blo 750330 9639749 := bstep (se 4 (by rfl) ⟨903726, by rfl⟩ : syracuseStep 9639749 = 1807453) B1807453
theorem B4396963 : Blo 750330 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B1808369 : Blo 750330 1808369 := bstep (se 2 (by rfl) ⟨678138, by rfl⟩ : syracuseStep 1808369 = 1356277) B1356277
theorem B5150789 : Blo 750330 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B4069453 : Blo 750330 4069453 := bstep (se 3 (by rfl) ⟨763022, by rfl⟩ : syracuseStep 4069453 = 1526045) B1526045
theorem B7248113 : Blo 750330 7248113 := bstep (se 2 (by rfl) ⟨2718042, by rfl⟩ : syracuseStep 7248113 = 5436085) B5436085
theorem B2857315 : Blo 750330 2857315 := bstep (se 1 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 2857315 = 4285973) B4285973
theorem B1907185 : Blo 750330 1907185 := bstep (se 2 (by rfl) ⟨715194, by rfl⟩ : syracuseStep 1907185 = 1430389) B1430389
theorem B1219169 : Blo 750330 1219169 := bstep (se 2 (by rfl) ⟨457188, by rfl⟩ : syracuseStep 1219169 = 914377) B914377
theorem B2136689 : Blo 750330 2136689 := bstep (se 2 (by rfl) ⟨801258, by rfl⟩ : syracuseStep 2136689 = 1602517) B1602517
theorem B1809059 : Blo 750330 1809059 := bstep (se 1 (by rfl) ⟨1356794, by rfl⟩ : syracuseStep 1809059 = 2713589) B2713589
theorem B3807971 : Blo 750330 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B1907459 : Blo 750330 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B2136881 : Blo 750330 2136881 := bstep (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) B1602661
theorem B4070213 : Blo 750330 4070213 := bstep (se 4 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 4070213 = 763165) B763165
theorem B1907651 : Blo 750330 1907651 := bstep (se 1 (by rfl) ⟨1430738, by rfl⟩ : syracuseStep 1907651 = 2861477) B2861477
theorem B1285219 : Blo 750330 1285219 := bstep (se 1 (by rfl) ⟨963914, by rfl⟩ : syracuseStep 1285219 = 1927829) B1927829
theorem B859267 : Blo 750330 859267 := bstep (se 1 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 859267 = 1288901) B1288901
theorem B1547491 : Blo 750330 1547491 := bstep (se 1 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 1547491 = 2321237) B2321237
theorem B5709041 : Blo 750330 5709041 := bstep (se 2 (by rfl) ⟨2140890, by rfl⟩ : syracuseStep 5709041 = 4281781) B4281781
theorem B3808781 : Blo 750330 3808781 := bstep (se 3 (by rfl) ⟨714146, by rfl⟩ : syracuseStep 3808781 = 1428293) B1428293
theorem B2137873 : Blo 750330 2137873 := bstep (se 2 (by rfl) ⟨801702, by rfl⟩ : syracuseStep 2137873 = 1603405) B1603405
theorem B1908593 : Blo 750330 1908593 := bstep (se 2 (by rfl) ⟨715722, by rfl⟩ : syracuseStep 1908593 = 1431445) B1431445
theorem B1908643 : Blo 750330 1908643 := bstep (se 1 (by rfl) ⟨1431482, by rfl⟩ : syracuseStep 1908643 = 2862965) B2862965
theorem B16752581 : Blo 750330 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B2138147 : Blo 750330 2138147 := bstep (se 1 (by rfl) ⟨1603610, by rfl⟩ : syracuseStep 2138147 = 3207221) B3207221
theorem B1908785 : Blo 750330 1908785 := bstep (se 2 (by rfl) ⟨715794, by rfl⟩ : syracuseStep 1908785 = 1431589) B1431589
theorem B2138339 : Blo 750330 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B1712387 : Blo 750330 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B2859533 : Blo 750330 2859533 := bstep (se 3 (by rfl) ⟨536162, by rfl⟩ : syracuseStep 2859533 = 1072325) B1072325
theorem B1811011 : Blo 750330 1811011 := bstep (se 1 (by rfl) ⟨1358258, by rfl⟩ : syracuseStep 1811011 = 2716517) B2716517
theorem B4825925 : Blo 750330 4825925 := bstep (se 4 (by rfl) ⟨452430, by rfl⟩ : syracuseStep 4825925 = 904861) B904861
theorem B762755 : Blo 750330 762755 := bstep (se 1 (by rfl) ⟨572066, by rfl⟩ : syracuseStep 762755 = 1144133) B1144133
theorem B2139149 : Blo 750330 2139149 := bstep (se 3 (by rfl) ⟨401090, by rfl⟩ : syracuseStep 2139149 = 802181) B802181
theorem B1319969 : Blo 750330 1319969 := bstep (se 2 (by rfl) ⟨494988, by rfl⟩ : syracuseStep 1319969 = 989977) B989977
theorem B2139331 : Blo 750330 2139331 := bstep (se 1 (by rfl) ⟨1604498, by rfl⟩ : syracuseStep 2139331 = 3208997) B3208997
theorem B2532653 : Blo 750330 2532653 := bstep (se 3 (by rfl) ⟨474872, by rfl⟩ : syracuseStep 2532653 = 949745) B949745
theorem B2532707 : Blo 750330 2532707 := bstep (se 1 (by rfl) ⟨1899530, by rfl⟩ : syracuseStep 2532707 = 3799061) B3799061
theorem B1287587 : Blo 750330 1287587 := bstep (se 1 (by rfl) ⟨965690, by rfl⟩ : syracuseStep 1287587 = 1931381) B1931381
theorem B3221041 : Blo 750330 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B2532977 : Blo 750330 2532977 := bstep (se 2 (by rfl) ⟨949866, by rfl⟩ : syracuseStep 2532977 = 1899733) B1899733
theorem B2139821 : Blo 750330 2139821 := bstep (se 3 (by rfl) ⟨401216, by rfl⟩ : syracuseStep 2139821 = 802433) B802433
theorem B1353457 : Blo 750330 1353457 := bstep (se 2 (by rfl) ⟨507546, by rfl⟩ : syracuseStep 1353457 = 1015093) B1015093
theorem B2533517 : Blo 750330 2533517 := bstep (se 3 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 2533517 = 950069) B950069
theorem B2533571 : Blo 750330 2533571 := bstep (se 1 (by rfl) ⟨1900178, by rfl⟩ : syracuseStep 2533571 = 3800357) B3800357
theorem B1222865 : Blo 750330 1222865 := bstep (se 2 (by rfl) ⟨458574, by rfl⟩ : syracuseStep 1222865 = 917149) B917149
theorem B3811697 : Blo 750330 3811697 := bstep (se 2 (by rfl) ⟨1429386, by rfl⟩ : syracuseStep 3811697 = 2858773) B2858773
theorem B2533841 : Blo 750330 2533841 := bstep (se 2 (by rfl) ⟨950190, by rfl⟩ : syracuseStep 2533841 = 1900381) B1900381
theorem B1223203 : Blo 750330 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B764515 : Blo 750330 764515 := bstep (se 1 (by rfl) ⟨573386, by rfl⟩ : syracuseStep 764515 = 1146773) B1146773
theorem B19507853 : Blo 750330 19507853 := bstep (se 3 (by rfl) ⟨3657722, by rfl⟩ : syracuseStep 19507853 = 7315445) B7315445
theorem B1157809 : Blo 750330 1157809 := bstep (se 2 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 1157809 = 868357) B868357
theorem B3058381 : Blo 750330 3058381 := bstep (se 3 (by rfl) ⟨573446, by rfl⟩ : syracuseStep 3058381 = 1146893) B1146893
theorem B2141005 : Blo 750330 2141005 := bstep (se 3 (by rfl) ⟨401438, by rfl⟩ : syracuseStep 2141005 = 802877) B802877
theorem B2534381 : Blo 750330 2534381 := bstep (se 3 (by rfl) ⟨475196, by rfl⟩ : syracuseStep 2534381 = 950393) B950393
theorem B2534435 : Blo 750330 2534435 := bstep (se 1 (by rfl) ⟨1900826, by rfl⟩ : syracuseStep 2534435 = 3801653) B3801653
theorem B1125521 : Blo 750330 1125521 := bstep (se 2 (by rfl) ⟨422070, by rfl⟩ : syracuseStep 1125521 = 844141) B844141
theorem B1125539 : Blo 750330 1125539 := bstep (se 1 (by rfl) ⟨844154, by rfl⟩ : syracuseStep 1125539 = 1688309) B1688309
theorem B1715377 : Blo 750330 1715377 := bstep (se 2 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 1715377 = 1286533) B1286533
theorem B1125569 : Blo 750330 1125569 := bstep (se 2 (by rfl) ⟨422088, by rfl⟩ : syracuseStep 1125569 = 844177) B844177
theorem B1125587 : Blo 750330 1125587 := bstep (se 1 (by rfl) ⟨844190, by rfl⟩ : syracuseStep 1125587 = 1688381) B1688381
theorem B1125617 : Blo 750330 1125617 := bstep (se 2 (by rfl) ⟨422106, by rfl⟩ : syracuseStep 1125617 = 844213) B844213
theorem B1125635 : Blo 750330 1125635 := bstep (se 1 (by rfl) ⟨844226, by rfl⟩ : syracuseStep 1125635 = 1688453) B1688453
theorem B1125665 : Blo 750330 1125665 := bstep (se 2 (by rfl) ⟨422124, by rfl⟩ : syracuseStep 1125665 = 844249) B844249
theorem B2534705 : Blo 750330 2534705 := bstep (se 2 (by rfl) ⟨950514, by rfl⟩ : syracuseStep 2534705 = 1901029) B1901029
theorem B1125683 : Blo 750330 1125683 := bstep (se 1 (by rfl) ⟨844262, by rfl⟩ : syracuseStep 1125683 = 1688525) B1688525
theorem B1125713 : Blo 750330 1125713 := bstep (se 2 (by rfl) ⟨422142, by rfl⟩ : syracuseStep 1125713 = 844285) B844285
theorem B1125731 : Blo 750330 1125731 := bstep (se 1 (by rfl) ⟨844298, by rfl⟩ : syracuseStep 1125731 = 1688597) B1688597
theorem B2862449 : Blo 750330 2862449 := bstep (se 2 (by rfl) ⟨1073418, by rfl⟩ : syracuseStep 2862449 = 2146837) B2146837
theorem B1125761 : Blo 750330 1125761 := bstep (se 2 (by rfl) ⟨422160, by rfl⟩ : syracuseStep 1125761 = 844321) B844321
theorem B1125779 : Blo 750330 1125779 := bstep (se 1 (by rfl) ⟨844334, by rfl⟩ : syracuseStep 1125779 = 1688669) B1688669
theorem B1125809 : Blo 750330 1125809 := bstep (se 2 (by rfl) ⟨422178, by rfl⟩ : syracuseStep 1125809 = 844357) B844357
theorem B1125827 : Blo 750330 1125827 := bstep (se 1 (by rfl) ⟨844370, by rfl⟩ : syracuseStep 1125827 = 1688741) B1688741
theorem B1125857 : Blo 750330 1125857 := bstep (se 2 (by rfl) ⟨422196, by rfl⟩ : syracuseStep 1125857 = 844393) B844393
theorem B2174435 : Blo 750330 2174435 := bstep (se 1 (by rfl) ⟨1630826, by rfl⟩ : syracuseStep 2174435 = 3261653) B3261653
theorem B1125875 : Blo 750330 1125875 := bstep (se 1 (by rfl) ⟨844406, by rfl⟩ : syracuseStep 1125875 = 1688813) B1688813
theorem B1125905 : Blo 750330 1125905 := bstep (se 2 (by rfl) ⟨422214, by rfl⟩ : syracuseStep 1125905 = 844429) B844429
theorem B1125923 : Blo 750330 1125923 := bstep (se 1 (by rfl) ⟨844442, by rfl⟩ : syracuseStep 1125923 = 1688885) B1688885
theorem B1125953 : Blo 750330 1125953 := bstep (se 2 (by rfl) ⟨422232, by rfl⟩ : syracuseStep 1125953 = 844465) B844465
theorem B1125971 : Blo 750330 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B1126001 : Blo 750330 1126001 := bstep (se 2 (by rfl) ⟨422250, by rfl⟩ : syracuseStep 1126001 = 844501) B844501
theorem B1126019 : Blo 750330 1126019 := bstep (se 1 (by rfl) ⟨844514, by rfl⟩ : syracuseStep 1126019 = 1689029) B1689029
theorem B1060499 : Blo 750330 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B1126049 : Blo 750330 1126049 := bstep (se 2 (by rfl) ⟨422268, by rfl⟩ : syracuseStep 1126049 = 844537) B844537
theorem B1126067 : Blo 750330 1126067 := bstep (se 1 (by rfl) ⟨844550, by rfl⟩ : syracuseStep 1126067 = 1689101) B1689101
theorem B1126097 : Blo 750330 1126097 := bstep (se 2 (by rfl) ⟨422286, by rfl⟩ : syracuseStep 1126097 = 844573) B844573
theorem B1126115 : Blo 750330 1126115 := bstep (se 1 (by rfl) ⟨844586, by rfl⟩ : syracuseStep 1126115 = 1689173) B1689173
theorem B1126145 : Blo 750330 1126145 := bstep (se 2 (by rfl) ⟨422304, by rfl⟩ : syracuseStep 1126145 = 844609) B844609
theorem B1126163 : Blo 750330 1126163 := bstep (se 1 (by rfl) ⟨844622, by rfl⟩ : syracuseStep 1126163 = 1689245) B1689245
theorem B3813155 : Blo 750330 3813155 := bstep (se 1 (by rfl) ⟨2859866, by rfl⟩ : syracuseStep 3813155 = 5719733) B5719733
theorem B1126193 : Blo 750330 1126193 := bstep (se 2 (by rfl) ⟨422322, by rfl⟩ : syracuseStep 1126193 = 844645) B844645
theorem B1126211 : Blo 750330 1126211 := bstep (se 1 (by rfl) ⟨844658, by rfl⟩ : syracuseStep 1126211 = 1689317) B1689317
theorem B2535245 : Blo 750330 2535245 := bstep (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) B950717
theorem B1126241 : Blo 750330 1126241 := bstep (se 2 (by rfl) ⟨422340, by rfl⟩ : syracuseStep 1126241 = 844681) B844681
theorem B10170211 : Blo 750330 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B2142065 : Blo 750330 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B1126259 : Blo 750330 1126259 := bstep (se 1 (by rfl) ⟨844694, by rfl⟩ : syracuseStep 1126259 = 1689389) B1689389
theorem B2535299 : Blo 750330 2535299 := bstep (se 1 (by rfl) ⟨1901474, by rfl⟩ : syracuseStep 2535299 = 3802949) B3802949
theorem B1126289 : Blo 750330 1126289 := bstep (se 2 (by rfl) ⟨422358, by rfl⟩ : syracuseStep 1126289 = 844717) B844717
theorem B1126307 : Blo 750330 1126307 := bstep (se 1 (by rfl) ⟨844730, by rfl⟩ : syracuseStep 1126307 = 1689461) B1689461
theorem B2895793 : Blo 750330 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B1126337 : Blo 750330 1126337 := bstep (se 2 (by rfl) ⟨422376, by rfl⟩ : syracuseStep 1126337 = 844753) B844753
theorem B1126355 : Blo 750330 1126355 := bstep (se 1 (by rfl) ⟨844766, by rfl⟩ : syracuseStep 1126355 = 1689533) B1689533
theorem B1126385 : Blo 750330 1126385 := bstep (se 2 (by rfl) ⟨422394, by rfl⟩ : syracuseStep 1126385 = 844789) B844789
theorem B1126403 : Blo 750330 1126403 := bstep (se 1 (by rfl) ⟨844802, by rfl⟩ : syracuseStep 1126403 = 1689605) B1689605
theorem B1126433 : Blo 750330 1126433 := bstep (se 2 (by rfl) ⟨422412, by rfl⟩ : syracuseStep 1126433 = 844825) B844825
theorem B1126451 : Blo 750330 1126451 := bstep (se 1 (by rfl) ⟨844838, by rfl⟩ : syracuseStep 1126451 = 1689677) B1689677
theorem B1126481 : Blo 750330 1126481 := bstep (se 2 (by rfl) ⟨422430, by rfl⟩ : syracuseStep 1126481 = 844861) B844861
theorem B1126499 : Blo 750330 1126499 := bstep (se 1 (by rfl) ⟨844874, by rfl⟩ : syracuseStep 1126499 = 1689749) B1689749
theorem B1126529 : Blo 750330 1126529 := bstep (se 2 (by rfl) ⟨422448, by rfl⟩ : syracuseStep 1126529 = 844897) B844897
theorem B2535569 : Blo 750330 2535569 := bstep (se 2 (by rfl) ⟨950838, by rfl⟩ : syracuseStep 2535569 = 1901677) B1901677
theorem B1126547 : Blo 750330 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B1126577 : Blo 750330 1126577 := bstep (se 2 (by rfl) ⟨422466, by rfl⟩ : syracuseStep 1126577 = 844933) B844933
theorem B1159361 : Blo 750330 1159361 := bstep (se 2 (by rfl) ⟨434760, by rfl⟩ : syracuseStep 1159361 = 869521) B869521
theorem B1126595 : Blo 750330 1126595 := bstep (se 1 (by rfl) ⟨844946, by rfl⟩ : syracuseStep 1126595 = 1689893) B1689893
theorem B1126625 : Blo 750330 1126625 := bstep (se 2 (by rfl) ⟨422484, by rfl⟩ : syracuseStep 1126625 = 844969) B844969
theorem B1126643 : Blo 750330 1126643 := bstep (se 1 (by rfl) ⟨844982, by rfl⟩ : syracuseStep 1126643 = 1689965) B1689965
theorem B1126673 : Blo 750330 1126673 := bstep (se 2 (by rfl) ⟨422502, by rfl⟩ : syracuseStep 1126673 = 845005) B845005
theorem B1126691 : Blo 750330 1126691 := bstep (se 1 (by rfl) ⟨845018, by rfl⟩ : syracuseStep 1126691 = 1690037) B1690037
theorem B4829489 : Blo 750330 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1126721 : Blo 750330 1126721 := bstep (se 2 (by rfl) ⟨422520, by rfl⟩ : syracuseStep 1126721 = 845041) B845041
theorem B1126739 : Blo 750330 1126739 := bstep (se 1 (by rfl) ⟨845054, by rfl⟩ : syracuseStep 1126739 = 1690109) B1690109
theorem B1126769 : Blo 750330 1126769 := bstep (se 2 (by rfl) ⟨422538, by rfl⟩ : syracuseStep 1126769 = 845077) B845077
theorem B1126787 : Blo 750330 1126787 := bstep (se 1 (by rfl) ⟨845090, by rfl⟩ : syracuseStep 1126787 = 1690181) B1690181
theorem B1126817 : Blo 750330 1126817 := bstep (se 2 (by rfl) ⟨422556, by rfl⟩ : syracuseStep 1126817 = 845113) B845113
theorem B1126835 : Blo 750330 1126835 := bstep (se 1 (by rfl) ⟨845126, by rfl⟩ : syracuseStep 1126835 = 1690253) B1690253
theorem B1126865 : Blo 750330 1126865 := bstep (se 2 (by rfl) ⟨422574, by rfl⟩ : syracuseStep 1126865 = 845149) B845149
theorem B1126883 : Blo 750330 1126883 := bstep (se 1 (by rfl) ⟨845162, by rfl⟩ : syracuseStep 1126883 = 1690325) B1690325
theorem B1126913 : Blo 750330 1126913 := bstep (se 2 (by rfl) ⟨422592, by rfl⟩ : syracuseStep 1126913 = 845185) B845185
theorem B2142737 : Blo 750330 2142737 := bstep (se 2 (by rfl) ⟨803526, by rfl⟩ : syracuseStep 2142737 = 1607053) B1607053
theorem B1126931 : Blo 750330 1126931 := bstep (se 1 (by rfl) ⟨845198, by rfl⟩ : syracuseStep 1126931 = 1690397) B1690397
theorem B1126961 : Blo 750330 1126961 := bstep (se 2 (by rfl) ⟨422610, by rfl⟩ : syracuseStep 1126961 = 845221) B845221
theorem B1126979 : Blo 750330 1126979 := bstep (se 1 (by rfl) ⟨845234, by rfl⟩ : syracuseStep 1126979 = 1690469) B1690469
theorem B3813965 : Blo 750330 3813965 := bstep (se 3 (by rfl) ⟨715118, by rfl⟩ : syracuseStep 3813965 = 1430237) B1430237
theorem B1127009 : Blo 750330 1127009 := bstep (se 2 (by rfl) ⟨422628, by rfl⟩ : syracuseStep 1127009 = 845257) B845257
theorem B1127027 : Blo 750330 1127027 := bstep (se 1 (by rfl) ⟨845270, by rfl⟩ : syracuseStep 1127027 = 1690541) B1690541
theorem B1127057 : Blo 750330 1127057 := bstep (se 2 (by rfl) ⟨422646, by rfl⟩ : syracuseStep 1127057 = 845293) B845293
theorem B1127075 : Blo 750330 1127075 := bstep (se 1 (by rfl) ⟨845306, by rfl⟩ : syracuseStep 1127075 = 1690613) B1690613
theorem B2536109 : Blo 750330 2536109 := bstep (se 3 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 2536109 = 951041) B951041
theorem B1127105 : Blo 750330 1127105 := bstep (se 2 (by rfl) ⟨422664, by rfl⟩ : syracuseStep 1127105 = 845329) B845329
theorem B1127123 : Blo 750330 1127123 := bstep (se 1 (by rfl) ⟨845342, by rfl⟩ : syracuseStep 1127123 = 1690685) B1690685
theorem B2536163 : Blo 750330 2536163 := bstep (se 1 (by rfl) ⟨1902122, by rfl⟩ : syracuseStep 2536163 = 3804245) B3804245
theorem B1127153 : Blo 750330 1127153 := bstep (se 2 (by rfl) ⟨422682, by rfl⟩ : syracuseStep 1127153 = 845365) B845365
theorem B1127171 : Blo 750330 1127171 := bstep (se 1 (by rfl) ⟨845378, by rfl⟩ : syracuseStep 1127171 = 1690757) B1690757
theorem B2175761 : Blo 750330 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B1127201 : Blo 750330 1127201 := bstep (se 2 (by rfl) ⟨422700, by rfl⟩ : syracuseStep 1127201 = 845401) B845401
theorem B2863907 : Blo 750330 2863907 := bstep (se 1 (by rfl) ⟨2147930, by rfl⟩ : syracuseStep 2863907 = 4295861) B4295861
theorem B1127219 : Blo 750330 1127219 := bstep (se 1 (by rfl) ⟨845414, by rfl⟩ : syracuseStep 1127219 = 1690829) B1690829
theorem B1127249 : Blo 750330 1127249 := bstep (se 2 (by rfl) ⟨422718, by rfl⟩ : syracuseStep 1127249 = 845437) B845437
theorem B1127267 : Blo 750330 1127267 := bstep (se 1 (by rfl) ⟨845450, by rfl⟩ : syracuseStep 1127267 = 1690901) B1690901
theorem B1127297 : Blo 750330 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B1127315 : Blo 750330 1127315 := bstep (se 1 (by rfl) ⟨845486, by rfl⟩ : syracuseStep 1127315 = 1690973) B1690973
theorem B1127345 : Blo 750330 1127345 := bstep (se 2 (by rfl) ⟨422754, by rfl⟩ : syracuseStep 1127345 = 845509) B845509
theorem B1127363 : Blo 750330 1127363 := bstep (se 1 (by rfl) ⟨845522, by rfl⟩ : syracuseStep 1127363 = 1691045) B1691045
theorem B1127393 : Blo 750330 1127393 := bstep (se 2 (by rfl) ⟨422772, by rfl⟩ : syracuseStep 1127393 = 845545) B845545
theorem B2536433 : Blo 750330 2536433 := bstep (se 2 (by rfl) ⟨951162, by rfl⟩ : syracuseStep 2536433 = 1902325) B1902325
theorem B1127411 : Blo 750330 1127411 := bstep (se 1 (by rfl) ⟨845558, by rfl⟩ : syracuseStep 1127411 = 1691117) B1691117
theorem B1127441 : Blo 750330 1127441 := bstep (se 2 (by rfl) ⟨422790, by rfl⟩ : syracuseStep 1127441 = 845581) B845581
theorem B1127459 : Blo 750330 1127459 := bstep (se 1 (by rfl) ⟨845594, by rfl⟩ : syracuseStep 1127459 = 1691189) B1691189
theorem B1127489 : Blo 750330 1127489 := bstep (se 2 (by rfl) ⟨422808, by rfl⟩ : syracuseStep 1127489 = 845617) B845617
theorem B1127507 : Blo 750330 1127507 := bstep (se 1 (by rfl) ⟨845630, by rfl⟩ : syracuseStep 1127507 = 1691261) B1691261
theorem B1127537 : Blo 750330 1127537 := bstep (se 2 (by rfl) ⟨422826, by rfl⟩ : syracuseStep 1127537 = 845653) B845653
theorem B1127555 : Blo 750330 1127555 := bstep (se 1 (by rfl) ⟨845666, by rfl⟩ : syracuseStep 1127555 = 1691333) B1691333
theorem B1356931 : Blo 750330 1356931 := bstep (se 1 (by rfl) ⟨1017698, by rfl⟩ : syracuseStep 1356931 = 2035397) B2035397
theorem B1127585 : Blo 750330 1127585 := bstep (se 2 (by rfl) ⟨422844, by rfl⟩ : syracuseStep 1127585 = 845689) B845689
theorem B1127603 : Blo 750330 1127603 := bstep (se 1 (by rfl) ⟨845702, by rfl⟩ : syracuseStep 1127603 = 1691405) B1691405
theorem B1127633 : Blo 750330 1127633 := bstep (se 2 (by rfl) ⟨422862, by rfl⟩ : syracuseStep 1127633 = 845725) B845725
theorem B1127651 : Blo 750330 1127651 := bstep (se 1 (by rfl) ⟨845738, by rfl⟩ : syracuseStep 1127651 = 1691477) B1691477
theorem B1127681 : Blo 750330 1127681 := bstep (se 2 (by rfl) ⟨422880, by rfl⟩ : syracuseStep 1127681 = 845761) B845761
theorem B1127699 : Blo 750330 1127699 := bstep (se 1 (by rfl) ⟨845774, by rfl⟩ : syracuseStep 1127699 = 1691549) B1691549
theorem B2143523 : Blo 750330 2143523 := bstep (se 1 (by rfl) ⟨1607642, by rfl⟩ : syracuseStep 2143523 = 3215285) B3215285
theorem B1127729 : Blo 750330 1127729 := bstep (se 2 (by rfl) ⟨422898, by rfl⟩ : syracuseStep 1127729 = 845797) B845797
theorem B1127747 : Blo 750330 1127747 := bstep (se 1 (by rfl) ⟨845810, by rfl⟩ : syracuseStep 1127747 = 1691621) B1691621
theorem B1127777 : Blo 750330 1127777 := bstep (se 2 (by rfl) ⟨422916, by rfl⟩ : syracuseStep 1127777 = 845833) B845833
theorem B1127795 : Blo 750330 1127795 := bstep (se 1 (by rfl) ⟨845846, by rfl⟩ : syracuseStep 1127795 = 1691693) B1691693
theorem B1127825 : Blo 750330 1127825 := bstep (se 2 (by rfl) ⟨422934, by rfl⟩ : syracuseStep 1127825 = 845869) B845869
theorem B1127843 : Blo 750330 1127843 := bstep (se 1 (by rfl) ⟨845882, by rfl⟩ : syracuseStep 1127843 = 1691765) B1691765
theorem B1127873 : Blo 750330 1127873 := bstep (se 2 (by rfl) ⟨422952, by rfl⟩ : syracuseStep 1127873 = 845905) B845905
theorem B2405837 : Blo 750330 2405837 := bstep (se 3 (by rfl) ⟨451094, by rfl⟩ : syracuseStep 2405837 = 902189) B902189
theorem B1127891 : Blo 750330 1127891 := bstep (se 1 (by rfl) ⟨845918, by rfl⟩ : syracuseStep 1127891 = 1691837) B1691837
theorem B1127921 : Blo 750330 1127921 := bstep (se 2 (by rfl) ⟨422970, by rfl⟩ : syracuseStep 1127921 = 845941) B845941
theorem B1127939 : Blo 750330 1127939 := bstep (se 1 (by rfl) ⟨845954, by rfl⟩ : syracuseStep 1127939 = 1691909) B1691909
theorem B2536973 : Blo 750330 2536973 := bstep (se 3 (by rfl) ⟨475682, by rfl⟩ : syracuseStep 2536973 = 951365) B951365
theorem B1127969 : Blo 750330 1127969 := bstep (se 2 (by rfl) ⟨422988, by rfl⟩ : syracuseStep 1127969 = 845977) B845977
theorem B1127987 : Blo 750330 1127987 := bstep (se 1 (by rfl) ⟨845990, by rfl⟩ : syracuseStep 1127987 = 1691981) B1691981
theorem B2537027 : Blo 750330 2537027 := bstep (se 1 (by rfl) ⟨1902770, by rfl⟩ : syracuseStep 2537027 = 3805541) B3805541
theorem B1128017 : Blo 750330 1128017 := bstep (se 2 (by rfl) ⟨423006, by rfl⟩ : syracuseStep 1128017 = 846013) B846013
theorem B1357393 : Blo 750330 1357393 := bstep (se 2 (by rfl) ⟨509022, by rfl⟩ : syracuseStep 1357393 = 1018045) B1018045
theorem B1128035 : Blo 750330 1128035 := bstep (se 1 (by rfl) ⟨846026, by rfl⟩ : syracuseStep 1128035 = 1692053) B1692053
theorem B2143853 : Blo 750330 2143853 := bstep (se 3 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 2143853 = 803945) B803945
theorem B1128065 : Blo 750330 1128065 := bstep (se 2 (by rfl) ⟨423024, by rfl⟩ : syracuseStep 1128065 = 846049) B846049
theorem B1128083 : Blo 750330 1128083 := bstep (se 1 (by rfl) ⟨846062, by rfl⟩ : syracuseStep 1128083 = 1692125) B1692125
theorem B1128113 : Blo 750330 1128113 := bstep (se 2 (by rfl) ⟨423042, by rfl⟩ : syracuseStep 1128113 = 846085) B846085
theorem B2143921 : Blo 750330 2143921 := bstep (se 2 (by rfl) ⟨803970, by rfl⟩ : syracuseStep 2143921 = 1607941) B1607941
theorem B1128131 : Blo 750330 1128131 := bstep (se 1 (by rfl) ⟨846098, by rfl⟩ : syracuseStep 1128131 = 1692197) B1692197
theorem B1128161 : Blo 750330 1128161 := bstep (se 2 (by rfl) ⟨423060, by rfl⟩ : syracuseStep 1128161 = 846121) B846121
theorem B4830947 : Blo 750330 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B1128179 : Blo 750330 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B1128209 : Blo 750330 1128209 := bstep (se 2 (by rfl) ⟨423078, by rfl⟩ : syracuseStep 1128209 = 846157) B846157
theorem B1128227 : Blo 750330 1128227 := bstep (se 1 (by rfl) ⟨846170, by rfl⟩ : syracuseStep 1128227 = 1692341) B1692341
theorem B1128257 : Blo 750330 1128257 := bstep (se 2 (by rfl) ⟨423096, by rfl⟩ : syracuseStep 1128257 = 846193) B846193
theorem B2537297 : Blo 750330 2537297 := bstep (se 2 (by rfl) ⟨951486, by rfl⟩ : syracuseStep 2537297 = 1902973) B1902973
theorem B1128275 : Blo 750330 1128275 := bstep (se 1 (by rfl) ⟨846206, by rfl⟩ : syracuseStep 1128275 = 1692413) B1692413
theorem B1128305 : Blo 750330 1128305 := bstep (se 2 (by rfl) ⟨423114, by rfl⟩ : syracuseStep 1128305 = 846229) B846229
theorem B1128323 : Blo 750330 1128323 := bstep (se 1 (by rfl) ⟨846242, by rfl⟩ : syracuseStep 1128323 = 1692485) B1692485
theorem B1128353 : Blo 750330 1128353 := bstep (se 2 (by rfl) ⟨423132, by rfl⟩ : syracuseStep 1128353 = 846265) B846265
theorem B1128371 : Blo 750330 1128371 := bstep (se 1 (by rfl) ⟨846278, by rfl⟩ : syracuseStep 1128371 = 1692557) B1692557
theorem B2144195 : Blo 750330 2144195 := bstep (se 1 (by rfl) ⟨1608146, by rfl⟩ : syracuseStep 2144195 = 3216293) B3216293
theorem B1128401 : Blo 750330 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B1128419 : Blo 750330 1128419 := bstep (se 1 (by rfl) ⟨846314, by rfl⟩ : syracuseStep 1128419 = 1692629) B1692629
theorem B2570221 : Blo 750330 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B1128449 : Blo 750330 1128449 := bstep (se 2 (by rfl) ⟨423168, by rfl⟩ : syracuseStep 1128449 = 846337) B846337
theorem B1128467 : Blo 750330 1128467 := bstep (se 1 (by rfl) ⟨846350, by rfl⟩ : syracuseStep 1128467 = 1692701) B1692701
theorem B1128497 : Blo 750330 1128497 := bstep (se 2 (by rfl) ⟨423186, by rfl⟩ : syracuseStep 1128497 = 846373) B846373
theorem B1521731 : Blo 750330 1521731 := bstep (se 1 (by rfl) ⟨1141298, by rfl⟩ : syracuseStep 1521731 = 2282597) B2282597
theorem B1128515 : Blo 750330 1128515 := bstep (se 1 (by rfl) ⟨846386, by rfl⟩ : syracuseStep 1128515 = 1692773) B1692773
theorem B1128545 : Blo 750330 1128545 := bstep (se 2 (by rfl) ⟨423204, by rfl⟩ : syracuseStep 1128545 = 846409) B846409
theorem B1128563 : Blo 750330 1128563 := bstep (se 1 (by rfl) ⟨846422, by rfl⟩ : syracuseStep 1128563 = 1692845) B1692845
theorem B1357955 : Blo 750330 1357955 := bstep (se 1 (by rfl) ⟨1018466, by rfl⟩ : syracuseStep 1357955 = 2036933) B2036933
theorem B4274309 : Blo 750330 4274309 := bstep (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) B801433
theorem B1128593 : Blo 750330 1128593 := bstep (se 2 (by rfl) ⟨423222, by rfl⟩ : syracuseStep 1128593 = 846445) B846445
theorem B1128611 : Blo 750330 1128611 := bstep (se 1 (by rfl) ⟨846458, by rfl⟩ : syracuseStep 1128611 = 1692917) B1692917
theorem B1128641 : Blo 750330 1128641 := bstep (se 2 (by rfl) ⟨423240, by rfl⟩ : syracuseStep 1128641 = 846481) B846481
theorem B1128659 : Blo 750330 1128659 := bstep (se 1 (by rfl) ⟨846494, by rfl⟩ : syracuseStep 1128659 = 1692989) B1692989
theorem B1128689 : Blo 750330 1128689 := bstep (se 2 (by rfl) ⟨423258, by rfl⟩ : syracuseStep 1128689 = 846517) B846517
theorem B1128707 : Blo 750330 1128707 := bstep (se 1 (by rfl) ⟨846530, by rfl⟩ : syracuseStep 1128707 = 1693061) B1693061
theorem B1128737 : Blo 750330 1128737 := bstep (se 2 (by rfl) ⟨423276, by rfl⟩ : syracuseStep 1128737 = 846553) B846553
theorem B1128755 : Blo 750330 1128755 := bstep (se 1 (by rfl) ⟨846566, by rfl⟩ : syracuseStep 1128755 = 1693133) B1693133
theorem B1128785 : Blo 750330 1128785 := bstep (se 2 (by rfl) ⟨423294, by rfl⟩ : syracuseStep 1128785 = 846589) B846589
theorem B964963 : Blo 750330 964963 := bstep (se 1 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 964963 = 1447445) B1447445
theorem B1128803 : Blo 750330 1128803 := bstep (se 1 (by rfl) ⟨846602, by rfl⟩ : syracuseStep 1128803 = 1693205) B1693205
theorem B2537837 : Blo 750330 2537837 := bstep (se 3 (by rfl) ⟨475844, by rfl⟩ : syracuseStep 2537837 = 951689) B951689
theorem B1128833 : Blo 750330 1128833 := bstep (se 2 (by rfl) ⟨423312, by rfl⟩ : syracuseStep 1128833 = 846625) B846625
theorem B1128851 : Blo 750330 1128851 := bstep (se 1 (by rfl) ⟨846638, by rfl⟩ : syracuseStep 1128851 = 1693277) B1693277
theorem B2537891 : Blo 750330 2537891 := bstep (se 1 (by rfl) ⟨1903418, by rfl⟩ : syracuseStep 2537891 = 3806837) B3806837
theorem B1128881 : Blo 750330 1128881 := bstep (se 2 (by rfl) ⟨423330, by rfl⟩ : syracuseStep 1128881 = 846661) B846661
theorem B1128899 : Blo 750330 1128899 := bstep (se 1 (by rfl) ⟨846674, by rfl⟩ : syracuseStep 1128899 = 1693349) B1693349
theorem B1128929 : Blo 750330 1128929 := bstep (se 2 (by rfl) ⟨423348, by rfl⟩ : syracuseStep 1128929 = 846697) B846697
theorem B1128947 : Blo 750330 1128947 := bstep (se 1 (by rfl) ⟨846710, by rfl⟩ : syracuseStep 1128947 = 1693421) B1693421
theorem B1128977 : Blo 750330 1128977 := bstep (se 2 (by rfl) ⟨423366, by rfl⟩ : syracuseStep 1128977 = 846733) B846733
theorem B1128995 : Blo 750330 1128995 := bstep (se 1 (by rfl) ⟨846746, by rfl⟩ : syracuseStep 1128995 = 1693493) B1693493
theorem B1129025 : Blo 750330 1129025 := bstep (se 2 (by rfl) ⟨423384, by rfl⟩ : syracuseStep 1129025 = 846769) B846769
theorem B4274765 : Blo 750330 4274765 := bstep (se 3 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 4274765 = 1603037) B1603037
theorem B1129043 : Blo 750330 1129043 := bstep (se 1 (by rfl) ⟨846782, by rfl⟩ : syracuseStep 1129043 = 1693565) B1693565
theorem B1129073 : Blo 750330 1129073 := bstep (se 2 (by rfl) ⟨423402, by rfl⟩ : syracuseStep 1129073 = 846805) B846805
theorem B1129091 : Blo 750330 1129091 := bstep (se 1 (by rfl) ⟨846818, by rfl⟩ : syracuseStep 1129091 = 1693637) B1693637
theorem B1129121 : Blo 750330 1129121 := bstep (se 2 (by rfl) ⟨423420, by rfl⟩ : syracuseStep 1129121 = 846841) B846841
theorem B2538161 : Blo 750330 2538161 := bstep (se 2 (by rfl) ⟨951810, by rfl⟩ : syracuseStep 2538161 = 1903621) B1903621
theorem B1129139 : Blo 750330 1129139 := bstep (se 1 (by rfl) ⟨846854, by rfl⟩ : syracuseStep 1129139 = 1693709) B1693709
theorem B1129169 : Blo 750330 1129169 := bstep (se 2 (by rfl) ⟨423438, by rfl⟩ : syracuseStep 1129169 = 846877) B846877
theorem B1129187 : Blo 750330 1129187 := bstep (se 1 (by rfl) ⟨846890, by rfl⟩ : syracuseStep 1129187 = 1693781) B1693781
theorem B1129217 : Blo 750330 1129217 := bstep (se 2 (by rfl) ⟨423456, by rfl⟩ : syracuseStep 1129217 = 846913) B846913
theorem B2145037 : Blo 750330 2145037 := bstep (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) B804389
theorem B1129235 : Blo 750330 1129235 := bstep (se 1 (by rfl) ⟨846926, by rfl⟩ : syracuseStep 1129235 = 1693853) B1693853
theorem B1129265 : Blo 750330 1129265 := bstep (se 2 (by rfl) ⟨423474, by rfl⟩ : syracuseStep 1129265 = 846949) B846949
theorem B801587 : Blo 750330 801587 := bstep (se 1 (by rfl) ⟨601190, by rfl⟩ : syracuseStep 801587 = 1202381) B1202381
theorem B19249973 : Blo 750330 19249973 := bstep (se 5 (by rfl) ⟨902342, by rfl⟩ : syracuseStep 19249973 = 1804685) B1804685
theorem B1129283 : Blo 750330 1129283 := bstep (se 1 (by rfl) ⟨846962, by rfl⟩ : syracuseStep 1129283 = 1693925) B1693925
theorem B1129313 : Blo 750330 1129313 := bstep (se 2 (by rfl) ⟨423492, by rfl⟩ : syracuseStep 1129313 = 846985) B846985
theorem B1129331 : Blo 750330 1129331 := bstep (se 1 (by rfl) ⟨846998, by rfl⟩ : syracuseStep 1129331 = 1693997) B1693997
theorem B1129361 : Blo 750330 1129361 := bstep (se 2 (by rfl) ⟨423510, by rfl⟩ : syracuseStep 1129361 = 847021) B847021
theorem B1129379 : Blo 750330 1129379 := bstep (se 1 (by rfl) ⟨847034, by rfl⟩ : syracuseStep 1129379 = 1694069) B1694069
theorem B2145197 : Blo 750330 2145197 := bstep (se 3 (by rfl) ⟨402224, by rfl⟩ : syracuseStep 2145197 = 804449) B804449
theorem B1129409 : Blo 750330 1129409 := bstep (se 2 (by rfl) ⟨423528, by rfl⟩ : syracuseStep 1129409 = 847057) B847057
theorem B1129427 : Blo 750330 1129427 := bstep (se 1 (by rfl) ⟨847070, by rfl⟩ : syracuseStep 1129427 = 1694141) B1694141
theorem B1129457 : Blo 750330 1129457 := bstep (se 2 (by rfl) ⟨423546, by rfl⟩ : syracuseStep 1129457 = 847093) B847093
theorem B2407427 : Blo 750330 2407427 := bstep (se 1 (by rfl) ⟨1805570, by rfl⟩ : syracuseStep 2407427 = 3611141) B3611141
theorem B1129475 : Blo 750330 1129475 := bstep (se 1 (by rfl) ⟨847106, by rfl⟩ : syracuseStep 1129475 = 1694213) B1694213
theorem B1129505 : Blo 750330 1129505 := bstep (se 2 (by rfl) ⟨423564, by rfl⟩ : syracuseStep 1129505 = 847129) B847129
theorem B1129523 : Blo 750330 1129523 := bstep (se 1 (by rfl) ⟨847142, by rfl⟩ : syracuseStep 1129523 = 1694285) B1694285
theorem B1129553 : Blo 750330 1129553 := bstep (se 2 (by rfl) ⟨423582, by rfl⟩ : syracuseStep 1129553 = 847165) B847165
theorem B1129571 : Blo 750330 1129571 := bstep (se 1 (by rfl) ⟨847178, by rfl⟩ : syracuseStep 1129571 = 1694357) B1694357
theorem B2145379 : Blo 750330 2145379 := bstep (se 1 (by rfl) ⟨1609034, by rfl⟩ : syracuseStep 2145379 = 3218069) B3218069
theorem B1129601 : Blo 750330 1129601 := bstep (se 2 (by rfl) ⟨423600, by rfl⟩ : syracuseStep 1129601 = 847201) B847201
theorem B3619981 : Blo 750330 3619981 := bstep (se 3 (by rfl) ⟨678746, by rfl⟩ : syracuseStep 3619981 = 1357493) B1357493
theorem B1358993 : Blo 750330 1358993 := bstep (se 2 (by rfl) ⟨509622, by rfl⟩ : syracuseStep 1358993 = 1019245) B1019245
theorem B1129619 : Blo 750330 1129619 := bstep (se 1 (by rfl) ⟨847214, by rfl⟩ : syracuseStep 1129619 = 1694429) B1694429
theorem B1129649 : Blo 750330 1129649 := bstep (se 2 (by rfl) ⟨423618, by rfl⟩ : syracuseStep 1129649 = 847237) B847237
theorem B1129667 : Blo 750330 1129667 := bstep (se 1 (by rfl) ⟨847250, by rfl⟩ : syracuseStep 1129667 = 1694501) B1694501
theorem B2538701 : Blo 750330 2538701 := bstep (se 3 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 2538701 = 952013) B952013
theorem B1129697 : Blo 750330 1129697 := bstep (se 2 (by rfl) ⟨423636, by rfl⟩ : syracuseStep 1129697 = 847273) B847273
theorem B1129715 : Blo 750330 1129715 := bstep (se 1 (by rfl) ⟨847286, by rfl⟩ : syracuseStep 1129715 = 1694573) B1694573
theorem B2538755 : Blo 750330 2538755 := bstep (se 1 (by rfl) ⟨1904066, by rfl⟩ : syracuseStep 2538755 = 3808133) B3808133
theorem B1129745 : Blo 750330 1129745 := bstep (se 2 (by rfl) ⟨423654, by rfl⟩ : syracuseStep 1129745 = 847309) B847309
theorem B1129763 : Blo 750330 1129763 := bstep (se 1 (by rfl) ⟨847322, by rfl⟩ : syracuseStep 1129763 = 1694645) B1694645
theorem B1129793 : Blo 750330 1129793 := bstep (se 2 (by rfl) ⟨423672, by rfl⟩ : syracuseStep 1129793 = 847345) B847345
theorem B1129811 : Blo 750330 1129811 := bstep (se 1 (by rfl) ⟨847358, by rfl⟩ : syracuseStep 1129811 = 1694717) B1694717
theorem B1129841 : Blo 750330 1129841 := bstep (se 2 (by rfl) ⟨423690, by rfl⟩ : syracuseStep 1129841 = 847381) B847381
theorem B1359217 : Blo 750330 1359217 := bstep (se 2 (by rfl) ⟨509706, by rfl⟩ : syracuseStep 1359217 = 1019413) B1019413
theorem B1129859 : Blo 750330 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B1424785 : Blo 750330 1424785 := bstep (se 2 (by rfl) ⟨534294, by rfl⟩ : syracuseStep 1424785 = 1068589) B1068589
theorem B1129889 : Blo 750330 1129889 := bstep (se 2 (by rfl) ⟨423708, by rfl⟩ : syracuseStep 1129889 = 847417) B847417
theorem B3816881 : Blo 750330 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B1129907 : Blo 750330 1129907 := bstep (se 1 (by rfl) ⟨847430, by rfl⟩ : syracuseStep 1129907 = 1694861) B1694861
theorem B1129937 : Blo 750330 1129937 := bstep (se 2 (by rfl) ⟨423726, by rfl⟩ : syracuseStep 1129937 = 847453) B847453
theorem B1129955 : Blo 750330 1129955 := bstep (se 1 (by rfl) ⟨847466, by rfl⟩ : syracuseStep 1129955 = 1694933) B1694933
theorem B966131 : Blo 750330 966131 := bstep (se 1 (by rfl) ⟨724598, by rfl⟩ : syracuseStep 966131 = 1449197) B1449197
theorem B1129985 : Blo 750330 1129985 := bstep (se 2 (by rfl) ⟨423744, by rfl⟩ : syracuseStep 1129985 = 847489) B847489
theorem B2539025 : Blo 750330 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B1130003 : Blo 750330 1130003 := bstep (se 1 (by rfl) ⟨847502, by rfl⟩ : syracuseStep 1130003 = 1695005) B1695005
theorem B1424945 : Blo 750330 1424945 := bstep (se 2 (by rfl) ⟨534354, by rfl⟩ : syracuseStep 1424945 = 1068709) B1068709
theorem B1130033 : Blo 750330 1130033 := bstep (se 2 (by rfl) ⟨423762, by rfl⟩ : syracuseStep 1130033 = 847525) B847525
theorem B1130051 : Blo 750330 1130051 := bstep (se 1 (by rfl) ⟨847538, by rfl⟩ : syracuseStep 1130051 = 1695077) B1695077
theorem B1130081 : Blo 750330 1130081 := bstep (se 2 (by rfl) ⟨423780, by rfl⟩ : syracuseStep 1130081 = 847561) B847561
theorem B1130099 : Blo 750330 1130099 := bstep (se 1 (by rfl) ⟨847574, by rfl⟩ : syracuseStep 1130099 = 1695149) B1695149
theorem B1130129 : Blo 750330 1130129 := bstep (se 2 (by rfl) ⟨423798, by rfl⟩ : syracuseStep 1130129 = 847597) B847597
theorem B1130147 : Blo 750330 1130147 := bstep (se 1 (by rfl) ⟨847610, by rfl⟩ : syracuseStep 1130147 = 1695221) B1695221
theorem B1130177 : Blo 750330 1130177 := bstep (se 2 (by rfl) ⟨423816, by rfl⟩ : syracuseStep 1130177 = 847633) B847633
theorem B1130195 : Blo 750330 1130195 := bstep (se 1 (by rfl) ⟨847646, by rfl⟩ : syracuseStep 1130195 = 1695293) B1695293
theorem B1130225 : Blo 750330 1130225 := bstep (se 2 (by rfl) ⟨423834, by rfl⟩ : syracuseStep 1130225 = 847669) B847669
theorem B1130243 : Blo 750330 1130243 := bstep (se 1 (by rfl) ⟨847682, by rfl⟩ : syracuseStep 1130243 = 1695365) B1695365
theorem B1130273 : Blo 750330 1130273 := bstep (se 2 (by rfl) ⟨423852, by rfl⟩ : syracuseStep 1130273 = 847705) B847705
theorem B802595 : Blo 750330 802595 := bstep (se 1 (by rfl) ⟨601946, by rfl⟩ : syracuseStep 802595 = 1203893) B1203893
theorem B1130291 : Blo 750330 1130291 := bstep (se 1 (by rfl) ⟨847718, by rfl⟩ : syracuseStep 1130291 = 1695437) B1695437
theorem B1130321 : Blo 750330 1130321 := bstep (se 2 (by rfl) ⟨423870, by rfl⟩ : syracuseStep 1130321 = 847741) B847741
theorem B1130339 : Blo 750330 1130339 := bstep (se 1 (by rfl) ⟨847754, by rfl⟩ : syracuseStep 1130339 = 1695509) B1695509
theorem B1130369 : Blo 750330 1130369 := bstep (se 2 (by rfl) ⟨423888, by rfl⟩ : syracuseStep 1130369 = 847777) B847777
theorem B1130387 : Blo 750330 1130387 := bstep (se 1 (by rfl) ⟨847790, by rfl⟩ : syracuseStep 1130387 = 1695581) B1695581
theorem B1130417 : Blo 750330 1130417 := bstep (se 2 (by rfl) ⟨423906, by rfl⟩ : syracuseStep 1130417 = 847813) B847813
theorem B1425347 : Blo 750330 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B1130435 : Blo 750330 1130435 := bstep (se 1 (by rfl) ⟨847826, by rfl⟩ : syracuseStep 1130435 = 1695653) B1695653
theorem B1130465 : Blo 750330 1130465 := bstep (se 2 (by rfl) ⟨423924, by rfl⟩ : syracuseStep 1130465 = 847849) B847849
theorem B1130483 : Blo 750330 1130483 := bstep (se 1 (by rfl) ⟨847862, by rfl⟩ : syracuseStep 1130483 = 1695725) B1695725
theorem B1130513 : Blo 750330 1130513 := bstep (se 2 (by rfl) ⟨423942, by rfl⟩ : syracuseStep 1130513 = 847885) B847885
theorem B1130531 : Blo 750330 1130531 := bstep (se 1 (by rfl) ⟨847898, by rfl⟩ : syracuseStep 1130531 = 1695797) B1695797
theorem B2539565 : Blo 750330 2539565 := bstep (se 3 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 2539565 = 952337) B952337
theorem B1130561 : Blo 750330 1130561 := bstep (se 2 (by rfl) ⟨423960, by rfl⟩ : syracuseStep 1130561 = 847921) B847921
theorem B1130579 : Blo 750330 1130579 := bstep (se 1 (by rfl) ⟨847934, by rfl⟩ : syracuseStep 1130579 = 1695869) B1695869
theorem B2539619 : Blo 750330 2539619 := bstep (se 1 (by rfl) ⟨1904714, by rfl⟩ : syracuseStep 2539619 = 3809429) B3809429
theorem B1130609 : Blo 750330 1130609 := bstep (se 2 (by rfl) ⟨423978, by rfl⟩ : syracuseStep 1130609 = 847957) B847957
theorem B1130627 : Blo 750330 1130627 := bstep (se 1 (by rfl) ⟨847970, by rfl⟩ : syracuseStep 1130627 = 1695941) B1695941
theorem B1130657 : Blo 750330 1130657 := bstep (se 2 (by rfl) ⟨423996, by rfl⟩ : syracuseStep 1130657 = 847993) B847993
theorem B1130675 : Blo 750330 1130675 := bstep (se 1 (by rfl) ⟨848006, by rfl⟩ : syracuseStep 1130675 = 1696013) B1696013
theorem B1130705 : Blo 750330 1130705 := bstep (se 2 (by rfl) ⟨424014, by rfl⟩ : syracuseStep 1130705 = 848029) B848029
theorem B1130723 : Blo 750330 1130723 := bstep (se 1 (by rfl) ⟨848042, by rfl⟩ : syracuseStep 1130723 = 1696085) B1696085
theorem B1130753 : Blo 750330 1130753 := bstep (se 2 (by rfl) ⟨424032, by rfl⟩ : syracuseStep 1130753 = 848065) B848065
theorem B2408707 : Blo 750330 2408707 := bstep (se 1 (by rfl) ⟨1806530, by rfl⟩ : syracuseStep 2408707 = 3613061) B3613061
theorem B1130771 : Blo 750330 1130771 := bstep (se 1 (by rfl) ⟨848078, by rfl⟩ : syracuseStep 1130771 = 1696157) B1696157
theorem B1130801 : Blo 750330 1130801 := bstep (se 2 (by rfl) ⟨424050, by rfl⟩ : syracuseStep 1130801 = 848101) B848101
theorem B1130819 : Blo 750330 1130819 := bstep (se 1 (by rfl) ⟨848114, by rfl⟩ : syracuseStep 1130819 = 1696229) B1696229
theorem B901459 : Blo 750330 901459 := bstep (se 1 (by rfl) ⟨676094, by rfl⟩ : syracuseStep 901459 = 1352189) B1352189
theorem B1130849 : Blo 750330 1130849 := bstep (se 2 (by rfl) ⟨424068, by rfl⟩ : syracuseStep 1130849 = 848137) B848137
theorem B2539889 : Blo 750330 2539889 := bstep (se 2 (by rfl) ⟨952458, by rfl⟩ : syracuseStep 2539889 = 1904917) B1904917
theorem B1130867 : Blo 750330 1130867 := bstep (se 1 (by rfl) ⟨848150, by rfl⟩ : syracuseStep 1130867 = 1696301) B1696301
theorem B1130897 : Blo 750330 1130897 := bstep (se 2 (by rfl) ⟨424086, by rfl⟩ : syracuseStep 1130897 = 848173) B848173
theorem B1130915 : Blo 750330 1130915 := bstep (se 1 (by rfl) ⟨848186, by rfl⟩ : syracuseStep 1130915 = 1696373) B1696373
theorem B1130945 : Blo 750330 1130945 := bstep (se 2 (by rfl) ⟨424104, by rfl⟩ : syracuseStep 1130945 = 848209) B848209
theorem B5489093 : Blo 750330 5489093 := bstep (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) B1029205
theorem B2146769 : Blo 750330 2146769 := bstep (se 2 (by rfl) ⟨805038, by rfl⟩ : syracuseStep 2146769 = 1610077) B1610077
theorem B1130963 : Blo 750330 1130963 := bstep (se 1 (by rfl) ⟨848222, by rfl⟩ : syracuseStep 1130963 = 1696445) B1696445
theorem B1130993 : Blo 750330 1130993 := bstep (se 2 (by rfl) ⟨424122, by rfl⟩ : syracuseStep 1130993 = 848245) B848245
theorem B1131011 : Blo 750330 1131011 := bstep (se 1 (by rfl) ⟨848258, by rfl⟩ : syracuseStep 1131011 = 1696517) B1696517
theorem B1131041 : Blo 750330 1131041 := bstep (se 2 (by rfl) ⟨424140, by rfl⟩ : syracuseStep 1131041 = 848281) B848281
theorem B1131059 : Blo 750330 1131059 := bstep (se 1 (by rfl) ⟨848294, by rfl⟩ : syracuseStep 1131059 = 1696589) B1696589
theorem B2409041 : Blo 750330 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B1131089 : Blo 750330 1131089 := bstep (se 2 (by rfl) ⟨424158, by rfl⟩ : syracuseStep 1131089 = 848317) B848317
theorem B1131107 : Blo 750330 1131107 := bstep (se 1 (by rfl) ⟨848330, by rfl⟩ : syracuseStep 1131107 = 1696661) B1696661
theorem B7225969 : Blo 750330 7225969 := bstep (se 2 (by rfl) ⟨2709738, by rfl⟩ : syracuseStep 7225969 = 5419477) B5419477
theorem B1131137 : Blo 750330 1131137 := bstep (se 2 (by rfl) ⟨424176, by rfl⟩ : syracuseStep 1131137 = 848353) B848353
theorem B1131155 : Blo 750330 1131155 := bstep (se 1 (by rfl) ⟨848366, by rfl⟩ : syracuseStep 1131155 = 1696733) B1696733
theorem B1131185 : Blo 750330 1131185 := bstep (se 2 (by rfl) ⟨424194, by rfl⟩ : syracuseStep 1131185 = 848389) B848389
theorem B1131203 : Blo 750330 1131203 := bstep (se 1 (by rfl) ⟨848402, by rfl⟩ : syracuseStep 1131203 = 1696805) B1696805
theorem B6439621 : Blo 750330 6439621 := bstep (se 4 (by rfl) ⟨603714, by rfl⟩ : syracuseStep 6439621 = 1207429) B1207429
theorem B1688273 : Blo 750330 1688273 := bstep (se 2 (by rfl) ⟨633102, by rfl⟩ : syracuseStep 1688273 = 1266205) B1266205
theorem B1131233 : Blo 750330 1131233 := bstep (se 2 (by rfl) ⟨424212, by rfl⟩ : syracuseStep 1131233 = 848425) B848425
theorem B1688291 : Blo 750330 1688291 := bstep (se 1 (by rfl) ⟨1266218, by rfl⟩ : syracuseStep 1688291 = 2532437) B2532437
theorem B11715299 : Blo 750330 11715299 := bstep (se 1 (by rfl) ⟨8786474, by rfl⟩ : syracuseStep 11715299 = 17572949) B17572949
theorem B1131251 : Blo 750330 1131251 := bstep (se 1 (by rfl) ⟨848438, by rfl⟩ : syracuseStep 1131251 = 1696877) B1696877
theorem B4571909 : Blo 750330 4571909 := bstep (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) B857233
theorem B1131281 : Blo 750330 1131281 := bstep (se 2 (by rfl) ⟨424230, by rfl⟩ : syracuseStep 1131281 = 848461) B848461
theorem B1131299 : Blo 750330 1131299 := bstep (se 1 (by rfl) ⟨848474, by rfl⟩ : syracuseStep 1131299 = 1696949) B1696949
theorem B1131329 : Blo 750330 1131329 := bstep (se 2 (by rfl) ⟨424248, by rfl⟩ : syracuseStep 1131329 = 848497) B848497
theorem B1426243 : Blo 750330 1426243 := bstep (se 1 (by rfl) ⟨1069682, by rfl⟩ : syracuseStep 1426243 = 2139365) B2139365
theorem B1131347 : Blo 750330 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B3818339 : Blo 750330 3818339 := bstep (se 1 (by rfl) ⟨2863754, by rfl⟩ : syracuseStep 3818339 = 5727509) B5727509
theorem B1131377 : Blo 750330 1131377 := bstep (se 2 (by rfl) ⟨424266, by rfl⟩ : syracuseStep 1131377 = 848533) B848533
theorem B1131395 : Blo 750330 1131395 := bstep (se 1 (by rfl) ⟨848546, by rfl⟩ : syracuseStep 1131395 = 1697093) B1697093
theorem B2540429 : Blo 750330 2540429 := bstep (se 3 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 2540429 = 952661) B952661
theorem B902035 : Blo 750330 902035 := bstep (se 1 (by rfl) ⟨676526, by rfl⟩ : syracuseStep 902035 = 1353053) B1353053
theorem B1131425 : Blo 750330 1131425 := bstep (se 2 (by rfl) ⟨424284, by rfl⟩ : syracuseStep 1131425 = 848569) B848569
theorem B3621809 : Blo 750330 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B1131443 : Blo 750330 1131443 := bstep (se 1 (by rfl) ⟨848582, by rfl⟩ : syracuseStep 1131443 = 1697165) B1697165
theorem B2540483 : Blo 750330 2540483 := bstep (se 1 (by rfl) ⟨1905362, by rfl⟩ : syracuseStep 2540483 = 3810725) B3810725
theorem B1131473 : Blo 750330 1131473 := bstep (se 2 (by rfl) ⟨424302, by rfl⟩ : syracuseStep 1131473 = 848605) B848605
theorem B1426403 : Blo 750330 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1131491 : Blo 750330 1131491 := bstep (se 1 (by rfl) ⟨848618, by rfl⟩ : syracuseStep 1131491 = 1697237) B1697237
theorem B1688561 : Blo 750330 1688561 := bstep (se 2 (by rfl) ⟨633210, by rfl⟩ : syracuseStep 1688561 = 1266421) B1266421
theorem B1688579 : Blo 750330 1688579 := bstep (se 1 (by rfl) ⟨1266434, by rfl⟩ : syracuseStep 1688579 = 2532869) B2532869
theorem B2540753 : Blo 750330 2540753 := bstep (se 2 (by rfl) ⟨952782, by rfl⟩ : syracuseStep 2540753 = 1905565) B1905565
theorem B1688849 : Blo 750330 1688849 := bstep (se 2 (by rfl) ⟨633318, by rfl⟩ : syracuseStep 1688849 = 1266637) B1266637
theorem B1688867 : Blo 750330 1688867 := bstep (se 1 (by rfl) ⟨1266650, by rfl⟩ : syracuseStep 1688867 = 2533301) B2533301
theorem B2573603 : Blo 750330 2573603 := bstep (se 1 (by rfl) ⟨1930202, by rfl⟩ : syracuseStep 2573603 = 3860405) B3860405
theorem B804163 : Blo 750330 804163 := bstep (se 1 (by rfl) ⟨603122, by rfl⟩ : syracuseStep 804163 = 1206245) B1206245
theorem B2147725 : Blo 750330 2147725 := bstep (se 3 (by rfl) ⟨402698, by rfl⟩ : syracuseStep 2147725 = 805397) B805397
theorem B4277681 : Blo 750330 4277681 := bstep (se 2 (by rfl) ⟨1604130, by rfl⟩ : syracuseStep 4277681 = 3208261) B3208261
theorem B1525169 : Blo 750330 1525169 := bstep (se 2 (by rfl) ⟨571938, by rfl⟩ : syracuseStep 1525169 = 1143877) B1143877
theorem B2606627 : Blo 750330 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B1689137 : Blo 750330 1689137 := bstep (se 2 (by rfl) ⟨633426, by rfl⟩ : syracuseStep 1689137 = 1266853) B1266853
theorem B1689155 : Blo 750330 1689155 := bstep (se 1 (by rfl) ⟨1266866, by rfl⟩ : syracuseStep 1689155 = 2533733) B2533733
theorem B2147953 : Blo 750330 2147953 := bstep (se 2 (by rfl) ⟨805482, by rfl⟩ : syracuseStep 2147953 = 1610965) B1610965
theorem B2541293 : Blo 750330 2541293 := bstep (se 3 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 2541293 = 952985) B952985
theorem B804611 : Blo 750330 804611 := bstep (se 1 (by rfl) ⟨603458, by rfl⟩ : syracuseStep 804611 = 1206917) B1206917
theorem B2541347 : Blo 750330 2541347 := bstep (se 1 (by rfl) ⟨1906010, by rfl⟩ : syracuseStep 2541347 = 3812021) B3812021
theorem B1689425 : Blo 750330 1689425 := bstep (se 2 (by rfl) ⟨633534, by rfl⟩ : syracuseStep 1689425 = 1267069) B1267069
theorem B1689443 : Blo 750330 1689443 := bstep (se 1 (by rfl) ⟨1267082, by rfl⟩ : syracuseStep 1689443 = 2534165) B2534165
theorem B1427473 : Blo 750330 1427473 := bstep (se 2 (by rfl) ⟨535302, by rfl⟩ : syracuseStep 1427473 = 1070605) B1070605
theorem B2541617 : Blo 750330 2541617 := bstep (se 2 (by rfl) ⟨953106, by rfl⟩ : syracuseStep 2541617 = 1906213) B1906213
theorem B1689713 : Blo 750330 1689713 := bstep (se 2 (by rfl) ⟨633642, by rfl⟩ : syracuseStep 1689713 = 1267285) B1267285
theorem B1689731 : Blo 750330 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B1690001 : Blo 750330 1690001 := bstep (se 2 (by rfl) ⟨633750, by rfl⟩ : syracuseStep 1690001 = 1267501) B1267501
theorem B1690019 : Blo 750330 1690019 := bstep (se 1 (by rfl) ⟨1267514, by rfl⟩ : syracuseStep 1690019 = 2535029) B2535029
theorem B2542157 : Blo 750330 2542157 := bstep (se 3 (by rfl) ⟨476654, by rfl⟩ : syracuseStep 2542157 = 953309) B953309
theorem B2411117 : Blo 750330 2411117 := bstep (se 3 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 2411117 = 904169) B904169
theorem B2542211 : Blo 750330 2542211 := bstep (se 1 (by rfl) ⟨1906658, by rfl⟩ : syracuseStep 2542211 = 3813317) B3813317
theorem B1690289 : Blo 750330 1690289 := bstep (se 2 (by rfl) ⟨633858, by rfl⟩ : syracuseStep 1690289 = 1267717) B1267717
theorem B1690307 : Blo 750330 1690307 := bstep (se 1 (by rfl) ⟨1267730, by rfl⟩ : syracuseStep 1690307 = 2535461) B2535461
theorem B1526467 : Blo 750330 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B9161525 : Blo 750330 9161525 := bstep (se 5 (by rfl) ⟨429446, by rfl⟩ : syracuseStep 9161525 = 858893) B858893
theorem B4279139 : Blo 750330 4279139 := bstep (se 1 (by rfl) ⟨3209354, by rfl⟩ : syracuseStep 4279139 = 6418709) B6418709
theorem B2542481 : Blo 750330 2542481 := bstep (se 2 (by rfl) ⟨953430, by rfl⟩ : syracuseStep 2542481 = 1906861) B1906861
theorem B1690577 : Blo 750330 1690577 := bstep (se 2 (by rfl) ⟨633966, by rfl⟩ : syracuseStep 1690577 = 1267933) B1267933
theorem B1690595 : Blo 750330 1690595 := bstep (se 1 (by rfl) ⟨1267946, by rfl⟩ : syracuseStep 1690595 = 2535893) B2535893
theorem B2706481 : Blo 750330 2706481 := bstep (se 2 (by rfl) ⟨1014930, by rfl⟩ : syracuseStep 2706481 = 2029861) B2029861
theorem B1428529 : Blo 750330 1428529 := bstep (se 2 (by rfl) ⟨535698, by rfl⟩ : syracuseStep 1428529 = 1071397) B1071397
theorem B11586673 : Blo 750330 11586673 := bstep (se 2 (by rfl) ⟨4345002, by rfl⟩ : syracuseStep 11586673 = 8690005) B8690005
theorem B1690865 : Blo 750330 1690865 := bstep (se 2 (by rfl) ⟨634074, by rfl⟩ : syracuseStep 1690865 = 1268149) B1268149
theorem B1690883 : Blo 750330 1690883 := bstep (se 1 (by rfl) ⟨1268162, by rfl⟩ : syracuseStep 1690883 = 2536325) B2536325
theorem B2543021 : Blo 750330 2543021 := bstep (se 3 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 2543021 = 953633) B953633
theorem B3263921 : Blo 750330 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B9293237 : Blo 750330 9293237 := bstep (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) B871241
theorem B1068481 : Blo 750330 1068481 := bstep (se 2 (by rfl) ⟨400680, by rfl⟩ : syracuseStep 1068481 = 801361) B801361
theorem B1428931 : Blo 750330 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B2543075 : Blo 750330 2543075 := bstep (se 1 (by rfl) ⟨1907306, by rfl⟩ : syracuseStep 2543075 = 3814613) B3814613
theorem B1428977 : Blo 750330 1428977 := bstep (se 2 (by rfl) ⟨535866, by rfl⟩ : syracuseStep 1428977 = 1071733) B1071733
theorem B1691153 : Blo 750330 1691153 := bstep (se 2 (by rfl) ⟨634182, by rfl⟩ : syracuseStep 1691153 = 1268365) B1268365
theorem B1691171 : Blo 750330 1691171 := bstep (se 1 (by rfl) ⟨1268378, by rfl⟩ : syracuseStep 1691171 = 2536757) B2536757
theorem B4181701 : Blo 750330 4181701 := bstep (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) B784069
theorem B2543345 : Blo 750330 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B1068817 : Blo 750330 1068817 := bstep (se 2 (by rfl) ⟨400806, by rfl⟩ : syracuseStep 1068817 = 801613) B801613
theorem B1429265 : Blo 750330 1429265 := bstep (se 2 (by rfl) ⟨535974, by rfl⟩ : syracuseStep 1429265 = 1071949) B1071949
theorem B1691441 : Blo 750330 1691441 := bstep (se 2 (by rfl) ⟨634290, by rfl⟩ : syracuseStep 1691441 = 1268581) B1268581
theorem B1691459 : Blo 750330 1691459 := bstep (se 1 (by rfl) ⟨1268594, by rfl⟩ : syracuseStep 1691459 = 2537189) B2537189
theorem B4280141 : Blo 750330 4280141 := bstep (se 3 (by rfl) ⟨802526, by rfl⟩ : syracuseStep 4280141 = 1605053) B1605053
theorem B905107 : Blo 750330 905107 := bstep (se 1 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 905107 = 1357661) B1357661
theorem B1691729 : Blo 750330 1691729 := bstep (se 2 (by rfl) ⟨634398, by rfl⟩ : syracuseStep 1691729 = 1268797) B1268797
theorem B6410339 : Blo 750330 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B1691747 : Blo 750330 1691747 := bstep (se 1 (by rfl) ⟨1268810, by rfl⟩ : syracuseStep 1691747 = 2537621) B2537621
theorem B4575365 : Blo 750330 4575365 := bstep (se 4 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 4575365 = 857881) B857881
theorem B2543885 : Blo 750330 2543885 := bstep (se 3 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 2543885 = 953957) B953957
theorem B2543939 : Blo 750330 2543939 := bstep (se 1 (by rfl) ⟨1907954, by rfl⟩ : syracuseStep 2543939 = 3815909) B3815909
theorem B1069409 : Blo 750330 1069409 := bstep (se 2 (by rfl) ⟨401028, by rfl⟩ : syracuseStep 1069409 = 802057) B802057
theorem B2412899 : Blo 750330 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B1692017 : Blo 750330 1692017 := bstep (se 2 (by rfl) ⟨634506, by rfl⟩ : syracuseStep 1692017 = 1269013) B1269013
theorem B1692035 : Blo 750330 1692035 := bstep (se 1 (by rfl) ⟨1269026, by rfl⟩ : syracuseStep 1692035 = 2538053) B2538053
theorem B14471621 : Blo 750330 14471621 := bstep (se 4 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 14471621 = 2713429) B2713429
theorem B1429987 : Blo 750330 1429987 := bstep (se 1 (by rfl) ⟨1072490, by rfl⟩ : syracuseStep 1429987 = 2144981) B2144981
theorem B2544209 : Blo 750330 2544209 := bstep (se 2 (by rfl) ⟨954078, by rfl⟩ : syracuseStep 2544209 = 1908157) B1908157
theorem B1266259 : Blo 750330 1266259 := bstep (se 1 (by rfl) ⟨949694, by rfl⟩ : syracuseStep 1266259 = 1899389) B1899389
theorem B1692305 : Blo 750330 1692305 := bstep (se 2 (by rfl) ⟨634614, by rfl⟩ : syracuseStep 1692305 = 1269229) B1269229
theorem B1692323 : Blo 750330 1692323 := bstep (se 1 (by rfl) ⟨1269242, by rfl⟩ : syracuseStep 1692323 = 2538485) B2538485
theorem B1266401 : Blo 750330 1266401 := bstep (se 2 (by rfl) ⟨474900, by rfl⟩ : syracuseStep 1266401 = 949801) B949801
theorem B10277603 : Blo 750330 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B1528625 : Blo 750330 1528625 := bstep (se 2 (by rfl) ⟨573234, by rfl⟩ : syracuseStep 1528625 = 1146469) B1146469
theorem B1266529 : Blo 750330 1266529 := bstep (se 2 (by rfl) ⟨474948, by rfl⟩ : syracuseStep 1266529 = 949897) B949897
theorem B1069939 : Blo 750330 1069939 := bstep (se 1 (by rfl) ⟨802454, by rfl⟩ : syracuseStep 1069939 = 1604909) B1604909
theorem B1266563 : Blo 750330 1266563 := bstep (se 1 (by rfl) ⟨949922, by rfl⟩ : syracuseStep 1266563 = 1899845) B1899845
theorem B1430435 : Blo 750330 1430435 := bstep (se 1 (by rfl) ⟨1072826, by rfl⟩ : syracuseStep 1430435 = 2145653) B2145653
theorem B1692593 : Blo 750330 1692593 := bstep (se 2 (by rfl) ⟨634722, by rfl⟩ : syracuseStep 1692593 = 1269445) B1269445
theorem B1692611 : Blo 750330 1692611 := bstep (se 1 (by rfl) ⟨1269458, by rfl⟩ : syracuseStep 1692611 = 2538917) B2538917
theorem B1266691 : Blo 750330 1266691 := bstep (se 1 (by rfl) ⟨950018, by rfl⟩ : syracuseStep 1266691 = 1900037) B1900037
theorem B1528931 : Blo 750330 1528931 := bstep (se 1 (by rfl) ⟨1146698, by rfl⟩ : syracuseStep 1528931 = 2293397) B2293397
theorem B2544749 : Blo 750330 2544749 := bstep (se 3 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 2544749 = 954281) B954281
theorem B1266833 : Blo 750330 1266833 := bstep (se 2 (by rfl) ⟨475062, by rfl⟩ : syracuseStep 1266833 = 950125) B950125
theorem B2544803 : Blo 750330 2544803 := bstep (se 1 (by rfl) ⟨1908602, by rfl⟩ : syracuseStep 2544803 = 3817205) B3817205
theorem B1070275 : Blo 750330 1070275 := bstep (se 1 (by rfl) ⟨802706, by rfl⟩ : syracuseStep 1070275 = 1605413) B1605413
theorem B1430723 : Blo 750330 1430723 := bstep (se 1 (by rfl) ⟨1073042, by rfl⟩ : syracuseStep 1430723 = 2146085) B2146085
theorem B1692881 : Blo 750330 1692881 := bstep (se 2 (by rfl) ⟨634830, by rfl⟩ : syracuseStep 1692881 = 1269661) B1269661
theorem B1692899 : Blo 750330 1692899 := bstep (se 1 (by rfl) ⟨1269674, by rfl⟩ : syracuseStep 1692899 = 2539349) B2539349
theorem B1266961 : Blo 750330 1266961 := bstep (se 2 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 1266961 = 950221) B950221
theorem B1266995 : Blo 750330 1266995 := bstep (se 1 (by rfl) ⟨950246, by rfl⟩ : syracuseStep 1266995 = 1900493) B1900493
theorem B2545073 : Blo 750330 2545073 := bstep (se 2 (by rfl) ⟨954402, by rfl⟩ : syracuseStep 2545073 = 1908805) B1908805
theorem B1267123 : Blo 750330 1267123 := bstep (se 1 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 1267123 = 1900685) B1900685
theorem B1693169 : Blo 750330 1693169 := bstep (se 2 (by rfl) ⟨634938, by rfl⟩ : syracuseStep 1693169 = 1269877) B1269877
theorem B1693187 : Blo 750330 1693187 := bstep (se 1 (by rfl) ⟨1269890, by rfl⟩ : syracuseStep 1693187 = 2539781) B2539781
theorem B1267265 : Blo 750330 1267265 := bstep (se 2 (by rfl) ⟨475224, by rfl⟩ : syracuseStep 1267265 = 950449) B950449
theorem B2414243 : Blo 750330 2414243 := bstep (se 1 (by rfl) ⟨1810682, by rfl⟩ : syracuseStep 2414243 = 3621365) B3621365
theorem B1267393 : Blo 750330 1267393 := bstep (se 2 (by rfl) ⟨475272, by rfl⟩ : syracuseStep 1267393 = 950545) B950545
theorem B1267427 : Blo 750330 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B1070833 : Blo 750330 1070833 := bstep (se 2 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 1070833 = 803125) B803125
theorem B1693457 : Blo 750330 1693457 := bstep (se 2 (by rfl) ⟨635046, by rfl⟩ : syracuseStep 1693457 = 1270093) B1270093
theorem B1070867 : Blo 750330 1070867 := bstep (se 1 (by rfl) ⟨803150, by rfl⟩ : syracuseStep 1070867 = 1606301) B1606301
theorem B1693475 : Blo 750330 1693475 := bstep (se 1 (by rfl) ⟨1270106, by rfl⟩ : syracuseStep 1693475 = 2540213) B2540213
theorem B1267555 : Blo 750330 1267555 := bstep (se 1 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 1267555 = 1901333) B1901333
theorem B6510449 : Blo 750330 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B2545613 : Blo 750330 2545613 := bstep (se 3 (by rfl) ⟨477302, by rfl⟩ : syracuseStep 2545613 = 954605) B954605
theorem B1267697 : Blo 750330 1267697 := bstep (se 2 (by rfl) ⟨475386, by rfl⟩ : syracuseStep 1267697 = 950773) B950773
theorem B2545667 : Blo 750330 2545667 := bstep (se 1 (by rfl) ⟨1909250, by rfl⟩ : syracuseStep 2545667 = 3818501) B3818501
theorem B1693745 : Blo 750330 1693745 := bstep (se 2 (by rfl) ⟨635154, by rfl⟩ : syracuseStep 1693745 = 1270309) B1270309
theorem B1693763 : Blo 750330 1693763 := bstep (se 1 (by rfl) ⟨1270322, by rfl⟩ : syracuseStep 1693763 = 2540645) B2540645
theorem B1267825 : Blo 750330 1267825 := bstep (se 2 (by rfl) ⟨475434, by rfl⟩ : syracuseStep 1267825 = 950869) B950869
theorem B1431665 : Blo 750330 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B1267859 : Blo 750330 1267859 := bstep (se 1 (by rfl) ⟨950894, by rfl⟩ : syracuseStep 1267859 = 1901789) B1901789
theorem B1267987 : Blo 750330 1267987 := bstep (se 1 (by rfl) ⟨950990, by rfl⟩ : syracuseStep 1267987 = 1901981) B1901981
theorem B1202483 : Blo 750330 1202483 := bstep (se 1 (by rfl) ⟨901862, by rfl⟩ : syracuseStep 1202483 = 1803725) B1803725
theorem B1071425 : Blo 750330 1071425 := bstep (se 2 (by rfl) ⟨401784, by rfl⟩ : syracuseStep 1071425 = 803569) B803569
theorem B1694033 : Blo 750330 1694033 := bstep (se 2 (by rfl) ⟨635262, by rfl⟩ : syracuseStep 1694033 = 1270525) B1270525
theorem B1694051 : Blo 750330 1694051 := bstep (se 1 (by rfl) ⟨1270538, by rfl⟩ : syracuseStep 1694051 = 2541077) B2541077
theorem B1071505 : Blo 750330 1071505 := bstep (se 2 (by rfl) ⟨401814, by rfl⟩ : syracuseStep 1071505 = 803629) B803629
theorem B1268129 : Blo 750330 1268129 := bstep (se 2 (by rfl) ⟨475548, by rfl⟩ : syracuseStep 1268129 = 951097) B951097
theorem B1202611 : Blo 750330 1202611 := bstep (se 1 (by rfl) ⟨901958, by rfl⟩ : syracuseStep 1202611 = 1803917) B1803917
theorem B1268257 : Blo 750330 1268257 := bstep (se 2 (by rfl) ⟨475596, by rfl⟩ : syracuseStep 1268257 = 951193) B951193
theorem B1268291 : Blo 750330 1268291 := bstep (se 1 (by rfl) ⟨951218, by rfl⟩ : syracuseStep 1268291 = 1902437) B1902437
theorem B2316899 : Blo 750330 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B1694321 : Blo 750330 1694321 := bstep (se 2 (by rfl) ⟨635370, by rfl⟩ : syracuseStep 1694321 = 1270741) B1270741
theorem B1694339 : Blo 750330 1694339 := bstep (se 1 (by rfl) ⟨1270754, by rfl⟩ : syracuseStep 1694339 = 2541509) B2541509
theorem B4283057 : Blo 750330 4283057 := bstep (se 2 (by rfl) ⟨1606146, by rfl⟩ : syracuseStep 4283057 = 3212293) B3212293
theorem B1268419 : Blo 750330 1268419 := bstep (se 1 (by rfl) ⟨951314, by rfl⟩ : syracuseStep 1268419 = 1902629) B1902629
theorem B1235731 : Blo 750330 1235731 := bstep (se 1 (by rfl) ⟨926798, by rfl⟩ : syracuseStep 1235731 = 1853597) B1853597
theorem B1268561 : Blo 750330 1268561 := bstep (se 2 (by rfl) ⟨475710, by rfl⟩ : syracuseStep 1268561 = 951421) B951421
theorem B1694609 : Blo 750330 1694609 := bstep (se 2 (by rfl) ⟨635478, by rfl⟩ : syracuseStep 1694609 = 1270957) B1270957
theorem B1694627 : Blo 750330 1694627 := bstep (se 1 (by rfl) ⟨1270970, by rfl⟩ : syracuseStep 1694627 = 2541941) B2541941
theorem B1268689 : Blo 750330 1268689 := bstep (se 2 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 1268689 = 951517) B951517
theorem B1203169 : Blo 750330 1203169 := bstep (se 2 (by rfl) ⟨451188, by rfl⟩ : syracuseStep 1203169 = 902377) B902377
theorem B1268723 : Blo 750330 1268723 := bstep (se 1 (by rfl) ⟨951542, by rfl⟩ : syracuseStep 1268723 = 1903085) B1903085
theorem B1268851 : Blo 750330 1268851 := bstep (se 1 (by rfl) ⟨951638, by rfl⟩ : syracuseStep 1268851 = 1903277) B1903277
theorem B1072291 : Blo 750330 1072291 := bstep (se 1 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 1072291 = 1608437) B1608437
theorem B1694897 : Blo 750330 1694897 := bstep (se 2 (by rfl) ⟨635586, by rfl⟩ : syracuseStep 1694897 = 1271173) B1271173
theorem B1694915 : Blo 750330 1694915 := bstep (se 1 (by rfl) ⟨1271186, by rfl⟩ : syracuseStep 1694915 = 2542373) B2542373
theorem B1268993 : Blo 750330 1268993 := bstep (se 2 (by rfl) ⟨475872, by rfl⟩ : syracuseStep 1268993 = 951745) B951745
theorem B1269121 : Blo 750330 1269121 := bstep (se 2 (by rfl) ⟨475920, by rfl⟩ : syracuseStep 1269121 = 951841) B951841
theorem B2416013 : Blo 750330 2416013 := bstep (se 3 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 2416013 = 906005) B906005
theorem B1269155 : Blo 750330 1269155 := bstep (se 1 (by rfl) ⟨951866, by rfl⟩ : syracuseStep 1269155 = 1903733) B1903733
theorem B1695185 : Blo 750330 1695185 := bstep (se 2 (by rfl) ⟨635694, by rfl⟩ : syracuseStep 1695185 = 1271389) B1271389
theorem B1695203 : Blo 750330 1695203 := bstep (se 1 (by rfl) ⟨1271402, by rfl⟩ : syracuseStep 1695203 = 2542805) B2542805
theorem B1269283 : Blo 750330 1269283 := bstep (se 1 (by rfl) ⟨951962, by rfl⟩ : syracuseStep 1269283 = 1903925) B1903925
theorem B1072769 : Blo 750330 1072769 := bstep (se 2 (by rfl) ⟨402288, by rfl⟩ : syracuseStep 1072769 = 804577) B804577
theorem B1203841 : Blo 750330 1203841 := bstep (se 2 (by rfl) ⟨451440, by rfl⟩ : syracuseStep 1203841 = 902881) B902881
theorem B1564337 : Blo 750330 1564337 := bstep (se 2 (by rfl) ⟨586626, by rfl⟩ : syracuseStep 1564337 = 1173253) B1173253
theorem B1269425 : Blo 750330 1269425 := bstep (se 2 (by rfl) ⟨476034, by rfl⟩ : syracuseStep 1269425 = 952069) B952069
theorem B1695473 : Blo 750330 1695473 := bstep (se 2 (by rfl) ⟨635802, by rfl⟩ : syracuseStep 1695473 = 1271605) B1271605
theorem B1072883 : Blo 750330 1072883 := bstep (se 1 (by rfl) ⟨804662, by rfl⟩ : syracuseStep 1072883 = 1609325) B1609325
theorem B1695491 : Blo 750330 1695491 := bstep (se 1 (by rfl) ⟨1271618, by rfl⟩ : syracuseStep 1695491 = 2543237) B2543237
theorem B2285347 : Blo 750330 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B1269553 : Blo 750330 1269553 := bstep (se 2 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 1269553 = 952165) B952165
theorem B1072963 : Blo 750330 1072963 := bstep (se 1 (by rfl) ⟨804722, by rfl⟩ : syracuseStep 1072963 = 1609445) B1609445
theorem B1269587 : Blo 750330 1269587 := bstep (se 1 (by rfl) ⟨952190, by rfl⟩ : syracuseStep 1269587 = 1904381) B1904381
theorem B5726051 : Blo 750330 5726051 := bstep (se 1 (by rfl) ⟨4294538, by rfl⟩ : syracuseStep 5726051 = 8589077) B8589077
theorem B1269715 : Blo 750330 1269715 := bstep (se 1 (by rfl) ⟨952286, by rfl⟩ : syracuseStep 1269715 = 1904573) B1904573
theorem B1695761 : Blo 750330 1695761 := bstep (se 2 (by rfl) ⟨635910, by rfl⟩ : syracuseStep 1695761 = 1271821) B1271821
theorem B1695779 : Blo 750330 1695779 := bstep (se 1 (by rfl) ⟨1271834, by rfl⟩ : syracuseStep 1695779 = 2543669) B2543669
theorem B1925201 : Blo 750330 1925201 := bstep (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) B1443901
theorem B1269857 : Blo 750330 1269857 := bstep (se 2 (by rfl) ⟨476196, by rfl⟩ : syracuseStep 1269857 = 952393) B952393
theorem B4808803 : Blo 750330 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B4284515 : Blo 750330 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B1269985 : Blo 750330 1269985 := bstep (se 2 (by rfl) ⟨476244, by rfl⟩ : syracuseStep 1269985 = 952489) B952489
theorem B1270019 : Blo 750330 1270019 := bstep (se 1 (by rfl) ⟨952514, by rfl⟩ : syracuseStep 1270019 = 1905029) B1905029
theorem B1696049 : Blo 750330 1696049 := bstep (se 2 (by rfl) ⟨636018, by rfl⟩ : syracuseStep 1696049 = 1272037) B1272037
theorem B1696067 : Blo 750330 1696067 := bstep (se 1 (by rfl) ⟨1272050, by rfl⟩ : syracuseStep 1696067 = 2544101) B2544101
theorem B1073521 : Blo 750330 1073521 := bstep (se 2 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 1073521 = 805141) B805141
theorem B1270147 : Blo 750330 1270147 := bstep (se 1 (by rfl) ⟨952610, by rfl⟩ : syracuseStep 1270147 = 1905221) B1905221
theorem B844195 : Blo 750330 844195 := bstep (se 1 (by rfl) ⟨633146, by rfl⟩ : syracuseStep 844195 = 1266293) B1266293
theorem B1270289 : Blo 750330 1270289 := bstep (se 2 (by rfl) ⟨476358, by rfl⟩ : syracuseStep 1270289 = 952717) B952717
theorem B844339 : Blo 750330 844339 := bstep (se 1 (by rfl) ⟨633254, by rfl⟩ : syracuseStep 844339 = 1266509) B1266509
theorem B1696337 : Blo 750330 1696337 := bstep (se 2 (by rfl) ⟨636126, by rfl⟩ : syracuseStep 1696337 = 1272253) B1272253
theorem B1696355 : Blo 750330 1696355 := bstep (se 1 (by rfl) ⟨1272266, by rfl⟩ : syracuseStep 1696355 = 2544533) B2544533
theorem B1270417 : Blo 750330 1270417 := bstep (se 2 (by rfl) ⟨476406, by rfl⟩ : syracuseStep 1270417 = 952813) B952813
theorem B1270451 : Blo 750330 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B844483 : Blo 750330 844483 := bstep (se 1 (by rfl) ⟨633362, by rfl⟩ : syracuseStep 844483 = 1266725) B1266725
theorem B1204931 : Blo 750330 1204931 := bstep (se 1 (by rfl) ⟨903698, by rfl⟩ : syracuseStep 1204931 = 1807397) B1807397
theorem B1270579 : Blo 750330 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B844627 : Blo 750330 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B1696625 : Blo 750330 1696625 := bstep (se 2 (by rfl) ⟨636234, by rfl⟩ : syracuseStep 1696625 = 1272469) B1272469
theorem B1696643 : Blo 750330 1696643 := bstep (se 1 (by rfl) ⟨1272482, by rfl⟩ : syracuseStep 1696643 = 2544965) B2544965
theorem B1270721 : Blo 750330 1270721 := bstep (se 2 (by rfl) ⟨476520, by rfl⟩ : syracuseStep 1270721 = 953041) B953041
theorem B844771 : Blo 750330 844771 := bstep (se 1 (by rfl) ⟨633578, by rfl⟩ : syracuseStep 844771 = 1267157) B1267157
theorem B1270849 : Blo 750330 1270849 := bstep (se 2 (by rfl) ⟨476568, by rfl⟩ : syracuseStep 1270849 = 953137) B953137
theorem B1270883 : Blo 750330 1270883 := bstep (se 1 (by rfl) ⟨953162, by rfl⟩ : syracuseStep 1270883 = 1906325) B1906325
theorem B844915 : Blo 750330 844915 := bstep (se 1 (by rfl) ⟨633686, by rfl⟩ : syracuseStep 844915 = 1267373) B1267373
theorem B1696913 : Blo 750330 1696913 := bstep (se 2 (by rfl) ⟨636342, by rfl⟩ : syracuseStep 1696913 = 1272685) B1272685
theorem B1696931 : Blo 750330 1696931 := bstep (se 1 (by rfl) ⟨1272698, by rfl⟩ : syracuseStep 1696931 = 2545397) B2545397
theorem B1271011 : Blo 750330 1271011 := bstep (se 1 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 1271011 = 1906517) B1906517
theorem B845059 : Blo 750330 845059 := bstep (se 1 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 845059 = 1267589) B1267589
theorem B4810033 : Blo 750330 4810033 := bstep (se 2 (by rfl) ⟨1803762, by rfl⟩ : syracuseStep 4810033 = 3607525) B3607525
theorem B1271153 : Blo 750330 1271153 := bstep (se 2 (by rfl) ⟨476682, by rfl⟩ : syracuseStep 1271153 = 953365) B953365
theorem B845203 : Blo 750330 845203 := bstep (se 1 (by rfl) ⟨633902, by rfl⟩ : syracuseStep 845203 = 1267805) B1267805
theorem B1697201 : Blo 750330 1697201 := bstep (se 2 (by rfl) ⟨636450, by rfl⟩ : syracuseStep 1697201 = 1272901) B1272901
theorem B1697219 : Blo 750330 1697219 := bstep (se 1 (by rfl) ⟨1272914, by rfl⟩ : syracuseStep 1697219 = 2545829) B2545829
theorem B1926641 : Blo 750330 1926641 := bstep (se 2 (by rfl) ⟨722490, by rfl⟩ : syracuseStep 1926641 = 1444981) B1444981
theorem B1271281 : Blo 750330 1271281 := bstep (se 2 (by rfl) ⟨476730, by rfl⟩ : syracuseStep 1271281 = 953461) B953461
theorem B2287121 : Blo 750330 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B1271315 : Blo 750330 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B845347 : Blo 750330 845347 := bstep (se 1 (by rfl) ⟨634010, by rfl⟩ : syracuseStep 845347 = 1268021) B1268021
theorem B1271443 : Blo 750330 1271443 := bstep (se 1 (by rfl) ⟨953582, by rfl⟩ : syracuseStep 1271443 = 1907165) B1907165
theorem B845491 : Blo 750330 845491 := bstep (se 1 (by rfl) ⟨634118, by rfl⟩ : syracuseStep 845491 = 1268237) B1268237
theorem B1271585 : Blo 750330 1271585 := bstep (se 2 (by rfl) ⟨476844, by rfl⟩ : syracuseStep 1271585 = 953689) B953689
theorem B845635 : Blo 750330 845635 := bstep (se 1 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 845635 = 1268453) B1268453
theorem B6088547 : Blo 750330 6088547 := bstep (se 1 (by rfl) ⟨4566410, by rfl⟩ : syracuseStep 6088547 = 9132821) B9132821
theorem B1271713 : Blo 750330 1271713 := bstep (se 2 (by rfl) ⟨476892, by rfl⟩ : syracuseStep 1271713 = 953785) B953785
theorem B1271747 : Blo 750330 1271747 := bstep (se 1 (by rfl) ⟨953810, by rfl⟩ : syracuseStep 1271747 = 1907621) B1907621
theorem B1632209 : Blo 750330 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B845779 : Blo 750330 845779 := bstep (se 1 (by rfl) ⟨634334, by rfl⟩ : syracuseStep 845779 = 1268669) B1268669
theorem B1271875 : Blo 750330 1271875 := bstep (se 1 (by rfl) ⟨953906, by rfl⟩ : syracuseStep 1271875 = 1907813) B1907813
theorem B1206353 : Blo 750330 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B845923 : Blo 750330 845923 := bstep (se 1 (by rfl) ⟨634442, by rfl⟩ : syracuseStep 845923 = 1268885) B1268885
theorem B1272017 : Blo 750330 1272017 := bstep (se 2 (by rfl) ⟨477006, by rfl⟩ : syracuseStep 1272017 = 954013) B954013
theorem B846067 : Blo 750330 846067 := bstep (se 1 (by rfl) ⟨634550, by rfl⟩ : syracuseStep 846067 = 1269101) B1269101
theorem B2287939 : Blo 750330 2287939 := bstep (se 1 (by rfl) ⟨1715954, by rfl⟩ : syracuseStep 2287939 = 3431909) B3431909
theorem B1272145 : Blo 750330 1272145 := bstep (se 2 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 1272145 = 954109) B954109
theorem B1272179 : Blo 750330 1272179 := bstep (se 1 (by rfl) ⟨954134, by rfl⟩ : syracuseStep 1272179 = 1908269) B1908269
theorem B846211 : Blo 750330 846211 := bstep (se 1 (by rfl) ⟨634658, by rfl⟩ : syracuseStep 846211 = 1269317) B1269317
theorem B9660869 : Blo 750330 9660869 := bstep (se 4 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 9660869 = 1811413) B1811413
theorem B1272307 : Blo 750330 1272307 := bstep (se 1 (by rfl) ⟨954230, by rfl⟩ : syracuseStep 1272307 = 1908461) B1908461
theorem B846355 : Blo 750330 846355 := bstep (se 1 (by rfl) ⟨634766, by rfl⟩ : syracuseStep 846355 = 1269533) B1269533
theorem B1272449 : Blo 750330 1272449 := bstep (se 2 (by rfl) ⟨477168, by rfl⟩ : syracuseStep 1272449 = 954337) B954337
theorem B846499 : Blo 750330 846499 := bstep (se 1 (by rfl) ⟨634874, by rfl⟩ : syracuseStep 846499 = 1269749) B1269749
theorem B1272577 : Blo 750330 1272577 := bstep (se 2 (by rfl) ⟨477216, by rfl⟩ : syracuseStep 1272577 = 954433) B954433
theorem B1272611 : Blo 750330 1272611 := bstep (se 1 (by rfl) ⟨954458, by rfl⟩ : syracuseStep 1272611 = 1908917) B1908917
theorem B846643 : Blo 750330 846643 := bstep (se 1 (by rfl) ⟨634982, by rfl⟩ : syracuseStep 846643 = 1269965) B1269965
theorem B20573041 : Blo 750330 20573041 := bstep (se 2 (by rfl) ⟨7714890, by rfl⟩ : syracuseStep 20573041 = 15429781) B15429781
theorem B1272739 : Blo 750330 1272739 := bstep (se 1 (by rfl) ⟨954554, by rfl⟩ : syracuseStep 1272739 = 1909109) B1909109
theorem B1207219 : Blo 750330 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B846787 : Blo 750330 846787 := bstep (se 1 (by rfl) ⟨635090, by rfl⟩ : syracuseStep 846787 = 1270181) B1270181
theorem B1272881 : Blo 750330 1272881 := bstep (se 2 (by rfl) ⟨477330, by rfl⟩ : syracuseStep 1272881 = 954661) B954661
theorem B846931 : Blo 750330 846931 := bstep (se 1 (by rfl) ⟨635198, by rfl⟩ : syracuseStep 846931 = 1270397) B1270397
theorem B4058275 : Blo 750330 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B1207475 : Blo 750330 1207475 := bstep (se 1 (by rfl) ⟨905606, by rfl⟩ : syracuseStep 1207475 = 1811213) B1811213
theorem B847075 : Blo 750330 847075 := bstep (se 1 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 847075 = 1270613) B1270613
theorem B847219 : Blo 750330 847219 := bstep (se 1 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 847219 = 1270829) B1270829
theorem B847363 : Blo 750330 847363 := bstep (se 1 (by rfl) ⟨635522, by rfl⟩ : syracuseStep 847363 = 1271045) B1271045
theorem B847507 : Blo 750330 847507 := bstep (se 1 (by rfl) ⟨635630, by rfl⟩ : syracuseStep 847507 = 1271261) B1271261
theorem B3206861 : Blo 750330 3206861 := bstep (se 3 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 3206861 = 1202573) B1202573
theorem B1044193 : Blo 750330 1044193 := bstep (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) B783145
theorem B3436301 : Blo 750330 3436301 := bstep (se 3 (by rfl) ⟨644306, by rfl⟩ : syracuseStep 3436301 = 1288613) B1288613
theorem B847651 : Blo 750330 847651 := bstep (se 1 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 847651 = 1271477) B1271477
theorem B847795 : Blo 750330 847795 := bstep (se 1 (by rfl) ⟨635846, by rfl⟩ : syracuseStep 847795 = 1271693) B1271693
theorem B847939 : Blo 750330 847939 := bstep (se 1 (by rfl) ⟨635954, by rfl⟩ : syracuseStep 847939 = 1271909) B1271909
theorem B4583587 : Blo 750330 4583587 := bstep (se 1 (by rfl) ⟨3437690, by rfl⟩ : syracuseStep 4583587 = 6875381) B6875381
theorem B848083 : Blo 750330 848083 := bstep (se 1 (by rfl) ⟨636062, by rfl⟩ : syracuseStep 848083 = 1272125) B1272125
theorem B848227 : Blo 750330 848227 := bstep (se 1 (by rfl) ⟨636170, by rfl⟩ : syracuseStep 848227 = 1272341) B1272341
theorem B1929635 : Blo 750330 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B848371 : Blo 750330 848371 := bstep (se 1 (by rfl) ⟨636278, by rfl⟩ : syracuseStep 848371 = 1272557) B1272557
theorem B3469873 : Blo 750330 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B848515 : Blo 750330 848515 := bstep (se 1 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 848515 = 1272773) B1272773
theorem B750339 : Blo 750330 750339 := bstep (se 1 (by rfl) ⟨562754, by rfl⟩ : syracuseStep 750339 = 1125509) B1125509
theorem B2716429 : Blo 750330 2716429 := bstep (se 3 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 2716429 = 1018661) B1018661
theorem B750355 : Blo 750330 750355 := bstep (se 1 (by rfl) ⟨562766, by rfl⟩ : syracuseStep 750355 = 1125533) B1125533
theorem B750371 : Blo 750330 750371 := bstep (se 1 (by rfl) ⟨562778, by rfl⟩ : syracuseStep 750371 = 1125557) B1125557
theorem B750387 : Blo 750330 750387 := bstep (se 1 (by rfl) ⟨562790, by rfl⟩ : syracuseStep 750387 = 1125581) B1125581
theorem B750403 : Blo 750330 750403 := bstep (se 1 (by rfl) ⟨562802, by rfl⟩ : syracuseStep 750403 = 1125605) B1125605
theorem B750419 : Blo 750330 750419 := bstep (se 1 (by rfl) ⟨562814, by rfl⟩ : syracuseStep 750419 = 1125629) B1125629
theorem B750435 : Blo 750330 750435 := bstep (se 1 (by rfl) ⟨562826, by rfl⟩ : syracuseStep 750435 = 1125653) B1125653
theorem B750451 : Blo 750330 750451 := bstep (se 1 (by rfl) ⟨562838, by rfl⟩ : syracuseStep 750451 = 1125677) B1125677
theorem B750467 : Blo 750330 750467 := bstep (se 1 (by rfl) ⟨562850, by rfl⟩ : syracuseStep 750467 = 1125701) B1125701
theorem B750483 : Blo 750330 750483 := bstep (se 1 (by rfl) ⟨562862, by rfl⟩ : syracuseStep 750483 = 1125725) B1125725
theorem B750499 : Blo 750330 750499 := bstep (se 1 (by rfl) ⟨562874, by rfl⟩ : syracuseStep 750499 = 1125749) B1125749
theorem B750515 : Blo 750330 750515 := bstep (se 1 (by rfl) ⟨562886, by rfl⟩ : syracuseStep 750515 = 1125773) B1125773
theorem B750531 : Blo 750330 750531 := bstep (se 1 (by rfl) ⟨562898, by rfl⟩ : syracuseStep 750531 = 1125797) B1125797
theorem B750547 : Blo 750330 750547 := bstep (se 1 (by rfl) ⟨562910, by rfl⟩ : syracuseStep 750547 = 1125821) B1125821
theorem B750563 : Blo 750330 750563 := bstep (se 1 (by rfl) ⟨562922, by rfl⟩ : syracuseStep 750563 = 1125845) B1125845
theorem B750579 : Blo 750330 750579 := bstep (se 1 (by rfl) ⟨562934, by rfl⟩ : syracuseStep 750579 = 1125869) B1125869
theorem B750595 : Blo 750330 750595 := bstep (se 1 (by rfl) ⟨562946, by rfl⟩ : syracuseStep 750595 = 1125893) B1125893
theorem B4813829 : Blo 750330 4813829 := bstep (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) B902593
theorem B750611 : Blo 750330 750611 := bstep (se 1 (by rfl) ⟨562958, by rfl⟩ : syracuseStep 750611 = 1125917) B1125917
theorem B750627 : Blo 750330 750627 := bstep (se 1 (by rfl) ⟨562970, by rfl⟩ : syracuseStep 750627 = 1125941) B1125941
theorem B750643 : Blo 750330 750643 := bstep (se 1 (by rfl) ⟨562982, by rfl⟩ : syracuseStep 750643 = 1125965) B1125965
theorem B750659 : Blo 750330 750659 := bstep (se 1 (by rfl) ⟨562994, by rfl⟩ : syracuseStep 750659 = 1125989) B1125989
theorem B750675 : Blo 750330 750675 := bstep (se 1 (by rfl) ⟨563006, by rfl⟩ : syracuseStep 750675 = 1126013) B1126013
theorem B750691 : Blo 750330 750691 := bstep (se 1 (by rfl) ⟨563018, by rfl⟩ : syracuseStep 750691 = 1126037) B1126037
theorem B750707 : Blo 750330 750707 := bstep (se 1 (by rfl) ⟨563030, by rfl⟩ : syracuseStep 750707 = 1126061) B1126061
theorem B750723 : Blo 750330 750723 := bstep (se 1 (by rfl) ⟨563042, by rfl⟩ : syracuseStep 750723 = 1126085) B1126085
theorem B750739 : Blo 750330 750739 := bstep (se 1 (by rfl) ⟨563054, by rfl⟩ : syracuseStep 750739 = 1126109) B1126109
theorem B750755 : Blo 750330 750755 := bstep (se 1 (by rfl) ⟨563066, by rfl⟩ : syracuseStep 750755 = 1126133) B1126133
theorem B750771 : Blo 750330 750771 := bstep (se 1 (by rfl) ⟨563078, by rfl⟩ : syracuseStep 750771 = 1126157) B1126157
theorem B750787 : Blo 750330 750787 := bstep (se 1 (by rfl) ⟨563090, by rfl⟩ : syracuseStep 750787 = 1126181) B1126181
theorem B750803 : Blo 750330 750803 := bstep (se 1 (by rfl) ⟨563102, by rfl⟩ : syracuseStep 750803 = 1126205) B1126205
theorem B750819 : Blo 750330 750819 := bstep (se 1 (by rfl) ⟨563114, by rfl⟩ : syracuseStep 750819 = 1126229) B1126229
theorem B750835 : Blo 750330 750835 := bstep (se 1 (by rfl) ⟨563126, by rfl⟩ : syracuseStep 750835 = 1126253) B1126253
theorem B750851 : Blo 750330 750851 := bstep (se 1 (by rfl) ⟨563138, by rfl⟩ : syracuseStep 750851 = 1126277) B1126277
theorem B2061571 : Blo 750330 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B750867 : Blo 750330 750867 := bstep (se 1 (by rfl) ⟨563150, by rfl⟩ : syracuseStep 750867 = 1126301) B1126301
theorem B750883 : Blo 750330 750883 := bstep (se 1 (by rfl) ⟨563162, by rfl⟩ : syracuseStep 750883 = 1126325) B1126325
theorem B750899 : Blo 750330 750899 := bstep (se 1 (by rfl) ⟨563174, by rfl⟩ : syracuseStep 750899 = 1126349) B1126349
theorem B750915 : Blo 750330 750915 := bstep (se 1 (by rfl) ⟨563186, by rfl⟩ : syracuseStep 750915 = 1126373) B1126373
theorem B750931 : Blo 750330 750931 := bstep (se 1 (by rfl) ⟨563198, by rfl⟩ : syracuseStep 750931 = 1126397) B1126397
theorem B750947 : Blo 750330 750947 := bstep (se 1 (by rfl) ⟨563210, by rfl⟩ : syracuseStep 750947 = 1126421) B1126421
theorem B750963 : Blo 750330 750963 := bstep (se 1 (by rfl) ⟨563222, by rfl⟩ : syracuseStep 750963 = 1126445) B1126445
theorem B750979 : Blo 750330 750979 := bstep (se 1 (by rfl) ⟨563234, by rfl⟩ : syracuseStep 750979 = 1126469) B1126469
theorem B750995 : Blo 750330 750995 := bstep (se 1 (by rfl) ⟨563246, by rfl⟩ : syracuseStep 750995 = 1126493) B1126493
theorem B751011 : Blo 750330 751011 := bstep (se 1 (by rfl) ⟨563258, by rfl⟩ : syracuseStep 751011 = 1126517) B1126517
theorem B751027 : Blo 750330 751027 := bstep (se 1 (by rfl) ⟨563270, by rfl⟩ : syracuseStep 751027 = 1126541) B1126541
theorem B751043 : Blo 750330 751043 := bstep (se 1 (by rfl) ⟨563282, by rfl⟩ : syracuseStep 751043 = 1126565) B1126565
theorem B751059 : Blo 750330 751059 := bstep (se 1 (by rfl) ⟨563294, by rfl⟩ : syracuseStep 751059 = 1126589) B1126589
theorem B751075 : Blo 750330 751075 := bstep (se 1 (by rfl) ⟨563306, by rfl⟩ : syracuseStep 751075 = 1126613) B1126613
theorem B751091 : Blo 750330 751091 := bstep (se 1 (by rfl) ⟨563318, by rfl⟩ : syracuseStep 751091 = 1126637) B1126637
theorem B751107 : Blo 750330 751107 := bstep (se 1 (by rfl) ⟨563330, by rfl⟩ : syracuseStep 751107 = 1126661) B1126661
theorem B751123 : Blo 750330 751123 := bstep (se 1 (by rfl) ⟨563342, by rfl⟩ : syracuseStep 751123 = 1126685) B1126685
theorem B751139 : Blo 750330 751139 := bstep (se 1 (by rfl) ⟨563354, by rfl⟩ : syracuseStep 751139 = 1126709) B1126709
theorem B1930787 : Blo 750330 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B751155 : Blo 750330 751155 := bstep (se 1 (by rfl) ⟨563366, by rfl⟩ : syracuseStep 751155 = 1126733) B1126733
theorem B751171 : Blo 750330 751171 := bstep (se 1 (by rfl) ⟨563378, by rfl⟩ : syracuseStep 751171 = 1126757) B1126757
theorem B751187 : Blo 750330 751187 := bstep (se 1 (by rfl) ⟨563390, by rfl⟩ : syracuseStep 751187 = 1126781) B1126781
theorem B751203 : Blo 750330 751203 := bstep (se 1 (by rfl) ⟨563402, by rfl⟩ : syracuseStep 751203 = 1126805) B1126805
theorem B2029169 : Blo 750330 2029169 := bstep (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) B1521877
theorem B751219 : Blo 750330 751219 := bstep (se 1 (by rfl) ⟨563414, by rfl⟩ : syracuseStep 751219 = 1126829) B1126829
theorem B751235 : Blo 750330 751235 := bstep (se 1 (by rfl) ⟨563426, by rfl⟩ : syracuseStep 751235 = 1126853) B1126853
theorem B751251 : Blo 750330 751251 := bstep (se 1 (by rfl) ⟨563438, by rfl⟩ : syracuseStep 751251 = 1126877) B1126877
theorem B751267 : Blo 750330 751267 := bstep (se 1 (by rfl) ⟨563450, by rfl⟩ : syracuseStep 751267 = 1126901) B1126901
theorem B751283 : Blo 750330 751283 := bstep (se 1 (by rfl) ⟨563462, by rfl⟩ : syracuseStep 751283 = 1126925) B1126925
theorem B751299 : Blo 750330 751299 := bstep (se 1 (by rfl) ⟨563474, by rfl⟩ : syracuseStep 751299 = 1126949) B1126949
theorem B751315 : Blo 750330 751315 := bstep (se 1 (by rfl) ⟨563486, by rfl⟩ : syracuseStep 751315 = 1126973) B1126973
theorem B751331 : Blo 750330 751331 := bstep (se 1 (by rfl) ⟨563498, by rfl⟩ : syracuseStep 751331 = 1126997) B1126997
theorem B751347 : Blo 750330 751347 := bstep (se 1 (by rfl) ⟨563510, by rfl⟩ : syracuseStep 751347 = 1127021) B1127021
theorem B751363 : Blo 750330 751363 := bstep (se 1 (by rfl) ⟨563522, by rfl⟩ : syracuseStep 751363 = 1127045) B1127045
theorem B751379 : Blo 750330 751379 := bstep (se 1 (by rfl) ⟨563534, by rfl⟩ : syracuseStep 751379 = 1127069) B1127069
theorem B751395 : Blo 750330 751395 := bstep (se 1 (by rfl) ⟨563546, by rfl⟩ : syracuseStep 751395 = 1127093) B1127093
theorem B751411 : Blo 750330 751411 := bstep (se 1 (by rfl) ⟨563558, by rfl⟩ : syracuseStep 751411 = 1127117) B1127117
theorem B751427 : Blo 750330 751427 := bstep (se 1 (by rfl) ⟨563570, by rfl⟩ : syracuseStep 751427 = 1127141) B1127141
theorem B751443 : Blo 750330 751443 := bstep (se 1 (by rfl) ⟨563582, by rfl⟩ : syracuseStep 751443 = 1127165) B1127165
theorem B751459 : Blo 750330 751459 := bstep (se 1 (by rfl) ⟨563594, by rfl⟩ : syracuseStep 751459 = 1127189) B1127189
theorem B751475 : Blo 750330 751475 := bstep (se 1 (by rfl) ⟨563606, by rfl⟩ : syracuseStep 751475 = 1127213) B1127213
theorem B751491 : Blo 750330 751491 := bstep (se 1 (by rfl) ⟨563618, by rfl⟩ : syracuseStep 751491 = 1127237) B1127237
theorem B751507 : Blo 750330 751507 := bstep (se 1 (by rfl) ⟨563630, by rfl⟩ : syracuseStep 751507 = 1127261) B1127261
theorem B751523 : Blo 750330 751523 := bstep (se 1 (by rfl) ⟨563642, by rfl⟩ : syracuseStep 751523 = 1127285) B1127285
theorem B751539 : Blo 750330 751539 := bstep (se 1 (by rfl) ⟨563654, by rfl⟩ : syracuseStep 751539 = 1127309) B1127309
theorem B751555 : Blo 750330 751555 := bstep (se 1 (by rfl) ⟨563666, by rfl⟩ : syracuseStep 751555 = 1127333) B1127333
theorem B751571 : Blo 750330 751571 := bstep (se 1 (by rfl) ⟨563678, by rfl⟩ : syracuseStep 751571 = 1127357) B1127357
theorem B751587 : Blo 750330 751587 := bstep (se 1 (by rfl) ⟨563690, by rfl⟩ : syracuseStep 751587 = 1127381) B1127381
theorem B751603 : Blo 750330 751603 := bstep (se 1 (by rfl) ⟨563702, by rfl⟩ : syracuseStep 751603 = 1127405) B1127405
theorem B751619 : Blo 750330 751619 := bstep (se 1 (by rfl) ⟨563714, by rfl⟩ : syracuseStep 751619 = 1127429) B1127429
theorem B751635 : Blo 750330 751635 := bstep (se 1 (by rfl) ⟨563726, by rfl⟩ : syracuseStep 751635 = 1127453) B1127453
theorem B751651 : Blo 750330 751651 := bstep (se 1 (by rfl) ⟨563738, by rfl⟩ : syracuseStep 751651 = 1127477) B1127477
theorem B751667 : Blo 750330 751667 := bstep (se 1 (by rfl) ⟨563750, by rfl⟩ : syracuseStep 751667 = 1127501) B1127501
theorem B751683 : Blo 750330 751683 := bstep (se 1 (by rfl) ⟨563762, by rfl⟩ : syracuseStep 751683 = 1127525) B1127525
theorem B751699 : Blo 750330 751699 := bstep (se 1 (by rfl) ⟨563774, by rfl⟩ : syracuseStep 751699 = 1127549) B1127549
theorem B751715 : Blo 750330 751715 := bstep (se 1 (by rfl) ⟨563786, by rfl⟩ : syracuseStep 751715 = 1127573) B1127573
theorem B751731 : Blo 750330 751731 := bstep (se 1 (by rfl) ⟨563798, by rfl⟩ : syracuseStep 751731 = 1127597) B1127597
theorem B751747 : Blo 750330 751747 := bstep (se 1 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 751747 = 1127621) B1127621
theorem B5961869 : Blo 750330 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B751763 : Blo 750330 751763 := bstep (se 1 (by rfl) ⟨563822, by rfl⟩ : syracuseStep 751763 = 1127645) B1127645
theorem B3045539 : Blo 750330 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B751779 : Blo 750330 751779 := bstep (se 1 (by rfl) ⟨563834, by rfl⟩ : syracuseStep 751779 = 1127669) B1127669
theorem B751795 : Blo 750330 751795 := bstep (se 1 (by rfl) ⟨563846, by rfl⟩ : syracuseStep 751795 = 1127693) B1127693
theorem B751811 : Blo 750330 751811 := bstep (se 1 (by rfl) ⟨563858, by rfl⟩ : syracuseStep 751811 = 1127717) B1127717
theorem B751827 : Blo 750330 751827 := bstep (se 1 (by rfl) ⟨563870, by rfl⟩ : syracuseStep 751827 = 1127741) B1127741
theorem B751843 : Blo 750330 751843 := bstep (se 1 (by rfl) ⟨563882, by rfl⟩ : syracuseStep 751843 = 1127765) B1127765
theorem B2291939 : Blo 750330 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B751859 : Blo 750330 751859 := bstep (se 1 (by rfl) ⟨563894, by rfl⟩ : syracuseStep 751859 = 1127789) B1127789
theorem B751875 : Blo 750330 751875 := bstep (se 1 (by rfl) ⟨563906, by rfl⟩ : syracuseStep 751875 = 1127813) B1127813
theorem B751891 : Blo 750330 751891 := bstep (se 1 (by rfl) ⟨563918, by rfl⟩ : syracuseStep 751891 = 1127837) B1127837
theorem B751907 : Blo 750330 751907 := bstep (se 1 (by rfl) ⟨563930, by rfl⟩ : syracuseStep 751907 = 1127861) B1127861
theorem B751923 : Blo 750330 751923 := bstep (se 1 (by rfl) ⟨563942, by rfl⟩ : syracuseStep 751923 = 1127885) B1127885
theorem B751939 : Blo 750330 751939 := bstep (se 1 (by rfl) ⟨563954, by rfl⟩ : syracuseStep 751939 = 1127909) B1127909
theorem B751955 : Blo 750330 751955 := bstep (se 1 (by rfl) ⟨563966, by rfl⟩ : syracuseStep 751955 = 1127933) B1127933
theorem B751971 : Blo 750330 751971 := bstep (se 1 (by rfl) ⟨563978, by rfl⟩ : syracuseStep 751971 = 1127957) B1127957
theorem B751987 : Blo 750330 751987 := bstep (se 1 (by rfl) ⟨563990, by rfl⟩ : syracuseStep 751987 = 1127981) B1127981
theorem B752003 : Blo 750330 752003 := bstep (se 1 (by rfl) ⟨564002, by rfl⟩ : syracuseStep 752003 = 1128005) B1128005
theorem B752019 : Blo 750330 752019 := bstep (se 1 (by rfl) ⟨564014, by rfl⟩ : syracuseStep 752019 = 1128029) B1128029
theorem B752035 : Blo 750330 752035 := bstep (se 1 (by rfl) ⟨564026, by rfl⟩ : syracuseStep 752035 = 1128053) B1128053
theorem B752051 : Blo 750330 752051 := bstep (se 1 (by rfl) ⟨564038, by rfl⟩ : syracuseStep 752051 = 1128077) B1128077
theorem B752067 : Blo 750330 752067 := bstep (se 1 (by rfl) ⟨564050, by rfl⟩ : syracuseStep 752067 = 1128101) B1128101
theorem B752083 : Blo 750330 752083 := bstep (se 1 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 752083 = 1128125) B1128125
theorem B752099 : Blo 750330 752099 := bstep (se 1 (by rfl) ⟨564074, by rfl⟩ : syracuseStep 752099 = 1128149) B1128149
theorem B752115 : Blo 750330 752115 := bstep (se 1 (by rfl) ⟨564086, by rfl⟩ : syracuseStep 752115 = 1128173) B1128173
theorem B752131 : Blo 750330 752131 := bstep (se 1 (by rfl) ⟨564098, by rfl⟩ : syracuseStep 752131 = 1128197) B1128197
theorem B752147 : Blo 750330 752147 := bstep (se 1 (by rfl) ⟨564110, by rfl⟩ : syracuseStep 752147 = 1128221) B1128221
theorem B752163 : Blo 750330 752163 := bstep (se 1 (by rfl) ⟨564122, by rfl⟩ : syracuseStep 752163 = 1128245) B1128245
theorem B2062883 : Blo 750330 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B752179 : Blo 750330 752179 := bstep (se 1 (by rfl) ⟨564134, by rfl⟩ : syracuseStep 752179 = 1128269) B1128269
theorem B752195 : Blo 750330 752195 := bstep (se 1 (by rfl) ⟨564146, by rfl⟩ : syracuseStep 752195 = 1128293) B1128293
theorem B2849357 : Blo 750330 2849357 := bstep (se 3 (by rfl) ⟨534254, by rfl⟩ : syracuseStep 2849357 = 1068509) B1068509
theorem B752211 : Blo 750330 752211 := bstep (se 1 (by rfl) ⟨564158, by rfl⟩ : syracuseStep 752211 = 1128317) B1128317
theorem B752227 : Blo 750330 752227 := bstep (se 1 (by rfl) ⟨564170, by rfl⟩ : syracuseStep 752227 = 1128341) B1128341
theorem B752243 : Blo 750330 752243 := bstep (se 1 (by rfl) ⟨564182, by rfl⟩ : syracuseStep 752243 = 1128365) B1128365
theorem B1014401 : Blo 750330 1014401 := bstep (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) B760801
theorem B752259 : Blo 750330 752259 := bstep (se 1 (by rfl) ⟨564194, by rfl⟩ : syracuseStep 752259 = 1128389) B1128389
theorem B752275 : Blo 750330 752275 := bstep (se 1 (by rfl) ⟨564206, by rfl⟩ : syracuseStep 752275 = 1128413) B1128413
theorem B752291 : Blo 750330 752291 := bstep (se 1 (by rfl) ⟨564218, by rfl⟩ : syracuseStep 752291 = 1128437) B1128437
theorem B1145507 : Blo 750330 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B752307 : Blo 750330 752307 := bstep (se 1 (by rfl) ⟨564230, by rfl⟩ : syracuseStep 752307 = 1128461) B1128461
theorem B752323 : Blo 750330 752323 := bstep (se 1 (by rfl) ⟨564242, by rfl⟩ : syracuseStep 752323 = 1128485) B1128485
theorem B5700293 : Blo 750330 5700293 := bstep (se 4 (by rfl) ⟨534402, by rfl⟩ : syracuseStep 5700293 = 1068805) B1068805
theorem B752339 : Blo 750330 752339 := bstep (se 1 (by rfl) ⟨564254, by rfl⟩ : syracuseStep 752339 = 1128509) B1128509
theorem B752355 : Blo 750330 752355 := bstep (se 1 (by rfl) ⟨564266, by rfl⟩ : syracuseStep 752355 = 1128533) B1128533
theorem B3209969 : Blo 750330 3209969 := bstep (se 2 (by rfl) ⟨1203738, by rfl⟩ : syracuseStep 3209969 = 2407477) B2407477
theorem B752371 : Blo 750330 752371 := bstep (se 1 (by rfl) ⟨564278, by rfl⟩ : syracuseStep 752371 = 1128557) B1128557
theorem B752387 : Blo 750330 752387 := bstep (se 1 (by rfl) ⟨564290, by rfl⟩ : syracuseStep 752387 = 1128581) B1128581
theorem B752403 : Blo 750330 752403 := bstep (se 1 (by rfl) ⟨564302, by rfl⟩ : syracuseStep 752403 = 1128605) B1128605
theorem B1604387 : Blo 750330 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B752419 : Blo 750330 752419 := bstep (se 1 (by rfl) ⟨564314, by rfl⟩ : syracuseStep 752419 = 1128629) B1128629
theorem B752435 : Blo 750330 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B752451 : Blo 750330 752451 := bstep (se 1 (by rfl) ⟨564338, by rfl⟩ : syracuseStep 752451 = 1128677) B1128677
theorem B752467 : Blo 750330 752467 := bstep (se 1 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 752467 = 1128701) B1128701
theorem B752483 : Blo 750330 752483 := bstep (se 1 (by rfl) ⟨564362, by rfl⟩ : syracuseStep 752483 = 1128725) B1128725
theorem B752499 : Blo 750330 752499 := bstep (se 1 (by rfl) ⟨564374, by rfl⟩ : syracuseStep 752499 = 1128749) B1128749
theorem B752515 : Blo 750330 752515 := bstep (se 1 (by rfl) ⟨564386, by rfl⟩ : syracuseStep 752515 = 1128773) B1128773
theorem B1899409 : Blo 750330 1899409 := bstep (se 2 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 1899409 = 1424557) B1424557
theorem B752531 : Blo 750330 752531 := bstep (se 1 (by rfl) ⟨564398, by rfl⟩ : syracuseStep 752531 = 1128797) B1128797
theorem B752547 : Blo 750330 752547 := bstep (se 1 (by rfl) ⟨564410, by rfl⟩ : syracuseStep 752547 = 1128821) B1128821
theorem B752563 : Blo 750330 752563 := bstep (se 1 (by rfl) ⟨564422, by rfl⟩ : syracuseStep 752563 = 1128845) B1128845
theorem B752579 : Blo 750330 752579 := bstep (se 1 (by rfl) ⟨564434, by rfl⟩ : syracuseStep 752579 = 1128869) B1128869
theorem B3046349 : Blo 750330 3046349 := bstep (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) B1142381
theorem B752595 : Blo 750330 752595 := bstep (se 1 (by rfl) ⟨564446, by rfl⟩ : syracuseStep 752595 = 1128893) B1128893
theorem B752611 : Blo 750330 752611 := bstep (se 1 (by rfl) ⟨564458, by rfl⟩ : syracuseStep 752611 = 1128917) B1128917
theorem B752627 : Blo 750330 752627 := bstep (se 1 (by rfl) ⟨564470, by rfl⟩ : syracuseStep 752627 = 1128941) B1128941
theorem B752643 : Blo 750330 752643 := bstep (se 1 (by rfl) ⟨564482, by rfl⟩ : syracuseStep 752643 = 1128965) B1128965
theorem B752659 : Blo 750330 752659 := bstep (se 1 (by rfl) ⟨564494, by rfl⟩ : syracuseStep 752659 = 1128989) B1128989
theorem B752675 : Blo 750330 752675 := bstep (se 1 (by rfl) ⟨564506, by rfl⟩ : syracuseStep 752675 = 1129013) B1129013
theorem B752691 : Blo 750330 752691 := bstep (se 1 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 752691 = 1129037) B1129037
theorem B752707 : Blo 750330 752707 := bstep (se 1 (by rfl) ⟨564530, by rfl⟩ : syracuseStep 752707 = 1129061) B1129061
theorem B752723 : Blo 750330 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B752739 : Blo 750330 752739 := bstep (se 1 (by rfl) ⟨564554, by rfl⟩ : syracuseStep 752739 = 1129109) B1129109
theorem B752755 : Blo 750330 752755 := bstep (se 1 (by rfl) ⟨564566, by rfl⟩ : syracuseStep 752755 = 1129133) B1129133
theorem B752771 : Blo 750330 752771 := bstep (se 1 (by rfl) ⟨564578, by rfl⟩ : syracuseStep 752771 = 1129157) B1129157
theorem B752787 : Blo 750330 752787 := bstep (se 1 (by rfl) ⟨564590, by rfl⟩ : syracuseStep 752787 = 1129181) B1129181
theorem B1899683 : Blo 750330 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B752803 : Blo 750330 752803 := bstep (se 1 (by rfl) ⟨564602, by rfl⟩ : syracuseStep 752803 = 1129205) B1129205
theorem B752819 : Blo 750330 752819 := bstep (se 1 (by rfl) ⟨564614, by rfl⟩ : syracuseStep 752819 = 1129229) B1129229
theorem B752835 : Blo 750330 752835 := bstep (se 1 (by rfl) ⟨564626, by rfl⟩ : syracuseStep 752835 = 1129253) B1129253
theorem B752851 : Blo 750330 752851 := bstep (se 1 (by rfl) ⟨564638, by rfl⟩ : syracuseStep 752851 = 1129277) B1129277
theorem B752867 : Blo 750330 752867 := bstep (se 1 (by rfl) ⟨564650, by rfl⟩ : syracuseStep 752867 = 1129301) B1129301
theorem B752883 : Blo 750330 752883 := bstep (se 1 (by rfl) ⟨564662, by rfl⟩ : syracuseStep 752883 = 1129325) B1129325
theorem B752899 : Blo 750330 752899 := bstep (se 1 (by rfl) ⟨564674, by rfl⟩ : syracuseStep 752899 = 1129349) B1129349
theorem B752915 : Blo 750330 752915 := bstep (se 1 (by rfl) ⟨564686, by rfl⟩ : syracuseStep 752915 = 1129373) B1129373
theorem B752931 : Blo 750330 752931 := bstep (se 1 (by rfl) ⟨564698, by rfl⟩ : syracuseStep 752931 = 1129397) B1129397
theorem B752947 : Blo 750330 752947 := bstep (se 1 (by rfl) ⟨564710, by rfl⟩ : syracuseStep 752947 = 1129421) B1129421
theorem B752963 : Blo 750330 752963 := bstep (se 1 (by rfl) ⟨564722, by rfl⟩ : syracuseStep 752963 = 1129445) B1129445
theorem B752979 : Blo 750330 752979 := bstep (se 1 (by rfl) ⟨564734, by rfl⟩ : syracuseStep 752979 = 1129469) B1129469
theorem B1899875 : Blo 750330 1899875 := bstep (se 1 (by rfl) ⟨1424906, by rfl⟩ : syracuseStep 1899875 = 2849813) B2849813
theorem B752995 : Blo 750330 752995 := bstep (se 1 (by rfl) ⟨564746, by rfl⟩ : syracuseStep 752995 = 1129493) B1129493
theorem B753011 : Blo 750330 753011 := bstep (se 1 (by rfl) ⟨564758, by rfl⟩ : syracuseStep 753011 = 1129517) B1129517
theorem B753027 : Blo 750330 753027 := bstep (se 1 (by rfl) ⟨564770, by rfl⟩ : syracuseStep 753027 = 1129541) B1129541
theorem B3210637 : Blo 750330 3210637 := bstep (se 3 (by rfl) ⟨601994, by rfl⟩ : syracuseStep 3210637 = 1203989) B1203989
theorem B753043 : Blo 750330 753043 := bstep (se 1 (by rfl) ⟨564782, by rfl⟩ : syracuseStep 753043 = 1129565) B1129565
theorem B1015201 : Blo 750330 1015201 := bstep (se 2 (by rfl) ⟨380700, by rfl⟩ : syracuseStep 1015201 = 761401) B761401
theorem B753059 : Blo 750330 753059 := bstep (se 1 (by rfl) ⟨564794, by rfl⟩ : syracuseStep 753059 = 1129589) B1129589
theorem B753075 : Blo 750330 753075 := bstep (se 1 (by rfl) ⟨564806, by rfl⟩ : syracuseStep 753075 = 1129613) B1129613
theorem B1146305 : Blo 750330 1146305 := bstep (se 2 (by rfl) ⟨429864, by rfl⟩ : syracuseStep 1146305 = 859729) B859729
theorem B753091 : Blo 750330 753091 := bstep (se 1 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 753091 = 1129637) B1129637
theorem B753107 : Blo 750330 753107 := bstep (se 1 (by rfl) ⟨564830, by rfl⟩ : syracuseStep 753107 = 1129661) B1129661
theorem B753123 : Blo 750330 753123 := bstep (se 1 (by rfl) ⟨564842, by rfl⟩ : syracuseStep 753123 = 1129685) B1129685
theorem B753139 : Blo 750330 753139 := bstep (se 1 (by rfl) ⟨564854, by rfl⟩ : syracuseStep 753139 = 1129709) B1129709
theorem B753155 : Blo 750330 753155 := bstep (se 1 (by rfl) ⟨564866, by rfl⟩ : syracuseStep 753155 = 1129733) B1129733
theorem B753171 : Blo 750330 753171 := bstep (se 1 (by rfl) ⟨564878, by rfl⟩ : syracuseStep 753171 = 1129757) B1129757
theorem B753187 : Blo 750330 753187 := bstep (se 1 (by rfl) ⟨564890, by rfl⟩ : syracuseStep 753187 = 1129781) B1129781
theorem B753203 : Blo 750330 753203 := bstep (se 1 (by rfl) ⟨564902, by rfl⟩ : syracuseStep 753203 = 1129805) B1129805
theorem B753219 : Blo 750330 753219 := bstep (se 1 (by rfl) ⟨564914, by rfl⟩ : syracuseStep 753219 = 1129829) B1129829
theorem B753235 : Blo 750330 753235 := bstep (se 1 (by rfl) ⟨564926, by rfl⟩ : syracuseStep 753235 = 1129853) B1129853
theorem B753251 : Blo 750330 753251 := bstep (se 1 (by rfl) ⟨564938, by rfl⟩ : syracuseStep 753251 = 1129877) B1129877
theorem B753267 : Blo 750330 753267 := bstep (se 1 (by rfl) ⟨564950, by rfl⟩ : syracuseStep 753267 = 1129901) B1129901
theorem B1605251 : Blo 750330 1605251 := bstep (se 1 (by rfl) ⟨1203938, by rfl⟩ : syracuseStep 1605251 = 2407877) B2407877
theorem B753283 : Blo 750330 753283 := bstep (se 1 (by rfl) ⟨564962, by rfl⟩ : syracuseStep 753283 = 1129925) B1129925
theorem B2031245 : Blo 750330 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B949907 : Blo 750330 949907 := bstep (se 1 (by rfl) ⟨712430, by rfl⟩ : syracuseStep 949907 = 1424861) B1424861
theorem B753299 : Blo 750330 753299 := bstep (se 1 (by rfl) ⟨564974, by rfl⟩ : syracuseStep 753299 = 1129949) B1129949
theorem B753315 : Blo 750330 753315 := bstep (se 1 (by rfl) ⟨564986, by rfl⟩ : syracuseStep 753315 = 1129973) B1129973
theorem B753331 : Blo 750330 753331 := bstep (se 1 (by rfl) ⟨564998, by rfl⟩ : syracuseStep 753331 = 1129997) B1129997
theorem B753347 : Blo 750330 753347 := bstep (se 1 (by rfl) ⟨565010, by rfl⟩ : syracuseStep 753347 = 1130021) B1130021
theorem B753363 : Blo 750330 753363 := bstep (se 1 (by rfl) ⟨565022, by rfl⟩ : syracuseStep 753363 = 1130045) B1130045
theorem B753379 : Blo 750330 753379 := bstep (se 1 (by rfl) ⟨565034, by rfl⟩ : syracuseStep 753379 = 1130069) B1130069
theorem B1605361 : Blo 750330 1605361 := bstep (se 2 (by rfl) ⟨602010, by rfl⟩ : syracuseStep 1605361 = 1204021) B1204021
theorem B753395 : Blo 750330 753395 := bstep (se 1 (by rfl) ⟨565046, by rfl⟩ : syracuseStep 753395 = 1130093) B1130093
theorem B753411 : Blo 750330 753411 := bstep (se 1 (by rfl) ⟨565058, by rfl⟩ : syracuseStep 753411 = 1130117) B1130117
theorem B753427 : Blo 750330 753427 := bstep (se 1 (by rfl) ⟨565070, by rfl⟩ : syracuseStep 753427 = 1130141) B1130141
theorem B753443 : Blo 750330 753443 := bstep (se 1 (by rfl) ⟨565082, by rfl⟩ : syracuseStep 753443 = 1130165) B1130165
theorem B753459 : Blo 750330 753459 := bstep (se 1 (by rfl) ⟨565094, by rfl⟩ : syracuseStep 753459 = 1130189) B1130189
theorem B18579253 : Blo 750330 18579253 := bstep (se 5 (by rfl) ⟨870902, by rfl⟩ : syracuseStep 18579253 = 1741805) B1741805
theorem B753475 : Blo 750330 753475 := bstep (se 1 (by rfl) ⟨565106, by rfl⟩ : syracuseStep 753475 = 1130213) B1130213
theorem B753491 : Blo 750330 753491 := bstep (se 1 (by rfl) ⟨565118, by rfl⟩ : syracuseStep 753491 = 1130237) B1130237
theorem B753507 : Blo 750330 753507 := bstep (se 1 (by rfl) ⟨565130, by rfl⟩ : syracuseStep 753507 = 1130261) B1130261
theorem B753523 : Blo 750330 753523 := bstep (se 1 (by rfl) ⟨565142, by rfl⟩ : syracuseStep 753523 = 1130285) B1130285
theorem B753539 : Blo 750330 753539 := bstep (se 1 (by rfl) ⟨565154, by rfl⟩ : syracuseStep 753539 = 1130309) B1130309
theorem B753555 : Blo 750330 753555 := bstep (se 1 (by rfl) ⟨565166, by rfl⟩ : syracuseStep 753555 = 1130333) B1130333
theorem B753571 : Blo 750330 753571 := bstep (se 1 (by rfl) ⟨565178, by rfl⟩ : syracuseStep 753571 = 1130357) B1130357
theorem B753587 : Blo 750330 753587 := bstep (se 1 (by rfl) ⟨565190, by rfl⟩ : syracuseStep 753587 = 1130381) B1130381
theorem B753603 : Blo 750330 753603 := bstep (se 1 (by rfl) ⟨565202, by rfl⟩ : syracuseStep 753603 = 1130405) B1130405
theorem B753619 : Blo 750330 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B3211235 : Blo 750330 3211235 := bstep (se 1 (by rfl) ⟨2408426, by rfl⟩ : syracuseStep 3211235 = 4816853) B4816853
theorem B753635 : Blo 750330 753635 := bstep (se 1 (by rfl) ⟨565226, by rfl⟩ : syracuseStep 753635 = 1130453) B1130453
theorem B753651 : Blo 750330 753651 := bstep (se 1 (by rfl) ⟨565238, by rfl⟩ : syracuseStep 753651 = 1130477) B1130477
theorem B753675 : Blo 750330 753675 := bstep (se 1 (by rfl) ⟨565256, by rfl⟩ : syracuseStep 753675 = 1130513) B1130513
theorem B753687 : Blo 750330 753687 := bstep (se 1 (by rfl) ⟨565265, by rfl⟩ : syracuseStep 753687 = 1130531) B1130531
theorem B753707 : Blo 750330 753707 := bstep (se 1 (by rfl) ⟨565280, by rfl⟩ : syracuseStep 753707 = 1130561) B1130561
theorem B753719 : Blo 750330 753719 := bstep (se 1 (by rfl) ⟨565289, by rfl⟩ : syracuseStep 753719 = 1130579) B1130579
theorem B753739 : Blo 750330 753739 := bstep (se 1 (by rfl) ⟨565304, by rfl⟩ : syracuseStep 753739 = 1130609) B1130609
theorem B753751 : Blo 750330 753751 := bstep (se 1 (by rfl) ⟨565313, by rfl⟩ : syracuseStep 753751 = 1130627) B1130627
theorem B753771 : Blo 750330 753771 := bstep (se 1 (by rfl) ⟨565328, by rfl⟩ : syracuseStep 753771 = 1130657) B1130657
theorem B753783 : Blo 750330 753783 := bstep (se 1 (by rfl) ⟨565337, by rfl⟩ : syracuseStep 753783 = 1130675) B1130675
theorem B753803 : Blo 750330 753803 := bstep (se 1 (by rfl) ⟨565352, by rfl⟩ : syracuseStep 753803 = 1130705) B1130705
theorem B753815 : Blo 750330 753815 := bstep (se 1 (by rfl) ⟨565361, by rfl⟩ : syracuseStep 753815 = 1130723) B1130723
theorem B753835 : Blo 750330 753835 := bstep (se 1 (by rfl) ⟨565376, by rfl⟩ : syracuseStep 753835 = 1130753) B1130753
theorem B753847 : Blo 750330 753847 := bstep (se 1 (by rfl) ⟨565385, by rfl⟩ : syracuseStep 753847 = 1130771) B1130771
theorem B753867 : Blo 750330 753867 := bstep (se 1 (by rfl) ⟨565400, by rfl⟩ : syracuseStep 753867 = 1130801) B1130801
theorem B753879 : Blo 750330 753879 := bstep (se 1 (by rfl) ⟨565409, by rfl⟩ : syracuseStep 753879 = 1130819) B1130819
theorem B753899 : Blo 750330 753899 := bstep (se 1 (by rfl) ⟨565424, by rfl⟩ : syracuseStep 753899 = 1130849) B1130849
theorem B753911 : Blo 750330 753911 := bstep (se 1 (by rfl) ⟨565433, by rfl⟩ : syracuseStep 753911 = 1130867) B1130867
theorem B753931 : Blo 750330 753931 := bstep (se 1 (by rfl) ⟨565448, by rfl⟩ : syracuseStep 753931 = 1130897) B1130897
theorem B753943 : Blo 750330 753943 := bstep (se 1 (by rfl) ⟨565457, by rfl⟩ : syracuseStep 753943 = 1130915) B1130915
theorem B753963 : Blo 750330 753963 := bstep (se 1 (by rfl) ⟨565472, by rfl⟩ : syracuseStep 753963 = 1130945) B1130945
theorem B753975 : Blo 750330 753975 := bstep (se 1 (by rfl) ⟨565481, by rfl⟩ : syracuseStep 753975 = 1130963) B1130963
theorem B3211595 : Blo 750330 3211595 := bstep (se 1 (by rfl) ⟨2408696, by rfl⟩ : syracuseStep 3211595 = 4817393) B4817393
theorem B753995 : Blo 750330 753995 := bstep (se 1 (by rfl) ⟨565496, by rfl⟩ : syracuseStep 753995 = 1130993) B1130993
theorem B754007 : Blo 750330 754007 := bstep (se 1 (by rfl) ⟨565505, by rfl⟩ : syracuseStep 754007 = 1131011) B1131011
theorem B754027 : Blo 750330 754027 := bstep (se 1 (by rfl) ⟨565520, by rfl⟩ : syracuseStep 754027 = 1131041) B1131041
theorem B754039 : Blo 750330 754039 := bstep (se 1 (by rfl) ⟨565529, by rfl⟩ : syracuseStep 754039 = 1131059) B1131059
theorem B754059 : Blo 750330 754059 := bstep (se 1 (by rfl) ⟨565544, by rfl⟩ : syracuseStep 754059 = 1131089) B1131089
theorem B754071 : Blo 750330 754071 := bstep (se 1 (by rfl) ⟨565553, by rfl⟩ : syracuseStep 754071 = 1131107) B1131107
theorem B754091 : Blo 750330 754091 := bstep (se 1 (by rfl) ⟨565568, by rfl⟩ : syracuseStep 754091 = 1131137) B1131137
theorem B1900979 : Blo 750330 1900979 := bstep (se 1 (by rfl) ⟨1425734, by rfl⟩ : syracuseStep 1900979 = 2851469) B2851469
theorem B754103 : Blo 750330 754103 := bstep (se 1 (by rfl) ⟨565577, by rfl⟩ : syracuseStep 754103 = 1131155) B1131155
theorem B754123 : Blo 750330 754123 := bstep (se 1 (by rfl) ⟨565592, by rfl⟩ : syracuseStep 754123 = 1131185) B1131185
theorem B754135 : Blo 750330 754135 := bstep (se 1 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 754135 = 1131203) B1131203
theorem B754155 : Blo 750330 754155 := bstep (se 1 (by rfl) ⟨565616, by rfl⟩ : syracuseStep 754155 = 1131233) B1131233
theorem B754167 : Blo 750330 754167 := bstep (se 1 (by rfl) ⟨565625, by rfl⟩ : syracuseStep 754167 = 1131251) B1131251
theorem B3047939 : Blo 750330 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B754187 : Blo 750330 754187 := bstep (se 1 (by rfl) ⟨565640, by rfl⟩ : syracuseStep 754187 = 1131281) B1131281
theorem B754199 : Blo 750330 754199 := bstep (se 1 (by rfl) ⟨565649, by rfl⟩ : syracuseStep 754199 = 1131299) B1131299
theorem B754219 : Blo 750330 754219 := bstep (se 1 (by rfl) ⟨565664, by rfl⟩ : syracuseStep 754219 = 1131329) B1131329
theorem B754231 : Blo 750330 754231 := bstep (se 1 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 754231 = 1131347) B1131347
theorem B754251 : Blo 750330 754251 := bstep (se 1 (by rfl) ⟨565688, by rfl⟩ : syracuseStep 754251 = 1131377) B1131377
theorem B754263 : Blo 750330 754263 := bstep (se 1 (by rfl) ⟨565697, by rfl⟩ : syracuseStep 754263 = 1131395) B1131395
theorem B5702237 : Blo 750330 5702237 := bstep (se 3 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 5702237 = 2138339) B2138339
theorem B754283 : Blo 750330 754283 := bstep (se 1 (by rfl) ⟨565712, by rfl⟩ : syracuseStep 754283 = 1131425) B1131425
theorem B754295 : Blo 750330 754295 := bstep (se 1 (by rfl) ⟨565721, by rfl⟩ : syracuseStep 754295 = 1131443) B1131443
theorem B754315 : Blo 750330 754315 := bstep (se 1 (by rfl) ⟨565736, by rfl⟩ : syracuseStep 754315 = 1131473) B1131473
theorem B950935 : Blo 750330 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B754327 : Blo 750330 754327 := bstep (se 1 (by rfl) ⟨565745, by rfl⟩ : syracuseStep 754327 = 1131491) B1131491
theorem B9634625 : Blo 750330 9634625 := bstep (se 2 (by rfl) ⟨3612984, by rfl⟩ : syracuseStep 9634625 = 7225969) B7225969
theorem B2851757 : Blo 750330 2851757 := bstep (se 3 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 2851757 = 1069409) B1069409
theorem B8586161 : Blo 750330 8586161 := bstep (se 2 (by rfl) ⟨3219810, by rfl⟩ : syracuseStep 8586161 = 6439621) B6439621
theorem B2851787 : Blo 750330 2851787 := bstep (se 1 (by rfl) ⟨2138840, by rfl⟩ : syracuseStep 2851787 = 4277681) B4277681
theorem B1901515 : Blo 750330 1901515 := bstep (se 1 (by rfl) ⟨1426136, by rfl⟩ : syracuseStep 1901515 = 2852273) B2852273
theorem B1901657 : Blo 750330 1901657 := bstep (se 2 (by rfl) ⟨713121, by rfl⟩ : syracuseStep 1901657 = 1426243) B1426243
theorem B3212567 : Blo 750330 3212567 := bstep (se 1 (by rfl) ⟨2409425, by rfl⟩ : syracuseStep 3212567 = 4818851) B4818851
theorem B12846437 : Blo 750330 12846437 := bstep (se 4 (by rfl) ⟨1204353, by rfl⟩ : syracuseStep 12846437 = 2408707) B2408707
theorem B6424109 : Blo 750330 6424109 := bstep (se 3 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 6424109 = 2409041) B2409041
theorem B2852441 : Blo 750330 2852441 := bstep (se 2 (by rfl) ⟨1069665, by rfl⟩ : syracuseStep 2852441 = 2139331) B2139331
theorem B1607411 : Blo 750330 1607411 := bstep (se 1 (by rfl) ⟨1205558, by rfl⟩ : syracuseStep 1607411 = 2411117) B2411117
theorem B4065041 : Blo 750330 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B2852759 : Blo 750330 2852759 := bstep (se 1 (by rfl) ⟨2139569, by rfl⟩ : syracuseStep 2852759 = 4279139) B4279139
theorem B1902487 : Blo 750330 1902487 := bstep (se 1 (by rfl) ⟨1426865, by rfl⟩ : syracuseStep 1902487 = 2853731) B2853731
theorem B5802029 : Blo 750330 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B4294721 : Blo 750330 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B6195491 : Blo 750330 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B1804609 : Blo 750330 1804609 := bstep (se 2 (by rfl) ⟨676728, by rfl⟩ : syracuseStep 1804609 = 1353457) B1353457
theorem B1902923 : Blo 750330 1902923 := bstep (se 1 (by rfl) ⟨1427192, by rfl⟩ : syracuseStep 1902923 = 2854385) B2854385
theorem B952651 : Blo 750330 952651 := bstep (se 1 (by rfl) ⟨714488, by rfl⟩ : syracuseStep 952651 = 1428977) B1428977
theorem B2034013 : Blo 750330 2034013 := bstep (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) B762755
theorem B2853427 : Blo 750330 2853427 := bstep (se 1 (by rfl) ⟨2140070, by rfl⟩ : syracuseStep 2853427 = 4280141) B4280141
theorem B2034251 : Blo 750330 2034251 := bstep (se 1 (by rfl) ⟨1525688, by rfl⟩ : syracuseStep 2034251 = 3051377) B3051377
theorem B1903297 : Blo 750330 1903297 := bstep (se 2 (by rfl) ⟨713736, by rfl⟩ : syracuseStep 1903297 = 1427473) B1427473
theorem B3050243 : Blo 750330 3050243 := bstep (se 1 (by rfl) ⟨2287682, by rfl⟩ : syracuseStep 3050243 = 4575365) B4575365
theorem B3803921 : Blo 750330 3803921 := bstep (se 2 (by rfl) ⟨1426470, by rfl⟩ : syracuseStep 3803921 = 2852941) B2852941
theorem B15928163 : Blo 750330 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B1608599 : Blo 750330 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B3804083 : Blo 750330 3804083 := bstep (se 1 (by rfl) ⟨2853062, by rfl⟩ : syracuseStep 3804083 = 5706125) B5706125
theorem B3050585 : Blo 750330 3050585 := bstep (se 2 (by rfl) ⟨1143969, by rfl⟩ : syracuseStep 3050585 = 2287939) B2287939
theorem B6851735 : Blo 750330 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B1019083 : Blo 750330 1019083 := bstep (se 1 (by rfl) ⟨764312, by rfl⟩ : syracuseStep 1019083 = 1528625) B1528625
theorem B1903895 : Blo 750330 1903895 := bstep (se 1 (by rfl) ⟨1427921, by rfl⟩ : syracuseStep 1903895 = 2855843) B2855843
theorem B953623 : Blo 750330 953623 := bstep (se 1 (by rfl) ⟨715217, by rfl⟩ : syracuseStep 953623 = 1430435) B1430435
theorem B1019353 : Blo 750330 1019353 := bstep (se 2 (by rfl) ⟨382257, by rfl⟩ : syracuseStep 1019353 = 764515) B764515
theorem B1543745 : Blo 750330 1543745 := bstep (se 2 (by rfl) ⟨578904, by rfl⟩ : syracuseStep 1543745 = 1157809) B1157809
theorem B2035289 : Blo 750330 2035289 := bstep (se 2 (by rfl) ⟨763233, by rfl⟩ : syracuseStep 2035289 = 1526467) B1526467
theorem B3215027 : Blo 750330 3215027 := bstep (se 1 (by rfl) ⟨2411270, by rfl⟩ : syracuseStep 3215027 = 4822541) B4822541
theorem B2854673 : Blo 750330 2854673 := bstep (se 2 (by rfl) ⟨1070502, by rfl⟩ : syracuseStep 2854673 = 2141005) B2141005
theorem B4067117 : Blo 750330 4067117 := bstep (se 3 (by rfl) ⟨762584, by rfl⟩ : syracuseStep 4067117 = 1525169) B1525169
theorem B27430721 : Blo 750330 27430721 := bstep (se 2 (by rfl) ⟨10286520, by rfl⟩ : syracuseStep 27430721 = 20573041) B20573041
theorem B6426499 : Blo 750330 6426499 := bstep (se 1 (by rfl) ⟨4819874, by rfl⟩ : syracuseStep 6426499 = 9639749) B9639749
theorem B1609625 : Blo 750330 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B6098989 : Blo 750330 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B3608641 : Blo 750330 3608641 := bstep (se 2 (by rfl) ⟨1353240, by rfl⟩ : syracuseStep 3608641 = 2706481) B2706481
theorem B1904705 : Blo 750330 1904705 := bstep (se 2 (by rfl) ⟨714264, by rfl⟩ : syracuseStep 1904705 = 1428529) B1428529
theorem B954443 : Blo 750330 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B6951005 : Blo 750330 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B5411033 : Blo 750330 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B5411117 : Blo 750330 5411117 := bstep (se 3 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 5411117 = 2029169) B2029169
theorem B2232665 : Blo 750330 2232665 := bstep (se 2 (by rfl) ⟨837249, by rfl⟩ : syracuseStep 2232665 = 1674499) B1674499
theorem B1544599 : Blo 750330 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B2855371 : Blo 750330 2855371 := bstep (se 1 (by rfl) ⟨2141528, by rfl⟩ : syracuseStep 2855371 = 4283057) B4283057
theorem B1905241 : Blo 750330 1905241 := bstep (se 2 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 1905241 = 1428931) B1428931
theorem B2855645 : Blo 750330 2855645 := bstep (se 3 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 2855645 = 1070867) B1070867
theorem B6427457 : Blo 750330 6427457 := bstep (se 2 (by rfl) ⟨2410296, by rfl⟩ : syracuseStep 6427457 = 4820593) B4820593
theorem B3806027 : Blo 750330 3806027 := bstep (se 1 (by rfl) ⟨2854520, by rfl⟩ : syracuseStep 3806027 = 5709041) B5709041
theorem B5575601 : Blo 750330 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B1610675 : Blo 750330 1610675 := bstep (se 1 (by rfl) ⟨1208006, by rfl⟩ : syracuseStep 1610675 = 2416013) B2416013
theorem B1446913 : Blo 750330 1446913 := bstep (se 2 (by rfl) ⟨542592, by rfl⟩ : syracuseStep 1446913 = 1085185) B1085185
theorem B2856343 : Blo 750330 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B3216941 : Blo 750330 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B1906355 : Blo 750330 1906355 := bstep (se 1 (by rfl) ⟨1429766, by rfl⟩ : syracuseStep 1906355 = 2859533) B2859533
theorem B3217283 : Blo 750330 3217283 := bstep (se 1 (by rfl) ⟨2412962, by rfl⟩ : syracuseStep 3217283 = 4825925) B4825925
theorem B1906649 : Blo 750330 1906649 := bstep (se 2 (by rfl) ⟨714993, by rfl⟩ : syracuseStep 1906649 = 1429987) B1429987
theorem B4626497 : Blo 750330 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B2857133 : Blo 750330 2857133 := bstep (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) B1071425
theorem B1284427 : Blo 750330 1284427 := bstep (se 1 (by rfl) ⟨963320, by rfl⟩ : syracuseStep 1284427 = 1926641) B1926641
theorem B3807809 : Blo 750330 3807809 := bstep (se 2 (by rfl) ⟨1427928, by rfl⟩ : syracuseStep 3807809 = 2855857) B2855857
theorem B4332305 : Blo 750330 4332305 := bstep (se 2 (by rfl) ⟨1624614, by rfl⟩ : syracuseStep 4332305 = 3249229) B3249229
theorem B3251117 : Blo 750330 3251117 := bstep (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) B1219169
theorem B1448921 : Blo 750330 1448921 := bstep (se 2 (by rfl) ⟨543345, by rfl⟩ : syracuseStep 1448921 = 1086691) B1086691
theorem B3054685 : Blo 750330 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B4824157 : Blo 750330 4824157 := bstep (se 3 (by rfl) ⟨904529, by rfl⟩ : syracuseStep 4824157 = 1809059) B1809059
theorem B8559917 : Blo 750330 8559917 := bstep (se 3 (by rfl) ⟨1604984, by rfl⟩ : syracuseStep 8559917 = 3209969) B3209969
theorem B1809857 : Blo 750330 1809857 := bstep (se 2 (by rfl) ⟨678696, by rfl⟩ : syracuseStep 1809857 = 1357393) B1357393
theorem B2137565 : Blo 750330 2137565 := bstep (se 3 (by rfl) ⟨400793, by rfl⟩ : syracuseStep 2137565 = 801587) B801587
theorem B2858561 : Blo 750330 2858561 := bstep (se 2 (by rfl) ⟨1071960, by rfl⟩ : syracuseStep 2858561 = 2143921) B2143921
theorem B1908299 : Blo 750330 1908299 := bstep (se 1 (by rfl) ⟨1431224, by rfl⟩ : syracuseStep 1908299 = 2862449) B2862449
theorem B1449623 : Blo 750330 1449623 := bstep (se 1 (by rfl) ⟨1087217, by rfl⟩ : syracuseStep 1449623 = 2174435) B2174435
theorem B2137907 : Blo 750330 2137907 := bstep (se 1 (by rfl) ⟨1603430, by rfl⟩ : syracuseStep 2137907 = 3206861) B3206861
theorem B3219659 : Blo 750330 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B1286423 : Blo 750330 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B1286617 : Blo 750330 1286617 := bstep (se 2 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 1286617 = 964963) B964963
theorem B3809753 : Blo 750330 3809753 := bstep (se 2 (by rfl) ⟨1428657, by rfl⟩ : syracuseStep 3809753 = 2857315) B2857315
theorem B1909271 : Blo 750330 1909271 := bstep (se 1 (by rfl) ⟨1431953, by rfl⟩ : syracuseStep 1909271 = 2863907) B2863907
theorem B2860049 : Blo 750330 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B1287191 : Blo 750330 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B1647641 : Blo 750330 1647641 := bstep (se 2 (by rfl) ⟨617865, by rfl⟩ : syracuseStep 1647641 = 1235731) B1235731
theorem B3220631 : Blo 750330 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B2532545 : Blo 750330 2532545 := bstep (se 2 (by rfl) ⟨949704, by rfl⟩ : syracuseStep 2532545 = 1899409) B1899409
theorem B3974579 : Blo 750330 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B1713625 : Blo 750330 1713625 := bstep (se 2 (by rfl) ⟨642609, by rfl⟩ : syracuseStep 1713625 = 1285219) B1285219
theorem B2860505 : Blo 750330 2860505 := bstep (se 2 (by rfl) ⟨1072689, by rfl⟩ : syracuseStep 2860505 = 2145379) B2145379
theorem B4826641 : Blo 750330 4826641 := bstep (se 2 (by rfl) ⟨1809990, by rfl⟩ : syracuseStep 4826641 = 3619981) B3619981
theorem B2860717 : Blo 750330 2860717 := bstep (se 3 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 2860717 = 1072769) B1072769
theorem B2533085 : Blo 750330 2533085 := bstep (se 3 (by rfl) ⟨474953, by rfl⟩ : syracuseStep 2533085 = 949907) B949907
theorem B2827997 : Blo 750330 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B4171565 : Blo 750330 4171565 := bstep (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) B1564337
theorem B1812289 : Blo 750330 1812289 := bstep (se 2 (by rfl) ⟨679608, by rfl⟩ : syracuseStep 1812289 = 1359217) B1359217
theorem B1353601 : Blo 750330 1353601 := bstep (se 2 (by rfl) ⟨507600, by rfl⟩ : syracuseStep 1353601 = 1015201) B1015201
theorem B2861021 : Blo 750330 2861021 := bstep (se 3 (by rfl) ⟨536441, by rfl⟩ : syracuseStep 2861021 = 1072883) B1072883
theorem B3811373 : Blo 750330 3811373 := bstep (se 3 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 3811373 = 1429265) B1429265
theorem B2140253 : Blo 750330 2140253 := bstep (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) B802595
theorem B17410229 : Blo 750330 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B15444229 : Blo 750330 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B764203 : Blo 750330 764203 := bstep (se 1 (by rfl) ⟨573152, by rfl⟩ : syracuseStep 764203 = 1146305) B1146305
theorem B2140481 : Blo 750330 2140481 := bstep (se 2 (by rfl) ⟨802680, by rfl⟩ : syracuseStep 2140481 = 1605361) B1605361
theorem B1354163 : Blo 750330 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B2140823 : Blo 750330 2140823 := bstep (se 1 (by rfl) ⟨1605617, by rfl⟩ : syracuseStep 2140823 = 3211235) B3211235
theorem B2534219 : Blo 750330 2534219 := bstep (se 1 (by rfl) ⟨1900664, by rfl⟩ : syracuseStep 2534219 = 3801329) B3801329
theorem B1354625 : Blo 750330 1354625 := bstep (se 2 (by rfl) ⟨507984, by rfl⟩ : syracuseStep 1354625 = 1015969) B1015969
theorem B2534489 : Blo 750330 2534489 := bstep (se 2 (by rfl) ⟨950433, by rfl⟩ : syracuseStep 2534489 = 1900867) B1900867
theorem B1125515 : Blo 750330 1125515 := bstep (se 1 (by rfl) ⟨844136, by rfl⟩ : syracuseStep 1125515 = 1688273) B1688273
theorem B1125527 : Blo 750330 1125527 := bstep (se 1 (by rfl) ⟨844145, by rfl⟩ : syracuseStep 1125527 = 1688291) B1688291
theorem B7810199 : Blo 750330 7810199 := bstep (se 1 (by rfl) ⟨5857649, by rfl⟩ : syracuseStep 7810199 = 11715299) B11715299
theorem B1125593 : Blo 750330 1125593 := bstep (se 2 (by rfl) ⟨422097, by rfl⟩ : syracuseStep 1125593 = 844195) B844195
theorem B1125707 : Blo 750330 1125707 := bstep (se 1 (by rfl) ⟨844280, by rfl⟩ : syracuseStep 1125707 = 1688561) B1688561
theorem B1125719 : Blo 750330 1125719 := bstep (se 1 (by rfl) ⟨844289, by rfl⟩ : syracuseStep 1125719 = 1688579) B1688579
theorem B4566365 : Blo 750330 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B1125785 : Blo 750330 1125785 := bstep (se 2 (by rfl) ⟨422169, by rfl⟩ : syracuseStep 1125785 = 844339) B844339
theorem B1125899 : Blo 750330 1125899 := bstep (se 1 (by rfl) ⟨844424, by rfl⟩ : syracuseStep 1125899 = 1688849) B1688849
theorem B1125911 : Blo 750330 1125911 := bstep (se 1 (by rfl) ⟨844433, by rfl⟩ : syracuseStep 1125911 = 1688867) B1688867
theorem B1715735 : Blo 750330 1715735 := bstep (se 1 (by rfl) ⟨1286801, by rfl⟩ : syracuseStep 1715735 = 2573603) B2573603
theorem B1125977 : Blo 750330 1125977 := bstep (se 2 (by rfl) ⟨422241, by rfl⟩ : syracuseStep 1125977 = 844483) B844483
theorem B2404019 : Blo 750330 2404019 := bstep (se 1 (by rfl) ⟨1803014, by rfl⟩ : syracuseStep 2404019 = 3606029) B3606029
theorem B1126091 : Blo 750330 1126091 := bstep (se 1 (by rfl) ⟨844568, by rfl⟩ : syracuseStep 1126091 = 1689137) B1689137
theorem B1126103 : Blo 750330 1126103 := bstep (se 1 (by rfl) ⟨844577, by rfl⟩ : syracuseStep 1126103 = 1689155) B1689155
theorem B2535191 : Blo 750330 2535191 := bstep (se 1 (by rfl) ⟨1901393, by rfl⟩ : syracuseStep 2535191 = 3802787) B3802787
theorem B1126169 : Blo 750330 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B1126283 : Blo 750330 1126283 := bstep (se 1 (by rfl) ⟨844712, by rfl⟩ : syracuseStep 1126283 = 1689425) B1689425
theorem B1126295 : Blo 750330 1126295 := bstep (se 1 (by rfl) ⟨844721, by rfl⟩ : syracuseStep 1126295 = 1689443) B1689443
theorem B1355735 : Blo 750330 1355735 := bstep (se 1 (by rfl) ⟨1016801, by rfl⟩ : syracuseStep 1355735 = 2033603) B2033603
theorem B1126361 : Blo 750330 1126361 := bstep (se 2 (by rfl) ⟨422385, by rfl⟩ : syracuseStep 1126361 = 844771) B844771
theorem B1126475 : Blo 750330 1126475 := bstep (se 1 (by rfl) ⟨844856, by rfl⟩ : syracuseStep 1126475 = 1689713) B1689713
theorem B1126487 : Blo 750330 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B1126553 : Blo 750330 1126553 := bstep (se 2 (by rfl) ⟨422457, by rfl⟩ : syracuseStep 1126553 = 844915) B844915
theorem B1126667 : Blo 750330 1126667 := bstep (se 1 (by rfl) ⟨845000, by rfl⟩ : syracuseStep 1126667 = 1690001) B1690001
theorem B1126679 : Blo 750330 1126679 := bstep (se 1 (by rfl) ⟨845009, by rfl⟩ : syracuseStep 1126679 = 1690019) B1690019
theorem B2535731 : Blo 750330 2535731 := bstep (se 1 (by rfl) ⟨1901798, by rfl⟩ : syracuseStep 2535731 = 3803597) B3803597
theorem B1126745 : Blo 750330 1126745 := bstep (se 2 (by rfl) ⟨422529, by rfl⟩ : syracuseStep 1126745 = 845059) B845059
theorem B1126859 : Blo 750330 1126859 := bstep (se 1 (by rfl) ⟨845144, by rfl⟩ : syracuseStep 1126859 = 1690289) B1690289
theorem B1126871 : Blo 750330 1126871 := bstep (se 1 (by rfl) ⟨845153, by rfl⟩ : syracuseStep 1126871 = 1690307) B1690307
theorem B2863619 : Blo 750330 2863619 := bstep (se 1 (by rfl) ⟨2147714, by rfl⟩ : syracuseStep 2863619 = 4295429) B4295429
theorem B2863633 : Blo 750330 2863633 := bstep (se 2 (by rfl) ⟨1073862, by rfl⟩ : syracuseStep 2863633 = 2147725) B2147725
theorem B1126937 : Blo 750330 1126937 := bstep (se 2 (by rfl) ⟨422601, by rfl⟩ : syracuseStep 1126937 = 845203) B845203
theorem B6107683 : Blo 750330 6107683 := bstep (se 1 (by rfl) ⟨4580762, by rfl⟩ : syracuseStep 6107683 = 9161525) B9161525
theorem B2536001 : Blo 750330 2536001 := bstep (se 2 (by rfl) ⟨951000, by rfl⟩ : syracuseStep 2536001 = 1902001) B1902001
theorem B1127051 : Blo 750330 1127051 := bstep (se 1 (by rfl) ⟨845288, by rfl⟩ : syracuseStep 1127051 = 1690577) B1690577
theorem B1127063 : Blo 750330 1127063 := bstep (se 1 (by rfl) ⟨845297, by rfl⟩ : syracuseStep 1127063 = 1690595) B1690595
theorem B1127129 : Blo 750330 1127129 := bstep (se 2 (by rfl) ⟨422673, by rfl⟩ : syracuseStep 1127129 = 845347) B845347
theorem B2863937 : Blo 750330 2863937 := bstep (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) B2147953
theorem B1127243 : Blo 750330 1127243 := bstep (se 1 (by rfl) ⟨845432, by rfl⟩ : syracuseStep 1127243 = 1690865) B1690865
theorem B1127255 : Blo 750330 1127255 := bstep (se 1 (by rfl) ⟨845441, by rfl⟩ : syracuseStep 1127255 = 1690883) B1690883
theorem B1127321 : Blo 750330 1127321 := bstep (se 2 (by rfl) ⟨422745, by rfl⟩ : syracuseStep 1127321 = 845491) B845491
theorem B2143169 : Blo 750330 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B2175947 : Blo 750330 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1127435 : Blo 750330 1127435 := bstep (se 1 (by rfl) ⟨845576, by rfl⟩ : syracuseStep 1127435 = 1691153) B1691153
theorem B1127447 : Blo 750330 1127447 := bstep (se 1 (by rfl) ⟨845585, by rfl⟩ : syracuseStep 1127447 = 1691171) B1691171
theorem B1127513 : Blo 750330 1127513 := bstep (se 2 (by rfl) ⟨422817, by rfl⟩ : syracuseStep 1127513 = 845635) B845635
theorem B2536541 : Blo 750330 2536541 := bstep (se 3 (by rfl) ⟨475601, by rfl⟩ : syracuseStep 2536541 = 951203) B951203
theorem B1127627 : Blo 750330 1127627 := bstep (se 1 (by rfl) ⟨845720, by rfl⟩ : syracuseStep 1127627 = 1691441) B1691441
theorem B1127639 : Blo 750330 1127639 := bstep (se 1 (by rfl) ⟨845729, by rfl⟩ : syracuseStep 1127639 = 1691459) B1691459
theorem B1127705 : Blo 750330 1127705 := bstep (se 2 (by rfl) ⟨422889, by rfl⟩ : syracuseStep 1127705 = 845779) B845779
theorem B1127819 : Blo 750330 1127819 := bstep (se 1 (by rfl) ⟨845864, by rfl⟩ : syracuseStep 1127819 = 1691729) B1691729
theorem B4273559 : Blo 750330 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B1127831 : Blo 750330 1127831 := bstep (se 1 (by rfl) ⟨845873, by rfl⟩ : syracuseStep 1127831 = 1691747) B1691747
theorem B1127897 : Blo 750330 1127897 := bstep (se 2 (by rfl) ⟨422961, by rfl⟩ : syracuseStep 1127897 = 845923) B845923
theorem B2143705 : Blo 750330 2143705 := bstep (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) B1607779
theorem B1128011 : Blo 750330 1128011 := bstep (se 1 (by rfl) ⟨846008, by rfl⟩ : syracuseStep 1128011 = 1692017) B1692017
theorem B1128023 : Blo 750330 1128023 := bstep (se 1 (by rfl) ⟨846017, by rfl⟩ : syracuseStep 1128023 = 1692035) B1692035
theorem B4077149 : Blo 750330 4077149 := bstep (se 3 (by rfl) ⟨764465, by rfl⟩ : syracuseStep 4077149 = 1528931) B1528931
theorem B9647747 : Blo 750330 9647747 := bstep (se 1 (by rfl) ⟨7235810, by rfl⟩ : syracuseStep 9647747 = 14471621) B14471621
theorem B1128089 : Blo 750330 1128089 := bstep (se 2 (by rfl) ⟨423033, by rfl⟩ : syracuseStep 1128089 = 846067) B846067
theorem B1128203 : Blo 750330 1128203 := bstep (se 1 (by rfl) ⟨846152, by rfl⟩ : syracuseStep 1128203 = 1692305) B1692305
theorem B1128215 : Blo 750330 1128215 := bstep (se 1 (by rfl) ⟨846161, by rfl⟩ : syracuseStep 1128215 = 1692323) B1692323
theorem B1128281 : Blo 750330 1128281 := bstep (se 2 (by rfl) ⟨423105, by rfl⟩ : syracuseStep 1128281 = 846211) B846211
theorem B3815261 : Blo 750330 3815261 := bstep (se 3 (by rfl) ⟨715361, by rfl⟩ : syracuseStep 3815261 = 1430723) B1430723
theorem B16299953 : Blo 750330 16299953 := bstep (se 2 (by rfl) ⟨6112482, by rfl⟩ : syracuseStep 16299953 = 12224965) B12224965
theorem B1128395 : Blo 750330 1128395 := bstep (se 1 (by rfl) ⟨846296, by rfl⟩ : syracuseStep 1128395 = 1692593) B1692593
theorem B1128407 : Blo 750330 1128407 := bstep (se 1 (by rfl) ⟨846305, by rfl⟩ : syracuseStep 1128407 = 1692611) B1692611
theorem B1128473 : Blo 750330 1128473 := bstep (se 2 (by rfl) ⟨423177, by rfl⟩ : syracuseStep 1128473 = 846355) B846355
theorem B1128587 : Blo 750330 1128587 := bstep (se 1 (by rfl) ⟨846440, by rfl⟩ : syracuseStep 1128587 = 1692881) B1692881
theorem B1128599 : Blo 750330 1128599 := bstep (se 1 (by rfl) ⟨846449, by rfl⟩ : syracuseStep 1128599 = 1692899) B1692899
theorem B2537675 : Blo 750330 2537675 := bstep (se 1 (by rfl) ⟨1903256, by rfl⟩ : syracuseStep 2537675 = 3806513) B3806513
theorem B1128665 : Blo 750330 1128665 := bstep (se 2 (by rfl) ⟨423249, by rfl⟩ : syracuseStep 1128665 = 846499) B846499
theorem B1128779 : Blo 750330 1128779 := bstep (se 1 (by rfl) ⟨846584, by rfl⟩ : syracuseStep 1128779 = 1693169) B1693169
theorem B1128791 : Blo 750330 1128791 := bstep (se 1 (by rfl) ⟨846593, by rfl⟩ : syracuseStep 1128791 = 1693187) B1693187
theorem B1128857 : Blo 750330 1128857 := bstep (se 2 (by rfl) ⟨423321, by rfl⟩ : syracuseStep 1128857 = 846643) B846643
theorem B2537945 : Blo 750330 2537945 := bstep (se 2 (by rfl) ⟨951729, by rfl⟩ : syracuseStep 2537945 = 1903459) B1903459
theorem B1128971 : Blo 750330 1128971 := bstep (se 1 (by rfl) ⟨846728, by rfl⟩ : syracuseStep 1128971 = 1693457) B1693457
theorem B1128983 : Blo 750330 1128983 := bstep (se 1 (by rfl) ⟨846737, by rfl⟩ : syracuseStep 1128983 = 1693475) B1693475
theorem B4340299 : Blo 750330 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B1129049 : Blo 750330 1129049 := bstep (se 2 (by rfl) ⟨423393, by rfl⟩ : syracuseStep 1129049 = 846787) B846787
theorem B1129163 : Blo 750330 1129163 := bstep (se 1 (by rfl) ⟨846872, by rfl⟩ : syracuseStep 1129163 = 1693745) B1693745
theorem B1129175 : Blo 750330 1129175 := bstep (se 1 (by rfl) ⟨846881, by rfl⟩ : syracuseStep 1129175 = 1693763) B1693763
theorem B1129241 : Blo 750330 1129241 := bstep (se 2 (by rfl) ⟨423465, by rfl⟩ : syracuseStep 1129241 = 846931) B846931
theorem B15448897 : Blo 750330 15448897 := bstep (se 2 (by rfl) ⟨5793336, by rfl⟩ : syracuseStep 15448897 = 11586673) B11586673
theorem B4832075 : Blo 750330 4832075 := bstep (se 1 (by rfl) ⟨3624056, by rfl⟩ : syracuseStep 4832075 = 7248113) B7248113
theorem B1129355 : Blo 750330 1129355 := bstep (se 1 (by rfl) ⟨847016, by rfl⟩ : syracuseStep 1129355 = 1694033) B1694033
theorem B1129367 : Blo 750330 1129367 := bstep (se 1 (by rfl) ⟨847025, by rfl⟩ : syracuseStep 1129367 = 1694051) B1694051
theorem B1129433 : Blo 750330 1129433 := bstep (se 2 (by rfl) ⟨423537, by rfl⟩ : syracuseStep 1129433 = 847075) B847075
theorem B1424459 : Blo 750330 1424459 := bstep (se 1 (by rfl) ⟨1068344, by rfl⟩ : syracuseStep 1424459 = 2136689) B2136689
theorem B1129547 : Blo 750330 1129547 := bstep (se 1 (by rfl) ⟨847160, by rfl⟩ : syracuseStep 1129547 = 1694321) B1694321
theorem B1129559 : Blo 750330 1129559 := bstep (se 1 (by rfl) ⟨847169, by rfl⟩ : syracuseStep 1129559 = 1694339) B1694339
theorem B6437981 : Blo 750330 6437981 := bstep (se 3 (by rfl) ⟨1207121, by rfl⟩ : syracuseStep 6437981 = 2414243) B2414243
theorem B2538647 : Blo 750330 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B1129625 : Blo 750330 1129625 := bstep (se 2 (by rfl) ⟨423609, by rfl⟩ : syracuseStep 1129625 = 847219) B847219
theorem B1424641 : Blo 750330 1424641 := bstep (se 2 (by rfl) ⟨534240, by rfl⟩ : syracuseStep 1424641 = 1068481) B1068481
theorem B1129739 : Blo 750330 1129739 := bstep (se 1 (by rfl) ⟨847304, by rfl⟩ : syracuseStep 1129739 = 1694609) B1694609
theorem B1129751 : Blo 750330 1129751 := bstep (se 1 (by rfl) ⟨847313, by rfl⟩ : syracuseStep 1129751 = 1694627) B1694627
theorem B1129817 : Blo 750330 1129817 := bstep (se 2 (by rfl) ⟨423681, by rfl⟩ : syracuseStep 1129817 = 847363) B847363
theorem B2145629 : Blo 750330 2145629 := bstep (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) B804611
theorem B1129931 : Blo 750330 1129931 := bstep (se 1 (by rfl) ⟨847448, by rfl⟩ : syracuseStep 1129931 = 1694897) B1694897
theorem B1129943 : Blo 750330 1129943 := bstep (se 1 (by rfl) ⟨847457, by rfl⟩ : syracuseStep 1129943 = 1694915) B1694915
theorem B1130009 : Blo 750330 1130009 := bstep (se 2 (by rfl) ⟨423753, by rfl⟩ : syracuseStep 1130009 = 847507) B847507
theorem B1392257 : Blo 750330 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B1130123 : Blo 750330 1130123 := bstep (se 1 (by rfl) ⟨847592, by rfl⟩ : syracuseStep 1130123 = 1695185) B1695185
theorem B1130135 : Blo 750330 1130135 := bstep (se 1 (by rfl) ⟨847601, by rfl⟩ : syracuseStep 1130135 = 1695203) B1695203
theorem B2539187 : Blo 750330 2539187 := bstep (se 1 (by rfl) ⟨1904390, by rfl⟩ : syracuseStep 2539187 = 3808781) B3808781
theorem B1425089 : Blo 750330 1425089 := bstep (se 2 (by rfl) ⟨534408, by rfl⟩ : syracuseStep 1425089 = 1068817) B1068817
theorem B1130201 : Blo 750330 1130201 := bstep (se 2 (by rfl) ⟨423825, by rfl⟩ : syracuseStep 1130201 = 847651) B847651
theorem B1130315 : Blo 750330 1130315 := bstep (se 1 (by rfl) ⟨847736, by rfl⟩ : syracuseStep 1130315 = 1695473) B1695473
theorem B1130327 : Blo 750330 1130327 := bstep (se 1 (by rfl) ⟨847745, by rfl⟩ : syracuseStep 1130327 = 1695491) B1695491
theorem B10305397 : Blo 750330 10305397 := bstep (se 5 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 10305397 = 966131) B966131
theorem B3817367 : Blo 750330 3817367 := bstep (se 1 (by rfl) ⟨2863025, by rfl⟩ : syracuseStep 3817367 = 5726051) B5726051
theorem B1130393 : Blo 750330 1130393 := bstep (se 2 (by rfl) ⟨423897, by rfl⟩ : syracuseStep 1130393 = 847795) B847795
theorem B2539457 : Blo 750330 2539457 := bstep (se 2 (by rfl) ⟨952296, by rfl⟩ : syracuseStep 2539457 = 1904593) B1904593
theorem B1130507 : Blo 750330 1130507 := bstep (se 1 (by rfl) ⟨847880, by rfl⟩ : syracuseStep 1130507 = 1695761) B1695761
theorem B1425431 : Blo 750330 1425431 := bstep (se 1 (by rfl) ⟨1069073, by rfl⟩ : syracuseStep 1425431 = 2138147) B2138147
theorem B1130519 : Blo 750330 1130519 := bstep (se 1 (by rfl) ⟨847889, by rfl⟩ : syracuseStep 1130519 = 1695779) B1695779
theorem B1130585 : Blo 750330 1130585 := bstep (se 2 (by rfl) ⟨423969, by rfl⟩ : syracuseStep 1130585 = 847939) B847939
theorem B1130699 : Blo 750330 1130699 := bstep (se 1 (by rfl) ⟨848024, by rfl⟩ : syracuseStep 1130699 = 1696049) B1696049
theorem B1130711 : Blo 750330 1130711 := bstep (se 1 (by rfl) ⟨848033, by rfl⟩ : syracuseStep 1130711 = 1696067) B1696067
theorem B6111449 : Blo 750330 6111449 := bstep (se 2 (by rfl) ⟨2291793, by rfl⟩ : syracuseStep 6111449 = 4583587) B4583587
theorem B1130777 : Blo 750330 1130777 := bstep (se 2 (by rfl) ⟨424041, by rfl⟩ : syracuseStep 1130777 = 848083) B848083
theorem B1130891 : Blo 750330 1130891 := bstep (se 1 (by rfl) ⟨848168, by rfl⟩ : syracuseStep 1130891 = 1696337) B1696337
theorem B1130903 : Blo 750330 1130903 := bstep (se 1 (by rfl) ⟨848177, by rfl⟩ : syracuseStep 1130903 = 1696355) B1696355
theorem B803287 : Blo 750330 803287 := bstep (se 1 (by rfl) ⟨602465, by rfl⟩ : syracuseStep 803287 = 1204931) B1204931
theorem B1130969 : Blo 750330 1130969 := bstep (se 2 (by rfl) ⟨424113, by rfl⟩ : syracuseStep 1130969 = 848227) B848227
theorem B2539997 : Blo 750330 2539997 := bstep (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) B952499
theorem B1131083 : Blo 750330 1131083 := bstep (se 1 (by rfl) ⟨848312, by rfl⟩ : syracuseStep 1131083 = 1696625) B1696625
theorem B1131095 : Blo 750330 1131095 := bstep (se 1 (by rfl) ⟨848321, by rfl⟩ : syracuseStep 1131095 = 1696643) B1696643
theorem B1131161 : Blo 750330 1131161 := bstep (se 2 (by rfl) ⟨424185, by rfl⟩ : syracuseStep 1131161 = 848371) B848371
theorem B1426099 : Blo 750330 1426099 := bstep (se 1 (by rfl) ⟨1069574, by rfl⟩ : syracuseStep 1426099 = 2139149) B2139149
theorem B1131275 : Blo 750330 1131275 := bstep (se 1 (by rfl) ⟨848456, by rfl⟩ : syracuseStep 1131275 = 1696913) B1696913
theorem B1131287 : Blo 750330 1131287 := bstep (se 1 (by rfl) ⟨848465, by rfl⟩ : syracuseStep 1131287 = 1696931) B1696931
theorem B1688345 : Blo 750330 1688345 := bstep (se 2 (by rfl) ⟨633129, by rfl⟩ : syracuseStep 1688345 = 1266259) B1266259
theorem B1131353 : Blo 750330 1131353 := bstep (se 2 (by rfl) ⟨424257, by rfl⟩ : syracuseStep 1131353 = 848515) B848515
theorem B1688435 : Blo 750330 1688435 := bstep (se 1 (by rfl) ⟨1266326, by rfl⟩ : syracuseStep 1688435 = 2532653) B2532653
theorem B1688471 : Blo 750330 1688471 := bstep (se 1 (by rfl) ⟨1266353, by rfl⟩ : syracuseStep 1688471 = 2532707) B2532707
theorem B1131467 : Blo 750330 1131467 := bstep (se 1 (by rfl) ⟨848600, by rfl⟩ : syracuseStep 1131467 = 1697201) B1697201
theorem B1131479 : Blo 750330 1131479 := bstep (se 1 (by rfl) ⟨848609, by rfl⟩ : syracuseStep 1131479 = 1697219) B1697219
theorem B3621905 : Blo 750330 3621905 := bstep (se 2 (by rfl) ⟨1358214, by rfl⟩ : syracuseStep 3621905 = 2716429) B2716429
theorem B1688651 : Blo 750330 1688651 := bstep (se 1 (by rfl) ⟨1266488, by rfl⟩ : syracuseStep 1688651 = 2532977) B2532977
theorem B1426547 : Blo 750330 1426547 := bstep (se 1 (by rfl) ⟨1069910, by rfl⟩ : syracuseStep 1426547 = 2139821) B2139821
theorem B1688705 : Blo 750330 1688705 := bstep (se 2 (by rfl) ⟨633264, by rfl⟩ : syracuseStep 1688705 = 1266529) B1266529
theorem B1426585 : Blo 750330 1426585 := bstep (se 2 (by rfl) ⟨534969, by rfl⟩ : syracuseStep 1426585 = 1069939) B1069939
theorem B1688921 : Blo 750330 1688921 := bstep (se 2 (by rfl) ⟨633345, by rfl⟩ : syracuseStep 1688921 = 1266691) B1266691
theorem B1689011 : Blo 750330 1689011 := bstep (se 1 (by rfl) ⟨1266758, by rfl⟩ : syracuseStep 1689011 = 2533517) B2533517
theorem B1689047 : Blo 750330 1689047 := bstep (se 1 (by rfl) ⟨1266785, by rfl⟩ : syracuseStep 1689047 = 2533571) B2533571
theorem B2541131 : Blo 750330 2541131 := bstep (se 1 (by rfl) ⟨1905848, by rfl⟩ : syracuseStep 2541131 = 3811697) B3811697
theorem B1427033 : Blo 750330 1427033 := bstep (se 2 (by rfl) ⟨535137, by rfl⟩ : syracuseStep 1427033 = 1070275) B1070275
theorem B6440579 : Blo 750330 6440579 := bstep (se 1 (by rfl) ⟨4830434, by rfl⟩ : syracuseStep 6440579 = 9660869) B9660869
theorem B1689227 : Blo 750330 1689227 := bstep (se 1 (by rfl) ⟨1266920, by rfl⟩ : syracuseStep 1689227 = 2533841) B2533841
theorem B2705069 : Blo 750330 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B1689281 : Blo 750330 1689281 := bstep (se 2 (by rfl) ⟨633480, by rfl⟩ : syracuseStep 1689281 = 1266961) B1266961
theorem B2541401 : Blo 750330 2541401 := bstep (se 2 (by rfl) ⟨953025, by rfl⟩ : syracuseStep 2541401 = 1906051) B1906051
theorem B1689497 : Blo 750330 1689497 := bstep (se 2 (by rfl) ⟨633561, by rfl⟩ : syracuseStep 1689497 = 1267123) B1267123
theorem B1689587 : Blo 750330 1689587 := bstep (se 1 (by rfl) ⟨1267190, by rfl⟩ : syracuseStep 1689587 = 2534381) B2534381
theorem B1689623 : Blo 750330 1689623 := bstep (se 1 (by rfl) ⟨1267217, by rfl⟩ : syracuseStep 1689623 = 2534435) B2534435
theorem B4278365 : Blo 750330 4278365 := bstep (se 3 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 4278365 = 1604387) B1604387
theorem B804983 : Blo 750330 804983 := bstep (se 1 (by rfl) ⟨603737, by rfl⟩ : syracuseStep 804983 = 1207475) B1207475
theorem B1689803 : Blo 750330 1689803 := bstep (se 1 (by rfl) ⟨1267352, by rfl⟩ : syracuseStep 1689803 = 2534705) B2534705
theorem B1689857 : Blo 750330 1689857 := bstep (se 2 (by rfl) ⟨633696, by rfl⟩ : syracuseStep 1689857 = 1267393) B1267393
theorem B1427777 : Blo 750330 1427777 := bstep (se 2 (by rfl) ⟨535416, by rfl⟩ : syracuseStep 1427777 = 1070833) B1070833
theorem B1690073 : Blo 750330 1690073 := bstep (se 2 (by rfl) ⟨633777, by rfl⟩ : syracuseStep 1690073 = 1267555) B1267555
theorem B2542103 : Blo 750330 2542103 := bstep (se 1 (by rfl) ⟨1906577, by rfl⟩ : syracuseStep 2542103 = 3813155) B3813155
theorem B1690163 : Blo 750330 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B1428043 : Blo 750330 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B1690199 : Blo 750330 1690199 := bstep (se 1 (by rfl) ⟨1267649, by rfl⟩ : syracuseStep 1690199 = 2535299) B2535299
theorem B3426961 : Blo 750330 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B1690379 : Blo 750330 1690379 := bstep (se 1 (by rfl) ⟨1267784, by rfl⟩ : syracuseStep 1690379 = 2535569) B2535569
theorem B5425937 : Blo 750330 5425937 := bstep (se 2 (by rfl) ⟨2034726, by rfl⟩ : syracuseStep 5425937 = 4069453) B4069453
theorem B772907 : Blo 750330 772907 := bstep (se 1 (by rfl) ⟨579680, by rfl⟩ : syracuseStep 772907 = 1159361) B1159361
theorem B1690433 : Blo 750330 1690433 := bstep (se 2 (by rfl) ⟨633912, by rfl⟩ : syracuseStep 1690433 = 1267825) B1267825
theorem B1428491 : Blo 750330 1428491 := bstep (se 1 (by rfl) ⟨1071368, by rfl⟩ : syracuseStep 1428491 = 2142737) B2142737
theorem B1690649 : Blo 750330 1690649 := bstep (se 2 (by rfl) ⟨633993, by rfl⟩ : syracuseStep 1690649 = 1267987) B1267987
theorem B2542643 : Blo 750330 2542643 := bstep (se 1 (by rfl) ⟨1906982, by rfl⟩ : syracuseStep 2542643 = 3813965) B3813965
theorem B1690739 : Blo 750330 1690739 := bstep (se 1 (by rfl) ⟨1268054, by rfl⟩ : syracuseStep 1690739 = 2536109) B2536109
theorem B1690775 : Blo 750330 1690775 := bstep (se 1 (by rfl) ⟨1268081, by rfl⟩ : syracuseStep 1690775 = 2536163) B2536163
theorem B1428673 : Blo 750330 1428673 := bstep (se 2 (by rfl) ⟨535752, by rfl⟩ : syracuseStep 1428673 = 1071505) B1071505
theorem B2542913 : Blo 750330 2542913 := bstep (se 2 (by rfl) ⟨953592, by rfl⟩ : syracuseStep 2542913 = 1907185) B1907185
theorem B1690955 : Blo 750330 1690955 := bstep (se 1 (by rfl) ⟨1268216, by rfl⟩ : syracuseStep 1690955 = 2536433) B2536433
theorem B1691009 : Blo 750330 1691009 := bstep (se 2 (by rfl) ⟨634128, by rfl⟩ : syracuseStep 1691009 = 1268257) B1268257
theorem B1429015 : Blo 750330 1429015 := bstep (se 1 (by rfl) ⟨1071761, by rfl⟩ : syracuseStep 1429015 = 2143523) B2143523
theorem B1691225 : Blo 750330 1691225 := bstep (se 2 (by rfl) ⟨634209, by rfl⟩ : syracuseStep 1691225 = 1268419) B1268419
theorem B1691315 : Blo 750330 1691315 := bstep (se 1 (by rfl) ⟨1268486, by rfl⟩ : syracuseStep 1691315 = 2536973) B2536973
theorem B1691351 : Blo 750330 1691351 := bstep (se 1 (by rfl) ⟨1268513, by rfl⟩ : syracuseStep 1691351 = 2537027) B2537027
theorem B1429235 : Blo 750330 1429235 := bstep (se 1 (by rfl) ⟨1071926, by rfl⟩ : syracuseStep 1429235 = 2143853) B2143853
theorem B2543453 : Blo 750330 2543453 := bstep (se 3 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 2543453 = 953795) B953795
theorem B1691531 : Blo 750330 1691531 := bstep (se 1 (by rfl) ⟨1268648, by rfl⟩ : syracuseStep 1691531 = 2537297) B2537297
theorem B1691585 : Blo 750330 1691585 := bstep (se 2 (by rfl) ⟨634344, by rfl⟩ : syracuseStep 1691585 = 1268689) B1268689
theorem B1429463 : Blo 750330 1429463 := bstep (se 1 (by rfl) ⟨1072097, by rfl⟩ : syracuseStep 1429463 = 2144195) B2144195
theorem B905303 : Blo 750330 905303 := bstep (se 1 (by rfl) ⟨678977, by rfl⟩ : syracuseStep 905303 = 1357955) B1357955
theorem B1527959 : Blo 750330 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B1691801 : Blo 750330 1691801 := bstep (se 2 (by rfl) ⟨634425, by rfl⟩ : syracuseStep 1691801 = 1268851) B1268851
theorem B1429721 : Blo 750330 1429721 := bstep (se 2 (by rfl) ⟨536145, by rfl⟩ : syracuseStep 1429721 = 1072291) B1072291
theorem B1691891 : Blo 750330 1691891 := bstep (se 1 (by rfl) ⟨1268918, by rfl⟩ : syracuseStep 1691891 = 2537837) B2537837
theorem B1691927 : Blo 750330 1691927 := bstep (se 1 (by rfl) ⟨1268945, by rfl⟩ : syracuseStep 1691927 = 2537891) B2537891
theorem B1692107 : Blo 750330 1692107 := bstep (se 1 (by rfl) ⟨1269080, by rfl⟩ : syracuseStep 1692107 = 2538161) B2538161
theorem B1692161 : Blo 750330 1692161 := bstep (se 2 (by rfl) ⟨634560, by rfl⟩ : syracuseStep 1692161 = 1269121) B1269121
theorem B4280849 : Blo 750330 4280849 := bstep (se 2 (by rfl) ⟨1605318, by rfl⟩ : syracuseStep 4280849 = 3210637) B3210637
theorem B12833315 : Blo 750330 12833315 := bstep (se 1 (by rfl) ⟨9624986, by rfl⟩ : syracuseStep 12833315 = 19249973) B19249973
theorem B1430131 : Blo 750330 1430131 := bstep (se 1 (by rfl) ⟨1072598, by rfl⟩ : syracuseStep 1430131 = 2145197) B2145197
theorem B9163469 : Blo 750330 9163469 := bstep (se 3 (by rfl) ⟨1718150, by rfl⟩ : syracuseStep 9163469 = 3436301) B3436301
theorem B1692377 : Blo 750330 1692377 := bstep (se 2 (by rfl) ⟨634641, by rfl⟩ : syracuseStep 1692377 = 1269283) B1269283
theorem B5788421 : Blo 750330 5788421 := bstep (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) B1085329
theorem B905995 : Blo 750330 905995 := bstep (se 1 (by rfl) ⟨679496, by rfl⟩ : syracuseStep 905995 = 1358993) B1358993
theorem B1266455 : Blo 750330 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B1692467 : Blo 750330 1692467 := bstep (se 1 (by rfl) ⟨1269350, by rfl⟩ : syracuseStep 1692467 = 2538701) B2538701
theorem B1692503 : Blo 750330 1692503 := bstep (se 1 (by rfl) ⟨1269377, by rfl⟩ : syracuseStep 1692503 = 2538755) B2538755
theorem B1266583 : Blo 750330 1266583 := bstep (se 1 (by rfl) ⟨949937, by rfl⟩ : syracuseStep 1266583 = 1899875) B1899875
theorem B2544587 : Blo 750330 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B1692683 : Blo 750330 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B1692737 : Blo 750330 1692737 := bstep (se 2 (by rfl) ⟨634776, by rfl⟩ : syracuseStep 1692737 = 1269553) B1269553
theorem B1070167 : Blo 750330 1070167 := bstep (se 1 (by rfl) ⟨802625, by rfl⟩ : syracuseStep 1070167 = 1605251) B1605251
theorem B1430617 : Blo 750330 1430617 := bstep (se 2 (by rfl) ⟨536481, by rfl⟩ : syracuseStep 1430617 = 1072963) B1072963
theorem B2544857 : Blo 750330 2544857 := bstep (se 2 (by rfl) ⟨954321, by rfl⟩ : syracuseStep 2544857 = 1908643) B1908643
theorem B1692953 : Blo 750330 1692953 := bstep (se 2 (by rfl) ⟨634857, by rfl⟩ : syracuseStep 1692953 = 1269715) B1269715
theorem B1693043 : Blo 750330 1693043 := bstep (se 1 (by rfl) ⟨1269782, by rfl⟩ : syracuseStep 1693043 = 2539565) B2539565
theorem B1693079 : Blo 750330 1693079 := bstep (se 1 (by rfl) ⟨1269809, by rfl⟩ : syracuseStep 1693079 = 2539619) B2539619
theorem B6411737 : Blo 750330 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B1267211 : Blo 750330 1267211 := bstep (se 1 (by rfl) ⟨950408, by rfl⟩ : syracuseStep 1267211 = 1900817) B1900817
theorem B5133869 : Blo 750330 5133869 := bstep (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) B1925201
theorem B1693259 : Blo 750330 1693259 := bstep (se 1 (by rfl) ⟨1269944, by rfl⟩ : syracuseStep 1693259 = 2539889) B2539889
theorem B1693313 : Blo 750330 1693313 := bstep (se 2 (by rfl) ⟨634992, by rfl⟩ : syracuseStep 1693313 = 1269985) B1269985
theorem B1267339 : Blo 750330 1267339 := bstep (se 1 (by rfl) ⟨950504, by rfl⟩ : syracuseStep 1267339 = 1901009) B1901009
theorem B1431179 : Blo 750330 1431179 := bstep (se 1 (by rfl) ⟨1073384, by rfl⟩ : syracuseStep 1431179 = 2146769) B2146769
theorem B1201945 : Blo 750330 1201945 := bstep (se 2 (by rfl) ⟨450729, by rfl⟩ : syracuseStep 1201945 = 901459) B901459
theorem B1267481 : Blo 750330 1267481 := bstep (se 2 (by rfl) ⟨475305, by rfl⟩ : syracuseStep 1267481 = 950611) B950611
theorem B1431361 : Blo 750330 1431361 := bstep (se 2 (by rfl) ⟨536760, by rfl⟩ : syracuseStep 1431361 = 1073521) B1073521
theorem B1693529 : Blo 750330 1693529 := bstep (se 2 (by rfl) ⟨635073, by rfl⟩ : syracuseStep 1693529 = 1270147) B1270147
theorem B2545559 : Blo 750330 2545559 := bstep (se 1 (by rfl) ⟨1909169, by rfl⟩ : syracuseStep 2545559 = 3818339) B3818339
theorem B1267609 : Blo 750330 1267609 := bstep (se 2 (by rfl) ⟨475353, by rfl⟩ : syracuseStep 1267609 = 950707) B950707
theorem B1693619 : Blo 750330 1693619 := bstep (se 1 (by rfl) ⟨1270214, by rfl⟩ : syracuseStep 1693619 = 2540429) B2540429
theorem B2414539 : Blo 750330 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B1693655 : Blo 750330 1693655 := bstep (se 1 (by rfl) ⟨1270241, by rfl⟩ : syracuseStep 1693655 = 2540483) B2540483
theorem B2414681 : Blo 750330 2414681 := bstep (se 2 (by rfl) ⟨905505, by rfl⟩ : syracuseStep 2414681 = 1811011) B1811011
theorem B1693835 : Blo 750330 1693835 := bstep (se 1 (by rfl) ⟨1270376, by rfl⟩ : syracuseStep 1693835 = 2540753) B2540753
theorem B43341965 : Blo 750330 43341965 := bstep (se 3 (by rfl) ⟨8126618, by rfl⟩ : syracuseStep 43341965 = 16253237) B16253237
theorem B2709683 : Blo 750330 2709683 := bstep (se 1 (by rfl) ⟨2032262, by rfl⟩ : syracuseStep 2709683 = 4064525) B4064525
theorem B1693889 : Blo 750330 1693889 := bstep (se 2 (by rfl) ⟨635208, by rfl⟩ : syracuseStep 1693889 = 1270417) B1270417
theorem B1694105 : Blo 750330 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B5724593 : Blo 750330 5724593 := bstep (se 2 (by rfl) ⟨2146722, by rfl⟩ : syracuseStep 5724593 = 4293445) B4293445
theorem B1268183 : Blo 750330 1268183 := bstep (se 1 (by rfl) ⟨951137, by rfl⟩ : syracuseStep 1268183 = 1902275) B1902275
theorem B1694195 : Blo 750330 1694195 := bstep (se 1 (by rfl) ⟨1270646, by rfl⟩ : syracuseStep 1694195 = 2541293) B2541293
theorem B14637581 : Blo 750330 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B1694231 : Blo 750330 1694231 := bstep (se 1 (by rfl) ⟨1270673, by rfl⟩ : syracuseStep 1694231 = 2541347) B2541347
theorem B1268311 : Blo 750330 1268311 := bstep (se 1 (by rfl) ⟨951233, by rfl⟩ : syracuseStep 1268311 = 1902467) B1902467
theorem B1694411 : Blo 750330 1694411 := bstep (se 1 (by rfl) ⟨1270808, by rfl⟩ : syracuseStep 1694411 = 2541617) B2541617
theorem B1694465 : Blo 750330 1694465 := bstep (se 2 (by rfl) ⟨635424, by rfl⟩ : syracuseStep 1694465 = 1270849) B1270849
theorem B2710361 : Blo 750330 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B5725079 : Blo 750330 5725079 := bstep (se 1 (by rfl) ⟨4293809, by rfl⟩ : syracuseStep 5725079 = 8587619) B8587619
theorem B1694681 : Blo 750330 1694681 := bstep (se 2 (by rfl) ⟨635505, by rfl⟩ : syracuseStep 1694681 = 1271011) B1271011
theorem B1694771 : Blo 750330 1694771 := bstep (se 1 (by rfl) ⟨1271078, by rfl⟩ : syracuseStep 1694771 = 2542157) B2542157
theorem B6413377 : Blo 750330 6413377 := bstep (se 2 (by rfl) ⟨2405016, by rfl⟩ : syracuseStep 6413377 = 4810033) B4810033
theorem B1694807 : Blo 750330 1694807 := bstep (se 1 (by rfl) ⟨1271105, by rfl⟩ : syracuseStep 1694807 = 2542211) B2542211
theorem B1072217 : Blo 750330 1072217 := bstep (se 2 (by rfl) ⟨402081, by rfl⟩ : syracuseStep 1072217 = 804163) B804163
theorem B5856407 : Blo 750330 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B1268939 : Blo 750330 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1694987 : Blo 750330 1694987 := bstep (se 1 (by rfl) ⟨1271240, by rfl⟩ : syracuseStep 1694987 = 2542481) B2542481
theorem B1695041 : Blo 750330 1695041 := bstep (se 2 (by rfl) ⟨635640, by rfl⟩ : syracuseStep 1695041 = 1271281) B1271281
theorem B1269067 : Blo 750330 1269067 := bstep (se 1 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 1269067 = 1903601) B1903601
theorem B1269209 : Blo 750330 1269209 := bstep (se 2 (by rfl) ⟨475953, by rfl⟩ : syracuseStep 1269209 = 951907) B951907
theorem B1695257 : Blo 750330 1695257 := bstep (se 2 (by rfl) ⟨635721, by rfl⟩ : syracuseStep 1695257 = 1271443) B1271443
theorem B1269337 : Blo 750330 1269337 := bstep (se 2 (by rfl) ⟨476001, by rfl⟩ : syracuseStep 1269337 = 952003) B952003
theorem B1695347 : Blo 750330 1695347 := bstep (se 1 (by rfl) ⟨1271510, by rfl⟩ : syracuseStep 1695347 = 2543021) B2543021
theorem B1695383 : Blo 750330 1695383 := bstep (se 1 (by rfl) ⟨1271537, by rfl⟩ : syracuseStep 1695383 = 2543075) B2543075
theorem B1072855 : Blo 750330 1072855 := bstep (se 1 (by rfl) ⟨804641, by rfl⟩ : syracuseStep 1072855 = 1609283) B1609283
theorem B1695563 : Blo 750330 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B1695617 : Blo 750330 1695617 := bstep (se 2 (by rfl) ⟨635856, by rfl⟩ : syracuseStep 1695617 = 1271713) B1271713
theorem B24404003 : Blo 750330 24404003 := bstep (se 1 (by rfl) ⟨18303002, by rfl⟩ : syracuseStep 24404003 = 36606005) B36606005
theorem B2711641 : Blo 750330 2711641 := bstep (se 2 (by rfl) ⟨1016865, by rfl⟩ : syracuseStep 2711641 = 2033731) B2033731
theorem B1695833 : Blo 750330 1695833 := bstep (se 2 (by rfl) ⟨635937, by rfl⟩ : syracuseStep 1695833 = 1271875) B1271875
theorem B1269911 : Blo 750330 1269911 := bstep (se 1 (by rfl) ⟨952433, by rfl⟩ : syracuseStep 1269911 = 1904867) B1904867
theorem B8151191 : Blo 750330 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B1695923 : Blo 750330 1695923 := bstep (se 1 (by rfl) ⟨1271942, by rfl⟩ : syracuseStep 1695923 = 2543885) B2543885
theorem B1695959 : Blo 750330 1695959 := bstep (se 1 (by rfl) ⟨1271969, by rfl⟩ : syracuseStep 1695959 = 2543939) B2543939
theorem B1270039 : Blo 750330 1270039 := bstep (se 1 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 1270039 = 1905059) B1905059
theorem B2711873 : Blo 750330 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B1696139 : Blo 750330 1696139 := bstep (se 1 (by rfl) ⟨1272104, by rfl⟩ : syracuseStep 1696139 = 2544209) B2544209
theorem B1696193 : Blo 750330 1696193 := bstep (se 2 (by rfl) ⟨636072, by rfl⟩ : syracuseStep 1696193 = 1272145) B1272145
theorem B844267 : Blo 750330 844267 := bstep (se 1 (by rfl) ⟨633200, by rfl⟩ : syracuseStep 844267 = 1266401) B1266401
theorem B1073675 : Blo 750330 1073675 := bstep (se 1 (by rfl) ⟨805256, by rfl⟩ : syracuseStep 1073675 = 1610513) B1610513
theorem B844375 : Blo 750330 844375 := bstep (se 1 (by rfl) ⟨633281, by rfl⟩ : syracuseStep 844375 = 1266563) B1266563
theorem B1696409 : Blo 750330 1696409 := bstep (se 2 (by rfl) ⟨636153, by rfl⟩ : syracuseStep 1696409 = 1272307) B1272307
theorem B4809395 : Blo 750330 4809395 := bstep (se 1 (by rfl) ⟨3607046, by rfl⟩ : syracuseStep 4809395 = 7214093) B7214093
theorem B1860275 : Blo 750330 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B1630937 : Blo 750330 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B1696499 : Blo 750330 1696499 := bstep (se 1 (by rfl) ⟨1272374, by rfl⟩ : syracuseStep 1696499 = 2544749) B2544749
theorem B844555 : Blo 750330 844555 := bstep (se 1 (by rfl) ⟨633416, by rfl⟩ : syracuseStep 844555 = 1266833) B1266833
theorem B1696535 : Blo 750330 1696535 := bstep (se 1 (by rfl) ⟨1272401, by rfl⟩ : syracuseStep 1696535 = 2544803) B2544803
theorem B844663 : Blo 750330 844663 := bstep (se 1 (by rfl) ⟨633497, by rfl⟩ : syracuseStep 844663 = 1266995) B1266995
theorem B1270667 : Blo 750330 1270667 := bstep (se 1 (by rfl) ⟨953000, by rfl⟩ : syracuseStep 1270667 = 1906001) B1906001
theorem B1696715 : Blo 750330 1696715 := bstep (se 1 (by rfl) ⟨1272536, by rfl⟩ : syracuseStep 1696715 = 2545073) B2545073
theorem B1696769 : Blo 750330 1696769 := bstep (se 2 (by rfl) ⟨636288, by rfl⟩ : syracuseStep 1696769 = 1272577) B1272577
theorem B1270795 : Blo 750330 1270795 := bstep (se 1 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 1270795 = 1906193) B1906193
theorem B844843 : Blo 750330 844843 := bstep (se 1 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 844843 = 1267265) B1267265
theorem B16311365 : Blo 750330 16311365 := bstep (se 4 (by rfl) ⟨1529190, by rfl⟩ : syracuseStep 16311365 = 3058381) B3058381
theorem B3433565 : Blo 750330 3433565 := bstep (se 3 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 3433565 = 1287587) B1287587
theorem B844951 : Blo 750330 844951 := bstep (se 1 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 844951 = 1267427) B1267427
theorem B1270937 : Blo 750330 1270937 := bstep (se 2 (by rfl) ⟨476601, by rfl⟩ : syracuseStep 1270937 = 953203) B953203
theorem B1696985 : Blo 750330 1696985 := bstep (se 2 (by rfl) ⟨636369, by rfl⟩ : syracuseStep 1696985 = 1272739) B1272739
theorem B2712797 : Blo 750330 2712797 := bstep (se 3 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 2712797 = 1017299) B1017299
theorem B1271065 : Blo 750330 1271065 := bstep (se 2 (by rfl) ⟨476649, by rfl⟩ : syracuseStep 1271065 = 953299) B953299
theorem B1697075 : Blo 750330 1697075 := bstep (se 1 (by rfl) ⟨1272806, by rfl⟩ : syracuseStep 1697075 = 2545613) B2545613
theorem B845131 : Blo 750330 845131 := bstep (se 1 (by rfl) ⟨633848, by rfl⟩ : syracuseStep 845131 = 1267697) B1267697
theorem B1205579 : Blo 750330 1205579 := bstep (se 1 (by rfl) ⟨904184, by rfl⟩ : syracuseStep 1205579 = 1808369) B1808369
theorem B1697111 : Blo 750330 1697111 := bstep (se 1 (by rfl) ⟨1272833, by rfl⟩ : syracuseStep 1697111 = 2545667) B2545667
theorem B3433859 : Blo 750330 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B845239 : Blo 750330 845239 := bstep (se 1 (by rfl) ⟨633929, by rfl⟩ : syracuseStep 845239 = 1267859) B1267859
theorem B2713025 : Blo 750330 2713025 := bstep (se 2 (by rfl) ⟨1017384, by rfl⟩ : syracuseStep 2713025 = 2034769) B2034769
theorem B2287169 : Blo 750330 2287169 := bstep (se 2 (by rfl) ⟨857688, by rfl⟩ : syracuseStep 2287169 = 1715377) B1715377
theorem B845419 : Blo 750330 845419 := bstep (se 1 (by rfl) ⟨634064, by rfl⟩ : syracuseStep 845419 = 1268129) B1268129
theorem B845527 : Blo 750330 845527 := bstep (se 1 (by rfl) ⟨634145, by rfl⟩ : syracuseStep 845527 = 1268291) B1268291
theorem B1271639 : Blo 750330 1271639 := bstep (se 1 (by rfl) ⟨953729, by rfl⟩ : syracuseStep 1271639 = 1907459) B1907459
theorem B2713475 : Blo 750330 2713475 := bstep (se 1 (by rfl) ⟨2035106, by rfl⟩ : syracuseStep 2713475 = 4070213) B4070213
theorem B845707 : Blo 750330 845707 := bstep (se 1 (by rfl) ⟨634280, by rfl⟩ : syracuseStep 845707 = 1268561) B1268561
theorem B21718961 : Blo 750330 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B1271767 : Blo 750330 1271767 := bstep (se 1 (by rfl) ⟨953825, by rfl⟩ : syracuseStep 1271767 = 1907651) B1907651
theorem B845815 : Blo 750330 845815 := bstep (se 1 (by rfl) ⟨634361, by rfl⟩ : syracuseStep 845815 = 1268723) B1268723
theorem B4810853 : Blo 750330 4810853 := bstep (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) B902035
theorem B845995 : Blo 750330 845995 := bstep (se 1 (by rfl) ⟨634496, by rfl⟩ : syracuseStep 845995 = 1268993) B1268993
theorem B4286681 : Blo 750330 4286681 := bstep (se 2 (by rfl) ⟨1607505, by rfl⟩ : syracuseStep 4286681 = 3215011) B3215011
theorem B846103 : Blo 750330 846103 := bstep (se 1 (by rfl) ⟨634577, by rfl⟩ : syracuseStep 846103 = 1269155) B1269155
theorem B2713949 : Blo 750330 2713949 := bstep (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) B1017731
theorem B846283 : Blo 750330 846283 := bstep (se 1 (by rfl) ⟨634712, by rfl⟩ : syracuseStep 846283 = 1269425) B1269425
theorem B13560281 : Blo 750330 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B1206809 : Blo 750330 1206809 := bstep (se 2 (by rfl) ⟨452553, by rfl⟩ : syracuseStep 1206809 = 905107) B905107
theorem B846391 : Blo 750330 846391 := bstep (se 1 (by rfl) ⟨634793, by rfl⟩ : syracuseStep 846391 = 1269587) B1269587
theorem B1272395 : Blo 750330 1272395 := bstep (se 1 (by rfl) ⟨954296, by rfl⟩ : syracuseStep 1272395 = 1908593) B1908593
theorem B11168387 : Blo 750330 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B1272523 : Blo 750330 1272523 := bstep (se 1 (by rfl) ⟨954392, by rfl⟩ : syracuseStep 1272523 = 1908785) B1908785
theorem B846571 : Blo 750330 846571 := bstep (se 1 (by rfl) ⟨634928, by rfl⟩ : syracuseStep 846571 = 1269857) B1269857
theorem B846679 : Blo 750330 846679 := bstep (se 1 (by rfl) ⟨635009, by rfl⟩ : syracuseStep 846679 = 1270019) B1270019
theorem B1272665 : Blo 750330 1272665 := bstep (se 2 (by rfl) ⟨477249, by rfl⟩ : syracuseStep 1272665 = 954499) B954499
theorem B1272793 : Blo 750330 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B846859 : Blo 750330 846859 := bstep (se 1 (by rfl) ⟨635144, by rfl⟩ : syracuseStep 846859 = 1270289) B1270289
theorem B846967 : Blo 750330 846967 := bstep (se 1 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 846967 = 1270451) B1270451
theorem B847147 : Blo 750330 847147 := bstep (se 1 (by rfl) ⟨635360, by rfl⟩ : syracuseStep 847147 = 1270721) B1270721
theorem B7236965 : Blo 750330 7236965 := bstep (se 4 (by rfl) ⟨678465, by rfl⟩ : syracuseStep 7236965 = 1356931) B1356931
theorem B879979 : Blo 750330 879979 := bstep (se 1 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 879979 = 1319969) B1319969
theorem B847255 : Blo 750330 847255 := bstep (se 1 (by rfl) ⟨635441, by rfl⟩ : syracuseStep 847255 = 1270883) B1270883
theorem B3206621 : Blo 750330 3206621 := bstep (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) B1202483
theorem B847435 : Blo 750330 847435 := bstep (se 1 (by rfl) ⟨635576, by rfl⟩ : syracuseStep 847435 = 1271153) B1271153
theorem B847543 : Blo 750330 847543 := bstep (se 1 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 847543 = 1271315) B1271315
theorem B847723 : Blo 750330 847723 := bstep (se 1 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 847723 = 1271585) B1271585
theorem B4059031 : Blo 750330 4059031 := bstep (se 1 (by rfl) ⟨3044273, by rfl⟩ : syracuseStep 4059031 = 6088547) B6088547
theorem B847831 : Blo 750330 847831 := bstep (se 1 (by rfl) ⟨635873, by rfl⟩ : syracuseStep 847831 = 1271747) B1271747
theorem B815243 : Blo 750330 815243 := bstep (se 1 (by rfl) ⟨611432, by rfl⟩ : syracuseStep 815243 = 1222865) B1222865
theorem B848011 : Blo 750330 848011 := bstep (se 1 (by rfl) ⟨636008, by rfl⟩ : syracuseStep 848011 = 1272017) B1272017
theorem B1143001 : Blo 750330 1143001 := bstep (se 2 (by rfl) ⟨428625, by rfl⟩ : syracuseStep 1143001 = 857251) B857251
theorem B848119 : Blo 750330 848119 := bstep (se 1 (by rfl) ⟨636089, by rfl⟩ : syracuseStep 848119 = 1272179) B1272179
theorem B2748761 : Blo 750330 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B848299 : Blo 750330 848299 := bstep (se 1 (by rfl) ⟨636224, by rfl⟩ : syracuseStep 848299 = 1272449) B1272449
theorem B13005235 : Blo 750330 13005235 := bstep (se 1 (by rfl) ⟨9753926, by rfl⟩ : syracuseStep 13005235 = 19507853) B19507853
theorem B848407 : Blo 750330 848407 := bstep (se 1 (by rfl) ⟨636305, by rfl⟩ : syracuseStep 848407 = 1272611) B1272611
theorem B848587 : Blo 750330 848587 := bstep (se 1 (by rfl) ⟨636440, by rfl⟩ : syracuseStep 848587 = 1272881) B1272881
theorem B750347 : Blo 750330 750347 := bstep (se 1 (by rfl) ⟨562760, by rfl⟩ : syracuseStep 750347 = 1125521) B1125521
theorem B750359 : Blo 750330 750359 := bstep (se 1 (by rfl) ⟨562769, by rfl⟩ : syracuseStep 750359 = 1125539) B1125539
theorem B750379 : Blo 750330 750379 := bstep (se 1 (by rfl) ⟨562784, by rfl⟩ : syracuseStep 750379 = 1125569) B1125569
theorem B5698349 : Blo 750330 5698349 := bstep (se 3 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 5698349 = 2136881) B2136881
theorem B750391 : Blo 750330 750391 := bstep (se 1 (by rfl) ⟨562793, by rfl⟩ : syracuseStep 750391 = 1125587) B1125587
theorem B4289345 : Blo 750330 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B750411 : Blo 750330 750411 := bstep (se 1 (by rfl) ⟨562808, by rfl⟩ : syracuseStep 750411 = 1125617) B1125617
theorem B750423 : Blo 750330 750423 := bstep (se 1 (by rfl) ⟨562817, by rfl⟩ : syracuseStep 750423 = 1125635) B1125635
theorem B750443 : Blo 750330 750443 := bstep (se 1 (by rfl) ⟨562832, by rfl⟩ : syracuseStep 750443 = 1125665) B1125665
theorem B750455 : Blo 750330 750455 := bstep (se 1 (by rfl) ⟨562841, by rfl⟩ : syracuseStep 750455 = 1125683) B1125683
theorem B750475 : Blo 750330 750475 := bstep (se 1 (by rfl) ⟨562856, by rfl⟩ : syracuseStep 750475 = 1125713) B1125713
theorem B750487 : Blo 750330 750487 := bstep (se 1 (by rfl) ⟨562865, by rfl⟩ : syracuseStep 750487 = 1125731) B1125731
theorem B750507 : Blo 750330 750507 := bstep (se 1 (by rfl) ⟨562880, by rfl⟩ : syracuseStep 750507 = 1125761) B1125761
theorem B750519 : Blo 750330 750519 := bstep (se 1 (by rfl) ⟨562889, by rfl⟩ : syracuseStep 750519 = 1125779) B1125779
theorem B750539 : Blo 750330 750539 := bstep (se 1 (by rfl) ⟨562904, by rfl⟩ : syracuseStep 750539 = 1125809) B1125809
theorem B750551 : Blo 750330 750551 := bstep (se 1 (by rfl) ⟨562913, by rfl⟩ : syracuseStep 750551 = 1125827) B1125827
theorem B750571 : Blo 750330 750571 := bstep (se 1 (by rfl) ⟨562928, by rfl⟩ : syracuseStep 750571 = 1125857) B1125857
theorem B750583 : Blo 750330 750583 := bstep (se 1 (by rfl) ⟨562937, by rfl⟩ : syracuseStep 750583 = 1125875) B1125875
theorem B750603 : Blo 750330 750603 := bstep (se 1 (by rfl) ⟨562952, by rfl⟩ : syracuseStep 750603 = 1125905) B1125905
theorem B750615 : Blo 750330 750615 := bstep (se 1 (by rfl) ⟨562961, by rfl⟩ : syracuseStep 750615 = 1125923) B1125923
theorem B750635 : Blo 750330 750635 := bstep (se 1 (by rfl) ⟨562976, by rfl⟩ : syracuseStep 750635 = 1125953) B1125953
theorem B750647 : Blo 750330 750647 := bstep (se 1 (by rfl) ⟨562985, by rfl⟩ : syracuseStep 750647 = 1125971) B1125971
theorem B750667 : Blo 750330 750667 := bstep (se 1 (by rfl) ⟨563000, by rfl⟩ : syracuseStep 750667 = 1126001) B1126001
theorem B750679 : Blo 750330 750679 := bstep (se 1 (by rfl) ⟨563009, by rfl⟩ : syracuseStep 750679 = 1126019) B1126019
theorem B750699 : Blo 750330 750699 := bstep (se 1 (by rfl) ⟨563024, by rfl⟩ : syracuseStep 750699 = 1126049) B1126049
theorem B750711 : Blo 750330 750711 := bstep (se 1 (by rfl) ⟨563033, by rfl⟩ : syracuseStep 750711 = 1126067) B1126067
theorem B750731 : Blo 750330 750731 := bstep (se 1 (by rfl) ⟨563048, by rfl⟩ : syracuseStep 750731 = 1126097) B1126097
theorem B750743 : Blo 750330 750743 := bstep (se 1 (by rfl) ⟨563057, by rfl⟩ : syracuseStep 750743 = 1126115) B1126115
theorem B750763 : Blo 750330 750763 := bstep (se 1 (by rfl) ⟨563072, by rfl⟩ : syracuseStep 750763 = 1126145) B1126145
theorem B750775 : Blo 750330 750775 := bstep (se 1 (by rfl) ⟨563081, by rfl⟩ : syracuseStep 750775 = 1126163) B1126163
theorem B750795 : Blo 750330 750795 := bstep (se 1 (by rfl) ⟨563096, by rfl⟩ : syracuseStep 750795 = 1126193) B1126193
theorem B8123597 : Blo 750330 8123597 := bstep (se 3 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 8123597 = 3046349) B3046349
theorem B750807 : Blo 750330 750807 := bstep (se 1 (by rfl) ⟨563105, by rfl⟩ : syracuseStep 750807 = 1126211) B1126211
theorem B5862617 : Blo 750330 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B750827 : Blo 750330 750827 := bstep (se 1 (by rfl) ⟨563120, by rfl⟩ : syracuseStep 750827 = 1126241) B1126241
theorem B750839 : Blo 750330 750839 := bstep (se 1 (by rfl) ⟨563129, by rfl⟩ : syracuseStep 750839 = 1126259) B1126259
theorem B750859 : Blo 750330 750859 := bstep (se 1 (by rfl) ⟨563144, by rfl⟩ : syracuseStep 750859 = 1126289) B1126289
theorem B750871 : Blo 750330 750871 := bstep (se 1 (by rfl) ⟨563153, by rfl⟩ : syracuseStep 750871 = 1126307) B1126307
theorem B750891 : Blo 750330 750891 := bstep (se 1 (by rfl) ⟨563168, by rfl⟩ : syracuseStep 750891 = 1126337) B1126337
theorem B750903 : Blo 750330 750903 := bstep (se 1 (by rfl) ⟨563177, by rfl⟩ : syracuseStep 750903 = 1126355) B1126355
theorem B750923 : Blo 750330 750923 := bstep (se 1 (by rfl) ⟨563192, by rfl⟩ : syracuseStep 750923 = 1126385) B1126385
theorem B750935 : Blo 750330 750935 := bstep (se 1 (by rfl) ⟨563201, by rfl⟩ : syracuseStep 750935 = 1126403) B1126403
theorem B750955 : Blo 750330 750955 := bstep (se 1 (by rfl) ⟨563216, by rfl⟩ : syracuseStep 750955 = 1126433) B1126433
theorem B750967 : Blo 750330 750967 := bstep (se 1 (by rfl) ⟨563225, by rfl⟩ : syracuseStep 750967 = 1126451) B1126451
theorem B750987 : Blo 750330 750987 := bstep (se 1 (by rfl) ⟨563240, by rfl⟩ : syracuseStep 750987 = 1126481) B1126481
theorem B750999 : Blo 750330 750999 := bstep (se 1 (by rfl) ⟨563249, by rfl⟩ : syracuseStep 750999 = 1126499) B1126499
theorem B751019 : Blo 750330 751019 := bstep (se 1 (by rfl) ⟨563264, by rfl⟩ : syracuseStep 751019 = 1126529) B1126529
theorem B751031 : Blo 750330 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B751051 : Blo 750330 751051 := bstep (se 1 (by rfl) ⟨563288, by rfl⟩ : syracuseStep 751051 = 1126577) B1126577
theorem B751063 : Blo 750330 751063 := bstep (se 1 (by rfl) ⟨563297, by rfl⟩ : syracuseStep 751063 = 1126595) B1126595
theorem B751083 : Blo 750330 751083 := bstep (se 1 (by rfl) ⟨563312, by rfl⟩ : syracuseStep 751083 = 1126625) B1126625
theorem B751095 : Blo 750330 751095 := bstep (se 1 (by rfl) ⟨563321, by rfl⟩ : syracuseStep 751095 = 1126643) B1126643
theorem B751115 : Blo 750330 751115 := bstep (se 1 (by rfl) ⟨563336, by rfl⟩ : syracuseStep 751115 = 1126673) B1126673
theorem B751127 : Blo 750330 751127 := bstep (se 1 (by rfl) ⟨563345, by rfl⟩ : syracuseStep 751127 = 1126691) B1126691
theorem B751147 : Blo 750330 751147 := bstep (se 1 (by rfl) ⟨563360, by rfl⟩ : syracuseStep 751147 = 1126721) B1126721
theorem B751159 : Blo 750330 751159 := bstep (se 1 (by rfl) ⟨563369, by rfl⟩ : syracuseStep 751159 = 1126739) B1126739
theorem B751179 : Blo 750330 751179 := bstep (se 1 (by rfl) ⟨563384, by rfl⟩ : syracuseStep 751179 = 1126769) B1126769
theorem B751191 : Blo 750330 751191 := bstep (se 1 (by rfl) ⟨563393, by rfl⟩ : syracuseStep 751191 = 1126787) B1126787
theorem B751211 : Blo 750330 751211 := bstep (se 1 (by rfl) ⟨563408, by rfl⟩ : syracuseStep 751211 = 1126817) B1126817
theorem B751223 : Blo 750330 751223 := bstep (se 1 (by rfl) ⟨563417, by rfl⟩ : syracuseStep 751223 = 1126835) B1126835
theorem B751243 : Blo 750330 751243 := bstep (se 1 (by rfl) ⟨563432, by rfl⟩ : syracuseStep 751243 = 1126865) B1126865
theorem B751255 : Blo 750330 751255 := bstep (se 1 (by rfl) ⟨563441, by rfl⟩ : syracuseStep 751255 = 1126883) B1126883
theorem B751275 : Blo 750330 751275 := bstep (se 1 (by rfl) ⟨563456, by rfl⟩ : syracuseStep 751275 = 1126913) B1126913
theorem B751287 : Blo 750330 751287 := bstep (se 1 (by rfl) ⟨563465, by rfl⟩ : syracuseStep 751287 = 1126931) B1126931
theorem B751307 : Blo 750330 751307 := bstep (se 1 (by rfl) ⟨563480, by rfl⟩ : syracuseStep 751307 = 1126961) B1126961
theorem B751319 : Blo 750330 751319 := bstep (se 1 (by rfl) ⟨563489, by rfl⟩ : syracuseStep 751319 = 1126979) B1126979
theorem B751339 : Blo 750330 751339 := bstep (se 1 (by rfl) ⟨563504, by rfl⟩ : syracuseStep 751339 = 1127009) B1127009
theorem B751351 : Blo 750330 751351 := bstep (se 1 (by rfl) ⟨563513, by rfl⟩ : syracuseStep 751351 = 1127027) B1127027
theorem B751371 : Blo 750330 751371 := bstep (se 1 (by rfl) ⟨563528, by rfl⟩ : syracuseStep 751371 = 1127057) B1127057
theorem B751383 : Blo 750330 751383 := bstep (se 1 (by rfl) ⟨563537, by rfl⟩ : syracuseStep 751383 = 1127075) B1127075
theorem B751403 : Blo 750330 751403 := bstep (se 1 (by rfl) ⟨563552, by rfl⟩ : syracuseStep 751403 = 1127105) B1127105
theorem B751415 : Blo 750330 751415 := bstep (se 1 (by rfl) ⟨563561, by rfl⟩ : syracuseStep 751415 = 1127123) B1127123
theorem B751435 : Blo 750330 751435 := bstep (se 1 (by rfl) ⟨563576, by rfl⟩ : syracuseStep 751435 = 1127153) B1127153
theorem B751447 : Blo 750330 751447 := bstep (se 1 (by rfl) ⟨563585, by rfl⟩ : syracuseStep 751447 = 1127171) B1127171
theorem B751467 : Blo 750330 751467 := bstep (se 1 (by rfl) ⟨563600, by rfl⟩ : syracuseStep 751467 = 1127201) B1127201
theorem B751479 : Blo 750330 751479 := bstep (se 1 (by rfl) ⟨563609, by rfl⟩ : syracuseStep 751479 = 1127219) B1127219
theorem B751499 : Blo 750330 751499 := bstep (se 1 (by rfl) ⟨563624, by rfl⟩ : syracuseStep 751499 = 1127249) B1127249
theorem B751511 : Blo 750330 751511 := bstep (se 1 (by rfl) ⟨563633, by rfl⟩ : syracuseStep 751511 = 1127267) B1127267
theorem B1603481 : Blo 750330 1603481 := bstep (se 2 (by rfl) ⟨601305, by rfl⟩ : syracuseStep 1603481 = 1202611) B1202611
theorem B751531 : Blo 750330 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B751543 : Blo 750330 751543 := bstep (se 1 (by rfl) ⟨563657, by rfl⟩ : syracuseStep 751543 = 1127315) B1127315
theorem B751563 : Blo 750330 751563 := bstep (se 1 (by rfl) ⟨563672, by rfl⟩ : syracuseStep 751563 = 1127345) B1127345
theorem B751575 : Blo 750330 751575 := bstep (se 1 (by rfl) ⟨563681, by rfl⟩ : syracuseStep 751575 = 1127363) B1127363
theorem B751595 : Blo 750330 751595 := bstep (se 1 (by rfl) ⟨563696, by rfl⟩ : syracuseStep 751595 = 1127393) B1127393
theorem B751607 : Blo 750330 751607 := bstep (se 1 (by rfl) ⟨563705, by rfl⟩ : syracuseStep 751607 = 1127411) B1127411
theorem B3209219 : Blo 750330 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B6420485 : Blo 750330 6420485 := bstep (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) B1203841
theorem B751627 : Blo 750330 751627 := bstep (se 1 (by rfl) ⟨563720, by rfl⟩ : syracuseStep 751627 = 1127441) B1127441
theorem B751639 : Blo 750330 751639 := bstep (se 1 (by rfl) ⟨563729, by rfl⟩ : syracuseStep 751639 = 1127459) B1127459
theorem B751659 : Blo 750330 751659 := bstep (se 1 (by rfl) ⟨563744, by rfl⟩ : syracuseStep 751659 = 1127489) B1127489
theorem B751671 : Blo 750330 751671 := bstep (se 1 (by rfl) ⟨563753, by rfl⟩ : syracuseStep 751671 = 1127507) B1127507
theorem B751691 : Blo 750330 751691 := bstep (se 1 (by rfl) ⟨563768, by rfl⟩ : syracuseStep 751691 = 1127537) B1127537
theorem B751703 : Blo 750330 751703 := bstep (se 1 (by rfl) ⟨563777, by rfl⟩ : syracuseStep 751703 = 1127555) B1127555
theorem B751723 : Blo 750330 751723 := bstep (se 1 (by rfl) ⟨563792, by rfl⟩ : syracuseStep 751723 = 1127585) B1127585
theorem B751735 : Blo 750330 751735 := bstep (se 1 (by rfl) ⟨563801, by rfl⟩ : syracuseStep 751735 = 1127603) B1127603
theorem B751755 : Blo 750330 751755 := bstep (se 1 (by rfl) ⟨563816, by rfl⟩ : syracuseStep 751755 = 1127633) B1127633
theorem B751767 : Blo 750330 751767 := bstep (se 1 (by rfl) ⟨563825, by rfl⟩ : syracuseStep 751767 = 1127651) B1127651
theorem B751787 : Blo 750330 751787 := bstep (se 1 (by rfl) ⟨563840, by rfl⟩ : syracuseStep 751787 = 1127681) B1127681
theorem B2717869 : Blo 750330 2717869 := bstep (se 3 (by rfl) ⟨509600, by rfl⟩ : syracuseStep 2717869 = 1019201) B1019201
theorem B751799 : Blo 750330 751799 := bstep (se 1 (by rfl) ⟨563849, by rfl⟩ : syracuseStep 751799 = 1127699) B1127699
theorem B751819 : Blo 750330 751819 := bstep (se 1 (by rfl) ⟨563864, by rfl⟩ : syracuseStep 751819 = 1127729) B1127729
theorem B751831 : Blo 750330 751831 := bstep (se 1 (by rfl) ⟨563873, by rfl⟩ : syracuseStep 751831 = 1127747) B1127747
theorem B751851 : Blo 750330 751851 := bstep (se 1 (by rfl) ⟨563888, by rfl⟩ : syracuseStep 751851 = 1127777) B1127777
theorem B751863 : Blo 750330 751863 := bstep (se 1 (by rfl) ⟨563897, by rfl⟩ : syracuseStep 751863 = 1127795) B1127795
theorem B751883 : Blo 750330 751883 := bstep (se 1 (by rfl) ⟨563912, by rfl⟩ : syracuseStep 751883 = 1127825) B1127825
theorem B751895 : Blo 750330 751895 := bstep (se 1 (by rfl) ⟨563921, by rfl⟩ : syracuseStep 751895 = 1127843) B1127843
theorem B751915 : Blo 750330 751915 := bstep (se 1 (by rfl) ⟨563936, by rfl⟩ : syracuseStep 751915 = 1127873) B1127873
theorem B1603891 : Blo 750330 1603891 := bstep (se 1 (by rfl) ⟨1202918, by rfl⟩ : syracuseStep 1603891 = 2405837) B2405837
theorem B751927 : Blo 750330 751927 := bstep (se 1 (by rfl) ⟨563945, by rfl⟩ : syracuseStep 751927 = 1127891) B1127891
theorem B751947 : Blo 750330 751947 := bstep (se 1 (by rfl) ⟨563960, by rfl⟩ : syracuseStep 751947 = 1127921) B1127921
theorem B751959 : Blo 750330 751959 := bstep (se 1 (by rfl) ⟨563969, by rfl⟩ : syracuseStep 751959 = 1127939) B1127939
theorem B751979 : Blo 750330 751979 := bstep (se 1 (by rfl) ⟨563984, by rfl⟩ : syracuseStep 751979 = 1127969) B1127969
theorem B751991 : Blo 750330 751991 := bstep (se 1 (by rfl) ⟨563993, by rfl⟩ : syracuseStep 751991 = 1127987) B1127987
theorem B752011 : Blo 750330 752011 := bstep (se 1 (by rfl) ⟨564008, by rfl⟩ : syracuseStep 752011 = 1128017) B1128017
theorem B752023 : Blo 750330 752023 := bstep (se 1 (by rfl) ⟨564017, by rfl⟩ : syracuseStep 752023 = 1128035) B1128035
theorem B752043 : Blo 750330 752043 := bstep (se 1 (by rfl) ⟨564032, by rfl⟩ : syracuseStep 752043 = 1128065) B1128065
theorem B752055 : Blo 750330 752055 := bstep (se 1 (by rfl) ⟨564041, by rfl⟩ : syracuseStep 752055 = 1128083) B1128083
theorem B752075 : Blo 750330 752075 := bstep (se 1 (by rfl) ⟨564056, by rfl⟩ : syracuseStep 752075 = 1128113) B1128113
theorem B752087 : Blo 750330 752087 := bstep (se 1 (by rfl) ⟨564065, by rfl⟩ : syracuseStep 752087 = 1128131) B1128131
theorem B752107 : Blo 750330 752107 := bstep (se 1 (by rfl) ⟨564080, by rfl⟩ : syracuseStep 752107 = 1128161) B1128161
theorem B752119 : Blo 750330 752119 := bstep (se 1 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 752119 = 1128179) B1128179
theorem B752139 : Blo 750330 752139 := bstep (se 1 (by rfl) ⟨564104, by rfl⟩ : syracuseStep 752139 = 1128209) B1128209
theorem B752151 : Blo 750330 752151 := bstep (se 1 (by rfl) ⟨564113, by rfl⟩ : syracuseStep 752151 = 1128227) B1128227
theorem B752171 : Blo 750330 752171 := bstep (se 1 (by rfl) ⟨564128, by rfl⟩ : syracuseStep 752171 = 1128257) B1128257
theorem B752183 : Blo 750330 752183 := bstep (se 1 (by rfl) ⟨564137, by rfl⟩ : syracuseStep 752183 = 1128275) B1128275
theorem B752203 : Blo 750330 752203 := bstep (se 1 (by rfl) ⟨564152, by rfl⟩ : syracuseStep 752203 = 1128305) B1128305
theorem B752215 : Blo 750330 752215 := bstep (se 1 (by rfl) ⟨564161, by rfl⟩ : syracuseStep 752215 = 1128323) B1128323
theorem B752235 : Blo 750330 752235 := bstep (se 1 (by rfl) ⟨564176, by rfl⟩ : syracuseStep 752235 = 1128353) B1128353
theorem B752247 : Blo 750330 752247 := bstep (se 1 (by rfl) ⟨564185, by rfl⟩ : syracuseStep 752247 = 1128371) B1128371
theorem B1604225 : Blo 750330 1604225 := bstep (se 2 (by rfl) ⟨601584, by rfl⟩ : syracuseStep 1604225 = 1203169) B1203169
theorem B752267 : Blo 750330 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B752279 : Blo 750330 752279 := bstep (se 1 (by rfl) ⟨564209, by rfl⟩ : syracuseStep 752279 = 1128419) B1128419
theorem B752299 : Blo 750330 752299 := bstep (se 1 (by rfl) ⟨564224, by rfl⟩ : syracuseStep 752299 = 1128449) B1128449
theorem B752311 : Blo 750330 752311 := bstep (se 1 (by rfl) ⟨564233, by rfl⟩ : syracuseStep 752311 = 1128467) B1128467
theorem B752331 : Blo 750330 752331 := bstep (se 1 (by rfl) ⟨564248, by rfl⟩ : syracuseStep 752331 = 1128497) B1128497
theorem B1014487 : Blo 750330 1014487 := bstep (se 1 (by rfl) ⟨760865, by rfl⟩ : syracuseStep 1014487 = 1521731) B1521731
theorem B752343 : Blo 750330 752343 := bstep (se 1 (by rfl) ⟨564257, by rfl⟩ : syracuseStep 752343 = 1128515) B1128515
theorem B752363 : Blo 750330 752363 := bstep (se 1 (by rfl) ⟨564272, by rfl⟩ : syracuseStep 752363 = 1128545) B1128545
theorem B752375 : Blo 750330 752375 := bstep (se 1 (by rfl) ⟨564281, by rfl⟩ : syracuseStep 752375 = 1128563) B1128563
theorem B2849539 : Blo 750330 2849539 := bstep (se 1 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 2849539 = 4274309) B4274309
theorem B752395 : Blo 750330 752395 := bstep (se 1 (by rfl) ⟨564296, by rfl⟩ : syracuseStep 752395 = 1128593) B1128593
theorem B2030359 : Blo 750330 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B752407 : Blo 750330 752407 := bstep (se 1 (by rfl) ⟨564305, by rfl⟩ : syracuseStep 752407 = 1128611) B1128611
theorem B752427 : Blo 750330 752427 := bstep (se 1 (by rfl) ⟨564320, by rfl⟩ : syracuseStep 752427 = 1128641) B1128641
theorem B752439 : Blo 750330 752439 := bstep (se 1 (by rfl) ⟨564329, by rfl⟩ : syracuseStep 752439 = 1128659) B1128659
theorem B752459 : Blo 750330 752459 := bstep (se 1 (by rfl) ⟨564344, by rfl⟩ : syracuseStep 752459 = 1128689) B1128689
theorem B752471 : Blo 750330 752471 := bstep (se 1 (by rfl) ⟨564353, by rfl⟩ : syracuseStep 752471 = 1128707) B1128707
theorem B1145689 : Blo 750330 1145689 := bstep (se 2 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 1145689 = 859267) B859267
theorem B752491 : Blo 750330 752491 := bstep (se 1 (by rfl) ⟨564368, by rfl⟩ : syracuseStep 752491 = 1128737) B1128737
theorem B752503 : Blo 750330 752503 := bstep (se 1 (by rfl) ⟨564377, by rfl⟩ : syracuseStep 752503 = 1128755) B1128755
theorem B752523 : Blo 750330 752523 := bstep (se 1 (by rfl) ⟨564392, by rfl⟩ : syracuseStep 752523 = 1128785) B1128785
theorem B752535 : Blo 750330 752535 := bstep (se 1 (by rfl) ⟨564401, by rfl⟩ : syracuseStep 752535 = 1128803) B1128803
theorem B752555 : Blo 750330 752555 := bstep (se 1 (by rfl) ⟨564416, by rfl⟩ : syracuseStep 752555 = 1128833) B1128833
theorem B752567 : Blo 750330 752567 := bstep (se 1 (by rfl) ⟨564425, by rfl⟩ : syracuseStep 752567 = 1128851) B1128851
theorem B752587 : Blo 750330 752587 := bstep (se 1 (by rfl) ⟨564440, by rfl⟩ : syracuseStep 752587 = 1128881) B1128881
theorem B752599 : Blo 750330 752599 := bstep (se 1 (by rfl) ⟨564449, by rfl⟩ : syracuseStep 752599 = 1128899) B1128899
theorem B2063321 : Blo 750330 2063321 := bstep (se 2 (by rfl) ⟨773745, by rfl⟩ : syracuseStep 2063321 = 1547491) B1547491
theorem B752619 : Blo 750330 752619 := bstep (se 1 (by rfl) ⟨564464, by rfl⟩ : syracuseStep 752619 = 1128929) B1128929
theorem B752631 : Blo 750330 752631 := bstep (se 1 (by rfl) ⟨564473, by rfl⟩ : syracuseStep 752631 = 1128947) B1128947
theorem B752651 : Blo 750330 752651 := bstep (se 1 (by rfl) ⟨564488, by rfl⟩ : syracuseStep 752651 = 1128977) B1128977
theorem B752663 : Blo 750330 752663 := bstep (se 1 (by rfl) ⟨564497, by rfl⟩ : syracuseStep 752663 = 1128995) B1128995
theorem B1375255 : Blo 750330 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B752683 : Blo 750330 752683 := bstep (se 1 (by rfl) ⟨564512, by rfl⟩ : syracuseStep 752683 = 1129025) B1129025
theorem B1899571 : Blo 750330 1899571 := bstep (se 1 (by rfl) ⟨1424678, by rfl⟩ : syracuseStep 1899571 = 2849357) B2849357
theorem B2849843 : Blo 750330 2849843 := bstep (se 1 (by rfl) ⟨2137382, by rfl⟩ : syracuseStep 2849843 = 4274765) B4274765
theorem B752695 : Blo 750330 752695 := bstep (se 1 (by rfl) ⟨564521, by rfl⟩ : syracuseStep 752695 = 1129043) B1129043
theorem B752715 : Blo 750330 752715 := bstep (se 1 (by rfl) ⟨564536, by rfl⟩ : syracuseStep 752715 = 1129073) B1129073
theorem B752727 : Blo 750330 752727 := bstep (se 1 (by rfl) ⟨564545, by rfl⟩ : syracuseStep 752727 = 1129091) B1129091
theorem B752747 : Blo 750330 752747 := bstep (se 1 (by rfl) ⟨564560, by rfl⟩ : syracuseStep 752747 = 1129121) B1129121
theorem B752759 : Blo 750330 752759 := bstep (se 1 (by rfl) ⟨564569, by rfl⟩ : syracuseStep 752759 = 1129139) B1129139
theorem B3800195 : Blo 750330 3800195 := bstep (se 1 (by rfl) ⟨2850146, by rfl⟩ : syracuseStep 3800195 = 5700293) B5700293
theorem B752779 : Blo 750330 752779 := bstep (se 1 (by rfl) ⟨564584, by rfl⟩ : syracuseStep 752779 = 1129169) B1129169
theorem B752791 : Blo 750330 752791 := bstep (se 1 (by rfl) ⟨564593, by rfl⟩ : syracuseStep 752791 = 1129187) B1129187
theorem B752811 : Blo 750330 752811 := bstep (se 1 (by rfl) ⟨564608, by rfl⟩ : syracuseStep 752811 = 1129217) B1129217
theorem B752823 : Blo 750330 752823 := bstep (se 1 (by rfl) ⟨564617, by rfl⟩ : syracuseStep 752823 = 1129235) B1129235
theorem B1899713 : Blo 750330 1899713 := bstep (se 2 (by rfl) ⟨712392, by rfl⟩ : syracuseStep 1899713 = 1424785) B1424785
theorem B752843 : Blo 750330 752843 := bstep (se 1 (by rfl) ⟨564632, by rfl⟩ : syracuseStep 752843 = 1129265) B1129265
theorem B752855 : Blo 750330 752855 := bstep (se 1 (by rfl) ⟨564641, by rfl⟩ : syracuseStep 752855 = 1129283) B1129283
theorem B752875 : Blo 750330 752875 := bstep (se 1 (by rfl) ⟨564656, by rfl⟩ : syracuseStep 752875 = 1129313) B1129313
theorem B752887 : Blo 750330 752887 := bstep (se 1 (by rfl) ⟨564665, by rfl⟩ : syracuseStep 752887 = 1129331) B1129331
theorem B752907 : Blo 750330 752907 := bstep (se 1 (by rfl) ⟨564680, by rfl⟩ : syracuseStep 752907 = 1129361) B1129361
theorem B752919 : Blo 750330 752919 := bstep (se 1 (by rfl) ⟨564689, by rfl⟩ : syracuseStep 752919 = 1129379) B1129379
theorem B752939 : Blo 750330 752939 := bstep (se 1 (by rfl) ⟨564704, by rfl⟩ : syracuseStep 752939 = 1129409) B1129409
theorem B752951 : Blo 750330 752951 := bstep (se 1 (by rfl) ⟨564713, by rfl⟩ : syracuseStep 752951 = 1129427) B1129427
theorem B752971 : Blo 750330 752971 := bstep (se 1 (by rfl) ⟨564728, by rfl⟩ : syracuseStep 752971 = 1129457) B1129457
theorem B1604951 : Blo 750330 1604951 := bstep (se 1 (by rfl) ⟨1203713, by rfl⟩ : syracuseStep 1604951 = 2407427) B2407427
theorem B752983 : Blo 750330 752983 := bstep (se 1 (by rfl) ⟨564737, by rfl⟩ : syracuseStep 752983 = 1129475) B1129475
theorem B753003 : Blo 750330 753003 := bstep (se 1 (by rfl) ⟨564752, by rfl⟩ : syracuseStep 753003 = 1129505) B1129505
theorem B753015 : Blo 750330 753015 := bstep (se 1 (by rfl) ⟨564761, by rfl⟩ : syracuseStep 753015 = 1129523) B1129523
theorem B753035 : Blo 750330 753035 := bstep (se 1 (by rfl) ⟨564776, by rfl⟩ : syracuseStep 753035 = 1129553) B1129553
theorem B753047 : Blo 750330 753047 := bstep (se 1 (by rfl) ⟨564785, by rfl⟩ : syracuseStep 753047 = 1129571) B1129571
theorem B753067 : Blo 750330 753067 := bstep (se 1 (by rfl) ⟨564800, by rfl⟩ : syracuseStep 753067 = 1129601) B1129601
theorem B753079 : Blo 750330 753079 := bstep (se 1 (by rfl) ⟨564809, by rfl⟩ : syracuseStep 753079 = 1129619) B1129619
theorem B753099 : Blo 750330 753099 := bstep (se 1 (by rfl) ⟨564824, by rfl⟩ : syracuseStep 753099 = 1129649) B1129649
theorem B753111 : Blo 750330 753111 := bstep (se 1 (by rfl) ⟨564833, by rfl⟩ : syracuseStep 753111 = 1129667) B1129667
theorem B753131 : Blo 750330 753131 := bstep (se 1 (by rfl) ⟨564848, by rfl⟩ : syracuseStep 753131 = 1129697) B1129697
theorem B753143 : Blo 750330 753143 := bstep (se 1 (by rfl) ⟨564857, by rfl⟩ : syracuseStep 753143 = 1129715) B1129715
theorem B753163 : Blo 750330 753163 := bstep (se 1 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 753163 = 1129745) B1129745
theorem B753175 : Blo 750330 753175 := bstep (se 1 (by rfl) ⟨564881, by rfl⟩ : syracuseStep 753175 = 1129763) B1129763
theorem B753195 : Blo 750330 753195 := bstep (se 1 (by rfl) ⟨564896, by rfl⟩ : syracuseStep 753195 = 1129793) B1129793
theorem B753207 : Blo 750330 753207 := bstep (se 1 (by rfl) ⟨564905, by rfl⟩ : syracuseStep 753207 = 1129811) B1129811
theorem B753227 : Blo 750330 753227 := bstep (se 1 (by rfl) ⟨564920, by rfl⟩ : syracuseStep 753227 = 1129841) B1129841
theorem B753239 : Blo 750330 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B753259 : Blo 750330 753259 := bstep (se 1 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 753259 = 1129889) B1129889
theorem B753271 : Blo 750330 753271 := bstep (se 1 (by rfl) ⟨564953, by rfl⟩ : syracuseStep 753271 = 1129907) B1129907
theorem B753291 : Blo 750330 753291 := bstep (se 1 (by rfl) ⟨564968, by rfl⟩ : syracuseStep 753291 = 1129937) B1129937
theorem B753303 : Blo 750330 753303 := bstep (se 1 (by rfl) ⟨564977, by rfl⟩ : syracuseStep 753303 = 1129955) B1129955
theorem B753323 : Blo 750330 753323 := bstep (se 1 (by rfl) ⟨564992, by rfl⟩ : syracuseStep 753323 = 1129985) B1129985
theorem B753335 : Blo 750330 753335 := bstep (se 1 (by rfl) ⟨565001, by rfl⟩ : syracuseStep 753335 = 1130003) B1130003
theorem B2850497 : Blo 750330 2850497 := bstep (se 2 (by rfl) ⟨1068936, by rfl⟩ : syracuseStep 2850497 = 2137873) B2137873
theorem B949963 : Blo 750330 949963 := bstep (se 1 (by rfl) ⟨712472, by rfl⟩ : syracuseStep 949963 = 1424945) B1424945
theorem B753355 : Blo 750330 753355 := bstep (se 1 (by rfl) ⟨565016, by rfl⟩ : syracuseStep 753355 = 1130033) B1130033
theorem B753367 : Blo 750330 753367 := bstep (se 1 (by rfl) ⟨565025, by rfl⟩ : syracuseStep 753367 = 1130051) B1130051
theorem B3047129 : Blo 750330 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B753387 : Blo 750330 753387 := bstep (se 1 (by rfl) ⟨565040, by rfl⟩ : syracuseStep 753387 = 1130081) B1130081
theorem B24772337 : Blo 750330 24772337 := bstep (se 2 (by rfl) ⟨9289626, by rfl⟩ : syracuseStep 24772337 = 18579253) B18579253
theorem B753399 : Blo 750330 753399 := bstep (se 1 (by rfl) ⟨565049, by rfl⟩ : syracuseStep 753399 = 1130099) B1130099
theorem B753419 : Blo 750330 753419 := bstep (se 1 (by rfl) ⟨565064, by rfl⟩ : syracuseStep 753419 = 1130129) B1130129
theorem B753431 : Blo 750330 753431 := bstep (se 1 (by rfl) ⟨565073, by rfl⟩ : syracuseStep 753431 = 1130147) B1130147
theorem B753451 : Blo 750330 753451 := bstep (se 1 (by rfl) ⟨565088, by rfl⟩ : syracuseStep 753451 = 1130177) B1130177
theorem B753463 : Blo 750330 753463 := bstep (se 1 (by rfl) ⟨565097, by rfl⟩ : syracuseStep 753463 = 1130195) B1130195
theorem B753483 : Blo 750330 753483 := bstep (se 1 (by rfl) ⟨565112, by rfl⟩ : syracuseStep 753483 = 1130225) B1130225
theorem B753495 : Blo 750330 753495 := bstep (se 1 (by rfl) ⟨565121, by rfl⟩ : syracuseStep 753495 = 1130243) B1130243
theorem B753515 : Blo 750330 753515 := bstep (se 1 (by rfl) ⟨565136, by rfl⟩ : syracuseStep 753515 = 1130273) B1130273
theorem B753527 : Blo 750330 753527 := bstep (se 1 (by rfl) ⟨565145, by rfl⟩ : syracuseStep 753527 = 1130291) B1130291
theorem B753547 : Blo 750330 753547 := bstep (se 1 (by rfl) ⟨565160, by rfl⟩ : syracuseStep 753547 = 1130321) B1130321
theorem B753559 : Blo 750330 753559 := bstep (se 1 (by rfl) ⟨565169, by rfl⟩ : syracuseStep 753559 = 1130339) B1130339
theorem B753579 : Blo 750330 753579 := bstep (se 1 (by rfl) ⟨565184, by rfl⟩ : syracuseStep 753579 = 1130369) B1130369
theorem B753591 : Blo 750330 753591 := bstep (se 1 (by rfl) ⟨565193, by rfl⟩ : syracuseStep 753591 = 1130387) B1130387
theorem B753611 : Blo 750330 753611 := bstep (se 1 (by rfl) ⟨565208, by rfl⟩ : syracuseStep 753611 = 1130417) B1130417
theorem B950231 : Blo 750330 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B753623 : Blo 750330 753623 := bstep (se 1 (by rfl) ⟨565217, by rfl⟩ : syracuseStep 753623 = 1130435) B1130435
theorem B753643 : Blo 750330 753643 := bstep (se 1 (by rfl) ⟨565232, by rfl⟩ : syracuseStep 753643 = 1130465) B1130465
theorem B753655 : Blo 750330 753655 := bstep (se 1 (by rfl) ⟨565241, by rfl⟩ : syracuseStep 753655 = 1130483) B1130483
theorem B753671 : Blo 750330 753671 := bstep (se 1 (by rfl) ⟨565253, by rfl⟩ : syracuseStep 753671 = 1130507) B1130507
theorem B950287 : Blo 750330 950287 := bstep (se 1 (by rfl) ⟨712715, by rfl⟩ : syracuseStep 950287 = 1425431) B1425431
theorem B753679 : Blo 750330 753679 := bstep (se 1 (by rfl) ⟨565259, by rfl⟩ : syracuseStep 753679 = 1130519) B1130519
theorem B753723 : Blo 750330 753723 := bstep (se 1 (by rfl) ⟨565292, by rfl⟩ : syracuseStep 753723 = 1130585) B1130585
theorem B753799 : Blo 750330 753799 := bstep (se 1 (by rfl) ⟨565349, by rfl⟩ : syracuseStep 753799 = 1130699) B1130699
theorem B753807 : Blo 750330 753807 := bstep (se 1 (by rfl) ⟨565355, by rfl⟩ : syracuseStep 753807 = 1130711) B1130711
theorem B753851 : Blo 750330 753851 := bstep (se 1 (by rfl) ⟨565388, by rfl⟩ : syracuseStep 753851 = 1130777) B1130777
theorem B753927 : Blo 750330 753927 := bstep (se 1 (by rfl) ⟨565445, by rfl⟩ : syracuseStep 753927 = 1130891) B1130891
theorem B753935 : Blo 750330 753935 := bstep (se 1 (by rfl) ⟨565451, by rfl⟩ : syracuseStep 753935 = 1130903) B1130903
theorem B753979 : Blo 750330 753979 := bstep (se 1 (by rfl) ⟨565484, by rfl⟩ : syracuseStep 753979 = 1130969) B1130969
theorem B2031959 : Blo 750330 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B754055 : Blo 750330 754055 := bstep (se 1 (by rfl) ⟨565541, by rfl⟩ : syracuseStep 754055 = 1131083) B1131083
theorem B754063 : Blo 750330 754063 := bstep (se 1 (by rfl) ⟨565547, by rfl⟩ : syracuseStep 754063 = 1131095) B1131095
theorem B3801491 : Blo 750330 3801491 := bstep (se 1 (by rfl) ⟨2851118, by rfl⟩ : syracuseStep 3801491 = 5702237) B5702237
theorem B754107 : Blo 750330 754107 := bstep (se 1 (by rfl) ⟨565580, by rfl⟩ : syracuseStep 754107 = 1131161) B1131161
theorem B754183 : Blo 750330 754183 := bstep (se 1 (by rfl) ⟨565637, by rfl⟩ : syracuseStep 754183 = 1131275) B1131275
theorem B754191 : Blo 750330 754191 := bstep (se 1 (by rfl) ⟨565643, by rfl⟩ : syracuseStep 754191 = 1131287) B1131287
theorem B6423083 : Blo 750330 6423083 := bstep (se 1 (by rfl) ⟨4817312, by rfl⟩ : syracuseStep 6423083 = 9634625) B9634625
theorem B754235 : Blo 750330 754235 := bstep (se 1 (by rfl) ⟨565676, by rfl⟩ : syracuseStep 754235 = 1131353) B1131353
theorem B1901171 : Blo 750330 1901171 := bstep (se 1 (by rfl) ⟨1425878, by rfl⟩ : syracuseStep 1901171 = 2851757) B2851757
theorem B1901191 : Blo 750330 1901191 := bstep (se 1 (by rfl) ⟨1425893, by rfl⟩ : syracuseStep 1901191 = 2851787) B2851787
theorem B754311 : Blo 750330 754311 := bstep (se 1 (by rfl) ⟨565733, by rfl⟩ : syracuseStep 754311 = 1131467) B1131467
theorem B754319 : Blo 750330 754319 := bstep (se 1 (by rfl) ⟨565739, by rfl⟩ : syracuseStep 754319 = 1131479) B1131479
theorem B951031 : Blo 750330 951031 := bstep (se 1 (by rfl) ⟨713273, by rfl⟩ : syracuseStep 951031 = 1426547) B1426547
theorem B1901465 : Blo 750330 1901465 := bstep (se 2 (by rfl) ⟨713049, by rfl⟩ : syracuseStep 1901465 = 1426099) B1426099
theorem B54887381 : Blo 750330 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B1901627 : Blo 750330 1901627 := bstep (se 1 (by rfl) ⟨1426220, by rfl⟩ : syracuseStep 1901627 = 2852441) B2852441
theorem B951355 : Blo 750330 951355 := bstep (se 1 (by rfl) ⟨713516, by rfl⟩ : syracuseStep 951355 = 1427033) B1427033
theorem B4293719 : Blo 750330 4293719 := bstep (se 1 (by rfl) ⟨3220289, by rfl⟩ : syracuseStep 4293719 = 6440579) B6440579
theorem B1803379 : Blo 750330 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B6096005 : Blo 750330 6096005 := bstep (se 4 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 6096005 = 1143001) B1143001
theorem B1901839 : Blo 750330 1901839 := bstep (se 1 (by rfl) ⟨1426379, by rfl⟩ : syracuseStep 1901839 = 2852759) B2852759
theorem B3868019 : Blo 750330 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B2852243 : Blo 750330 2852243 := bstep (se 1 (by rfl) ⟨2139182, by rfl⟩ : syracuseStep 2852243 = 4278365) B4278365
theorem B4130327 : Blo 750330 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B1902113 : Blo 750330 1902113 := bstep (se 2 (by rfl) ⟨713292, by rfl⟩ : syracuseStep 1902113 = 1426585) B1426585
theorem B951851 : Blo 750330 951851 := bstep (se 1 (by rfl) ⟨713888, by rfl⟩ : syracuseStep 951851 = 1427777) B1427777
theorem B8554085 : Blo 750330 8554085 := bstep (se 4 (by rfl) ⟨801945, by rfl⟩ : syracuseStep 8554085 = 1603891) B1603891
theorem B6850277 : Blo 750330 6850277 := bstep (se 4 (by rfl) ⟨642213, by rfl⟩ : syracuseStep 6850277 = 1284427) B1284427
theorem B2033495 : Blo 750330 2033495 := bstep (se 1 (by rfl) ⟨1525121, by rfl⟩ : syracuseStep 2033495 = 3050243) B3050243
theorem B10618775 : Blo 750330 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B952327 : Blo 750330 952327 := bstep (se 1 (by rfl) ⟨714245, by rfl⟩ : syracuseStep 952327 = 1428491) B1428491
theorem B2033723 : Blo 750330 2033723 := bstep (se 1 (by rfl) ⟨1525292, by rfl⟩ : syracuseStep 2033723 = 3050585) B3050585
theorem B952823 : Blo 750330 952823 := bstep (se 1 (by rfl) ⟨714617, by rfl⟩ : syracuseStep 952823 = 1429235) B1429235
theorem B1903115 : Blo 750330 1903115 := bstep (se 1 (by rfl) ⟨1427336, by rfl⟩ : syracuseStep 1903115 = 2854673) B2854673
theorem B18287147 : Blo 750330 18287147 := bstep (se 1 (by rfl) ⟨13715360, by rfl⟩ : syracuseStep 18287147 = 27430721) B27430721
theorem B952975 : Blo 750330 952975 := bstep (se 1 (by rfl) ⟨714731, by rfl⟩ : syracuseStep 952975 = 1429463) B1429463
theorem B1018639 : Blo 750330 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B3607355 : Blo 750330 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B953147 : Blo 750330 953147 := bstep (se 1 (by rfl) ⟨714860, by rfl⟩ : syracuseStep 953147 = 1429721) B1429721
theorem B3607411 : Blo 750330 3607411 := bstep (se 1 (by rfl) ⟨2705558, by rfl⟩ : syracuseStep 3607411 = 5411117) B5411117
theorem B2853899 : Blo 750330 2853899 := bstep (se 1 (by rfl) ⟨2140424, by rfl⟩ : syracuseStep 2853899 = 4280849) B4280849
theorem B8555543 : Blo 750330 8555543 := bstep (se 1 (by rfl) ⟨6416657, by rfl⟩ : syracuseStep 8555543 = 12833315) B12833315
theorem B1018937 : Blo 750330 1018937 := bstep (se 2 (by rfl) ⟨382101, by rfl⟩ : syracuseStep 1018937 = 764203) B764203
theorem B1903763 : Blo 750330 1903763 := bstep (se 1 (by rfl) ⟨1427822, by rfl⟩ : syracuseStep 1903763 = 2855645) B2855645
theorem B3804569 : Blo 750330 3804569 := bstep (se 2 (by rfl) ⟨1426713, by rfl⟩ : syracuseStep 3804569 = 2853427) B2853427
theorem B1904057 : Blo 750330 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B954119 : Blo 750330 954119 := bstep (se 1 (by rfl) ⟨715589, by rfl⟩ : syracuseStep 954119 = 1431179) B1431179
theorem B5410597 : Blo 750330 5410597 := bstep (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) B1014487
theorem B3084331 : Blo 750330 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B1609787 : Blo 750330 1609787 := bstep (se 1 (by rfl) ⟨1207340, by rfl⟩ : syracuseStep 1609787 = 2414681) B2414681
theorem B1904755 : Blo 750330 1904755 := bstep (se 1 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 1904755 = 2857133) B2857133
theorem B1806455 : Blo 750330 1806455 := bstep (se 1 (by rfl) ⟨1354841, by rfl⟩ : syracuseStep 1806455 = 2709683) B2709683
theorem B1904897 : Blo 750330 1904897 := bstep (se 2 (by rfl) ⟨714336, by rfl⟩ : syracuseStep 1904897 = 1428673) B1428673
theorem B1806907 : Blo 750330 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B1905353 : Blo 750330 1905353 := bstep (se 2 (by rfl) ⟨714507, by rfl⟩ : syracuseStep 1905353 = 1429015) B1429015
theorem B3904271 : Blo 750330 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B5706611 : Blo 750330 5706611 := bstep (se 1 (by rfl) ⟨4279958, by rfl⟩ : syracuseStep 5706611 = 8559917) B8559917
theorem B1905707 : Blo 750330 1905707 := bstep (se 1 (by rfl) ⟨1429280, by rfl⟩ : syracuseStep 1905707 = 2858561) B2858561
theorem B5412041 : Blo 750330 5412041 := bstep (se 2 (by rfl) ⟨2029515, by rfl⟩ : syracuseStep 5412041 = 4059031) B4059031
theorem B8131985 : Blo 750330 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B1807915 : Blo 750330 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B1087291 : Blo 750330 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B17340313 : Blo 750330 17340313 := bstep (se 2 (by rfl) ⟨6502617, by rfl⟩ : syracuseStep 17340313 = 13005235) B13005235
theorem B3807161 : Blo 750330 3807161 := bstep (se 2 (by rfl) ⟨1427685, by rfl⟩ : syracuseStep 3807161 = 2855371) B2855371
theorem B1906699 : Blo 750330 1906699 := bstep (se 1 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 1906699 = 2860049) B2860049
theorem B858127 : Blo 750330 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B1808531 : Blo 750330 1808531 := bstep (se 1 (by rfl) ⟨1356398, by rfl⟩ : syracuseStep 1808531 = 2712797) B2712797
theorem B1906841 : Blo 750330 1906841 := bstep (se 2 (by rfl) ⟨715065, by rfl⟩ : syracuseStep 1906841 = 1430131) B1430131
theorem B1907003 : Blo 750330 1907003 := bstep (se 1 (by rfl) ⟨1430252, by rfl⟩ : syracuseStep 1907003 = 2860505) B2860505
theorem B1808983 : Blo 750330 1808983 := bstep (se 1 (by rfl) ⟨1356737, by rfl⟩ : syracuseStep 1808983 = 2713475) B2713475
theorem B1907347 : Blo 750330 1907347 := bstep (se 1 (by rfl) ⟨1430510, by rfl⟩ : syracuseStep 1907347 = 2861021) B2861021
theorem B1907489 : Blo 750330 1907489 := bstep (se 2 (by rfl) ⟨715308, by rfl⟩ : syracuseStep 1907489 = 1430617) B1430617
theorem B11606819 : Blo 750330 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B2857787 : Blo 750330 2857787 := bstep (se 1 (by rfl) ⟨2143340, by rfl⟩ : syracuseStep 2857787 = 4286681) B4286681
theorem B1809299 : Blo 750330 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B7445591 : Blo 750330 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B3808457 : Blo 750330 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B2858273 : Blo 750330 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B4824643 : Blo 750330 4824643 := bstep (se 1 (by rfl) ⟨3618482, by rfl⟩ : syracuseStep 4824643 = 7236965) B7236965
theorem B2137747 : Blo 750330 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B1908481 : Blo 750330 1908481 := bstep (se 2 (by rfl) ⟨715680, by rfl⟩ : syracuseStep 1908481 = 1431361) B1431361
theorem B3219385 : Blo 750330 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B2859245 : Blo 750330 2859245 := bstep (se 3 (by rfl) ⟨536108, by rfl⟩ : syracuseStep 2859245 = 1072217) B1072217
theorem B1909079 : Blo 750330 1909079 := bstep (se 1 (by rfl) ⟨1431809, by rfl⟩ : syracuseStep 1909079 = 2863619) B2863619
theorem B2859563 : Blo 750330 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B1909291 : Blo 750330 1909291 := bstep (se 1 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 1909291 = 2863937) B2863937
theorem B1450631 : Blo 750330 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B5415731 : Blo 750330 5415731 := bstep (se 1 (by rfl) ⟨4061798, by rfl⟩ : syracuseStep 5415731 = 8123597) B8123597
theorem B3908411 : Blo 750330 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B6431831 : Blo 750330 6431831 := bstep (se 1 (by rfl) ⟨4823873, by rfl⟩ : syracuseStep 6431831 = 9647747) B9647747
theorem B2139479 : Blo 750330 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B2532761 : Blo 750330 2532761 := bstep (se 2 (by rfl) ⟨949785, by rfl⟩ : syracuseStep 2532761 = 1899571) B1899571
theorem B6432209 : Blo 750330 6432209 := bstep (se 2 (by rfl) ⟨2412078, by rfl⟩ : syracuseStep 6432209 = 4824157) B4824157
theorem B4072913 : Blo 750330 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B3221383 : Blo 750330 3221383 := bstep (se 1 (by rfl) ⟨2416037, by rfl⟩ : syracuseStep 3221383 = 4832075) B4832075
theorem B7219205 : Blo 750330 7219205 := bstep (se 4 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 7219205 = 1353601) B1353601
theorem B2533463 : Blo 750330 2533463 := bstep (se 1 (by rfl) ⟨1900097, by rfl⟩ : syracuseStep 2533463 = 3800195) B3800195
theorem B928171 : Blo 750330 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B13740529 : Blo 750330 13740529 := bstep (se 2 (by rfl) ⟨5152698, by rfl⟩ : syracuseStep 13740529 = 10305397) B10305397
theorem B2533949 : Blo 750330 2533949 := bstep (se 3 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 2533949 = 950231) B950231
theorem B3615293 : Blo 750330 3615293 := bstep (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) B1355735
theorem B3615521 : Blo 750330 3615521 := bstep (se 2 (by rfl) ⟨1355820, by rfl⟩ : syracuseStep 3615521 = 2711641) B2711641
theorem B4074299 : Blo 750330 4074299 := bstep (se 1 (by rfl) ⟨3055724, by rfl⟩ : syracuseStep 4074299 = 6111449) B6111449
theorem B2141063 : Blo 750330 2141063 := bstep (se 1 (by rfl) ⟨1605797, by rfl⟩ : syracuseStep 2141063 = 3211595) B3211595
theorem B2173981 : Blo 750330 2173981 := bstep (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) B815243
theorem B1125563 : Blo 750330 1125563 := bstep (se 1 (by rfl) ⟨844172, by rfl⟩ : syracuseStep 1125563 = 1688345) B1688345
theorem B1125623 : Blo 750330 1125623 := bstep (se 1 (by rfl) ⟨844217, by rfl⟩ : syracuseStep 1125623 = 1688435) B1688435
theorem B1125647 : Blo 750330 1125647 := bstep (se 1 (by rfl) ⟨844235, by rfl⟩ : syracuseStep 1125647 = 1688471) B1688471
theorem B1715489 : Blo 750330 1715489 := bstep (se 2 (by rfl) ⟨643308, by rfl⟩ : syracuseStep 1715489 = 1286617) B1286617
theorem B1125689 : Blo 750330 1125689 := bstep (se 2 (by rfl) ⟨422133, by rfl⟩ : syracuseStep 1125689 = 844267) B844267
theorem B1125767 : Blo 750330 1125767 := bstep (se 1 (by rfl) ⟨844325, by rfl⟩ : syracuseStep 1125767 = 1688651) B1688651
theorem B1125803 : Blo 750330 1125803 := bstep (se 1 (by rfl) ⟨844352, by rfl⟩ : syracuseStep 1125803 = 1688705) B1688705
theorem B1125833 : Blo 750330 1125833 := bstep (se 2 (by rfl) ⟨422187, by rfl⟩ : syracuseStep 1125833 = 844375) B844375
theorem B2141711 : Blo 750330 2141711 := bstep (se 1 (by rfl) ⟨1606283, by rfl⟩ : syracuseStep 2141711 = 3212567) B3212567
theorem B1125947 : Blo 750330 1125947 := bstep (se 1 (by rfl) ⟨844460, by rfl⟩ : syracuseStep 1125947 = 1688921) B1688921
theorem B8564291 : Blo 750330 8564291 := bstep (se 1 (by rfl) ⟨6423218, by rfl⟩ : syracuseStep 8564291 = 12846437) B12846437
theorem B1126007 : Blo 750330 1126007 := bstep (se 1 (by rfl) ⟨844505, by rfl⟩ : syracuseStep 1126007 = 1689011) B1689011
theorem B1126031 : Blo 750330 1126031 := bstep (se 1 (by rfl) ⟨844523, by rfl⟩ : syracuseStep 1126031 = 1689047) B1689047
theorem B1126073 : Blo 750330 1126073 := bstep (se 2 (by rfl) ⟨422277, by rfl⟩ : syracuseStep 1126073 = 844555) B844555
theorem B1126151 : Blo 750330 1126151 := bstep (se 1 (by rfl) ⟨844613, by rfl⟩ : syracuseStep 1126151 = 1689227) B1689227
theorem B1126187 : Blo 750330 1126187 := bstep (se 1 (by rfl) ⟨844640, by rfl⟩ : syracuseStep 1126187 = 1689281) B1689281
theorem B1126217 : Blo 750330 1126217 := bstep (se 2 (by rfl) ⟨422331, by rfl⟩ : syracuseStep 1126217 = 844663) B844663
theorem B2535353 : Blo 750330 2535353 := bstep (se 2 (by rfl) ⟨950757, by rfl⟩ : syracuseStep 2535353 = 1901515) B1901515
theorem B1126331 : Blo 750330 1126331 := bstep (se 1 (by rfl) ⟨844748, by rfl⟩ : syracuseStep 1126331 = 1689497) B1689497
theorem B1126391 : Blo 750330 1126391 := bstep (se 1 (by rfl) ⟨844793, by rfl⟩ : syracuseStep 1126391 = 1689587) B1689587
theorem B1126415 : Blo 750330 1126415 := bstep (se 1 (by rfl) ⟨844811, by rfl⟩ : syracuseStep 1126415 = 1689623) B1689623
theorem B2863133 : Blo 750330 2863133 := bstep (se 3 (by rfl) ⟨536837, by rfl⟩ : syracuseStep 2863133 = 1073675) B1073675
theorem B2863147 : Blo 750330 2863147 := bstep (se 1 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 2863147 = 4294721) B4294721
theorem B1126457 : Blo 750330 1126457 := bstep (se 2 (by rfl) ⟨422421, by rfl⟩ : syracuseStep 1126457 = 844843) B844843
theorem B1126535 : Blo 750330 1126535 := bstep (se 1 (by rfl) ⟨844901, by rfl⟩ : syracuseStep 1126535 = 1689803) B1689803
theorem B1126571 : Blo 750330 1126571 := bstep (se 1 (by rfl) ⟨844928, by rfl⟩ : syracuseStep 1126571 = 1689857) B1689857
theorem B1126601 : Blo 750330 1126601 := bstep (se 2 (by rfl) ⟨422475, by rfl⟩ : syracuseStep 1126601 = 844951) B844951
theorem B1126715 : Blo 750330 1126715 := bstep (se 1 (by rfl) ⟨845036, by rfl⟩ : syracuseStep 1126715 = 1690073) B1690073
theorem B1126775 : Blo 750330 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B1356167 : Blo 750330 1356167 := bstep (se 1 (by rfl) ⟨1017125, by rfl⟩ : syracuseStep 1356167 = 2034251) B2034251
theorem B1126799 : Blo 750330 1126799 := bstep (se 1 (by rfl) ⟨845099, by rfl⟩ : syracuseStep 1126799 = 1690199) B1690199
theorem B1126841 : Blo 750330 1126841 := bstep (se 2 (by rfl) ⟨422565, by rfl⟩ : syracuseStep 1126841 = 845131) B845131
theorem B1126919 : Blo 750330 1126919 := bstep (se 1 (by rfl) ⟨845189, by rfl⟩ : syracuseStep 1126919 = 1690379) B1690379
theorem B2535947 : Blo 750330 2535947 := bstep (se 1 (by rfl) ⟨1901960, by rfl⟩ : syracuseStep 2535947 = 3803921) B3803921
theorem B3617291 : Blo 750330 3617291 := bstep (se 1 (by rfl) ⟨2712968, by rfl⟩ : syracuseStep 3617291 = 5425937) B5425937
theorem B1126955 : Blo 750330 1126955 := bstep (se 1 (by rfl) ⟨845216, by rfl⟩ : syracuseStep 1126955 = 1690433) B1690433
theorem B1126985 : Blo 750330 1126985 := bstep (se 2 (by rfl) ⟨422619, by rfl⟩ : syracuseStep 1126985 = 845239) B845239
theorem B2536055 : Blo 750330 2536055 := bstep (se 1 (by rfl) ⟨1902041, by rfl⟩ : syracuseStep 2536055 = 3804083) B3804083
theorem B1127099 : Blo 750330 1127099 := bstep (se 1 (by rfl) ⟨845324, by rfl⟩ : syracuseStep 1127099 = 1690649) B1690649
theorem B6435521 : Blo 750330 6435521 := bstep (se 2 (by rfl) ⟨2413320, by rfl⟩ : syracuseStep 6435521 = 4826641) B4826641
theorem B1127159 : Blo 750330 1127159 := bstep (se 1 (by rfl) ⟨845369, by rfl⟩ : syracuseStep 1127159 = 1690739) B1690739
theorem B4567823 : Blo 750330 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B1127183 : Blo 750330 1127183 := bstep (se 1 (by rfl) ⟨845387, by rfl⟩ : syracuseStep 1127183 = 1690775) B1690775
theorem B1127225 : Blo 750330 1127225 := bstep (se 2 (by rfl) ⟨422709, by rfl⟩ : syracuseStep 1127225 = 845419) B845419
theorem B1127303 : Blo 750330 1127303 := bstep (se 1 (by rfl) ⟨845477, by rfl⟩ : syracuseStep 1127303 = 1690955) B1690955
theorem B3814289 : Blo 750330 3814289 := bstep (se 2 (by rfl) ⟨1430358, by rfl⟩ : syracuseStep 3814289 = 2860717) B2860717
theorem B1127339 : Blo 750330 1127339 := bstep (se 1 (by rfl) ⟨845504, by rfl⟩ : syracuseStep 1127339 = 1691009) B1691009
theorem B1127369 : Blo 750330 1127369 := bstep (se 2 (by rfl) ⟨422763, by rfl⟩ : syracuseStep 1127369 = 845527) B845527
theorem B1127483 : Blo 750330 1127483 := bstep (se 1 (by rfl) ⟨845612, by rfl⟩ : syracuseStep 1127483 = 1691225) B1691225
theorem B1356859 : Blo 750330 1356859 := bstep (se 1 (by rfl) ⟨1017644, by rfl⟩ : syracuseStep 1356859 = 2035289) B2035289
theorem B1127543 : Blo 750330 1127543 := bstep (se 1 (by rfl) ⟨845657, by rfl⟩ : syracuseStep 1127543 = 1691315) B1691315
theorem B2143351 : Blo 750330 2143351 := bstep (se 1 (by rfl) ⟨1607513, by rfl⟩ : syracuseStep 2143351 = 3215027) B3215027
theorem B1127567 : Blo 750330 1127567 := bstep (se 1 (by rfl) ⟨845675, by rfl⟩ : syracuseStep 1127567 = 1691351) B1691351
theorem B1127609 : Blo 750330 1127609 := bstep (se 2 (by rfl) ⟨422853, by rfl⟩ : syracuseStep 1127609 = 845707) B845707
theorem B2536649 : Blo 750330 2536649 := bstep (se 2 (by rfl) ⟨951243, by rfl⟩ : syracuseStep 2536649 = 1902487) B1902487
theorem B1127687 : Blo 750330 1127687 := bstep (se 1 (by rfl) ⟨845765, by rfl⟩ : syracuseStep 1127687 = 1691531) B1691531
theorem B1127723 : Blo 750330 1127723 := bstep (se 1 (by rfl) ⟨845792, by rfl⟩ : syracuseStep 1127723 = 1691585) B1691585
theorem B1127753 : Blo 750330 1127753 := bstep (se 2 (by rfl) ⟨422907, by rfl⟩ : syracuseStep 1127753 = 845815) B845815
theorem B4634003 : Blo 750330 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B1127867 : Blo 750330 1127867 := bstep (se 1 (by rfl) ⟨845900, by rfl⟩ : syracuseStep 1127867 = 1691801) B1691801
theorem B1127927 : Blo 750330 1127927 := bstep (se 1 (by rfl) ⟨845945, by rfl⟩ : syracuseStep 1127927 = 1691891) B1691891
theorem B1127951 : Blo 750330 1127951 := bstep (se 1 (by rfl) ⟨845963, by rfl⟩ : syracuseStep 1127951 = 1691927) B1691927
theorem B1127993 : Blo 750330 1127993 := bstep (se 2 (by rfl) ⟨422997, by rfl⟩ : syracuseStep 1127993 = 845995) B845995
theorem B1488443 : Blo 750330 1488443 := bstep (se 1 (by rfl) ⟨1116332, by rfl⟩ : syracuseStep 1488443 = 2232665) B2232665
theorem B1128071 : Blo 750330 1128071 := bstep (se 1 (by rfl) ⟨846053, by rfl⟩ : syracuseStep 1128071 = 1692107) B1692107
theorem B1128107 : Blo 750330 1128107 := bstep (se 1 (by rfl) ⟨846080, by rfl⟩ : syracuseStep 1128107 = 1692161) B1692161
theorem B20592305 : Blo 750330 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B1128137 : Blo 750330 1128137 := bstep (se 2 (by rfl) ⟨423051, by rfl⟩ : syracuseStep 1128137 = 846103) B846103
theorem B2406145 : Blo 750330 2406145 := bstep (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) B1804609
theorem B6108979 : Blo 750330 6108979 := bstep (se 1 (by rfl) ⟨4581734, by rfl⟩ : syracuseStep 6108979 = 9163469) B9163469
theorem B1128251 : Blo 750330 1128251 := bstep (se 1 (by rfl) ⟨846188, by rfl⟩ : syracuseStep 1128251 = 1692377) B1692377
theorem B1128311 : Blo 750330 1128311 := bstep (se 1 (by rfl) ⟨846233, by rfl⟩ : syracuseStep 1128311 = 1692467) B1692467
theorem B2537351 : Blo 750330 2537351 := bstep (se 1 (by rfl) ⟨1903013, by rfl⟩ : syracuseStep 2537351 = 3806027) B3806027
theorem B1128335 : Blo 750330 1128335 := bstep (se 1 (by rfl) ⟨846251, by rfl⟩ : syracuseStep 1128335 = 1692503) B1692503
theorem B1128377 : Blo 750330 1128377 := bstep (se 2 (by rfl) ⟨423141, by rfl⟩ : syracuseStep 1128377 = 846283) B846283
theorem B1128455 : Blo 750330 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B1128491 : Blo 750330 1128491 := bstep (se 1 (by rfl) ⟨846368, by rfl⟩ : syracuseStep 1128491 = 1692737) B1692737
theorem B1128521 : Blo 750330 1128521 := bstep (se 2 (by rfl) ⟨423195, by rfl⟩ : syracuseStep 1128521 = 846391) B846391
theorem B1128635 : Blo 750330 1128635 := bstep (se 1 (by rfl) ⟨846476, by rfl⟩ : syracuseStep 1128635 = 1692953) B1692953
theorem B4569281 : Blo 750330 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B1128695 : Blo 750330 1128695 := bstep (se 1 (by rfl) ⟨846521, by rfl⟩ : syracuseStep 1128695 = 1693043) B1693043
theorem B2537729 : Blo 750330 2537729 := bstep (se 2 (by rfl) ⟨951648, by rfl⟩ : syracuseStep 2537729 = 1903297) B1903297
theorem B1128719 : Blo 750330 1128719 := bstep (se 1 (by rfl) ⟨846539, by rfl⟩ : syracuseStep 1128719 = 1693079) B1693079
theorem B1128761 : Blo 750330 1128761 := bstep (se 2 (by rfl) ⟨423285, by rfl⟩ : syracuseStep 1128761 = 846571) B846571
theorem B4274491 : Blo 750330 4274491 := bstep (se 1 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 4274491 = 6411737) B6411737
theorem B3422579 : Blo 750330 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B2144627 : Blo 750330 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B1128839 : Blo 750330 1128839 := bstep (se 1 (by rfl) ⟨846629, by rfl⟩ : syracuseStep 1128839 = 1693259) B1693259
theorem B1128875 : Blo 750330 1128875 := bstep (se 1 (by rfl) ⟨846656, by rfl⟩ : syracuseStep 1128875 = 1693313) B1693313
theorem B1128905 : Blo 750330 1128905 := bstep (se 2 (by rfl) ⟨423339, by rfl⟩ : syracuseStep 1128905 = 846679) B846679
theorem B1129019 : Blo 750330 1129019 := bstep (se 1 (by rfl) ⟨846764, by rfl⟩ : syracuseStep 1129019 = 1693529) B1693529
theorem B2144855 : Blo 750330 2144855 := bstep (se 1 (by rfl) ⟨1608641, by rfl⟩ : syracuseStep 2144855 = 3217283) B3217283
theorem B1129079 : Blo 750330 1129079 := bstep (se 1 (by rfl) ⟨846809, by rfl⟩ : syracuseStep 1129079 = 1693619) B1693619
theorem B1129103 : Blo 750330 1129103 := bstep (se 1 (by rfl) ⟨846827, by rfl⟩ : syracuseStep 1129103 = 1693655) B1693655
theorem B1129145 : Blo 750330 1129145 := bstep (se 2 (by rfl) ⟨423429, by rfl⟩ : syracuseStep 1129145 = 846859) B846859
theorem B4831973 : Blo 750330 4831973 := bstep (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) B905995
theorem B1129223 : Blo 750330 1129223 := bstep (se 1 (by rfl) ⟨846917, by rfl⟩ : syracuseStep 1129223 = 1693835) B1693835
theorem B1129259 : Blo 750330 1129259 := bstep (se 1 (by rfl) ⟨846944, by rfl⟩ : syracuseStep 1129259 = 1693889) B1693889
theorem B1129289 : Blo 750330 1129289 := bstep (se 2 (by rfl) ⟨423483, by rfl⟩ : syracuseStep 1129289 = 846967) B846967
theorem B1358777 : Blo 750330 1358777 := bstep (se 2 (by rfl) ⟨509541, by rfl⟩ : syracuseStep 1358777 = 1019083) B1019083
theorem B1129403 : Blo 750330 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B3816395 : Blo 750330 3816395 := bstep (se 1 (by rfl) ⟨2862296, by rfl⟩ : syracuseStep 3816395 = 5724593) B5724593
theorem B1129463 : Blo 750330 1129463 := bstep (se 1 (by rfl) ⟨847097, by rfl⟩ : syracuseStep 1129463 = 1694195) B1694195
theorem B82394117 : Blo 750330 82394117 := bstep (se 4 (by rfl) ⟨7724448, by rfl⟩ : syracuseStep 82394117 = 15448897) B15448897
theorem B1129487 : Blo 750330 1129487 := bstep (se 1 (by rfl) ⟨847115, by rfl⟩ : syracuseStep 1129487 = 1694231) B1694231
theorem B2538539 : Blo 750330 2538539 := bstep (se 1 (by rfl) ⟨1903904, by rfl⟩ : syracuseStep 2538539 = 3807809) B3807809
theorem B1129529 : Blo 750330 1129529 := bstep (se 2 (by rfl) ⟨423573, by rfl⟩ : syracuseStep 1129529 = 847147) B847147
theorem B1129607 : Blo 750330 1129607 := bstep (se 1 (by rfl) ⟨847205, by rfl⟩ : syracuseStep 1129607 = 1694411) B1694411
theorem B1129643 : Blo 750330 1129643 := bstep (se 1 (by rfl) ⟨847232, by rfl⟩ : syracuseStep 1129643 = 1694465) B1694465
theorem B1129673 : Blo 750330 1129673 := bstep (se 2 (by rfl) ⟨423627, by rfl⟩ : syracuseStep 1129673 = 847255) B847255
theorem B3816719 : Blo 750330 3816719 := bstep (se 1 (by rfl) ⟨2862539, by rfl⟩ : syracuseStep 3816719 = 5725079) B5725079
theorem B1359137 : Blo 750330 1359137 := bstep (se 2 (by rfl) ⟨509676, by rfl⟩ : syracuseStep 1359137 = 1019353) B1019353
theorem B1129787 : Blo 750330 1129787 := bstep (se 1 (by rfl) ⟨847340, by rfl⟩ : syracuseStep 1129787 = 1694681) B1694681
theorem B1129847 : Blo 750330 1129847 := bstep (se 1 (by rfl) ⟨847385, by rfl⟩ : syracuseStep 1129847 = 1694771) B1694771
theorem B1129871 : Blo 750330 1129871 := bstep (se 1 (by rfl) ⟨847403, by rfl⟩ : syracuseStep 1129871 = 1694807) B1694807
theorem B1129913 : Blo 750330 1129913 := bstep (se 2 (by rfl) ⟨423717, by rfl⟩ : syracuseStep 1129913 = 847435) B847435
theorem B11124173 : Blo 750330 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B1129991 : Blo 750330 1129991 := bstep (se 1 (by rfl) ⟨847493, by rfl⟩ : syracuseStep 1129991 = 1694987) B1694987
theorem B1130027 : Blo 750330 1130027 := bstep (se 1 (by rfl) ⟨847520, by rfl⟩ : syracuseStep 1130027 = 1695041) B1695041
theorem B1130057 : Blo 750330 1130057 := bstep (se 2 (by rfl) ⟨423771, by rfl⟩ : syracuseStep 1130057 = 847543) B847543
theorem B1425043 : Blo 750330 1425043 := bstep (se 1 (by rfl) ⟨1068782, by rfl⟩ : syracuseStep 1425043 = 2137565) B2137565
theorem B1130171 : Blo 750330 1130171 := bstep (se 1 (by rfl) ⟨847628, by rfl⟩ : syracuseStep 1130171 = 1695257) B1695257
theorem B4275949 : Blo 750330 4275949 := bstep (se 3 (by rfl) ⟨801740, by rfl⟩ : syracuseStep 4275949 = 1603481) B1603481
theorem B1130231 : Blo 750330 1130231 := bstep (se 1 (by rfl) ⟨847673, by rfl⟩ : syracuseStep 1130231 = 1695347) B1695347
theorem B966415 : Blo 750330 966415 := bstep (se 1 (by rfl) ⟨724811, by rfl⟩ : syracuseStep 966415 = 1449623) B1449623
theorem B1130255 : Blo 750330 1130255 := bstep (se 1 (by rfl) ⟨847691, by rfl⟩ : syracuseStep 1130255 = 1695383) B1695383
theorem B1130297 : Blo 750330 1130297 := bstep (se 2 (by rfl) ⟨423861, by rfl⟩ : syracuseStep 1130297 = 847723) B847723
theorem B8568665 : Blo 750330 8568665 := bstep (se 2 (by rfl) ⟨3213249, by rfl⟩ : syracuseStep 8568665 = 6426499) B6426499
theorem B1425271 : Blo 750330 1425271 := bstep (se 1 (by rfl) ⟨1068953, by rfl⟩ : syracuseStep 1425271 = 2137907) B2137907
theorem B1130375 : Blo 750330 1130375 := bstep (se 1 (by rfl) ⟨847781, by rfl⟩ : syracuseStep 1130375 = 1695563) B1695563
theorem B1130411 : Blo 750330 1130411 := bstep (se 1 (by rfl) ⟨847808, by rfl⟩ : syracuseStep 1130411 = 1695617) B1695617
theorem B1130441 : Blo 750330 1130441 := bstep (se 2 (by rfl) ⟨423915, by rfl⟩ : syracuseStep 1130441 = 847831) B847831
theorem B16269335 : Blo 750330 16269335 := bstep (se 1 (by rfl) ⟨12202001, by rfl⟩ : syracuseStep 16269335 = 24404003) B24404003
theorem B1130555 : Blo 750330 1130555 := bstep (se 1 (by rfl) ⟨847916, by rfl⟩ : syracuseStep 1130555 = 1695833) B1695833
theorem B1130615 : Blo 750330 1130615 := bstep (se 1 (by rfl) ⟨847961, by rfl⟩ : syracuseStep 1130615 = 1695923) B1695923
theorem B2146439 : Blo 750330 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B1130639 : Blo 750330 1130639 := bstep (se 1 (by rfl) ⟨847979, by rfl⟩ : syracuseStep 1130639 = 1695959) B1695959
theorem B1130681 : Blo 750330 1130681 := bstep (se 2 (by rfl) ⟨424005, by rfl⟩ : syracuseStep 1130681 = 848011) B848011
theorem B1130759 : Blo 750330 1130759 := bstep (se 1 (by rfl) ⟨848069, by rfl⟩ : syracuseStep 1130759 = 1696139) B1696139
theorem B12828941 : Blo 750330 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B1130795 : Blo 750330 1130795 := bstep (se 1 (by rfl) ⟨848096, by rfl⟩ : syracuseStep 1130795 = 1696193) B1696193
theorem B2539835 : Blo 750330 2539835 := bstep (se 1 (by rfl) ⟨1904876, by rfl⟩ : syracuseStep 2539835 = 3809753) B3809753
theorem B2146621 : Blo 750330 2146621 := bstep (se 3 (by rfl) ⟨402491, by rfl⟩ : syracuseStep 2146621 = 804983) B804983
theorem B1130825 : Blo 750330 1130825 := bstep (se 2 (by rfl) ⟨424059, by rfl⟩ : syracuseStep 1130825 = 848119) B848119
theorem B1130939 : Blo 750330 1130939 := bstep (se 1 (by rfl) ⟨848204, by rfl⟩ : syracuseStep 1130939 = 1696409) B1696409
theorem B1130999 : Blo 750330 1130999 := bstep (se 1 (by rfl) ⟨848249, by rfl⟩ : syracuseStep 1130999 = 1696499) B1696499
theorem B1131023 : Blo 750330 1131023 := bstep (se 1 (by rfl) ⟨848267, by rfl⟩ : syracuseStep 1131023 = 1696535) B1696535
theorem B1131065 : Blo 750330 1131065 := bstep (se 2 (by rfl) ⟨424149, by rfl⟩ : syracuseStep 1131065 = 848299) B848299
theorem B1131143 : Blo 750330 1131143 := bstep (se 1 (by rfl) ⟨848357, by rfl⟩ : syracuseStep 1131143 = 1696715) B1696715
theorem B1131179 : Blo 750330 1131179 := bstep (se 1 (by rfl) ⟨848384, by rfl⟩ : syracuseStep 1131179 = 1696769) B1696769
theorem B1098427 : Blo 750330 1098427 := bstep (se 1 (by rfl) ⟨823820, by rfl⟩ : syracuseStep 1098427 = 1647641) B1647641
theorem B3818177 : Blo 750330 3818177 := bstep (se 2 (by rfl) ⟨1431816, by rfl⟩ : syracuseStep 3818177 = 2863633) B2863633
theorem B1131209 : Blo 750330 1131209 := bstep (se 2 (by rfl) ⟨424203, by rfl⟩ : syracuseStep 1131209 = 848407) B848407
theorem B8143577 : Blo 750330 8143577 := bstep (se 2 (by rfl) ⟨3053841, by rfl⟩ : syracuseStep 8143577 = 6107683) B6107683
theorem B2147087 : Blo 750330 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B2540321 : Blo 750330 2540321 := bstep (se 2 (by rfl) ⟨952620, by rfl⟩ : syracuseStep 2540321 = 1905241) B1905241
theorem B1688363 : Blo 750330 1688363 := bstep (se 1 (by rfl) ⟨1266272, by rfl⟩ : syracuseStep 1688363 = 2532545) B2532545
theorem B1131323 : Blo 750330 1131323 := bstep (se 1 (by rfl) ⟨848492, by rfl⟩ : syracuseStep 1131323 = 1696985) B1696985
theorem B1131383 : Blo 750330 1131383 := bstep (se 1 (by rfl) ⟨848537, by rfl⟩ : syracuseStep 1131383 = 1697075) B1697075
theorem B803719 : Blo 750330 803719 := bstep (se 1 (by rfl) ⟨602789, by rfl⟩ : syracuseStep 803719 = 1205579) B1205579
theorem B1131407 : Blo 750330 1131407 := bstep (se 1 (by rfl) ⟨848555, by rfl⟩ : syracuseStep 1131407 = 1697111) B1697111
theorem B1131449 : Blo 750330 1131449 := bstep (se 2 (by rfl) ⟨424293, by rfl⟩ : syracuseStep 1131449 = 848587) B848587
theorem B1524779 : Blo 750330 1524779 := bstep (se 1 (by rfl) ⟨1143584, by rfl⟩ : syracuseStep 1524779 = 2287169) B2287169
theorem B1688723 : Blo 750330 1688723 := bstep (se 1 (by rfl) ⟨1266542, by rfl⟩ : syracuseStep 1688723 = 2533085) B2533085
theorem B1885331 : Blo 750330 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1688777 : Blo 750330 1688777 := bstep (se 2 (by rfl) ⟨633291, by rfl⟩ : syracuseStep 1688777 = 1266583) B1266583
theorem B2540915 : Blo 750330 2540915 := bstep (se 1 (by rfl) ⟨1905686, by rfl⟩ : syracuseStep 2540915 = 3811373) B3811373
theorem B1426835 : Blo 750330 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B1426889 : Blo 750330 1426889 := bstep (se 2 (by rfl) ⟨535083, by rfl⟩ : syracuseStep 1426889 = 1070167) B1070167
theorem B1426987 : Blo 750330 1426987 := bstep (se 1 (by rfl) ⟨1070240, by rfl⟩ : syracuseStep 1426987 = 2140481) B2140481
theorem B4277933 : Blo 750330 4277933 := bstep (se 3 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 4277933 = 1604225) B1604225
theorem B804539 : Blo 750330 804539 := bstep (se 1 (by rfl) ⟨603404, by rfl⟩ : syracuseStep 804539 = 1206809) B1206809
theorem B1427215 : Blo 750330 1427215 := bstep (se 1 (by rfl) ⟨1070411, by rfl⟩ : syracuseStep 1427215 = 2140823) B2140823
theorem B1689479 : Blo 750330 1689479 := bstep (se 1 (by rfl) ⟨1267109, by rfl⟩ : syracuseStep 1689479 = 2534219) B2534219
theorem B903083 : Blo 750330 903083 := bstep (se 1 (by rfl) ⟨677312, by rfl⟩ : syracuseStep 903083 = 1354625) B1354625
theorem B11552813 : Blo 750330 11552813 := bstep (se 3 (by rfl) ⟨2166152, by rfl⟩ : syracuseStep 11552813 = 4332305) B4332305
theorem B1689659 : Blo 750330 1689659 := bstep (se 1 (by rfl) ⟨1267244, by rfl⟩ : syracuseStep 1689659 = 2534489) B2534489
theorem B1689785 : Blo 750330 1689785 := bstep (se 2 (by rfl) ⟨633669, by rfl⟩ : syracuseStep 1689785 = 1267339) B1267339
theorem B8669645 : Blo 750330 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B1690127 : Blo 750330 1690127 := bstep (se 1 (by rfl) ⟨1267595, by rfl⟩ : syracuseStep 1690127 = 2535191) B2535191
theorem B1690145 : Blo 750330 1690145 := bstep (se 2 (by rfl) ⟨633804, by rfl⟩ : syracuseStep 1690145 = 1267609) B1267609
theorem B1690487 : Blo 750330 1690487 := bstep (se 1 (by rfl) ⟨1267865, by rfl⟩ : syracuseStep 1690487 = 2535731) B2535731
theorem B3623825 : Blo 750330 3623825 := bstep (se 2 (by rfl) ⟨1358934, by rfl⟩ : syracuseStep 3623825 = 2717869) B2717869
theorem B1690667 : Blo 750330 1690667 := bstep (se 1 (by rfl) ⟨1268000, by rfl⟩ : syracuseStep 1690667 = 2536001) B2536001
theorem B8244341 : Blo 750330 8244341 := bstep (se 5 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 8244341 = 772907) B772907
theorem B1428779 : Blo 750330 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B1691027 : Blo 750330 1691027 := bstep (se 1 (by rfl) ⟨1268270, by rfl⟩ : syracuseStep 1691027 = 2536541) B2536541
theorem B5787065 : Blo 750330 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B1691081 : Blo 750330 1691081 := bstep (se 2 (by rfl) ⟨634155, by rfl⟩ : syracuseStep 1691081 = 1268311) B1268311
theorem B5721677 : Blo 750330 5721677 := bstep (se 3 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 5721677 = 2145629) B2145629
theorem B2707145 : Blo 750330 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B2543507 : Blo 750330 2543507 := bstep (se 1 (by rfl) ⟨1907630, by rfl⟩ : syracuseStep 2543507 = 3815261) B3815261
theorem B10866635 : Blo 750330 10866635 := bstep (se 1 (by rfl) ⟨8149976, by rfl⟩ : syracuseStep 10866635 = 16299953) B16299953
theorem B4280323 : Blo 750330 4280323 := bstep (se 1 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 4280323 = 6420485) B6420485
theorem B1691783 : Blo 750330 1691783 := bstep (se 1 (by rfl) ⟨1268837, by rfl⟩ : syracuseStep 1691783 = 2537675) B2537675
theorem B4116653 : Blo 750330 4116653 := bstep (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) B1543745
theorem B1691963 : Blo 750330 1691963 := bstep (se 1 (by rfl) ⟨1268972, by rfl⟩ : syracuseStep 1691963 = 2537945) B2537945
theorem B1692089 : Blo 750330 1692089 := bstep (se 2 (by rfl) ⟨634533, by rfl⟩ : syracuseStep 1692089 = 1269067) B1269067
theorem B1692431 : Blo 750330 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B1692449 : Blo 750330 1692449 := bstep (se 2 (by rfl) ⟨634668, by rfl⟩ : syracuseStep 1692449 = 1269337) B1269337
theorem B1266475 : Blo 750330 1266475 := bstep (se 1 (by rfl) ⟨949856, by rfl⟩ : syracuseStep 1266475 = 1899713) B1899713
theorem B1069967 : Blo 750330 1069967 := bstep (se 1 (by rfl) ⟨802475, by rfl⟩ : syracuseStep 1069967 = 1604951) B1604951
theorem B1266617 : Blo 750330 1266617 := bstep (se 2 (by rfl) ⟨474981, by rfl⟩ : syracuseStep 1266617 = 949963) B949963
theorem B1430473 : Blo 750330 1430473 := bstep (se 2 (by rfl) ⟨536427, by rfl⟩ : syracuseStep 1430473 = 1072855) B1072855
theorem B1692791 : Blo 750330 1692791 := bstep (se 1 (by rfl) ⟨1269593, by rfl⟩ : syracuseStep 1692791 = 2539187) B2539187
theorem B2544911 : Blo 750330 2544911 := bstep (se 1 (by rfl) ⟨1908683, by rfl⟩ : syracuseStep 2544911 = 3817367) B3817367
theorem B1692971 : Blo 750330 1692971 := bstep (se 1 (by rfl) ⟨1269728, by rfl⟩ : syracuseStep 1692971 = 2539457) B2539457
theorem B2545181 : Blo 750330 2545181 := bstep (se 3 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 2545181 = 954443) B954443
theorem B2414141 : Blo 750330 2414141 := bstep (se 3 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 2414141 = 905303) B905303
theorem B1267319 : Blo 750330 1267319 := bstep (se 1 (by rfl) ⟨950489, by rfl⟩ : syracuseStep 1267319 = 1900979) B1900979
theorem B1693331 : Blo 750330 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B1693385 : Blo 750330 1693385 := bstep (se 2 (by rfl) ⟨635019, by rfl⟩ : syracuseStep 1693385 = 1270039) B1270039
theorem B5724107 : Blo 750330 5724107 := bstep (se 1 (by rfl) ⟨4293080, by rfl⟩ : syracuseStep 5724107 = 8586161) B8586161
theorem B2414603 : Blo 750330 2414603 := bstep (se 1 (by rfl) ⟨1810952, by rfl⟩ : syracuseStep 2414603 = 3621905) B3621905
theorem B1267771 : Blo 750330 1267771 := bstep (se 1 (by rfl) ⟨950828, by rfl⟩ : syracuseStep 1267771 = 1901657) B1901657
theorem B1267913 : Blo 750330 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B4282739 : Blo 750330 4282739 := bstep (se 1 (by rfl) ⟨3212054, by rfl⟩ : syracuseStep 4282739 = 6424109) B6424109
theorem B1694087 : Blo 750330 1694087 := bstep (se 1 (by rfl) ⟨1270565, by rfl⟩ : syracuseStep 1694087 = 2541131) B2541131
theorem B2710027 : Blo 750330 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B1694267 : Blo 750330 1694267 := bstep (se 1 (by rfl) ⟨1270700, by rfl⟩ : syracuseStep 1694267 = 2541401) B2541401
theorem B1694393 : Blo 750330 1694393 := bstep (se 2 (by rfl) ⟨635397, by rfl⟩ : syracuseStep 1694393 = 1270795) B1270795
theorem B1268615 : Blo 750330 1268615 := bstep (se 1 (by rfl) ⟨951461, by rfl⟩ : syracuseStep 1268615 = 1902923) B1902923
theorem B1694735 : Blo 750330 1694735 := bstep (se 1 (by rfl) ⟨1271051, by rfl⟩ : syracuseStep 1694735 = 2542103) B2542103
theorem B1694753 : Blo 750330 1694753 := bstep (se 2 (by rfl) ⟨635532, by rfl⟩ : syracuseStep 1694753 = 1271065) B1271065
theorem B1695095 : Blo 750330 1695095 := bstep (se 1 (by rfl) ⟨1271321, by rfl⟩ : syracuseStep 1695095 = 2542643) B2542643
theorem B1269263 : Blo 750330 1269263 := bstep (se 1 (by rfl) ⟨951947, by rfl⟩ : syracuseStep 1269263 = 1903895) B1903895
theorem B1695275 : Blo 750330 1695275 := bstep (se 1 (by rfl) ⟨1271456, by rfl⟩ : syracuseStep 1695275 = 2542913) B2542913
theorem B2416385 : Blo 750330 2416385 := bstep (se 2 (by rfl) ⟨906144, by rfl⟩ : syracuseStep 2416385 = 1812289) B1812289
theorem B4284197 : Blo 750330 4284197 := bstep (se 4 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 4284197 = 803287) B803287
theorem B14868269 : Blo 750330 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B2711411 : Blo 750330 2711411 := bstep (se 1 (by rfl) ⟨2033558, by rfl⟩ : syracuseStep 2711411 = 4067117) B4067117
theorem B1695635 : Blo 750330 1695635 := bstep (se 1 (by rfl) ⟨1271726, by rfl⟩ : syracuseStep 1695635 = 2543453) B2543453
theorem B1073083 : Blo 750330 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B1695689 : Blo 750330 1695689 := bstep (se 2 (by rfl) ⟨635883, by rfl⟩ : syracuseStep 1695689 = 1271767) B1271767
theorem B1269803 : Blo 750330 1269803 := bstep (se 1 (by rfl) ⟨952352, by rfl⟩ : syracuseStep 1269803 = 1904705) B1904705
theorem B1270201 : Blo 750330 1270201 := bstep (se 2 (by rfl) ⟨476325, by rfl⟩ : syracuseStep 1270201 = 952651) B952651
theorem B2712017 : Blo 750330 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B3858947 : Blo 750330 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B844303 : Blo 750330 844303 := bstep (se 1 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 844303 = 1266455) B1266455
theorem B4284971 : Blo 750330 4284971 := bstep (se 1 (by rfl) ⟨3213728, by rfl⟩ : syracuseStep 4284971 = 6427457) B6427457
theorem B1073783 : Blo 750330 1073783 := bstep (se 1 (by rfl) ⟨805337, by rfl⟩ : syracuseStep 1073783 = 1610675) B1610675
theorem B1696391 : Blo 750330 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B1696571 : Blo 750330 1696571 := bstep (se 1 (by rfl) ⟨1272428, by rfl⟩ : syracuseStep 1696571 = 2544857) B2544857
theorem B1696697 : Blo 750330 1696697 := bstep (se 2 (by rfl) ⟨636261, by rfl⟩ : syracuseStep 1696697 = 1272523) B1272523
theorem B844807 : Blo 750330 844807 := bstep (se 1 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 844807 = 1267211) B1267211
theorem B1270903 : Blo 750330 1270903 := bstep (se 1 (by rfl) ⟨953177, by rfl⟩ : syracuseStep 1270903 = 1906355) B1906355
theorem B7234733 : Blo 750330 7234733 := bstep (se 3 (by rfl) ⟨1356512, by rfl⟩ : syracuseStep 7234733 = 2713025) B2713025
theorem B844987 : Blo 750330 844987 := bstep (se 1 (by rfl) ⟨633740, by rfl⟩ : syracuseStep 844987 = 1267481) B1267481
theorem B1697039 : Blo 750330 1697039 := bstep (se 1 (by rfl) ⟨1272779, by rfl⟩ : syracuseStep 1697039 = 2545559) B2545559
theorem B1697057 : Blo 750330 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B1271099 : Blo 750330 1271099 := bstep (se 1 (by rfl) ⟨953324, by rfl⟩ : syracuseStep 1271099 = 1906649) B1906649
theorem B28894643 : Blo 750330 28894643 := bstep (se 1 (by rfl) ⟨21670982, by rfl⟩ : syracuseStep 28894643 = 43341965) B43341965
theorem B10872397 : Blo 750330 10872397 := bstep (se 3 (by rfl) ⟨2038574, by rfl⟩ : syracuseStep 10872397 = 4077149) B4077149
theorem B845455 : Blo 750330 845455 := bstep (se 1 (by rfl) ⟨634091, by rfl⟩ : syracuseStep 845455 = 1268183) B1268183
theorem B9758387 : Blo 750330 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B1271497 : Blo 750330 1271497 := bstep (se 2 (by rfl) ⟨476811, by rfl⟩ : syracuseStep 1271497 = 953623) B953623
theorem B1173305 : Blo 750330 1173305 := bstep (se 2 (by rfl) ⟨439989, by rfl⟩ : syracuseStep 1173305 = 879979) B879979
theorem B14444405 : Blo 750330 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B4286429 : Blo 750330 4286429 := bstep (se 3 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 4286429 = 1607411) B1607411
theorem B845959 : Blo 750330 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B1206571 : Blo 750330 1206571 := bstep (se 1 (by rfl) ⟨904928, by rfl⟩ : syracuseStep 1206571 = 1809857) B1809857
theorem B846139 : Blo 750330 846139 := bstep (se 1 (by rfl) ⟨634604, by rfl⟩ : syracuseStep 846139 = 1269209) B1269209
theorem B1272199 : Blo 750330 1272199 := bstep (se 1 (by rfl) ⟨954149, by rfl⟩ : syracuseStep 1272199 = 1908299) B1908299
theorem B4811521 : Blo 750330 4811521 := bstep (se 2 (by rfl) ⟨1804320, by rfl⟩ : syracuseStep 4811521 = 3608641) B3608641
theorem B846607 : Blo 750330 846607 := bstep (se 1 (by rfl) ⟨634955, by rfl⟩ : syracuseStep 846607 = 1269911) B1269911
theorem B5434127 : Blo 750330 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B1272847 : Blo 750330 1272847 := bstep (se 1 (by rfl) ⟨954635, by rfl⟩ : syracuseStep 1272847 = 1909271) B1909271
theorem B3206263 : Blo 750330 3206263 := bstep (se 1 (by rfl) ⟨2404697, by rfl⟩ : syracuseStep 3206263 = 4809395) B4809395
theorem B1240183 : Blo 750330 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B2059465 : Blo 750330 2059465 := bstep (se 2 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 2059465 = 1544599) B1544599
theorem B847111 : Blo 750330 847111 := bstep (se 1 (by rfl) ⟨635333, by rfl⟩ : syracuseStep 847111 = 1270667) B1270667
theorem B10874243 : Blo 750330 10874243 := bstep (se 1 (by rfl) ⟨8155682, by rfl⟩ : syracuseStep 10874243 = 16311365) B16311365
theorem B2289043 : Blo 750330 2289043 := bstep (se 1 (by rfl) ⟨1716782, by rfl⟩ : syracuseStep 2289043 = 3433565) B3433565
theorem B847291 : Blo 750330 847291 := bstep (se 1 (by rfl) ⟨635468, by rfl⟩ : syracuseStep 847291 = 1270937) B1270937
theorem B2289239 : Blo 750330 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B2649719 : Blo 750330 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B847759 : Blo 750330 847759 := bstep (se 1 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 847759 = 1271639) B1271639
theorem B14479307 : Blo 750330 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B1929217 : Blo 750330 1929217 := bstep (se 2 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 1929217 = 1446913) B1446913
theorem B9040187 : Blo 750330 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B848263 : Blo 750330 848263 := bstep (se 1 (by rfl) ⟨636197, by rfl⟩ : syracuseStep 848263 = 1272395) B1272395
theorem B24441365 : Blo 750330 24441365 := bstep (se 6 (by rfl) ⟨572844, by rfl⟩ : syracuseStep 24441365 = 1145689) B1145689
theorem B848443 : Blo 750330 848443 := bstep (se 1 (by rfl) ⟨636332, by rfl⟩ : syracuseStep 848443 = 1272665) B1272665
theorem B750343 : Blo 750330 750343 := bstep (se 1 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 750343 = 1125515) B1125515
theorem B750351 : Blo 750330 750351 := bstep (se 1 (by rfl) ⟨562763, by rfl⟩ : syracuseStep 750351 = 1125527) B1125527
theorem B5206799 : Blo 750330 5206799 := bstep (se 1 (by rfl) ⟨3905099, by rfl⟩ : syracuseStep 5206799 = 7810199) B7810199
theorem B750395 : Blo 750330 750395 := bstep (se 1 (by rfl) ⟨562796, by rfl⟩ : syracuseStep 750395 = 1125593) B1125593
theorem B750471 : Blo 750330 750471 := bstep (se 1 (by rfl) ⟨562853, by rfl⟩ : syracuseStep 750471 = 1125707) B1125707
theorem B750479 : Blo 750330 750479 := bstep (se 1 (by rfl) ⟨562859, by rfl⟩ : syracuseStep 750479 = 1125719) B1125719
theorem B3044243 : Blo 750330 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B750523 : Blo 750330 750523 := bstep (se 1 (by rfl) ⟨562892, by rfl⟩ : syracuseStep 750523 = 1125785) B1125785
theorem B750599 : Blo 750330 750599 := bstep (se 1 (by rfl) ⟨562949, by rfl⟩ : syracuseStep 750599 = 1125899) B1125899
theorem B750607 : Blo 750330 750607 := bstep (se 1 (by rfl) ⟨562955, by rfl⟩ : syracuseStep 750607 = 1125911) B1125911
theorem B1143823 : Blo 750330 1143823 := bstep (se 1 (by rfl) ⟨857867, by rfl⟩ : syracuseStep 1143823 = 1715735) B1715735
theorem B1602593 : Blo 750330 1602593 := bstep (se 2 (by rfl) ⟨600972, by rfl⟩ : syracuseStep 1602593 = 1201945) B1201945
theorem B750651 : Blo 750330 750651 := bstep (se 1 (by rfl) ⟨562988, by rfl⟩ : syracuseStep 750651 = 1125977) B1125977
theorem B4289597 : Blo 750330 4289597 := bstep (se 3 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 4289597 = 1608599) B1608599
theorem B1602679 : Blo 750330 1602679 := bstep (se 1 (by rfl) ⟨1202009, by rfl⟩ : syracuseStep 1602679 = 2404019) B2404019
theorem B9139333 : Blo 750330 9139333 := bstep (se 4 (by rfl) ⟨856812, by rfl⟩ : syracuseStep 9139333 = 1713625) B1713625
theorem B750727 : Blo 750330 750727 := bstep (se 1 (by rfl) ⟨563045, by rfl⟩ : syracuseStep 750727 = 1126091) B1126091
theorem B750735 : Blo 750330 750735 := bstep (se 1 (by rfl) ⟨563051, by rfl⟩ : syracuseStep 750735 = 1126103) B1126103
theorem B750779 : Blo 750330 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B3863789 : Blo 750330 3863789 := bstep (se 3 (by rfl) ⟨724460, by rfl⟩ : syracuseStep 3863789 = 1448921) B1448921
theorem B750855 : Blo 750330 750855 := bstep (se 1 (by rfl) ⟨563141, by rfl⟩ : syracuseStep 750855 = 1126283) B1126283
theorem B750863 : Blo 750330 750863 := bstep (se 1 (by rfl) ⟨563147, by rfl⟩ : syracuseStep 750863 = 1126295) B1126295
theorem B750907 : Blo 750330 750907 := bstep (se 1 (by rfl) ⟨563180, by rfl⟩ : syracuseStep 750907 = 1126361) B1126361
theorem B750983 : Blo 750330 750983 := bstep (se 1 (by rfl) ⟨563237, by rfl⟩ : syracuseStep 750983 = 1126475) B1126475
theorem B750991 : Blo 750330 750991 := bstep (se 1 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 750991 = 1126487) B1126487
theorem B751035 : Blo 750330 751035 := bstep (se 1 (by rfl) ⟨563276, by rfl⟩ : syracuseStep 751035 = 1126553) B1126553
theorem B751111 : Blo 750330 751111 := bstep (se 1 (by rfl) ⟨563333, by rfl⟩ : syracuseStep 751111 = 1126667) B1126667
theorem B751119 : Blo 750330 751119 := bstep (se 1 (by rfl) ⟨563339, by rfl⟩ : syracuseStep 751119 = 1126679) B1126679
theorem B751163 : Blo 750330 751163 := bstep (se 1 (by rfl) ⟨563372, by rfl⟩ : syracuseStep 751163 = 1126745) B1126745
theorem B1832507 : Blo 750330 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B751239 : Blo 750330 751239 := bstep (se 1 (by rfl) ⟨563429, by rfl⟩ : syracuseStep 751239 = 1126859) B1126859
theorem B751247 : Blo 750330 751247 := bstep (se 1 (by rfl) ⟨563435, by rfl⟩ : syracuseStep 751247 = 1126871) B1126871
theorem B751291 : Blo 750330 751291 := bstep (se 1 (by rfl) ⟨563468, by rfl⟩ : syracuseStep 751291 = 1126937) B1126937
theorem B751367 : Blo 750330 751367 := bstep (se 1 (by rfl) ⟨563525, by rfl⟩ : syracuseStep 751367 = 1127051) B1127051
theorem B751375 : Blo 750330 751375 := bstep (se 1 (by rfl) ⟨563531, by rfl⟩ : syracuseStep 751375 = 1127063) B1127063
theorem B751419 : Blo 750330 751419 := bstep (se 1 (by rfl) ⟨563564, by rfl⟩ : syracuseStep 751419 = 1127129) B1127129
theorem B3798899 : Blo 750330 3798899 := bstep (se 1 (by rfl) ⟨2849174, by rfl⟩ : syracuseStep 3798899 = 5698349) B5698349
theorem B751495 : Blo 750330 751495 := bstep (se 1 (by rfl) ⟨563621, by rfl⟩ : syracuseStep 751495 = 1127243) B1127243
theorem B751503 : Blo 750330 751503 := bstep (se 1 (by rfl) ⟨563627, by rfl⟩ : syracuseStep 751503 = 1127255) B1127255
theorem B751547 : Blo 750330 751547 := bstep (se 1 (by rfl) ⟨563660, by rfl⟩ : syracuseStep 751547 = 1127321) B1127321
theorem B751623 : Blo 750330 751623 := bstep (se 1 (by rfl) ⟨563717, by rfl⟩ : syracuseStep 751623 = 1127435) B1127435
theorem B751631 : Blo 750330 751631 := bstep (se 1 (by rfl) ⟨563723, by rfl⟩ : syracuseStep 751631 = 1127447) B1127447
theorem B751675 : Blo 750330 751675 := bstep (se 1 (by rfl) ⟨563756, by rfl⟩ : syracuseStep 751675 = 1127513) B1127513
theorem B751751 : Blo 750330 751751 := bstep (se 1 (by rfl) ⟨563813, by rfl⟩ : syracuseStep 751751 = 1127627) B1127627
theorem B751759 : Blo 750330 751759 := bstep (se 1 (by rfl) ⟨563819, by rfl⟩ : syracuseStep 751759 = 1127639) B1127639
theorem B751803 : Blo 750330 751803 := bstep (se 1 (by rfl) ⟨563852, by rfl⟩ : syracuseStep 751803 = 1127705) B1127705
theorem B751879 : Blo 750330 751879 := bstep (se 1 (by rfl) ⟨563909, by rfl⟩ : syracuseStep 751879 = 1127819) B1127819
theorem B2849039 : Blo 750330 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B751887 : Blo 750330 751887 := bstep (se 1 (by rfl) ⟨563915, by rfl⟩ : syracuseStep 751887 = 1127831) B1127831
theorem B751931 : Blo 750330 751931 := bstep (se 1 (by rfl) ⟨563948, by rfl⟩ : syracuseStep 751931 = 1127897) B1127897
theorem B3799385 : Blo 750330 3799385 := bstep (se 2 (by rfl) ⟨1424769, by rfl⟩ : syracuseStep 3799385 = 2849539) B2849539
theorem B752007 : Blo 750330 752007 := bstep (se 1 (by rfl) ⟨564005, by rfl⟩ : syracuseStep 752007 = 1128011) B1128011
theorem B752015 : Blo 750330 752015 := bstep (se 1 (by rfl) ⟨564011, by rfl⟩ : syracuseStep 752015 = 1128023) B1128023
theorem B752059 : Blo 750330 752059 := bstep (se 1 (by rfl) ⟨564044, by rfl⟩ : syracuseStep 752059 = 1128089) B1128089
theorem B752135 : Blo 750330 752135 := bstep (se 1 (by rfl) ⟨564101, by rfl⟩ : syracuseStep 752135 = 1128203) B1128203
theorem B752143 : Blo 750330 752143 := bstep (se 1 (by rfl) ⟨564107, by rfl⟩ : syracuseStep 752143 = 1128215) B1128215
theorem B752187 : Blo 750330 752187 := bstep (se 1 (by rfl) ⟨564140, by rfl⟩ : syracuseStep 752187 = 1128281) B1128281
theorem B752263 : Blo 750330 752263 := bstep (se 1 (by rfl) ⟨564197, by rfl⟩ : syracuseStep 752263 = 1128395) B1128395
theorem B752271 : Blo 750330 752271 := bstep (se 1 (by rfl) ⟨564203, by rfl⟩ : syracuseStep 752271 = 1128407) B1128407
theorem B752315 : Blo 750330 752315 := bstep (se 1 (by rfl) ⟨564236, by rfl⟩ : syracuseStep 752315 = 1128473) B1128473
theorem B1833673 : Blo 750330 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B8551169 : Blo 750330 8551169 := bstep (se 2 (by rfl) ⟨3206688, by rfl⟩ : syracuseStep 8551169 = 6413377) B6413377
theorem B752391 : Blo 750330 752391 := bstep (se 1 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 752391 = 1128587) B1128587
theorem B752399 : Blo 750330 752399 := bstep (se 1 (by rfl) ⟨564299, by rfl⟩ : syracuseStep 752399 = 1128599) B1128599
theorem B752443 : Blo 750330 752443 := bstep (se 1 (by rfl) ⟨564332, by rfl⟩ : syracuseStep 752443 = 1128665) B1128665
theorem B752519 : Blo 750330 752519 := bstep (se 1 (by rfl) ⟨564389, by rfl⟩ : syracuseStep 752519 = 1128779) B1128779
theorem B752527 : Blo 750330 752527 := bstep (se 1 (by rfl) ⟨564395, by rfl⟩ : syracuseStep 752527 = 1128791) B1128791
theorem B752571 : Blo 750330 752571 := bstep (se 1 (by rfl) ⟨564428, by rfl⟩ : syracuseStep 752571 = 1128857) B1128857
theorem B1899521 : Blo 750330 1899521 := bstep (se 2 (by rfl) ⟨712320, by rfl⟩ : syracuseStep 1899521 = 1424641) B1424641
theorem B752647 : Blo 750330 752647 := bstep (se 1 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 752647 = 1128971) B1128971
theorem B752655 : Blo 750330 752655 := bstep (se 1 (by rfl) ⟨564491, by rfl⟩ : syracuseStep 752655 = 1128983) B1128983
theorem B752699 : Blo 750330 752699 := bstep (se 1 (by rfl) ⟨564524, by rfl⟩ : syracuseStep 752699 = 1129049) B1129049
theorem B752775 : Blo 750330 752775 := bstep (se 1 (by rfl) ⟨564581, by rfl⟩ : syracuseStep 752775 = 1129163) B1129163
theorem B752783 : Blo 750330 752783 := bstep (se 1 (by rfl) ⟨564587, by rfl⟩ : syracuseStep 752783 = 1129175) B1129175
theorem B752827 : Blo 750330 752827 := bstep (se 1 (by rfl) ⟨564620, by rfl⟩ : syracuseStep 752827 = 1129241) B1129241
theorem B752903 : Blo 750330 752903 := bstep (se 1 (by rfl) ⟨564677, by rfl⟩ : syracuseStep 752903 = 1129355) B1129355
theorem B752911 : Blo 750330 752911 := bstep (se 1 (by rfl) ⟨564683, by rfl⟩ : syracuseStep 752911 = 1129367) B1129367
theorem B752955 : Blo 750330 752955 := bstep (se 1 (by rfl) ⟨564716, by rfl⟩ : syracuseStep 752955 = 1129433) B1129433
theorem B1375547 : Blo 750330 1375547 := bstep (se 1 (by rfl) ⟨1031660, by rfl⟩ : syracuseStep 1375547 = 2063321) B2063321
theorem B1899895 : Blo 750330 1899895 := bstep (se 1 (by rfl) ⟨1424921, by rfl⟩ : syracuseStep 1899895 = 2849843) B2849843
theorem B949639 : Blo 750330 949639 := bstep (se 1 (by rfl) ⟨712229, by rfl⟩ : syracuseStep 949639 = 1424459) B1424459
theorem B753031 : Blo 750330 753031 := bstep (se 1 (by rfl) ⟨564773, by rfl⟩ : syracuseStep 753031 = 1129547) B1129547
theorem B753039 : Blo 750330 753039 := bstep (se 1 (by rfl) ⟨564779, by rfl⟩ : syracuseStep 753039 = 1129559) B1129559
theorem B4291987 : Blo 750330 4291987 := bstep (se 1 (by rfl) ⟨3218990, by rfl⟩ : syracuseStep 4291987 = 6437981) B6437981
theorem B753083 : Blo 750330 753083 := bstep (se 1 (by rfl) ⟨564812, by rfl⟩ : syracuseStep 753083 = 1129625) B1129625
theorem B753159 : Blo 750330 753159 := bstep (se 1 (by rfl) ⟨564869, by rfl⟩ : syracuseStep 753159 = 1129739) B1129739
theorem B753167 : Blo 750330 753167 := bstep (se 1 (by rfl) ⟨564875, by rfl⟩ : syracuseStep 753167 = 1129751) B1129751
theorem B753211 : Blo 750330 753211 := bstep (se 1 (by rfl) ⟨564908, by rfl⟩ : syracuseStep 753211 = 1129817) B1129817
theorem B753287 : Blo 750330 753287 := bstep (se 1 (by rfl) ⟨564965, by rfl⟩ : syracuseStep 753287 = 1129931) B1129931
theorem B753295 : Blo 750330 753295 := bstep (se 1 (by rfl) ⟨564971, by rfl⟩ : syracuseStep 753295 = 1129943) B1129943
theorem B753339 : Blo 750330 753339 := bstep (se 1 (by rfl) ⟨565004, by rfl⟩ : syracuseStep 753339 = 1130009) B1130009
theorem B753415 : Blo 750330 753415 := bstep (se 1 (by rfl) ⟨565061, by rfl⟩ : syracuseStep 753415 = 1130123) B1130123
theorem B753423 : Blo 750330 753423 := bstep (se 1 (by rfl) ⟨565067, by rfl⟩ : syracuseStep 753423 = 1130135) B1130135
theorem B950059 : Blo 750330 950059 := bstep (se 1 (by rfl) ⟨712544, by rfl⟩ : syracuseStep 950059 = 1425089) B1425089
theorem B1900331 : Blo 750330 1900331 := bstep (se 1 (by rfl) ⟨1425248, by rfl⟩ : syracuseStep 1900331 = 2850497) B2850497
theorem B2031419 : Blo 750330 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B753467 : Blo 750330 753467 := bstep (se 1 (by rfl) ⟨565100, by rfl⟩ : syracuseStep 753467 = 1130201) B1130201
theorem B16514891 : Blo 750330 16514891 := bstep (se 1 (by rfl) ⟨12386168, by rfl⟩ : syracuseStep 16514891 = 24772337) B24772337
theorem B753543 : Blo 750330 753543 := bstep (se 1 (by rfl) ⟨565157, by rfl⟩ : syracuseStep 753543 = 1130315) B1130315
theorem B753551 : Blo 750330 753551 := bstep (se 1 (by rfl) ⟨565163, by rfl⟩ : syracuseStep 753551 = 1130327) B1130327
theorem B753595 : Blo 750330 753595 := bstep (se 1 (by rfl) ⟨565196, by rfl⟩ : syracuseStep 753595 = 1130393) B1130393
theorem B10846223 : Blo 750330 10846223 := bstep (se 1 (by rfl) ⟨8134667, by rfl⟩ : syracuseStep 10846223 = 16269335) B16269335
theorem B753703 : Blo 750330 753703 := bstep (se 1 (by rfl) ⟨565277, by rfl⟩ : syracuseStep 753703 = 1130555) B1130555
theorem B753743 : Blo 750330 753743 := bstep (se 1 (by rfl) ⟨565307, by rfl⟩ : syracuseStep 753743 = 1130615) B1130615
theorem B753759 : Blo 750330 753759 := bstep (se 1 (by rfl) ⟨565319, by rfl⟩ : syracuseStep 753759 = 1130639) B1130639
theorem B753787 : Blo 750330 753787 := bstep (se 1 (by rfl) ⟨565340, by rfl⟩ : syracuseStep 753787 = 1130681) B1130681
theorem B753839 : Blo 750330 753839 := bstep (se 1 (by rfl) ⟨565379, by rfl⟩ : syracuseStep 753839 = 1130759) B1130759
theorem B8552627 : Blo 750330 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B753863 : Blo 750330 753863 := bstep (se 1 (by rfl) ⟨565397, by rfl⟩ : syracuseStep 753863 = 1130795) B1130795
theorem B753883 : Blo 750330 753883 := bstep (se 1 (by rfl) ⟨565412, by rfl⟩ : syracuseStep 753883 = 1130825) B1130825
theorem B753959 : Blo 750330 753959 := bstep (se 1 (by rfl) ⟨565469, by rfl⟩ : syracuseStep 753959 = 1130939) B1130939
theorem B753999 : Blo 750330 753999 := bstep (se 1 (by rfl) ⟨565499, by rfl⟩ : syracuseStep 753999 = 1130999) B1130999
theorem B754015 : Blo 750330 754015 := bstep (se 1 (by rfl) ⟨565511, by rfl⟩ : syracuseStep 754015 = 1131023) B1131023
theorem B754043 : Blo 750330 754043 := bstep (se 1 (by rfl) ⟨565532, by rfl⟩ : syracuseStep 754043 = 1131065) B1131065
theorem B754095 : Blo 750330 754095 := bstep (se 1 (by rfl) ⟨565571, by rfl⟩ : syracuseStep 754095 = 1131143) B1131143
theorem B754119 : Blo 750330 754119 := bstep (se 1 (by rfl) ⟨565589, by rfl⟩ : syracuseStep 754119 = 1131179) B1131179
theorem B754139 : Blo 750330 754139 := bstep (se 1 (by rfl) ⟨565604, by rfl⟩ : syracuseStep 754139 = 1131209) B1131209
theorem B754215 : Blo 750330 754215 := bstep (se 1 (by rfl) ⟨565661, by rfl⟩ : syracuseStep 754215 = 1131323) B1131323
theorem B754255 : Blo 750330 754255 := bstep (se 1 (by rfl) ⟨565691, by rfl⟩ : syracuseStep 754255 = 1131383) B1131383
theorem B754271 : Blo 750330 754271 := bstep (se 1 (by rfl) ⟨565703, by rfl⟩ : syracuseStep 754271 = 1131407) B1131407
theorem B754299 : Blo 750330 754299 := bstep (se 1 (by rfl) ⟨565724, by rfl⟩ : syracuseStep 754299 = 1131449) B1131449
theorem B4064003 : Blo 750330 4064003 := bstep (se 1 (by rfl) ⟨3048002, by rfl⟩ : syracuseStep 4064003 = 6096005) B6096005
theorem B1901495 : Blo 750330 1901495 := bstep (se 1 (by rfl) ⟨1426121, by rfl⟩ : syracuseStep 1901495 = 2852243) B2852243
theorem B951259 : Blo 750330 951259 := bstep (se 1 (by rfl) ⟨713444, by rfl⟩ : syracuseStep 951259 = 1426889) B1426889
theorem B2753551 : Blo 750330 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B5702723 : Blo 750330 5702723 := bstep (se 1 (by rfl) ⟨4277042, by rfl⟩ : syracuseStep 5702723 = 8554085) B8554085
theorem B2851955 : Blo 750330 2851955 := bstep (se 1 (by rfl) ⟨2138966, by rfl⟩ : syracuseStep 2851955 = 4277933) B4277933
theorem B7079183 : Blo 750330 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B7701875 : Blo 750330 7701875 := bstep (se 1 (by rfl) ⟨5776406, by rfl⟩ : syracuseStep 7701875 = 11552813) B11552813
theorem B12191431 : Blo 750330 12191431 := bstep (se 1 (by rfl) ⟨9143573, by rfl⟩ : syracuseStep 12191431 = 18287147) B18287147
theorem B1902599 : Blo 750330 1902599 := bstep (se 1 (by rfl) ⟨1426949, by rfl⟩ : syracuseStep 1902599 = 2853899) B2853899
theorem B5703695 : Blo 750330 5703695 := bstep (se 1 (by rfl) ⟨4277771, by rfl⟩ : syracuseStep 5703695 = 8555543) B8555543
theorem B1902649 : Blo 750330 1902649 := bstep (se 2 (by rfl) ⟨713493, by rfl⟩ : syracuseStep 1902649 = 1426987) B1426987
theorem B4950245 : Blo 750330 4950245 := bstep (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) B928171
theorem B1902953 : Blo 750330 1902953 := bstep (se 2 (by rfl) ⟨713607, by rfl⟩ : syracuseStep 1902953 = 1427215) B1427215
theorem B2853245 : Blo 750330 2853245 := bstep (se 3 (by rfl) ⟨534983, by rfl⟩ : syracuseStep 2853245 = 1069967) B1069967
theorem B1804763 : Blo 750330 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B4295177 : Blo 750330 4295177 := bstep (se 2 (by rfl) ⟨1610691, by rfl⟩ : syracuseStep 4295177 = 3221383) B3221383
theorem B7244423 : Blo 750330 7244423 := bstep (se 1 (by rfl) ⟨5433317, by rfl⟩ : syracuseStep 7244423 = 10866635) B10866635
theorem B1608761 : Blo 750330 1608761 := bstep (se 2 (by rfl) ⟨603285, by rfl⟩ : syracuseStep 1608761 = 1206571) B1206571
theorem B3804407 : Blo 750330 3804407 := bstep (se 1 (by rfl) ⟨2853305, by rfl⟩ : syracuseStep 3804407 = 5706611) B5706611
theorem B18320705 : Blo 750330 18320705 := bstep (se 2 (by rfl) ⟨6870264, by rfl⟩ : syracuseStep 18320705 = 13740529) B13740529
theorem B3608027 : Blo 750330 3608027 := bstep (se 1 (by rfl) ⟨2706020, by rfl⟩ : syracuseStep 3608027 = 5412041) B5412041
theorem B1609427 : Blo 750330 1609427 := bstep (se 1 (by rfl) ⟨1207070, by rfl⟩ : syracuseStep 1609427 = 2414141) B2414141
theorem B3804893 : Blo 750330 3804893 := bstep (se 3 (by rfl) ⟨713417, by rfl⟩ : syracuseStep 3804893 = 1426835) B1426835
theorem B36507509 : Blo 750330 36507509 := bstep (se 5 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 36507509 = 3422579) B3422579
theorem B1609735 : Blo 750330 1609735 := bstep (se 1 (by rfl) ⟨1207301, by rfl⟩ : syracuseStep 1609735 = 2414603) B2414603
theorem B3969181 : Blo 750330 3969181 := bstep (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) B1488443
theorem B2855159 : Blo 750330 2855159 := bstep (se 1 (by rfl) ⟨2141369, by rfl⟩ : syracuseStep 2855159 = 4282739) B4282739
theorem B1905191 : Blo 750330 1905191 := bstep (se 1 (by rfl) ⟨1428893, by rfl⟩ : syracuseStep 1905191 = 2857787) B2857787
theorem B1905515 : Blo 750330 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B7214129 : Blo 750330 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B1610923 : Blo 750330 1610923 := bstep (se 1 (by rfl) ⟨1208192, by rfl⟩ : syracuseStep 1610923 = 2416385) B2416385
theorem B2856131 : Blo 750330 2856131 := bstep (se 1 (by rfl) ⟨2142098, by rfl⟩ : syracuseStep 2856131 = 4284197) B4284197
theorem B1807607 : Blo 750330 1807607 := bstep (se 1 (by rfl) ⟨1355705, by rfl⟩ : syracuseStep 1807607 = 2711411) B2711411
theorem B5707097 : Blo 750330 5707097 := bstep (se 2 (by rfl) ⟨2140161, by rfl⟩ : syracuseStep 5707097 = 4280323) B4280323
theorem B1906163 : Blo 750330 1906163 := bstep (se 1 (by rfl) ⟨1429622, by rfl⟩ : syracuseStep 1906163 = 2859245) B2859245
theorem B1808011 : Blo 750330 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B2856647 : Blo 750330 2856647 := bstep (se 1 (by rfl) ⟨2142485, by rfl⟩ : syracuseStep 2856647 = 4284971) B4284971
theorem B1906375 : Blo 750330 1906375 := bstep (se 1 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 1906375 = 2859563) B2859563
theorem B3610487 : Blo 750330 3610487 := bstep (se 1 (by rfl) ⟨2707865, by rfl⟩ : syracuseStep 3610487 = 5415731) B5415731
theorem B4823155 : Blo 750330 4823155 := bstep (se 1 (by rfl) ⟨3617366, by rfl⟩ : syracuseStep 4823155 = 7234733) B7234733
theorem B1907297 : Blo 750330 1907297 := bstep (se 2 (by rfl) ⟨715236, by rfl⟩ : syracuseStep 1907297 = 1430473) B1430473
theorem B2857619 : Blo 750330 2857619 := bstep (se 1 (by rfl) ⟨2143214, by rfl⟩ : syracuseStep 2857619 = 4286429) B4286429
theorem B1809145 : Blo 750330 1809145 := bstep (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) B1356859
theorem B2136905 : Blo 750330 2136905 := bstep (se 2 (by rfl) ⟨801339, by rfl⟩ : syracuseStep 2136905 = 1602679) B1602679
theorem B2857801 : Blo 750330 2857801 := bstep (se 2 (by rfl) ⟨1071675, by rfl⟩ : syracuseStep 2857801 = 2143351) B2143351
theorem B9641389 : Blo 750330 9641389 := bstep (se 3 (by rfl) ⟨1807760, by rfl⟩ : syracuseStep 9641389 = 3615521) B3615521
theorem B7249495 : Blo 750330 7249495 := bstep (se 1 (by rfl) ⟨5437121, by rfl⟩ : syracuseStep 7249495 = 10874243) B10874243
theorem B5709527 : Blo 750330 5709527 := bstep (se 1 (by rfl) ⟨4282145, by rfl⟩ : syracuseStep 5709527 = 8564291) B8564291
theorem B1449721 : Blo 750330 1449721 := bstep (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) B1087291
theorem B1908755 : Blo 750330 1908755 := bstep (se 1 (by rfl) ⟨1431566, by rfl⟩ : syracuseStep 1908755 = 2863133) B2863133
theorem B16294243 : Blo 750330 16294243 := bstep (se 1 (by rfl) ⟨12220682, by rfl⟩ : syracuseStep 16294243 = 24441365) B24441365
theorem B3613369 : Blo 750330 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B2859731 : Blo 750330 2859731 := bstep (se 1 (by rfl) ⟨2144798, by rfl⟩ : syracuseStep 2859731 = 4289597) B4289597
theorem B3810077 : Blo 750330 3810077 := bstep (se 3 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 3810077 = 1428779) B1428779
theorem B3089335 : Blo 750330 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B1221671 : Blo 750330 1221671 := bstep (se 1 (by rfl) ⟨916253, by rfl⟩ : syracuseStep 1221671 = 1832507) B1832507
theorem B29664461 : Blo 750330 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B2532599 : Blo 750330 2532599 := bstep (se 1 (by rfl) ⟨1899449, by rfl⟩ : syracuseStep 2532599 = 3798899) B3798899
theorem B2532923 : Blo 750330 2532923 := bstep (se 1 (by rfl) ⟨1899692, by rfl⟩ : syracuseStep 2532923 = 3799385) B3799385
theorem B3221315 : Blo 750330 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B2533193 : Blo 750330 2533193 := bstep (se 2 (by rfl) ⟨949947, by rfl⟩ : syracuseStep 2533193 = 1899895) B1899895
theorem B54929411 : Blo 750330 54929411 := bstep (se 1 (by rfl) ⟨41197058, by rfl⟩ : syracuseStep 54929411 = 82394117) B82394117
theorem B6432857 : Blo 750330 6432857 := bstep (se 2 (by rfl) ⟨2412321, by rfl⟩ : syracuseStep 6432857 = 4824643) B4824643
theorem B5417117 : Blo 750330 5417117 := bstep (se 3 (by rfl) ⟨1015709, by rfl⟩ : syracuseStep 5417117 = 2031419) B2031419
theorem B1288553 : Blo 750330 1288553 := bstep (se 2 (by rfl) ⟨483207, by rfl⟩ : syracuseStep 1288553 = 966415) B966415
theorem B5712443 : Blo 750330 5712443 := bstep (se 1 (by rfl) ⟨4284332, by rfl⟩ : syracuseStep 5712443 = 8568665) B8568665
theorem B1354639 : Blo 750330 1354639 := bstep (se 1 (by rfl) ⟨1015979, by rfl⟩ : syracuseStep 1354639 = 2031959) B2031959
theorem B2534327 : Blo 750330 2534327 := bstep (se 1 (by rfl) ⟨1900745, by rfl⟩ : syracuseStep 2534327 = 3801491) B3801491
theorem B2862161 : Blo 750330 2862161 := bstep (se 2 (by rfl) ⟨1073310, by rfl⟩ : syracuseStep 2862161 = 2146621) B2146621
theorem B16264309 : Blo 750330 16264309 := bstep (se 5 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 16264309 = 1524779) B1524779
theorem B1125575 : Blo 750330 1125575 := bstep (se 1 (by rfl) ⟨844181, by rfl⟩ : syracuseStep 1125575 = 1688363) B1688363
theorem B1125737 : Blo 750330 1125737 := bstep (se 2 (by rfl) ⟨422151, by rfl⟩ : syracuseStep 1125737 = 844303) B844303
theorem B2862479 : Blo 750330 2862479 := bstep (se 1 (by rfl) ⟨2146859, by rfl⟩ : syracuseStep 2862479 = 4293719) B4293719
theorem B1125815 : Blo 750330 1125815 := bstep (se 1 (by rfl) ⟨844361, by rfl⟩ : syracuseStep 1125815 = 1688723) B1688723
theorem B1256887 : Blo 750330 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B1125851 : Blo 750330 1125851 := bstep (se 1 (by rfl) ⟨844388, by rfl⟩ : syracuseStep 1125851 = 1688777) B1688777
theorem B2534921 : Blo 750330 2534921 := bstep (se 2 (by rfl) ⟨950595, by rfl⟩ : syracuseStep 2534921 = 1901191) B1901191
theorem B4566851 : Blo 750330 4566851 := bstep (se 1 (by rfl) ⟨3425138, by rfl⟩ : syracuseStep 4566851 = 6850277) B6850277
theorem B1355663 : Blo 750330 1355663 := bstep (se 1 (by rfl) ⟨1016747, by rfl⟩ : syracuseStep 1355663 = 2033495) B2033495
theorem B1126319 : Blo 750330 1126319 := bstep (se 1 (by rfl) ⟨844739, by rfl⟩ : syracuseStep 1126319 = 1689479) B1689479
theorem B1126409 : Blo 750330 1126409 := bstep (se 2 (by rfl) ⟨422403, by rfl⟩ : syracuseStep 1126409 = 844807) B844807
theorem B1126439 : Blo 750330 1126439 := bstep (se 1 (by rfl) ⟨844829, by rfl⟩ : syracuseStep 1126439 = 1689659) B1689659
theorem B1355815 : Blo 750330 1355815 := bstep (se 1 (by rfl) ⟨1016861, by rfl⟩ : syracuseStep 1355815 = 2033723) B2033723
theorem B1126523 : Blo 750330 1126523 := bstep (se 1 (by rfl) ⟨844892, by rfl⟩ : syracuseStep 1126523 = 1689785) B1689785
theorem B2404505 : Blo 750330 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B1126649 : Blo 750330 1126649 := bstep (se 2 (by rfl) ⟨422493, by rfl⟩ : syracuseStep 1126649 = 844987) B844987
theorem B5779763 : Blo 750330 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B2863421 : Blo 750330 2863421 := bstep (se 3 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 2863421 = 1073783) B1073783
theorem B1126751 : Blo 750330 1126751 := bstep (se 1 (by rfl) ⟨845063, by rfl⟩ : syracuseStep 1126751 = 1690127) B1690127
theorem B2535785 : Blo 750330 2535785 := bstep (se 2 (by rfl) ⟨950919, by rfl⟩ : syracuseStep 2535785 = 1901839) B1901839
theorem B1126763 : Blo 750330 1126763 := bstep (se 1 (by rfl) ⟨845072, by rfl⟩ : syracuseStep 1126763 = 1690145) B1690145
theorem B2404903 : Blo 750330 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B1126991 : Blo 750330 1126991 := bstep (se 1 (by rfl) ⟨845243, by rfl⟩ : syracuseStep 1126991 = 1690487) B1690487
theorem B1127111 : Blo 750330 1127111 := bstep (se 1 (by rfl) ⟨845333, by rfl⟩ : syracuseStep 1127111 = 1690667) B1690667
theorem B14496529 : Blo 750330 14496529 := bstep (se 2 (by rfl) ⟨5436198, by rfl⟩ : syracuseStep 14496529 = 10872397) B10872397
theorem B1127273 : Blo 750330 1127273 := bstep (se 2 (by rfl) ⟨422727, by rfl⟩ : syracuseStep 1127273 = 845455) B845455
theorem B1127351 : Blo 750330 1127351 := bstep (se 1 (by rfl) ⟨845513, by rfl⟩ : syracuseStep 1127351 = 1691027) B1691027
theorem B2536379 : Blo 750330 2536379 := bstep (se 1 (by rfl) ⟨1902284, by rfl⟩ : syracuseStep 2536379 = 3804569) B3804569
theorem B1127387 : Blo 750330 1127387 := bstep (se 1 (by rfl) ⟨845540, by rfl⟩ : syracuseStep 1127387 = 1691081) B1691081
theorem B3814451 : Blo 750330 3814451 := bstep (se 1 (by rfl) ⟨2860838, by rfl⟩ : syracuseStep 3814451 = 5721677) B5721677
theorem B1127855 : Blo 750330 1127855 := bstep (se 1 (by rfl) ⟨845891, by rfl⟩ : syracuseStep 1127855 = 1691783) B1691783
theorem B1127945 : Blo 750330 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B1127975 : Blo 750330 1127975 := bstep (se 1 (by rfl) ⟨845981, by rfl⟩ : syracuseStep 1127975 = 1691963) B1691963
theorem B1128059 : Blo 750330 1128059 := bstep (se 1 (by rfl) ⟨846044, by rfl⟩ : syracuseStep 1128059 = 1692089) B1692089
theorem B1128185 : Blo 750330 1128185 := bstep (se 2 (by rfl) ⟨423069, by rfl⟩ : syracuseStep 1128185 = 846139) B846139
theorem B2602847 : Blo 750330 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B1128287 : Blo 750330 1128287 := bstep (se 1 (by rfl) ⟨846215, by rfl⟩ : syracuseStep 1128287 = 1692431) B1692431
theorem B1128299 : Blo 750330 1128299 := bstep (se 1 (by rfl) ⟨846224, by rfl⟩ : syracuseStep 1128299 = 1692449) B1692449
theorem B1128527 : Blo 750330 1128527 := bstep (se 1 (by rfl) ⟨846395, by rfl⟩ : syracuseStep 1128527 = 1692791) B1692791
theorem B1128647 : Blo 750330 1128647 := bstep (se 1 (by rfl) ⟨846485, by rfl⟩ : syracuseStep 1128647 = 1692971) B1692971
theorem B5421323 : Blo 750330 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B1128809 : Blo 750330 1128809 := bstep (se 2 (by rfl) ⟨423303, by rfl⟩ : syracuseStep 1128809 = 846607) B846607
theorem B1128887 : Blo 750330 1128887 := bstep (se 1 (by rfl) ⟨846665, by rfl⟩ : syracuseStep 1128887 = 1693331) B1693331
theorem B1128923 : Blo 750330 1128923 := bstep (se 1 (by rfl) ⟨846692, by rfl⟩ : syracuseStep 1128923 = 1693385) B1693385
theorem B2538107 : Blo 750330 2538107 := bstep (se 1 (by rfl) ⟨1903580, by rfl⟩ : syracuseStep 2538107 = 3807161) B3807161
theorem B3816071 : Blo 750330 3816071 := bstep (se 1 (by rfl) ⟨2862053, by rfl⟩ : syracuseStep 3816071 = 5724107) B5724107
theorem B2898641 : Blo 750330 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B2538269 : Blo 750330 2538269 := bstep (se 3 (by rfl) ⟨475925, by rfl⟩ : syracuseStep 2538269 = 951851) B951851
theorem B1653577 : Blo 750330 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B4275017 : Blo 750330 4275017 := bstep (se 2 (by rfl) ⟨1603131, by rfl⟩ : syracuseStep 4275017 = 3206263) B3206263
theorem B1129391 : Blo 750330 1129391 := bstep (se 1 (by rfl) ⟨847043, by rfl⟩ : syracuseStep 1129391 = 1694087) B1694087
theorem B1129481 : Blo 750330 1129481 := bstep (se 2 (by rfl) ⟨423555, by rfl⟩ : syracuseStep 1129481 = 847111) B847111
theorem B1129511 : Blo 750330 1129511 := bstep (se 1 (by rfl) ⟨847133, by rfl⟩ : syracuseStep 1129511 = 1694267) B1694267
theorem B1129595 : Blo 750330 1129595 := bstep (se 1 (by rfl) ⟨847196, by rfl⟩ : syracuseStep 1129595 = 1694393) B1694393
theorem B2145437 : Blo 750330 2145437 := bstep (se 3 (by rfl) ⟨402269, by rfl⟩ : syracuseStep 2145437 = 804539) B804539
theorem B1129721 : Blo 750330 1129721 := bstep (se 2 (by rfl) ⟨423645, by rfl⟩ : syracuseStep 1129721 = 847291) B847291
theorem B1129823 : Blo 750330 1129823 := bstep (se 1 (by rfl) ⟨847367, by rfl⟩ : syracuseStep 1129823 = 1694735) B1694735
theorem B1129835 : Blo 750330 1129835 := bstep (se 1 (by rfl) ⟨847376, by rfl⟩ : syracuseStep 1129835 = 1694753) B1694753
theorem B4963727 : Blo 750330 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B2538971 : Blo 750330 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B3128813 : Blo 750330 3128813 := bstep (se 3 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 3128813 = 1173305) B1173305
theorem B1130063 : Blo 750330 1130063 := bstep (se 1 (by rfl) ⟨847547, by rfl⟩ : syracuseStep 1130063 = 1695095) B1695095
theorem B1130183 : Blo 750330 1130183 := bstep (se 1 (by rfl) ⟨847637, by rfl⟩ : syracuseStep 1130183 = 1695275) B1695275
theorem B2408221 : Blo 750330 2408221 := bstep (se 3 (by rfl) ⟨451541, by rfl⟩ : syracuseStep 2408221 = 903083) B903083
theorem B1130345 : Blo 750330 1130345 := bstep (se 2 (by rfl) ⟨423879, by rfl⟩ : syracuseStep 1130345 = 847759) B847759
theorem B9912179 : Blo 750330 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B1130423 : Blo 750330 1130423 := bstep (se 1 (by rfl) ⟨847817, by rfl⟩ : syracuseStep 1130423 = 1695635) B1695635
theorem B1130459 : Blo 750330 1130459 := bstep (se 1 (by rfl) ⟨847844, by rfl⟩ : syracuseStep 1130459 = 1695689) B1695689
theorem B2572289 : Blo 750330 2572289 := bstep (se 2 (by rfl) ⟨964608, by rfl⟩ : syracuseStep 2572289 = 1929217) B1929217
theorem B4112441 : Blo 750330 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B3817529 : Blo 750330 3817529 := bstep (se 2 (by rfl) ⟨1431573, by rfl⟩ : syracuseStep 3817529 = 2863147) B2863147
theorem B2539673 : Blo 750330 2539673 := bstep (se 2 (by rfl) ⟨952377, by rfl⟩ : syracuseStep 2539673 = 1904755) B1904755
theorem B2572631 : Blo 750330 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B967087 : Blo 750330 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B1130927 : Blo 750330 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B1131017 : Blo 750330 1131017 := bstep (se 2 (by rfl) ⟨424131, by rfl⟩ : syracuseStep 1131017 = 848263) B848263
theorem B2605607 : Blo 750330 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B1131047 : Blo 750330 1131047 := bstep (se 1 (by rfl) ⟨848285, by rfl⟩ : syracuseStep 1131047 = 1696571) B1696571
theorem B1131131 : Blo 750330 1131131 := bstep (se 1 (by rfl) ⟨848348, by rfl⟩ : syracuseStep 1131131 = 1696697) B1696697
theorem B2409209 : Blo 750330 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B1131257 : Blo 750330 1131257 := bstep (se 2 (by rfl) ⟨424221, by rfl⟩ : syracuseStep 1131257 = 848443) B848443
theorem B1131359 : Blo 750330 1131359 := bstep (se 1 (by rfl) ⟨848519, by rfl⟩ : syracuseStep 1131359 = 1697039) B1697039
theorem B1131371 : Blo 750330 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B1426319 : Blo 750330 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B1688507 : Blo 750330 1688507 := bstep (se 1 (by rfl) ⟨1266380, by rfl⟩ : syracuseStep 1688507 = 2532761) B2532761
theorem B1688633 : Blo 750330 1688633 := bstep (se 2 (by rfl) ⟨633237, by rfl⟩ : syracuseStep 1688633 = 1266475) B1266475
theorem B6505591 : Blo 750330 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B2540861 : Blo 750330 2540861 := bstep (se 3 (by rfl) ⟨476411, by rfl⟩ : syracuseStep 2540861 = 952823) B952823
theorem B1525097 : Blo 750330 1525097 := bstep (se 2 (by rfl) ⟨571911, by rfl⟩ : syracuseStep 1525097 = 1143823) B1143823
theorem B1688975 : Blo 750330 1688975 := bstep (se 1 (by rfl) ⟨1266731, by rfl⟩ : syracuseStep 1688975 = 2533463) B2533463
theorem B1689299 : Blo 750330 1689299 := bstep (se 1 (by rfl) ⟨1266974, by rfl⟩ : syracuseStep 1689299 = 2533949) B2533949
theorem B2410195 : Blo 750330 2410195 := bstep (se 1 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 2410195 = 3615293) B3615293
theorem B3622751 : Blo 750330 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B1427375 : Blo 750330 1427375 := bstep (se 1 (by rfl) ⟨1070531, by rfl⟩ : syracuseStep 1427375 = 2141063) B2141063
theorem B2410553 : Blo 750330 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B30951517 : Blo 750330 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B12208229 : Blo 750330 12208229 := bstep (se 4 (by rfl) ⟨1144521, by rfl⟩ : syracuseStep 12208229 = 2289043) B2289043
theorem B2541725 : Blo 750330 2541725 := bstep (se 3 (by rfl) ⟨476573, by rfl⟩ : syracuseStep 2541725 = 953147) B953147
theorem B1427807 : Blo 750330 1427807 := bstep (se 1 (by rfl) ⟨1070855, by rfl⟩ : syracuseStep 1427807 = 2141711) B2141711
theorem B1526159 : Blo 750330 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B8145305 : Blo 750330 8145305 := bstep (se 2 (by rfl) ⟨3054489, by rfl⟩ : syracuseStep 8145305 = 6108979) B6108979
theorem B23120417 : Blo 750330 23120417 := bstep (se 2 (by rfl) ⟨8670156, by rfl⟩ : syracuseStep 23120417 = 17340313) B17340313
theorem B1690235 : Blo 750330 1690235 := bstep (se 1 (by rfl) ⟨1267676, by rfl⟩ : syracuseStep 1690235 = 2535353) B2535353
theorem B9652871 : Blo 750330 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B2542265 : Blo 750330 2542265 := bstep (se 2 (by rfl) ⟨953349, by rfl⟩ : syracuseStep 2542265 = 1906699) B1906699
theorem B1690361 : Blo 750330 1690361 := bstep (se 2 (by rfl) ⟨633885, by rfl⟩ : syracuseStep 1690361 = 1267771) B1267771
theorem B904111 : Blo 750330 904111 := bstep (se 1 (by rfl) ⟨678083, by rfl⟩ : syracuseStep 904111 = 1356167) B1356167
theorem B1690631 : Blo 750330 1690631 := bstep (se 1 (by rfl) ⟨1267973, by rfl⟩ : syracuseStep 1690631 = 2535947) B2535947
theorem B2411527 : Blo 750330 2411527 := bstep (se 1 (by rfl) ⟨1808645, by rfl⟩ : syracuseStep 2411527 = 3617291) B3617291
theorem B1690703 : Blo 750330 1690703 := bstep (se 1 (by rfl) ⟨1268027, by rfl⟩ : syracuseStep 1690703 = 2536055) B2536055
theorem B2542859 : Blo 750330 2542859 := bstep (se 1 (by rfl) ⟨1907144, by rfl⟩ : syracuseStep 2542859 = 3814289) B3814289
theorem B1068395 : Blo 750330 1068395 := bstep (se 1 (by rfl) ⟨801296, by rfl⟩ : syracuseStep 1068395 = 1602593) B1602593
theorem B3624365 : Blo 750330 3624365 := bstep (se 3 (by rfl) ⟨679568, by rfl⟩ : syracuseStep 3624365 = 1359137) B1359137
theorem B2411977 : Blo 750330 2411977 := bstep (se 2 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 2411977 = 1808983) B1808983
theorem B1691099 : Blo 750330 1691099 := bstep (se 1 (by rfl) ⟨1268324, by rfl⟩ : syracuseStep 1691099 = 2536649) B2536649
theorem B2575859 : Blo 750330 2575859 := bstep (se 1 (by rfl) ⟨1931894, by rfl⟩ : syracuseStep 2575859 = 3863789) B3863789
theorem B2543129 : Blo 750330 2543129 := bstep (se 2 (by rfl) ⟨953673, by rfl⟩ : syracuseStep 2543129 = 1907347) B1907347
theorem B2444897 : Blo 750330 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B1691567 : Blo 750330 1691567 := bstep (se 1 (by rfl) ⟨1268675, by rfl⟩ : syracuseStep 1691567 = 2537351) B2537351
theorem B1691819 : Blo 750330 1691819 := bstep (se 1 (by rfl) ⟨1268864, by rfl⟩ : syracuseStep 1691819 = 2537729) B2537729
theorem B1429751 : Blo 750330 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B7065917 : Blo 750330 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B1429903 : Blo 750330 1429903 := bstep (se 1 (by rfl) ⟨1072427, by rfl⟩ : syracuseStep 1429903 = 2144855) B2144855
theorem B1266185 : Blo 750330 1266185 := bstep (se 2 (by rfl) ⟨474819, by rfl⟩ : syracuseStep 1266185 = 949639) B949639
theorem B5722649 : Blo 750330 5722649 := bstep (se 2 (by rfl) ⟨2145993, by rfl⟩ : syracuseStep 5722649 = 4291987) B4291987
theorem B905851 : Blo 750330 905851 := bstep (se 1 (by rfl) ⟨679388, by rfl⟩ : syracuseStep 905851 = 1358777) B1358777
theorem B2544263 : Blo 750330 2544263 := bstep (se 1 (by rfl) ⟨1908197, by rfl⟩ : syracuseStep 2544263 = 3816395) B3816395
theorem B1266347 : Blo 750330 1266347 := bstep (se 1 (by rfl) ⟨949760, by rfl⟩ : syracuseStep 1266347 = 1899521) B1899521
theorem B2544317 : Blo 750330 2544317 := bstep (se 3 (by rfl) ⟨477059, by rfl⟩ : syracuseStep 2544317 = 954119) B954119
theorem B1692359 : Blo 750330 1692359 := bstep (se 1 (by rfl) ⟨1269269, by rfl⟩ : syracuseStep 1692359 = 2538539) B2538539
theorem B2544479 : Blo 750330 2544479 := bstep (se 1 (by rfl) ⟨1908359, by rfl⟩ : syracuseStep 2544479 = 3816719) B3816719
theorem B2544641 : Blo 750330 2544641 := bstep (se 2 (by rfl) ⟨954240, by rfl⟩ : syracuseStep 2544641 = 1908481) B1908481
theorem B1266745 : Blo 750330 1266745 := bstep (se 2 (by rfl) ⟨475029, by rfl⟩ : syracuseStep 1266745 = 950059) B950059
theorem B1266887 : Blo 750330 1266887 := bstep (se 1 (by rfl) ⟨950165, by rfl⟩ : syracuseStep 1266887 = 1900331) B1900331
theorem B1430777 : Blo 750330 1430777 := bstep (se 2 (by rfl) ⟨536541, by rfl⟩ : syracuseStep 1430777 = 1073083) B1073083
theorem B1267049 : Blo 750330 1267049 := bstep (se 2 (by rfl) ⟨475143, by rfl⟩ : syracuseStep 1267049 = 950287) B950287
theorem B1430959 : Blo 750330 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B1693223 : Blo 750330 1693223 := bstep (se 1 (by rfl) ⟨1269917, by rfl⟩ : syracuseStep 1693223 = 2539835) B2539835
theorem B4282055 : Blo 750330 4282055 := bstep (se 1 (by rfl) ⟨3211541, by rfl⟩ : syracuseStep 4282055 = 6423083) B6423083
theorem B1267447 : Blo 750330 1267447 := bstep (se 1 (by rfl) ⟨950585, by rfl⟩ : syracuseStep 1267447 = 1901171) B1901171
theorem B2545451 : Blo 750330 2545451 := bstep (se 1 (by rfl) ⟨1909088, by rfl⟩ : syracuseStep 2545451 = 3818177) B3818177
theorem B5429051 : Blo 750330 5429051 := bstep (se 1 (by rfl) ⟨4071788, by rfl⟩ : syracuseStep 5429051 = 8143577) B8143577
theorem B1693547 : Blo 750330 1693547 := bstep (se 1 (by rfl) ⟨1270160, by rfl⟩ : syracuseStep 1693547 = 2540321) B2540321
theorem B1693601 : Blo 750330 1693601 := bstep (se 2 (by rfl) ⟨635100, by rfl⟩ : syracuseStep 1693601 = 1270201) B1270201
theorem B1267643 : Blo 750330 1267643 := bstep (se 1 (by rfl) ⟨950732, by rfl⟩ : syracuseStep 1267643 = 1901465) B1901465
theorem B36591587 : Blo 750330 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B1267751 : Blo 750330 1267751 := bstep (se 1 (by rfl) ⟨950813, by rfl⟩ : syracuseStep 1267751 = 1901627) B1901627
theorem B2545721 : Blo 750330 2545721 := bstep (se 2 (by rfl) ⟨954645, by rfl⟩ : syracuseStep 2545721 = 1909291) B1909291
theorem B24107165 : Blo 750330 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B1693943 : Blo 750330 1693943 := bstep (se 1 (by rfl) ⟨1270457, by rfl⟩ : syracuseStep 1693943 = 2540915) B2540915
theorem B1464569 : Blo 750330 1464569 := bstep (se 2 (by rfl) ⟨549213, by rfl⟩ : syracuseStep 1464569 = 1098427) B1098427
theorem B2578679 : Blo 750330 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B1268041 : Blo 750330 1268041 := bstep (se 2 (by rfl) ⟨475515, by rfl⟩ : syracuseStep 1268041 = 951031) B951031
theorem B1268075 : Blo 750330 1268075 := bstep (se 1 (by rfl) ⟨951056, by rfl⟩ : syracuseStep 1268075 = 1902113) B1902113
theorem B1071625 : Blo 750330 1071625 := bstep (se 2 (by rfl) ⟨401859, by rfl⟩ : syracuseStep 1071625 = 803719) B803719
theorem B1268473 : Blo 750330 1268473 := bstep (se 2 (by rfl) ⟨475677, by rfl⟩ : syracuseStep 1268473 = 951355) B951355
theorem B1694537 : Blo 750330 1694537 := bstep (se 2 (by rfl) ⟨635451, by rfl⟩ : syracuseStep 1694537 = 1270903) B1270903
theorem B1268743 : Blo 750330 1268743 := bstep (se 1 (by rfl) ⟨951557, by rfl⟩ : syracuseStep 1268743 = 1903115) B1903115
theorem B13884797 : Blo 750330 13884797 := bstep (se 3 (by rfl) ⟨2603399, by rfl⟩ : syracuseStep 13884797 = 5206799) B5206799
theorem B5725565 : Blo 750330 5725565 := bstep (se 3 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 5725565 = 2147087) B2147087
theorem B5496227 : Blo 750330 5496227 := bstep (se 1 (by rfl) ⟨4122170, by rfl⟩ : syracuseStep 5496227 = 8244341) B8244341
theorem B1269175 : Blo 750330 1269175 := bstep (se 1 (by rfl) ⟨951881, by rfl⟩ : syracuseStep 1269175 = 1903763) B1903763
theorem B1695329 : Blo 750330 1695329 := bstep (se 2 (by rfl) ⟨635748, by rfl⟩ : syracuseStep 1695329 = 1271497) B1271497
theorem B3858043 : Blo 750330 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1269371 : Blo 750330 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B1695671 : Blo 750330 1695671 := bstep (se 1 (by rfl) ⟨1271753, by rfl⟩ : syracuseStep 1695671 = 2543507) B2543507
theorem B1269769 : Blo 750330 1269769 := bstep (se 2 (by rfl) ⟨476163, by rfl⟩ : syracuseStep 1269769 = 952327) B952327
theorem B1073191 : Blo 750330 1073191 := bstep (se 1 (by rfl) ⟨804893, by rfl⟩ : syracuseStep 1073191 = 1609787) B1609787
theorem B1204303 : Blo 750330 1204303 := bstep (se 1 (by rfl) ⟨903227, by rfl⟩ : syracuseStep 1204303 = 1806455) B1806455
theorem B2744435 : Blo 750330 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B1269931 : Blo 750330 1269931 := bstep (se 1 (by rfl) ⟨952448, by rfl⟩ : syracuseStep 1269931 = 1904897) B1904897
theorem B1270235 : Blo 750330 1270235 := bstep (se 1 (by rfl) ⟨952676, by rfl⟩ : syracuseStep 1270235 = 1905353) B1905353
theorem B1696265 : Blo 750330 1696265 := bstep (se 2 (by rfl) ⟨636099, by rfl⟩ : syracuseStep 1696265 = 1272199) B1272199
theorem B844411 : Blo 750330 844411 := bstep (se 1 (by rfl) ⟨633308, by rfl⟩ : syracuseStep 844411 = 1266617) B1266617
theorem B1270471 : Blo 750330 1270471 := bstep (se 1 (by rfl) ⟨952853, by rfl⟩ : syracuseStep 1270471 = 1905707) B1905707
theorem B1696607 : Blo 750330 1696607 := bstep (se 1 (by rfl) ⟨1272455, by rfl⟩ : syracuseStep 1696607 = 2544911) B2544911
theorem B1270633 : Blo 750330 1270633 := bstep (se 2 (by rfl) ⟨476487, by rfl⟩ : syracuseStep 1270633 = 952975) B952975
theorem B6415361 : Blo 750330 6415361 := bstep (se 2 (by rfl) ⟨2405760, by rfl⟩ : syracuseStep 6415361 = 4811521) B4811521
theorem B1696787 : Blo 750330 1696787 := bstep (se 1 (by rfl) ⟨1272590, by rfl⟩ : syracuseStep 1696787 = 2545181) B2545181
theorem B844879 : Blo 750330 844879 := bstep (se 1 (by rfl) ⟨633659, by rfl⟩ : syracuseStep 844879 = 1267319) B1267319
theorem B4809881 : Blo 750330 4809881 := bstep (se 2 (by rfl) ⟨1803705, by rfl⟩ : syracuseStep 4809881 = 3607411) B3607411
theorem B1697129 : Blo 750330 1697129 := bstep (se 2 (by rfl) ⟨636423, by rfl⟩ : syracuseStep 1697129 = 1272847) B1272847
theorem B5432741 : Blo 750330 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B1205687 : Blo 750330 1205687 := bstep (se 1 (by rfl) ⟨904265, by rfl⟩ : syracuseStep 1205687 = 1808531) B1808531
theorem B1271227 : Blo 750330 1271227 := bstep (se 1 (by rfl) ⟨953420, by rfl⟩ : syracuseStep 1271227 = 1906841) B1906841
theorem B845275 : Blo 750330 845275 := bstep (se 1 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 845275 = 1267913) B1267913
theorem B1271335 : Blo 750330 1271335 := bstep (se 1 (by rfl) ⟨953501, by rfl⟩ : syracuseStep 1271335 = 1907003) B1907003
theorem B2745953 : Blo 750330 2745953 := bstep (se 2 (by rfl) ⟨1029732, by rfl⟩ : syracuseStep 2745953 = 2059465) B2059465
theorem B1271659 : Blo 750330 1271659 := bstep (se 1 (by rfl) ⟨953744, by rfl⟩ : syracuseStep 1271659 = 1907489) B1907489
theorem B845743 : Blo 750330 845743 := bstep (se 1 (by rfl) ⟨634307, by rfl⟩ : syracuseStep 845743 = 1268615) B1268615
theorem B1206199 : Blo 750330 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B846175 : Blo 750330 846175 := bstep (se 1 (by rfl) ⟨634631, by rfl⟩ : syracuseStep 846175 = 1269263) B1269263
theorem B846535 : Blo 750330 846535 := bstep (se 1 (by rfl) ⟨634901, by rfl⟩ : syracuseStep 846535 = 1269803) B1269803
theorem B1272719 : Blo 750330 1272719 := bstep (se 1 (by rfl) ⟨954539, by rfl⟩ : syracuseStep 1272719 = 1909079) B1909079
theorem B4287887 : Blo 750330 4287887 := bstep (se 1 (by rfl) ⟨3215915, by rfl⟩ : syracuseStep 4287887 = 6431831) B6431831
theorem B847399 : Blo 750330 847399 := bstep (se 1 (by rfl) ⟨635549, by rfl⟩ : syracuseStep 847399 = 1271099) B1271099
theorem B19263095 : Blo 750330 19263095 := bstep (se 1 (by rfl) ⟨14447321, by rfl⟩ : syracuseStep 19263095 = 28894643) B28894643
theorem B4288139 : Blo 750330 4288139 := bstep (se 1 (by rfl) ⟨3216104, by rfl⟩ : syracuseStep 4288139 = 6432209) B6432209
theorem B2715275 : Blo 750330 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B9629603 : Blo 750330 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B4812803 : Blo 750330 4812803 := bstep (se 1 (by rfl) ⟨3609602, by rfl⟩ : syracuseStep 4812803 = 7219205) B7219205
theorem B12185777 : Blo 750330 12185777 := bstep (se 2 (by rfl) ⟨4569666, by rfl⟩ : syracuseStep 12185777 = 9139333) B9139333
theorem B2716199 : Blo 750330 2716199 := bstep (se 1 (by rfl) ⟨2037149, by rfl⟩ : syracuseStep 2716199 = 4074299) B4074299
theorem B750375 : Blo 750330 750375 := bstep (se 1 (by rfl) ⟨562781, by rfl⟩ : syracuseStep 750375 = 1125563) B1125563
theorem B750415 : Blo 750330 750415 := bstep (se 1 (by rfl) ⟨562811, by rfl⟩ : syracuseStep 750415 = 1125623) B1125623
theorem B750431 : Blo 750330 750431 := bstep (se 1 (by rfl) ⟨562823, by rfl⟩ : syracuseStep 750431 = 1125647) B1125647
theorem B1143659 : Blo 750330 1143659 := bstep (se 1 (by rfl) ⟨857744, by rfl⟩ : syracuseStep 1143659 = 1715489) B1715489
theorem B750459 : Blo 750330 750459 := bstep (se 1 (by rfl) ⟨562844, by rfl⟩ : syracuseStep 750459 = 1125689) B1125689
theorem B750511 : Blo 750330 750511 := bstep (se 1 (by rfl) ⟨562883, by rfl⟩ : syracuseStep 750511 = 1125767) B1125767
theorem B750535 : Blo 750330 750535 := bstep (se 1 (by rfl) ⟨562901, by rfl⟩ : syracuseStep 750535 = 1125803) B1125803
theorem B750555 : Blo 750330 750555 := bstep (se 1 (by rfl) ⟨562916, by rfl⟩ : syracuseStep 750555 = 1125833) B1125833
theorem B3208193 : Blo 750330 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B750631 : Blo 750330 750631 := bstep (se 1 (by rfl) ⟨562973, by rfl⟩ : syracuseStep 750631 = 1125947) B1125947
theorem B9663533 : Blo 750330 9663533 := bstep (se 3 (by rfl) ⟨1811912, by rfl⟩ : syracuseStep 9663533 = 3623825) B3623825
theorem B750671 : Blo 750330 750671 := bstep (se 1 (by rfl) ⟨563003, by rfl⟩ : syracuseStep 750671 = 1126007) B1126007
theorem B750687 : Blo 750330 750687 := bstep (se 1 (by rfl) ⟨563015, by rfl⟩ : syracuseStep 750687 = 1126031) B1126031
theorem B750715 : Blo 750330 750715 := bstep (se 1 (by rfl) ⟨563036, by rfl⟩ : syracuseStep 750715 = 1126073) B1126073
theorem B750767 : Blo 750330 750767 := bstep (se 1 (by rfl) ⟨563075, by rfl⟩ : syracuseStep 750767 = 1126151) B1126151
theorem B750791 : Blo 750330 750791 := bstep (se 1 (by rfl) ⟨563093, by rfl⟩ : syracuseStep 750791 = 1126187) B1126187
theorem B750811 : Blo 750330 750811 := bstep (se 1 (by rfl) ⟨563108, by rfl⟩ : syracuseStep 750811 = 1126217) B1126217
theorem B750887 : Blo 750330 750887 := bstep (se 1 (by rfl) ⟨563165, by rfl⟩ : syracuseStep 750887 = 1126331) B1126331
theorem B750927 : Blo 750330 750927 := bstep (se 1 (by rfl) ⟨563195, by rfl⟩ : syracuseStep 750927 = 1126391) B1126391
theorem B750943 : Blo 750330 750943 := bstep (se 1 (by rfl) ⟨563207, by rfl⟩ : syracuseStep 750943 = 1126415) B1126415
theorem B1144169 : Blo 750330 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B750971 : Blo 750330 750971 := bstep (se 1 (by rfl) ⟨563228, by rfl⟩ : syracuseStep 750971 = 1126457) B1126457
theorem B751023 : Blo 750330 751023 := bstep (se 1 (by rfl) ⟨563267, by rfl⟩ : syracuseStep 751023 = 1126535) B1126535
theorem B751047 : Blo 750330 751047 := bstep (se 1 (by rfl) ⟨563285, by rfl⟩ : syracuseStep 751047 = 1126571) B1126571
theorem B751067 : Blo 750330 751067 := bstep (se 1 (by rfl) ⟨563300, by rfl⟩ : syracuseStep 751067 = 1126601) B1126601
theorem B2717165 : Blo 750330 2717165 := bstep (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) B1018937
theorem B751143 : Blo 750330 751143 := bstep (se 1 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 751143 = 1126715) B1126715
theorem B751183 : Blo 750330 751183 := bstep (se 1 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 751183 = 1126775) B1126775
theorem B751199 : Blo 750330 751199 := bstep (se 1 (by rfl) ⟨563399, by rfl⟩ : syracuseStep 751199 = 1126799) B1126799
theorem B751227 : Blo 750330 751227 := bstep (se 1 (by rfl) ⟨563420, by rfl⟩ : syracuseStep 751227 = 1126841) B1126841
theorem B751279 : Blo 750330 751279 := bstep (se 1 (by rfl) ⟨563459, by rfl⟩ : syracuseStep 751279 = 1126919) B1126919
theorem B751303 : Blo 750330 751303 := bstep (se 1 (by rfl) ⟨563477, by rfl⟩ : syracuseStep 751303 = 1126955) B1126955
theorem B751323 : Blo 750330 751323 := bstep (se 1 (by rfl) ⟨563492, by rfl⟩ : syracuseStep 751323 = 1126985) B1126985
theorem B5699321 : Blo 750330 5699321 := bstep (se 2 (by rfl) ⟨2137245, by rfl⟩ : syracuseStep 5699321 = 4274491) B4274491
theorem B751399 : Blo 750330 751399 := bstep (se 1 (by rfl) ⟨563549, by rfl⟩ : syracuseStep 751399 = 1127099) B1127099
theorem B4290347 : Blo 750330 4290347 := bstep (se 1 (by rfl) ⟨3217760, by rfl⟩ : syracuseStep 4290347 = 6435521) B6435521
theorem B751439 : Blo 750330 751439 := bstep (se 1 (by rfl) ⟨563579, by rfl⟩ : syracuseStep 751439 = 1127159) B1127159
theorem B3045215 : Blo 750330 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B751455 : Blo 750330 751455 := bstep (se 1 (by rfl) ⟨563591, by rfl⟩ : syracuseStep 751455 = 1127183) B1127183
theorem B751483 : Blo 750330 751483 := bstep (se 1 (by rfl) ⟨563612, by rfl⟩ : syracuseStep 751483 = 1127225) B1127225
theorem B751535 : Blo 750330 751535 := bstep (se 1 (by rfl) ⟨563651, by rfl⟩ : syracuseStep 751535 = 1127303) B1127303
theorem B2029495 : Blo 750330 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B751559 : Blo 750330 751559 := bstep (se 1 (by rfl) ⟨563669, by rfl⟩ : syracuseStep 751559 = 1127339) B1127339
theorem B751579 : Blo 750330 751579 := bstep (se 1 (by rfl) ⟨563684, by rfl⟩ : syracuseStep 751579 = 1127369) B1127369
theorem B751655 : Blo 750330 751655 := bstep (se 1 (by rfl) ⟨563741, by rfl⟩ : syracuseStep 751655 = 1127483) B1127483
theorem B751695 : Blo 750330 751695 := bstep (se 1 (by rfl) ⟨563771, by rfl⟩ : syracuseStep 751695 = 1127543) B1127543
theorem B751711 : Blo 750330 751711 := bstep (se 1 (by rfl) ⟨563783, by rfl⟩ : syracuseStep 751711 = 1127567) B1127567
theorem B751739 : Blo 750330 751739 := bstep (se 1 (by rfl) ⟨563804, by rfl⟩ : syracuseStep 751739 = 1127609) B1127609
theorem B3668125 : Blo 750330 3668125 := bstep (se 3 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 3668125 = 1375547) B1375547
theorem B751791 : Blo 750330 751791 := bstep (se 1 (by rfl) ⟨563843, by rfl⟩ : syracuseStep 751791 = 1127687) B1127687
theorem B751815 : Blo 750330 751815 := bstep (se 1 (by rfl) ⟨563861, by rfl⟩ : syracuseStep 751815 = 1127723) B1127723
theorem B751835 : Blo 750330 751835 := bstep (se 1 (by rfl) ⟨563876, by rfl⟩ : syracuseStep 751835 = 1127753) B1127753
theorem B751911 : Blo 750330 751911 := bstep (se 1 (by rfl) ⟨563933, by rfl⟩ : syracuseStep 751911 = 1127867) B1127867
theorem B751951 : Blo 750330 751951 := bstep (se 1 (by rfl) ⟨563963, by rfl⟩ : syracuseStep 751951 = 1127927) B1127927
theorem B751967 : Blo 750330 751967 := bstep (se 1 (by rfl) ⟨563975, by rfl⟩ : syracuseStep 751967 = 1127951) B1127951
theorem B751995 : Blo 750330 751995 := bstep (se 1 (by rfl) ⟨563996, by rfl⟩ : syracuseStep 751995 = 1127993) B1127993
theorem B752047 : Blo 750330 752047 := bstep (se 1 (by rfl) ⟨564035, by rfl⟩ : syracuseStep 752047 = 1128071) B1128071
theorem B752071 : Blo 750330 752071 := bstep (se 1 (by rfl) ⟨564053, by rfl⟩ : syracuseStep 752071 = 1128107) B1128107
theorem B13728203 : Blo 750330 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B752091 : Blo 750330 752091 := bstep (se 1 (by rfl) ⟨564068, by rfl⟩ : syracuseStep 752091 = 1128137) B1128137
theorem B752167 : Blo 750330 752167 := bstep (se 1 (by rfl) ⟨564125, by rfl⟩ : syracuseStep 752167 = 1128251) B1128251
theorem B752207 : Blo 750330 752207 := bstep (se 1 (by rfl) ⟨564155, by rfl⟩ : syracuseStep 752207 = 1128311) B1128311
theorem B752223 : Blo 750330 752223 := bstep (se 1 (by rfl) ⟨564167, by rfl⟩ : syracuseStep 752223 = 1128335) B1128335
theorem B752251 : Blo 750330 752251 := bstep (se 1 (by rfl) ⟨564188, by rfl⟩ : syracuseStep 752251 = 1128377) B1128377
theorem B752303 : Blo 750330 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B752327 : Blo 750330 752327 := bstep (se 1 (by rfl) ⟨564245, by rfl⟩ : syracuseStep 752327 = 1128491) B1128491
theorem B752347 : Blo 750330 752347 := bstep (se 1 (by rfl) ⟨564260, by rfl⟩ : syracuseStep 752347 = 1128521) B1128521
theorem B752423 : Blo 750330 752423 := bstep (se 1 (by rfl) ⟨564317, by rfl⟩ : syracuseStep 752423 = 1128635) B1128635
theorem B3046187 : Blo 750330 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B752463 : Blo 750330 752463 := bstep (se 1 (by rfl) ⟨564347, by rfl⟩ : syracuseStep 752463 = 1128695) B1128695
theorem B1899359 : Blo 750330 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B752479 : Blo 750330 752479 := bstep (se 1 (by rfl) ⟨564359, by rfl⟩ : syracuseStep 752479 = 1128719) B1128719
theorem B752507 : Blo 750330 752507 := bstep (se 1 (by rfl) ⟨564380, by rfl⟩ : syracuseStep 752507 = 1128761) B1128761
theorem B752559 : Blo 750330 752559 := bstep (se 1 (by rfl) ⟨564419, by rfl⟩ : syracuseStep 752559 = 1128839) B1128839
theorem B752583 : Blo 750330 752583 := bstep (se 1 (by rfl) ⟨564437, by rfl⟩ : syracuseStep 752583 = 1128875) B1128875
theorem B752603 : Blo 750330 752603 := bstep (se 1 (by rfl) ⟨564452, by rfl⟩ : syracuseStep 752603 = 1128905) B1128905
theorem B752679 : Blo 750330 752679 := bstep (se 1 (by rfl) ⟨564509, by rfl⟩ : syracuseStep 752679 = 1129019) B1129019
theorem B752719 : Blo 750330 752719 := bstep (se 1 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 752719 = 1129079) B1129079
theorem B752735 : Blo 750330 752735 := bstep (se 1 (by rfl) ⟨564551, by rfl⟩ : syracuseStep 752735 = 1129103) B1129103
theorem B752763 : Blo 750330 752763 := bstep (se 1 (by rfl) ⟨564572, by rfl⟩ : syracuseStep 752763 = 1129145) B1129145
theorem B5700779 : Blo 750330 5700779 := bstep (se 1 (by rfl) ⟨4275584, by rfl⟩ : syracuseStep 5700779 = 8551169) B8551169
theorem B752815 : Blo 750330 752815 := bstep (se 1 (by rfl) ⟨564611, by rfl⟩ : syracuseStep 752815 = 1129223) B1129223
theorem B752839 : Blo 750330 752839 := bstep (se 1 (by rfl) ⟨564629, by rfl⟩ : syracuseStep 752839 = 1129259) B1129259
theorem B752859 : Blo 750330 752859 := bstep (se 1 (by rfl) ⟨564644, by rfl⟩ : syracuseStep 752859 = 1129289) B1129289
theorem B752935 : Blo 750330 752935 := bstep (se 1 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 752935 = 1129403) B1129403
theorem B752975 : Blo 750330 752975 := bstep (se 1 (by rfl) ⟨564731, by rfl⟩ : syracuseStep 752975 = 1129463) B1129463
theorem B752991 : Blo 750330 752991 := bstep (se 1 (by rfl) ⟨564743, by rfl⟩ : syracuseStep 752991 = 1129487) B1129487
theorem B753019 : Blo 750330 753019 := bstep (se 1 (by rfl) ⟨564764, by rfl⟩ : syracuseStep 753019 = 1129529) B1129529
theorem B753071 : Blo 750330 753071 := bstep (se 1 (by rfl) ⟨564803, by rfl⟩ : syracuseStep 753071 = 1129607) B1129607
theorem B753095 : Blo 750330 753095 := bstep (se 1 (by rfl) ⟨564821, by rfl⟩ : syracuseStep 753095 = 1129643) B1129643
theorem B753115 : Blo 750330 753115 := bstep (se 1 (by rfl) ⟨564836, by rfl⟩ : syracuseStep 753115 = 1129673) B1129673
theorem B1900057 : Blo 750330 1900057 := bstep (se 2 (by rfl) ⟨712521, by rfl⟩ : syracuseStep 1900057 = 1425043) B1425043
theorem B2850329 : Blo 750330 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B753191 : Blo 750330 753191 := bstep (se 1 (by rfl) ⟨564893, by rfl⟩ : syracuseStep 753191 = 1129787) B1129787
theorem B753231 : Blo 750330 753231 := bstep (se 1 (by rfl) ⟨564923, by rfl⟩ : syracuseStep 753231 = 1129847) B1129847
theorem B753247 : Blo 750330 753247 := bstep (se 1 (by rfl) ⟨564935, by rfl⟩ : syracuseStep 753247 = 1129871) B1129871
theorem B753275 : Blo 750330 753275 := bstep (se 1 (by rfl) ⟨564956, by rfl⟩ : syracuseStep 753275 = 1129913) B1129913
theorem B5701265 : Blo 750330 5701265 := bstep (se 2 (by rfl) ⟨2137974, by rfl⟩ : syracuseStep 5701265 = 4275949) B4275949
theorem B753327 : Blo 750330 753327 := bstep (se 1 (by rfl) ⟨564995, by rfl⟩ : syracuseStep 753327 = 1129991) B1129991
theorem B753351 : Blo 750330 753351 := bstep (se 1 (by rfl) ⟨565013, by rfl⟩ : syracuseStep 753351 = 1130027) B1130027
theorem B753371 : Blo 750330 753371 := bstep (se 1 (by rfl) ⟨565028, by rfl⟩ : syracuseStep 753371 = 1130057) B1130057
theorem B753447 : Blo 750330 753447 := bstep (se 1 (by rfl) ⟨565085, by rfl⟩ : syracuseStep 753447 = 1130171) B1130171
theorem B1900361 : Blo 750330 1900361 := bstep (se 2 (by rfl) ⟨712635, by rfl⟩ : syracuseStep 1900361 = 1425271) B1425271
theorem B753487 : Blo 750330 753487 := bstep (se 1 (by rfl) ⟨565115, by rfl⟩ : syracuseStep 753487 = 1130231) B1130231
theorem B753503 : Blo 750330 753503 := bstep (se 1 (by rfl) ⟨565127, by rfl⟩ : syracuseStep 753503 = 1130255) B1130255
theorem B753531 : Blo 750330 753531 := bstep (se 1 (by rfl) ⟨565148, by rfl⟩ : syracuseStep 753531 = 1130297) B1130297
theorem B11009927 : Blo 750330 11009927 := bstep (se 1 (by rfl) ⟨8257445, by rfl⟩ : syracuseStep 11009927 = 16514891) B16514891
theorem B4292513 : Blo 750330 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B753583 : Blo 750330 753583 := bstep (se 1 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 753583 = 1130375) B1130375
theorem B753607 : Blo 750330 753607 := bstep (se 1 (by rfl) ⟨565205, by rfl⟩ : syracuseStep 753607 = 1130411) B1130411
theorem B753627 : Blo 750330 753627 := bstep (se 1 (by rfl) ⟨565220, by rfl⟩ : syracuseStep 753627 = 1130441) B1130441
theorem B1605737 : Blo 750330 1605737 := bstep (se 2 (by rfl) ⟨602151, by rfl⟩ : syracuseStep 1605737 = 1204303) B1204303
theorem B5701751 : Blo 750330 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B753951 : Blo 750330 753951 := bstep (se 1 (by rfl) ⟨565463, by rfl⟩ : syracuseStep 753951 = 1130927) B1130927
theorem B754011 : Blo 750330 754011 := bstep (se 1 (by rfl) ⟨565508, by rfl⟩ : syracuseStep 754011 = 1131017) B1131017
theorem B1737071 : Blo 750330 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B754031 : Blo 750330 754031 := bstep (se 1 (by rfl) ⟨565523, by rfl⟩ : syracuseStep 754031 = 1131047) B1131047
theorem B754087 : Blo 750330 754087 := bstep (se 1 (by rfl) ⟨565565, by rfl⟩ : syracuseStep 754087 = 1131131) B1131131
theorem B21725657 : Blo 750330 21725657 := bstep (se 2 (by rfl) ⟨8147121, by rfl⟩ : syracuseStep 21725657 = 16294243) B16294243
theorem B1606139 : Blo 750330 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B754171 : Blo 750330 754171 := bstep (se 1 (by rfl) ⟨565628, by rfl⟩ : syracuseStep 754171 = 1131257) B1131257
theorem B754239 : Blo 750330 754239 := bstep (se 1 (by rfl) ⟨565679, by rfl⟩ : syracuseStep 754239 = 1131359) B1131359
theorem B754247 : Blo 750330 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B950879 : Blo 750330 950879 := bstep (se 1 (by rfl) ⟨713159, by rfl⟩ : syracuseStep 950879 = 1426319) B1426319
theorem B3801815 : Blo 750330 3801815 := bstep (se 1 (by rfl) ⟨2851361, by rfl⟩ : syracuseStep 3801815 = 5702723) B5702723
theorem B1901303 : Blo 750330 1901303 := bstep (se 1 (by rfl) ⟨1425977, by rfl⟩ : syracuseStep 1901303 = 2851955) B2851955
theorem B21168965 : Blo 750330 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B4719455 : Blo 750330 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B1016731 : Blo 750330 1016731 := bstep (se 1 (by rfl) ⟨762548, by rfl⟩ : syracuseStep 1016731 = 1525097) B1525097
theorem B4817825 : Blo 750330 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B951583 : Blo 750330 951583 := bstep (se 1 (by rfl) ⟨713687, by rfl⟩ : syracuseStep 951583 = 1427375) B1427375
theorem B3802463 : Blo 750330 3802463 := bstep (se 1 (by rfl) ⟨2851847, by rfl⟩ : syracuseStep 3802463 = 5703695) B5703695
theorem B3671401 : Blo 750330 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B1607035 : Blo 750330 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B1902163 : Blo 750330 1902163 := bstep (se 1 (by rfl) ⟨1426622, by rfl⟩ : syracuseStep 1902163 = 2853245) B2853245
theorem B16255241 : Blo 750330 16255241 := bstep (se 2 (by rfl) ⟨6095715, by rfl⟩ : syracuseStep 16255241 = 12191431) B12191431
theorem B3213593 : Blo 750330 3213593 := bstep (se 2 (by rfl) ⟨1205097, by rfl⟩ : syracuseStep 3213593 = 2410195) B2410195
theorem B3049757 : Blo 750330 3049757 := bstep (se 3 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 3049757 = 1143659) B1143659
theorem B1608265 : Blo 750330 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B1903439 : Blo 750330 1903439 := bstep (se 1 (by rfl) ⟨1427579, by rfl⟩ : syracuseStep 1903439 = 2855159) B2855159
theorem B4820285 : Blo 750330 4820285 := bstep (se 3 (by rfl) ⟨903803, by rfl⟩ : syracuseStep 4820285 = 1807607) B1807607
theorem B1904087 : Blo 750330 1904087 := bstep (se 1 (by rfl) ⟨1428065, by rfl⟩ : syracuseStep 1904087 = 2856131) B2856131
theorem B953851 : Blo 750330 953851 := bstep (se 1 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 953851 = 1430777) B1430777
theorem B3804731 : Blo 750330 3804731 := bstep (se 1 (by rfl) ⟨2853548, by rfl⟩ : syracuseStep 3804731 = 5707097) B5707097
theorem B2854703 : Blo 750330 2854703 := bstep (se 1 (by rfl) ⟨2141027, by rfl⟩ : syracuseStep 2854703 = 4282055) B4282055
theorem B1904431 : Blo 750330 1904431 := bstep (se 1 (by rfl) ⟨1428323, by rfl⟩ : syracuseStep 1904431 = 2856647) B2856647
theorem B1806185 : Blo 750330 1806185 := bstep (se 2 (by rfl) ⟨677319, by rfl⟩ : syracuseStep 1806185 = 1354639) B1354639
theorem B7245773 : Blo 750330 7245773 := bstep (se 3 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 7245773 = 2717165) B2717165
theorem B3215369 : Blo 750330 3215369 := bstep (se 2 (by rfl) ⟨1205763, by rfl⟩ : syracuseStep 3215369 = 2411527) B2411527
theorem B1905079 : Blo 750330 1905079 := bstep (se 1 (by rfl) ⟨1428809, by rfl⟩ : syracuseStep 1905079 = 2857619) B2857619
theorem B3215969 : Blo 750330 3215969 := bstep (se 2 (by rfl) ⟨1205988, by rfl⟩ : syracuseStep 3215969 = 2411977) B2411977
theorem B4821925 : Blo 750330 4821925 := bstep (se 4 (by rfl) ⟨452055, by rfl⟩ : syracuseStep 4821925 = 904111) B904111
theorem B3806351 : Blo 750330 3806351 := bstep (se 1 (by rfl) ⟨2854763, by rfl⟩ : syracuseStep 3806351 = 5709527) B5709527
theorem B1807753 : Blo 750330 1807753 := bstep (se 2 (by rfl) ⟨677907, by rfl⟩ : syracuseStep 1807753 = 1355815) B1355815
theorem B1906487 : Blo 750330 1906487 := bstep (se 1 (by rfl) ⟨1429865, by rfl⟩ : syracuseStep 1906487 = 2859731) B2859731
theorem B1906537 : Blo 750330 1906537 := bstep (se 2 (by rfl) ⟨714951, by rfl⟩ : syracuseStep 1906537 = 1429903) B1429903
theorem B3807485 : Blo 750330 3807485 := bstep (se 3 (by rfl) ⟨713903, by rfl⟩ : syracuseStep 3807485 = 1427807) B1427807
theorem B4069757 : Blo 750330 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B3611411 : Blo 750330 3611411 := bstep (se 1 (by rfl) ⟨2708558, by rfl⟩ : syracuseStep 3611411 = 5417117) B5417117
theorem B3808295 : Blo 750330 3808295 := bstep (se 1 (by rfl) ⟨2856221, by rfl⟩ : syracuseStep 3808295 = 5712443) B5712443
theorem B1907945 : Blo 750330 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B1908107 : Blo 750330 1908107 := bstep (se 1 (by rfl) ⟨1431080, by rfl⟩ : syracuseStep 1908107 = 2862161) B2862161
theorem B2858591 : Blo 750330 2858591 := bstep (se 1 (by rfl) ⟨2143943, by rfl⟩ : syracuseStep 2858591 = 4287887) B4287887
theorem B1908319 : Blo 750330 1908319 := bstep (se 1 (by rfl) ⟨1431239, by rfl⟩ : syracuseStep 1908319 = 2862479) B2862479
theorem B2858759 : Blo 750330 2858759 := bstep (se 1 (by rfl) ⟨2144069, by rfl⟩ : syracuseStep 2858759 = 4288139) B4288139
theorem B1810183 : Blo 750330 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B6430873 : Blo 750330 6430873 := bstep (se 2 (by rfl) ⟨2411577, by rfl⟩ : syracuseStep 6430873 = 4823155) B4823155
theorem B4890833 : Blo 750330 4890833 := bstep (se 2 (by rfl) ⟨1834062, by rfl⟩ : syracuseStep 4890833 = 3668125) B3668125
theorem B1908947 : Blo 750330 1908947 := bstep (se 1 (by rfl) ⟨1431710, by rfl⟩ : syracuseStep 1908947 = 2863421) B2863421
theorem B1810799 : Blo 750330 1810799 := bstep (se 1 (by rfl) ⟨1358099, by rfl⟩ : syracuseStep 1810799 = 2716199) B2716199
theorem B2138795 : Blo 750330 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B9642725 : Blo 750330 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B762779 : Blo 750330 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B3810401 : Blo 750330 3810401 := bstep (se 2 (by rfl) ⟨1428900, by rfl⟩ : syracuseStep 3810401 = 2857801) B2857801
theorem B2860231 : Blo 750330 2860231 := bstep (se 1 (by rfl) ⟨2145173, by rfl⟩ : syracuseStep 2860231 = 4290347) B4290347
theorem B3614215 : Blo 750330 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B9152135 : Blo 750330 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B12855185 : Blo 750330 12855185 := bstep (se 2 (by rfl) ⟨4820694, by rfl⟩ : syracuseStep 12855185 = 9641389) B9641389
theorem B2533409 : Blo 750330 2533409 := bstep (se 2 (by rfl) ⟨950028, by rfl⟩ : syracuseStep 2533409 = 1900057) B1900057
theorem B3615101 : Blo 750330 3615101 := bstep (se 3 (by rfl) ⟨677831, by rfl⟩ : syracuseStep 3615101 = 1355663) B1355663
theorem B2861675 : Blo 750330 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B1714859 : Blo 750330 1714859 := bstep (se 1 (by rfl) ⟨1286144, by rfl⟩ : syracuseStep 1714859 = 2572289) B2572289
theorem B1715087 : Blo 750330 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B1289449 : Blo 750330 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B1125671 : Blo 750330 1125671 := bstep (se 1 (by rfl) ⟨844253, by rfl⟩ : syracuseStep 1125671 = 1688507) B1688507
theorem B3812669 : Blo 750330 3812669 := bstep (se 3 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 3812669 = 1429751) B1429751
theorem B1125755 : Blo 750330 1125755 := bstep (se 1 (by rfl) ⟨844316, by rfl⟩ : syracuseStep 1125755 = 1688633) B1688633
theorem B1125881 : Blo 750330 1125881 := bstep (se 2 (by rfl) ⟨422205, by rfl⟩ : syracuseStep 1125881 = 844411) B844411
theorem B1125983 : Blo 750330 1125983 := bstep (se 1 (by rfl) ⟨844487, by rfl⟩ : syracuseStep 1125983 = 1688975) B1688975
theorem B1126199 : Blo 750330 1126199 := bstep (se 1 (by rfl) ⟨844649, by rfl⟩ : syracuseStep 1126199 = 1689299) B1689299
theorem B8138819 : Blo 750330 8138819 := bstep (se 1 (by rfl) ⟨6104114, by rfl⟩ : syracuseStep 8138819 = 12208229) B12208229
theorem B1126505 : Blo 750330 1126505 := bstep (se 2 (by rfl) ⟨422439, by rfl⟩ : syracuseStep 1126505 = 844879) B844879
theorem B2863451 : Blo 750330 2863451 := bstep (se 1 (by rfl) ⟨2147588, by rfl⟩ : syracuseStep 2863451 = 4295177) B4295177
theorem B15413611 : Blo 750330 15413611 := bstep (se 1 (by rfl) ⟨11560208, by rfl⟩ : syracuseStep 15413611 = 23120417) B23120417
theorem B1126823 : Blo 750330 1126823 := bstep (se 1 (by rfl) ⟨845117, by rfl⟩ : syracuseStep 1126823 = 1690235) B1690235
theorem B6435247 : Blo 750330 6435247 := bstep (se 1 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 6435247 = 9652871) B9652871
theorem B4829615 : Blo 750330 4829615 := bstep (se 1 (by rfl) ⟨3622211, by rfl⟩ : syracuseStep 4829615 = 7244423) B7244423
theorem B1126907 : Blo 750330 1126907 := bstep (se 1 (by rfl) ⟨845180, by rfl⟩ : syracuseStep 1126907 = 1690361) B1690361
theorem B1127033 : Blo 750330 1127033 := bstep (se 2 (by rfl) ⟨422637, by rfl⟩ : syracuseStep 1127033 = 845275) B845275
theorem B1127087 : Blo 750330 1127087 := bstep (se 1 (by rfl) ⟨845315, by rfl⟩ : syracuseStep 1127087 = 1690631) B1690631
theorem B1127135 : Blo 750330 1127135 := bstep (se 1 (by rfl) ⟨845351, by rfl⟩ : syracuseStep 1127135 = 1690703) B1690703
theorem B2536271 : Blo 750330 2536271 := bstep (se 1 (by rfl) ⟨1902203, by rfl⟩ : syracuseStep 2536271 = 3804407) B3804407
theorem B2405351 : Blo 750330 2405351 := bstep (se 1 (by rfl) ⟨1804013, by rfl⟩ : syracuseStep 2405351 = 3608027) B3608027
theorem B1127399 : Blo 750330 1127399 := bstep (se 1 (by rfl) ⟨845549, by rfl⟩ : syracuseStep 1127399 = 1691099) B1691099
theorem B2536595 : Blo 750330 2536595 := bstep (se 1 (by rfl) ⟨1902446, by rfl⟩ : syracuseStep 2536595 = 3804893) B3804893
theorem B1127657 : Blo 750330 1127657 := bstep (se 2 (by rfl) ⟨422871, by rfl⟩ : syracuseStep 1127657 = 845743) B845743
theorem B1127711 : Blo 750330 1127711 := bstep (se 1 (by rfl) ⟨845783, by rfl⟩ : syracuseStep 1127711 = 1691567) B1691567
theorem B2536865 : Blo 750330 2536865 := bstep (se 2 (by rfl) ⟨951324, by rfl⟩ : syracuseStep 2536865 = 1902649) B1902649
theorem B1127879 : Blo 750330 1127879 := bstep (se 1 (by rfl) ⟨845909, by rfl⟩ : syracuseStep 1127879 = 1691819) B1691819
theorem B41268689 : Blo 750330 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B3815099 : Blo 750330 3815099 := bstep (se 1 (by rfl) ⟨2861324, by rfl⟩ : syracuseStep 3815099 = 5722649) B5722649
theorem B1128233 : Blo 750330 1128233 := bstep (se 2 (by rfl) ⟨423087, by rfl⟩ : syracuseStep 1128233 = 846175) B846175
theorem B1128239 : Blo 750330 1128239 := bstep (se 1 (by rfl) ⟨846179, by rfl⟩ : syracuseStep 1128239 = 1692359) B1692359
theorem B1128713 : Blo 750330 1128713 := bstep (se 2 (by rfl) ⟨423267, by rfl⟩ : syracuseStep 1128713 = 846535) B846535
theorem B1128815 : Blo 750330 1128815 := bstep (se 1 (by rfl) ⟨846611, by rfl⟩ : syracuseStep 1128815 = 1693223) B1693223
theorem B3619367 : Blo 750330 3619367 := bstep (se 1 (by rfl) ⟨2714525, by rfl⟩ : syracuseStep 3619367 = 5429051) B5429051
theorem B1129031 : Blo 750330 1129031 := bstep (se 1 (by rfl) ⟨846773, by rfl⟩ : syracuseStep 1129031 = 1693547) B1693547
theorem B2406991 : Blo 750330 2406991 := bstep (se 1 (by rfl) ⟨1805243, by rfl⟩ : syracuseStep 2406991 = 3610487) B3610487
theorem B1129067 : Blo 750330 1129067 := bstep (se 1 (by rfl) ⟨846800, by rfl⟩ : syracuseStep 1129067 = 1693601) B1693601
theorem B24394391 : Blo 750330 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B16071443 : Blo 750330 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B1129295 : Blo 750330 1129295 := bstep (se 1 (by rfl) ⟨846971, by rfl⟩ : syracuseStep 1129295 = 1693943) B1693943
theorem B1719119 : Blo 750330 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B1424603 : Blo 750330 1424603 := bstep (se 1 (by rfl) ⟨1068452, by rfl⟩ : syracuseStep 1424603 = 2136905) B2136905
theorem B1129691 : Blo 750330 1129691 := bstep (se 1 (by rfl) ⟨847268, by rfl⟩ : syracuseStep 1129691 = 1694537) B1694537
theorem B1129865 : Blo 750330 1129865 := bstep (se 2 (by rfl) ⟨423699, by rfl⟩ : syracuseStep 1129865 = 847399) B847399
theorem B9256531 : Blo 750330 9256531 := bstep (se 1 (by rfl) ⟨6942398, by rfl⟩ : syracuseStep 9256531 = 13884797) B13884797
theorem B3817043 : Blo 750330 3817043 := bstep (se 1 (by rfl) ⟨2862782, by rfl⟩ : syracuseStep 3817043 = 5725565) B5725565
theorem B1130219 : Blo 750330 1130219 := bstep (se 1 (by rfl) ⟨847664, by rfl⟩ : syracuseStep 1130219 = 1695329) B1695329
theorem B1130447 : Blo 750330 1130447 := bstep (se 1 (by rfl) ⟨847835, by rfl⟩ : syracuseStep 1130447 = 1695671) B1695671
theorem B2146313 : Blo 750330 2146313 := bstep (se 2 (by rfl) ⟨804867, by rfl⟩ : syracuseStep 2146313 = 1609735) B1609735
theorem B1130843 : Blo 750330 1130843 := bstep (se 1 (by rfl) ⟨848132, by rfl⟩ : syracuseStep 1130843 = 1696265) B1696265
theorem B2540051 : Blo 750330 2540051 := bstep (se 1 (by rfl) ⟨1905038, by rfl⟩ : syracuseStep 2540051 = 3810077) B3810077
theorem B1131071 : Blo 750330 1131071 := bstep (se 1 (by rfl) ⟨848303, by rfl⟩ : syracuseStep 1131071 = 1696607) B1696607
theorem B4276907 : Blo 750330 4276907 := bstep (se 1 (by rfl) ⟨3207680, by rfl⟩ : syracuseStep 4276907 = 6415361) B6415361
theorem B1131191 : Blo 750330 1131191 := bstep (se 1 (by rfl) ⟨848393, by rfl⟩ : syracuseStep 1131191 = 1696787) B1696787
theorem B19776307 : Blo 750330 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B1688399 : Blo 750330 1688399 := bstep (se 1 (by rfl) ⟨1266299, by rfl⟩ : syracuseStep 1688399 = 2532599) B2532599
theorem B1131419 : Blo 750330 1131419 := bstep (se 1 (by rfl) ⟨848564, by rfl⟩ : syracuseStep 1131419 = 1697129) B1697129
theorem B3621827 : Blo 750330 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B803791 : Blo 750330 803791 := bstep (se 1 (by rfl) ⟨602843, by rfl⟩ : syracuseStep 803791 = 1205687) B1205687
theorem B1688615 : Blo 750330 1688615 := bstep (se 1 (by rfl) ⟨1266461, by rfl⟩ : syracuseStep 1688615 = 2532923) B2532923
theorem B2147543 : Blo 750330 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B1688795 : Blo 750330 1688795 := bstep (se 1 (by rfl) ⟨1266596, by rfl⟩ : syracuseStep 1688795 = 2533193) B2533193
theorem B36619607 : Blo 750330 36619607 := bstep (se 1 (by rfl) ⟨27464705, by rfl⟩ : syracuseStep 36619607 = 54929411) B54929411
theorem B1688993 : Blo 750330 1688993 := bstep (se 2 (by rfl) ⟨633372, by rfl⟩ : syracuseStep 1688993 = 1266745) B1266745
theorem B35276309 : Blo 750330 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B2147897 : Blo 750330 2147897 := bstep (se 2 (by rfl) ⟨805461, by rfl⟩ : syracuseStep 2147897 = 1610923) B1610923
theorem B1689551 : Blo 750330 1689551 := bstep (se 1 (by rfl) ⟨1267163, by rfl⟩ : syracuseStep 1689551 = 2534327) B2534327
theorem B2541833 : Blo 750330 2541833 := bstep (se 2 (by rfl) ⟨953187, by rfl⟩ : syracuseStep 2541833 = 1906375) B1906375
theorem B6703397 : Blo 750330 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1689929 : Blo 750330 1689929 := bstep (se 2 (by rfl) ⟨633723, by rfl⟩ : syracuseStep 1689929 = 1267447) B1267447
theorem B1689947 : Blo 750330 1689947 := bstep (se 1 (by rfl) ⟨1267460, by rfl⟩ : syracuseStep 1689947 = 2534921) B2534921
theorem B2705993 : Blo 750330 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B3853175 : Blo 750330 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B1690523 : Blo 750330 1690523 := bstep (se 1 (by rfl) ⟨1267892, by rfl⟩ : syracuseStep 1690523 = 2535785) B2535785
theorem B1690721 : Blo 750330 1690721 := bstep (se 2 (by rfl) ⟨634020, by rfl⟩ : syracuseStep 1690721 = 1268041) B1268041
theorem B1690919 : Blo 750330 1690919 := bstep (se 1 (by rfl) ⟨1268189, by rfl⟩ : syracuseStep 1690919 = 2536379) B2536379
theorem B1428833 : Blo 750330 1428833 := bstep (se 2 (by rfl) ⟨535812, by rfl⟩ : syracuseStep 1428833 = 1071625) B1071625
theorem B6442355 : Blo 750330 6442355 := bstep (se 1 (by rfl) ⟨4831766, by rfl⟩ : syracuseStep 6442355 = 9663533) B9663533
theorem B2542967 : Blo 750330 2542967 := bstep (se 1 (by rfl) ⟨1907225, by rfl⟩ : syracuseStep 2542967 = 3814451) B3814451
theorem B1691297 : Blo 750330 1691297 := bstep (se 2 (by rfl) ⟨634236, by rfl⟩ : syracuseStep 1691297 = 1268473) B1268473
theorem B2412193 : Blo 750330 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B6868957 : Blo 750330 6868957 := bstep (se 3 (by rfl) ⟨1287929, by rfl⟩ : syracuseStep 6868957 = 2575859) B2575859
theorem B1691657 : Blo 750330 1691657 := bstep (se 2 (by rfl) ⟨634371, by rfl⟩ : syracuseStep 1691657 = 1268743) B1268743
theorem B1692071 : Blo 750330 1692071 := bstep (se 1 (by rfl) ⟨1269053, by rfl⟩ : syracuseStep 1692071 = 2538107) B2538107
theorem B2544047 : Blo 750330 2544047 := bstep (se 1 (by rfl) ⟨1908035, by rfl⟩ : syracuseStep 2544047 = 3816071) B3816071
theorem B1692179 : Blo 750330 1692179 := bstep (se 1 (by rfl) ⟨1269134, by rfl⟩ : syracuseStep 1692179 = 2538269) B2538269
theorem B1266239 : Blo 750330 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B1692233 : Blo 750330 1692233 := bstep (se 2 (by rfl) ⟨634587, by rfl⟩ : syracuseStep 1692233 = 1269175) B1269175
theorem B1430291 : Blo 750330 1430291 := bstep (se 1 (by rfl) ⟨1072718, by rfl⟩ : syracuseStep 1430291 = 2145437) B2145437
theorem B26432477 : Blo 750330 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B1692647 : Blo 750330 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B2085875 : Blo 750330 2085875 := bstep (se 1 (by rfl) ⟨1564406, by rfl⟩ : syracuseStep 2085875 = 3128813) B3128813
theorem B1266907 : Blo 750330 1266907 := bstep (se 1 (by rfl) ⟨950180, by rfl⟩ : syracuseStep 1266907 = 1900361) B1900361
theorem B7230815 : Blo 750330 7230815 := bstep (se 1 (by rfl) ⟨5423111, by rfl⟩ : syracuseStep 7230815 = 10846223) B10846223
theorem B1693025 : Blo 750330 1693025 := bstep (se 2 (by rfl) ⟨634884, by rfl⟩ : syracuseStep 1693025 = 1269769) B1269769
theorem B2741627 : Blo 750330 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B2545019 : Blo 750330 2545019 := bstep (se 1 (by rfl) ⟨1908764, by rfl⟩ : syracuseStep 2545019 = 3817529) B3817529
theorem B1430921 : Blo 750330 1430921 := bstep (se 2 (by rfl) ⟨536595, by rfl⟩ : syracuseStep 1430921 = 1073191) B1073191
theorem B1693115 : Blo 750330 1693115 := bstep (se 1 (by rfl) ⟨1269836, by rfl⟩ : syracuseStep 1693115 = 2539673) B2539673
theorem B1693241 : Blo 750330 1693241 := bstep (se 2 (by rfl) ⟨634965, by rfl⟩ : syracuseStep 1693241 = 1269931) B1269931
theorem B2709335 : Blo 750330 2709335 := bstep (se 1 (by rfl) ⟨2032001, by rfl⟩ : syracuseStep 2709335 = 4064003) B4064003
theorem B1267663 : Blo 750330 1267663 := bstep (se 1 (by rfl) ⟨950747, by rfl⟩ : syracuseStep 1267663 = 1901495) B1901495
theorem B1693907 : Blo 750330 1693907 := bstep (se 1 (by rfl) ⟨1270430, by rfl⟩ : syracuseStep 1693907 = 2540861) B2540861
theorem B5134583 : Blo 750330 5134583 := bstep (se 1 (by rfl) ⟨3850937, by rfl⟩ : syracuseStep 5134583 = 7701875) B7701875
theorem B1693961 : Blo 750330 1693961 := bstep (se 2 (by rfl) ⟨635235, by rfl⟩ : syracuseStep 1693961 = 1270471) B1270471
theorem B1694177 : Blo 750330 1694177 := bstep (se 2 (by rfl) ⟨635316, by rfl⟩ : syracuseStep 1694177 = 1270633) B1270633
theorem B2415167 : Blo 750330 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B4119113 : Blo 750330 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B1268345 : Blo 750330 1268345 := bstep (se 2 (by rfl) ⟨475629, by rfl⟩ : syracuseStep 1268345 = 951259) B951259
theorem B1268399 : Blo 750330 1268399 := bstep (se 1 (by rfl) ⟨951299, by rfl⟩ : syracuseStep 1268399 = 1902599) B1902599
theorem B1694483 : Blo 750330 1694483 := bstep (se 1 (by rfl) ⟨1270862, by rfl⟩ : syracuseStep 1694483 = 2541725) B2541725
theorem B8674121 : Blo 750330 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B1268635 : Blo 750330 1268635 := bstep (se 1 (by rfl) ⟨951476, by rfl⟩ : syracuseStep 1268635 = 1902953) B1902953
theorem B5430203 : Blo 750330 5430203 := bstep (se 1 (by rfl) ⟨4072652, by rfl⟩ : syracuseStep 5430203 = 8145305) B8145305
theorem B1203175 : Blo 750330 1203175 := bstep (se 1 (by rfl) ⟨902381, by rfl⟩ : syracuseStep 1203175 = 1804763) B1804763
theorem B1694843 : Blo 750330 1694843 := bstep (se 1 (by rfl) ⟨1271132, by rfl⟩ : syracuseStep 1694843 = 2542265) B2542265
theorem B1694969 : Blo 750330 1694969 := bstep (se 2 (by rfl) ⟨635613, by rfl⟩ : syracuseStep 1694969 = 1271227) B1271227
theorem B1695113 : Blo 750330 1695113 := bstep (se 2 (by rfl) ⟨635667, by rfl⟩ : syracuseStep 1695113 = 1271335) B1271335
theorem B1695239 : Blo 750330 1695239 := bstep (se 1 (by rfl) ⟨1271429, by rfl⟩ : syracuseStep 1695239 = 2542859) B2542859
theorem B12213803 : Blo 750330 12213803 := bstep (se 1 (by rfl) ⟨9160352, by rfl⟩ : syracuseStep 12213803 = 18320705) B18320705
theorem B2416243 : Blo 750330 2416243 := bstep (se 1 (by rfl) ⟨1812182, by rfl⟩ : syracuseStep 2416243 = 3624365) B3624365
theorem B1695419 : Blo 750330 1695419 := bstep (se 1 (by rfl) ⟨1271564, by rfl⟩ : syracuseStep 1695419 = 2543129) B2543129
theorem B1629931 : Blo 750330 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B1695545 : Blo 750330 1695545 := bstep (se 2 (by rfl) ⟨635829, by rfl⟩ : syracuseStep 1695545 = 1271659) B1271659
theorem B24338339 : Blo 750330 24338339 := bstep (se 1 (by rfl) ⟨18253754, by rfl⟩ : syracuseStep 24338339 = 36507509) B36507509
theorem B4710611 : Blo 750330 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B844123 : Blo 750330 844123 := bstep (se 1 (by rfl) ⟨633092, by rfl⟩ : syracuseStep 844123 = 1266185) B1266185
theorem B1270127 : Blo 750330 1270127 := bstep (se 1 (by rfl) ⟨952595, by rfl⟩ : syracuseStep 1270127 = 1905191) B1905191
theorem B1696175 : Blo 750330 1696175 := bstep (se 1 (by rfl) ⟨1272131, by rfl⟩ : syracuseStep 1696175 = 2544263) B2544263
theorem B844231 : Blo 750330 844231 := bstep (se 1 (by rfl) ⟨633173, by rfl⟩ : syracuseStep 844231 = 1266347) B1266347
theorem B1696211 : Blo 750330 1696211 := bstep (se 1 (by rfl) ⟨1272158, by rfl⟩ : syracuseStep 1696211 = 2544317) B2544317
theorem B1696319 : Blo 750330 1696319 := bstep (se 1 (by rfl) ⟨1272239, by rfl⟩ : syracuseStep 1696319 = 2544479) B2544479
theorem B1270343 : Blo 750330 1270343 := bstep (se 1 (by rfl) ⟨952757, by rfl⟩ : syracuseStep 1270343 = 1905515) B1905515
theorem B1696427 : Blo 750330 1696427 := bstep (se 1 (by rfl) ⟨1272320, by rfl⟩ : syracuseStep 1696427 = 2544641) B2544641
theorem B4809419 : Blo 750330 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B844591 : Blo 750330 844591 := bstep (se 1 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 844591 = 1266887) B1266887
theorem B844699 : Blo 750330 844699 := bstep (se 1 (by rfl) ⟨633524, by rfl⟩ : syracuseStep 844699 = 1267049) B1267049
theorem B1270775 : Blo 750330 1270775 := bstep (se 1 (by rfl) ⟨953081, by rfl⟩ : syracuseStep 1270775 = 1906163) B1906163
theorem B1696967 : Blo 750330 1696967 := bstep (se 1 (by rfl) ⟨1272725, by rfl⟩ : syracuseStep 1696967 = 2545451) B2545451
theorem B845095 : Blo 750330 845095 := bstep (se 1 (by rfl) ⟨633821, by rfl⟩ : syracuseStep 845095 = 1267643) B1267643
theorem B845167 : Blo 750330 845167 := bstep (se 1 (by rfl) ⟨633875, by rfl⟩ : syracuseStep 845167 = 1267751) B1267751
theorem B1697147 : Blo 750330 1697147 := bstep (se 1 (by rfl) ⟨1272860, by rfl⟩ : syracuseStep 1697147 = 2545721) B2545721
theorem B21685745 : Blo 750330 21685745 := bstep (se 2 (by rfl) ⟨8132154, by rfl⟩ : syracuseStep 21685745 = 16264309) B16264309
theorem B976379 : Blo 750330 976379 := bstep (se 1 (by rfl) ⟨732284, by rfl⟩ : syracuseStep 976379 = 1464569) B1464569
theorem B845383 : Blo 750330 845383 := bstep (se 1 (by rfl) ⟨634037, by rfl⟩ : syracuseStep 845383 = 1268075) B1268075
theorem B1271531 : Blo 750330 1271531 := bstep (se 1 (by rfl) ⟨953648, by rfl⟩ : syracuseStep 1271531 = 1907297) B1907297
theorem B8120573 : Blo 750330 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B3664151 : Blo 750330 3664151 := bstep (se 1 (by rfl) ⟨2748113, by rfl⟩ : syracuseStep 3664151 = 5496227) B5496227
theorem B846247 : Blo 750330 846247 := bstep (se 1 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 846247 = 1269371) B1269371
theorem B1272503 : Blo 750330 1272503 := bstep (se 1 (by rfl) ⟨954377, by rfl⟩ : syracuseStep 1272503 = 1908755) B1908755
theorem B1829623 : Blo 750330 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B846823 : Blo 750330 846823 := bstep (se 1 (by rfl) ⟨635117, by rfl⟩ : syracuseStep 846823 = 1270235) B1270235
theorem B13200653 : Blo 750330 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B814447 : Blo 750330 814447 := bstep (se 1 (by rfl) ⟨610835, by rfl⟩ : syracuseStep 814447 = 1221671) B1221671
theorem B3206537 : Blo 750330 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B3206587 : Blo 750330 3206587 := bstep (se 1 (by rfl) ⟨2404940, by rfl⟩ : syracuseStep 3206587 = 4809881) B4809881
theorem B1207801 : Blo 750330 1207801 := bstep (se 2 (by rfl) ⟨452925, by rfl⟩ : syracuseStep 1207801 = 905851) B905851
theorem B3436141 : Blo 750330 3436141 := bstep (se 3 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 3436141 = 1288553) B1288553
theorem B19328705 : Blo 750330 19328705 := bstep (se 2 (by rfl) ⟨7248264, by rfl⟩ : syracuseStep 19328705 = 14496529) B14496529
theorem B1830635 : Blo 750330 1830635 := bstep (se 1 (by rfl) ⟨1372976, by rfl⟩ : syracuseStep 1830635 = 2745953) B2745953
theorem B4288571 : Blo 750330 4288571 := bstep (se 1 (by rfl) ⟨3216428, by rfl⟩ : syracuseStep 4288571 = 6432857) B6432857
theorem B848479 : Blo 750330 848479 := bstep (se 1 (by rfl) ⟨636359, by rfl⟩ : syracuseStep 848479 = 1272719) B1272719
theorem B750383 : Blo 750330 750383 := bstep (se 1 (by rfl) ⟨562787, by rfl⟩ : syracuseStep 750383 = 1125575) B1125575
theorem B750491 : Blo 750330 750491 := bstep (se 1 (by rfl) ⟨562868, by rfl⟩ : syracuseStep 750491 = 1125737) B1125737
theorem B750543 : Blo 750330 750543 := bstep (se 1 (by rfl) ⟨562907, by rfl⟩ : syracuseStep 750543 = 1125815) B1125815
theorem B750567 : Blo 750330 750567 := bstep (se 1 (by rfl) ⟨562925, by rfl⟩ : syracuseStep 750567 = 1125851) B1125851
theorem B12842063 : Blo 750330 12842063 := bstep (se 1 (by rfl) ⟨9631547, by rfl⟩ : syracuseStep 12842063 = 19263095) B19263095
theorem B3044567 : Blo 750330 3044567 := bstep (se 1 (by rfl) ⟨2283425, by rfl⟩ : syracuseStep 3044567 = 4566851) B4566851
theorem B6419735 : Blo 750330 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B750879 : Blo 750330 750879 := bstep (se 1 (by rfl) ⟨563159, by rfl⟩ : syracuseStep 750879 = 1126319) B1126319
theorem B3208535 : Blo 750330 3208535 := bstep (se 1 (by rfl) ⟨2406401, by rfl⟩ : syracuseStep 3208535 = 4812803) B4812803
theorem B750939 : Blo 750330 750939 := bstep (se 1 (by rfl) ⟨563204, by rfl⟩ : syracuseStep 750939 = 1126409) B1126409
theorem B750959 : Blo 750330 750959 := bstep (se 1 (by rfl) ⟨563219, by rfl⟩ : syracuseStep 750959 = 1126439) B1126439
theorem B751015 : Blo 750330 751015 := bstep (se 1 (by rfl) ⟨563261, by rfl⟩ : syracuseStep 751015 = 1126523) B1126523
theorem B1603003 : Blo 750330 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B8123851 : Blo 750330 8123851 := bstep (se 1 (by rfl) ⟨6092888, by rfl⟩ : syracuseStep 8123851 = 12185777) B12185777
theorem B4290029 : Blo 750330 4290029 := bstep (se 3 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 4290029 = 1608761) B1608761
theorem B751099 : Blo 750330 751099 := bstep (se 1 (by rfl) ⟨563324, by rfl⟩ : syracuseStep 751099 = 1126649) B1126649
theorem B751167 : Blo 750330 751167 := bstep (se 1 (by rfl) ⟨563375, by rfl⟩ : syracuseStep 751167 = 1126751) B1126751
theorem B751175 : Blo 750330 751175 := bstep (se 1 (by rfl) ⟨563381, by rfl⟩ : syracuseStep 751175 = 1126763) B1126763
theorem B751327 : Blo 750330 751327 := bstep (se 1 (by rfl) ⟨563495, by rfl⟩ : syracuseStep 751327 = 1126991) B1126991
theorem B751407 : Blo 750330 751407 := bstep (se 1 (by rfl) ⟨563555, by rfl⟩ : syracuseStep 751407 = 1127111) B1127111
theorem B751515 : Blo 750330 751515 := bstep (se 1 (by rfl) ⟨563636, by rfl⟩ : syracuseStep 751515 = 1127273) B1127273
theorem B751567 : Blo 750330 751567 := bstep (se 1 (by rfl) ⟨563675, by rfl⟩ : syracuseStep 751567 = 1127351) B1127351
theorem B751591 : Blo 750330 751591 := bstep (se 1 (by rfl) ⟨563693, by rfl⟩ : syracuseStep 751591 = 1127387) B1127387
theorem B2849053 : Blo 750330 2849053 := bstep (se 3 (by rfl) ⟨534197, by rfl⟩ : syracuseStep 2849053 = 1068395) B1068395
theorem B751903 : Blo 750330 751903 := bstep (se 1 (by rfl) ⟨563927, by rfl⟩ : syracuseStep 751903 = 1127855) B1127855
theorem B751963 : Blo 750330 751963 := bstep (se 1 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 751963 = 1127945) B1127945
theorem B751983 : Blo 750330 751983 := bstep (se 1 (by rfl) ⟨563987, by rfl⟩ : syracuseStep 751983 = 1127975) B1127975
theorem B13236605 : Blo 750330 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B752039 : Blo 750330 752039 := bstep (se 1 (by rfl) ⟨564029, by rfl⟩ : syracuseStep 752039 = 1128059) B1128059
theorem B3799547 : Blo 750330 3799547 := bstep (se 1 (by rfl) ⟨2849660, by rfl⟩ : syracuseStep 3799547 = 5699321) B5699321
theorem B752123 : Blo 750330 752123 := bstep (se 1 (by rfl) ⟨564092, by rfl⟩ : syracuseStep 752123 = 1128185) B1128185
theorem B1735231 : Blo 750330 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B752191 : Blo 750330 752191 := bstep (se 1 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 752191 = 1128287) B1128287
theorem B752199 : Blo 750330 752199 := bstep (se 1 (by rfl) ⟨564149, by rfl⟩ : syracuseStep 752199 = 1128299) B1128299
theorem B7731845 : Blo 750330 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B752351 : Blo 750330 752351 := bstep (se 1 (by rfl) ⟨564263, by rfl⟩ : syracuseStep 752351 = 1128527) B1128527
theorem B752431 : Blo 750330 752431 := bstep (se 1 (by rfl) ⟨564323, by rfl⟩ : syracuseStep 752431 = 1128647) B1128647
theorem B752539 : Blo 750330 752539 := bstep (se 1 (by rfl) ⟨564404, by rfl⟩ : syracuseStep 752539 = 1128809) B1128809
theorem B752591 : Blo 750330 752591 := bstep (se 1 (by rfl) ⟨564443, by rfl⟩ : syracuseStep 752591 = 1128887) B1128887
theorem B752615 : Blo 750330 752615 := bstep (se 1 (by rfl) ⟨564461, by rfl⟩ : syracuseStep 752615 = 1128923) B1128923
theorem B1932427 : Blo 750330 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B2030791 : Blo 750330 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B2850011 : Blo 750330 2850011 := bstep (se 1 (by rfl) ⟨2137508, by rfl⟩ : syracuseStep 2850011 = 4275017) B4275017
theorem B4291805 : Blo 750330 4291805 := bstep (se 3 (by rfl) ⟨804713, by rfl⟩ : syracuseStep 4291805 = 1609427) B1609427
theorem B752927 : Blo 750330 752927 := bstep (se 1 (by rfl) ⟨564695, by rfl⟩ : syracuseStep 752927 = 1129391) B1129391
theorem B752987 : Blo 750330 752987 := bstep (se 1 (by rfl) ⟨564740, by rfl⟩ : syracuseStep 752987 = 1129481) B1129481
theorem B753007 : Blo 750330 753007 := bstep (se 1 (by rfl) ⟨564755, by rfl⟩ : syracuseStep 753007 = 1129511) B1129511
theorem B753063 : Blo 750330 753063 := bstep (se 1 (by rfl) ⟨564797, by rfl⟩ : syracuseStep 753063 = 1129595) B1129595
theorem B3800519 : Blo 750330 3800519 := bstep (se 1 (by rfl) ⟨2850389, by rfl⟩ : syracuseStep 3800519 = 5700779) B5700779
theorem B9665993 : Blo 750330 9665993 := bstep (se 2 (by rfl) ⟨3624747, by rfl⟩ : syracuseStep 9665993 = 7249495) B7249495
theorem B5144057 : Blo 750330 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B753147 : Blo 750330 753147 := bstep (se 1 (by rfl) ⟨564860, by rfl⟩ : syracuseStep 753147 = 1129721) B1129721
theorem B753215 : Blo 750330 753215 := bstep (se 1 (by rfl) ⟨564911, by rfl⟩ : syracuseStep 753215 = 1129823) B1129823
theorem B753223 : Blo 750330 753223 := bstep (se 1 (by rfl) ⟨564917, by rfl⟩ : syracuseStep 753223 = 1129835) B1129835
theorem B1900219 : Blo 750330 1900219 := bstep (se 1 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 1900219 = 2850329) B2850329
theorem B3210961 : Blo 750330 3210961 := bstep (se 2 (by rfl) ⟨1204110, by rfl⟩ : syracuseStep 3210961 = 2408221) B2408221
theorem B753375 : Blo 750330 753375 := bstep (se 1 (by rfl) ⟨565031, by rfl⟩ : syracuseStep 753375 = 1130063) B1130063
theorem B3800843 : Blo 750330 3800843 := bstep (se 1 (by rfl) ⟨2850632, by rfl⟩ : syracuseStep 3800843 = 5701265) B5701265
theorem B753455 : Blo 750330 753455 := bstep (se 1 (by rfl) ⟨565091, by rfl⟩ : syracuseStep 753455 = 1130183) B1130183
theorem B753563 : Blo 750330 753563 := bstep (se 1 (by rfl) ⟨565172, by rfl⟩ : syracuseStep 753563 = 1130345) B1130345
theorem B7339951 : Blo 750330 7339951 := bstep (se 1 (by rfl) ⟨5504963, by rfl⟩ : syracuseStep 7339951 = 11009927) B11009927
theorem B753615 : Blo 750330 753615 := bstep (se 1 (by rfl) ⟨565211, by rfl⟩ : syracuseStep 753615 = 1130423) B1130423
theorem B753639 : Blo 750330 753639 := bstep (se 1 (by rfl) ⟨565229, by rfl⟩ : syracuseStep 753639 = 1130459) B1130459
theorem B3801167 : Blo 750330 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B753895 : Blo 750330 753895 := bstep (se 1 (by rfl) ⟨565421, by rfl⟩ : syracuseStep 753895 = 1130843) B1130843
theorem B14483771 : Blo 750330 14483771 := bstep (se 1 (by rfl) ⟨10862828, by rfl⟩ : syracuseStep 14483771 = 21725657) B21725657
theorem B754047 : Blo 750330 754047 := bstep (se 1 (by rfl) ⟨565535, by rfl⟩ : syracuseStep 754047 = 1131071) B1131071
theorem B2851271 : Blo 750330 2851271 := bstep (se 1 (by rfl) ⟨2138453, by rfl⟩ : syracuseStep 2851271 = 4276907) B4276907
theorem B754127 : Blo 750330 754127 := bstep (se 1 (by rfl) ⟨565595, by rfl⟩ : syracuseStep 754127 = 1131191) B1131191
theorem B3146303 : Blo 750330 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B754279 : Blo 750330 754279 := bstep (se 1 (by rfl) ⟨565709, by rfl⟩ : syracuseStep 754279 = 1131419) B1131419
theorem B3211883 : Blo 750330 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B24413071 : Blo 750330 24413071 := bstep (se 1 (by rfl) ⟨18309803, by rfl⟩ : syracuseStep 24413071 = 36619607) B36619607
theorem B2033171 : Blo 750330 2033171 := bstep (se 1 (by rfl) ⟨1524878, by rfl⟩ : syracuseStep 2033171 = 3049757) B3049757
theorem B1803995 : Blo 750330 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B4818953 : Blo 750330 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B3213523 : Blo 750330 3213523 := bstep (se 1 (by rfl) ⟨2410142, by rfl⟩ : syracuseStep 3213523 = 4820285) B4820285
theorem B952555 : Blo 750330 952555 := bstep (se 1 (by rfl) ⟨714416, by rfl⟩ : syracuseStep 952555 = 1428833) B1428833
theorem B4294903 : Blo 750330 4294903 := bstep (se 1 (by rfl) ⟨3221177, by rfl⟩ : syracuseStep 4294903 = 6442355) B6442355
theorem B2034077 : Blo 750330 2034077 := bstep (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) B762779
theorem B1903135 : Blo 750330 1903135 := bstep (se 1 (by rfl) ⟨1427351, by rfl⟩ : syracuseStep 1903135 = 2854703) B2854703
theorem B953527 : Blo 750330 953527 := bstep (se 1 (by rfl) ⟨715145, by rfl⟩ : syracuseStep 953527 = 1430291) B1430291
theorem B4820543 : Blo 750330 4820543 := bstep (se 1 (by rfl) ⟨3615407, by rfl⟩ : syracuseStep 4820543 = 7230815) B7230815
theorem B953947 : Blo 750330 953947 := bstep (se 1 (by rfl) ⟨715460, by rfl⟩ : syracuseStep 953947 = 1430921) B1430921
theorem B7311005 : Blo 750330 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B1806223 : Blo 750330 1806223 := bstep (se 1 (by rfl) ⟨1354667, by rfl⟩ : syracuseStep 1806223 = 2709335) B2709335
theorem B1610111 : Blo 750330 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B1085929 : Blo 750330 1085929 := bstep (se 2 (by rfl) ⟨407223, by rfl⟩ : syracuseStep 1085929 = 814447) B814447
theorem B3216257 : Blo 750330 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B1905727 : Blo 750330 1905727 := bstep (se 1 (by rfl) ⟨1429295, by rfl⟩ : syracuseStep 1905727 = 2858591) B2858591
theorem B1905839 : Blo 750330 1905839 := bstep (se 1 (by rfl) ⟨1429379, by rfl⟩ : syracuseStep 1905839 = 2858759) B2858759
theorem B16225559 : Blo 750330 16225559 := bstep (se 1 (by rfl) ⟨12169169, by rfl⟩ : syracuseStep 16225559 = 24338339) B24338339
theorem B20551481 : Blo 750330 20551481 := bstep (se 2 (by rfl) ⟨7706805, by rfl⟩ : syracuseStep 20551481 = 15413611) B15413611
theorem B6428483 : Blo 750330 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B14457163 : Blo 750330 14457163 := bstep (se 1 (by rfl) ⟨10842872, by rfl⟩ : syracuseStep 14457163 = 21685745) B21685745
theorem B6101423 : Blo 750330 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B6429233 : Blo 750330 6429233 := bstep (se 2 (by rfl) ⟨2410962, by rfl⟩ : syracuseStep 6429233 = 4821925) B4821925
theorem B5413715 : Blo 750330 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B1907783 : Blo 750330 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B2137337 : Blo 750330 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B2137691 : Blo 750330 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B12885803 : Blo 750330 12885803 := bstep (se 1 (by rfl) ⟨9664352, by rfl⟩ : syracuseStep 12885803 = 19328705) B19328705
theorem B1220423 : Blo 750330 1220423 := bstep (se 1 (by rfl) ⟨915317, by rfl⟩ : syracuseStep 1220423 = 1830635) B1830635
theorem B2859047 : Blo 750330 2859047 := bstep (se 1 (by rfl) ⟨2144285, by rfl⟩ : syracuseStep 2859047 = 4288571) B4288571
theorem B1908967 : Blo 750330 1908967 := bstep (se 1 (by rfl) ⟨1431725, by rfl⟩ : syracuseStep 1908967 = 2863451) B2863451
theorem B3219743 : Blo 750330 3219743 := bstep (se 1 (by rfl) ⟨2414807, by rfl⟩ : syracuseStep 3219743 = 4829615) B4829615
theorem B8561375 : Blo 750330 8561375 := bstep (se 1 (by rfl) ⟨6421031, by rfl⟩ : syracuseStep 8561375 = 12842063) B12842063
theorem B2139023 : Blo 750330 2139023 := bstep (se 1 (by rfl) ⟨1604267, by rfl⟩ : syracuseStep 2139023 = 3208535) B3208535
theorem B2860019 : Blo 750330 2860019 := bstep (se 1 (by rfl) ⟨2145014, by rfl⟩ : syracuseStep 2860019 = 4290029) B4290029
theorem B41100533 : Blo 750330 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B8824403 : Blo 750330 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B2533031 : Blo 750330 2533031 := bstep (se 1 (by rfl) ⟨1899773, by rfl⟩ : syracuseStep 2533031 = 3799547) B3799547
theorem B5154563 : Blo 750330 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B16262927 : Blo 750330 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B2861203 : Blo 750330 2861203 := bstep (se 1 (by rfl) ⟨2145902, by rfl⟩ : syracuseStep 2861203 = 4291805) B4291805
theorem B3221657 : Blo 750330 3221657 := bstep (se 2 (by rfl) ⟨1208121, by rfl⟩ : syracuseStep 3221657 = 2416243) B2416243
theorem B2533625 : Blo 750330 2533625 := bstep (se 2 (by rfl) ⟨950109, by rfl⟩ : syracuseStep 2533625 = 1900219) B1900219
theorem B2533679 : Blo 750330 2533679 := bstep (se 1 (by rfl) ⟨1900259, by rfl⟩ : syracuseStep 2533679 = 3800519) B3800519
theorem B2173241 : Blo 750330 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B2533895 : Blo 750330 2533895 := bstep (se 1 (by rfl) ⟨1900421, by rfl⟩ : syracuseStep 2533895 = 3800843) B3800843
theorem B1158047 : Blo 750330 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B1125497 : Blo 750330 1125497 := bstep (se 2 (by rfl) ⟨422061, by rfl⟩ : syracuseStep 1125497 = 844123) B844123
theorem B2534543 : Blo 750330 2534543 := bstep (se 1 (by rfl) ⟨1900907, by rfl⟩ : syracuseStep 2534543 = 3801815) B3801815
theorem B1125599 : Blo 750330 1125599 := bstep (se 1 (by rfl) ⟨844199, by rfl⟩ : syracuseStep 1125599 = 1688399) B1688399
theorem B1125641 : Blo 750330 1125641 := bstep (se 2 (by rfl) ⟨422115, by rfl⟩ : syracuseStep 1125641 = 844231) B844231
theorem B1125743 : Blo 750330 1125743 := bstep (se 1 (by rfl) ⟨844307, by rfl⟩ : syracuseStep 1125743 = 1688615) B1688615
theorem B1125863 : Blo 750330 1125863 := bstep (se 1 (by rfl) ⟨844397, by rfl⟩ : syracuseStep 1125863 = 1688795) B1688795
theorem B2534975 : Blo 750330 2534975 := bstep (se 1 (by rfl) ⟨1901231, by rfl⟩ : syracuseStep 2534975 = 3802463) B3802463
theorem B1125995 : Blo 750330 1125995 := bstep (se 1 (by rfl) ⟨844496, by rfl⟩ : syracuseStep 1125995 = 1688993) B1688993
theorem B1126121 : Blo 750330 1126121 := bstep (se 2 (by rfl) ⟨422295, by rfl⟩ : syracuseStep 1126121 = 844591) B844591
theorem B1126265 : Blo 750330 1126265 := bstep (se 2 (by rfl) ⟨422349, by rfl⟩ : syracuseStep 1126265 = 844699) B844699
theorem B1126367 : Blo 750330 1126367 := bstep (se 1 (by rfl) ⟨844775, by rfl⟩ : syracuseStep 1126367 = 1689551) B1689551
theorem B2142395 : Blo 750330 2142395 := bstep (se 1 (by rfl) ⟨1606796, by rfl⟩ : syracuseStep 2142395 = 3213593) B3213593
theorem B4468931 : Blo 750330 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1126619 : Blo 750330 1126619 := bstep (se 1 (by rfl) ⟨844964, by rfl⟩ : syracuseStep 1126619 = 1689929) B1689929
theorem B1126631 : Blo 750330 1126631 := bstep (se 1 (by rfl) ⟨844973, by rfl⟩ : syracuseStep 1126631 = 1689947) B1689947
theorem B2535677 : Blo 750330 2535677 := bstep (se 3 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 2535677 = 950879) B950879
theorem B3813641 : Blo 750330 3813641 := bstep (se 2 (by rfl) ⟨1430115, by rfl⟩ : syracuseStep 3813641 = 2860231) B2860231
theorem B1126793 : Blo 750330 1126793 := bstep (se 2 (by rfl) ⟨422547, by rfl⟩ : syracuseStep 1126793 = 845095) B845095
theorem B4895201 : Blo 750330 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B1126889 : Blo 750330 1126889 := bstep (se 2 (by rfl) ⟨422583, by rfl⟩ : syracuseStep 1126889 = 845167) B845167
theorem B2142713 : Blo 750330 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B1127015 : Blo 750330 1127015 := bstep (se 1 (by rfl) ⟨845261, by rfl⟩ : syracuseStep 1127015 = 1690523) B1690523
theorem B1127147 : Blo 750330 1127147 := bstep (se 1 (by rfl) ⟨845360, by rfl⟩ : syracuseStep 1127147 = 1690721) B1690721
theorem B1127177 : Blo 750330 1127177 := bstep (se 2 (by rfl) ⟨422691, by rfl⟩ : syracuseStep 1127177 = 845383) B845383
theorem B2536217 : Blo 750330 2536217 := bstep (se 2 (by rfl) ⟨951081, by rfl⟩ : syracuseStep 2536217 = 1902163) B1902163
theorem B1127279 : Blo 750330 1127279 := bstep (se 1 (by rfl) ⟨845459, by rfl⟩ : syracuseStep 1127279 = 1690919) B1690919
theorem B2536487 : Blo 750330 2536487 := bstep (se 1 (by rfl) ⟨1902365, by rfl⟩ : syracuseStep 2536487 = 3804731) B3804731
theorem B1127531 : Blo 750330 1127531 := bstep (se 1 (by rfl) ⟨845648, by rfl⟩ : syracuseStep 1127531 = 1691297) B1691297
theorem B4830515 : Blo 750330 4830515 := bstep (se 1 (by rfl) ⟨3622886, by rfl⟩ : syracuseStep 4830515 = 7245773) B7245773
theorem B1127771 : Blo 750330 1127771 := bstep (se 1 (by rfl) ⟨845828, by rfl⟩ : syracuseStep 1127771 = 1691657) B1691657
theorem B2143579 : Blo 750330 2143579 := bstep (se 1 (by rfl) ⟨1607684, by rfl⟩ : syracuseStep 2143579 = 3215369) B3215369
theorem B1128047 : Blo 750330 1128047 := bstep (se 1 (by rfl) ⟨846035, by rfl⟩ : syracuseStep 1128047 = 1692071) B1692071
theorem B1128119 : Blo 750330 1128119 := bstep (se 1 (by rfl) ⟨846089, by rfl⟩ : syracuseStep 1128119 = 1692179) B1692179
theorem B1128155 : Blo 750330 1128155 := bstep (se 1 (by rfl) ⟨846116, by rfl⟩ : syracuseStep 1128155 = 1692233) B1692233
theorem B2143979 : Blo 750330 2143979 := bstep (se 1 (by rfl) ⟨1607984, by rfl⟩ : syracuseStep 2143979 = 3215969) B3215969
theorem B1128329 : Blo 750330 1128329 := bstep (se 2 (by rfl) ⟨423123, by rfl⟩ : syracuseStep 1128329 = 846247) B846247
theorem B1128431 : Blo 750330 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B1390583 : Blo 750330 1390583 := bstep (se 1 (by rfl) ⟨1042937, by rfl⟩ : syracuseStep 1390583 = 2085875) B2085875
theorem B2537567 : Blo 750330 2537567 := bstep (se 1 (by rfl) ⟨1903175, by rfl⟩ : syracuseStep 2537567 = 3806351) B3806351
theorem B1128683 : Blo 750330 1128683 := bstep (se 1 (by rfl) ⟨846512, by rfl⟩ : syracuseStep 1128683 = 1693025) B1693025
theorem B1128743 : Blo 750330 1128743 := bstep (se 1 (by rfl) ⟨846557, by rfl⟩ : syracuseStep 1128743 = 1693115) B1693115
theorem B2439497 : Blo 750330 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B1128827 : Blo 750330 1128827 := bstep (se 1 (by rfl) ⟨846620, by rfl⟩ : syracuseStep 1128827 = 1693241) B1693241
theorem B1129097 : Blo 750330 1129097 := bstep (se 2 (by rfl) ⟨423411, by rfl⟩ : syracuseStep 1129097 = 846823) B846823
theorem B2603677 : Blo 750330 2603677 := bstep (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) B976379
theorem B1129271 : Blo 750330 1129271 := bstep (se 1 (by rfl) ⟨846953, by rfl⟩ : syracuseStep 1129271 = 1693907) B1693907
theorem B3423055 : Blo 750330 3423055 := bstep (se 1 (by rfl) ⟨2567291, by rfl⟩ : syracuseStep 3423055 = 5134583) B5134583
theorem B2538323 : Blo 750330 2538323 := bstep (se 1 (by rfl) ⟨1903742, by rfl⟩ : syracuseStep 2538323 = 3807485) B3807485
theorem B1129307 : Blo 750330 1129307 := bstep (se 1 (by rfl) ⟨846980, by rfl⟩ : syracuseStep 1129307 = 1693961) B1693961
theorem B1719265 : Blo 750330 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B1129451 : Blo 750330 1129451 := bstep (se 1 (by rfl) ⟨847088, by rfl⟩ : syracuseStep 1129451 = 1694177) B1694177
theorem B2407607 : Blo 750330 2407607 := bstep (se 1 (by rfl) ⟨1805705, by rfl⟩ : syracuseStep 2407607 = 3611411) B3611411
theorem B1129655 : Blo 750330 1129655 := bstep (se 1 (by rfl) ⟨847241, by rfl⟩ : syracuseStep 1129655 = 1694483) B1694483
theorem B5782747 : Blo 750330 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B4275449 : Blo 750330 4275449 := bstep (se 2 (by rfl) ⟨1603293, by rfl⟩ : syracuseStep 4275449 = 3206587) B3206587
theorem B3620135 : Blo 750330 3620135 := bstep (se 1 (by rfl) ⟨2715101, by rfl⟩ : syracuseStep 3620135 = 5430203) B5430203
theorem B2538863 : Blo 750330 2538863 := bstep (se 1 (by rfl) ⟨1904147, by rfl⟩ : syracuseStep 2538863 = 3808295) B3808295
theorem B1129895 : Blo 750330 1129895 := bstep (se 1 (by rfl) ⟨847421, by rfl⟩ : syracuseStep 1129895 = 1694843) B1694843
theorem B5422565 : Blo 750330 5422565 := bstep (se 4 (by rfl) ⟨508365, by rfl⟩ : syracuseStep 5422565 = 1016731) B1016731
theorem B1129979 : Blo 750330 1129979 := bstep (se 1 (by rfl) ⟨847484, by rfl⟩ : syracuseStep 1129979 = 1694969) B1694969
theorem B1130075 : Blo 750330 1130075 := bstep (se 1 (by rfl) ⟨847556, by rfl⟩ : syracuseStep 1130075 = 1695113) B1695113
theorem B1130159 : Blo 750330 1130159 := bstep (se 1 (by rfl) ⟨847619, by rfl⟩ : syracuseStep 1130159 = 1695239) B1695239
theorem B8142535 : Blo 750330 8142535 := bstep (se 1 (by rfl) ⟨6106901, by rfl⟩ : syracuseStep 8142535 = 12213803) B12213803
theorem B2539241 : Blo 750330 2539241 := bstep (se 2 (by rfl) ⟨952215, by rfl⟩ : syracuseStep 2539241 = 1904431) B1904431
theorem B1130279 : Blo 750330 1130279 := bstep (se 1 (by rfl) ⟨847709, by rfl⟩ : syracuseStep 1130279 = 1695419) B1695419
theorem B1130363 : Blo 750330 1130363 := bstep (se 1 (by rfl) ⟨847772, by rfl⟩ : syracuseStep 1130363 = 1695545) B1695545
theorem B9158609 : Blo 750330 9158609 := bstep (se 2 (by rfl) ⟨3434478, by rfl⟩ : syracuseStep 9158609 = 6868957) B6868957
theorem B3260555 : Blo 750330 3260555 := bstep (se 1 (by rfl) ⟨2445416, by rfl⟩ : syracuseStep 3260555 = 4890833) B4890833
theorem B1130783 : Blo 750330 1130783 := bstep (se 1 (by rfl) ⟨848087, by rfl⟩ : syracuseStep 1130783 = 1696175) B1696175
theorem B1130807 : Blo 750330 1130807 := bstep (se 1 (by rfl) ⟨848105, by rfl⟩ : syracuseStep 1130807 = 1696211) B1696211
theorem B1130879 : Blo 750330 1130879 := bstep (se 1 (by rfl) ⟨848159, by rfl⟩ : syracuseStep 1130879 = 1696319) B1696319
theorem B1425863 : Blo 750330 1425863 := bstep (se 1 (by rfl) ⟨1069397, by rfl⟩ : syracuseStep 1425863 = 2138795) B2138795
theorem B1130951 : Blo 750330 1130951 := bstep (se 1 (by rfl) ⟨848213, by rfl⟩ : syracuseStep 1130951 = 1696427) B1696427
theorem B2540105 : Blo 750330 2540105 := bstep (se 2 (by rfl) ⟨952539, by rfl⟩ : syracuseStep 2540105 = 1905079) B1905079
theorem B2540267 : Blo 750330 2540267 := bstep (se 1 (by rfl) ⟨1905200, by rfl⟩ : syracuseStep 2540267 = 3810401) B3810401
theorem B1131305 : Blo 750330 1131305 := bstep (se 2 (by rfl) ⟨424239, by rfl⟩ : syracuseStep 1131305 = 848479) B848479
theorem B1131311 : Blo 750330 1131311 := bstep (se 1 (by rfl) ⟨848483, by rfl⟩ : syracuseStep 1131311 = 1696967) B1696967
theorem B1131431 : Blo 750330 1131431 := bstep (se 1 (by rfl) ⟨848573, by rfl⟩ : syracuseStep 1131431 = 1697147) B1697147
theorem B8570123 : Blo 750330 8570123 := bstep (se 1 (by rfl) ⟨6427592, by rfl⟩ : syracuseStep 8570123 = 12855185) B12855185
theorem B1688939 : Blo 750330 1688939 := bstep (se 1 (by rfl) ⟨1266704, by rfl⟩ : syracuseStep 1688939 = 2533409) B2533409
theorem B2442767 : Blo 750330 2442767 := bstep (se 1 (by rfl) ⟨1832075, by rfl⟩ : syracuseStep 2442767 = 3664151) B3664151
theorem B2410067 : Blo 750330 2410067 := bstep (se 1 (by rfl) ⟨1807550, by rfl⟩ : syracuseStep 2410067 = 3615101) B3615101
theorem B1689209 : Blo 750330 1689209 := bstep (se 2 (by rfl) ⟨633453, by rfl⟩ : syracuseStep 1689209 = 1266907) B1266907
theorem B2410337 : Blo 750330 2410337 := bstep (se 2 (by rfl) ⟨903876, by rfl⟩ : syracuseStep 2410337 = 1807753) B1807753
theorem B10831801 : Blo 750330 10831801 := bstep (se 2 (by rfl) ⟨4061925, by rfl⟩ : syracuseStep 10831801 = 8123851) B8123851
theorem B8800435 : Blo 750330 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B2541779 : Blo 750330 2541779 := bstep (se 1 (by rfl) ⟨1906334, by rfl⟩ : syracuseStep 2541779 = 3812669) B3812669
theorem B2542049 : Blo 750330 2542049 := bstep (se 2 (by rfl) ⟨953268, by rfl⟩ : syracuseStep 2542049 = 1906537) B1906537
theorem B1690217 : Blo 750330 1690217 := bstep (se 2 (by rfl) ⟨633831, by rfl⟩ : syracuseStep 1690217 = 1267663) B1267663
theorem B6441605 : Blo 750330 6441605 := bstep (se 4 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 6441605 = 1207801) B1207801
theorem B5425879 : Blo 750330 5425879 := bstep (se 1 (by rfl) ⟨4069409, by rfl⟩ : syracuseStep 5425879 = 8138819) B8138819
theorem B1690847 : Blo 750330 1690847 := bstep (se 1 (by rfl) ⟨1268135, by rfl⟩ : syracuseStep 1690847 = 2536271) B2536271
theorem B2313641 : Blo 750330 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B1691063 : Blo 750330 1691063 := bstep (se 1 (by rfl) ⟨1268297, by rfl⟩ : syracuseStep 1691063 = 2536595) B2536595
theorem B4279823 : Blo 750330 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B1691243 : Blo 750330 1691243 := bstep (se 1 (by rfl) ⟨1268432, by rfl⟩ : syracuseStep 1691243 = 2536865) B2536865
theorem B27512459 : Blo 750330 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B2543399 : Blo 750330 2543399 := bstep (se 1 (by rfl) ⟨1907549, by rfl⟩ : syracuseStep 2543399 = 3815099) B3815099
theorem B1691513 : Blo 750330 1691513 := bstep (se 2 (by rfl) ⟨634317, by rfl⟩ : syracuseStep 1691513 = 1268635) B1268635
theorem B2576569 : Blo 750330 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B2707721 : Blo 750330 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B2412911 : Blo 750330 2412911 := bstep (se 1 (by rfl) ⟨1809683, by rfl⟩ : syracuseStep 2412911 = 3619367) B3619367
theorem B12342041 : Blo 750330 12342041 := bstep (se 2 (by rfl) ⟨4628265, by rfl⟩ : syracuseStep 12342041 = 9256531) B9256531
theorem B2544425 : Blo 750330 2544425 := bstep (se 2 (by rfl) ⟨954159, by rfl⟩ : syracuseStep 2544425 = 1908319) B1908319
theorem B4281281 : Blo 750330 4281281 := bstep (se 2 (by rfl) ⟨1605480, by rfl⟩ : syracuseStep 4281281 = 3210961) B3210961
theorem B6443995 : Blo 750330 6443995 := bstep (se 1 (by rfl) ⟨4832996, by rfl⟩ : syracuseStep 6443995 = 9665993) B9665993
theorem B3429371 : Blo 750330 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B2413577 : Blo 750330 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B2544695 : Blo 750330 2544695 := bstep (se 1 (by rfl) ⟨1908521, by rfl⟩ : syracuseStep 2544695 = 3817043) B3817043
theorem B9786601 : Blo 750330 9786601 := bstep (se 2 (by rfl) ⟨3669975, by rfl⟩ : syracuseStep 9786601 = 7339951) B7339951
theorem B1430875 : Blo 750330 1430875 := bstep (se 1 (by rfl) ⟨1073156, by rfl⟩ : syracuseStep 1430875 = 2146313) B2146313
theorem B1070491 : Blo 750330 1070491 := bstep (se 1 (by rfl) ⟨802868, by rfl⟩ : syracuseStep 1070491 = 1605737) B1605737
theorem B8574497 : Blo 750330 8574497 := bstep (se 2 (by rfl) ⟨3215436, by rfl⟩ : syracuseStep 8574497 = 6430873) B6430873
theorem B1070759 : Blo 750330 1070759 := bstep (se 1 (by rfl) ⟨803069, by rfl⟩ : syracuseStep 1070759 = 1606139) B1606139
theorem B1693367 : Blo 750330 1693367 := bstep (se 1 (by rfl) ⟨1270025, by rfl⟩ : syracuseStep 1693367 = 2540051) B2540051
theorem B1267535 : Blo 750330 1267535 := bstep (se 1 (by rfl) ⟨950651, by rfl⟩ : syracuseStep 1267535 = 1901303) B1901303
theorem B14112643 : Blo 750330 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B2414551 : Blo 750330 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B1431695 : Blo 750330 1431695 := bstep (se 1 (by rfl) ⟨1073771, by rfl⟩ : syracuseStep 1431695 = 2147543) B2147543
theorem B23517539 : Blo 750330 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B1431931 : Blo 750330 1431931 := bstep (se 1 (by rfl) ⟨1073948, by rfl⟩ : syracuseStep 1431931 = 2147897) B2147897
theorem B26368409 : Blo 750330 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B1071721 : Blo 750330 1071721 := bstep (se 2 (by rfl) ⟨401895, by rfl⟩ : syracuseStep 1071721 = 803791) B803791
theorem B10836827 : Blo 750330 10836827 := bstep (se 1 (by rfl) ⟨8127620, by rfl⟩ : syracuseStep 10836827 = 16255241) B16255241
theorem B1694555 : Blo 750330 1694555 := bstep (se 1 (by rfl) ⟨1270916, by rfl⟩ : syracuseStep 1694555 = 2541833) B2541833
theorem B1268777 : Blo 750330 1268777 := bstep (se 2 (by rfl) ⟨475791, by rfl⟩ : syracuseStep 1268777 = 951583) B951583
theorem B1268959 : Blo 750330 1268959 := bstep (se 1 (by rfl) ⟨951719, by rfl⟩ : syracuseStep 1268959 = 1903439) B1903439
theorem B1695311 : Blo 750330 1695311 := bstep (se 1 (by rfl) ⟨1271483, by rfl⟩ : syracuseStep 1695311 = 2542967) B2542967
theorem B1269391 : Blo 750330 1269391 := bstep (se 1 (by rfl) ⟨952043, by rfl⟩ : syracuseStep 1269391 = 1904087) B1904087
theorem B1696031 : Blo 750330 1696031 := bstep (se 1 (by rfl) ⟨1272023, by rfl⟩ : syracuseStep 1696031 = 2544047) B2544047
theorem B844159 : Blo 750330 844159 := bstep (se 1 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 844159 = 1266239) B1266239
theorem B8577413 : Blo 750330 8577413 := bstep (se 4 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 8577413 = 1608265) B1608265
theorem B17621651 : Blo 750330 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B1696679 : Blo 750330 1696679 := bstep (se 1 (by rfl) ⟨1272509, by rfl⟩ : syracuseStep 1696679 = 2545019) B2545019
theorem B1270991 : Blo 750330 1270991 := bstep (se 1 (by rfl) ⟨953243, by rfl⟩ : syracuseStep 1270991 = 1906487) B1906487
theorem B2713171 : Blo 750330 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B2746075 : Blo 750330 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B845563 : Blo 750330 845563 := bstep (se 1 (by rfl) ⟨634172, by rfl⟩ : syracuseStep 845563 = 1268345) B1268345
theorem B845599 : Blo 750330 845599 := bstep (se 1 (by rfl) ⟨634199, by rfl⟩ : syracuseStep 845599 = 1268399) B1268399
theorem B1271801 : Blo 750330 1271801 := bstep (se 2 (by rfl) ⟨476925, by rfl⟩ : syracuseStep 1271801 = 953851) B953851
theorem B4581521 : Blo 750330 4581521 := bstep (se 2 (by rfl) ⟨1718070, by rfl⟩ : syracuseStep 4581521 = 3436141) B3436141
theorem B1271963 : Blo 750330 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B1272071 : Blo 750330 1272071 := bstep (se 1 (by rfl) ⟨954053, by rfl⟩ : syracuseStep 1272071 = 1908107) B1908107
theorem B3140407 : Blo 750330 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B1272631 : Blo 750330 1272631 := bstep (se 1 (by rfl) ⟨954473, by rfl⟩ : syracuseStep 1272631 = 1908947) B1908947
theorem B846751 : Blo 750330 846751 := bstep (se 1 (by rfl) ⟨635063, by rfl⟩ : syracuseStep 846751 = 1270127) B1270127
theorem B1207199 : Blo 750330 1207199 := bstep (se 1 (by rfl) ⟨905399, by rfl⟩ : syracuseStep 1207199 = 1810799) B1810799
theorem B846895 : Blo 750330 846895 := bstep (se 1 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 846895 = 1270343) B1270343
theorem B3206279 : Blo 750330 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B8580329 : Blo 750330 8580329 := bstep (se 2 (by rfl) ⟨3217623, by rfl⟩ : syracuseStep 8580329 = 6435247) B6435247
theorem B847183 : Blo 750330 847183 := bstep (se 1 (by rfl) ⟨635387, by rfl⟩ : syracuseStep 847183 = 1270775) B1270775
theorem B847687 : Blo 750330 847687 := bstep (se 1 (by rfl) ⟨635765, by rfl⟩ : syracuseStep 847687 = 1271531) B1271531
theorem B1143239 : Blo 750330 1143239 := bstep (se 1 (by rfl) ⟨857429, by rfl⟩ : syracuseStep 1143239 = 1714859) B1714859
theorem B848335 : Blo 750330 848335 := bstep (se 1 (by rfl) ⟨636251, by rfl⟩ : syracuseStep 848335 = 1272503) B1272503
theorem B1143391 : Blo 750330 1143391 := bstep (se 1 (by rfl) ⟨857543, by rfl⟩ : syracuseStep 1143391 = 1715087) B1715087
theorem B750447 : Blo 750330 750447 := bstep (se 1 (by rfl) ⟨562835, by rfl⟩ : syracuseStep 750447 = 1125671) B1125671
theorem B750503 : Blo 750330 750503 := bstep (se 1 (by rfl) ⟨562877, by rfl⟩ : syracuseStep 750503 = 1125755) B1125755
theorem B750587 : Blo 750330 750587 := bstep (se 1 (by rfl) ⟨562940, by rfl⟩ : syracuseStep 750587 = 1125881) B1125881
theorem B750655 : Blo 750330 750655 := bstep (se 1 (by rfl) ⟨562991, by rfl⟩ : syracuseStep 750655 = 1125983) B1125983
theorem B750799 : Blo 750330 750799 := bstep (se 1 (by rfl) ⟨563099, by rfl⟩ : syracuseStep 750799 = 1126199) B1126199
theorem B751003 : Blo 750330 751003 := bstep (se 1 (by rfl) ⟨563252, by rfl⟩ : syracuseStep 751003 = 1126505) B1126505
theorem B751215 : Blo 750330 751215 := bstep (se 1 (by rfl) ⟨563411, by rfl⟩ : syracuseStep 751215 = 1126823) B1126823
theorem B751271 : Blo 750330 751271 := bstep (se 1 (by rfl) ⟨563453, by rfl⟩ : syracuseStep 751271 = 1126907) B1126907
theorem B3798737 : Blo 750330 3798737 := bstep (se 2 (by rfl) ⟨1424526, by rfl⟩ : syracuseStep 3798737 = 2849053) B2849053
theorem B751355 : Blo 750330 751355 := bstep (se 1 (by rfl) ⟨563516, by rfl⟩ : syracuseStep 751355 = 1127033) B1127033
theorem B751391 : Blo 750330 751391 := bstep (se 1 (by rfl) ⟨563543, by rfl⟩ : syracuseStep 751391 = 1127087) B1127087
theorem B751423 : Blo 750330 751423 := bstep (se 1 (by rfl) ⟨563567, by rfl⟩ : syracuseStep 751423 = 1127135) B1127135
theorem B1603567 : Blo 750330 1603567 := bstep (se 1 (by rfl) ⟨1202675, by rfl⟩ : syracuseStep 1603567 = 2405351) B2405351
theorem B751599 : Blo 750330 751599 := bstep (se 1 (by rfl) ⟨563699, by rfl⟩ : syracuseStep 751599 = 1127399) B1127399
theorem B3209321 : Blo 750330 3209321 := bstep (se 2 (by rfl) ⟨1203495, by rfl⟩ : syracuseStep 3209321 = 2406991) B2406991
theorem B2029711 : Blo 750330 2029711 := bstep (se 1 (by rfl) ⟨1522283, by rfl⟩ : syracuseStep 2029711 = 3044567) B3044567
theorem B751771 : Blo 750330 751771 := bstep (se 1 (by rfl) ⟨563828, by rfl⟩ : syracuseStep 751771 = 1127657) B1127657
theorem B751807 : Blo 750330 751807 := bstep (se 1 (by rfl) ⟨563855, by rfl⟩ : syracuseStep 751807 = 1127711) B1127711
theorem B751919 : Blo 750330 751919 := bstep (se 1 (by rfl) ⟨563939, by rfl⟩ : syracuseStep 751919 = 1127879) B1127879
theorem B752155 : Blo 750330 752155 := bstep (se 1 (by rfl) ⟨564116, by rfl⟩ : syracuseStep 752155 = 1128233) B1128233
theorem B752159 : Blo 750330 752159 := bstep (se 1 (by rfl) ⟨564119, by rfl⟩ : syracuseStep 752159 = 1128239) B1128239
theorem B1604233 : Blo 750330 1604233 := bstep (se 2 (by rfl) ⟨601587, by rfl⟩ : syracuseStep 1604233 = 1203175) B1203175
theorem B752475 : Blo 750330 752475 := bstep (se 1 (by rfl) ⟨564356, by rfl⟩ : syracuseStep 752475 = 1128713) B1128713
theorem B752543 : Blo 750330 752543 := bstep (se 1 (by rfl) ⟨564407, by rfl⟩ : syracuseStep 752543 = 1128815) B1128815
theorem B752687 : Blo 750330 752687 := bstep (se 1 (by rfl) ⟨564515, by rfl⟩ : syracuseStep 752687 = 1129031) B1129031
theorem B752711 : Blo 750330 752711 := bstep (se 1 (by rfl) ⟨564533, by rfl⟩ : syracuseStep 752711 = 1129067) B1129067
theorem B10714295 : Blo 750330 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B752863 : Blo 750330 752863 := bstep (se 1 (by rfl) ⟨564647, by rfl⟩ : syracuseStep 752863 = 1129295) B1129295
theorem B1146079 : Blo 750330 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B949735 : Blo 750330 949735 := bstep (se 1 (by rfl) ⟨712301, by rfl⟩ : syracuseStep 949735 = 1424603) B1424603
theorem B1900007 : Blo 750330 1900007 := bstep (se 1 (by rfl) ⟨1425005, by rfl⟩ : syracuseStep 1900007 = 2850011) B2850011
theorem B753127 : Blo 750330 753127 := bstep (se 1 (by rfl) ⟨564845, by rfl⟩ : syracuseStep 753127 = 1129691) B1129691
theorem B753243 : Blo 750330 753243 := bstep (se 1 (by rfl) ⟨564932, by rfl⟩ : syracuseStep 753243 = 1129865) B1129865
theorem B4816493 : Blo 750330 4816493 := bstep (se 3 (by rfl) ⟨903092, by rfl⟩ : syracuseStep 4816493 = 1806185) B1806185
theorem B753479 : Blo 750330 753479 := bstep (se 1 (by rfl) ⟨565109, by rfl⟩ : syracuseStep 753479 = 1130219) B1130219
theorem B753631 : Blo 750330 753631 := bstep (se 1 (by rfl) ⟨565223, by rfl⟩ : syracuseStep 753631 = 1130447) B1130447
theorem B753855 : Blo 750330 753855 := bstep (se 1 (by rfl) ⟨565391, by rfl⟩ : syracuseStep 753855 = 1130783) B1130783
theorem B753871 : Blo 750330 753871 := bstep (se 1 (by rfl) ⟨565403, by rfl⟩ : syracuseStep 753871 = 1130807) B1130807
theorem B753919 : Blo 750330 753919 := bstep (se 1 (by rfl) ⟨565439, by rfl⟩ : syracuseStep 753919 = 1130879) B1130879
theorem B1900847 : Blo 750330 1900847 := bstep (se 1 (by rfl) ⟨1425635, by rfl⟩ : syracuseStep 1900847 = 2851271) B2851271
theorem B753967 : Blo 750330 753967 := bstep (se 1 (by rfl) ⟨565475, by rfl⟩ : syracuseStep 753967 = 1130951) B1130951
theorem B2097535 : Blo 750330 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B754203 : Blo 750330 754203 := bstep (se 1 (by rfl) ⟨565652, by rfl⟩ : syracuseStep 754203 = 1131305) B1131305
theorem B754207 : Blo 750330 754207 := bstep (se 1 (by rfl) ⟨565655, by rfl⟩ : syracuseStep 754207 = 1131311) B1131311
theorem B754287 : Blo 750330 754287 := bstep (se 1 (by rfl) ⟨565715, by rfl⟩ : syracuseStep 754287 = 1131431) B1131431
theorem B1606711 : Blo 750330 1606711 := bstep (se 1 (by rfl) ⟨1205033, by rfl⟩ : syracuseStep 1606711 = 2410067) B2410067
theorem B3802301 : Blo 750330 3802301 := bstep (se 3 (by rfl) ⟨712931, by rfl⟩ : syracuseStep 3802301 = 1425863) B1425863
theorem B3048637 : Blo 750330 3048637 := bstep (se 3 (by rfl) ⟨571619, by rfl⟩ : syracuseStep 3048637 = 1143239) B1143239
theorem B1606891 : Blo 750330 1606891 := bstep (se 1 (by rfl) ⟨1205168, by rfl⟩ : syracuseStep 1606891 = 2410337) B2410337
theorem B3212635 : Blo 750330 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B4294403 : Blo 750330 4294403 := bstep (se 1 (by rfl) ⟨3220802, by rfl⟩ : syracuseStep 4294403 = 6441605) B6441605
theorem B2853215 : Blo 750330 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B3213695 : Blo 750330 3213695 := bstep (se 1 (by rfl) ⟨2410271, by rfl⟩ : syracuseStep 3213695 = 4820543) B4820543
theorem B1805147 : Blo 750330 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B11733913 : Blo 750330 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B1608607 : Blo 750330 1608607 := bstep (se 1 (by rfl) ⟨1206455, by rfl⟩ : syracuseStep 1608607 = 2412911) B2412911
theorem B8228027 : Blo 750330 8228027 := bstep (se 1 (by rfl) ⟨6171020, by rfl⟩ : syracuseStep 8228027 = 12342041) B12342041
theorem B2854187 : Blo 750330 2854187 := bstep (se 1 (by rfl) ⟨2140640, by rfl⟩ : syracuseStep 2854187 = 4281281) B4281281
theorem B10817039 : Blo 750330 10817039 := bstep (se 1 (by rfl) ⟨8112779, by rfl⟩ : syracuseStep 10817039 = 16225559) B16225559
theorem B13700987 : Blo 750330 13700987 := bstep (se 1 (by rfl) ⟨10275740, by rfl⟩ : syracuseStep 13700987 = 20551481) B20551481
theorem B23531741 : Blo 750330 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B4067615 : Blo 750330 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B2855357 : Blo 750330 2855357 := bstep (se 3 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 2855357 = 1070759) B1070759
theorem B3609143 : Blo 750330 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B8590535 : Blo 750330 8590535 := bstep (se 1 (by rfl) ⟨6442901, by rfl⟩ : syracuseStep 8590535 = 12885803) B12885803
theorem B1906031 : Blo 750330 1906031 := bstep (se 1 (by rfl) ⟨1429523, by rfl⟩ : syracuseStep 1906031 = 2859047) B2859047
theorem B26056181 : Blo 750330 26056181 := bstep (se 5 (by rfl) ⟨1221383, by rfl⟩ : syracuseStep 26056181 = 2442767) B2442767
theorem B5707583 : Blo 750330 5707583 := bstep (se 1 (by rfl) ⟨4280687, by rfl⟩ : syracuseStep 5707583 = 8561375) B8561375
theorem B1906679 : Blo 750330 1906679 := bstep (se 1 (by rfl) ⟨1430009, by rfl⟩ : syracuseStep 1906679 = 2860019) B2860019
theorem B27400355 : Blo 750330 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B8591993 : Blo 750330 8591993 := bstep (se 2 (by rfl) ⟨3221997, by rfl⟩ : syracuseStep 8591993 = 6443995) B6443995
theorem B3054347 : Blo 750330 3054347 := bstep (se 1 (by rfl) ⟨2290760, by rfl⟩ : syracuseStep 3054347 = 4581521) B4581521
theorem B2858105 : Blo 750330 2858105 := bstep (se 2 (by rfl) ⟨1071789, by rfl⟩ : syracuseStep 2858105 = 2143579) B2143579
theorem B1907833 : Blo 750330 1907833 := bstep (se 2 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 1907833 = 1430875) B1430875
theorem B2137519 : Blo 750330 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B18816857 : Blo 750330 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B3219401 : Blo 750330 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B2138089 : Blo 750330 2138089 := bstep (se 2 (by rfl) ⟨801783, by rfl⟩ : syracuseStep 2138089 = 1603567) B1603567
theorem B19276217 : Blo 750330 19276217 := bstep (se 2 (by rfl) ⟨7228581, by rfl⟩ : syracuseStep 19276217 = 14457163) B14457163
theorem B1909241 : Blo 750330 1909241 := bstep (se 2 (by rfl) ⟨715965, by rfl⟩ : syracuseStep 1909241 = 1431931) B1431931
theorem B2138977 : Blo 750330 2138977 := bstep (se 2 (by rfl) ⟨802116, by rfl⟩ : syracuseStep 2138977 = 1604233) B1604233
theorem B3220343 : Blo 750330 3220343 := bstep (se 1 (by rfl) ⟨2415257, by rfl⟩ : syracuseStep 3220343 = 4830515) B4830515
theorem B4564073 : Blo 750330 4564073 := bstep (se 2 (by rfl) ⟨1711527, by rfl⟩ : syracuseStep 4564073 = 3423055) B3423055
theorem B6169709 : Blo 750330 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B2532491 : Blo 750330 2532491 := bstep (se 1 (by rfl) ⟨1899368, by rfl⟩ : syracuseStep 2532491 = 3798737) B3798737
theorem B927055 : Blo 750330 927055 := bstep (se 1 (by rfl) ⟨695291, by rfl⟩ : syracuseStep 927055 = 1390583) B1390583
theorem B2139547 : Blo 750330 2139547 := bstep (se 1 (by rfl) ⟨1604660, by rfl⟩ : syracuseStep 2139547 = 3209321) B3209321
theorem B7710329 : Blo 750330 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B3254461 : Blo 750330 3254461 := bstep (se 3 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 3254461 = 1220423) B1220423
theorem B10856713 : Blo 750330 10856713 := bstep (se 2 (by rfl) ⟨4071267, by rfl⟩ : syracuseStep 10856713 = 8142535) B8142535
theorem B3615043 : Blo 750330 3615043 := bstep (se 1 (by rfl) ⟨2711282, by rfl⟩ : syracuseStep 3615043 = 5422565) B5422565
theorem B6105739 : Blo 750330 6105739 := bstep (se 1 (by rfl) ⟨4579304, by rfl⟩ : syracuseStep 6105739 = 9158609) B9158609
theorem B2534111 : Blo 750330 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B2173703 : Blo 750330 2173703 := bstep (se 1 (by rfl) ⟨1630277, by rfl⟩ : syracuseStep 2173703 = 3260555) B3260555
theorem B2141255 : Blo 750330 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B1125545 : Blo 750330 1125545 := bstep (se 2 (by rfl) ⟨422079, by rfl⟩ : syracuseStep 1125545 = 844159) B844159
theorem B5713415 : Blo 750330 5713415 := bstep (se 1 (by rfl) ⟨4285061, by rfl⟩ : syracuseStep 5713415 = 8570123) B8570123
theorem B1125959 : Blo 750330 1125959 := bstep (se 1 (by rfl) ⟨844469, by rfl⟩ : syracuseStep 1125959 = 1688939) B1688939
theorem B1355447 : Blo 750330 1355447 := bstep (se 1 (by rfl) ⟨1016585, by rfl⟩ : syracuseStep 1355447 = 2033171) B2033171
theorem B1126139 : Blo 750330 1126139 := bstep (se 1 (by rfl) ⟨844604, by rfl⟩ : syracuseStep 1126139 = 1689209) B1689209
theorem B32550761 : Blo 750330 32550761 := bstep (se 2 (by rfl) ⟨12206535, by rfl⟩ : syracuseStep 32550761 = 24413071) B24413071
theorem B13053869 : Blo 750330 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B5713901 : Blo 750330 5713901 := bstep (se 3 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 5713901 = 2142713) B2142713
theorem B1126811 : Blo 750330 1126811 := bstep (se 1 (by rfl) ⟨845108, by rfl⟩ : syracuseStep 1126811 = 1690217) B1690217
theorem B3617561 : Blo 750330 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B1127231 : Blo 750330 1127231 := bstep (se 1 (by rfl) ⟨845423, by rfl⟩ : syracuseStep 1127231 = 1690847) B1690847
theorem B1127375 : Blo 750330 1127375 := bstep (se 1 (by rfl) ⟨845531, by rfl⟩ : syracuseStep 1127375 = 1691063) B1691063
theorem B1127417 : Blo 750330 1127417 := bstep (se 2 (by rfl) ⟨422781, by rfl⟩ : syracuseStep 1127417 = 845563) B845563
theorem B1127465 : Blo 750330 1127465 := bstep (se 2 (by rfl) ⟨422799, by rfl⟩ : syracuseStep 1127465 = 845599) B845599
theorem B1127495 : Blo 750330 1127495 := bstep (se 1 (by rfl) ⟨845621, by rfl⟩ : syracuseStep 1127495 = 1691243) B1691243
theorem B1127675 : Blo 750330 1127675 := bstep (se 1 (by rfl) ⟨845756, by rfl⟩ : syracuseStep 1127675 = 1691513) B1691513
theorem B6436205 : Blo 750330 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B3814937 : Blo 750330 3814937 := bstep (se 2 (by rfl) ⟨1430601, by rfl⟩ : syracuseStep 3814937 = 2861203) B2861203
theorem B5715845 : Blo 750330 5715845 := bstep (se 4 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 5715845 = 1071721) B1071721
theorem B2144171 : Blo 750330 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B2537513 : Blo 750330 2537513 := bstep (se 2 (by rfl) ⟨951567, by rfl⟩ : syracuseStep 2537513 = 1903135) B1903135
theorem B5716331 : Blo 750330 5716331 := bstep (se 1 (by rfl) ⟨4287248, by rfl⟩ : syracuseStep 5716331 = 8574497) B8574497
theorem B1128911 : Blo 750330 1128911 := bstep (se 1 (by rfl) ⟨846683, by rfl⟩ : syracuseStep 1128911 = 1693367) B1693367
theorem B1129001 : Blo 750330 1129001 := bstep (se 2 (by rfl) ⟨423375, by rfl⟩ : syracuseStep 1129001 = 846751) B846751
theorem B1129193 : Blo 750330 1129193 := bstep (se 2 (by rfl) ⟨423447, by rfl⟩ : syracuseStep 1129193 = 846895) B846895
theorem B15678359 : Blo 750330 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B17578939 : Blo 750330 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B1129577 : Blo 750330 1129577 := bstep (se 2 (by rfl) ⟨423591, by rfl⟩ : syracuseStep 1129577 = 847183) B847183
theorem B7224551 : Blo 750330 7224551 := bstep (se 1 (by rfl) ⟨5418413, by rfl⟩ : syracuseStep 7224551 = 10836827) B10836827
theorem B1129703 : Blo 750330 1129703 := bstep (se 1 (by rfl) ⟨847277, by rfl⟩ : syracuseStep 1129703 = 1694555) B1694555
theorem B13745501 : Blo 750330 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B1424891 : Blo 750330 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B1130207 : Blo 750330 1130207 := bstep (se 1 (by rfl) ⟨847655, by rfl⟩ : syracuseStep 1130207 = 1695311) B1695311
theorem B1425127 : Blo 750330 1425127 := bstep (se 1 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 1425127 = 2137691) B2137691
theorem B1130249 : Blo 750330 1130249 := bstep (se 2 (by rfl) ⟨423843, by rfl⟩ : syracuseStep 1130249 = 847687) B847687
theorem B2408297 : Blo 750330 2408297 := bstep (se 2 (by rfl) ⟨903111, by rfl⟩ : syracuseStep 2408297 = 1806223) B1806223
theorem B2146495 : Blo 750330 2146495 := bstep (se 1 (by rfl) ⟨1609871, by rfl⟩ : syracuseStep 2146495 = 3219743) B3219743
theorem B1130687 : Blo 750330 1130687 := bstep (se 1 (by rfl) ⟨848015, by rfl⟩ : syracuseStep 1130687 = 1696031) B1696031
theorem B5718275 : Blo 750330 5718275 := bstep (se 1 (by rfl) ⟨4288706, by rfl⟩ : syracuseStep 5718275 = 8577413) B8577413
theorem B3817853 : Blo 750330 3817853 := bstep (se 3 (by rfl) ⟨715847, by rfl⟩ : syracuseStep 3817853 = 1431695) B1431695
theorem B11747767 : Blo 750330 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B1426015 : Blo 750330 1426015 := bstep (se 1 (by rfl) ⟨1069511, by rfl⟩ : syracuseStep 1426015 = 2139023) B2139023
theorem B1131113 : Blo 750330 1131113 := bstep (se 2 (by rfl) ⟨424167, by rfl⟩ : syracuseStep 1131113 = 848335) B848335
theorem B1131119 : Blo 750330 1131119 := bstep (se 1 (by rfl) ⟨848339, by rfl⟩ : syracuseStep 1131119 = 1696679) B1696679
theorem B1524521 : Blo 750330 1524521 := bstep (se 2 (by rfl) ⟨571695, by rfl⟩ : syracuseStep 1524521 = 1143391) B1143391
theorem B5424205 : Blo 750330 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B1688687 : Blo 750330 1688687 := bstep (se 1 (by rfl) ⟨1266515, by rfl⟩ : syracuseStep 1688687 = 2533031) B2533031
theorem B6112421 : Blo 750330 6112421 := bstep (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) B1146079
theorem B2540969 : Blo 750330 2540969 := bstep (se 2 (by rfl) ⟨952863, by rfl⟩ : syracuseStep 2540969 = 1905727) B1905727
theorem B2147771 : Blo 750330 2147771 := bstep (se 1 (by rfl) ⟨1610828, by rfl⟩ : syracuseStep 2147771 = 3221657) B3221657
theorem B1689083 : Blo 750330 1689083 := bstep (se 1 (by rfl) ⟨1266812, by rfl⟩ : syracuseStep 1689083 = 2533625) B2533625
theorem B1689119 : Blo 750330 1689119 := bstep (se 1 (by rfl) ⟨1266839, by rfl⟩ : syracuseStep 1689119 = 2533679) B2533679
theorem B1689263 : Blo 750330 1689263 := bstep (se 1 (by rfl) ⟨1266947, by rfl⟩ : syracuseStep 1689263 = 2533895) B2533895
theorem B1427321 : Blo 750330 1427321 := bstep (se 2 (by rfl) ⟨535245, by rfl⟩ : syracuseStep 1427321 = 1070491) B1070491
theorem B804799 : Blo 750330 804799 := bstep (se 1 (by rfl) ⟨603599, by rfl⟩ : syracuseStep 804799 = 1207199) B1207199
theorem B1689695 : Blo 750330 1689695 := bstep (se 1 (by rfl) ⟨1267271, by rfl⟩ : syracuseStep 1689695 = 2534543) B2534543
theorem B5720219 : Blo 750330 5720219 := bstep (se 1 (by rfl) ⟨4290164, by rfl⟩ : syracuseStep 5720219 = 8580329) B8580329
theorem B1689983 : Blo 750330 1689983 := bstep (se 1 (by rfl) ⟨1267487, by rfl⟩ : syracuseStep 1689983 = 2534975) B2534975
theorem B1428263 : Blo 750330 1428263 := bstep (se 1 (by rfl) ⟨1071197, by rfl⟩ : syracuseStep 1428263 = 2142395) B2142395
theorem B1690451 : Blo 750330 1690451 := bstep (se 1 (by rfl) ⟨1267838, by rfl⟩ : syracuseStep 1690451 = 2535677) B2535677
theorem B2542427 : Blo 750330 2542427 := bstep (se 1 (by rfl) ⟨1906820, by rfl⟩ : syracuseStep 2542427 = 3813641) B3813641
theorem B2706281 : Blo 750330 2706281 := bstep (se 2 (by rfl) ⟨1014855, by rfl⟩ : syracuseStep 2706281 = 2029711) B2029711
theorem B1690811 : Blo 750330 1690811 := bstep (se 1 (by rfl) ⟨1268108, by rfl⟩ : syracuseStep 1690811 = 2536217) B2536217
theorem B1690991 : Blo 750330 1690991 := bstep (se 1 (by rfl) ⟨1268243, by rfl⟩ : syracuseStep 1690991 = 2536487) B2536487
theorem B1429319 : Blo 750330 1429319 := bstep (se 1 (by rfl) ⟨1071989, by rfl⟩ : syracuseStep 1429319 = 2143979) B2143979
theorem B1691711 : Blo 750330 1691711 := bstep (se 1 (by rfl) ⟨1268783, by rfl⟩ : syracuseStep 1691711 = 2537567) B2537567
theorem B1626331 : Blo 750330 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B1691945 : Blo 750330 1691945 := bstep (se 2 (by rfl) ⟨634479, by rfl⟩ : syracuseStep 1691945 = 1268959) B1268959
theorem B1692215 : Blo 750330 1692215 := bstep (se 1 (by rfl) ⟨1269161, by rfl⟩ : syracuseStep 1692215 = 2538323) B2538323
theorem B1266313 : Blo 750330 1266313 := bstep (se 2 (by rfl) ⟨474867, by rfl⟩ : syracuseStep 1266313 = 949735) B949735
theorem B1692521 : Blo 750330 1692521 := bstep (se 2 (by rfl) ⟨634695, by rfl⟩ : syracuseStep 1692521 = 1269391) B1269391
theorem B2413423 : Blo 750330 2413423 := bstep (se 1 (by rfl) ⟨1810067, by rfl⟩ : syracuseStep 2413423 = 3620135) B3620135
theorem B1692575 : Blo 750330 1692575 := bstep (se 1 (by rfl) ⟨1269431, by rfl⟩ : syracuseStep 1692575 = 2538863) B2538863
theorem B1266671 : Blo 750330 1266671 := bstep (se 1 (by rfl) ⟨950003, by rfl⟩ : syracuseStep 1266671 = 1900007) B1900007
theorem B1692827 : Blo 750330 1692827 := bstep (se 1 (by rfl) ⟨1269620, by rfl⟩ : syracuseStep 1692827 = 2539241) B2539241
theorem B9655847 : Blo 750330 9655847 := bstep (se 1 (by rfl) ⟨7241885, by rfl⟩ : syracuseStep 9655847 = 14483771) B14483771
theorem B2545289 : Blo 750330 2545289 := bstep (se 2 (by rfl) ⟨954483, by rfl⟩ : syracuseStep 2545289 = 1908967) B1908967
theorem B1693403 : Blo 750330 1693403 := bstep (se 1 (by rfl) ⟨1270052, by rfl⟩ : syracuseStep 1693403 = 2540105) B2540105
theorem B1693511 : Blo 750330 1693511 := bstep (se 1 (by rfl) ⟨1270133, by rfl⟩ : syracuseStep 1693511 = 2540267) B2540267
theorem B1202663 : Blo 750330 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B1694519 : Blo 750330 1694519 := bstep (se 1 (by rfl) ⟨1270889, by rfl⟩ : syracuseStep 1694519 = 2541779) B2541779
theorem B1694699 : Blo 750330 1694699 := bstep (se 1 (by rfl) ⟨1271024, by rfl⟩ : syracuseStep 1694699 = 2542049) B2542049
theorem B3661433 : Blo 750330 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B18341639 : Blo 750330 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B4874003 : Blo 750330 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B1695599 : Blo 750330 1695599 := bstep (se 1 (by rfl) ⟨1271699, by rfl⟩ : syracuseStep 1695599 = 2543399) B2543399
theorem B5791621 : Blo 750330 5791621 := bstep (se 4 (by rfl) ⟨542964, by rfl⟩ : syracuseStep 5791621 = 1085929) B1085929
theorem B14442401 : Blo 750330 14442401 := bstep (se 2 (by rfl) ⟨5415900, by rfl⟩ : syracuseStep 14442401 = 10831801) B10831801
theorem B1073407 : Blo 750330 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B4284697 : Blo 750330 4284697 := bstep (se 2 (by rfl) ⟨1606761, by rfl⟩ : syracuseStep 4284697 = 3213523) B3213523
theorem B1270073 : Blo 750330 1270073 := bstep (se 2 (by rfl) ⟨476277, by rfl⟩ : syracuseStep 1270073 = 952555) B952555
theorem B5726537 : Blo 750330 5726537 := bstep (se 2 (by rfl) ⟨2147451, by rfl⟩ : syracuseStep 5726537 = 4294903) B4294903
theorem B1696283 : Blo 750330 1696283 := bstep (se 1 (by rfl) ⟨1272212, by rfl⟩ : syracuseStep 1696283 = 2544425) B2544425
theorem B2286247 : Blo 750330 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B1696463 : Blo 750330 1696463 := bstep (se 1 (by rfl) ⟨1272347, by rfl⟩ : syracuseStep 1696463 = 2544695) B2544695
theorem B1270559 : Blo 750330 1270559 := bstep (se 1 (by rfl) ⟨952919, by rfl⟩ : syracuseStep 1270559 = 1905839) B1905839
theorem B7234505 : Blo 750330 7234505 := bstep (se 2 (by rfl) ⟨2712939, by rfl⟩ : syracuseStep 7234505 = 5425879) B5425879
theorem B4187209 : Blo 750330 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B1696841 : Blo 750330 1696841 := bstep (se 2 (by rfl) ⟨636315, by rfl⟩ : syracuseStep 1696841 = 1272631) B1272631
theorem B4285655 : Blo 750330 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B845023 : Blo 750330 845023 := bstep (se 1 (by rfl) ⟨633767, by rfl⟩ : syracuseStep 845023 = 1267535) B1267535
theorem B1271369 : Blo 750330 1271369 := bstep (se 2 (by rfl) ⟨476763, by rfl⟩ : syracuseStep 1271369 = 953527) B953527
theorem B4286155 : Blo 750330 4286155 := bstep (se 1 (by rfl) ⟨3214616, by rfl⟩ : syracuseStep 4286155 = 6429233) B6429233
theorem B845851 : Blo 750330 845851 := bstep (se 1 (by rfl) ⟨634388, by rfl⟩ : syracuseStep 845851 = 1268777) B1268777
theorem B1271855 : Blo 750330 1271855 := bstep (se 1 (by rfl) ⟨953891, by rfl⟩ : syracuseStep 1271855 = 1907783) B1907783
theorem B1271929 : Blo 750330 1271929 := bstep (se 2 (by rfl) ⟨476973, by rfl⟩ : syracuseStep 1271929 = 953947) B953947
theorem B3435425 : Blo 750330 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B847327 : Blo 750330 847327 := bstep (se 1 (by rfl) ⟨635495, by rfl⟩ : syracuseStep 847327 = 1270991) B1270991
theorem B5795309 : Blo 750330 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B10841951 : Blo 750330 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B52195205 : Blo 750330 52195205 := bstep (se 4 (by rfl) ⟨4893300, by rfl⟩ : syracuseStep 52195205 = 9786601) B9786601
theorem B847867 : Blo 750330 847867 := bstep (se 1 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 847867 = 1271801) B1271801
theorem B847975 : Blo 750330 847975 := bstep (se 1 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 847975 = 1271963) B1271963
theorem B848047 : Blo 750330 848047 := bstep (se 1 (by rfl) ⟨636035, by rfl⟩ : syracuseStep 848047 = 1272071) B1272071
theorem B750331 : Blo 750330 750331 := bstep (se 1 (by rfl) ⟨562748, by rfl⟩ : syracuseStep 750331 = 1125497) B1125497
theorem B750399 : Blo 750330 750399 := bstep (se 1 (by rfl) ⟨562799, by rfl⟩ : syracuseStep 750399 = 1125599) B1125599
theorem B750427 : Blo 750330 750427 := bstep (se 1 (by rfl) ⟨562820, by rfl⟩ : syracuseStep 750427 = 1125641) B1125641
theorem B750495 : Blo 750330 750495 := bstep (se 1 (by rfl) ⟨562871, by rfl⟩ : syracuseStep 750495 = 1125743) B1125743
theorem B750575 : Blo 750330 750575 := bstep (se 1 (by rfl) ⟨562931, by rfl⟩ : syracuseStep 750575 = 1125863) B1125863
theorem B750663 : Blo 750330 750663 := bstep (se 1 (by rfl) ⟨562997, by rfl⟩ : syracuseStep 750663 = 1125995) B1125995
theorem B750747 : Blo 750330 750747 := bstep (se 1 (by rfl) ⟨563060, by rfl⟩ : syracuseStep 750747 = 1126121) B1126121
theorem B750843 : Blo 750330 750843 := bstep (se 1 (by rfl) ⟨563132, by rfl⟩ : syracuseStep 750843 = 1126265) B1126265
theorem B750911 : Blo 750330 750911 := bstep (se 1 (by rfl) ⟨563183, by rfl⟩ : syracuseStep 750911 = 1126367) B1126367
theorem B2979287 : Blo 750330 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B751079 : Blo 750330 751079 := bstep (se 1 (by rfl) ⟨563309, by rfl⟩ : syracuseStep 751079 = 1126619) B1126619
theorem B751087 : Blo 750330 751087 := bstep (se 1 (by rfl) ⟨563315, by rfl⟩ : syracuseStep 751087 = 1126631) B1126631
theorem B751195 : Blo 750330 751195 := bstep (se 1 (by rfl) ⟨563396, by rfl⟩ : syracuseStep 751195 = 1126793) B1126793
theorem B751259 : Blo 750330 751259 := bstep (se 1 (by rfl) ⟨563444, by rfl⟩ : syracuseStep 751259 = 1126889) B1126889
theorem B751343 : Blo 750330 751343 := bstep (se 1 (by rfl) ⟨563507, by rfl⟩ : syracuseStep 751343 = 1127015) B1127015
theorem B751431 : Blo 750330 751431 := bstep (se 1 (by rfl) ⟨563573, by rfl⟩ : syracuseStep 751431 = 1127147) B1127147
theorem B751451 : Blo 750330 751451 := bstep (se 1 (by rfl) ⟨563588, by rfl⟩ : syracuseStep 751451 = 1127177) B1127177
theorem B751519 : Blo 750330 751519 := bstep (se 1 (by rfl) ⟨563639, by rfl⟩ : syracuseStep 751519 = 1127279) B1127279
theorem B751687 : Blo 750330 751687 := bstep (se 1 (by rfl) ⟨563765, by rfl⟩ : syracuseStep 751687 = 1127531) B1127531
theorem B3471569 : Blo 750330 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B751847 : Blo 750330 751847 := bstep (se 1 (by rfl) ⟨563885, by rfl⟩ : syracuseStep 751847 = 1127771) B1127771
theorem B752031 : Blo 750330 752031 := bstep (se 1 (by rfl) ⟨564023, by rfl⟩ : syracuseStep 752031 = 1128047) B1128047
theorem B752079 : Blo 750330 752079 := bstep (se 1 (by rfl) ⟨564059, by rfl⟩ : syracuseStep 752079 = 1128119) B1128119
theorem B752103 : Blo 750330 752103 := bstep (se 1 (by rfl) ⟨564077, by rfl⟩ : syracuseStep 752103 = 1128155) B1128155
theorem B752219 : Blo 750330 752219 := bstep (se 1 (by rfl) ⟨564164, by rfl⟩ : syracuseStep 752219 = 1128329) B1128329
theorem B2292353 : Blo 750330 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B752287 : Blo 750330 752287 := bstep (se 1 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 752287 = 1128431) B1128431
theorem B752455 : Blo 750330 752455 := bstep (se 1 (by rfl) ⟨564341, by rfl⟩ : syracuseStep 752455 = 1128683) B1128683
theorem B752495 : Blo 750330 752495 := bstep (se 1 (by rfl) ⟨564371, by rfl⟩ : syracuseStep 752495 = 1128743) B1128743
theorem B752551 : Blo 750330 752551 := bstep (se 1 (by rfl) ⟨564413, by rfl⟩ : syracuseStep 752551 = 1128827) B1128827
theorem B12352501 : Blo 750330 12352501 := bstep (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) B1158047
theorem B752731 : Blo 750330 752731 := bstep (se 1 (by rfl) ⟨564548, by rfl⟩ : syracuseStep 752731 = 1129097) B1129097
theorem B752847 : Blo 750330 752847 := bstep (se 1 (by rfl) ⟨564635, by rfl⟩ : syracuseStep 752847 = 1129271) B1129271
theorem B752871 : Blo 750330 752871 := bstep (se 1 (by rfl) ⟨564653, by rfl⟩ : syracuseStep 752871 = 1129307) B1129307
theorem B752967 : Blo 750330 752967 := bstep (se 1 (by rfl) ⟨564725, by rfl⟩ : syracuseStep 752967 = 1129451) B1129451
theorem B1605071 : Blo 750330 1605071 := bstep (se 1 (by rfl) ⟨1203803, by rfl⟩ : syracuseStep 1605071 = 2407607) B2407607
theorem B7142863 : Blo 750330 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B753103 : Blo 750330 753103 := bstep (se 1 (by rfl) ⟨564827, by rfl⟩ : syracuseStep 753103 = 1129655) B1129655
theorem B2850299 : Blo 750330 2850299 := bstep (se 1 (by rfl) ⟨2137724, by rfl⟩ : syracuseStep 2850299 = 4275449) B4275449
theorem B753263 : Blo 750330 753263 := bstep (se 1 (by rfl) ⟨564947, by rfl⟩ : syracuseStep 753263 = 1129895) B1129895
theorem B753319 : Blo 750330 753319 := bstep (se 1 (by rfl) ⟨564989, by rfl⟩ : syracuseStep 753319 = 1129979) B1129979
theorem B753383 : Blo 750330 753383 := bstep (se 1 (by rfl) ⟨565037, by rfl⟩ : syracuseStep 753383 = 1130075) B1130075
theorem B3210995 : Blo 750330 3210995 := bstep (se 1 (by rfl) ⟨2408246, by rfl⟩ : syracuseStep 3210995 = 4816493) B4816493
theorem B753439 : Blo 750330 753439 := bstep (se 1 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 753439 = 1130159) B1130159
theorem B753519 : Blo 750330 753519 := bstep (se 1 (by rfl) ⟨565139, by rfl⟩ : syracuseStep 753519 = 1130279) B1130279
theorem B753575 : Blo 750330 753575 := bstep (se 1 (by rfl) ⟨565181, by rfl⟩ : syracuseStep 753575 = 1130363) B1130363
theorem B753791 : Blo 750330 753791 := bstep (se 1 (by rfl) ⟨565343, by rfl⟩ : syracuseStep 753791 = 1130687) B1130687
theorem B754075 : Blo 750330 754075 := bstep (se 1 (by rfl) ⟨565556, by rfl⟩ : syracuseStep 754075 = 1131113) B1131113
theorem B754079 : Blo 750330 754079 := bstep (se 1 (by rfl) ⟨565559, by rfl⟩ : syracuseStep 754079 = 1131119) B1131119
theorem B15663689 : Blo 750330 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B10846973 : Blo 750330 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B1901353 : Blo 750330 1901353 := bstep (se 2 (by rfl) ⟨713007, by rfl⟩ : syracuseStep 1901353 = 1426015) B1426015
theorem B3048329 : Blo 750330 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B2851969 : Blo 750330 2851969 := bstep (se 2 (by rfl) ⟨1069488, by rfl⟩ : syracuseStep 2851969 = 2138977) B2138977
theorem B1902143 : Blo 750330 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B4064849 : Blo 750330 4064849 := bstep (se 2 (by rfl) ⟨1524318, by rfl⟩ : syracuseStep 4064849 = 3048637) B3048637
theorem B952175 : Blo 750330 952175 := bstep (se 1 (by rfl) ⟨714131, by rfl⟩ : syracuseStep 952175 = 1428263) B1428263
theorem B2852729 : Blo 750330 2852729 := bstep (se 2 (by rfl) ⟨1069773, by rfl⟩ : syracuseStep 2852729 = 2139547) B2139547
theorem B1804187 : Blo 750330 1804187 := bstep (se 1 (by rfl) ⟨1353140, by rfl⟩ : syracuseStep 1804187 = 2706281) B2706281
theorem B4065389 : Blo 750330 4065389 := bstep (se 3 (by rfl) ⟨762260, by rfl⟩ : syracuseStep 4065389 = 1524521) B1524521
theorem B1902791 : Blo 750330 1902791 := bstep (se 1 (by rfl) ⟨1427093, by rfl⟩ : syracuseStep 1902791 = 2854187) B2854187
theorem B7211359 : Blo 750330 7211359 := bstep (se 1 (by rfl) ⟨5408519, by rfl⟩ : syracuseStep 7211359 = 10817039) B10817039
theorem B952879 : Blo 750330 952879 := bstep (se 1 (by rfl) ⟨714659, by rfl⟩ : syracuseStep 952879 = 1429319) B1429319
theorem B1903571 : Blo 750330 1903571 := bstep (se 1 (by rfl) ⟨1427678, by rfl⟩ : syracuseStep 1903571 = 2855357) B2855357
theorem B4820057 : Blo 750330 4820057 := bstep (se 2 (by rfl) ⟨1807521, by rfl⟩ : syracuseStep 4820057 = 3615043) B3615043
theorem B17370787 : Blo 750330 17370787 := bstep (se 1 (by rfl) ⟨13028090, by rfl⟩ : syracuseStep 17370787 = 26056181) B26056181
theorem B3805055 : Blo 750330 3805055 := bstep (se 1 (by rfl) ⟨2853791, by rfl⟩ : syracuseStep 3805055 = 5707583) B5707583
theorem B2036231 : Blo 750330 2036231 := bstep (se 1 (by rfl) ⟨1527173, by rfl⟩ : syracuseStep 2036231 = 3054347) B3054347
theorem B1905403 : Blo 750330 1905403 := bstep (se 1 (by rfl) ⟨1429052, by rfl⟩ : syracuseStep 1905403 = 2858105) B2858105
theorem B3806189 : Blo 750330 3806189 := bstep (se 3 (by rfl) ⟨713660, by rfl⟩ : syracuseStep 3806189 = 1427321) B1427321
theorem B12227759 : Blo 750330 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B3249335 : Blo 750330 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B2168441 : Blo 750330 2168441 := bstep (se 2 (by rfl) ⟨813165, by rfl⟩ : syracuseStep 2168441 = 1626331) B1626331
theorem B12850811 : Blo 750330 12850811 := bstep (se 1 (by rfl) ⟨9638108, by rfl⟩ : syracuseStep 12850811 = 19276217) B19276217
theorem B4823003 : Blo 750330 4823003 := bstep (se 1 (by rfl) ⟨3617252, by rfl⟩ : syracuseStep 4823003 = 7234505) B7234505
theorem B2857103 : Blo 750330 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B3217897 : Blo 750330 3217897 := bstep (se 2 (by rfl) ⟨1206711, by rfl⟩ : syracuseStep 3217897 = 2413423) B2413423
theorem B3808943 : Blo 750330 3808943 := bstep (se 1 (by rfl) ⟨2856707, by rfl⟩ : syracuseStep 3808943 = 5713415) B5713415
theorem B21700507 : Blo 750330 21700507 := bstep (se 1 (by rfl) ⟨16275380, by rfl⟩ : syracuseStep 21700507 = 32550761) B32550761
theorem B3809267 : Blo 750330 3809267 := bstep (se 1 (by rfl) ⟨2856950, by rfl⟩ : syracuseStep 3809267 = 5713901) B5713901
theorem B5710013 : Blo 750330 5710013 := bstep (se 3 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 5710013 = 2141255) B2141255
theorem B23438585 : Blo 750330 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B3810563 : Blo 750330 3810563 := bstep (se 1 (by rfl) ⟨2857922, by rfl⟩ : syracuseStep 3810563 = 5715845) B5715845
theorem B3810887 : Blo 750330 3810887 := bstep (se 1 (by rfl) ⟨2858165, by rfl⟩ : syracuseStep 3810887 = 5716331) B5716331
theorem B2140663 : Blo 750330 2140663 := bstep (se 1 (by rfl) ⟨1605497, by rfl⟩ : syracuseStep 2140663 = 3210995) B3210995
theorem B3812183 : Blo 750330 3812183 := bstep (se 1 (by rfl) ⟨2859137, by rfl⟩ : syracuseStep 3812183 = 5718275) B5718275
theorem B2861993 : Blo 750330 2861993 := bstep (se 2 (by rfl) ⟨1073247, by rfl⟩ : syracuseStep 2861993 = 2146495) B2146495
theorem B5712929 : Blo 750330 5712929 := bstep (se 2 (by rfl) ⟨2142348, by rfl⟩ : syracuseStep 5712929 = 4284697) B4284697
theorem B2796713 : Blo 750330 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B1125791 : Blo 750330 1125791 := bstep (se 1 (by rfl) ⟨844343, by rfl⟩ : syracuseStep 1125791 = 1688687) B1688687
theorem B4074947 : Blo 750330 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B2534867 : Blo 750330 2534867 := bstep (se 1 (by rfl) ⟨1901150, by rfl⟩ : syracuseStep 2534867 = 3802301) B3802301
theorem B1126055 : Blo 750330 1126055 := bstep (se 1 (by rfl) ⟨844541, by rfl⟩ : syracuseStep 1126055 = 1689083) B1689083
theorem B1126079 : Blo 750330 1126079 := bstep (se 1 (by rfl) ⟨844559, by rfl⟩ : syracuseStep 1126079 = 1689119) B1689119
theorem B1126175 : Blo 750330 1126175 := bstep (se 1 (by rfl) ⟨844631, by rfl⟩ : syracuseStep 1126175 = 1689263) B1689263
theorem B2862935 : Blo 750330 2862935 := bstep (se 1 (by rfl) ⟨2147201, by rfl⟩ : syracuseStep 2862935 = 4294403) B4294403
theorem B1126463 : Blo 750330 1126463 := bstep (se 1 (by rfl) ⟨844847, by rfl⟩ : syracuseStep 1126463 = 1689695) B1689695
theorem B2142281 : Blo 750330 2142281 := bstep (se 2 (by rfl) ⟨803355, by rfl⟩ : syracuseStep 2142281 = 1606711) B1606711
theorem B5582945 : Blo 750330 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B3813479 : Blo 750330 3813479 := bstep (se 1 (by rfl) ⟨2860109, by rfl⟩ : syracuseStep 3813479 = 5720219) B5720219
theorem B1126655 : Blo 750330 1126655 := bstep (se 1 (by rfl) ⟨844991, by rfl⟩ : syracuseStep 1126655 = 1689983) B1689983
theorem B2142463 : Blo 750330 2142463 := bstep (se 1 (by rfl) ⟨1606847, by rfl⟩ : syracuseStep 2142463 = 3213695) B3213695
theorem B1126697 : Blo 750330 1126697 := bstep (se 2 (by rfl) ⟨422511, by rfl⟩ : syracuseStep 1126697 = 845023) B845023
theorem B2142521 : Blo 750330 2142521 := bstep (se 2 (by rfl) ⟨803445, by rfl⟩ : syracuseStep 2142521 = 1606891) B1606891
theorem B1126967 : Blo 750330 1126967 := bstep (se 1 (by rfl) ⟨845225, by rfl⟩ : syracuseStep 1126967 = 1690451) B1690451
theorem B1127207 : Blo 750330 1127207 := bstep (se 1 (by rfl) ⟨845405, by rfl⟩ : syracuseStep 1127207 = 1690811) B1690811
theorem B1127327 : Blo 750330 1127327 := bstep (se 1 (by rfl) ⟨845495, by rfl⟩ : syracuseStep 1127327 = 1690991) B1690991
theorem B5714873 : Blo 750330 5714873 := bstep (se 2 (by rfl) ⟨2143077, by rfl⟩ : syracuseStep 5714873 = 4286155) B4286155
theorem B1127801 : Blo 750330 1127801 := bstep (se 2 (by rfl) ⟨422925, by rfl⟩ : syracuseStep 1127801 = 845851) B845851
theorem B1127807 : Blo 750330 1127807 := bstep (se 1 (by rfl) ⟨845855, by rfl⟩ : syracuseStep 1127807 = 1691711) B1691711
theorem B1127963 : Blo 750330 1127963 := bstep (se 1 (by rfl) ⟨845972, by rfl⟩ : syracuseStep 1127963 = 1691945) B1691945
theorem B12170861 : Blo 750330 12170861 := bstep (se 3 (by rfl) ⟨2282036, by rfl⟩ : syracuseStep 12170861 = 4564073) B4564073
theorem B2406095 : Blo 750330 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B1128143 : Blo 750330 1128143 := bstep (se 1 (by rfl) ⟨846107, by rfl⟩ : syracuseStep 1128143 = 1692215) B1692215
theorem B1128347 : Blo 750330 1128347 := bstep (se 1 (by rfl) ⟨846260, by rfl⟩ : syracuseStep 1128347 = 1692521) B1692521
theorem B1128383 : Blo 750330 1128383 := bstep (se 1 (by rfl) ⟨846287, by rfl⟩ : syracuseStep 1128383 = 1692575) B1692575
theorem B1128551 : Blo 750330 1128551 := bstep (se 1 (by rfl) ⟨846413, by rfl⟩ : syracuseStep 1128551 = 1692827) B1692827
theorem B8140985 : Blo 750330 8140985 := bstep (se 2 (by rfl) ⟨3052869, by rfl⟩ : syracuseStep 8140985 = 6105739) B6105739
theorem B6437231 : Blo 750330 6437231 := bstep (se 1 (by rfl) ⟨4827923, by rfl⟩ : syracuseStep 6437231 = 9655847) B9655847
theorem B1128935 : Blo 750330 1128935 := bstep (se 1 (by rfl) ⟨846701, by rfl⟩ : syracuseStep 1128935 = 1693403) B1693403
theorem B2144809 : Blo 750330 2144809 := bstep (se 2 (by rfl) ⟨804303, by rfl⟩ : syracuseStep 2144809 = 1608607) B1608607
theorem B1129007 : Blo 750330 1129007 := bstep (se 1 (by rfl) ⟨846755, by rfl⟩ : syracuseStep 1129007 = 1693511) B1693511
theorem B18266903 : Blo 750330 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B20560877 : Blo 750330 20560877 := bstep (se 3 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 20560877 = 7710329) B7710329
theorem B801775 : Blo 750330 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B1129679 : Blo 750330 1129679 := bstep (se 1 (by rfl) ⟨847259, by rfl⟩ : syracuseStep 1129679 = 1694519) B1694519
theorem B1129769 : Blo 750330 1129769 := bstep (se 2 (by rfl) ⟨423663, by rfl⟩ : syracuseStep 1129769 = 847327) B847327
theorem B1129799 : Blo 750330 1129799 := bstep (se 1 (by rfl) ⟨847349, by rfl⟩ : syracuseStep 1129799 = 1694699) B1694699
theorem B2440955 : Blo 750330 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B5717789 : Blo 750330 5717789 := bstep (se 3 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 5717789 = 2144171) B2144171
theorem B1130399 : Blo 750330 1130399 := bstep (se 1 (by rfl) ⟨847799, by rfl⟩ : syracuseStep 1130399 = 1695599) B1695599
theorem B2146267 : Blo 750330 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B1130489 : Blo 750330 1130489 := bstep (se 2 (by rfl) ⟨423933, by rfl⟩ : syracuseStep 1130489 = 847867) B847867
theorem B1130633 : Blo 750330 1130633 := bstep (se 2 (by rfl) ⟨423987, by rfl⟩ : syracuseStep 1130633 = 847975) B847975
theorem B3817691 : Blo 750330 3817691 := bstep (se 1 (by rfl) ⟨2863268, by rfl⟩ : syracuseStep 3817691 = 5726537) B5726537
theorem B1130729 : Blo 750330 1130729 := bstep (se 2 (by rfl) ⟨424023, by rfl⟩ : syracuseStep 1130729 = 848047) B848047
theorem B1130855 : Blo 750330 1130855 := bstep (se 1 (by rfl) ⟨848141, by rfl⟩ : syracuseStep 1130855 = 1696283) B1696283
theorem B1130975 : Blo 750330 1130975 := bstep (se 1 (by rfl) ⟨848231, by rfl⟩ : syracuseStep 1130975 = 1696463) B1696463
theorem B2146895 : Blo 750330 2146895 := bstep (se 1 (by rfl) ⟨1610171, by rfl⟩ : syracuseStep 2146895 = 3220343) B3220343
theorem B1131227 : Blo 750330 1131227 := bstep (se 1 (by rfl) ⟨848420, by rfl⟩ : syracuseStep 1131227 = 1696841) B1696841
theorem B4113139 : Blo 750330 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B1688327 : Blo 750330 1688327 := bstep (se 1 (by rfl) ⟨1266245, by rfl⟩ : syracuseStep 1688327 = 2532491) B2532491
theorem B1688417 : Blo 750330 1688417 := bstep (se 2 (by rfl) ⟨633156, by rfl⟩ : syracuseStep 1688417 = 1266313) B1266313
theorem B1689407 : Blo 750330 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B903631 : Blo 750330 903631 := bstep (se 1 (by rfl) ⟨677723, by rfl⟩ : syracuseStep 903631 = 1355447) B1355447
theorem B7227967 : Blo 750330 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B8702579 : Blo 750330 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B21941405 : Blo 750330 21941405 := bstep (se 3 (by rfl) ⟨4114013, by rfl⟩ : syracuseStep 21941405 = 8228027) B8228027
theorem B2411707 : Blo 750330 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B1986191 : Blo 750330 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B2543291 : Blo 750330 2543291 := bstep (se 1 (by rfl) ⟨1907468, by rfl⟩ : syracuseStep 2543291 = 3814937) B3814937
theorem B16470001 : Blo 750330 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B1691675 : Blo 750330 1691675 := bstep (se 1 (by rfl) ⟨1268756, by rfl⟩ : syracuseStep 1691675 = 2537513) B2537513
theorem B2314379 : Blo 750330 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B2543777 : Blo 750330 2543777 := bstep (se 2 (by rfl) ⟨953916, by rfl⟩ : syracuseStep 2543777 = 1907833) B1907833
theorem B1528235 : Blo 750330 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B9523817 : Blo 750330 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B9163667 : Blo 750330 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B1070047 : Blo 750330 1070047 := bstep (se 1 (by rfl) ⟨802535, by rfl⟩ : syracuseStep 1070047 = 1605071) B1605071
theorem B7722161 : Blo 750330 7722161 := bstep (se 2 (by rfl) ⟨2895810, by rfl⟩ : syracuseStep 7722161 = 5791621) B5791621
theorem B1267231 : Blo 750330 1267231 := bstep (se 1 (by rfl) ⟨950423, by rfl⟩ : syracuseStep 1267231 = 1900847) B1900847
theorem B2545235 : Blo 750330 2545235 := bstep (se 1 (by rfl) ⟨1908926, by rfl⟩ : syracuseStep 2545235 = 3817853) B3817853
theorem B1431209 : Blo 750330 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B1693979 : Blo 750330 1693979 := bstep (se 1 (by rfl) ⟨1270484, by rfl⟩ : syracuseStep 1693979 = 2540969) B2540969
theorem B1431847 : Blo 750330 1431847 := bstep (se 1 (by rfl) ⟨1073885, by rfl⟩ : syracuseStep 1431847 = 2147771) B2147771
theorem B17357125 : Blo 750330 17357125 := bstep (se 4 (by rfl) ⟨1627230, by rfl⟩ : syracuseStep 17357125 = 3254461) B3254461
theorem B7232273 : Blo 750330 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B1236073 : Blo 750330 1236073 := bstep (se 2 (by rfl) ⟨463527, by rfl⟩ : syracuseStep 1236073 = 927055) B927055
theorem B4283513 : Blo 750330 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B1203431 : Blo 750330 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B1694951 : Blo 750330 1694951 := bstep (se 1 (by rfl) ⟨1271213, by rfl⟩ : syracuseStep 1694951 = 2542427) B2542427
theorem B9133991 : Blo 750330 9133991 := bstep (se 1 (by rfl) ⟨6850493, by rfl⟩ : syracuseStep 9133991 = 13700987) B13700987
theorem B15687827 : Blo 750330 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B1695905 : Blo 750330 1695905 := bstep (se 2 (by rfl) ⟨635964, by rfl⟩ : syracuseStep 1695905 = 1271929) B1271929
theorem B14475617 : Blo 750330 14475617 := bstep (se 2 (by rfl) ⟨5428356, by rfl⟩ : syracuseStep 14475617 = 10856713) B10856713
theorem B844447 : Blo 750330 844447 := bstep (se 1 (by rfl) ⟨633335, by rfl⟩ : syracuseStep 844447 = 1266671) B1266671
theorem B5727023 : Blo 750330 5727023 := bstep (se 1 (by rfl) ⟨4295267, by rfl⟩ : syracuseStep 5727023 = 8590535) B8590535
theorem B1270687 : Blo 750330 1270687 := bstep (se 1 (by rfl) ⟨953015, by rfl⟩ : syracuseStep 1270687 = 1906031) B1906031
theorem B1696859 : Blo 750330 1696859 := bstep (se 1 (by rfl) ⟨1272644, by rfl⟩ : syracuseStep 1696859 = 2545289) B2545289
theorem B1271119 : Blo 750330 1271119 := bstep (se 1 (by rfl) ⟨953339, by rfl⟩ : syracuseStep 1271119 = 1906679) B1906679
theorem B5727995 : Blo 750330 5727995 := bstep (se 1 (by rfl) ⟨4295996, by rfl⟩ : syracuseStep 5727995 = 8591993) B8591993
theorem B62580869 : Blo 750330 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B12544571 : Blo 750330 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B9628267 : Blo 750330 9628267 := bstep (se 1 (by rfl) ⟨7221200, by rfl⟩ : syracuseStep 9628267 = 14442401) B14442401
theorem B846715 : Blo 750330 846715 := bstep (se 1 (by rfl) ⟨635036, by rfl⟩ : syracuseStep 846715 = 1270073) B1270073
theorem B1272827 : Blo 750330 1272827 := bstep (se 1 (by rfl) ⟨954620, by rfl⟩ : syracuseStep 1272827 = 1909241) B1909241
theorem B847039 : Blo 750330 847039 := bstep (se 1 (by rfl) ⟨635279, by rfl⟩ : syracuseStep 847039 = 1270559) B1270559
theorem B847579 : Blo 750330 847579 := bstep (se 1 (by rfl) ⟨635684, by rfl⟩ : syracuseStep 847579 = 1271369) B1271369
theorem B847903 : Blo 750330 847903 := bstep (se 1 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 847903 = 1271855) B1271855
theorem B2290283 : Blo 750330 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B5796541 : Blo 750330 5796541 := bstep (se 3 (by rfl) ⟨1086851, by rfl⟩ : syracuseStep 5796541 = 2173703) B2173703
theorem B750363 : Blo 750330 750363 := bstep (se 1 (by rfl) ⟨562772, by rfl⟩ : syracuseStep 750363 = 1125545) B1125545
theorem B3863539 : Blo 750330 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B750639 : Blo 750330 750639 := bstep (se 1 (by rfl) ⟨562979, by rfl⟩ : syracuseStep 750639 = 1125959) B1125959
theorem B750759 : Blo 750330 750759 := bstep (se 1 (by rfl) ⟨563069, by rfl⟩ : syracuseStep 750759 = 1126139) B1126139
theorem B34796803 : Blo 750330 34796803 := bstep (se 1 (by rfl) ⟨26097602, by rfl⟩ : syracuseStep 34796803 = 52195205) B52195205
theorem B751207 : Blo 750330 751207 := bstep (se 1 (by rfl) ⟨563405, by rfl⟩ : syracuseStep 751207 = 1126811) B1126811
theorem B751487 : Blo 750330 751487 := bstep (se 1 (by rfl) ⟨563615, by rfl⟩ : syracuseStep 751487 = 1127231) B1127231
theorem B751583 : Blo 750330 751583 := bstep (se 1 (by rfl) ⟨563687, by rfl⟩ : syracuseStep 751583 = 1127375) B1127375
theorem B751611 : Blo 750330 751611 := bstep (se 1 (by rfl) ⟨563708, by rfl⟩ : syracuseStep 751611 = 1127417) B1127417
theorem B751643 : Blo 750330 751643 := bstep (se 1 (by rfl) ⟨563732, by rfl⟩ : syracuseStep 751643 = 1127465) B1127465
theorem B751663 : Blo 750330 751663 := bstep (se 1 (by rfl) ⟨563747, by rfl⟩ : syracuseStep 751663 = 1127495) B1127495
theorem B751783 : Blo 750330 751783 := bstep (se 1 (by rfl) ⟨563837, by rfl⟩ : syracuseStep 751783 = 1127675) B1127675
theorem B4290803 : Blo 750330 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B3799709 : Blo 750330 3799709 := bstep (se 3 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 3799709 = 1424891) B1424891
theorem B752607 : Blo 750330 752607 := bstep (se 1 (by rfl) ⟨564455, by rfl⟩ : syracuseStep 752607 = 1128911) B1128911
theorem B752667 : Blo 750330 752667 := bstep (se 1 (by rfl) ⟨564500, by rfl⟩ : syracuseStep 752667 = 1129001) B1129001
theorem B752795 : Blo 750330 752795 := bstep (se 1 (by rfl) ⟨564596, by rfl⟩ : syracuseStep 752795 = 1129193) B1129193
theorem B2850025 : Blo 750330 2850025 := bstep (se 2 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 2850025 = 2137519) B2137519
theorem B10452239 : Blo 750330 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B753051 : Blo 750330 753051 := bstep (se 1 (by rfl) ⟨564788, by rfl⟩ : syracuseStep 753051 = 1129577) B1129577
theorem B4816367 : Blo 750330 4816367 := bstep (se 1 (by rfl) ⟨3612275, by rfl⟩ : syracuseStep 4816367 = 7224551) B7224551
theorem B753135 : Blo 750330 753135 := bstep (se 1 (by rfl) ⟨564851, by rfl⟩ : syracuseStep 753135 = 1129703) B1129703
theorem B6422125 : Blo 750330 6422125 := bstep (se 3 (by rfl) ⟨1204148, by rfl⟩ : syracuseStep 6422125 = 2408297) B2408297
theorem B1900169 : Blo 750330 1900169 := bstep (se 2 (by rfl) ⟨712563, by rfl⟩ : syracuseStep 1900169 = 1425127) B1425127
theorem B4292261 : Blo 750330 4292261 := bstep (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) B804799
theorem B1900199 : Blo 750330 1900199 := bstep (se 1 (by rfl) ⟨1425149, by rfl⟩ : syracuseStep 1900199 = 2850299) B2850299
theorem B753471 : Blo 750330 753471 := bstep (se 1 (by rfl) ⟨565103, by rfl⟩ : syracuseStep 753471 = 1130207) B1130207
theorem B753499 : Blo 750330 753499 := bstep (se 1 (by rfl) ⟨565124, by rfl⟩ : syracuseStep 753499 = 1130249) B1130249
theorem B2850785 : Blo 750330 2850785 := bstep (se 2 (by rfl) ⟨1069044, by rfl⟩ : syracuseStep 2850785 = 2138089) B2138089
theorem B753755 : Blo 750330 753755 := bstep (se 1 (by rfl) ⟨565316, by rfl⟩ : syracuseStep 753755 = 1130633) B1130633
theorem B753819 : Blo 750330 753819 := bstep (se 1 (by rfl) ⟨565364, by rfl⟩ : syracuseStep 753819 = 1130729) B1130729
theorem B753903 : Blo 750330 753903 := bstep (se 1 (by rfl) ⟨565427, by rfl⟩ : syracuseStep 753903 = 1130855) B1130855
theorem B753983 : Blo 750330 753983 := bstep (se 1 (by rfl) ⟨565487, by rfl⟩ : syracuseStep 753983 = 1130975) B1130975
theorem B754151 : Blo 750330 754151 := bstep (se 1 (by rfl) ⟨565613, by rfl⟩ : syracuseStep 754151 = 1131227) B1131227
theorem B2032219 : Blo 750330 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B1901819 : Blo 750330 1901819 := bstep (se 1 (by rfl) ⟨1426364, by rfl⟩ : syracuseStep 1901819 = 2852729) B2852729
theorem B3802625 : Blo 750330 3802625 := bstep (se 2 (by rfl) ⟨1425984, by rfl⟩ : syracuseStep 3802625 = 2851969) B2851969
theorem B5801719 : Blo 750330 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B3213371 : Blo 750330 3213371 := bstep (se 1 (by rfl) ⟨2410028, by rfl⟩ : syracuseStep 3213371 = 4820057) B4820057
theorem B1018823 : Blo 750330 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B2854217 : Blo 750330 2854217 := bstep (se 2 (by rfl) ⟨1070331, by rfl⟩ : syracuseStep 2854217 = 2140663) B2140663
theorem B9637289 : Blo 750330 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B5148107 : Blo 750330 5148107 := bstep (se 1 (by rfl) ⟨3861080, by rfl⟩ : syracuseStep 5148107 = 7722161) B7722161
theorem B1445627 : Blo 750330 1445627 := bstep (se 1 (by rfl) ⟨1084220, by rfl⟩ : syracuseStep 1445627 = 2168441) B2168441
theorem B3215335 : Blo 750330 3215335 := bstep (se 1 (by rfl) ⟨2411501, by rfl⟩ : syracuseStep 3215335 = 4823003) B4823003
theorem B1904735 : Blo 750330 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B3215609 : Blo 750330 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B4821515 : Blo 750330 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B2855675 : Blo 750330 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B21960001 : Blo 750330 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B10458551 : Blo 750330 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B3806675 : Blo 750330 3806675 := bstep (se 1 (by rfl) ⟨2855006, by rfl⟩ : syracuseStep 3806675 = 5710013) B5710013
theorem B2856617 : Blo 750330 2856617 := bstep (se 2 (by rfl) ⟨1071231, by rfl⟩ : syracuseStep 2856617 = 2142463) B2142463
theorem B5151385 : Blo 750330 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B41720579 : Blo 750330 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B8363047 : Blo 750330 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B1907995 : Blo 750330 1907995 := bstep (se 1 (by rfl) ⟨1430996, by rfl⟩ : syracuseStep 1907995 = 2861993) B2861993
theorem B3808619 : Blo 750330 3808619 := bstep (se 1 (by rfl) ⟨2856464, by rfl⟩ : syracuseStep 3808619 = 5712929) B5712929
theorem B1908623 : Blo 750330 1908623 := bstep (se 1 (by rfl) ⟨1431467, by rfl⟩ : syracuseStep 1908623 = 2862935) B2862935
theorem B1909129 : Blo 750330 1909129 := bstep (se 2 (by rfl) ⟨715923, by rfl⟩ : syracuseStep 1909129 = 1431847) B1431847
theorem B23142833 : Blo 750330 23142833 := bstep (se 2 (by rfl) ⟨8678562, by rfl⟩ : syracuseStep 23142833 = 17357125) B17357125
theorem B3809915 : Blo 750330 3809915 := bstep (se 1 (by rfl) ⟨2857436, by rfl⟩ : syracuseStep 3809915 = 5714873) B5714873
theorem B2859745 : Blo 750330 2859745 := bstep (se 2 (by rfl) ⟨1072404, by rfl⟩ : syracuseStep 2859745 = 2144809) B2144809
theorem B1648097 : Blo 750330 1648097 := bstep (se 2 (by rfl) ⟨618036, by rfl⟩ : syracuseStep 1648097 = 1236073) B1236073
theorem B2860535 : Blo 750330 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B2533139 : Blo 750330 2533139 := bstep (se 1 (by rfl) ⟨1899854, by rfl⟩ : syracuseStep 2533139 = 3799709) B3799709
theorem B13707251 : Blo 750330 13707251 := bstep (se 1 (by rfl) ⟨10280438, by rfl⟩ : syracuseStep 13707251 = 20560877) B20560877
theorem B8562833 : Blo 750330 8562833 := bstep (se 2 (by rfl) ⟨3211062, by rfl⟩ : syracuseStep 8562833 = 6422125) B6422125
theorem B2861507 : Blo 750330 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B3811859 : Blo 750330 3811859 := bstep (se 1 (by rfl) ⟨2858894, by rfl⟩ : syracuseStep 3811859 = 5717789) B5717789
theorem B2861689 : Blo 750330 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B6171677 : Blo 750330 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B1125551 : Blo 750330 1125551 := bstep (se 1 (by rfl) ⟨844163, by rfl⟩ : syracuseStep 1125551 = 1688327) B1688327
theorem B1125611 : Blo 750330 1125611 := bstep (se 1 (by rfl) ⟨844208, by rfl⟩ : syracuseStep 1125611 = 1688417) B1688417
theorem B1125929 : Blo 750330 1125929 := bstep (se 2 (by rfl) ⟨422223, by rfl⟩ : syracuseStep 1125929 = 844447) B844447
theorem B5484185 : Blo 750330 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B2535137 : Blo 750330 2535137 := bstep (se 2 (by rfl) ⟨950676, by rfl⟩ : syracuseStep 2535137 = 1901353) B1901353
theorem B1126271 : Blo 750330 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B14627603 : Blo 750330 14627603 := bstep (se 1 (by rfl) ⟨10970702, by rfl⟩ : syracuseStep 14627603 = 21941405) B21941405
theorem B1324127 : Blo 750330 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B2536703 : Blo 750330 2536703 := bstep (se 1 (by rfl) ⟨1902527, by rfl⟩ : syracuseStep 2536703 = 3805055) B3805055
theorem B1127783 : Blo 750330 1127783 := bstep (se 1 (by rfl) ⟨845837, by rfl⟩ : syracuseStep 1127783 = 1691675) B1691675
theorem B1357487 : Blo 750330 1357487 := bstep (se 1 (by rfl) ⟨1018115, by rfl⟩ : syracuseStep 1357487 = 2036231) B2036231
theorem B9615145 : Blo 750330 9615145 := bstep (se 2 (by rfl) ⟨3605679, by rfl⟩ : syracuseStep 9615145 = 7211359) B7211359
theorem B8664893 : Blo 750330 8664893 := bstep (se 3 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 8664893 = 3249335) B3249335
theorem B6109111 : Blo 750330 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B2537459 : Blo 750330 2537459 := bstep (se 1 (by rfl) ⟨1903094, by rfl⟩ : syracuseStep 2537459 = 3806189) B3806189
theorem B30914885 : Blo 750330 30914885 := bstep (se 4 (by rfl) ⟨2898270, by rfl⟩ : syracuseStep 30914885 = 5796541) B5796541
theorem B8567207 : Blo 750330 8567207 := bstep (se 1 (by rfl) ⟨6425405, by rfl⟩ : syracuseStep 8567207 = 12850811) B12850811
theorem B1128953 : Blo 750330 1128953 := bstep (se 2 (by rfl) ⟨423357, by rfl⟩ : syracuseStep 1128953 = 846715) B846715
theorem B1129319 : Blo 750330 1129319 := bstep (se 1 (by rfl) ⟨846989, by rfl⟩ : syracuseStep 1129319 = 1693979) B1693979
theorem B1129385 : Blo 750330 1129385 := bstep (se 2 (by rfl) ⟨423519, by rfl⟩ : syracuseStep 1129385 = 847039) B847039
theorem B3816557 : Blo 750330 3816557 := bstep (se 3 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 3816557 = 1431209) B1431209
theorem B1129967 : Blo 750330 1129967 := bstep (se 1 (by rfl) ⟨847475, by rfl⟩ : syracuseStep 1129967 = 1694951) B1694951
theorem B1130105 : Blo 750330 1130105 := bstep (se 2 (by rfl) ⟨423789, by rfl⟩ : syracuseStep 1130105 = 847579) B847579
theorem B2539133 : Blo 750330 2539133 := bstep (se 3 (by rfl) ⟨476087, by rfl⟩ : syracuseStep 2539133 = 952175) B952175
theorem B2539295 : Blo 750330 2539295 := bstep (se 1 (by rfl) ⟨1904471, by rfl⟩ : syracuseStep 2539295 = 3808943) B3808943
theorem B2539511 : Blo 750330 2539511 := bstep (se 1 (by rfl) ⟨1904633, by rfl⟩ : syracuseStep 2539511 = 3809267) B3809267
theorem B1130537 : Blo 750330 1130537 := bstep (se 2 (by rfl) ⟨423951, by rfl⟩ : syracuseStep 1130537 = 847903) B847903
theorem B1130603 : Blo 750330 1130603 := bstep (se 1 (by rfl) ⟨847952, by rfl⟩ : syracuseStep 1130603 = 1695905) B1695905
theorem B9650411 : Blo 750330 9650411 := bstep (se 1 (by rfl) ⟨7237808, by rfl⟩ : syracuseStep 9650411 = 14475617) B14475617
theorem B3818015 : Blo 750330 3818015 := bstep (se 1 (by rfl) ⟨2863511, by rfl⟩ : syracuseStep 3818015 = 5727023) B5727023
theorem B1131239 : Blo 750330 1131239 := bstep (se 1 (by rfl) ⟨848429, by rfl⟩ : syracuseStep 1131239 = 1696859) B1696859
theorem B2540375 : Blo 750330 2540375 := bstep (se 1 (by rfl) ⟨1905281, by rfl⟩ : syracuseStep 2540375 = 3810563) B3810563
theorem B2540537 : Blo 750330 2540537 := bstep (se 2 (by rfl) ⟨952701, by rfl⟩ : syracuseStep 2540537 = 1905403) B1905403
theorem B2540591 : Blo 750330 2540591 := bstep (se 1 (by rfl) ⟨1905443, by rfl⟩ : syracuseStep 2540591 = 3810887) B3810887
theorem B3818663 : Blo 750330 3818663 := bstep (se 1 (by rfl) ⟨2863997, by rfl⟩ : syracuseStep 3818663 = 5727995) B5727995
theorem B1426729 : Blo 750330 1426729 := bstep (se 2 (by rfl) ⟨535023, by rfl⟩ : syracuseStep 1426729 = 1070047) B1070047
theorem B2541455 : Blo 750330 2541455 := bstep (se 1 (by rfl) ⟨1906091, by rfl⟩ : syracuseStep 2541455 = 3812183) B3812183
theorem B1689641 : Blo 750330 1689641 := bstep (se 2 (by rfl) ⟨633615, by rfl⟩ : syracuseStep 1689641 = 1267231) B1267231
theorem B1689911 : Blo 750330 1689911 := bstep (se 1 (by rfl) ⟨1267433, by rfl⟩ : syracuseStep 1689911 = 2534867) B2534867
theorem B1428187 : Blo 750330 1428187 := bstep (se 1 (by rfl) ⟨1071140, by rfl⟩ : syracuseStep 1428187 = 2142281) B2142281
theorem B3721963 : Blo 750330 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B2542319 : Blo 750330 2542319 := bstep (se 1 (by rfl) ⟨1906739, by rfl⟩ : syracuseStep 2542319 = 3813479) B3813479
theorem B1428347 : Blo 750330 1428347 := bstep (se 1 (by rfl) ⟨1071260, by rfl⟩ : syracuseStep 1428347 = 2142521) B2142521
theorem B1526855 : Blo 750330 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B8113907 : Blo 750330 8113907 := bstep (se 1 (by rfl) ⟨6085430, by rfl⟩ : syracuseStep 8113907 = 12170861) B12170861
theorem B1069033 : Blo 750330 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B5427323 : Blo 750330 5427323 := bstep (se 1 (by rfl) ⟨4070492, by rfl⟩ : syracuseStep 5427323 = 8140985) B8140985
theorem B12177935 : Blo 750330 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B6968159 : Blo 750330 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B1266779 : Blo 750330 1266779 := bstep (se 1 (by rfl) ⟨950084, by rfl⟩ : syracuseStep 1266779 = 1900169) B1900169
theorem B1266799 : Blo 750330 1266799 := bstep (se 1 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 1266799 = 1900199) B1900199
theorem B1627303 : Blo 750330 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B2545127 : Blo 750330 2545127 := bstep (se 1 (by rfl) ⟨1908845, by rfl⟩ : syracuseStep 2545127 = 3817691) B3817691
theorem B10442459 : Blo 750330 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B1431263 : Blo 750330 1431263 := bstep (se 1 (by rfl) ⟨1073447, by rfl⟩ : syracuseStep 1431263 = 2146895) B2146895
theorem B7231315 : Blo 750330 7231315 := bstep (se 1 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 7231315 = 10846973) B10846973
theorem B1268095 : Blo 750330 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B2709899 : Blo 750330 2709899 := bstep (se 1 (by rfl) ⟨2032424, by rfl⟩ : syracuseStep 2709899 = 4064849) B4064849
theorem B1694249 : Blo 750330 1694249 := bstep (se 2 (by rfl) ⟨635343, by rfl⟩ : syracuseStep 1694249 = 1270687) B1270687
theorem B1202791 : Blo 750330 1202791 := bstep (se 1 (by rfl) ⟨902093, by rfl⟩ : syracuseStep 1202791 = 1804187) B1804187
theorem B2710259 : Blo 750330 2710259 := bstep (se 1 (by rfl) ⟨2032694, by rfl⟩ : syracuseStep 2710259 = 4065389) B4065389
theorem B1268527 : Blo 750330 1268527 := bstep (se 1 (by rfl) ⟨951395, by rfl⟩ : syracuseStep 1268527 = 1902791) B1902791
theorem B1694825 : Blo 750330 1694825 := bstep (se 2 (by rfl) ⟨635559, by rfl⟩ : syracuseStep 1694825 = 1271119) B1271119
theorem B1269047 : Blo 750330 1269047 := bstep (se 1 (by rfl) ⟨951785, by rfl⟩ : syracuseStep 1269047 = 1903571) B1903571
theorem B1695527 : Blo 750330 1695527 := bstep (se 1 (by rfl) ⟨1271645, by rfl⟩ : syracuseStep 1695527 = 2543291) B2543291
theorem B1695851 : Blo 750330 1695851 := bstep (se 1 (by rfl) ⟨1271888, by rfl⟩ : syracuseStep 1695851 = 2543777) B2543777
theorem B6349211 : Blo 750330 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B1204841 : Blo 750330 1204841 := bstep (se 2 (by rfl) ⟨451815, by rfl⟩ : syracuseStep 1204841 = 903631) B903631
theorem B1270505 : Blo 750330 1270505 := bstep (se 2 (by rfl) ⟨476439, by rfl⟩ : syracuseStep 1270505 = 952879) B952879
theorem B8151839 : Blo 750330 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B12837689 : Blo 750330 12837689 := bstep (se 2 (by rfl) ⟨4814133, by rfl⟩ : syracuseStep 12837689 = 9628267) B9628267
theorem B1696823 : Blo 750330 1696823 := bstep (se 1 (by rfl) ⟨1272617, by rfl⟩ : syracuseStep 1696823 = 2545235) B2545235
theorem B23161049 : Blo 750330 23161049 := bstep (se 2 (by rfl) ⟨8685393, by rfl⟩ : syracuseStep 23161049 = 17370787) B17370787
theorem B6089327 : Blo 750330 6089327 := bstep (se 1 (by rfl) ⟨4566995, by rfl⟩ : syracuseStep 6089327 = 9133991) B9133991
theorem B15625723 : Blo 750330 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B46395737 : Blo 750330 46395737 := bstep (se 2 (by rfl) ⟨17398401, by rfl⟩ : syracuseStep 46395737 = 34796803) B34796803
theorem B848551 : Blo 750330 848551 := bstep (se 1 (by rfl) ⟨636413, by rfl⟩ : syracuseStep 848551 = 1272827) B1272827
theorem B1864475 : Blo 750330 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B750527 : Blo 750330 750527 := bstep (se 1 (by rfl) ⟨562895, by rfl⟩ : syracuseStep 750527 = 1125791) B1125791
theorem B2716631 : Blo 750330 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B750703 : Blo 750330 750703 := bstep (se 1 (by rfl) ⟨563027, by rfl⟩ : syracuseStep 750703 = 1126055) B1126055
theorem B750719 : Blo 750330 750719 := bstep (se 1 (by rfl) ⟨563039, by rfl⟩ : syracuseStep 750719 = 1126079) B1126079
theorem B750783 : Blo 750330 750783 := bstep (se 1 (by rfl) ⟨563087, by rfl⟩ : syracuseStep 750783 = 1126175) B1126175
theorem B750975 : Blo 750330 750975 := bstep (se 1 (by rfl) ⟨563231, by rfl⟩ : syracuseStep 750975 = 1126463) B1126463
theorem B751103 : Blo 750330 751103 := bstep (se 1 (by rfl) ⟨563327, by rfl⟩ : syracuseStep 751103 = 1126655) B1126655
theorem B751131 : Blo 750330 751131 := bstep (se 1 (by rfl) ⟨563348, by rfl⟩ : syracuseStep 751131 = 1126697) B1126697
theorem B751311 : Blo 750330 751311 := bstep (se 1 (by rfl) ⟨563483, by rfl⟩ : syracuseStep 751311 = 1126967) B1126967
theorem B751471 : Blo 750330 751471 := bstep (se 1 (by rfl) ⟨563603, by rfl⟩ : syracuseStep 751471 = 1127207) B1127207
theorem B3209149 : Blo 750330 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B751551 : Blo 750330 751551 := bstep (se 1 (by rfl) ⟨563663, by rfl⟩ : syracuseStep 751551 = 1127327) B1127327
theorem B4290529 : Blo 750330 4290529 := bstep (se 2 (by rfl) ⟨1608948, by rfl⟩ : syracuseStep 4290529 = 3217897) B3217897
theorem B751867 : Blo 750330 751867 := bstep (se 1 (by rfl) ⟨563900, by rfl⟩ : syracuseStep 751867 = 1127801) B1127801
theorem B751871 : Blo 750330 751871 := bstep (se 1 (by rfl) ⟨563903, by rfl⟩ : syracuseStep 751871 = 1127807) B1127807
theorem B751975 : Blo 750330 751975 := bstep (se 1 (by rfl) ⟨563981, by rfl⟩ : syracuseStep 751975 = 1127963) B1127963
theorem B1604063 : Blo 750330 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B752095 : Blo 750330 752095 := bstep (se 1 (by rfl) ⟨564071, by rfl⟩ : syracuseStep 752095 = 1128143) B1128143
theorem B752231 : Blo 750330 752231 := bstep (se 1 (by rfl) ⟨564173, by rfl⟩ : syracuseStep 752231 = 1128347) B1128347
theorem B752255 : Blo 750330 752255 := bstep (se 1 (by rfl) ⟨564191, by rfl⟩ : syracuseStep 752255 = 1128383) B1128383
theorem B752367 : Blo 750330 752367 := bstep (se 1 (by rfl) ⟨564275, by rfl⟩ : syracuseStep 752367 = 1128551) B1128551
theorem B4291487 : Blo 750330 4291487 := bstep (se 1 (by rfl) ⟨3218615, by rfl⟩ : syracuseStep 4291487 = 6437231) B6437231
theorem B3800033 : Blo 750330 3800033 := bstep (se 2 (by rfl) ⟨1425012, by rfl⟩ : syracuseStep 3800033 = 2850025) B2850025
theorem B752623 : Blo 750330 752623 := bstep (se 1 (by rfl) ⟨564467, by rfl⟩ : syracuseStep 752623 = 1128935) B1128935
theorem B752671 : Blo 750330 752671 := bstep (se 1 (by rfl) ⟨564503, by rfl⟩ : syracuseStep 752671 = 1129007) B1129007
theorem B753119 : Blo 750330 753119 := bstep (se 1 (by rfl) ⟨564839, by rfl⟩ : syracuseStep 753119 = 1129679) B1129679
theorem B753179 : Blo 750330 753179 := bstep (se 1 (by rfl) ⟨564884, by rfl⟩ : syracuseStep 753179 = 1129769) B1129769
theorem B753199 : Blo 750330 753199 := bstep (se 1 (by rfl) ⟨564899, by rfl⟩ : syracuseStep 753199 = 1129799) B1129799
theorem B3210911 : Blo 750330 3210911 := bstep (se 1 (by rfl) ⟨2408183, by rfl⟩ : syracuseStep 3210911 = 4816367) B4816367
theorem B28934009 : Blo 750330 28934009 := bstep (se 2 (by rfl) ⟨10850253, by rfl⟩ : syracuseStep 28934009 = 21700507) B21700507
theorem B753599 : Blo 750330 753599 := bstep (se 1 (by rfl) ⟨565199, by rfl⟩ : syracuseStep 753599 = 1130399) B1130399
theorem B1900523 : Blo 750330 1900523 := bstep (se 1 (by rfl) ⟨1425392, by rfl⟩ : syracuseStep 1900523 = 2850785) B2850785
theorem B753659 : Blo 750330 753659 := bstep (se 1 (by rfl) ⟨565244, by rfl⟩ : syracuseStep 753659 = 1130489) B1130489
theorem B753691 : Blo 750330 753691 := bstep (se 1 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 753691 = 1130537) B1130537
theorem B753735 : Blo 750330 753735 := bstep (se 1 (by rfl) ⟨565301, by rfl⟩ : syracuseStep 753735 = 1130603) B1130603
theorem B754159 : Blo 750330 754159 := bstep (se 1 (by rfl) ⟨565619, by rfl⟩ : syracuseStep 754159 = 1131239) B1131239
theorem B16286453 : Blo 750330 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B3212909 : Blo 750330 3212909 := bstep (se 3 (by rfl) ⟨602420, by rfl⟩ : syracuseStep 3212909 = 1204841) B1204841
theorem B1902305 : Blo 750330 1902305 := bstep (se 2 (by rfl) ⟨713364, by rfl⟩ : syracuseStep 1902305 = 1426729) B1426729
theorem B952231 : Blo 750330 952231 := bstep (se 1 (by rfl) ⟨714173, by rfl⟩ : syracuseStep 952231 = 1428347) B1428347
theorem B1902811 : Blo 750330 1902811 := bstep (se 1 (by rfl) ⟨1427108, by rfl⟩ : syracuseStep 1902811 = 2854217) B2854217
theorem B6424859 : Blo 750330 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B7735625 : Blo 750330 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B5409271 : Blo 750330 5409271 := bstep (se 1 (by rfl) ⟨4056953, by rfl⟩ : syracuseStep 5409271 = 8113907) B8113907
theorem B3214343 : Blo 750330 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B1903783 : Blo 750330 1903783 := bstep (se 1 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 1903783 = 2855675) B2855675
theorem B1904249 : Blo 750330 1904249 := bstep (se 2 (by rfl) ⟨714093, by rfl⟩ : syracuseStep 1904249 = 1428187) B1428187
theorem B1904411 : Blo 750330 1904411 := bstep (se 1 (by rfl) ⟨1428308, by rfl⟩ : syracuseStep 1904411 = 2856617) B2856617
theorem B954175 : Blo 750330 954175 := bstep (se 1 (by rfl) ⟨715631, by rfl⟩ : syracuseStep 954175 = 1431263) B1431263
theorem B1806599 : Blo 750330 1806599 := bstep (se 1 (by rfl) ⟨1354949, by rfl⟩ : syracuseStep 1806599 = 2709899) B2709899
theorem B1806839 : Blo 750330 1806839 := bstep (se 1 (by rfl) ⟨1355129, by rfl⟩ : syracuseStep 1806839 = 2710259) B2710259
theorem B4232807 : Blo 750330 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B8558459 : Blo 750330 8558459 := bstep (se 1 (by rfl) ⟨6418844, by rfl⟩ : syracuseStep 8558459 = 12837689) B12837689
theorem B1907023 : Blo 750330 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B5708555 : Blo 750330 5708555 := bstep (se 1 (by rfl) ⟨4281416, by rfl⟩ : syracuseStep 5708555 = 8562833) B8562833
theorem B15440699 : Blo 750330 15440699 := bstep (se 1 (by rfl) ⟨11580524, by rfl⟩ : syracuseStep 15440699 = 23161049) B23161049
theorem B2169737 : Blo 750330 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B1907671 : Blo 750330 1907671 := bstep (se 1 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 1907671 = 2861507) B2861507
theorem B12820193 : Blo 750330 12820193 := bstep (se 2 (by rfl) ⟨4807572, by rfl⟩ : syracuseStep 12820193 = 9615145) B9615145
theorem B9641753 : Blo 750330 9641753 := bstep (se 2 (by rfl) ⟨3615657, by rfl⟩ : syracuseStep 9641753 = 7231315) B7231315
theorem B1811087 : Blo 750330 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B5776595 : Blo 750330 5776595 := bstep (se 1 (by rfl) ⟨4332446, by rfl⟩ : syracuseStep 5776595 = 8664893) B8664893
theorem B11150729 : Blo 750330 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B5711471 : Blo 750330 5711471 := bstep (se 1 (by rfl) ⟨4283603, by rfl⟩ : syracuseStep 5711471 = 8567207) B8567207
theorem B2860991 : Blo 750330 2860991 := bstep (se 1 (by rfl) ⟨2145743, by rfl⟩ : syracuseStep 2860991 = 4291487) B4291487
theorem B2533355 : Blo 750330 2533355 := bstep (se 1 (by rfl) ⟨1900016, by rfl⟩ : syracuseStep 2533355 = 3800033) B3800033
theorem B2140607 : Blo 750330 2140607 := bstep (se 1 (by rfl) ⟨1605455, by rfl⟩ : syracuseStep 2140607 = 3210911) B3210911
theorem B6433607 : Blo 750330 6433607 := bstep (se 1 (by rfl) ⟨4825205, by rfl⟩ : syracuseStep 6433607 = 9650411) B9650411
theorem B3812993 : Blo 750330 3812993 := bstep (se 2 (by rfl) ⟨1429872, by rfl⟩ : syracuseStep 3812993 = 2859745) B2859745
theorem B2535083 : Blo 750330 2535083 := bstep (se 1 (by rfl) ⟨1901312, by rfl⟩ : syracuseStep 2535083 = 3802625) B3802625
theorem B1126427 : Blo 750330 1126427 := bstep (se 1 (by rfl) ⟨844820, by rfl⟩ : syracuseStep 1126427 = 1689641) B1689641
theorem B2142247 : Blo 750330 2142247 := bstep (se 1 (by rfl) ⟨1606685, by rfl⟩ : syracuseStep 2142247 = 3213371) B3213371
theorem B1126607 : Blo 750330 1126607 := bstep (se 1 (by rfl) ⟨844955, by rfl⟩ : syracuseStep 1126607 = 1689911) B1689911
theorem B963751 : Blo 750330 963751 := bstep (se 1 (by rfl) ⟨722813, by rfl⟩ : syracuseStep 963751 = 1445627) B1445627
theorem B3618215 : Blo 750330 3618215 := bstep (se 1 (by rfl) ⟨2713661, by rfl⟩ : syracuseStep 3618215 = 5427323) B5427323
theorem B2143739 : Blo 750330 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B3815585 : Blo 750330 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B2537783 : Blo 750330 2537783 := bstep (se 1 (by rfl) ⟨1903337, by rfl⟩ : syracuseStep 2537783 = 3806675) B3806675
theorem B4962617 : Blo 750330 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B6961639 : Blo 750330 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B1129499 : Blo 750330 1129499 := bstep (se 1 (by rfl) ⟨847124, by rfl⟩ : syracuseStep 1129499 = 1694249) B1694249
theorem B1129883 : Blo 750330 1129883 := bstep (se 1 (by rfl) ⟨847412, by rfl⟩ : syracuseStep 1129883 = 1694825) B1694825
theorem B2539079 : Blo 750330 2539079 := bstep (se 1 (by rfl) ⟨1904309, by rfl⟩ : syracuseStep 2539079 = 3808619) B3808619
theorem B1130351 : Blo 750330 1130351 := bstep (se 1 (by rfl) ⟨847763, by rfl⟩ : syracuseStep 1130351 = 1695527) B1695527
theorem B1425377 : Blo 750330 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B1130567 : Blo 750330 1130567 := bstep (se 1 (by rfl) ⟨847925, by rfl⟩ : syracuseStep 1130567 = 1695851) B1695851
theorem B2539943 : Blo 750330 2539943 := bstep (se 1 (by rfl) ⟨1904957, by rfl⟩ : syracuseStep 2539943 = 3809915) B3809915
theorem B1131215 : Blo 750330 1131215 := bstep (se 1 (by rfl) ⟨848411, by rfl⟩ : syracuseStep 1131215 = 1696823) B1696823
theorem B1131401 : Blo 750330 1131401 := bstep (se 2 (by rfl) ⟨424275, by rfl⟩ : syracuseStep 1131401 = 848551) B848551
theorem B1098731 : Blo 750330 1098731 := bstep (se 1 (by rfl) ⟨824048, by rfl⟩ : syracuseStep 1098731 = 1648097) B1648097
theorem B1688759 : Blo 750330 1688759 := bstep (se 1 (by rfl) ⟨1266569, by rfl⟩ : syracuseStep 1688759 = 2533139) B2533139
theorem B1689065 : Blo 750330 1689065 := bstep (se 2 (by rfl) ⟨633399, by rfl⟩ : syracuseStep 1689065 = 1266799) B1266799
theorem B2541239 : Blo 750330 2541239 := bstep (se 1 (by rfl) ⟨1905929, by rfl⟩ : syracuseStep 2541239 = 3811859) B3811859
theorem B29280001 : Blo 750330 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B4114451 : Blo 750330 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B3656123 : Blo 750330 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B1690091 : Blo 750330 1690091 := bstep (se 1 (by rfl) ⟨1267568, by rfl⟩ : syracuseStep 1690091 = 2535137) B2535137
theorem B8145481 : Blo 750330 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B4278865 : Blo 750330 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B5720705 : Blo 750330 5720705 := bstep (se 2 (by rfl) ⟨2145264, by rfl⟩ : syracuseStep 5720705 = 4290529) B4290529
theorem B1690793 : Blo 750330 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B9751735 : Blo 750330 9751735 := bstep (se 1 (by rfl) ⟨7313801, by rfl⟩ : syracuseStep 9751735 = 14627603) B14627603
theorem B1691135 : Blo 750330 1691135 := bstep (se 1 (by rfl) ⟨1268351, by rfl⟩ : syracuseStep 1691135 = 2536703) B2536703
theorem B6868513 : Blo 750330 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B1691369 : Blo 750330 1691369 := bstep (se 2 (by rfl) ⟨634263, by rfl⟩ : syracuseStep 1691369 = 1268527) B1268527
theorem B904991 : Blo 750330 904991 := bstep (se 1 (by rfl) ⟨678743, by rfl⟩ : syracuseStep 904991 = 1357487) B1357487
theorem B1691639 : Blo 750330 1691639 := bstep (se 1 (by rfl) ⟨1268729, by rfl⟩ : syracuseStep 1691639 = 2537459) B2537459
theorem B1069375 : Blo 750330 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B2543993 : Blo 750330 2543993 := bstep (se 2 (by rfl) ⟨953997, by rfl⟩ : syracuseStep 2543993 = 1907995) B1907995
theorem B2544371 : Blo 750330 2544371 := bstep (se 1 (by rfl) ⟨1908278, by rfl⟩ : syracuseStep 2544371 = 3816557) B3816557
theorem B10867445 : Blo 750330 10867445 := bstep (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) B1018823
theorem B1692755 : Blo 750330 1692755 := bstep (se 1 (by rfl) ⟨1269566, by rfl⟩ : syracuseStep 1692755 = 2539133) B2539133
theorem B1692863 : Blo 750330 1692863 := bstep (se 1 (by rfl) ⟨1269647, by rfl⟩ : syracuseStep 1692863 = 2539295) B2539295
theorem B19289339 : Blo 750330 19289339 := bstep (se 1 (by rfl) ⟨14467004, by rfl⟩ : syracuseStep 19289339 = 28934009) B28934009
theorem B1267015 : Blo 750330 1267015 := bstep (se 1 (by rfl) ⟨950261, by rfl⟩ : syracuseStep 1267015 = 1900523) B1900523
theorem B1693007 : Blo 750330 1693007 := bstep (se 1 (by rfl) ⟨1269755, by rfl⟩ : syracuseStep 1693007 = 2539511) B2539511
theorem B2545343 : Blo 750330 2545343 := bstep (se 1 (by rfl) ⟨1909007, by rfl⟩ : syracuseStep 2545343 = 3818015) B3818015
theorem B2545505 : Blo 750330 2545505 := bstep (se 2 (by rfl) ⟨954564, by rfl⟩ : syracuseStep 2545505 = 1909129) B1909129
theorem B1693583 : Blo 750330 1693583 := bstep (se 1 (by rfl) ⟨1270187, by rfl⟩ : syracuseStep 1693583 = 2540375) B2540375
theorem B1693691 : Blo 750330 1693691 := bstep (se 1 (by rfl) ⟨1270268, by rfl⟩ : syracuseStep 1693691 = 2540537) B2540537
theorem B1693727 : Blo 750330 1693727 := bstep (se 1 (by rfl) ⟨1270295, by rfl⟩ : syracuseStep 1693727 = 2540591) B2540591
theorem B2545775 : Blo 750330 2545775 := bstep (se 1 (by rfl) ⟨1909331, by rfl⟩ : syracuseStep 2545775 = 3818663) B3818663
theorem B2709625 : Blo 750330 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B1267879 : Blo 750330 1267879 := bstep (se 1 (by rfl) ⟨950909, by rfl⟩ : syracuseStep 1267879 = 1901819) B1901819
theorem B1694303 : Blo 750330 1694303 := bstep (se 1 (by rfl) ⟨1270727, by rfl⟩ : syracuseStep 1694303 = 2541455) B2541455
theorem B1694879 : Blo 750330 1694879 := bstep (se 1 (by rfl) ⟨1271159, by rfl⟩ : syracuseStep 1694879 = 2542319) B2542319
theorem B3432071 : Blo 750330 3432071 := bstep (se 1 (by rfl) ⟨2574053, by rfl⟩ : syracuseStep 3432071 = 5148107) B5148107
theorem B1269823 : Blo 750330 1269823 := bstep (se 1 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 1269823 = 1904735) B1904735
theorem B3531005 : Blo 750330 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B8118623 : Blo 750330 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B4645439 : Blo 750330 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B844519 : Blo 750330 844519 := bstep (se 1 (by rfl) ⟨633389, by rfl⟩ : syracuseStep 844519 = 1266779) B1266779
theorem B6972367 : Blo 750330 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B1696751 : Blo 750330 1696751 := bstep (se 1 (by rfl) ⟨1272563, by rfl⟩ : syracuseStep 1696751 = 2545127) B2545127
theorem B27813719 : Blo 750330 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B20834297 : Blo 750330 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B846031 : Blo 750330 846031 := bstep (se 1 (by rfl) ⟨634523, by rfl⟩ : syracuseStep 846031 = 1269047) B1269047
theorem B1272415 : Blo 750330 1272415 := bstep (se 1 (by rfl) ⟨954311, by rfl⟩ : syracuseStep 1272415 = 1908623) B1908623
theorem B4287113 : Blo 750330 4287113 := bstep (se 2 (by rfl) ⟨1607667, by rfl⟩ : syracuseStep 4287113 = 3215335) B3215335
theorem B15428555 : Blo 750330 15428555 := bstep (se 1 (by rfl) ⟨11571416, by rfl⟩ : syracuseStep 15428555 = 23142833) B23142833
theorem B847003 : Blo 750330 847003 := bstep (se 1 (by rfl) ⟨635252, by rfl⟩ : syracuseStep 847003 = 1270505) B1270505
theorem B5434559 : Blo 750330 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B9138167 : Blo 750330 9138167 := bstep (se 1 (by rfl) ⟨6853625, by rfl⟩ : syracuseStep 9138167 = 13707251) B13707251
theorem B4059551 : Blo 750330 4059551 := bstep (se 1 (by rfl) ⟨3044663, by rfl⟩ : syracuseStep 4059551 = 6089327) B6089327
theorem B750367 : Blo 750330 750367 := bstep (se 1 (by rfl) ⟨562775, by rfl⟩ : syracuseStep 750367 = 1125551) B1125551
theorem B750407 : Blo 750330 750407 := bstep (se 1 (by rfl) ⟨562805, by rfl⟩ : syracuseStep 750407 = 1125611) B1125611
theorem B750619 : Blo 750330 750619 := bstep (se 1 (by rfl) ⟨562964, by rfl⟩ : syracuseStep 750619 = 1125929) B1125929
theorem B750847 : Blo 750330 750847 := bstep (se 1 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 750847 = 1126271) B1126271
theorem B30930491 : Blo 750330 30930491 := bstep (se 1 (by rfl) ⟨23197868, by rfl⟩ : syracuseStep 30930491 = 46395737) B46395737
theorem B1242983 : Blo 750330 1242983 := bstep (se 1 (by rfl) ⟨932237, by rfl⟩ : syracuseStep 1242983 = 1864475) B1864475
theorem B1603721 : Blo 750330 1603721 := bstep (se 2 (by rfl) ⟨601395, by rfl⟩ : syracuseStep 1603721 = 1202791) B1202791
theorem B751855 : Blo 750330 751855 := bstep (se 1 (by rfl) ⟨563891, by rfl⟩ : syracuseStep 751855 = 1127783) B1127783
theorem B20609923 : Blo 750330 20609923 := bstep (se 1 (by rfl) ⟨15457442, by rfl⟩ : syracuseStep 20609923 = 30914885) B30914885
theorem B752635 : Blo 750330 752635 := bstep (se 1 (by rfl) ⟨564476, by rfl⟩ : syracuseStep 752635 = 1128953) B1128953
theorem B752879 : Blo 750330 752879 := bstep (se 1 (by rfl) ⟨564659, by rfl⟩ : syracuseStep 752879 = 1129319) B1129319
theorem B752923 : Blo 750330 752923 := bstep (se 1 (by rfl) ⟨564692, by rfl⟩ : syracuseStep 752923 = 1129385) B1129385
theorem B753311 : Blo 750330 753311 := bstep (se 1 (by rfl) ⟨564983, by rfl⟩ : syracuseStep 753311 = 1129967) B1129967
theorem B753403 : Blo 750330 753403 := bstep (se 1 (by rfl) ⟨565052, by rfl⟩ : syracuseStep 753403 = 1130105) B1130105
theorem B753711 : Blo 750330 753711 := bstep (se 1 (by rfl) ⟨565283, by rfl⟩ : syracuseStep 753711 = 1130567) B1130567
theorem B754143 : Blo 750330 754143 := bstep (se 1 (by rfl) ⟨565607, by rfl⟩ : syracuseStep 754143 = 1131215) B1131215
theorem B754267 : Blo 750330 754267 := bstep (se 1 (by rfl) ⟨565700, by rfl⟩ : syracuseStep 754267 = 1131401) B1131401
theorem B7244963 : Blo 750330 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B7212361 : Blo 750330 7212361 := bstep (se 2 (by rfl) ⟨2704635, by rfl⟩ : syracuseStep 7212361 = 5409271) B5409271
theorem B5705153 : Blo 750330 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B2821871 : Blo 750330 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B5705639 : Blo 750330 5705639 := bstep (se 1 (by rfl) ⟨4279229, by rfl⟩ : syracuseStep 5705639 = 8558459) B8558459
theorem B3805703 : Blo 750330 3805703 := bstep (se 1 (by rfl) ⟨2854277, by rfl⟩ : syracuseStep 3805703 = 5708555) B5708555
theorem B10293799 : Blo 750330 10293799 := bstep (se 1 (by rfl) ⟨7720349, by rfl⟩ : syracuseStep 10293799 = 15440699) B15440699
theorem B1446491 : Blo 750330 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B3314621 : Blo 750330 3314621 := bstep (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) B1242983
theorem B6427835 : Blo 750330 6427835 := bstep (se 1 (by rfl) ⟨4820876, by rfl⟩ : syracuseStep 6427835 = 9641753) B9641753
theorem B2856329 : Blo 750330 2856329 := bstep (se 2 (by rfl) ⟨1071123, by rfl⟩ : syracuseStep 2856329 = 2142247) B2142247
theorem B5412415 : Blo 750330 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B52009253 : Blo 750330 52009253 := bstep (se 4 (by rfl) ⟨4875867, by rfl⟩ : syracuseStep 52009253 = 9751735) B9751735
theorem B3807647 : Blo 750330 3807647 := bstep (se 1 (by rfl) ⟨2855735, by rfl⟩ : syracuseStep 3807647 = 5711471) B5711471
theorem B1907327 : Blo 750330 1907327 := bstep (se 1 (by rfl) ⟨1430495, by rfl⟩ : syracuseStep 1907327 = 2860991) B2860991
theorem B1285001 : Blo 750330 1285001 := bstep (se 2 (by rfl) ⟨481875, by rfl⟩ : syracuseStep 1285001 = 963751) B963751
theorem B2858075 : Blo 750330 2858075 := bstep (se 1 (by rfl) ⟨2143556, by rfl⟩ : syracuseStep 2858075 = 4287113) B4287113
theorem B3612833 : Blo 750330 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B9282185 : Blo 750330 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B20620327 : Blo 750330 20620327 := bstep (se 1 (by rfl) ⟨15465245, by rfl⟩ : syracuseStep 20620327 = 30930491) B30930491
theorem B10857635 : Blo 750330 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B1125839 : Blo 750330 1125839 := bstep (se 1 (by rfl) ⟨844379, by rfl⟩ : syracuseStep 1125839 = 1688759) B1688759
theorem B1126025 : Blo 750330 1126025 := bstep (se 2 (by rfl) ⟨422259, by rfl⟩ : syracuseStep 1126025 = 844519) B844519
theorem B1126043 : Blo 750330 1126043 := bstep (se 1 (by rfl) ⟨844532, by rfl⟩ : syracuseStep 1126043 = 1689065) B1689065
theorem B2141939 : Blo 750330 2141939 := bstep (se 1 (by rfl) ⟨1606454, by rfl⟩ : syracuseStep 2141939 = 3212909) B3212909
theorem B5157083 : Blo 750330 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B2437415 : Blo 750330 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B1126727 : Blo 750330 1126727 := bstep (se 1 (by rfl) ⟨845045, by rfl⟩ : syracuseStep 1126727 = 1690091) B1690091
theorem B3813803 : Blo 750330 3813803 := bstep (se 1 (by rfl) ⟨2860352, by rfl⟩ : syracuseStep 3813803 = 5720705) B5720705
theorem B1127195 : Blo 750330 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B1127423 : Blo 750330 1127423 := bstep (se 1 (by rfl) ⟨845567, by rfl⟩ : syracuseStep 1127423 = 1691135) B1691135
theorem B39040001 : Blo 750330 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B1127579 : Blo 750330 1127579 := bstep (se 1 (by rfl) ⟨845684, by rfl⟩ : syracuseStep 1127579 = 1691369) B1691369
theorem B2929949 : Blo 750330 2929949 := bstep (se 3 (by rfl) ⟨549365, by rfl⟩ : syracuseStep 2929949 = 1098731) B1098731
theorem B1127759 : Blo 750330 1127759 := bstep (se 1 (by rfl) ⟨845819, by rfl⟩ : syracuseStep 1127759 = 1691639) B1691639
theorem B1128041 : Blo 750330 1128041 := bstep (se 2 (by rfl) ⟨423015, by rfl⟩ : syracuseStep 1128041 = 846031) B846031
theorem B2537081 : Blo 750330 2537081 := bstep (se 2 (by rfl) ⟨951405, by rfl⟩ : syracuseStep 2537081 = 1902811) B1902811
theorem B702199637 : Blo 750330 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B1128503 : Blo 750330 1128503 := bstep (se 1 (by rfl) ⟨846377, by rfl⟩ : syracuseStep 1128503 = 1692755) B1692755
theorem B10860641 : Blo 750330 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B1128575 : Blo 750330 1128575 := bstep (se 1 (by rfl) ⟨846431, by rfl⟩ : syracuseStep 1128575 = 1692863) B1692863
theorem B12859559 : Blo 750330 12859559 := bstep (se 1 (by rfl) ⟨9644669, by rfl⟩ : syracuseStep 12859559 = 19289339) B19289339
theorem B1128671 : Blo 750330 1128671 := bstep (se 1 (by rfl) ⟨846503, by rfl⟩ : syracuseStep 1128671 = 1693007) B1693007
theorem B1129055 : Blo 750330 1129055 := bstep (se 1 (by rfl) ⟨846791, by rfl⟩ : syracuseStep 1129055 = 1693583) B1693583
theorem B1129127 : Blo 750330 1129127 := bstep (se 1 (by rfl) ⟨846845, by rfl⟩ : syracuseStep 1129127 = 1693691) B1693691
theorem B1129151 : Blo 750330 1129151 := bstep (se 1 (by rfl) ⟨846863, by rfl⟩ : syracuseStep 1129151 = 1693727) B1693727
theorem B1129337 : Blo 750330 1129337 := bstep (se 2 (by rfl) ⟨423501, by rfl⟩ : syracuseStep 1129337 = 847003) B847003
theorem B2538377 : Blo 750330 2538377 := bstep (se 2 (by rfl) ⟨951891, by rfl⟩ : syracuseStep 2538377 = 1903783) B1903783
theorem B1129535 : Blo 750330 1129535 := bstep (se 1 (by rfl) ⟨847151, by rfl⟩ : syracuseStep 1129535 = 1694303) B1694303
theorem B9158017 : Blo 750330 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B1129919 : Blo 750330 1129919 := bstep (se 1 (by rfl) ⟨847439, by rfl⟩ : syracuseStep 1129919 = 1694879) B1694879
theorem B3096959 : Blo 750330 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B1425833 : Blo 750330 1425833 := bstep (se 2 (by rfl) ⟨534687, by rfl⟩ : syracuseStep 1425833 = 1069375) B1069375
theorem B1131167 : Blo 750330 1131167 := bstep (se 1 (by rfl) ⟨848375, by rfl⟩ : syracuseStep 1131167 = 1696751) B1696751
theorem B3851063 : Blo 750330 3851063 := bstep (se 1 (by rfl) ⟨2888297, by rfl⟩ : syracuseStep 3851063 = 5776595) B5776595
theorem B1688903 : Blo 750330 1688903 := bstep (se 1 (by rfl) ⟨1266677, by rfl⟩ : syracuseStep 1688903 = 2533355) B2533355
theorem B1427071 : Blo 750330 1427071 := bstep (se 1 (by rfl) ⟨1070303, by rfl⟩ : syracuseStep 1427071 = 2140607) B2140607
theorem B1689353 : Blo 750330 1689353 := bstep (se 2 (by rfl) ⟨633507, by rfl⟩ : syracuseStep 1689353 = 1267015) B1267015
theorem B3623039 : Blo 750330 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B2541995 : Blo 750330 2541995 := bstep (se 1 (by rfl) ⟨1906496, by rfl⟩ : syracuseStep 2541995 = 3812993) B3812993
theorem B1690055 : Blo 750330 1690055 := bstep (se 1 (by rfl) ⟨1267541, by rfl⟩ : syracuseStep 1690055 = 2535083) B2535083
theorem B8571581 : Blo 750330 8571581 := bstep (se 3 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 8571581 = 3214343) B3214343
theorem B1690505 : Blo 750330 1690505 := bstep (se 2 (by rfl) ⟨633939, by rfl⟩ : syracuseStep 1690505 = 1267879) B1267879
theorem B2706367 : Blo 750330 2706367 := bstep (se 1 (by rfl) ⟨2029775, by rfl⟩ : syracuseStep 2706367 = 4059551) B4059551
theorem B2542697 : Blo 750330 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B2412143 : Blo 750330 2412143 := bstep (se 1 (by rfl) ⟨1809107, by rfl⟩ : syracuseStep 2412143 = 3618215) B3618215
theorem B1429159 : Blo 750330 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B27479897 : Blo 750330 27479897 := bstep (se 2 (by rfl) ⟨10304961, by rfl⟩ : syracuseStep 27479897 = 20609923) B20609923
theorem B2543561 : Blo 750330 2543561 := bstep (se 2 (by rfl) ⟨953835, by rfl⟩ : syracuseStep 2543561 = 1907671) B1907671
theorem B1069147 : Blo 750330 1069147 := bstep (se 1 (by rfl) ⟨801860, by rfl⟩ : syracuseStep 1069147 = 1603721) B1603721
theorem B2543723 : Blo 750330 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B1691855 : Blo 750330 1691855 := bstep (se 1 (by rfl) ⟨1268891, by rfl⟩ : syracuseStep 1691855 = 2537783) B2537783
theorem B2413309 : Blo 750330 2413309 := bstep (se 3 (by rfl) ⟨452495, by rfl⟩ : syracuseStep 2413309 = 904991) B904991
theorem B1692719 : Blo 750330 1692719 := bstep (se 1 (by rfl) ⟨1269539, by rfl⟩ : syracuseStep 1692719 = 2539079) B2539079
theorem B1693097 : Blo 750330 1693097 := bstep (se 2 (by rfl) ⟨634911, by rfl⟩ : syracuseStep 1693097 = 1269823) B1269823
theorem B1693295 : Blo 750330 1693295 := bstep (se 1 (by rfl) ⟨1269971, by rfl⟩ : syracuseStep 1693295 = 2539943) B2539943
theorem B1694159 : Blo 750330 1694159 := bstep (se 1 (by rfl) ⟨1270619, by rfl⟩ : syracuseStep 1694159 = 2541239) B2541239
theorem B1268203 : Blo 750330 1268203 := bstep (se 1 (by rfl) ⟨951152, by rfl⟩ : syracuseStep 1268203 = 1902305) B1902305
theorem B9296489 : Blo 750330 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B4283239 : Blo 750330 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B1269499 : Blo 750330 1269499 := bstep (se 1 (by rfl) ⟨952124, by rfl⟩ : syracuseStep 1269499 = 1904249) B1904249
theorem B1269607 : Blo 750330 1269607 := bstep (se 1 (by rfl) ⟨952205, by rfl⟩ : syracuseStep 1269607 = 1904411) B1904411
theorem B1269641 : Blo 750330 1269641 := bstep (se 2 (by rfl) ⟨476115, by rfl⟩ : syracuseStep 1269641 = 952231) B952231
theorem B1204399 : Blo 750330 1204399 := bstep (se 1 (by rfl) ⟨903299, by rfl⟩ : syracuseStep 1204399 = 1806599) B1806599
theorem B1695995 : Blo 750330 1695995 := bstep (se 1 (by rfl) ⟨1271996, by rfl⟩ : syracuseStep 1695995 = 2543993) B2543993
theorem B1204559 : Blo 750330 1204559 := bstep (se 1 (by rfl) ⟨903419, by rfl⟩ : syracuseStep 1204559 = 1806839) B1806839
theorem B1696247 : Blo 750330 1696247 := bstep (se 1 (by rfl) ⟨1272185, by rfl⟩ : syracuseStep 1696247 = 2544371) B2544371
theorem B1696553 : Blo 750330 1696553 := bstep (se 2 (by rfl) ⟨636207, by rfl⟩ : syracuseStep 1696553 = 1272415) B1272415
theorem B1696895 : Blo 750330 1696895 := bstep (se 1 (by rfl) ⟨1272671, by rfl⟩ : syracuseStep 1696895 = 2545343) B2545343
theorem B1697003 : Blo 750330 1697003 := bstep (se 1 (by rfl) ⟨1272752, by rfl⟩ : syracuseStep 1697003 = 2545505) B2545505
theorem B1697183 : Blo 750330 1697183 := bstep (se 1 (by rfl) ⟨1272887, by rfl⟩ : syracuseStep 1697183 = 2545775) B2545775
theorem B1272233 : Blo 750330 1272233 := bstep (se 2 (by rfl) ⟨477087, by rfl⟩ : syracuseStep 1272233 = 954175) B954175
theorem B2288047 : Blo 750330 2288047 := bstep (se 1 (by rfl) ⟨1716035, by rfl⟩ : syracuseStep 2288047 = 3432071) B3432071
theorem B8546795 : Blo 750330 8546795 := bstep (se 1 (by rfl) ⟨6410096, by rfl⟩ : syracuseStep 8546795 = 12820193) B12820193
theorem B2354003 : Blo 750330 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B1207391 : Blo 750330 1207391 := bstep (se 1 (by rfl) ⟨905543, by rfl⟩ : syracuseStep 1207391 = 1811087) B1811087
theorem B7433819 : Blo 750330 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B18542479 : Blo 750330 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B13889531 : Blo 750330 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B4289071 : Blo 750330 4289071 := bstep (se 1 (by rfl) ⟨3216803, by rfl⟩ : syracuseStep 4289071 = 6433607) B6433607
theorem B10285703 : Blo 750330 10285703 := bstep (se 1 (by rfl) ⟨7714277, by rfl⟩ : syracuseStep 10285703 = 15428555) B15428555
theorem B6092111 : Blo 750330 6092111 := bstep (se 1 (by rfl) ⟨4569083, by rfl⟩ : syracuseStep 6092111 = 9138167) B9138167
theorem B750951 : Blo 750330 750951 := bstep (se 1 (by rfl) ⟨563213, by rfl⟩ : syracuseStep 750951 = 1126427) B1126427
theorem B751071 : Blo 750330 751071 := bstep (se 1 (by rfl) ⟨563303, by rfl⟩ : syracuseStep 751071 = 1126607) B1126607
theorem B3308411 : Blo 750330 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B752999 : Blo 750330 752999 := bstep (se 1 (by rfl) ⟨564749, by rfl⟩ : syracuseStep 752999 = 1129499) B1129499
theorem B753255 : Blo 750330 753255 := bstep (se 1 (by rfl) ⟨564941, by rfl⟩ : syracuseStep 753255 = 1129883) B1129883
theorem B753567 : Blo 750330 753567 := bstep (se 1 (by rfl) ⟨565175, by rfl⟩ : syracuseStep 753567 = 1130351) B1130351
theorem B3801005 : Blo 750330 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B950555 : Blo 750330 950555 := bstep (se 1 (by rfl) ⟨712916, by rfl⟩ : syracuseStep 950555 = 1425833) B1425833
theorem B754111 : Blo 750330 754111 := bstep (se 1 (by rfl) ⟨565583, by rfl⟩ : syracuseStep 754111 = 1131167) B1131167
theorem B6423461 : Blo 750330 6423461 := bstep (se 4 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 6423461 = 1204399) B1204399
theorem B8258557 : Blo 750330 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B27493769 : Blo 750330 27493769 := bstep (se 2 (by rfl) ⟨10310163, by rfl⟩ : syracuseStep 27493769 = 20620327) B20620327
theorem B1902761 : Blo 750330 1902761 := bstep (se 2 (by rfl) ⟨713535, by rfl⟩ : syracuseStep 1902761 = 1427071) B1427071
theorem B3803435 : Blo 750330 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B1608095 : Blo 750330 1608095 := bstep (se 1 (by rfl) ⟨1206071, by rfl⟩ : syracuseStep 1608095 = 2412143) B2412143
theorem B18319931 : Blo 750330 18319931 := bstep (se 1 (by rfl) ⟨13739948, by rfl⟩ : syracuseStep 18319931 = 27479897) B27479897
theorem B3803759 : Blo 750330 3803759 := bstep (se 1 (by rfl) ⟨2852819, by rfl⟩ : syracuseStep 3803759 = 5705639) B5705639
theorem B3050729 : Blo 750330 3050729 := bstep (se 2 (by rfl) ⟨1144023, by rfl⟩ : syracuseStep 3050729 = 2288047) B2288047
theorem B1904219 : Blo 750330 1904219 := bstep (se 1 (by rfl) ⟨1428164, by rfl⟩ : syracuseStep 1904219 = 2856329) B2856329
theorem B3608489 : Blo 750330 3608489 := bstep (se 2 (by rfl) ⟨1353183, by rfl⟩ : syracuseStep 3608489 = 2706367) B2706367
theorem B34672835 : Blo 750330 34672835 := bstep (se 1 (by rfl) ⟨26004626, by rfl⟩ : syracuseStep 34672835 = 52009253) B52009253
theorem B856667 : Blo 750330 856667 := bstep (se 1 (by rfl) ⟨642500, by rfl⟩ : syracuseStep 856667 = 1285001) B1285001
theorem B1905383 : Blo 750330 1905383 := bstep (se 1 (by rfl) ⟨1429037, by rfl⟩ : syracuseStep 1905383 = 2858075) B2858075
theorem B1905545 : Blo 750330 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B3217745 : Blo 750330 3217745 := bstep (se 2 (by rfl) ⟨1206654, by rfl⟩ : syracuseStep 3217745 = 2413309) B2413309
theorem B7216553 : Blo 750330 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B4955879 : Blo 750330 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B3219709 : Blo 750330 3219709 := bstep (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) B1207391
theorem B6857135 : Blo 750330 6857135 := bstep (se 1 (by rfl) ⟨5142851, by rfl⟩ : syracuseStep 6857135 = 10285703) B10285703
theorem B26026667 : Blo 750330 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B25109365 : Blo 750330 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B5710985 : Blo 750330 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B468133091 : Blo 750330 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B2205607 : Blo 750330 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B2534003 : Blo 750330 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B2567375 : Blo 750330 2567375 := bstep (se 1 (by rfl) ⟨1925531, by rfl⟩ : syracuseStep 2567375 = 3851063) B3851063
theorem B1125935 : Blo 750330 1125935 := bstep (se 1 (by rfl) ⟨844451, by rfl⟩ : syracuseStep 1125935 = 1688903) B1688903
theorem B1126235 : Blo 750330 1126235 := bstep (se 1 (by rfl) ⟨844676, by rfl⟩ : syracuseStep 1126235 = 1689353) B1689353
theorem B1126703 : Blo 750330 1126703 := bstep (se 1 (by rfl) ⟨845027, by rfl⟩ : syracuseStep 1126703 = 1690055) B1690055
theorem B5714387 : Blo 750330 5714387 := bstep (se 1 (by rfl) ⟨4285790, by rfl⟩ : syracuseStep 5714387 = 8571581) B8571581
theorem B1127003 : Blo 750330 1127003 := bstep (se 1 (by rfl) ⟨845252, by rfl⟩ : syracuseStep 1127003 = 1690505) B1690505
theorem B4829975 : Blo 750330 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B1127903 : Blo 750330 1127903 := bstep (se 1 (by rfl) ⟨845927, by rfl⟩ : syracuseStep 1127903 = 1691855) B1691855
theorem B2537135 : Blo 750330 2537135 := bstep (se 1 (by rfl) ⟨1902851, by rfl⟩ : syracuseStep 2537135 = 3805703) B3805703
theorem B964327 : Blo 750330 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B2209747 : Blo 750330 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B1128479 : Blo 750330 1128479 := bstep (se 1 (by rfl) ⟨846359, by rfl⟩ : syracuseStep 1128479 = 1692719) B1692719
theorem B1128731 : Blo 750330 1128731 := bstep (se 1 (by rfl) ⟨846548, by rfl⟩ : syracuseStep 1128731 = 1693097) B1693097
theorem B1128863 : Blo 750330 1128863 := bstep (se 1 (by rfl) ⟨846647, by rfl⟩ : syracuseStep 1128863 = 1693295) B1693295
theorem B2538431 : Blo 750330 2538431 := bstep (se 1 (by rfl) ⟨1903823, by rfl⟩ : syracuseStep 2538431 = 3807647) B3807647
theorem B1129439 : Blo 750330 1129439 := bstep (se 1 (by rfl) ⟨847079, by rfl⟩ : syracuseStep 1129439 = 1694159) B1694159
theorem B9616481 : Blo 750330 9616481 := bstep (se 2 (by rfl) ⟨3606180, by rfl⟩ : syracuseStep 9616481 = 7212361) B7212361
theorem B24723305 : Blo 750330 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B2408555 : Blo 750330 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B1425529 : Blo 750330 1425529 := bstep (se 2 (by rfl) ⟨534573, by rfl⟩ : syracuseStep 1425529 = 1069147) B1069147
theorem B1130663 : Blo 750330 1130663 := bstep (se 1 (by rfl) ⟨847997, by rfl⟩ : syracuseStep 1130663 = 1695995) B1695995
theorem B803039 : Blo 750330 803039 := bstep (se 1 (by rfl) ⟨602279, by rfl⟩ : syracuseStep 803039 = 1204559) B1204559
theorem B1130831 : Blo 750330 1130831 := bstep (se 1 (by rfl) ⟨848123, by rfl⟩ : syracuseStep 1130831 = 1696247) B1696247
theorem B1131035 : Blo 750330 1131035 := bstep (se 1 (by rfl) ⟨848276, by rfl⟩ : syracuseStep 1131035 = 1696553) B1696553
theorem B5718761 : Blo 750330 5718761 := bstep (se 2 (by rfl) ⟨2144535, by rfl⟩ : syracuseStep 5718761 = 4289071) B4289071
theorem B1131263 : Blo 750330 1131263 := bstep (se 1 (by rfl) ⟨848447, by rfl⟩ : syracuseStep 1131263 = 1696895) B1696895
theorem B1131335 : Blo 750330 1131335 := bstep (se 1 (by rfl) ⟨848501, by rfl⟩ : syracuseStep 1131335 = 1697003) B1697003
theorem B1131455 : Blo 750330 1131455 := bstep (se 1 (by rfl) ⟨848591, by rfl⟩ : syracuseStep 1131455 = 1697183) B1697183
theorem B24790637 : Blo 750330 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B1427959 : Blo 750330 1427959 := bstep (se 1 (by rfl) ⟨1070969, by rfl⟩ : syracuseStep 1427959 = 2141939) B2141939
theorem B9259687 : Blo 750330 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B1624943 : Blo 750330 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B2542535 : Blo 750330 2542535 := bstep (se 1 (by rfl) ⟨1906901, by rfl⟩ : syracuseStep 2542535 = 3813803) B3813803
theorem B1690937 : Blo 750330 1690937 := bstep (se 2 (by rfl) ⟨634101, by rfl⟩ : syracuseStep 1690937 = 1268203) B1268203
theorem B1953299 : Blo 750330 1953299 := bstep (se 1 (by rfl) ⟨1464974, by rfl⟩ : syracuseStep 1953299 = 2929949) B2929949
theorem B1691387 : Blo 750330 1691387 := bstep (se 1 (by rfl) ⟨1268540, by rfl⟩ : syracuseStep 1691387 = 2537081) B2537081
theorem B8573039 : Blo 750330 8573039 := bstep (se 1 (by rfl) ⟨6429779, by rfl⟩ : syracuseStep 8573039 = 12859559) B12859559
theorem B12210689 : Blo 750330 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B1692251 : Blo 750330 1692251 := bstep (se 1 (by rfl) ⟨1269188, by rfl⟩ : syracuseStep 1692251 = 2538377) B2538377
theorem B7524989 : Blo 750330 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B1692665 : Blo 750330 1692665 := bstep (se 2 (by rfl) ⟨634749, by rfl⟩ : syracuseStep 1692665 = 1269499) B1269499
theorem B1692809 : Blo 750330 1692809 := bstep (se 2 (by rfl) ⟨634803, by rfl⟩ : syracuseStep 1692809 = 1269607) B1269607
theorem B2415359 : Blo 750330 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B1694663 : Blo 750330 1694663 := bstep (se 1 (by rfl) ⟨1270997, by rfl⟩ : syracuseStep 1694663 = 2541995) B2541995
theorem B1695131 : Blo 750330 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B1695707 : Blo 750330 1695707 := bstep (se 1 (by rfl) ⟨1271780, by rfl⟩ : syracuseStep 1695707 = 2543561) B2543561
theorem B1695815 : Blo 750330 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B4285223 : Blo 750330 4285223 := bstep (se 1 (by rfl) ⟨3213917, by rfl⟩ : syracuseStep 4285223 = 6427835) B6427835
theorem B16245629 : Blo 750330 16245629 := bstep (se 3 (by rfl) ⟨3046055, by rfl⟩ : syracuseStep 16245629 = 6092111) B6092111
theorem B1271551 : Blo 750330 1271551 := bstep (se 1 (by rfl) ⟨953663, by rfl⟩ : syracuseStep 1271551 = 1907327) B1907327
theorem B846427 : Blo 750330 846427 := bstep (se 1 (by rfl) ⟨634820, by rfl⟩ : syracuseStep 846427 = 1269641) B1269641
theorem B6188123 : Blo 750330 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B13725065 : Blo 750330 13725065 := bstep (se 2 (by rfl) ⟨5146899, by rfl⟩ : syracuseStep 13725065 = 10293799) B10293799
theorem B848155 : Blo 750330 848155 := bstep (se 1 (by rfl) ⟨636116, by rfl⟩ : syracuseStep 848155 = 1272233) B1272233
theorem B5697863 : Blo 750330 5697863 := bstep (se 1 (by rfl) ⟨4273397, by rfl⟩ : syracuseStep 5697863 = 8546795) B8546795
theorem B7238423 : Blo 750330 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B750559 : Blo 750330 750559 := bstep (se 1 (by rfl) ⟨562919, by rfl⟩ : syracuseStep 750559 = 1125839) B1125839
theorem B750683 : Blo 750330 750683 := bstep (se 1 (by rfl) ⟨563012, by rfl⟩ : syracuseStep 750683 = 1126025) B1126025
theorem B750695 : Blo 750330 750695 := bstep (se 1 (by rfl) ⟨563021, by rfl⟩ : syracuseStep 750695 = 1126043) B1126043
theorem B3438055 : Blo 750330 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B751151 : Blo 750330 751151 := bstep (se 1 (by rfl) ⟨563363, by rfl⟩ : syracuseStep 751151 = 1126727) B1126727
theorem B751463 : Blo 750330 751463 := bstep (se 1 (by rfl) ⟨563597, by rfl⟩ : syracuseStep 751463 = 1127195) B1127195
theorem B751615 : Blo 750330 751615 := bstep (se 1 (by rfl) ⟨563711, by rfl⟩ : syracuseStep 751615 = 1127423) B1127423
theorem B751719 : Blo 750330 751719 := bstep (se 1 (by rfl) ⟨563789, by rfl⟩ : syracuseStep 751719 = 1127579) B1127579
theorem B751839 : Blo 750330 751839 := bstep (se 1 (by rfl) ⟨563879, by rfl⟩ : syracuseStep 751839 = 1127759) B1127759
theorem B752027 : Blo 750330 752027 := bstep (se 1 (by rfl) ⟨564020, by rfl⟩ : syracuseStep 752027 = 1128041) B1128041
theorem B752335 : Blo 750330 752335 := bstep (se 1 (by rfl) ⟨564251, by rfl⟩ : syracuseStep 752335 = 1128503) B1128503
theorem B7240427 : Blo 750330 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B752383 : Blo 750330 752383 := bstep (se 1 (by rfl) ⟨564287, by rfl⟩ : syracuseStep 752383 = 1128575) B1128575
theorem B752447 : Blo 750330 752447 := bstep (se 1 (by rfl) ⟨564335, by rfl⟩ : syracuseStep 752447 = 1128671) B1128671
theorem B752703 : Blo 750330 752703 := bstep (se 1 (by rfl) ⟨564527, by rfl⟩ : syracuseStep 752703 = 1129055) B1129055
theorem B752751 : Blo 750330 752751 := bstep (se 1 (by rfl) ⟨564563, by rfl⟩ : syracuseStep 752751 = 1129127) B1129127
theorem B752767 : Blo 750330 752767 := bstep (se 1 (by rfl) ⟨564575, by rfl⟩ : syracuseStep 752767 = 1129151) B1129151
theorem B752891 : Blo 750330 752891 := bstep (se 1 (by rfl) ⟨564668, by rfl⟩ : syracuseStep 752891 = 1129337) B1129337
theorem B753023 : Blo 750330 753023 := bstep (se 1 (by rfl) ⟨564767, by rfl⟩ : syracuseStep 753023 = 1129535) B1129535
theorem B753279 : Blo 750330 753279 := bstep (se 1 (by rfl) ⟨564959, by rfl⟩ : syracuseStep 753279 = 1129919) B1129919
theorem B1605703 : Blo 750330 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B753775 : Blo 750330 753775 := bstep (se 1 (by rfl) ⟨565331, by rfl⟩ : syracuseStep 753775 = 1130663) B1130663
theorem B1900705 : Blo 750330 1900705 := bstep (se 2 (by rfl) ⟨712764, by rfl⟩ : syracuseStep 1900705 = 1425529) B1425529
theorem B753887 : Blo 750330 753887 := bstep (se 1 (by rfl) ⟨565415, by rfl⟩ : syracuseStep 753887 = 1130831) B1130831
theorem B4292945 : Blo 750330 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B754023 : Blo 750330 754023 := bstep (se 1 (by rfl) ⟨565517, by rfl⟩ : syracuseStep 754023 = 1131035) B1131035
theorem B754175 : Blo 750330 754175 := bstep (se 1 (by rfl) ⟨565631, by rfl⟩ : syracuseStep 754175 = 1131263) B1131263
theorem B754223 : Blo 750330 754223 := bstep (se 1 (by rfl) ⟨565667, by rfl⟩ : syracuseStep 754223 = 1131335) B1131335
theorem B754303 : Blo 750330 754303 := bstep (se 1 (by rfl) ⟨565727, by rfl⟩ : syracuseStep 754303 = 1131455) B1131455
theorem B11011409 : Blo 750330 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B1083295 : Blo 750330 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B19302461 : Blo 750330 19302461 := bstep (se 3 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 19302461 = 7238423) B7238423
theorem B2033819 : Blo 750330 2033819 := bstep (se 1 (by rfl) ⟨1525364, by rfl⟩ : syracuseStep 2033819 = 3050729) B3050729
theorem B5016659 : Blo 750330 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B1903945 : Blo 750330 1903945 := bstep (se 2 (by rfl) ⟨713979, by rfl⟩ : syracuseStep 1903945 = 1427959) B1427959
theorem B49384997 : Blo 750330 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B2856815 : Blo 750330 2856815 := bstep (se 1 (by rfl) ⟨2142611, by rfl⟩ : syracuseStep 2856815 = 4285223) B4285223
theorem B3807323 : Blo 750330 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B312088727 : Blo 750330 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B1711583 : Blo 750330 1711583 := bstep (se 1 (by rfl) ⟨1283687, by rfl⟩ : syracuseStep 1711583 = 2567375) B2567375
theorem B9150043 : Blo 750330 9150043 := bstep (se 1 (by rfl) ⟨6862532, by rfl⟩ : syracuseStep 9150043 = 13725065) B13725065
theorem B1285769 : Blo 750330 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B3809591 : Blo 750330 3809591 := bstep (se 1 (by rfl) ⟨2857193, by rfl⟩ : syracuseStep 3809591 = 5714387) B5714387
theorem B3219983 : Blo 750330 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B4826951 : Blo 750330 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B3812507 : Blo 750330 3812507 := bstep (se 1 (by rfl) ⟨2859380, by rfl⟩ : syracuseStep 3812507 = 5718761) B5718761
theorem B2534813 : Blo 750330 2534813 := bstep (se 3 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 2534813 = 950555) B950555
theorem B18329179 : Blo 750330 18329179 := bstep (se 1 (by rfl) ⟨13746884, by rfl⟩ : syracuseStep 18329179 = 27493769) B27493769
theorem B16527091 : Blo 750330 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B2535623 : Blo 750330 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B2535839 : Blo 750330 2535839 := bstep (se 1 (by rfl) ⟨1901879, by rfl⟩ : syracuseStep 2535839 = 3803759) B3803759
theorem B1127291 : Blo 750330 1127291 := bstep (se 1 (by rfl) ⟨845468, by rfl⟩ : syracuseStep 1127291 = 1690937) B1690937
theorem B8565749 : Blo 750330 8565749 := bstep (se 5 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 8565749 = 803039) B803039
theorem B1127591 : Blo 750330 1127591 := bstep (se 1 (by rfl) ⟨845693, by rfl⟩ : syracuseStep 1127591 = 1691387) B1691387
theorem B2405659 : Blo 750330 2405659 := bstep (se 1 (by rfl) ⟨1804244, by rfl⟩ : syracuseStep 2405659 = 3608489) B3608489
theorem B5715359 : Blo 750330 5715359 := bstep (se 1 (by rfl) ⟨4286519, by rfl⟩ : syracuseStep 5715359 = 8573039) B8573039
theorem B23115223 : Blo 750330 23115223 := bstep (se 1 (by rfl) ⟨17336417, by rfl⟩ : syracuseStep 23115223 = 34672835) B34672835
theorem B8140459 : Blo 750330 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B1128167 : Blo 750330 1128167 := bstep (se 1 (by rfl) ⟨846125, by rfl⟩ : syracuseStep 1128167 = 1692251) B1692251
theorem B1128443 : Blo 750330 1128443 := bstep (se 1 (by rfl) ⟨846332, by rfl⟩ : syracuseStep 1128443 = 1692665) B1692665
theorem B1128539 : Blo 750330 1128539 := bstep (se 1 (by rfl) ⟨846404, by rfl⟩ : syracuseStep 1128539 = 1692809) B1692809
theorem B1128569 : Blo 750330 1128569 := bstep (se 2 (by rfl) ⟨423213, by rfl⟩ : syracuseStep 1128569 = 846427) B846427
theorem B2145163 : Blo 750330 2145163 := bstep (se 1 (by rfl) ⟨1608872, by rfl⟩ : syracuseStep 2145163 = 3217745) B3217745
theorem B1129775 : Blo 750330 1129775 := bstep (se 1 (by rfl) ⟨847331, by rfl⟩ : syracuseStep 1129775 = 1694663) B1694663
theorem B1130087 : Blo 750330 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1130471 : Blo 750330 1130471 := bstep (se 1 (by rfl) ⟨847853, by rfl⟩ : syracuseStep 1130471 = 1695707) B1695707
theorem B1130543 : Blo 750330 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B4571423 : Blo 750330 4571423 := bstep (se 1 (by rfl) ⟨3428567, by rfl⟩ : syracuseStep 4571423 = 6857135) B6857135
theorem B1130873 : Blo 750330 1130873 := bstep (se 2 (by rfl) ⟨424077, by rfl⟩ : syracuseStep 1130873 = 848155) B848155
theorem B17351111 : Blo 750330 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B10830419 : Blo 750330 10830419 := bstep (se 1 (by rfl) ⟨8122814, by rfl⟩ : syracuseStep 10830419 = 16245629) B16245629
theorem B188565077 : Blo 750330 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B1689335 : Blo 750330 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B6440957 : Blo 750330 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B1691423 : Blo 750330 1691423 := bstep (se 1 (by rfl) ⟨1268567, by rfl⟩ : syracuseStep 1691423 = 2537135) B2537135
theorem B1692287 : Blo 750330 1692287 := bstep (se 1 (by rfl) ⟨1269215, by rfl⟩ : syracuseStep 1692287 = 2538431) B2538431
theorem B6410987 : Blo 750330 6410987 := bstep (se 1 (by rfl) ⟨4808240, by rfl⟩ : syracuseStep 6410987 = 9616481) B9616481
theorem B4282307 : Blo 750330 4282307 := bstep (se 1 (by rfl) ⟨3211730, by rfl⟩ : syracuseStep 4282307 = 6423461) B6423461
theorem B33479153 : Blo 750330 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B1268507 : Blo 750330 1268507 := bstep (se 1 (by rfl) ⟨951380, by rfl⟩ : syracuseStep 1268507 = 1902761) B1902761
theorem B2284445 : Blo 750330 2284445 := bstep (se 3 (by rfl) ⟨428333, by rfl⟩ : syracuseStep 2284445 = 856667) B856667
theorem B1072063 : Blo 750330 1072063 := bstep (se 1 (by rfl) ⟨804047, by rfl⟩ : syracuseStep 1072063 = 1608095) B1608095
theorem B12213287 : Blo 750330 12213287 := bstep (se 1 (by rfl) ⟨9159965, by rfl⟩ : syracuseStep 12213287 = 18319931) B18319931
theorem B1695023 : Blo 750330 1695023 := bstep (se 1 (by rfl) ⟨1271267, by rfl⟩ : syracuseStep 1695023 = 2542535) B2542535
theorem B1695401 : Blo 750330 1695401 := bstep (se 2 (by rfl) ⟨635775, by rfl⟩ : syracuseStep 1695401 = 1271551) B1271551
theorem B1302199 : Blo 750330 1302199 := bstep (se 1 (by rfl) ⟨976649, by rfl⟩ : syracuseStep 1302199 = 1953299) B1953299
theorem B1269479 : Blo 750330 1269479 := bstep (se 1 (by rfl) ⟨952109, by rfl⟩ : syracuseStep 1269479 = 1904219) B1904219
theorem B2940809 : Blo 750330 2940809 := bstep (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) B2205607
theorem B1270255 : Blo 750330 1270255 := bstep (se 1 (by rfl) ⟨952691, by rfl⟩ : syracuseStep 1270255 = 1905383) B1905383
theorem B1270363 : Blo 750330 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B4811035 : Blo 750330 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B3303919 : Blo 750330 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B4584073 : Blo 750330 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B4125415 : Blo 750330 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B750623 : Blo 750330 750623 := bstep (se 1 (by rfl) ⟨562967, by rfl⟩ : syracuseStep 750623 = 1125935) B1125935
theorem B750823 : Blo 750330 750823 := bstep (se 1 (by rfl) ⟨563117, by rfl⟩ : syracuseStep 750823 = 1126235) B1126235
theorem B751135 : Blo 750330 751135 := bstep (se 1 (by rfl) ⟨563351, by rfl⟩ : syracuseStep 751135 = 1126703) B1126703
theorem B3798575 : Blo 750330 3798575 := bstep (se 1 (by rfl) ⟨2848931, by rfl⟩ : syracuseStep 3798575 = 5697863) B5697863
theorem B751335 : Blo 750330 751335 := bstep (se 1 (by rfl) ⟨563501, by rfl⟩ : syracuseStep 751335 = 1127003) B1127003
theorem B751935 : Blo 750330 751935 := bstep (se 1 (by rfl) ⟨563951, by rfl⟩ : syracuseStep 751935 = 1127903) B1127903
theorem B752319 : Blo 750330 752319 := bstep (se 1 (by rfl) ⟨564239, by rfl⟩ : syracuseStep 752319 = 1128479) B1128479
theorem B752487 : Blo 750330 752487 := bstep (se 1 (by rfl) ⟨564365, by rfl⟩ : syracuseStep 752487 = 1128731) B1128731
theorem B752575 : Blo 750330 752575 := bstep (se 1 (by rfl) ⟨564431, by rfl⟩ : syracuseStep 752575 = 1128863) B1128863
theorem B752959 : Blo 750330 752959 := bstep (se 1 (by rfl) ⟨564719, by rfl⟩ : syracuseStep 752959 = 1129439) B1129439
theorem B16482203 : Blo 750330 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B753695 : Blo 750330 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B3047615 : Blo 750330 3047615 := bstep (se 1 (by rfl) ⟨2285711, by rfl⟩ : syracuseStep 3047615 = 4571423) B4571423
theorem B753915 : Blo 750330 753915 := bstep (se 1 (by rfl) ⟨565436, by rfl⟩ : syracuseStep 753915 = 1130873) B1130873
theorem B53511029 : Blo 750330 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B7340939 : Blo 750330 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B46269629 : Blo 750330 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B4293971 : Blo 750330 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B1904543 : Blo 750330 1904543 := bstep (se 1 (by rfl) ⟨1428407, by rfl⟩ : syracuseStep 1904543 = 2856815) B2856815
theorem B2854871 : Blo 750330 2854871 := bstep (se 1 (by rfl) ⟨2141153, by rfl⟩ : syracuseStep 2854871 = 4282307) B4282307
theorem B22319435 : Blo 750330 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B857179 : Blo 750330 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B3217967 : Blo 750330 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B10853945 : Blo 750330 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B5710499 : Blo 750330 5710499 := bstep (se 1 (by rfl) ⟨4282874, by rfl⟩ : syracuseStep 5710499 = 8565749) B8565749
theorem B3810239 : Blo 750330 3810239 := bstep (se 1 (by rfl) ⟨2857679, by rfl⟩ : syracuseStep 3810239 = 5715359) B5715359
theorem B2532383 : Blo 750330 2532383 := bstep (se 1 (by rfl) ⟨1899287, by rfl⟩ : syracuseStep 2532383 = 3798575) B3798575
theorem B2860217 : Blo 750330 2860217 := bstep (se 2 (by rfl) ⟨1072581, by rfl⟩ : syracuseStep 2860217 = 2145163) B2145163
theorem B31368629 : Blo 750330 31368629 := bstep (se 5 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 31368629 = 2940809) B2940809
theorem B12200057 : Blo 750330 12200057 := bstep (se 2 (by rfl) ⟨4575021, by rfl⟩ : syracuseStep 12200057 = 9150043) B9150043
theorem B5777573 : Blo 750330 5777573 := bstep (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) B1083295
theorem B10988135 : Blo 750330 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B2140937 : Blo 750330 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B2534273 : Blo 750330 2534273 := bstep (se 2 (by rfl) ⟨950352, by rfl⟩ : syracuseStep 2534273 = 1900705) B1900705
theorem B2861963 : Blo 750330 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B7220279 : Blo 750330 7220279 := bstep (se 1 (by rfl) ⟨5415209, by rfl⟩ : syracuseStep 7220279 = 10830419) B10830419
theorem B125710051 : Blo 750330 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B1126223 : Blo 750330 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B1355879 : Blo 750330 1355879 := bstep (se 1 (by rfl) ⟨1016909, by rfl⟩ : syracuseStep 1355879 = 2033819) B2033819
theorem B1127615 : Blo 750330 1127615 := bstep (se 1 (by rfl) ⟨845711, by rfl⟩ : syracuseStep 1127615 = 1691423) B1691423
theorem B1128191 : Blo 750330 1128191 := bstep (se 1 (by rfl) ⟨846143, by rfl⟩ : syracuseStep 1128191 = 1692287) B1692287
theorem B4273991 : Blo 750330 4273991 := bstep (se 1 (by rfl) ⟨3205493, by rfl⟩ : syracuseStep 4273991 = 6410987) B6410987
theorem B2538215 : Blo 750330 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B2538593 : Blo 750330 2538593 := bstep (se 2 (by rfl) ⟨951972, by rfl⟩ : syracuseStep 2538593 = 1903945) B1903945
theorem B1522963 : Blo 750330 1522963 := bstep (se 1 (by rfl) ⟨1142222, by rfl⟩ : syracuseStep 1522963 = 2284445) B2284445
theorem B8142191 : Blo 750330 8142191 := bstep (se 1 (by rfl) ⟨6106643, by rfl⟩ : syracuseStep 8142191 = 12213287) B12213287
theorem B1130015 : Blo 750330 1130015 := bstep (se 1 (by rfl) ⟨847511, by rfl⟩ : syracuseStep 1130015 = 1695023) B1695023
theorem B22036121 : Blo 750330 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B1130267 : Blo 750330 1130267 := bstep (se 1 (by rfl) ⟨847700, by rfl⟩ : syracuseStep 1130267 = 1695401) B1695401
theorem B2539727 : Blo 750330 2539727 := bstep (se 1 (by rfl) ⟨1904795, by rfl⟩ : syracuseStep 2539727 = 3809591) B3809591
theorem B2146655 : Blo 750330 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B6112097 : Blo 750330 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B30820297 : Blo 750330 30820297 := bstep (se 2 (by rfl) ⟨11557611, by rfl⟩ : syracuseStep 30820297 = 23115223) B23115223
theorem B2541671 : Blo 750330 2541671 := bstep (se 1 (by rfl) ⟨1906253, by rfl⟩ : syracuseStep 2541671 = 3812507) B3812507
theorem B1689875 : Blo 750330 1689875 := bstep (se 1 (by rfl) ⟨1267406, by rfl⟩ : syracuseStep 1689875 = 2534813) B2534813
theorem B1690415 : Blo 750330 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B1690559 : Blo 750330 1690559 := bstep (se 1 (by rfl) ⟨1267919, by rfl⟩ : syracuseStep 1690559 = 2535839) B2535839
theorem B1429417 : Blo 750330 1429417 := bstep (se 2 (by rfl) ⟨536031, by rfl⟩ : syracuseStep 1429417 = 1072063) B1072063
theorem B1693673 : Blo 750330 1693673 := bstep (se 2 (by rfl) ⟨635127, by rfl⟩ : syracuseStep 1693673 = 1270255) B1270255
theorem B1693817 : Blo 750330 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B12868307 : Blo 750330 12868307 := bstep (se 1 (by rfl) ⟨9651230, by rfl⟩ : syracuseStep 12868307 = 19302461) B19302461
theorem B32923331 : Blo 750330 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B17620901 : Blo 750330 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B6414713 : Blo 750330 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B27780245 : Blo 750330 27780245 := bstep (se 6 (by rfl) ⟨651099, by rfl⟩ : syracuseStep 27780245 = 1302199) B1302199
theorem B845671 : Blo 750330 845671 := bstep (se 1 (by rfl) ⟨634253, by rfl⟩ : syracuseStep 845671 = 1268507) B1268507
theorem B24438905 : Blo 750330 24438905 := bstep (se 2 (by rfl) ⟨9164589, by rfl⟩ : syracuseStep 24438905 = 18329179) B18329179
theorem B1141055 : Blo 750330 1141055 := bstep (se 1 (by rfl) ⟨855791, by rfl⟩ : syracuseStep 1141055 = 1711583) B1711583
theorem B846319 : Blo 750330 846319 := bstep (se 1 (by rfl) ⟨634739, by rfl⟩ : syracuseStep 846319 = 1269479) B1269479
theorem B832236605 : Blo 750330 832236605 := bstep (se 3 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 832236605 = 312088727) B312088727
theorem B5500553 : Blo 750330 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B3207545 : Blo 750330 3207545 := bstep (se 2 (by rfl) ⟨1202829, by rfl⟩ : syracuseStep 3207545 = 2405659) B2405659
theorem B751527 : Blo 750330 751527 := bstep (se 1 (by rfl) ⟨563645, by rfl⟩ : syracuseStep 751527 = 1127291) B1127291
theorem B751727 : Blo 750330 751727 := bstep (se 1 (by rfl) ⟨563795, by rfl⟩ : syracuseStep 751727 = 1127591) B1127591
theorem B752111 : Blo 750330 752111 := bstep (se 1 (by rfl) ⟨564083, by rfl⟩ : syracuseStep 752111 = 1128167) B1128167
theorem B752295 : Blo 750330 752295 := bstep (se 1 (by rfl) ⟨564221, by rfl⟩ : syracuseStep 752295 = 1128443) B1128443
theorem B752359 : Blo 750330 752359 := bstep (se 1 (by rfl) ⟨564269, by rfl⟩ : syracuseStep 752359 = 1128539) B1128539
theorem B752379 : Blo 750330 752379 := bstep (se 1 (by rfl) ⟨564284, by rfl⟩ : syracuseStep 752379 = 1128569) B1128569
theorem B753183 : Blo 750330 753183 := bstep (se 1 (by rfl) ⟨564887, by rfl⟩ : syracuseStep 753183 = 1129775) B1129775
theorem B753391 : Blo 750330 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B753647 : Blo 750330 753647 := bstep (se 1 (by rfl) ⟨565235, by rfl⟩ : syracuseStep 753647 = 1130471) B1130471
theorem B2031743 : Blo 750330 2031743 := bstep (se 1 (by rfl) ⟨1523807, by rfl⟩ : syracuseStep 2031743 = 3047615) B3047615
theorem B41093729 : Blo 750330 41093729 := bstep (se 2 (by rfl) ⟨15410148, by rfl⟩ : syracuseStep 41093729 = 30820297) B30820297
theorem B1903247 : Blo 750330 1903247 := bstep (se 1 (by rfl) ⟨1427435, by rfl⟩ : syracuseStep 1903247 = 2854871) B2854871
theorem B14879623 : Blo 750330 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B167613401 : Blo 750330 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B1905889 : Blo 750330 1905889 := bstep (se 2 (by rfl) ⟨714708, by rfl⟩ : syracuseStep 1905889 = 1429417) B1429417
theorem B15406861 : Blo 750330 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B3806999 : Blo 750330 3806999 := bstep (se 1 (by rfl) ⟨2855249, by rfl⟩ : syracuseStep 3806999 = 5710499) B5710499
theorem B18520163 : Blo 750330 18520163 := bstep (se 1 (by rfl) ⟨13890122, by rfl⟩ : syracuseStep 18520163 = 27780245) B27780245
theorem B1906811 : Blo 750330 1906811 := bstep (se 1 (by rfl) ⟨1430108, by rfl⟩ : syracuseStep 1906811 = 2860217) B2860217
theorem B20912419 : Blo 750330 20912419 := bstep (se 1 (by rfl) ⟨15684314, by rfl⟩ : syracuseStep 20912419 = 31368629) B31368629
theorem B8133371 : Blo 750330 8133371 := bstep (se 1 (by rfl) ⟨6100028, by rfl⟩ : syracuseStep 8133371 = 12200057) B12200057
theorem B16292603 : Blo 750330 16292603 := bstep (se 1 (by rfl) ⟨12219452, by rfl⟩ : syracuseStep 16292603 = 24438905) B24438905
theorem B760703 : Blo 750330 760703 := bstep (se 1 (by rfl) ⟨570527, by rfl⟩ : syracuseStep 760703 = 1141055) B1141055
theorem B1907975 : Blo 750330 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B2138363 : Blo 750330 2138363 := bstep (se 1 (by rfl) ⟨1603772, by rfl⟩ : syracuseStep 2138363 = 3207545) B3207545
theorem B14690747 : Blo 750330 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B3615677 : Blo 750330 3615677 := bstep (se 3 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 3615677 = 1355879) B1355879
theorem B4074731 : Blo 750330 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B4893959 : Blo 750330 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B30846419 : Blo 750330 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B2862647 : Blo 750330 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B1126583 : Blo 750330 1126583 := bstep (se 1 (by rfl) ⟨844937, by rfl⟩ : syracuseStep 1126583 = 1689875) B1689875
theorem B1126943 : Blo 750330 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B1127039 : Blo 750330 1127039 := bstep (se 1 (by rfl) ⟨845279, by rfl⟩ : syracuseStep 1127039 = 1690559) B1690559
theorem B1127561 : Blo 750330 1127561 := bstep (se 2 (by rfl) ⟨422835, by rfl⟩ : syracuseStep 1127561 = 845671) B845671
theorem B1128425 : Blo 750330 1128425 := bstep (se 2 (by rfl) ⟨423159, by rfl⟩ : syracuseStep 1128425 = 846319) B846319
theorem B1129115 : Blo 750330 1129115 := bstep (se 1 (by rfl) ⟨846836, by rfl⟩ : syracuseStep 1129115 = 1693673) B1693673
theorem B1129211 : Blo 750330 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B2145311 : Blo 750330 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B11747267 : Blo 750330 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B4276475 : Blo 750330 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B2540159 : Blo 750330 2540159 := bstep (se 1 (by rfl) ⟨1905119, by rfl⟩ : syracuseStep 2540159 = 3810239) B3810239
theorem B1688255 : Blo 750330 1688255 := bstep (se 1 (by rfl) ⟨1266191, by rfl⟩ : syracuseStep 1688255 = 2532383) B2532383
theorem B7325423 : Blo 750330 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B1427291 : Blo 750330 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B1689515 : Blo 750330 1689515 := bstep (se 1 (by rfl) ⟨1267136, by rfl⟩ : syracuseStep 1689515 = 2534273) B2534273
theorem B14668141 : Blo 750330 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B1692143 : Blo 750330 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B1692395 : Blo 750330 1692395 := bstep (se 1 (by rfl) ⟨1269296, by rfl⟩ : syracuseStep 1692395 = 2538593) B2538593
theorem B5428127 : Blo 750330 5428127 := bstep (se 1 (by rfl) ⟨4071095, by rfl⟩ : syracuseStep 5428127 = 8142191) B8142191
theorem B1693151 : Blo 750330 1693151 := bstep (se 1 (by rfl) ⟨1269863, by rfl⟩ : syracuseStep 1693151 = 2539727) B2539727
theorem B1431103 : Blo 750330 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B35674019 : Blo 750330 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B1694447 : Blo 750330 1694447 := bstep (se 1 (by rfl) ⟨1270835, by rfl⟩ : syracuseStep 1694447 = 2541671) B2541671
theorem B1269695 : Blo 750330 1269695 := bstep (se 1 (by rfl) ⟨952271, by rfl⟩ : syracuseStep 1269695 = 1904543) B1904543
theorem B8578871 : Blo 750330 8578871 := bstep (se 1 (by rfl) ⟨6434153, by rfl⟩ : syracuseStep 8578871 = 12868307) B12868307
theorem B7235963 : Blo 750330 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B21948887 : Blo 750330 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B1142905 : Blo 750330 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B4813519 : Blo 750330 4813519 := bstep (se 1 (by rfl) ⟨3610139, by rfl⟩ : syracuseStep 4813519 = 7220279) B7220279
theorem B554824403 : Blo 750330 554824403 := bstep (se 1 (by rfl) ⟨416118302, by rfl⟩ : syracuseStep 554824403 = 832236605) B832236605
theorem B750815 : Blo 750330 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B751743 : Blo 750330 751743 := bstep (se 1 (by rfl) ⟨563807, by rfl⟩ : syracuseStep 751743 = 1127615) B1127615
theorem B752127 : Blo 750330 752127 := bstep (se 1 (by rfl) ⟨564095, by rfl⟩ : syracuseStep 752127 = 1128191) B1128191
theorem B2849327 : Blo 750330 2849327 := bstep (se 1 (by rfl) ⟨2136995, by rfl⟩ : syracuseStep 2849327 = 4273991) B4273991
theorem B2030617 : Blo 750330 2030617 := bstep (se 2 (by rfl) ⟨761481, by rfl⟩ : syracuseStep 2030617 = 1522963) B1522963
theorem B753343 : Blo 750330 753343 := bstep (se 1 (by rfl) ⟨565007, by rfl⟩ : syracuseStep 753343 = 1130015) B1130015
theorem B753511 : Blo 750330 753511 := bstep (se 1 (by rfl) ⟨565133, by rfl⟩ : syracuseStep 753511 = 1130267) B1130267
theorem B2850983 : Blo 750330 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B4883615 : Blo 750330 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B951527 : Blo 750330 951527 := bstep (se 1 (by rfl) ⟨713645, by rfl⟩ : syracuseStep 951527 = 1427291) B1427291
theorem B27395819 : Blo 750330 27395819 := bstep (se 1 (by rfl) ⟨20546864, by rfl⟩ : syracuseStep 27395819 = 41093729) B41093729
theorem B111742267 : Blo 750330 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B4823975 : Blo 750330 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B1908137 : Blo 750330 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B1908431 : Blo 750330 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B1354495 : Blo 750330 1354495 := bstep (se 1 (by rfl) ⟨1015871, by rfl⟩ : syracuseStep 1354495 = 2031743) B2031743
theorem B1125503 : Blo 750330 1125503 := bstep (se 1 (by rfl) ⟨844127, by rfl⟩ : syracuseStep 1125503 = 1688255) B1688255
theorem B1126343 : Blo 750330 1126343 := bstep (se 1 (by rfl) ⟨844757, by rfl⟩ : syracuseStep 1126343 = 1689515) B1689515
theorem B1128095 : Blo 750330 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1128263 : Blo 750330 1128263 := bstep (se 1 (by rfl) ⟨846197, by rfl⟩ : syracuseStep 1128263 = 1692395) B1692395
theorem B3618751 : Blo 750330 3618751 := bstep (se 1 (by rfl) ⟨2714063, by rfl⟩ : syracuseStep 3618751 = 5428127) B5428127
theorem B1128767 : Blo 750330 1128767 := bstep (se 1 (by rfl) ⟨846575, by rfl⟩ : syracuseStep 1128767 = 1693151) B1693151
theorem B19839497 : Blo 750330 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B2537999 : Blo 750330 2537999 := bstep (se 1 (by rfl) ⟨1903499, by rfl⟩ : syracuseStep 2537999 = 3806999) B3806999
theorem B1129631 : Blo 750330 1129631 := bstep (se 1 (by rfl) ⟨847223, by rfl⟩ : syracuseStep 1129631 = 1694447) B1694447
theorem B5422247 : Blo 750330 5422247 := bstep (se 1 (by rfl) ⟨4066685, by rfl⟩ : syracuseStep 5422247 = 8133371) B8133371
theorem B10861735 : Blo 750330 10861735 := bstep (se 1 (by rfl) ⟨8146301, by rfl⟩ : syracuseStep 10861735 = 16292603) B16292603
theorem B1523873 : Blo 750330 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B1425575 : Blo 750330 1425575 := bstep (se 1 (by rfl) ⟨1069181, by rfl⟩ : syracuseStep 1425575 = 2138363) B2138363
theorem B5719247 : Blo 750330 5719247 := bstep (se 1 (by rfl) ⟨4289435, by rfl⟩ : syracuseStep 5719247 = 8578871) B8578871
theorem B2541185 : Blo 750330 2541185 := bstep (se 2 (by rfl) ⟨952944, by rfl⟩ : syracuseStep 2541185 = 1905889) B1905889
theorem B14632591 : Blo 750330 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B2410451 : Blo 750330 2410451 := bstep (se 1 (by rfl) ⟨1807838, by rfl⟩ : syracuseStep 2410451 = 3615677) B3615677
theorem B3262639 : Blo 750330 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B20564279 : Blo 750330 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B8114165 : Blo 750330 8114165 := bstep (se 5 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 8114165 = 760703) B760703
theorem B2707489 : Blo 750330 2707489 := bstep (se 2 (by rfl) ⟨1015308, by rfl⟩ : syracuseStep 2707489 = 2030617) B2030617
theorem B1430207 : Blo 750330 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B1693439 : Blo 750330 1693439 := bstep (se 1 (by rfl) ⟨1270079, by rfl⟩ : syracuseStep 1693439 = 2540159) B2540159
theorem B1268831 : Blo 750330 1268831 := bstep (se 1 (by rfl) ⟨951623, by rfl⟩ : syracuseStep 1268831 = 1903247) B1903247
theorem B23782679 : Blo 750330 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B12346775 : Blo 750330 12346775 := bstep (se 1 (by rfl) ⟨9260081, by rfl⟩ : syracuseStep 12346775 = 18520163) B18520163
theorem B1271207 : Blo 750330 1271207 := bstep (se 1 (by rfl) ⟨953405, by rfl⟩ : syracuseStep 1271207 = 1906811) B1906811
theorem B1271983 : Blo 750330 1271983 := bstep (se 1 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 1271983 = 1907975) B1907975
theorem B846463 : Blo 750330 846463 := bstep (se 1 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 846463 = 1269695) B1269695
theorem B19557521 : Blo 750330 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B6418025 : Blo 750330 6418025 := bstep (se 2 (by rfl) ⟨2406759, by rfl⟩ : syracuseStep 6418025 = 4813519) B4813519
theorem B9793831 : Blo 750330 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B2716487 : Blo 750330 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B20542481 : Blo 750330 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B751055 : Blo 750330 751055 := bstep (se 1 (by rfl) ⟨563291, by rfl⟩ : syracuseStep 751055 = 1126583) B1126583
theorem B751295 : Blo 750330 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B27883225 : Blo 750330 27883225 := bstep (se 2 (by rfl) ⟨10456209, by rfl⟩ : syracuseStep 27883225 = 20912419) B20912419
theorem B751359 : Blo 750330 751359 := bstep (se 1 (by rfl) ⟨563519, by rfl⟩ : syracuseStep 751359 = 1127039) B1127039
theorem B369882935 : Blo 750330 369882935 := bstep (se 1 (by rfl) ⟨277412201, by rfl⟩ : syracuseStep 369882935 = 554824403) B554824403
theorem B751707 : Blo 750330 751707 := bstep (se 1 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 751707 = 1127561) B1127561
theorem B752283 : Blo 750330 752283 := bstep (se 1 (by rfl) ⟨564212, by rfl⟩ : syracuseStep 752283 = 1128425) B1128425
theorem B1899551 : Blo 750330 1899551 := bstep (se 1 (by rfl) ⟨1424663, by rfl⟩ : syracuseStep 1899551 = 2849327) B2849327
theorem B752743 : Blo 750330 752743 := bstep (se 1 (by rfl) ⟨564557, by rfl⟩ : syracuseStep 752743 = 1129115) B1129115
theorem B752807 : Blo 750330 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B7831511 : Blo 750330 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B1015915 : Blo 750330 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B1900655 : Blo 750330 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B950383 : Blo 750330 950383 := bstep (se 1 (by rfl) ⟨712787, by rfl⟩ : syracuseStep 950383 = 1425575) B1425575
theorem B1606967 : Blo 750330 1606967 := bstep (se 1 (by rfl) ⟨1205225, by rfl⟩ : syracuseStep 1606967 = 2410451) B2410451
theorem B5409443 : Blo 750330 5409443 := bstep (se 1 (by rfl) ⟨4057082, by rfl⟩ : syracuseStep 5409443 = 8114165) B8114165
theorem B953471 : Blo 750330 953471 := bstep (se 1 (by rfl) ⟨715103, by rfl⟩ : syracuseStep 953471 = 1430207) B1430207
theorem B1805993 : Blo 750330 1805993 := bstep (se 2 (by rfl) ⟨677247, by rfl⟩ : syracuseStep 1805993 = 1354495) B1354495
theorem B8231183 : Blo 750330 8231183 := bstep (se 1 (by rfl) ⟨6173387, by rfl⟩ : syracuseStep 8231183 = 12346775) B12346775
theorem B4825001 : Blo 750330 4825001 := bstep (se 2 (by rfl) ⟨1809375, by rfl⟩ : syracuseStep 4825001 = 3618751) B3618751
theorem B1810991 : Blo 750330 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B246588623 : Blo 750330 246588623 := bstep (se 1 (by rfl) ⟨184941467, by rfl⟩ : syracuseStep 246588623 = 369882935) B369882935
theorem B3614831 : Blo 750330 3614831 := bstep (se 1 (by rfl) ⟨2711123, by rfl⟩ : syracuseStep 3614831 = 5422247) B5422247
theorem B5221007 : Blo 750330 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B3255743 : Blo 750330 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B3812831 : Blo 750330 3812831 := bstep (se 1 (by rfl) ⟨2859623, by rfl⟩ : syracuseStep 3812831 = 5719247) B5719247
theorem B18263879 : Blo 750330 18263879 := bstep (se 1 (by rfl) ⟨13697909, by rfl⟩ : syracuseStep 18263879 = 27395819) B27395819
theorem B13709519 : Blo 750330 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B19510121 : Blo 750330 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B2537405 : Blo 750330 2537405 := bstep (se 3 (by rfl) ⟨475763, by rfl⟩ : syracuseStep 2537405 = 951527) B951527
theorem B1128617 : Blo 750330 1128617 := bstep (se 2 (by rfl) ⟨423231, by rfl⟩ : syracuseStep 1128617 = 846463) B846463
theorem B1128959 : Blo 750330 1128959 := bstep (se 1 (by rfl) ⟨846719, by rfl⟩ : syracuseStep 1128959 = 1693439) B1693439
theorem B13058441 : Blo 750330 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B52905325 : Blo 750330 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B37177633 : Blo 750330 37177633 := bstep (se 2 (by rfl) ⟨13941612, by rfl⟩ : syracuseStep 37177633 = 27883225) B27883225
theorem B4278683 : Blo 750330 4278683 := bstep (se 1 (by rfl) ⟨3209012, by rfl⟩ : syracuseStep 4278683 = 6418025) B6418025
theorem B12863933 : Blo 750330 12863933 := bstep (se 3 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 12863933 = 4823975) B4823975
theorem B1691999 : Blo 750330 1691999 := bstep (se 1 (by rfl) ⟨1268999, by rfl⟩ : syracuseStep 1691999 = 2537999) B2537999
theorem B1266367 : Blo 750330 1266367 := bstep (se 1 (by rfl) ⟨949775, by rfl⟩ : syracuseStep 1266367 = 1899551) B1899551
theorem B14439941 : Blo 750330 14439941 := bstep (se 4 (by rfl) ⟨1353744, by rfl⟩ : syracuseStep 14439941 = 2707489) B2707489
theorem B1694123 : Blo 750330 1694123 := bstep (se 1 (by rfl) ⟨1270592, by rfl⟩ : syracuseStep 1694123 = 2541185) B2541185
theorem B4350185 : Blo 750330 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B1695977 : Blo 750330 1695977 := bstep (se 2 (by rfl) ⟨635991, by rfl⟩ : syracuseStep 1695977 = 1271983) B1271983
theorem B148989689 : Blo 750330 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B845887 : Blo 750330 845887 := bstep (se 1 (by rfl) ⟨634415, by rfl⟩ : syracuseStep 845887 = 1268831) B1268831
theorem B1272091 : Blo 750330 1272091 := bstep (se 1 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 1272091 = 1908137) B1908137
theorem B1272287 : Blo 750330 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B15855119 : Blo 750330 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B847471 : Blo 750330 847471 := bstep (se 1 (by rfl) ⟨635603, by rfl⟩ : syracuseStep 847471 = 1271207) B1271207
theorem B750335 : Blo 750330 750335 := bstep (se 1 (by rfl) ⟨562751, by rfl⟩ : syracuseStep 750335 = 1125503) B1125503
theorem B13038347 : Blo 750330 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B750895 : Blo 750330 750895 := bstep (se 1 (by rfl) ⟨563171, by rfl⟩ : syracuseStep 750895 = 1126343) B1126343
theorem B13694987 : Blo 750330 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B752063 : Blo 750330 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B752175 : Blo 750330 752175 := bstep (se 1 (by rfl) ⟨564131, by rfl⟩ : syracuseStep 752175 = 1128263) B1128263
theorem B752511 : Blo 750330 752511 := bstep (se 1 (by rfl) ⟨564383, by rfl⟩ : syracuseStep 752511 = 1128767) B1128767
theorem B14482313 : Blo 750330 14482313 := bstep (se 2 (by rfl) ⟨5430867, by rfl⟩ : syracuseStep 14482313 = 10861735) B10861735
theorem B753087 : Blo 750330 753087 := bstep (se 1 (by rfl) ⟨564815, by rfl⟩ : syracuseStep 753087 = 1129631) B1129631
theorem B2852455 : Blo 750330 2852455 := bstep (se 1 (by rfl) ⟨2139341, by rfl⟩ : syracuseStep 2852455 = 4278683) B4278683
theorem B3606295 : Blo 750330 3606295 := bstep (se 1 (by rfl) ⟨2704721, by rfl⟩ : syracuseStep 3606295 = 5409443) B5409443
theorem B3216667 : Blo 750330 3216667 := bstep (se 1 (by rfl) ⟨2412500, by rfl⟩ : syracuseStep 3216667 = 4825001) B4825001
theorem B99326459 : Blo 750330 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B3480671 : Blo 750330 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B2170495 : Blo 750330 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B8692231 : Blo 750330 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B1354553 : Blo 750330 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B1127849 : Blo 750330 1127849 := bstep (se 2 (by rfl) ⟨422943, by rfl⟩ : syracuseStep 1127849 = 845887) B845887
theorem B1127999 : Blo 750330 1127999 := bstep (se 1 (by rfl) ⟨845999, by rfl⟩ : syracuseStep 1127999 = 1691999) B1691999
theorem B5487455 : Blo 750330 5487455 := bstep (se 1 (by rfl) ⟨4115591, by rfl⟩ : syracuseStep 5487455 = 8231183) B8231183
theorem B1129415 : Blo 750330 1129415 := bstep (se 1 (by rfl) ⟨847061, by rfl⟩ : syracuseStep 1129415 = 1694123) B1694123
theorem B1129961 : Blo 750330 1129961 := bstep (se 2 (by rfl) ⟨423735, by rfl⟩ : syracuseStep 1129961 = 847471) B847471
theorem B2900123 : Blo 750330 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B1130651 : Blo 750330 1130651 := bstep (se 1 (by rfl) ⟨847988, by rfl⟩ : syracuseStep 1130651 = 1695977) B1695977
theorem B1688489 : Blo 750330 1688489 := bstep (se 2 (by rfl) ⟨633183, by rfl⟩ : syracuseStep 1688489 = 1266367) B1266367
theorem B2409887 : Blo 750330 2409887 := bstep (se 1 (by rfl) ⟨1807415, by rfl⟩ : syracuseStep 2409887 = 3614831) B3614831
theorem B2541887 : Blo 750330 2541887 := bstep (se 1 (by rfl) ⟨1906415, by rfl⟩ : syracuseStep 2541887 = 3812831) B3812831
theorem B10570079 : Blo 750330 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B12175919 : Blo 750330 12175919 := bstep (se 1 (by rfl) ⟨9131939, by rfl⟩ : syracuseStep 12175919 = 18263879) B18263879
theorem B2542589 : Blo 750330 2542589 := bstep (se 3 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 2542589 = 953471) B953471
theorem B1691603 : Blo 750330 1691603 := bstep (se 1 (by rfl) ⟨1268702, by rfl⟩ : syracuseStep 1691603 = 2537405) B2537405
theorem B9129991 : Blo 750330 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B9654875 : Blo 750330 9654875 := bstep (se 1 (by rfl) ⟨7241156, by rfl⟩ : syracuseStep 9654875 = 14482313) B14482313
theorem B1267103 : Blo 750330 1267103 := bstep (se 1 (by rfl) ⟨950327, by rfl⟩ : syracuseStep 1267103 = 1900655) B1900655
theorem B1267177 : Blo 750330 1267177 := bstep (se 2 (by rfl) ⟨475191, by rfl⟩ : syracuseStep 1267177 = 950383) B950383
theorem B8705627 : Blo 750330 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B1071311 : Blo 750330 1071311 := bstep (se 1 (by rfl) ⟨803483, by rfl⟩ : syracuseStep 1071311 = 1606967) B1606967
theorem B8575955 : Blo 750330 8575955 := bstep (se 1 (by rfl) ⟨6431966, by rfl⟩ : syracuseStep 8575955 = 12863933) B12863933
theorem B70540433 : Blo 750330 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B1203995 : Blo 750330 1203995 := bstep (se 1 (by rfl) ⟨902996, by rfl⟩ : syracuseStep 1203995 = 1805993) B1805993
theorem B1696121 : Blo 750330 1696121 := bstep (se 2 (by rfl) ⟨636045, by rfl⟩ : syracuseStep 1696121 = 1272091) B1272091
theorem B49570177 : Blo 750330 49570177 := bstep (se 2 (by rfl) ⟨18588816, by rfl⟩ : syracuseStep 49570177 = 37177633) B37177633
theorem B9626627 : Blo 750330 9626627 := bstep (se 1 (by rfl) ⟨7219970, by rfl⟩ : syracuseStep 9626627 = 14439941) B14439941
theorem B1207327 : Blo 750330 1207327 := bstep (se 1 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 1207327 = 1810991) B1810991
theorem B164392415 : Blo 750330 164392415 := bstep (se 1 (by rfl) ⟨123294311, by rfl⟩ : syracuseStep 164392415 = 246588623) B246588623
theorem B848191 : Blo 750330 848191 := bstep (se 1 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 848191 = 1272287) B1272287
theorem B9139679 : Blo 750330 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B13006747 : Blo 750330 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B752411 : Blo 750330 752411 := bstep (se 1 (by rfl) ⟨564308, by rfl⟩ : syracuseStep 752411 = 1128617) B1128617
theorem B752639 : Blo 750330 752639 := bstep (se 1 (by rfl) ⟨564479, by rfl⟩ : syracuseStep 752639 = 1128959) B1128959
theorem B1933415 : Blo 750330 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B753767 : Blo 750330 753767 := bstep (se 1 (by rfl) ⟨565325, by rfl⟩ : syracuseStep 753767 = 1130651) B1130651
theorem B66093569 : Blo 750330 66093569 := bstep (se 2 (by rfl) ⟨24785088, by rfl⟩ : syracuseStep 66093569 = 49570177) B49570177
theorem B1606591 : Blo 750330 1606591 := bstep (se 1 (by rfl) ⟨1204943, by rfl⟩ : syracuseStep 1606591 = 2409887) B2409887
theorem B7046719 : Blo 750330 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B3803273 : Blo 750330 3803273 := bstep (se 2 (by rfl) ⟨1426227, by rfl⟩ : syracuseStep 3803273 = 2852455) B2852455
theorem B5803751 : Blo 750330 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B1609769 : Blo 750330 1609769 := bstep (se 2 (by rfl) ⟨603663, by rfl⟩ : syracuseStep 1609769 = 1207327) B1207327
theorem B47026955 : Blo 750330 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B2856829 : Blo 750330 2856829 := bstep (se 3 (by rfl) ⟨535655, by rfl⟩ : syracuseStep 2856829 = 1071311) B1071311
theorem B264870557 : Blo 750330 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B9281789 : Blo 750330 9281789 := bstep (se 3 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 9281789 = 3480671) B3480671
theorem B11575973 : Blo 750330 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B1125659 : Blo 750330 1125659 := bstep (se 1 (by rfl) ⟨844244, by rfl⟩ : syracuseStep 1125659 = 1688489) B1688489
theorem B1127735 : Blo 750330 1127735 := bstep (se 1 (by rfl) ⟨845801, by rfl⟩ : syracuseStep 1127735 = 1691603) B1691603
theorem B6436583 : Blo 750330 6436583 := bstep (se 1 (by rfl) ⟨4827437, by rfl⟩ : syracuseStep 6436583 = 9654875) B9654875
theorem B5717303 : Blo 750330 5717303 := bstep (se 1 (by rfl) ⟨4287977, by rfl⟩ : syracuseStep 5717303 = 8575955) B8575955
theorem B12173321 : Blo 750330 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B1130747 : Blo 750330 1130747 := bstep (se 1 (by rfl) ⟨848060, by rfl⟩ : syracuseStep 1130747 = 1696121) B1696121
theorem B1130921 : Blo 750330 1130921 := bstep (se 2 (by rfl) ⟨424095, by rfl⟩ : syracuseStep 1130921 = 848191) B848191
theorem B903035 : Blo 750330 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B1689569 : Blo 750330 1689569 := bstep (se 2 (by rfl) ⟨633588, by rfl⟩ : syracuseStep 1689569 = 1267177) B1267177
theorem B109594943 : Blo 750330 109594943 := bstep (se 1 (by rfl) ⟨82196207, by rfl⟩ : syracuseStep 109594943 = 164392415) B164392415
theorem B3658303 : Blo 750330 3658303 := bstep (se 1 (by rfl) ⟨2743727, by rfl⟩ : syracuseStep 3658303 = 5487455) B5487455
theorem B11589641 : Blo 750330 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B1694591 : Blo 750330 1694591 := bstep (se 1 (by rfl) ⟨1270943, by rfl⟩ : syracuseStep 1694591 = 2541887) B2541887
theorem B8117279 : Blo 750330 8117279 := bstep (se 1 (by rfl) ⟨6087959, by rfl⟩ : syracuseStep 8117279 = 12175919) B12175919
theorem B1695059 : Blo 750330 1695059 := bstep (se 1 (by rfl) ⟨1271294, by rfl⟩ : syracuseStep 1695059 = 2542589) B2542589
theorem B4808393 : Blo 750330 4808393 := bstep (se 2 (by rfl) ⟨1803147, by rfl⟩ : syracuseStep 4808393 = 3606295) B3606295
theorem B844735 : Blo 750330 844735 := bstep (se 1 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 844735 = 1267103) B1267103
theorem B6417751 : Blo 750330 6417751 := bstep (se 1 (by rfl) ⟨4813313, by rfl⟩ : syracuseStep 6417751 = 9626627) B9626627
theorem B4288889 : Blo 750330 4288889 := bstep (se 2 (by rfl) ⟨1608333, by rfl⟩ : syracuseStep 4288889 = 3216667) B3216667
theorem B751899 : Blo 750330 751899 := bstep (se 1 (by rfl) ⟨563924, by rfl⟩ : syracuseStep 751899 = 1127849) B1127849
theorem B6093119 : Blo 750330 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B751999 : Blo 750330 751999 := bstep (se 1 (by rfl) ⟨563999, by rfl⟩ : syracuseStep 751999 = 1127999) B1127999
theorem B752943 : Blo 750330 752943 := bstep (se 1 (by rfl) ⟨564707, by rfl⟩ : syracuseStep 752943 = 1129415) B1129415
theorem B3210653 : Blo 750330 3210653 := bstep (se 3 (by rfl) ⟨601997, by rfl⟩ : syracuseStep 3210653 = 1203995) B1203995
theorem B69369317 : Blo 750330 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B753307 : Blo 750330 753307 := bstep (se 1 (by rfl) ⟨564980, by rfl⟩ : syracuseStep 753307 = 1129961) B1129961
theorem B753831 : Blo 750330 753831 := bstep (se 1 (by rfl) ⟨565373, by rfl⟩ : syracuseStep 753831 = 1130747) B1130747
theorem B753947 : Blo 750330 753947 := bstep (se 1 (by rfl) ⟨565460, by rfl⟩ : syracuseStep 753947 = 1130921) B1130921
theorem B8557001 : Blo 750330 8557001 := bstep (se 2 (by rfl) ⟨3208875, by rfl⟩ : syracuseStep 8557001 = 6417751) B6417751
theorem B5411519 : Blo 750330 5411519 := bstep (se 1 (by rfl) ⟨4058639, by rfl⟩ : syracuseStep 5411519 = 8117279) B8117279
theorem B3809105 : Blo 750330 3809105 := bstep (se 2 (by rfl) ⟨1428414, by rfl⟩ : syracuseStep 3809105 = 2856829) B2856829
theorem B2859259 : Blo 750330 2859259 := bstep (se 1 (by rfl) ⟨2144444, by rfl⟩ : syracuseStep 2859259 = 4288889) B4288889
theorem B15476669 : Blo 750330 15476669 := bstep (se 3 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 15476669 = 5803751) B5803751
theorem B3811535 : Blo 750330 3811535 := bstep (se 1 (by rfl) ⟨2858651, by rfl⟩ : syracuseStep 3811535 = 5717303) B5717303
theorem B2140435 : Blo 750330 2140435 := bstep (se 1 (by rfl) ⟨1605326, by rfl⟩ : syracuseStep 2140435 = 3210653) B3210653
theorem B46246211 : Blo 750330 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B1288943 : Blo 750330 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B1126313 : Blo 750330 1126313 := bstep (se 2 (by rfl) ⟨422367, by rfl⟩ : syracuseStep 1126313 = 844735) B844735
theorem B2142121 : Blo 750330 2142121 := bstep (se 2 (by rfl) ⟨803295, by rfl⟩ : syracuseStep 2142121 = 1606591) B1606591
theorem B1126379 : Blo 750330 1126379 := bstep (se 1 (by rfl) ⟨844784, by rfl⟩ : syracuseStep 1126379 = 1689569) B1689569
theorem B2535515 : Blo 750330 2535515 := bstep (se 1 (by rfl) ⟨1901636, by rfl⟩ : syracuseStep 2535515 = 3803273) B3803273
theorem B19510949 : Blo 750330 19510949 := bstep (se 4 (by rfl) ⟨1829151, by rfl⟩ : syracuseStep 19510949 = 3658303) B3658303
theorem B1129727 : Blo 750330 1129727 := bstep (se 1 (by rfl) ⟨847295, by rfl⟩ : syracuseStep 1129727 = 1694591) B1694591
theorem B1130039 : Blo 750330 1130039 := bstep (se 1 (by rfl) ⟨847529, by rfl⟩ : syracuseStep 1130039 = 1695059) B1695059
theorem B2408093 : Blo 750330 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B7717315 : Blo 750330 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B8115547 : Blo 750330 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B44062379 : Blo 750330 44062379 := bstep (se 1 (by rfl) ⟨33046784, by rfl⟩ : syracuseStep 44062379 = 66093569) B66093569
theorem B73063295 : Blo 750330 73063295 := bstep (se 1 (by rfl) ⟨54797471, by rfl⟩ : syracuseStep 73063295 = 109594943) B109594943
theorem B1073179 : Blo 750330 1073179 := bstep (se 1 (by rfl) ⟨804884, by rfl⟩ : syracuseStep 1073179 = 1609769) B1609769
theorem B31351303 : Blo 750330 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B7726427 : Blo 750330 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B176580371 : Blo 750330 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B3205595 : Blo 750330 3205595 := bstep (se 1 (by rfl) ⟨2404196, by rfl⟩ : syracuseStep 3205595 = 4808393) B4808393
theorem B6187859 : Blo 750330 6187859 := bstep (se 1 (by rfl) ⟨4640894, by rfl⟩ : syracuseStep 6187859 = 9281789) B9281789
theorem B750439 : Blo 750330 750439 := bstep (se 1 (by rfl) ⟨562829, by rfl⟩ : syracuseStep 750439 = 1125659) B1125659
theorem B37582501 : Blo 750330 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B751823 : Blo 750330 751823 := bstep (se 1 (by rfl) ⟨563867, by rfl⟩ : syracuseStep 751823 = 1127735) B1127735
theorem B4291055 : Blo 750330 4291055 := bstep (se 1 (by rfl) ⟨3218291, by rfl⟩ : syracuseStep 4291055 = 6436583) B6436583
theorem B4062079 : Blo 750330 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B10289753 : Blo 750330 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B5704667 : Blo 750330 5704667 := bstep (se 1 (by rfl) ⟨4278500, by rfl⟩ : syracuseStep 5704667 = 8557001) B8557001
theorem B2853913 : Blo 750330 2853913 := bstep (se 2 (by rfl) ⟨1070217, by rfl⟩ : syracuseStep 2853913 = 2140435) B2140435
theorem B3607679 : Blo 750330 3607679 := bstep (se 1 (by rfl) ⟨2705759, by rfl⟩ : syracuseStep 3607679 = 5411519) B5411519
theorem B21664421 : Blo 750330 21664421 := bstep (se 4 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 21664421 = 4062079) B4062079
theorem B470880989 : Blo 750330 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B2856161 : Blo 750330 2856161 := bstep (se 2 (by rfl) ⟨1071060, by rfl⟩ : syracuseStep 2856161 = 2142121) B2142121
theorem B5150951 : Blo 750330 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B10820729 : Blo 750330 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B859295 : Blo 750330 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B50110001 : Blo 750330 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B2860703 : Blo 750330 2860703 := bstep (se 1 (by rfl) ⟨2145527, by rfl⟩ : syracuseStep 2860703 = 4291055) B4291055
theorem B3812345 : Blo 750330 3812345 := bstep (se 2 (by rfl) ⟨1429629, by rfl⟩ : syracuseStep 3812345 = 2859259) B2859259
theorem B29374919 : Blo 750330 29374919 := bstep (se 1 (by rfl) ⟨22031189, by rfl⟩ : syracuseStep 29374919 = 44062379) B44062379
theorem B48708863 : Blo 750330 48708863 := bstep (se 1 (by rfl) ⟨36531647, by rfl⟩ : syracuseStep 48708863 = 73063295) B73063295
theorem B2539403 : Blo 750330 2539403 := bstep (se 1 (by rfl) ⟨1904552, by rfl⟩ : syracuseStep 2539403 = 3809105) B3809105
theorem B2541023 : Blo 750330 2541023 := bstep (se 1 (by rfl) ⟨1905767, by rfl⟩ : syracuseStep 2541023 = 3811535) B3811535
theorem B1690343 : Blo 750330 1690343 := bstep (se 1 (by rfl) ⟨1267757, by rfl⟩ : syracuseStep 1690343 = 2535515) B2535515
theorem B5723621 : Blo 750330 5723621 := bstep (se 4 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 5723621 = 1073179) B1073179
theorem B167206949 : Blo 750330 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B8548253 : Blo 750330 8548253 := bstep (se 3 (by rfl) ⟨1602797, by rfl⟩ : syracuseStep 8548253 = 3205595) B3205595
theorem B10317779 : Blo 750330 10317779 := bstep (se 1 (by rfl) ⟨7738334, by rfl⟩ : syracuseStep 10317779 = 15476669) B15476669
theorem B30830807 : Blo 750330 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B4125239 : Blo 750330 4125239 := bstep (se 1 (by rfl) ⟨3093929, by rfl⟩ : syracuseStep 4125239 = 6187859) B6187859
theorem B750875 : Blo 750330 750875 := bstep (se 1 (by rfl) ⟨563156, by rfl⟩ : syracuseStep 750875 = 1126313) B1126313
theorem B750919 : Blo 750330 750919 := bstep (se 1 (by rfl) ⟨563189, by rfl⟩ : syracuseStep 750919 = 1126379) B1126379
theorem B13007299 : Blo 750330 13007299 := bstep (se 1 (by rfl) ⟨9755474, by rfl⟩ : syracuseStep 13007299 = 19510949) B19510949
theorem B753151 : Blo 750330 753151 := bstep (se 1 (by rfl) ⟨564863, by rfl⟩ : syracuseStep 753151 = 1129727) B1129727
theorem B753359 : Blo 750330 753359 := bstep (se 1 (by rfl) ⟨565019, by rfl⟩ : syracuseStep 753359 = 1130039) B1130039
theorem B1605395 : Blo 750330 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B3803111 : Blo 750330 3803111 := bstep (se 1 (by rfl) ⟨2852333, by rfl⟩ : syracuseStep 3803111 = 5704667) B5704667
theorem B313920659 : Blo 750330 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B1904107 : Blo 750330 1904107 := bstep (se 1 (by rfl) ⟨1428080, by rfl⟩ : syracuseStep 1904107 = 2856161) B2856161
theorem B3805217 : Blo 750330 3805217 := bstep (se 2 (by rfl) ⟨1426956, by rfl⟩ : syracuseStep 3805217 = 2853913) B2853913
theorem B1907135 : Blo 750330 1907135 := bstep (se 1 (by rfl) ⟨1430351, by rfl⟩ : syracuseStep 1907135 = 2860703) B2860703
theorem B20553871 : Blo 750330 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B17343065 : Blo 750330 17343065 := bstep (se 2 (by rfl) ⟨6503649, by rfl⟩ : syracuseStep 17343065 = 13007299) B13007299
theorem B6859835 : Blo 750330 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B1126895 : Blo 750330 1126895 := bstep (se 1 (by rfl) ⟨845171, by rfl⟩ : syracuseStep 1126895 = 1690343) B1690343
theorem B3815747 : Blo 750330 3815747 := bstep (se 1 (by rfl) ⟨2861810, by rfl⟩ : syracuseStep 3815747 = 5723621) B5723621
theorem B33406667 : Blo 750330 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B2541563 : Blo 750330 2541563 := bstep (se 1 (by rfl) ⟨1906172, by rfl⟩ : syracuseStep 2541563 = 3812345) B3812345
theorem B28855277 : Blo 750330 28855277 := bstep (se 3 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 28855277 = 10820729) B10820729
theorem B9620477 : Blo 750330 9620477 := bstep (se 3 (by rfl) ⟨1803839, by rfl⟩ : syracuseStep 9620477 = 3607679) B3607679
theorem B19583279 : Blo 750330 19583279 := bstep (se 1 (by rfl) ⟨14687459, by rfl⟩ : syracuseStep 19583279 = 29374919) B29374919
theorem B1070263 : Blo 750330 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B1692935 : Blo 750330 1692935 := bstep (se 1 (by rfl) ⟨1269701, by rfl⟩ : syracuseStep 1692935 = 2539403) B2539403
theorem B1694015 : Blo 750330 1694015 := bstep (se 1 (by rfl) ⟨1270511, by rfl⟩ : syracuseStep 1694015 = 2541023) B2541023
theorem B14442947 : Blo 750330 14442947 := bstep (se 1 (by rfl) ⟨10832210, by rfl⟩ : syracuseStep 14442947 = 21664421) B21664421
theorem B3433967 : Blo 750330 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B111471299 : Blo 750330 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B5698835 : Blo 750330 5698835 := bstep (se 1 (by rfl) ⟨4274126, by rfl⟩ : syracuseStep 5698835 = 8548253) B8548253
theorem B6878519 : Blo 750330 6878519 := bstep (se 1 (by rfl) ⟨5158889, by rfl⟩ : syracuseStep 6878519 = 10317779) B10317779
theorem B2750159 : Blo 750330 2750159 := bstep (se 1 (by rfl) ⟨2062619, by rfl⟩ : syracuseStep 2750159 = 4125239) B4125239
theorem B2291453 : Blo 750330 2291453 := bstep (se 3 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 2291453 = 859295) B859295
theorem B32472575 : Blo 750330 32472575 := bstep (se 1 (by rfl) ⟨24354431, by rfl⟩ : syracuseStep 32472575 = 48708863) B48708863
theorem B19236851 : Blo 750330 19236851 := bstep (se 1 (by rfl) ⟨14427638, by rfl⟩ : syracuseStep 19236851 = 28855277) B28855277
theorem B5708069 : Blo 750330 5708069 := bstep (se 4 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 5708069 = 1070263) B1070263
theorem B27405161 : Blo 750330 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B2535407 : Blo 750330 2535407 := bstep (se 1 (by rfl) ⟨1901555, by rfl⟩ : syracuseStep 2535407 = 3803111) B3803111
theorem B2536811 : Blo 750330 2536811 := bstep (se 1 (by rfl) ⟨1902608, by rfl⟩ : syracuseStep 2536811 = 3805217) B3805217
theorem B13055519 : Blo 750330 13055519 := bstep (se 1 (by rfl) ⟨9791639, by rfl⟩ : syracuseStep 13055519 = 19583279) B19583279
theorem B1128623 : Blo 750330 1128623 := bstep (se 1 (by rfl) ⟨846467, by rfl⟩ : syracuseStep 1128623 = 1692935) B1692935
theorem B1129343 : Blo 750330 1129343 := bstep (se 1 (by rfl) ⟨847007, by rfl⟩ : syracuseStep 1129343 = 1694015) B1694015
theorem B2538809 : Blo 750330 2538809 := bstep (se 2 (by rfl) ⟨952053, by rfl⟩ : syracuseStep 2538809 = 1904107) B1904107
theorem B4573223 : Blo 750330 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B1527635 : Blo 750330 1527635 := bstep (se 1 (by rfl) ⟨1145726, by rfl⟩ : syracuseStep 1527635 = 2291453) B2291453
theorem B2543831 : Blo 750330 2543831 := bstep (se 1 (by rfl) ⟨1907873, by rfl⟩ : syracuseStep 2543831 = 3815747) B3815747
theorem B21648383 : Blo 750330 21648383 := bstep (se 1 (by rfl) ⟨16236287, by rfl⟩ : syracuseStep 21648383 = 32472575) B32472575
theorem B22271111 : Blo 750330 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B1694375 : Blo 750330 1694375 := bstep (se 1 (by rfl) ⟨1270781, by rfl⟩ : syracuseStep 1694375 = 2541563) B2541563
theorem B6413651 : Blo 750330 6413651 := bstep (se 1 (by rfl) ⟨4810238, by rfl⟩ : syracuseStep 6413651 = 9620477) B9620477
theorem B209280439 : Blo 750330 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B1271423 : Blo 750330 1271423 := bstep (se 1 (by rfl) ⟨953567, by rfl⟩ : syracuseStep 1271423 = 1907135) B1907135
theorem B9628631 : Blo 750330 9628631 := bstep (se 1 (by rfl) ⟨7221473, by rfl⟩ : syracuseStep 9628631 = 14442947) B14442947
theorem B11562043 : Blo 750330 11562043 := bstep (se 1 (by rfl) ⟨8671532, by rfl⟩ : syracuseStep 11562043 = 17343065) B17343065
theorem B2289311 : Blo 750330 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B74314199 : Blo 750330 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B751263 : Blo 750330 751263 := bstep (se 1 (by rfl) ⟨563447, by rfl⟩ : syracuseStep 751263 = 1126895) B1126895
theorem B3799223 : Blo 750330 3799223 := bstep (se 1 (by rfl) ⟨2849417, by rfl⟩ : syracuseStep 3799223 = 5698835) B5698835
theorem B4585679 : Blo 750330 4585679 := bstep (se 1 (by rfl) ⟨3439259, by rfl⟩ : syracuseStep 4585679 = 6878519) B6878519
theorem B1833439 : Blo 750330 1833439 := bstep (se 1 (by rfl) ⟨1375079, by rfl⟩ : syracuseStep 1833439 = 2750159) B2750159
theorem B3048815 : Blo 750330 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B1018423 : Blo 750330 1018423 := bstep (se 1 (by rfl) ⟨763817, by rfl⟩ : syracuseStep 1018423 = 1527635) B1527635
theorem B14847407 : Blo 750330 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B3805379 : Blo 750330 3805379 := bstep (se 1 (by rfl) ⟨2854034, by rfl⟩ : syracuseStep 3805379 = 5708069) B5708069
theorem B2532815 : Blo 750330 2532815 := bstep (se 1 (by rfl) ⟨1899611, by rfl⟩ : syracuseStep 2532815 = 3799223) B3799223
theorem B3057119 : Blo 750330 3057119 := bstep (se 1 (by rfl) ⟨2292839, by rfl⟩ : syracuseStep 3057119 = 4585679) B4585679
theorem B12824567 : Blo 750330 12824567 := bstep (se 1 (by rfl) ⟨9618425, by rfl⟩ : syracuseStep 12824567 = 19236851) B19236851
theorem B14432255 : Blo 750330 14432255 := bstep (se 1 (by rfl) ⟨10824191, by rfl⟩ : syracuseStep 14432255 = 21648383) B21648383
theorem B15416057 : Blo 750330 15416057 := bstep (se 2 (by rfl) ⟨5781021, by rfl⟩ : syracuseStep 15416057 = 11562043) B11562043
theorem B34814717 : Blo 750330 34814717 := bstep (se 3 (by rfl) ⟨6527759, by rfl⟩ : syracuseStep 34814717 = 13055519) B13055519
theorem B1129583 : Blo 750330 1129583 := bstep (se 1 (by rfl) ⟨847187, by rfl⟩ : syracuseStep 1129583 = 1694375) B1694375
theorem B4275767 : Blo 750330 4275767 := bstep (se 1 (by rfl) ⟨3206825, by rfl⟩ : syracuseStep 4275767 = 6413651) B6413651
theorem B18270107 : Blo 750330 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B1526207 : Blo 750330 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B1690271 : Blo 750330 1690271 := bstep (se 1 (by rfl) ⟨1267703, by rfl⟩ : syracuseStep 1690271 = 2535407) B2535407
theorem B2444585 : Blo 750330 2444585 := bstep (se 2 (by rfl) ⟨916719, by rfl⟩ : syracuseStep 2444585 = 1833439) B1833439
theorem B1691207 : Blo 750330 1691207 := bstep (se 1 (by rfl) ⟨1268405, by rfl⟩ : syracuseStep 1691207 = 2536811) B2536811
theorem B279040585 : Blo 750330 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B1692539 : Blo 750330 1692539 := bstep (se 1 (by rfl) ⟨1269404, by rfl⟩ : syracuseStep 1692539 = 2538809) B2538809
theorem B1695887 : Blo 750330 1695887 := bstep (se 1 (by rfl) ⟨1271915, by rfl⟩ : syracuseStep 1695887 = 2543831) B2543831
theorem B847615 : Blo 750330 847615 := bstep (se 1 (by rfl) ⟨635711, by rfl⟩ : syracuseStep 847615 = 1271423) B1271423
theorem B6419087 : Blo 750330 6419087 := bstep (se 1 (by rfl) ⟨4814315, by rfl⟩ : syracuseStep 6419087 = 9628631) B9628631
theorem B49542799 : Blo 750330 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B752415 : Blo 750330 752415 := bstep (se 1 (by rfl) ⟨564311, by rfl⟩ : syracuseStep 752415 = 1128623) B1128623
theorem B752895 : Blo 750330 752895 := bstep (se 1 (by rfl) ⟨564671, by rfl⟩ : syracuseStep 752895 = 1129343) B1129343
theorem B2032543 : Blo 750330 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B9898271 : Blo 750330 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B372054113 : Blo 750330 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B2038079 : Blo 750330 2038079 := bstep (se 1 (by rfl) ⟨1528559, by rfl⟩ : syracuseStep 2038079 = 3057119) B3057119
theorem B4069885 : Blo 750330 4069885 := bstep (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) B1526207
theorem B23209811 : Blo 750330 23209811 := bstep (se 1 (by rfl) ⟨17407358, by rfl⟩ : syracuseStep 23209811 = 34814717) B34814717
theorem B1126847 : Blo 750330 1126847 := bstep (se 1 (by rfl) ⟨845135, by rfl⟩ : syracuseStep 1126847 = 1690271) B1690271
theorem B1127471 : Blo 750330 1127471 := bstep (se 1 (by rfl) ⟨845603, by rfl⟩ : syracuseStep 1127471 = 1691207) B1691207
theorem B2536919 : Blo 750330 2536919 := bstep (se 1 (by rfl) ⟨1902689, by rfl⟩ : syracuseStep 2536919 = 3805379) B3805379
theorem B1128359 : Blo 750330 1128359 := bstep (se 1 (by rfl) ⟨846269, by rfl⟩ : syracuseStep 1128359 = 1692539) B1692539
theorem B1357897 : Blo 750330 1357897 := bstep (se 2 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 1357897 = 1018423) B1018423
theorem B1130153 : Blo 750330 1130153 := bstep (se 2 (by rfl) ⟨423807, by rfl⟩ : syracuseStep 1130153 = 847615) B847615
theorem B1130591 : Blo 750330 1130591 := bstep (se 1 (by rfl) ⟨847943, by rfl⟩ : syracuseStep 1130591 = 1695887) B1695887
theorem B1688543 : Blo 750330 1688543 := bstep (se 1 (by rfl) ⟨1266407, by rfl⟩ : syracuseStep 1688543 = 2532815) B2532815
theorem B4279391 : Blo 750330 4279391 := bstep (se 1 (by rfl) ⟨3209543, by rfl⟩ : syracuseStep 4279391 = 6419087) B6419087
theorem B9621503 : Blo 750330 9621503 := bstep (se 1 (by rfl) ⟨7216127, by rfl⟩ : syracuseStep 9621503 = 14432255) B14432255
theorem B10277371 : Blo 750330 10277371 := bstep (se 1 (by rfl) ⟨7708028, by rfl⟩ : syracuseStep 10277371 = 15416057) B15416057
theorem B12180071 : Blo 750330 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B66057065 : Blo 750330 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B8549711 : Blo 750330 8549711 := bstep (se 1 (by rfl) ⟨6412283, by rfl⟩ : syracuseStep 8549711 = 12824567) B12824567
theorem B6518893 : Blo 750330 6518893 := bstep (se 3 (by rfl) ⟨1222292, by rfl⟩ : syracuseStep 6518893 = 2444585) B2444585
theorem B753055 : Blo 750330 753055 := bstep (se 1 (by rfl) ⟨564791, by rfl⟩ : syracuseStep 753055 = 1129583) B1129583
theorem B2850511 : Blo 750330 2850511 := bstep (se 1 (by rfl) ⟨2137883, by rfl⟩ : syracuseStep 2850511 = 4275767) B4275767
theorem B753727 : Blo 750330 753727 := bstep (se 1 (by rfl) ⟨565295, by rfl⟩ : syracuseStep 753727 = 1130591) B1130591
theorem B2852927 : Blo 750330 2852927 := bstep (se 1 (by rfl) ⟨2139695, by rfl⟩ : syracuseStep 2852927 = 4279391) B4279391
theorem B15473207 : Blo 750330 15473207 := bstep (se 1 (by rfl) ⟨11604905, by rfl⟩ : syracuseStep 15473207 = 23209811) B23209811
theorem B1810529 : Blo 750330 1810529 := bstep (se 2 (by rfl) ⟨678948, by rfl⟩ : syracuseStep 1810529 = 1357897) B1357897
theorem B8691857 : Blo 750330 8691857 := bstep (se 2 (by rfl) ⟨3259446, by rfl⟩ : syracuseStep 8691857 = 6518893) B6518893
theorem B1125695 : Blo 750330 1125695 := bstep (se 1 (by rfl) ⟨844271, by rfl⟩ : syracuseStep 1125695 = 1688543) B1688543
theorem B6598847 : Blo 750330 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B248036075 : Blo 750330 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B5426513 : Blo 750330 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B1691279 : Blo 750330 1691279 := bstep (se 1 (by rfl) ⟨1268459, by rfl⟩ : syracuseStep 1691279 = 2536919) B2536919
theorem B54812645 : Blo 750330 54812645 := bstep (se 4 (by rfl) ⟨5138685, by rfl⟩ : syracuseStep 54812645 = 10277371) B10277371
theorem B6414335 : Blo 750330 6414335 := bstep (se 1 (by rfl) ⟨4810751, by rfl⟩ : syracuseStep 6414335 = 9621503) B9621503
theorem B8120047 : Blo 750330 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B10840229 : Blo 750330 10840229 := bstep (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) B2032543
theorem B5434877 : Blo 750330 5434877 := bstep (se 3 (by rfl) ⟨1019039, by rfl⟩ : syracuseStep 5434877 = 2038079) B2038079
theorem B751231 : Blo 750330 751231 := bstep (se 1 (by rfl) ⟨563423, by rfl⟩ : syracuseStep 751231 = 1126847) B1126847
theorem B44038043 : Blo 750330 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B751647 : Blo 750330 751647 := bstep (se 1 (by rfl) ⟨563735, by rfl⟩ : syracuseStep 751647 = 1127471) B1127471
theorem B5699807 : Blo 750330 5699807 := bstep (se 1 (by rfl) ⟨4274855, by rfl⟩ : syracuseStep 5699807 = 8549711) B8549711
theorem B752239 : Blo 750330 752239 := bstep (se 1 (by rfl) ⟨564179, by rfl⟩ : syracuseStep 752239 = 1128359) B1128359
theorem B3800681 : Blo 750330 3800681 := bstep (se 2 (by rfl) ⟨1425255, by rfl⟩ : syracuseStep 3800681 = 2850511) B2850511
theorem B753435 : Blo 750330 753435 := bstep (se 1 (by rfl) ⟨565076, by rfl⟩ : syracuseStep 753435 = 1130153) B1130153
theorem B1901951 : Blo 750330 1901951 := bstep (se 1 (by rfl) ⟨1426463, by rfl⟩ : syracuseStep 1901951 = 2852927) B2852927
theorem B36541763 : Blo 750330 36541763 := bstep (se 1 (by rfl) ⟨27406322, by rfl⟩ : syracuseStep 36541763 = 54812645) B54812645
theorem B4399231 : Blo 750330 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B165357383 : Blo 750330 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B2533787 : Blo 750330 2533787 := bstep (se 1 (by rfl) ⟨1900340, by rfl⟩ : syracuseStep 2533787 = 3800681) B3800681
theorem B3617675 : Blo 750330 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B10826729 : Blo 750330 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B1127519 : Blo 750330 1127519 := bstep (se 1 (by rfl) ⟨845639, by rfl⟩ : syracuseStep 1127519 = 1691279) B1691279
theorem B4276223 : Blo 750330 4276223 := bstep (se 1 (by rfl) ⟨3207167, by rfl⟩ : syracuseStep 4276223 = 6414335) B6414335
theorem B7226819 : Blo 750330 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B3623251 : Blo 750330 3623251 := bstep (se 1 (by rfl) ⟨2717438, by rfl⟩ : syracuseStep 3623251 = 5434877) B5434877
theorem B10315471 : Blo 750330 10315471 := bstep (se 1 (by rfl) ⟨7736603, by rfl⟩ : syracuseStep 10315471 = 15473207) B15473207
theorem B1207019 : Blo 750330 1207019 := bstep (se 1 (by rfl) ⟨905264, by rfl⟩ : syracuseStep 1207019 = 1810529) B1810529
theorem B5794571 : Blo 750330 5794571 := bstep (se 1 (by rfl) ⟨4345928, by rfl⟩ : syracuseStep 5794571 = 8691857) B8691857
theorem B750463 : Blo 750330 750463 := bstep (se 1 (by rfl) ⟨562847, by rfl⟩ : syracuseStep 750463 = 1125695) B1125695
theorem B29358695 : Blo 750330 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B3799871 : Blo 750330 3799871 := bstep (se 1 (by rfl) ⟨2849903, by rfl⟩ : syracuseStep 3799871 = 5699807) B5699807
theorem B5865641 : Blo 750330 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B4817879 : Blo 750330 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B3218717 : Blo 750330 3218717 := bstep (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) B1207019
theorem B7217819 : Blo 750330 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B19572463 : Blo 750330 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B2533247 : Blo 750330 2533247 := bstep (se 1 (by rfl) ⟨1899935, by rfl⟩ : syracuseStep 2533247 = 3799871) B3799871
theorem B4831001 : Blo 750330 4831001 := bstep (se 2 (by rfl) ⟨1811625, by rfl⟩ : syracuseStep 4831001 = 3623251) B3623251
theorem B24361175 : Blo 750330 24361175 := bstep (se 1 (by rfl) ⟨18270881, by rfl⟩ : syracuseStep 24361175 = 36541763) B36541763
theorem B1689191 : Blo 750330 1689191 := bstep (se 1 (by rfl) ⟨1266893, by rfl⟩ : syracuseStep 1689191 = 2533787) B2533787
theorem B2411783 : Blo 750330 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B1267967 : Blo 750330 1267967 := bstep (se 1 (by rfl) ⟨950975, by rfl⟩ : syracuseStep 1267967 = 1901951) B1901951
theorem B2850815 : Blo 750330 2850815 := bstep (se 1 (by rfl) ⟨2138111, by rfl⟩ : syracuseStep 2850815 = 4276223) B4276223
theorem B13753961 : Blo 750330 13753961 := bstep (se 2 (by rfl) ⟨5157735, by rfl⟩ : syracuseStep 13753961 = 10315471) B10315471
theorem B440953021 : Blo 750330 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B3863047 : Blo 750330 3863047 := bstep (se 1 (by rfl) ⟨2897285, by rfl⟩ : syracuseStep 3863047 = 5794571) B5794571
theorem B751679 : Blo 750330 751679 := bstep (se 1 (by rfl) ⟨563759, by rfl⟩ : syracuseStep 751679 = 1127519) B1127519
theorem B3211919 : Blo 750330 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B1607855 : Blo 750330 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B5150729 : Blo 750330 5150729 := bstep (se 2 (by rfl) ⟨1931523, by rfl⟩ : syracuseStep 5150729 = 3863047) B3863047
theorem B3220667 : Blo 750330 3220667 := bstep (se 1 (by rfl) ⟨2415500, by rfl⟩ : syracuseStep 3220667 = 4831001) B4831001
theorem B3910427 : Blo 750330 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B1126127 : Blo 750330 1126127 := bstep (se 1 (by rfl) ⟨844595, by rfl⟩ : syracuseStep 1126127 = 1689191) B1689191
theorem B26096617 : Blo 750330 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B587937361 : Blo 750330 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B1688831 : Blo 750330 1688831 := bstep (se 1 (by rfl) ⟨1266623, by rfl⟩ : syracuseStep 1688831 = 2533247) B2533247
theorem B16240783 : Blo 750330 16240783 := bstep (se 1 (by rfl) ⟨12180587, by rfl⟩ : syracuseStep 16240783 = 24361175) B24361175
theorem B845311 : Blo 750330 845311 := bstep (se 1 (by rfl) ⟨633983, by rfl⟩ : syracuseStep 845311 = 1267967) B1267967
theorem B9169307 : Blo 750330 9169307 := bstep (se 1 (by rfl) ⟨6876980, by rfl⟩ : syracuseStep 9169307 = 13753961) B13753961
theorem B4811879 : Blo 750330 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B8583245 : Blo 750330 8583245 := bstep (se 3 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 8583245 = 3218717) B3218717
theorem B1900543 : Blo 750330 1900543 := bstep (se 1 (by rfl) ⟨1425407, by rfl⟩ : syracuseStep 1900543 = 2850815) B2850815
theorem B13735277 : Blo 750330 13735277 := bstep (se 3 (by rfl) ⟨2575364, by rfl⟩ : syracuseStep 13735277 = 5150729) B5150729
theorem B783916481 : Blo 750330 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B2534057 : Blo 750330 2534057 := bstep (se 2 (by rfl) ⟨950271, by rfl⟩ : syracuseStep 2534057 = 1900543) B1900543
theorem B2141279 : Blo 750330 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B1125887 : Blo 750330 1125887 := bstep (se 1 (by rfl) ⟨844415, by rfl⟩ : syracuseStep 1125887 = 1688831) B1688831
theorem B1127081 : Blo 750330 1127081 := bstep (se 2 (by rfl) ⟨422655, by rfl⟩ : syracuseStep 1127081 = 845311) B845311
theorem B2147111 : Blo 750330 2147111 := bstep (se 1 (by rfl) ⟨1610333, by rfl⟩ : syracuseStep 2147111 = 3220667) B3220667
theorem B6112871 : Blo 750330 6112871 := bstep (se 1 (by rfl) ⟨4584653, by rfl⟩ : syracuseStep 6112871 = 9169307) B9169307
theorem B2606951 : Blo 750330 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B5722163 : Blo 750330 5722163 := bstep (se 1 (by rfl) ⟨4291622, by rfl⟩ : syracuseStep 5722163 = 8583245) B8583245
theorem B21654377 : Blo 750330 21654377 := bstep (se 2 (by rfl) ⟨8120391, by rfl⟩ : syracuseStep 21654377 = 16240783) B16240783
theorem B4287613 : Blo 750330 4287613 := bstep (se 3 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 4287613 = 1607855) B1607855
theorem B34795489 : Blo 750330 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B3207919 : Blo 750330 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B750751 : Blo 750330 750751 := bstep (se 1 (by rfl) ⟨563063, by rfl⟩ : syracuseStep 750751 = 1126127) B1126127
theorem B1737967 : Blo 750330 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B4075247 : Blo 750330 4075247 := bstep (se 1 (by rfl) ⟨3056435, by rfl⟩ : syracuseStep 4075247 = 6112871) B6112871
theorem B3814775 : Blo 750330 3814775 := bstep (se 1 (by rfl) ⟨2861081, by rfl⟩ : syracuseStep 3814775 = 5722163) B5722163
theorem B9156851 : Blo 750330 9156851 := bstep (se 1 (by rfl) ⟨6867638, by rfl⟩ : syracuseStep 9156851 = 13735277) B13735277
theorem B5716817 : Blo 750330 5716817 := bstep (se 2 (by rfl) ⟨2143806, by rfl⟩ : syracuseStep 5716817 = 4287613) B4287613
theorem B4277225 : Blo 750330 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B1689371 : Blo 750330 1689371 := bstep (se 1 (by rfl) ⟨1267028, by rfl⟩ : syracuseStep 1689371 = 2534057) B2534057
theorem B14436251 : Blo 750330 14436251 := bstep (se 1 (by rfl) ⟨10827188, by rfl⟩ : syracuseStep 14436251 = 21654377) B21654377
theorem B1427519 : Blo 750330 1427519 := bstep (se 1 (by rfl) ⟨1070639, by rfl⟩ : syracuseStep 1427519 = 2141279) B2141279
theorem B1431407 : Blo 750330 1431407 := bstep (se 1 (by rfl) ⟨1073555, by rfl⟩ : syracuseStep 1431407 = 2147111) B2147111
theorem B522610987 : Blo 750330 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B46393985 : Blo 750330 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B750591 : Blo 750330 750591 := bstep (se 1 (by rfl) ⟨562943, by rfl⟩ : syracuseStep 750591 = 1125887) B1125887
theorem B751387 : Blo 750330 751387 := bstep (se 1 (by rfl) ⟨563540, by rfl⟩ : syracuseStep 751387 = 1127081) B1127081
theorem B2851483 : Blo 750330 2851483 := bstep (se 1 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 2851483 = 4277225) B4277225
theorem B951679 : Blo 750330 951679 := bstep (se 1 (by rfl) ⟨713759, by rfl⟩ : syracuseStep 951679 = 1427519) B1427519
theorem B696814649 : Blo 750330 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B954271 : Blo 750330 954271 := bstep (se 1 (by rfl) ⟨715703, by rfl⟩ : syracuseStep 954271 = 1431407) B1431407
theorem B6104567 : Blo 750330 6104567 := bstep (se 1 (by rfl) ⟨4578425, by rfl⟩ : syracuseStep 6104567 = 9156851) B9156851
theorem B3811211 : Blo 750330 3811211 := bstep (se 1 (by rfl) ⟨2858408, by rfl⟩ : syracuseStep 3811211 = 5716817) B5716817
theorem B1126247 : Blo 750330 1126247 := bstep (se 1 (by rfl) ⟨844685, by rfl⟩ : syracuseStep 1126247 = 1689371) B1689371
theorem B123717293 : Blo 750330 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B2543183 : Blo 750330 2543183 := bstep (se 1 (by rfl) ⟨1907387, by rfl⟩ : syracuseStep 2543183 = 3814775) B3814775
theorem B9624167 : Blo 750330 9624167 := bstep (se 1 (by rfl) ⟨7218125, by rfl⟩ : syracuseStep 9624167 = 14436251) B14436251
theorem B2317289 : Blo 750330 2317289 := bstep (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) B1737967
theorem B2716831 : Blo 750330 2716831 := bstep (se 1 (by rfl) ⟨2037623, by rfl⟩ : syracuseStep 2716831 = 4075247) B4075247
theorem B3801977 : Blo 750330 3801977 := bstep (se 2 (by rfl) ⟨1425741, by rfl⟩ : syracuseStep 3801977 = 2851483) B2851483
theorem B82478195 : Blo 750330 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B14489765 : Blo 750330 14489765 := bstep (se 4 (by rfl) ⟨1358415, by rfl⟩ : syracuseStep 14489765 = 2716831) B2716831
theorem B4069711 : Blo 750330 4069711 := bstep (se 1 (by rfl) ⟨3052283, by rfl⟩ : syracuseStep 4069711 = 6104567) B6104567
theorem B2540807 : Blo 750330 2540807 := bstep (se 1 (by rfl) ⟨1905605, by rfl⟩ : syracuseStep 2540807 = 3811211) B3811211
theorem B6179437 : Blo 750330 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B1268905 : Blo 750330 1268905 := bstep (se 2 (by rfl) ⟨475839, by rfl⟩ : syracuseStep 1268905 = 951679) B951679
theorem B464543099 : Blo 750330 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B1695455 : Blo 750330 1695455 := bstep (se 1 (by rfl) ⟨1271591, by rfl⟩ : syracuseStep 1695455 = 2543183) B2543183
theorem B6416111 : Blo 750330 6416111 := bstep (se 1 (by rfl) ⟨4812083, by rfl⟩ : syracuseStep 6416111 = 9624167) B9624167
theorem B1272361 : Blo 750330 1272361 := bstep (se 2 (by rfl) ⟨477135, by rfl⟩ : syracuseStep 1272361 = 954271) B954271
theorem B750831 : Blo 750330 750831 := bstep (se 1 (by rfl) ⟨563123, by rfl⟩ : syracuseStep 750831 = 1126247) B1126247
theorem B54985463 : Blo 750330 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B309695399 : Blo 750330 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B2534651 : Blo 750330 2534651 := bstep (se 1 (by rfl) ⟨1900988, by rfl⟩ : syracuseStep 2534651 = 3801977) B3801977
theorem B8239249 : Blo 750330 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B1130303 : Blo 750330 1130303 := bstep (se 1 (by rfl) ⟨847727, by rfl⟩ : syracuseStep 1130303 = 1695455) B1695455
theorem B4277407 : Blo 750330 4277407 := bstep (se 1 (by rfl) ⟨3208055, by rfl⟩ : syracuseStep 4277407 = 6416111) B6416111
theorem B5426281 : Blo 750330 5426281 := bstep (se 2 (by rfl) ⟨2034855, by rfl⟩ : syracuseStep 5426281 = 4069711) B4069711
theorem B1691873 : Blo 750330 1691873 := bstep (se 2 (by rfl) ⟨634452, by rfl⟩ : syracuseStep 1691873 = 1268905) B1268905
theorem B1693871 : Blo 750330 1693871 := bstep (se 1 (by rfl) ⟨1270403, by rfl⟩ : syracuseStep 1693871 = 2540807) B2540807
theorem B1696481 : Blo 750330 1696481 := bstep (se 2 (by rfl) ⟨636180, by rfl⟩ : syracuseStep 1696481 = 1272361) B1272361
theorem B9659843 : Blo 750330 9659843 := bstep (se 1 (by rfl) ⟨7244882, by rfl⟩ : syracuseStep 9659843 = 14489765) B14489765
theorem B43942661 : Blo 750330 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B5703209 : Blo 750330 5703209 := bstep (se 2 (by rfl) ⟨2138703, by rfl⟩ : syracuseStep 5703209 = 4277407) B4277407
theorem B1127915 : Blo 750330 1127915 := bstep (se 1 (by rfl) ⟨845936, by rfl⟩ : syracuseStep 1127915 = 1691873) B1691873
theorem B1129247 : Blo 750330 1129247 := bstep (se 1 (by rfl) ⟨846935, by rfl⟩ : syracuseStep 1129247 = 1693871) B1693871
theorem B1130987 : Blo 750330 1130987 := bstep (se 1 (by rfl) ⟨848240, by rfl⟩ : syracuseStep 1130987 = 1696481) B1696481
theorem B6439895 : Blo 750330 6439895 := bstep (se 1 (by rfl) ⟨4829921, by rfl⟩ : syracuseStep 6439895 = 9659843) B9659843
theorem B1689767 : Blo 750330 1689767 := bstep (se 1 (by rfl) ⟨1267325, by rfl⟩ : syracuseStep 1689767 = 2534651) B2534651
theorem B36656975 : Blo 750330 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B206463599 : Blo 750330 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B7235041 : Blo 750330 7235041 := bstep (se 2 (by rfl) ⟨2713140, by rfl⟩ : syracuseStep 7235041 = 5426281) B5426281
theorem B753535 : Blo 750330 753535 := bstep (se 1 (by rfl) ⟨565151, by rfl⟩ : syracuseStep 753535 = 1130303) B1130303
theorem B753991 : Blo 750330 753991 := bstep (se 1 (by rfl) ⟨565493, by rfl⟩ : syracuseStep 753991 = 1130987) B1130987
theorem B29295107 : Blo 750330 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B4293263 : Blo 750330 4293263 := bstep (se 1 (by rfl) ⟨3219947, by rfl⟩ : syracuseStep 4293263 = 6439895) B6439895
theorem B3802139 : Blo 750330 3802139 := bstep (se 1 (by rfl) ⟨2851604, by rfl⟩ : syracuseStep 3802139 = 5703209) B5703209
theorem B1126511 : Blo 750330 1126511 := bstep (se 1 (by rfl) ⟨844883, by rfl⟩ : syracuseStep 1126511 = 1689767) B1689767
theorem B9646721 : Blo 750330 9646721 := bstep (se 2 (by rfl) ⟨3617520, by rfl⟩ : syracuseStep 9646721 = 7235041) B7235041
theorem B137642399 : Blo 750330 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B24437983 : Blo 750330 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B751943 : Blo 750330 751943 := bstep (se 1 (by rfl) ⟨563957, by rfl⟩ : syracuseStep 751943 = 1127915) B1127915
theorem B752831 : Blo 750330 752831 := bstep (se 1 (by rfl) ⟨564623, by rfl⟩ : syracuseStep 752831 = 1129247) B1129247
theorem B19530071 : Blo 750330 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B6431147 : Blo 750330 6431147 := bstep (se 1 (by rfl) ⟨4823360, by rfl⟩ : syracuseStep 6431147 = 9646721) B9646721
theorem B91761599 : Blo 750330 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B2862175 : Blo 750330 2862175 := bstep (se 1 (by rfl) ⟨2146631, by rfl⟩ : syracuseStep 2862175 = 4293263) B4293263
theorem B2534759 : Blo 750330 2534759 := bstep (se 1 (by rfl) ⟨1901069, by rfl⟩ : syracuseStep 2534759 = 3802139) B3802139
theorem B32583977 : Blo 750330 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B751007 : Blo 750330 751007 := bstep (se 1 (by rfl) ⟨563255, by rfl⟩ : syracuseStep 751007 = 1126511) B1126511
theorem B13020047 : Blo 750330 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B3816233 : Blo 750330 3816233 := bstep (se 2 (by rfl) ⟨1431087, by rfl⟩ : syracuseStep 3816233 = 2862175) B2862175
theorem B1689839 : Blo 750330 1689839 := bstep (se 1 (by rfl) ⟨1267379, by rfl⟩ : syracuseStep 1689839 = 2534759) B2534759
theorem B4287431 : Blo 750330 4287431 := bstep (se 1 (by rfl) ⟨3215573, by rfl⟩ : syracuseStep 4287431 = 6431147) B6431147
theorem B61174399 : Blo 750330 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B21722651 : Blo 750330 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B81565865 : Blo 750330 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B2858287 : Blo 750330 2858287 := bstep (se 1 (by rfl) ⟨2143715, by rfl⟩ : syracuseStep 2858287 = 4287431) B4287431
theorem B1126559 : Blo 750330 1126559 := bstep (se 1 (by rfl) ⟨844919, by rfl⟩ : syracuseStep 1126559 = 1689839) B1689839
theorem B2544155 : Blo 750330 2544155 := bstep (se 1 (by rfl) ⟨1908116, by rfl⟩ : syracuseStep 2544155 = 3816233) B3816233
theorem B8680031 : Blo 750330 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B14481767 : Blo 750330 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B3811049 : Blo 750330 3811049 := bstep (se 2 (by rfl) ⟨1429143, by rfl⟩ : syracuseStep 3811049 = 2858287) B2858287
theorem B54377243 : Blo 750330 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B5786687 : Blo 750330 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B9654511 : Blo 750330 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B1696103 : Blo 750330 1696103 := bstep (se 1 (by rfl) ⟨1272077, by rfl⟩ : syracuseStep 1696103 = 2544155) B2544155
theorem B751039 : Blo 750330 751039 := bstep (se 1 (by rfl) ⟨563279, by rfl⟩ : syracuseStep 751039 = 1126559) B1126559
theorem B36251495 : Blo 750330 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B1130735 : Blo 750330 1130735 := bstep (se 1 (by rfl) ⟨848051, by rfl⟩ : syracuseStep 1130735 = 1696103) B1696103
theorem B2540699 : Blo 750330 2540699 := bstep (se 1 (by rfl) ⟨1905524, by rfl⟩ : syracuseStep 2540699 = 3811049) B3811049
theorem B12872681 : Blo 750330 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B15431165 : Blo 750330 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B753823 : Blo 750330 753823 := bstep (se 1 (by rfl) ⟨565367, by rfl⟩ : syracuseStep 753823 = 1130735) B1130735
theorem B24167663 : Blo 750330 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B1693799 : Blo 750330 1693799 := bstep (se 1 (by rfl) ⟨1270349, by rfl⟩ : syracuseStep 1693799 = 2540699) B2540699
theorem B8581787 : Blo 750330 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B10287443 : Blo 750330 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B27433181 : Blo 750330 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B1129199 : Blo 750330 1129199 := bstep (se 1 (by rfl) ⟨846899, by rfl⟩ : syracuseStep 1129199 = 1693799) B1693799
theorem B5721191 : Blo 750330 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B16111775 : Blo 750330 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B3814127 : Blo 750330 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B73155149 : Blo 750330 73155149 := bstep (se 3 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 73155149 = 27433181) B27433181
theorem B10741183 : Blo 750330 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B752799 : Blo 750330 752799 := bstep (se 1 (by rfl) ⟨564599, by rfl⟩ : syracuseStep 752799 = 1129199) B1129199
theorem B57286309 : Blo 750330 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B48770099 : Blo 750330 48770099 := bstep (se 1 (by rfl) ⟨36577574, by rfl⟩ : syracuseStep 48770099 = 73155149) B73155149
theorem B2542751 : Blo 750330 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B32513399 : Blo 750330 32513399 := bstep (se 1 (by rfl) ⟨24385049, by rfl⟩ : syracuseStep 32513399 = 48770099) B48770099
theorem B1695167 : Blo 750330 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B76381745 : Blo 750330 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B21675599 : Blo 750330 21675599 := bstep (se 1 (by rfl) ⟨16256699, by rfl⟩ : syracuseStep 21675599 = 32513399) B32513399
theorem B1130111 : Blo 750330 1130111 := bstep (se 1 (by rfl) ⟨847583, by rfl⟩ : syracuseStep 1130111 = 1695167) B1695167
theorem B203684653 : Blo 750330 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B271579537 : Blo 750330 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B14450399 : Blo 750330 14450399 := bstep (se 1 (by rfl) ⟨10837799, by rfl⟩ : syracuseStep 14450399 = 21675599) B21675599
theorem B753407 : Blo 750330 753407 := bstep (se 1 (by rfl) ⟨565055, by rfl⟩ : syracuseStep 753407 = 1130111) B1130111
theorem B362106049 : Blo 750330 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B9633599 : Blo 750330 9633599 := bstep (se 1 (by rfl) ⟨7225199, by rfl⟩ : syracuseStep 9633599 = 14450399) B14450399
theorem B482808065 : Blo 750330 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B6422399 : Blo 750330 6422399 := bstep (se 1 (by rfl) ⟨4816799, by rfl⟩ : syracuseStep 6422399 = 9633599) B9633599
theorem B5149952693 : Blo 750330 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B4281599 : Blo 750330 4281599 := bstep (se 1 (by rfl) ⟨3211199, by rfl⟩ : syracuseStep 4281599 = 6422399) B6422399
theorem B3433301795 : Blo 750330 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B2854399 : Blo 750330 2854399 := bstep (se 1 (by rfl) ⟨2140799, by rfl⟩ : syracuseStep 2854399 = 4281599) B4281599
theorem B3805865 : Blo 750330 3805865 := bstep (se 2 (by rfl) ⟨1427199, by rfl⟩ : syracuseStep 3805865 = 2854399) B2854399
theorem B2288867863 : Blo 750330 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B3051823817 : Blo 750330 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B2537243 : Blo 750330 2537243 := bstep (se 1 (by rfl) ⟨1902932, by rfl⟩ : syracuseStep 2537243 = 3805865) B3805865
theorem B8138196845 : Blo 750330 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B1691495 : Blo 750330 1691495 := bstep (se 1 (by rfl) ⟨1268621, by rfl⟩ : syracuseStep 1691495 = 2537243) B2537243
theorem B5425464563 : Blo 750330 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B1127663 : Blo 750330 1127663 := bstep (se 1 (by rfl) ⟨845747, by rfl⟩ : syracuseStep 1127663 = 1691495) B1691495
theorem B3616976375 : Blo 750330 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B751775 : Blo 750330 751775 := bstep (se 1 (by rfl) ⟨563831, by rfl⟩ : syracuseStep 751775 = 1127663) B1127663
theorem B2411317583 : Blo 750330 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B1607545055 : Blo 750330 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B1071696703 : Blo 750330 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B1428928937 : Blo 750330 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B952619291 : Blo 750330 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B635079527 : Blo 750330 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B423386351 : Blo 750330 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B282257567 : Blo 750330 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B188171711 : Blo 750330 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B125447807 : Blo 750330 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B83631871 : Blo 750330 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B446036645 : Blo 750330 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B297357763 : Blo 750330 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B396477017 : Blo 750330 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B264318011 : Blo 750330 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B176212007 : Blo 750330 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B117474671 : Blo 750330 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B313265789 : Blo 750330 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B208843859 : Blo 750330 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B139229239 : Blo 750330 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B185638985 : Blo 750330 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B123759323 : Blo 750330 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B82506215 : Blo 750330 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B220016573 : Blo 750330 220016573 := bstep (se 3 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 220016573 = 82506215) B82506215
theorem B146677715 : Blo 750330 146677715 := bstep (se 1 (by rfl) ⟨110008286, by rfl⟩ : syracuseStep 146677715 = 220016573) B220016573
theorem B97785143 : Blo 750330 97785143 := bstep (se 1 (by rfl) ⟨73338857, by rfl⟩ : syracuseStep 97785143 = 146677715) B146677715
theorem B65190095 : Blo 750330 65190095 := bstep (se 1 (by rfl) ⟨48892571, by rfl⟩ : syracuseStep 65190095 = 97785143) B97785143
theorem B43460063 : Blo 750330 43460063 := bstep (se 1 (by rfl) ⟨32595047, by rfl⟩ : syracuseStep 43460063 = 65190095) B65190095
theorem B28973375 : Blo 750330 28973375 := bstep (se 1 (by rfl) ⟨21730031, by rfl⟩ : syracuseStep 28973375 = 43460063) B43460063
theorem B19315583 : Blo 750330 19315583 := bstep (se 1 (by rfl) ⟨14486687, by rfl⟩ : syracuseStep 19315583 = 28973375) B28973375
theorem B12877055 : Blo 750330 12877055 := bstep (se 1 (by rfl) ⟨9657791, by rfl⟩ : syracuseStep 12877055 = 19315583) B19315583
theorem B8584703 : Blo 750330 8584703 := bstep (se 1 (by rfl) ⟨6438527, by rfl⟩ : syracuseStep 8584703 = 12877055) B12877055
theorem B5723135 : Blo 750330 5723135 := bstep (se 1 (by rfl) ⟨4292351, by rfl⟩ : syracuseStep 5723135 = 8584703) B8584703
theorem B3815423 : Blo 750330 3815423 := bstep (se 1 (by rfl) ⟨2861567, by rfl⟩ : syracuseStep 3815423 = 5723135) B5723135
theorem B2543615 : Blo 750330 2543615 := bstep (se 1 (by rfl) ⟨1907711, by rfl⟩ : syracuseStep 2543615 = 3815423) B3815423
theorem B1695743 : Blo 750330 1695743 := bstep (se 1 (by rfl) ⟨1271807, by rfl⟩ : syracuseStep 1695743 = 2543615) B2543615
theorem B1130495 : Blo 750330 1130495 := bstep (se 1 (by rfl) ⟨847871, by rfl⟩ : syracuseStep 1130495 = 1695743) B1695743
theorem B753663 : Blo 750330 753663 := bstep (se 1 (by rfl) ⟨565247, by rfl⟩ : syracuseStep 753663 = 1130495) B1130495

theorem C0 (j : ℕ) (h1 : 187582 ≤ j) (h2 : j ≤ 188281) : Blo 750330 (4 * j + 3) := by
  interval_cases j
  · exact B750331
  · exact B750335
  · exact B750339
  · exact B750343
  · exact B750347
  · exact B750351
  · exact B750355
  · exact B750359
  · exact B750363
  · exact B750367
  · exact B750371
  · exact B750375
  · exact B750379
  · exact B750383
  · exact B750387
  · exact B750391
  · exact B750395
  · exact B750399
  · exact B750403
  · exact B750407
  · exact B750411
  · exact B750415
  · exact B750419
  · exact B750423
  · exact B750427
  · exact B750431
  · exact B750435
  · exact B750439
  · exact B750443
  · exact B750447
  · exact B750451
  · exact B750455
  · exact B750459
  · exact B750463
  · exact B750467
  · exact B750471
  · exact B750475
  · exact B750479
  · exact B750483
  · exact B750487
  · exact B750491
  · exact B750495
  · exact B750499
  · exact B750503
  · exact B750507
  · exact B750511
  · exact B750515
  · exact B750519
  · exact B750523
  · exact B750527
  · exact B750531
  · exact B750535
  · exact B750539
  · exact B750543
  · exact B750547
  · exact B750551
  · exact B750555
  · exact B750559
  · exact B750563
  · exact B750567
  · exact B750571
  · exact B750575
  · exact B750579
  · exact B750583
  · exact B750587
  · exact B750591
  · exact B750595
  · exact B750599
  · exact B750603
  · exact B750607
  · exact B750611
  · exact B750615
  · exact B750619
  · exact B750623
  · exact B750627
  · exact B750631
  · exact B750635
  · exact B750639
  · exact B750643
  · exact B750647
  · exact B750651
  · exact B750655
  · exact B750659
  · exact B750663
  · exact B750667
  · exact B750671
  · exact B750675
  · exact B750679
  · exact B750683
  · exact B750687
  · exact B750691
  · exact B750695
  · exact B750699
  · exact B750703
  · exact B750707
  · exact B750711
  · exact B750715
  · exact B750719
  · exact B750723
  · exact B750727
  · exact B750731
  · exact B750735
  · exact B750739
  · exact B750743
  · exact B750747
  · exact B750751
  · exact B750755
  · exact B750759
  · exact B750763
  · exact B750767
  · exact B750771
  · exact B750775
  · exact B750779
  · exact B750783
  · exact B750787
  · exact B750791
  · exact B750795
  · exact B750799
  · exact B750803
  · exact B750807
  · exact B750811
  · exact B750815
  · exact B750819
  · exact B750823
  · exact B750827
  · exact B750831
  · exact B750835
  · exact B750839
  · exact B750843
  · exact B750847
  · exact B750851
  · exact B750855
  · exact B750859
  · exact B750863
  · exact B750867
  · exact B750871
  · exact B750875
  · exact B750879
  · exact B750883
  · exact B750887
  · exact B750891
  · exact B750895
  · exact B750899
  · exact B750903
  · exact B750907
  · exact B750911
  · exact B750915
  · exact B750919
  · exact B750923
  · exact B750927
  · exact B750931
  · exact B750935
  · exact B750939
  · exact B750943
  · exact B750947
  · exact B750951
  · exact B750955
  · exact B750959
  · exact B750963
  · exact B750967
  · exact B750971
  · exact B750975
  · exact B750979
  · exact B750983
  · exact B750987
  · exact B750991
  · exact B750995
  · exact B750999
  · exact B751003
  · exact B751007
  · exact B751011
  · exact B751015
  · exact B751019
  · exact B751023
  · exact B751027
  · exact B751031
  · exact B751035
  · exact B751039
  · exact B751043
  · exact B751047
  · exact B751051
  · exact B751055
  · exact B751059
  · exact B751063
  · exact B751067
  · exact B751071
  · exact B751075
  · exact B751079
  · exact B751083
  · exact B751087
  · exact B751091
  · exact B751095
  · exact B751099
  · exact B751103
  · exact B751107
  · exact B751111
  · exact B751115
  · exact B751119
  · exact B751123
  · exact B751127
  · exact B751131
  · exact B751135
  · exact B751139
  · exact B751143
  · exact B751147
  · exact B751151
  · exact B751155
  · exact B751159
  · exact B751163
  · exact B751167
  · exact B751171
  · exact B751175
  · exact B751179
  · exact B751183
  · exact B751187
  · exact B751191
  · exact B751195
  · exact B751199
  · exact B751203
  · exact B751207
  · exact B751211
  · exact B751215
  · exact B751219
  · exact B751223
  · exact B751227
  · exact B751231
  · exact B751235
  · exact B751239
  · exact B751243
  · exact B751247
  · exact B751251
  · exact B751255
  · exact B751259
  · exact B751263
  · exact B751267
  · exact B751271
  · exact B751275
  · exact B751279
  · exact B751283
  · exact B751287
  · exact B751291
  · exact B751295
  · exact B751299
  · exact B751303
  · exact B751307
  · exact B751311
  · exact B751315
  · exact B751319
  · exact B751323
  · exact B751327
  · exact B751331
  · exact B751335
  · exact B751339
  · exact B751343
  · exact B751347
  · exact B751351
  · exact B751355
  · exact B751359
  · exact B751363
  · exact B751367
  · exact B751371
  · exact B751375
  · exact B751379
  · exact B751383
  · exact B751387
  · exact B751391
  · exact B751395
  · exact B751399
  · exact B751403
  · exact B751407
  · exact B751411
  · exact B751415
  · exact B751419
  · exact B751423
  · exact B751427
  · exact B751431
  · exact B751435
  · exact B751439
  · exact B751443
  · exact B751447
  · exact B751451
  · exact B751455
  · exact B751459
  · exact B751463
  · exact B751467
  · exact B751471
  · exact B751475
  · exact B751479
  · exact B751483
  · exact B751487
  · exact B751491
  · exact B751495
  · exact B751499
  · exact B751503
  · exact B751507
  · exact B751511
  · exact B751515
  · exact B751519
  · exact B751523
  · exact B751527
  · exact B751531
  · exact B751535
  · exact B751539
  · exact B751543
  · exact B751547
  · exact B751551
  · exact B751555
  · exact B751559
  · exact B751563
  · exact B751567
  · exact B751571
  · exact B751575
  · exact B751579
  · exact B751583
  · exact B751587
  · exact B751591
  · exact B751595
  · exact B751599
  · exact B751603
  · exact B751607
  · exact B751611
  · exact B751615
  · exact B751619
  · exact B751623
  · exact B751627
  · exact B751631
  · exact B751635
  · exact B751639
  · exact B751643
  · exact B751647
  · exact B751651
  · exact B751655
  · exact B751659
  · exact B751663
  · exact B751667
  · exact B751671
  · exact B751675
  · exact B751679
  · exact B751683
  · exact B751687
  · exact B751691
  · exact B751695
  · exact B751699
  · exact B751703
  · exact B751707
  · exact B751711
  · exact B751715
  · exact B751719
  · exact B751723
  · exact B751727
  · exact B751731
  · exact B751735
  · exact B751739
  · exact B751743
  · exact B751747
  · exact B751751
  · exact B751755
  · exact B751759
  · exact B751763
  · exact B751767
  · exact B751771
  · exact B751775
  · exact B751779
  · exact B751783
  · exact B751787
  · exact B751791
  · exact B751795
  · exact B751799
  · exact B751803
  · exact B751807
  · exact B751811
  · exact B751815
  · exact B751819
  · exact B751823
  · exact B751827
  · exact B751831
  · exact B751835
  · exact B751839
  · exact B751843
  · exact B751847
  · exact B751851
  · exact B751855
  · exact B751859
  · exact B751863
  · exact B751867
  · exact B751871
  · exact B751875
  · exact B751879
  · exact B751883
  · exact B751887
  · exact B751891
  · exact B751895
  · exact B751899
  · exact B751903
  · exact B751907
  · exact B751911
  · exact B751915
  · exact B751919
  · exact B751923
  · exact B751927
  · exact B751931
  · exact B751935
  · exact B751939
  · exact B751943
  · exact B751947
  · exact B751951
  · exact B751955
  · exact B751959
  · exact B751963
  · exact B751967
  · exact B751971
  · exact B751975
  · exact B751979
  · exact B751983
  · exact B751987
  · exact B751991
  · exact B751995
  · exact B751999
  · exact B752003
  · exact B752007
  · exact B752011
  · exact B752015
  · exact B752019
  · exact B752023
  · exact B752027
  · exact B752031
  · exact B752035
  · exact B752039
  · exact B752043
  · exact B752047
  · exact B752051
  · exact B752055
  · exact B752059
  · exact B752063
  · exact B752067
  · exact B752071
  · exact B752075
  · exact B752079
  · exact B752083
  · exact B752087
  · exact B752091
  · exact B752095
  · exact B752099
  · exact B752103
  · exact B752107
  · exact B752111
  · exact B752115
  · exact B752119
  · exact B752123
  · exact B752127
  · exact B752131
  · exact B752135
  · exact B752139
  · exact B752143
  · exact B752147
  · exact B752151
  · exact B752155
  · exact B752159
  · exact B752163
  · exact B752167
  · exact B752171
  · exact B752175
  · exact B752179
  · exact B752183
  · exact B752187
  · exact B752191
  · exact B752195
  · exact B752199
  · exact B752203
  · exact B752207
  · exact B752211
  · exact B752215
  · exact B752219
  · exact B752223
  · exact B752227
  · exact B752231
  · exact B752235
  · exact B752239
  · exact B752243
  · exact B752247
  · exact B752251
  · exact B752255
  · exact B752259
  · exact B752263
  · exact B752267
  · exact B752271
  · exact B752275
  · exact B752279
  · exact B752283
  · exact B752287
  · exact B752291
  · exact B752295
  · exact B752299
  · exact B752303
  · exact B752307
  · exact B752311
  · exact B752315
  · exact B752319
  · exact B752323
  · exact B752327
  · exact B752331
  · exact B752335
  · exact B752339
  · exact B752343
  · exact B752347
  · exact B752351
  · exact B752355
  · exact B752359
  · exact B752363
  · exact B752367
  · exact B752371
  · exact B752375
  · exact B752379
  · exact B752383
  · exact B752387
  · exact B752391
  · exact B752395
  · exact B752399
  · exact B752403
  · exact B752407
  · exact B752411
  · exact B752415
  · exact B752419
  · exact B752423
  · exact B752427
  · exact B752431
  · exact B752435
  · exact B752439
  · exact B752443
  · exact B752447
  · exact B752451
  · exact B752455
  · exact B752459
  · exact B752463
  · exact B752467
  · exact B752471
  · exact B752475
  · exact B752479
  · exact B752483
  · exact B752487
  · exact B752491
  · exact B752495
  · exact B752499
  · exact B752503
  · exact B752507
  · exact B752511
  · exact B752515
  · exact B752519
  · exact B752523
  · exact B752527
  · exact B752531
  · exact B752535
  · exact B752539
  · exact B752543
  · exact B752547
  · exact B752551
  · exact B752555
  · exact B752559
  · exact B752563
  · exact B752567
  · exact B752571
  · exact B752575
  · exact B752579
  · exact B752583
  · exact B752587
  · exact B752591
  · exact B752595
  · exact B752599
  · exact B752603
  · exact B752607
  · exact B752611
  · exact B752615
  · exact B752619
  · exact B752623
  · exact B752627
  · exact B752631
  · exact B752635
  · exact B752639
  · exact B752643
  · exact B752647
  · exact B752651
  · exact B752655
  · exact B752659
  · exact B752663
  · exact B752667
  · exact B752671
  · exact B752675
  · exact B752679
  · exact B752683
  · exact B752687
  · exact B752691
  · exact B752695
  · exact B752699
  · exact B752703
  · exact B752707
  · exact B752711
  · exact B752715
  · exact B752719
  · exact B752723
  · exact B752727
  · exact B752731
  · exact B752735
  · exact B752739
  · exact B752743
  · exact B752747
  · exact B752751
  · exact B752755
  · exact B752759
  · exact B752763
  · exact B752767
  · exact B752771
  · exact B752775
  · exact B752779
  · exact B752783
  · exact B752787
  · exact B752791
  · exact B752795
  · exact B752799
  · exact B752803
  · exact B752807
  · exact B752811
  · exact B752815
  · exact B752819
  · exact B752823
  · exact B752827
  · exact B752831
  · exact B752835
  · exact B752839
  · exact B752843
  · exact B752847
  · exact B752851
  · exact B752855
  · exact B752859
  · exact B752863
  · exact B752867
  · exact B752871
  · exact B752875
  · exact B752879
  · exact B752883
  · exact B752887
  · exact B752891
  · exact B752895
  · exact B752899
  · exact B752903
  · exact B752907
  · exact B752911
  · exact B752915
  · exact B752919
  · exact B752923
  · exact B752927
  · exact B752931
  · exact B752935
  · exact B752939
  · exact B752943
  · exact B752947
  · exact B752951
  · exact B752955
  · exact B752959
  · exact B752963
  · exact B752967
  · exact B752971
  · exact B752975
  · exact B752979
  · exact B752983
  · exact B752987
  · exact B752991
  · exact B752995
  · exact B752999
  · exact B753003
  · exact B753007
  · exact B753011
  · exact B753015
  · exact B753019
  · exact B753023
  · exact B753027
  · exact B753031
  · exact B753035
  · exact B753039
  · exact B753043
  · exact B753047
  · exact B753051
  · exact B753055
  · exact B753059
  · exact B753063
  · exact B753067
  · exact B753071
  · exact B753075
  · exact B753079
  · exact B753083
  · exact B753087
  · exact B753091
  · exact B753095
  · exact B753099
  · exact B753103
  · exact B753107
  · exact B753111
  · exact B753115
  · exact B753119
  · exact B753123
  · exact B753127

theorem C1 (j : ℕ) (h1 : 188282 ≤ j) (h2 : j ≤ 188581) : Blo 750330 (4 * j + 3) := by
  interval_cases j
  · exact B753131
  · exact B753135
  · exact B753139
  · exact B753143
  · exact B753147
  · exact B753151
  · exact B753155
  · exact B753159
  · exact B753163
  · exact B753167
  · exact B753171
  · exact B753175
  · exact B753179
  · exact B753183
  · exact B753187
  · exact B753191
  · exact B753195
  · exact B753199
  · exact B753203
  · exact B753207
  · exact B753211
  · exact B753215
  · exact B753219
  · exact B753223
  · exact B753227
  · exact B753231
  · exact B753235
  · exact B753239
  · exact B753243
  · exact B753247
  · exact B753251
  · exact B753255
  · exact B753259
  · exact B753263
  · exact B753267
  · exact B753271
  · exact B753275
  · exact B753279
  · exact B753283
  · exact B753287
  · exact B753291
  · exact B753295
  · exact B753299
  · exact B753303
  · exact B753307
  · exact B753311
  · exact B753315
  · exact B753319
  · exact B753323
  · exact B753327
  · exact B753331
  · exact B753335
  · exact B753339
  · exact B753343
  · exact B753347
  · exact B753351
  · exact B753355
  · exact B753359
  · exact B753363
  · exact B753367
  · exact B753371
  · exact B753375
  · exact B753379
  · exact B753383
  · exact B753387
  · exact B753391
  · exact B753395
  · exact B753399
  · exact B753403
  · exact B753407
  · exact B753411
  · exact B753415
  · exact B753419
  · exact B753423
  · exact B753427
  · exact B753431
  · exact B753435
  · exact B753439
  · exact B753443
  · exact B753447
  · exact B753451
  · exact B753455
  · exact B753459
  · exact B753463
  · exact B753467
  · exact B753471
  · exact B753475
  · exact B753479
  · exact B753483
  · exact B753487
  · exact B753491
  · exact B753495
  · exact B753499
  · exact B753503
  · exact B753507
  · exact B753511
  · exact B753515
  · exact B753519
  · exact B753523
  · exact B753527
  · exact B753531
  · exact B753535
  · exact B753539
  · exact B753543
  · exact B753547
  · exact B753551
  · exact B753555
  · exact B753559
  · exact B753563
  · exact B753567
  · exact B753571
  · exact B753575
  · exact B753579
  · exact B753583
  · exact B753587
  · exact B753591
  · exact B753595
  · exact B753599
  · exact B753603
  · exact B753607
  · exact B753611
  · exact B753615
  · exact B753619
  · exact B753623
  · exact B753627
  · exact B753631
  · exact B753635
  · exact B753639
  · exact B753643
  · exact B753647
  · exact B753651
  · exact B753655
  · exact B753659
  · exact B753663
  · exact B753667
  · exact B753671
  · exact B753675
  · exact B753679
  · exact B753683
  · exact B753687
  · exact B753691
  · exact B753695
  · exact B753699
  · exact B753703
  · exact B753707
  · exact B753711
  · exact B753715
  · exact B753719
  · exact B753723
  · exact B753727
  · exact B753731
  · exact B753735
  · exact B753739
  · exact B753743
  · exact B753747
  · exact B753751
  · exact B753755
  · exact B753759
  · exact B753763
  · exact B753767
  · exact B753771
  · exact B753775
  · exact B753779
  · exact B753783
  · exact B753787
  · exact B753791
  · exact B753795
  · exact B753799
  · exact B753803
  · exact B753807
  · exact B753811
  · exact B753815
  · exact B753819
  · exact B753823
  · exact B753827
  · exact B753831
  · exact B753835
  · exact B753839
  · exact B753843
  · exact B753847
  · exact B753851
  · exact B753855
  · exact B753859
  · exact B753863
  · exact B753867
  · exact B753871
  · exact B753875
  · exact B753879
  · exact B753883
  · exact B753887
  · exact B753891
  · exact B753895
  · exact B753899
  · exact B753903
  · exact B753907
  · exact B753911
  · exact B753915
  · exact B753919
  · exact B753923
  · exact B753927
  · exact B753931
  · exact B753935
  · exact B753939
  · exact B753943
  · exact B753947
  · exact B753951
  · exact B753955
  · exact B753959
  · exact B753963
  · exact B753967
  · exact B753971
  · exact B753975
  · exact B753979
  · exact B753983
  · exact B753987
  · exact B753991
  · exact B753995
  · exact B753999
  · exact B754003
  · exact B754007
  · exact B754011
  · exact B754015
  · exact B754019
  · exact B754023
  · exact B754027
  · exact B754031
  · exact B754035
  · exact B754039
  · exact B754043
  · exact B754047
  · exact B754051
  · exact B754055
  · exact B754059
  · exact B754063
  · exact B754067
  · exact B754071
  · exact B754075
  · exact B754079
  · exact B754083
  · exact B754087
  · exact B754091
  · exact B754095
  · exact B754099
  · exact B754103
  · exact B754107
  · exact B754111
  · exact B754115
  · exact B754119
  · exact B754123
  · exact B754127
  · exact B754131
  · exact B754135
  · exact B754139
  · exact B754143
  · exact B754147
  · exact B754151
  · exact B754155
  · exact B754159
  · exact B754163
  · exact B754167
  · exact B754171
  · exact B754175
  · exact B754179
  · exact B754183
  · exact B754187
  · exact B754191
  · exact B754195
  · exact B754199
  · exact B754203
  · exact B754207
  · exact B754211
  · exact B754215
  · exact B754219
  · exact B754223
  · exact B754227
  · exact B754231
  · exact B754235
  · exact B754239
  · exact B754243
  · exact B754247
  · exact B754251
  · exact B754255
  · exact B754259
  · exact B754263
  · exact B754267
  · exact B754271
  · exact B754275
  · exact B754279
  · exact B754283
  · exact B754287
  · exact B754291
  · exact B754295
  · exact B754299
  · exact B754303
  · exact B754307
  · exact B754311
  · exact B754315
  · exact B754319
  · exact B754323
  · exact B754327

theorem solution (m : ℕ) (hlo : 750330 ≤ m) (hhi : m ≤ 754330) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 187582 ≤ j := by omega
    have hj2 : j ≤ 188581 := by omega
    have hb : Blo 750330 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 188282 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
