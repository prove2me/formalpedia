-- Prove2me | solution 1 for syracuse_descends_range_1883143_1883431
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:18:39.420312+00:00
-- url     : https://prove2.me/submissions/5046d891-2fb1-4fb4-80b2-42b5a281d2fc

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


theorem B4237325 : Blo 1883143 4237325 := bbase (se 3 (by rfl) ⟨794498, by rfl⟩ : syracuseStep 4237325 = 1588997) (by norm_num)
theorem B2011169 : Blo 1883143 2011169 := bbase (se 2 (by rfl) ⟨754188, by rfl⟩ : syracuseStep 2011169 = 1508377) (by norm_num)
theorem B3393589 : Blo 1883143 3393589 := bbase (se 5 (by rfl) ⟨159074, by rfl⟩ : syracuseStep 3393589 = 318149) (by norm_num)
theorem B4237397 : Blo 1883143 4237397 := bbase (se 8 (by rfl) ⟨24828, by rfl⟩ : syracuseStep 4237397 = 49657) (by norm_num)
theorem B4022389 : Blo 1883143 4022389 := bbase (se 5 (by rfl) ⟨188549, by rfl⟩ : syracuseStep 4022389 = 377099) (by norm_num)
theorem B4237469 : Blo 1883143 4237469 := bbase (se 3 (by rfl) ⟨794525, by rfl⟩ : syracuseStep 4237469 = 1589051) (by norm_num)
theorem B4237541 : Blo 1883143 4237541 := bbase (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) (by norm_num)
theorem B4237613 : Blo 1883143 4237613 := bbase (se 3 (by rfl) ⟨794552, by rfl⟩ : syracuseStep 4237613 = 1589105) (by norm_num)
theorem B10180981 : Blo 1883143 10180981 := bbase (se 5 (by rfl) ⟨477233, by rfl⟩ : syracuseStep 10180981 = 954467) (by norm_num)
theorem B4237685 : Blo 1883143 4237685 := bbase (se 5 (by rfl) ⟨198641, by rfl⟩ : syracuseStep 4237685 = 397283) (by norm_num)
theorem B1909117 : Blo 1883143 1909117 := bbase (se 3 (by rfl) ⟨357959, by rfl⟩ : syracuseStep 1909117 = 715919) (by norm_num)
theorem B3723661 : Blo 1883143 3723661 := bbase (se 3 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 3723661 = 1396373) (by norm_num)
theorem B9533861 : Blo 1883143 9533861 := bbase (se 4 (by rfl) ⟨893799, by rfl⟩ : syracuseStep 9533861 = 1787599) (by norm_num)
theorem B3817981 : Blo 1883143 3817981 := bbase (se 3 (by rfl) ⟨715871, by rfl⟩ : syracuseStep 3817981 = 1431743) (by norm_num)
theorem B3310093 : Blo 1883143 3310093 := bbase (se 3 (by rfl) ⟨620642, by rfl⟩ : syracuseStep 3310093 = 1241285) (by norm_num)
theorem B2681365 : Blo 1883143 2681365 := bbase (se 6 (by rfl) ⟨62844, by rfl⟩ : syracuseStep 2681365 = 125689) (by norm_num)
theorem B2824733 : Blo 1883143 2824733 := bbase (se 3 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 2824733 = 1059275) (by norm_num)
theorem B2824757 : Blo 1883143 2824757 := bbase (se 5 (by rfl) ⟨132410, by rfl⟩ : syracuseStep 2824757 = 264821) (by norm_num)
theorem B2824781 : Blo 1883143 2824781 := bbase (se 3 (by rfl) ⟨529646, by rfl⟩ : syracuseStep 2824781 = 1059293) (by norm_num)
theorem B2824805 : Blo 1883143 2824805 := bbase (se 4 (by rfl) ⟨264825, by rfl⟩ : syracuseStep 2824805 = 529651) (by norm_num)
theorem B2824829 : Blo 1883143 2824829 := bbase (se 3 (by rfl) ⟨529655, by rfl⟩ : syracuseStep 2824829 = 1059311) (by norm_num)
theorem B2824853 : Blo 1883143 2824853 := bbase (se 6 (by rfl) ⟨66207, by rfl⟩ : syracuseStep 2824853 = 132415) (by norm_num)
theorem B2824877 : Blo 1883143 2824877 := bbase (se 3 (by rfl) ⟨529664, by rfl⟩ : syracuseStep 2824877 = 1059329) (by norm_num)
theorem B6355637 : Blo 1883143 6355637 := bbase (se 5 (by rfl) ⟨297920, by rfl⟩ : syracuseStep 6355637 = 595841) (by norm_num)
theorem B2824901 : Blo 1883143 2824901 := bbase (se 4 (by rfl) ⟨264834, by rfl⟩ : syracuseStep 2824901 = 529669) (by norm_num)
theorem B2824925 : Blo 1883143 2824925 := bbase (se 3 (by rfl) ⟨529673, by rfl⟩ : syracuseStep 2824925 = 1059347) (by norm_num)
theorem B2681581 : Blo 1883143 2681581 := bbase (se 3 (by rfl) ⟨502796, by rfl⟩ : syracuseStep 2681581 = 1005593) (by norm_num)
theorem B2824949 : Blo 1883143 2824949 := bbase (se 5 (by rfl) ⟨132419, by rfl⟩ : syracuseStep 2824949 = 264839) (by norm_num)
theorem B2824973 : Blo 1883143 2824973 := bbase (se 3 (by rfl) ⟨529682, by rfl⟩ : syracuseStep 2824973 = 1059365) (by norm_num)
theorem B2824997 : Blo 1883143 2824997 := bbase (se 4 (by rfl) ⟨264843, by rfl⟩ : syracuseStep 2824997 = 529687) (by norm_num)
theorem B2825021 : Blo 1883143 2825021 := bbase (se 3 (by rfl) ⟨529691, by rfl⟩ : syracuseStep 2825021 = 1059383) (by norm_num)
theorem B2825045 : Blo 1883143 2825045 := bbase (se 9 (by rfl) ⟨8276, by rfl⟩ : syracuseStep 2825045 = 16553) (by norm_num)
theorem B2825069 : Blo 1883143 2825069 := bbase (se 3 (by rfl) ⟨529700, by rfl⟩ : syracuseStep 2825069 = 1059401) (by norm_num)
theorem B2825093 : Blo 1883143 2825093 := bbase (se 4 (by rfl) ⟨264852, by rfl⟩ : syracuseStep 2825093 = 529705) (by norm_num)
theorem B2118541 : Blo 1883143 2118541 := bbase (se 3 (by rfl) ⟨397226, by rfl⟩ : syracuseStep 2118541 = 794453) (by norm_num)
theorem B2825117 : Blo 1883143 2825117 := bbase (se 3 (by rfl) ⟨529709, by rfl⟩ : syracuseStep 2825117 = 1059419) (by norm_num)
theorem B2118577 : Blo 1883143 2118577 := bbase (se 2 (by rfl) ⟨794466, by rfl⟩ : syracuseStep 2118577 = 1588933) (by norm_num)
theorem B2825141 : Blo 1883143 2825141 := bbase (se 5 (by rfl) ⟨132428, by rfl⟩ : syracuseStep 2825141 = 264857) (by norm_num)
theorem B2118613 : Blo 1883143 2118613 := bbase (se 7 (by rfl) ⟨24827, by rfl⟩ : syracuseStep 2118613 = 49655) (by norm_num)
theorem B5362661 : Blo 1883143 5362661 := bbase (se 4 (by rfl) ⟨502749, by rfl⟩ : syracuseStep 5362661 = 1005499) (by norm_num)
theorem B2118649 : Blo 1883143 2118649 := bbase (se 2 (by rfl) ⟨794493, by rfl⟩ : syracuseStep 2118649 = 1588987) (by norm_num)
theorem B2118685 : Blo 1883143 2118685 := bbase (se 3 (by rfl) ⟨397253, by rfl⟩ : syracuseStep 2118685 = 794507) (by norm_num)
theorem B2118721 : Blo 1883143 2118721 := bbase (se 2 (by rfl) ⟨794520, by rfl⟩ : syracuseStep 2118721 = 1589041) (by norm_num)
theorem B4766789 : Blo 1883143 4766789 := bbase (se 4 (by rfl) ⟨446886, by rfl⟩ : syracuseStep 4766789 = 893773) (by norm_num)
theorem B6356069 : Blo 1883143 6356069 := bbase (se 4 (by rfl) ⟨595881, by rfl⟩ : syracuseStep 6356069 = 1191763) (by norm_num)
theorem B2118757 : Blo 1883143 2118757 := bbase (se 4 (by rfl) ⟨198633, by rfl⟩ : syracuseStep 2118757 = 397267) (by norm_num)
theorem B2118793 : Blo 1883143 2118793 := bbase (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) (by norm_num)
theorem B2118829 : Blo 1883143 2118829 := bbase (se 3 (by rfl) ⟨397280, by rfl⟩ : syracuseStep 2118829 = 794561) (by norm_num)
theorem B4525237 : Blo 1883143 4525237 := bbase (se 5 (by rfl) ⟨212120, by rfl⟩ : syracuseStep 4525237 = 424241) (by norm_num)
theorem B11453653 : Blo 1883143 11453653 := bbase (se 7 (by rfl) ⟨134222, by rfl⟩ : syracuseStep 11453653 = 268445) (by norm_num)
theorem B3177805 : Blo 1883143 3177805 := bbase (se 3 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 3177805 = 1191677) (by norm_num)
theorem B2262349 : Blo 1883143 2262349 := bbase (se 3 (by rfl) ⟨424190, by rfl⟩ : syracuseStep 2262349 = 848381) (by norm_num)
theorem B4767133 : Blo 1883143 4767133 := bbase (se 3 (by rfl) ⟨893837, by rfl⟩ : syracuseStep 4767133 = 1787675) (by norm_num)
theorem B3177893 : Blo 1883143 3177893 := bbase (se 4 (by rfl) ⟨297927, by rfl⟩ : syracuseStep 3177893 = 595855) (by norm_num)
theorem B4767245 : Blo 1883143 4767245 := bbase (se 3 (by rfl) ⟨893858, by rfl⟩ : syracuseStep 4767245 = 1787717) (by norm_num)
theorem B6356501 : Blo 1883143 6356501 := bbase (se 6 (by rfl) ⟨148980, by rfl⟩ : syracuseStep 6356501 = 297961) (by norm_num)
theorem B7151125 : Blo 1883143 7151125 := bbase (se 6 (by rfl) ⟨167604, by rfl⟩ : syracuseStep 7151125 = 335209) (by norm_num)
theorem B3178021 : Blo 1883143 3178021 := bbase (se 4 (by rfl) ⟨297939, by rfl⟩ : syracuseStep 3178021 = 595879) (by norm_num)
theorem B2383445 : Blo 1883143 2383445 := bbase (se 8 (by rfl) ⟨13965, by rfl⟩ : syracuseStep 2383445 = 27931) (by norm_num)
theorem B3178109 : Blo 1883143 3178109 := bbase (se 3 (by rfl) ⟨595895, by rfl⟩ : syracuseStep 3178109 = 1191791) (by norm_num)
theorem B2383501 : Blo 1883143 2383501 := bbase (se 3 (by rfl) ⟨446906, by rfl⟩ : syracuseStep 2383501 = 893813) (by norm_num)
theorem B8044181 : Blo 1883143 8044181 := bbase (se 6 (by rfl) ⟨188535, by rfl⟩ : syracuseStep 8044181 = 377071) (by norm_num)
theorem B2449073 : Blo 1883143 2449073 := bbase (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) (by norm_num)
theorem B3534517 : Blo 1883143 3534517 := bbase (se 5 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 3534517 = 331361) (by norm_num)
theorem B4767437 : Blo 1883143 4767437 := bbase (se 3 (by rfl) ⟨893894, by rfl⟩ : syracuseStep 4767437 = 1787789) (by norm_num)
theorem B2383597 : Blo 1883143 2383597 := bbase (se 3 (by rfl) ⟨446924, by rfl⟩ : syracuseStep 2383597 = 893849) (by norm_num)
theorem B3178237 : Blo 1883143 3178237 := bbase (se 3 (by rfl) ⟨595919, by rfl⟩ : syracuseStep 3178237 = 1191839) (by norm_num)
theorem B2545429 : Blo 1883143 2545429 := bbase (se 6 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 2545429 = 119317) (by norm_num)
theorem B4237109 : Blo 1883143 4237109 := bbase (se 5 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 4237109 = 397229) (by norm_num)
theorem B4237181 : Blo 1883143 4237181 := bbase (se 3 (by rfl) ⟨794471, by rfl⟩ : syracuseStep 4237181 = 1588943) (by norm_num)
theorem B4237253 : Blo 1883143 4237253 := bbase (se 4 (by rfl) ⟨397242, by rfl⟩ : syracuseStep 4237253 = 794485) (by norm_num)
theorem B9050069 : Blo 1883143 9050069 := bbase (se 7 (by rfl) ⟨106055, by rfl⟩ : syracuseStep 9050069 = 212111) (by norm_num)
theorem B6787061 : Blo 1883143 6787061 := bbase (se 5 (by rfl) ⟨318143, by rfl⟩ : syracuseStep 6787061 = 636287) (by norm_num)
theorem B4413457 : Blo 1883143 4413457 := bstep (se 2 (by rfl) ⟨1655046, by rfl⟩ : syracuseStep 4413457 = 3310093) B3310093
theorem B4237361 : Blo 1883143 4237361 := bstep (se 2 (by rfl) ⟨1589010, by rfl⟩ : syracuseStep 4237361 = 3178021) B3178021
theorem B4237379 : Blo 1883143 4237379 := bstep (se 1 (by rfl) ⟨3178034, by rfl⟩ : syracuseStep 4237379 = 6356069) B6356069
theorem B19859525 : Blo 1883143 19859525 := bstep (se 4 (by rfl) ⟨1861830, by rfl⟩ : syracuseStep 19859525 = 3723661) B3723661
theorem B4712689 : Blo 1883143 4712689 := bstep (se 2 (by rfl) ⟨1767258, by rfl⟩ : syracuseStep 4712689 = 3534517) B3534517
theorem B6033649 : Blo 1883143 6033649 := bstep (se 2 (by rfl) ⟨2262618, by rfl⟩ : syracuseStep 6033649 = 4525237) B4525237
theorem B4237649 : Blo 1883143 4237649 := bstep (se 2 (by rfl) ⟨1589118, by rfl⟩ : syracuseStep 4237649 = 3178237) B3178237
theorem B4237667 : Blo 1883143 4237667 := bstep (se 1 (by rfl) ⟨3178250, by rfl⟩ : syracuseStep 4237667 = 6356501) B6356501
theorem B3393905 : Blo 1883143 3393905 := bstep (se 2 (by rfl) ⟨1272714, by rfl⟩ : syracuseStep 3393905 = 2545429) B2545429
theorem B13574641 : Blo 1883143 13574641 := bstep (se 2 (by rfl) ⟨5090490, by rfl⟩ : syracuseStep 13574641 = 10180981) B10180981
theorem B2824721 : Blo 1883143 2824721 := bstep (se 2 (by rfl) ⟨1059270, by rfl⟩ : syracuseStep 2824721 = 2118541) B2118541
theorem B2824739 : Blo 1883143 2824739 := bstep (se 1 (by rfl) ⟨2118554, by rfl⟩ : syracuseStep 2824739 = 4237109) B4237109
theorem B2824769 : Blo 1883143 2824769 := bstep (se 2 (by rfl) ⟨1059288, by rfl⟩ : syracuseStep 2824769 = 2118577) B2118577
theorem B2824787 : Blo 1883143 2824787 := bstep (se 1 (by rfl) ⟨2118590, by rfl⟩ : syracuseStep 2824787 = 4237181) B4237181
theorem B2824817 : Blo 1883143 2824817 := bstep (se 2 (by rfl) ⟨1059306, by rfl⟩ : syracuseStep 2824817 = 2118613) B2118613
theorem B2824835 : Blo 1883143 2824835 := bstep (se 1 (by rfl) ⟨2118626, by rfl⟩ : syracuseStep 2824835 = 4237253) B4237253
theorem B2824865 : Blo 1883143 2824865 := bstep (se 2 (by rfl) ⟨1059324, by rfl⟩ : syracuseStep 2824865 = 2118649) B2118649
theorem B4524707 : Blo 1883143 4524707 := bstep (se 1 (by rfl) ⟨3393530, by rfl⟩ : syracuseStep 4524707 = 6787061) B6787061
theorem B2824883 : Blo 1883143 2824883 := bstep (se 1 (by rfl) ⟨2118662, by rfl⟩ : syracuseStep 2824883 = 4237325) B4237325
theorem B2824913 : Blo 1883143 2824913 := bstep (se 2 (by rfl) ⟨1059342, by rfl⟩ : syracuseStep 2824913 = 2118685) B2118685
theorem B2824931 : Blo 1883143 2824931 := bstep (se 1 (by rfl) ⟨2118698, by rfl⟩ : syracuseStep 2824931 = 4237397) B4237397
theorem B4524785 : Blo 1883143 4524785 := bstep (se 2 (by rfl) ⟨1696794, by rfl⟩ : syracuseStep 4524785 = 3393589) B3393589
theorem B2824961 : Blo 1883143 2824961 := bstep (se 2 (by rfl) ⟨1059360, by rfl⟩ : syracuseStep 2824961 = 2118721) B2118721
theorem B2824979 : Blo 1883143 2824979 := bstep (se 1 (by rfl) ⟨2118734, by rfl⟩ : syracuseStep 2824979 = 4237469) B4237469
theorem B2825009 : Blo 1883143 2825009 := bstep (se 2 (by rfl) ⟨1059378, by rfl⟩ : syracuseStep 2825009 = 2118757) B2118757
theorem B2825027 : Blo 1883143 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B2825057 : Blo 1883143 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B2825075 : Blo 1883143 2825075 := bstep (se 1 (by rfl) ⟨2118806, by rfl⟩ : syracuseStep 2825075 = 4237613) B4237613
theorem B6355853 : Blo 1883143 6355853 := bstep (se 3 (by rfl) ⟨1191722, by rfl⟩ : syracuseStep 6355853 = 2383445) B2383445
theorem B2825105 : Blo 1883143 2825105 := bstep (se 2 (by rfl) ⟨1059414, by rfl⟩ : syracuseStep 2825105 = 2118829) B2118829
theorem B2825123 : Blo 1883143 2825123 := bstep (se 1 (by rfl) ⟨2118842, by rfl⟩ : syracuseStep 2825123 = 4237685) B4237685
theorem B2118595 : Blo 1883143 2118595 := bstep (se 1 (by rfl) ⟨1588946, by rfl⟩ : syracuseStep 2118595 = 3177893) B3177893
theorem B6355907 : Blo 1883143 6355907 := bstep (se 1 (by rfl) ⟨4766930, by rfl⟩ : syracuseStep 6355907 = 9533861) B9533861
theorem B1883155 : Blo 1883143 1883155 := bstep (se 1 (by rfl) ⟨1412366, by rfl⟩ : syracuseStep 1883155 = 2824733) B2824733
theorem B1883171 : Blo 1883143 1883171 := bstep (se 1 (by rfl) ⟨1412378, by rfl⟩ : syracuseStep 1883171 = 2824757) B2824757
theorem B1883187 : Blo 1883143 1883187 := bstep (se 1 (by rfl) ⟨1412390, by rfl⟩ : syracuseStep 1883187 = 2824781) B2824781
theorem B1883203 : Blo 1883143 1883203 := bstep (se 1 (by rfl) ⟨1412402, by rfl⟩ : syracuseStep 1883203 = 2824805) B2824805
theorem B12065861 : Blo 1883143 12065861 := bstep (se 4 (by rfl) ⟨1131174, by rfl⟩ : syracuseStep 12065861 = 2262349) B2262349
theorem B1883219 : Blo 1883143 1883219 := bstep (se 1 (by rfl) ⟨1412414, by rfl⟩ : syracuseStep 1883219 = 2824829) B2824829
theorem B2118739 : Blo 1883143 2118739 := bstep (se 1 (by rfl) ⟨1589054, by rfl⟩ : syracuseStep 2118739 = 3178109) B3178109
theorem B5362787 : Blo 1883143 5362787 := bstep (se 1 (by rfl) ⟨4022090, by rfl⟩ : syracuseStep 5362787 = 8044181) B8044181
theorem B1883235 : Blo 1883143 1883235 := bstep (se 1 (by rfl) ⟨1412426, by rfl⟩ : syracuseStep 1883235 = 2824853) B2824853
theorem B1883251 : Blo 1883143 1883251 := bstep (se 1 (by rfl) ⟨1412438, by rfl⟩ : syracuseStep 1883251 = 2824877) B2824877
theorem B1883267 : Blo 1883143 1883267 := bstep (se 1 (by rfl) ⟨1412450, by rfl⟩ : syracuseStep 1883267 = 2824901) B2824901
theorem B1883283 : Blo 1883143 1883283 := bstep (se 1 (by rfl) ⟨1412462, by rfl⟩ : syracuseStep 1883283 = 2824925) B2824925
theorem B1883299 : Blo 1883143 1883299 := bstep (se 1 (by rfl) ⟨1412474, by rfl⟩ : syracuseStep 1883299 = 2824949) B2824949
theorem B1883315 : Blo 1883143 1883315 := bstep (se 1 (by rfl) ⟨1412486, by rfl⟩ : syracuseStep 1883315 = 2824973) B2824973
theorem B1883331 : Blo 1883143 1883331 := bstep (se 1 (by rfl) ⟨1412498, by rfl⟩ : syracuseStep 1883331 = 2824997) B2824997
theorem B6356177 : Blo 1883143 6356177 := bstep (se 2 (by rfl) ⟨2383566, by rfl⟩ : syracuseStep 6356177 = 4767133) B4767133
theorem B1883347 : Blo 1883143 1883347 := bstep (se 1 (by rfl) ⟨1412510, by rfl⟩ : syracuseStep 1883347 = 2825021) B2825021
theorem B1883363 : Blo 1883143 1883363 := bstep (se 1 (by rfl) ⟨1412522, by rfl⟩ : syracuseStep 1883363 = 2825045) B2825045
theorem B1883379 : Blo 1883143 1883379 := bstep (se 1 (by rfl) ⟨1412534, by rfl⟩ : syracuseStep 1883379 = 2825069) B2825069
theorem B1883395 : Blo 1883143 1883395 := bstep (se 1 (by rfl) ⟨1412546, by rfl⟩ : syracuseStep 1883395 = 2825093) B2825093
theorem B1883411 : Blo 1883143 1883411 := bstep (se 1 (by rfl) ⟨1412558, by rfl⟩ : syracuseStep 1883411 = 2825117) B2825117
theorem B1883427 : Blo 1883143 1883427 := bstep (se 1 (by rfl) ⟨1412570, by rfl⟩ : syracuseStep 1883427 = 2825141) B2825141
theorem B3575107 : Blo 1883143 3575107 := bstep (se 1 (by rfl) ⟨2681330, by rfl⟩ : syracuseStep 3575107 = 5362661) B5362661
theorem B20362565 : Blo 1883143 20362565 := bstep (se 4 (by rfl) ⟨1908990, by rfl⟩ : syracuseStep 20362565 = 3817981) B3817981
theorem B3575153 : Blo 1883143 3575153 := bstep (se 2 (by rfl) ⟨1340682, by rfl⟩ : syracuseStep 3575153 = 2681365) B2681365
theorem B9534833 : Blo 1883143 9534833 := bstep (se 2 (by rfl) ⟨3575562, by rfl⟩ : syracuseStep 9534833 = 7151125) B7151125
theorem B3177859 : Blo 1883143 3177859 := bstep (se 1 (by rfl) ⟨2383394, by rfl⟩ : syracuseStep 3177859 = 4766789) B4766789
theorem B5363117 : Blo 1883143 5363117 := bstep (se 3 (by rfl) ⟨1005584, by rfl⟩ : syracuseStep 5363117 = 2011169) B2011169
theorem B5363185 : Blo 1883143 5363185 := bstep (se 2 (by rfl) ⟨2011194, by rfl⟩ : syracuseStep 5363185 = 4022389) B4022389
theorem B3178001 : Blo 1883143 3178001 := bstep (se 2 (by rfl) ⟨1191750, by rfl⟩ : syracuseStep 3178001 = 2383501) B2383501
theorem B15271537 : Blo 1883143 15271537 := bstep (se 2 (by rfl) ⟨5726826, by rfl⟩ : syracuseStep 15271537 = 11453653) B11453653
theorem B3178129 : Blo 1883143 3178129 := bstep (se 2 (by rfl) ⟨1191798, by rfl⟩ : syracuseStep 3178129 = 2383597) B2383597
theorem B3575441 : Blo 1883143 3575441 := bstep (se 2 (by rfl) ⟨1340790, by rfl⟩ : syracuseStep 3575441 = 2681581) B2681581
theorem B3178163 : Blo 1883143 3178163 := bstep (se 1 (by rfl) ⟨2383622, by rfl⟩ : syracuseStep 3178163 = 4767245) B4767245
theorem B4237073 : Blo 1883143 4237073 := bstep (se 2 (by rfl) ⟨1588902, by rfl⟩ : syracuseStep 4237073 = 3177805) B3177805
theorem B4237091 : Blo 1883143 4237091 := bstep (se 1 (by rfl) ⟨3177818, by rfl⟩ : syracuseStep 4237091 = 6355637) B6355637
theorem B6530861 : Blo 1883143 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B3178291 : Blo 1883143 3178291 := bstep (se 1 (by rfl) ⟨2383718, by rfl⟩ : syracuseStep 3178291 = 4767437) B4767437
theorem B2545489 : Blo 1883143 2545489 := bstep (se 2 (by rfl) ⟨954558, by rfl⟩ : syracuseStep 2545489 = 1909117) B1909117
theorem B6033379 : Blo 1883143 6033379 := bstep (se 1 (by rfl) ⟨4525034, by rfl⟩ : syracuseStep 6033379 = 9050069) B9050069
theorem B4237451 : Blo 1883143 4237451 := bstep (se 1 (by rfl) ⟨3178088, by rfl⟩ : syracuseStep 4237451 = 6356177) B6356177
theorem B4237505 : Blo 1883143 4237505 := bstep (se 2 (by rfl) ⟨1589064, by rfl⟩ : syracuseStep 4237505 = 3178129) B3178129
theorem B6283585 : Blo 1883143 6283585 := bstep (se 2 (by rfl) ⟨2356344, by rfl⟩ : syracuseStep 6283585 = 4712689) B4712689
theorem B8044865 : Blo 1883143 8044865 := bstep (se 2 (by rfl) ⟨3016824, by rfl⟩ : syracuseStep 8044865 = 6033649) B6033649
theorem B4237721 : Blo 1883143 4237721 := bstep (se 2 (by rfl) ⟨1589145, by rfl⟩ : syracuseStep 4237721 = 3178291) B3178291
theorem B3393985 : Blo 1883143 3393985 := bstep (se 2 (by rfl) ⟨1272744, by rfl⟩ : syracuseStep 3393985 = 2545489) B2545489
theorem B2824715 : Blo 1883143 2824715 := bstep (se 1 (by rfl) ⟨2118536, by rfl⟩ : syracuseStep 2824715 = 4237073) B4237073
theorem B2824727 : Blo 1883143 2824727 := bstep (se 1 (by rfl) ⟨2118545, by rfl⟩ : syracuseStep 2824727 = 4237091) B4237091
theorem B2824793 : Blo 1883143 2824793 := bstep (se 2 (by rfl) ⟨1059297, by rfl⟩ : syracuseStep 2824793 = 2118595) B2118595
theorem B2824907 : Blo 1883143 2824907 := bstep (se 1 (by rfl) ⟨2118680, by rfl⟩ : syracuseStep 2824907 = 4237361) B4237361
theorem B2824919 : Blo 1883143 2824919 := bstep (se 1 (by rfl) ⟨2118689, by rfl⟩ : syracuseStep 2824919 = 4237379) B4237379
theorem B23538437 : Blo 1883143 23538437 := bstep (se 4 (by rfl) ⟨2206728, by rfl⟩ : syracuseStep 23538437 = 4413457) B4413457
theorem B2824985 : Blo 1883143 2824985 := bstep (se 2 (by rfl) ⟨1059369, by rfl⟩ : syracuseStep 2824985 = 2118739) B2118739
theorem B20362049 : Blo 1883143 20362049 := bstep (se 2 (by rfl) ⟨7635768, by rfl⟩ : syracuseStep 20362049 = 15271537) B15271537
theorem B13575043 : Blo 1883143 13575043 := bstep (se 1 (by rfl) ⟨10181282, by rfl⟩ : syracuseStep 13575043 = 20362565) B20362565
theorem B2825099 : Blo 1883143 2825099 := bstep (se 1 (by rfl) ⟨2118824, by rfl⟩ : syracuseStep 2825099 = 4237649) B4237649
theorem B2825111 : Blo 1883143 2825111 := bstep (se 1 (by rfl) ⟨2118833, by rfl⟩ : syracuseStep 2825111 = 4237667) B4237667
theorem B1883147 : Blo 1883143 1883147 := bstep (se 1 (by rfl) ⟨1412360, by rfl⟩ : syracuseStep 1883147 = 2824721) B2824721
theorem B2118667 : Blo 1883143 2118667 := bstep (se 1 (by rfl) ⟨1589000, by rfl⟩ : syracuseStep 2118667 = 3178001) B3178001
theorem B1883159 : Blo 1883143 1883159 := bstep (se 1 (by rfl) ⟨1412369, by rfl⟩ : syracuseStep 1883159 = 2824739) B2824739
theorem B1883179 : Blo 1883143 1883179 := bstep (se 1 (by rfl) ⟨1412384, by rfl⟩ : syracuseStep 1883179 = 2824769) B2824769
theorem B9534509 : Blo 1883143 9534509 := bstep (se 3 (by rfl) ⟨1787720, by rfl⟩ : syracuseStep 9534509 = 3575441) B3575441
theorem B1883191 : Blo 1883143 1883191 := bstep (se 1 (by rfl) ⟨1412393, by rfl⟩ : syracuseStep 1883191 = 2824787) B2824787
theorem B1883211 : Blo 1883143 1883211 := bstep (se 1 (by rfl) ⟨1412408, by rfl⟩ : syracuseStep 1883211 = 2824817) B2824817
theorem B1883223 : Blo 1883143 1883223 := bstep (se 1 (by rfl) ⟨1412417, by rfl⟩ : syracuseStep 1883223 = 2824835) B2824835
theorem B4766809 : Blo 1883143 4766809 := bstep (se 2 (by rfl) ⟨1787553, by rfl⟩ : syracuseStep 4766809 = 3575107) B3575107
theorem B12065885 : Blo 1883143 12065885 := bstep (se 3 (by rfl) ⟨2262353, by rfl⟩ : syracuseStep 12065885 = 4524707) B4524707
theorem B1883243 : Blo 1883143 1883243 := bstep (se 1 (by rfl) ⟨1412432, by rfl⟩ : syracuseStep 1883243 = 2824865) B2824865
theorem B1883255 : Blo 1883143 1883255 := bstep (se 1 (by rfl) ⟨1412441, by rfl⟩ : syracuseStep 1883255 = 2824883) B2824883
theorem B2118775 : Blo 1883143 2118775 := bstep (se 1 (by rfl) ⟨1589081, by rfl⟩ : syracuseStep 2118775 = 3178163) B3178163
theorem B1883275 : Blo 1883143 1883275 := bstep (se 1 (by rfl) ⟨1412456, by rfl⟩ : syracuseStep 1883275 = 2824913) B2824913
theorem B1883287 : Blo 1883143 1883287 := bstep (se 1 (by rfl) ⟨1412465, by rfl⟩ : syracuseStep 1883287 = 2824931) B2824931
theorem B1883307 : Blo 1883143 1883307 := bstep (se 1 (by rfl) ⟨1412480, by rfl⟩ : syracuseStep 1883307 = 2824961) B2824961
theorem B36201653 : Blo 1883143 36201653 := bstep (se 5 (by rfl) ⟨1696952, by rfl⟩ : syracuseStep 36201653 = 3393905) B3393905
theorem B1883319 : Blo 1883143 1883319 := bstep (se 1 (by rfl) ⟨1412489, by rfl⟩ : syracuseStep 1883319 = 2824979) B2824979
theorem B1883339 : Blo 1883143 1883339 := bstep (se 1 (by rfl) ⟨1412504, by rfl⟩ : syracuseStep 1883339 = 2825009) B2825009
theorem B1883351 : Blo 1883143 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B1883371 : Blo 1883143 1883371 := bstep (se 1 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 1883371 = 2825057) B2825057
theorem B1883383 : Blo 1883143 1883383 := bstep (se 1 (by rfl) ⟨1412537, by rfl⟩ : syracuseStep 1883383 = 2825075) B2825075
theorem B1883403 : Blo 1883143 1883403 := bstep (se 1 (by rfl) ⟨1412552, by rfl⟩ : syracuseStep 1883403 = 2825105) B2825105
theorem B1883415 : Blo 1883143 1883415 := bstep (se 1 (by rfl) ⟨1412561, by rfl⟩ : syracuseStep 1883415 = 2825123) B2825123
theorem B18099521 : Blo 1883143 18099521 := bstep (se 2 (by rfl) ⟨6787320, by rfl⟩ : syracuseStep 18099521 = 13574641) B13574641
theorem B7150913 : Blo 1883143 7150913 := bstep (se 2 (by rfl) ⟨2681592, by rfl⟩ : syracuseStep 7150913 = 5363185) B5363185
theorem B8043907 : Blo 1883143 8043907 := bstep (se 1 (by rfl) ⟨6032930, by rfl⟩ : syracuseStep 8043907 = 12065861) B12065861
theorem B13239683 : Blo 1883143 13239683 := bstep (se 1 (by rfl) ⟨9929762, by rfl⟩ : syracuseStep 13239683 = 19859525) B19859525
theorem B3575191 : Blo 1883143 3575191 := bstep (se 1 (by rfl) ⟨2681393, by rfl⟩ : syracuseStep 3575191 = 5362787) B5362787
theorem B2383435 : Blo 1883143 2383435 := bstep (se 1 (by rfl) ⟨1787576, by rfl⟩ : syracuseStep 2383435 = 3575153) B3575153
theorem B6356555 : Blo 1883143 6356555 := bstep (se 1 (by rfl) ⟨4767416, by rfl⟩ : syracuseStep 6356555 = 9534833) B9534833
theorem B3575411 : Blo 1883143 3575411 := bstep (se 1 (by rfl) ⟨2681558, by rfl⟩ : syracuseStep 3575411 = 5363117) B5363117
theorem B3016523 : Blo 1883143 3016523 := bstep (se 1 (by rfl) ⟨2262392, by rfl⟩ : syracuseStep 3016523 = 4524785) B4524785
theorem B4237145 : Blo 1883143 4237145 := bstep (se 2 (by rfl) ⟨1588929, by rfl⟩ : syracuseStep 4237145 = 3177859) B3177859
theorem B4353907 : Blo 1883143 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B4237235 : Blo 1883143 4237235 := bstep (se 1 (by rfl) ⟨3177926, by rfl⟩ : syracuseStep 4237235 = 6355853) B6355853
theorem B4237271 : Blo 1883143 4237271 := bstep (se 1 (by rfl) ⟨3177953, by rfl⟩ : syracuseStep 4237271 = 6355907) B6355907
theorem B8044505 : Blo 1883143 8044505 := bstep (se 2 (by rfl) ⟨3016689, by rfl⟩ : syracuseStep 8044505 = 6033379) B6033379
theorem B4237703 : Blo 1883143 4237703 := bstep (se 1 (by rfl) ⟨3178277, by rfl⟩ : syracuseStep 4237703 = 6356555) B6356555
theorem B15692291 : Blo 1883143 15692291 := bstep (se 1 (by rfl) ⟨11769218, by rfl⟩ : syracuseStep 15692291 = 23538437) B23538437
theorem B13574699 : Blo 1883143 13574699 := bstep (se 1 (by rfl) ⟨10181024, by rfl⟩ : syracuseStep 13574699 = 20362049) B20362049
theorem B2824763 : Blo 1883143 2824763 := bstep (se 1 (by rfl) ⟨2118572, by rfl⟩ : syracuseStep 2824763 = 4237145) B4237145
theorem B2824823 : Blo 1883143 2824823 := bstep (se 1 (by rfl) ⟨2118617, by rfl⟩ : syracuseStep 2824823 = 4237235) B4237235
theorem B2824847 : Blo 1883143 2824847 := bstep (se 1 (by rfl) ⟨2118635, by rfl⟩ : syracuseStep 2824847 = 4237271) B4237271
theorem B2824889 : Blo 1883143 2824889 := bstep (se 2 (by rfl) ⟨1059333, by rfl⟩ : syracuseStep 2824889 = 2118667) B2118667
theorem B2824967 : Blo 1883143 2824967 := bstep (se 1 (by rfl) ⟨2118725, by rfl⟩ : syracuseStep 2824967 = 4237451) B4237451
theorem B6355745 : Blo 1883143 6355745 := bstep (se 2 (by rfl) ⟨2383404, by rfl⟩ : syracuseStep 6355745 = 4766809) B4766809
theorem B24134435 : Blo 1883143 24134435 := bstep (se 1 (by rfl) ⟨18100826, by rfl⟩ : syracuseStep 24134435 = 36201653) B36201653
theorem B2825003 : Blo 1883143 2825003 := bstep (se 1 (by rfl) ⟨2118752, by rfl⟩ : syracuseStep 2825003 = 4237505) B4237505
theorem B2825033 : Blo 1883143 2825033 := bstep (se 2 (by rfl) ⟨1059387, by rfl⟩ : syracuseStep 2825033 = 2118775) B2118775
theorem B2825147 : Blo 1883143 2825147 := bstep (se 1 (by rfl) ⟨2118860, by rfl⟩ : syracuseStep 2825147 = 4237721) B4237721
theorem B1883143 : Blo 1883143 1883143 := bstep (se 1 (by rfl) ⟨1412357, by rfl⟩ : syracuseStep 1883143 = 2824715) B2824715
theorem B1883151 : Blo 1883143 1883151 := bstep (se 1 (by rfl) ⟨1412363, by rfl⟩ : syracuseStep 1883151 = 2824727) B2824727
theorem B1883195 : Blo 1883143 1883195 := bstep (se 1 (by rfl) ⟨1412396, by rfl⟩ : syracuseStep 1883195 = 2824793) B2824793
theorem B1883271 : Blo 1883143 1883271 := bstep (se 1 (by rfl) ⟨1412453, by rfl⟩ : syracuseStep 1883271 = 2824907) B2824907
theorem B1883279 : Blo 1883143 1883279 := bstep (se 1 (by rfl) ⟨1412459, by rfl⟩ : syracuseStep 1883279 = 2824919) B2824919
theorem B5805209 : Blo 1883143 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B1883323 : Blo 1883143 1883323 := bstep (se 1 (by rfl) ⟨1412492, by rfl⟩ : syracuseStep 1883323 = 2824985) B2824985
theorem B4766921 : Blo 1883143 4766921 := bstep (se 2 (by rfl) ⟨1787595, by rfl⟩ : syracuseStep 4766921 = 3575191) B3575191
theorem B4525313 : Blo 1883143 4525313 := bstep (se 2 (by rfl) ⟨1696992, by rfl⟩ : syracuseStep 4525313 = 3393985) B3393985
theorem B1883399 : Blo 1883143 1883399 := bstep (se 1 (by rfl) ⟨1412549, by rfl⟩ : syracuseStep 1883399 = 2825099) B2825099
theorem B1883407 : Blo 1883143 1883407 := bstep (se 1 (by rfl) ⟨1412555, by rfl⟩ : syracuseStep 1883407 = 2825111) B2825111
theorem B5363003 : Blo 1883143 5363003 := bstep (se 1 (by rfl) ⟨4022252, by rfl⟩ : syracuseStep 5363003 = 8044505) B8044505
theorem B6356339 : Blo 1883143 6356339 := bstep (se 1 (by rfl) ⟨4767254, by rfl⟩ : syracuseStep 6356339 = 9534509) B9534509
theorem B8043923 : Blo 1883143 8043923 := bstep (se 1 (by rfl) ⟨6032942, by rfl⟩ : syracuseStep 8043923 = 12065885) B12065885
theorem B3177913 : Blo 1883143 3177913 := bstep (se 2 (by rfl) ⟨1191717, by rfl⟩ : syracuseStep 3177913 = 2383435) B2383435
theorem B12066347 : Blo 1883143 12066347 := bstep (se 1 (by rfl) ⟨9049760, by rfl⟩ : syracuseStep 12066347 = 18099521) B18099521
theorem B4767275 : Blo 1883143 4767275 := bstep (se 1 (by rfl) ⟨3575456, by rfl⟩ : syracuseStep 4767275 = 7150913) B7150913
theorem B5363243 : Blo 1883143 5363243 := bstep (se 1 (by rfl) ⟨4022432, by rfl⟩ : syracuseStep 5363243 = 8044865) B8044865
theorem B8826455 : Blo 1883143 8826455 := bstep (se 1 (by rfl) ⟨6619841, by rfl⟩ : syracuseStep 8826455 = 13239683) B13239683
theorem B2383607 : Blo 1883143 2383607 := bstep (se 1 (by rfl) ⟨1787705, by rfl⟩ : syracuseStep 2383607 = 3575411) B3575411
theorem B8378113 : Blo 1883143 8378113 := bstep (se 2 (by rfl) ⟨3141792, by rfl⟩ : syracuseStep 8378113 = 6283585) B6283585
theorem B10725209 : Blo 1883143 10725209 := bstep (se 2 (by rfl) ⟨4021953, by rfl⟩ : syracuseStep 10725209 = 8043907) B8043907
theorem B18100057 : Blo 1883143 18100057 := bstep (se 2 (by rfl) ⟨6787521, by rfl⟩ : syracuseStep 18100057 = 13575043) B13575043
theorem B2011015 : Blo 1883143 2011015 := bstep (se 1 (by rfl) ⟨1508261, by rfl⟩ : syracuseStep 2011015 = 3016523) B3016523
theorem B4237559 : Blo 1883143 4237559 := bstep (se 1 (by rfl) ⟨3178169, by rfl⟩ : syracuseStep 4237559 = 6356339) B6356339
theorem B10461527 : Blo 1883143 10461527 := bstep (se 1 (by rfl) ⟨7846145, by rfl⟩ : syracuseStep 10461527 = 15692291) B15692291
theorem B2681353 : Blo 1883143 2681353 := bstep (se 2 (by rfl) ⟨1005507, by rfl⟩ : syracuseStep 2681353 = 2011015) B2011015
theorem B16089623 : Blo 1883143 16089623 := bstep (se 1 (by rfl) ⟨12067217, by rfl⟩ : syracuseStep 16089623 = 24134435) B24134435
theorem B7150139 : Blo 1883143 7150139 := bstep (se 1 (by rfl) ⟨5362604, by rfl⟩ : syracuseStep 7150139 = 10725209) B10725209
theorem B12067501 : Blo 1883143 12067501 := bstep (se 3 (by rfl) ⟨2262656, by rfl⟩ : syracuseStep 12067501 = 4525313) B4525313
theorem B2825135 : Blo 1883143 2825135 := bstep (se 1 (by rfl) ⟨2118851, by rfl⟩ : syracuseStep 2825135 = 4237703) B4237703
theorem B5362615 : Blo 1883143 5362615 := bstep (se 1 (by rfl) ⟨4021961, by rfl⟩ : syracuseStep 5362615 = 8043923) B8043923
theorem B11170817 : Blo 1883143 11170817 := bstep (se 2 (by rfl) ⟨4189056, by rfl⟩ : syracuseStep 11170817 = 8378113) B8378113
theorem B1883175 : Blo 1883143 1883175 := bstep (se 1 (by rfl) ⟨1412381, by rfl⟩ : syracuseStep 1883175 = 2824763) B2824763
theorem B1883215 : Blo 1883143 1883215 := bstep (se 1 (by rfl) ⟨1412411, by rfl⟩ : syracuseStep 1883215 = 2824823) B2824823
theorem B1883231 : Blo 1883143 1883231 := bstep (se 1 (by rfl) ⟨1412423, by rfl⟩ : syracuseStep 1883231 = 2824847) B2824847
theorem B1883259 : Blo 1883143 1883259 := bstep (se 1 (by rfl) ⟨1412444, by rfl⟩ : syracuseStep 1883259 = 2824889) B2824889
theorem B1883311 : Blo 1883143 1883311 := bstep (se 1 (by rfl) ⟨1412483, by rfl⟩ : syracuseStep 1883311 = 2824967) B2824967
theorem B1883335 : Blo 1883143 1883335 := bstep (se 1 (by rfl) ⟨1412501, by rfl⟩ : syracuseStep 1883335 = 2825003) B2825003
theorem B1883355 : Blo 1883143 1883355 := bstep (se 1 (by rfl) ⟨1412516, by rfl⟩ : syracuseStep 1883355 = 2825033) B2825033
theorem B1883431 : Blo 1883143 1883431 := bstep (se 1 (by rfl) ⟨1412573, by rfl⟩ : syracuseStep 1883431 = 2825147) B2825147
theorem B6356285 : Blo 1883143 6356285 := bstep (se 3 (by rfl) ⟨1191803, by rfl⟩ : syracuseStep 6356285 = 2383607) B2383607
theorem B3177947 : Blo 1883143 3177947 := bstep (se 1 (by rfl) ⟨2383460, by rfl⟩ : syracuseStep 3177947 = 4766921) B4766921
theorem B3575335 : Blo 1883143 3575335 := bstep (se 1 (by rfl) ⟨2681501, by rfl⟩ : syracuseStep 3575335 = 5363003) B5363003
theorem B23537213 : Blo 1883143 23537213 := bstep (se 3 (by rfl) ⟨4413227, by rfl⟩ : syracuseStep 23537213 = 8826455) B8826455
theorem B8044231 : Blo 1883143 8044231 := bstep (se 1 (by rfl) ⟨6033173, by rfl⟩ : syracuseStep 8044231 = 12066347) B12066347
theorem B9049799 : Blo 1883143 9049799 := bstep (se 1 (by rfl) ⟨6787349, by rfl⟩ : syracuseStep 9049799 = 13574699) B13574699
theorem B3178183 : Blo 1883143 3178183 := bstep (se 1 (by rfl) ⟨2383637, by rfl⟩ : syracuseStep 3178183 = 4767275) B4767275
theorem B3575495 : Blo 1883143 3575495 := bstep (se 1 (by rfl) ⟨2681621, by rfl⟩ : syracuseStep 3575495 = 5363243) B5363243
theorem B15480557 : Blo 1883143 15480557 := bstep (se 3 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 15480557 = 5805209) B5805209
theorem B24133409 : Blo 1883143 24133409 := bstep (se 2 (by rfl) ⟨9050028, by rfl⟩ : syracuseStep 24133409 = 18100057) B18100057
theorem B4237163 : Blo 1883143 4237163 := bstep (se 1 (by rfl) ⟨3177872, by rfl⟩ : syracuseStep 4237163 = 6355745) B6355745
theorem B4237217 : Blo 1883143 4237217 := bstep (se 2 (by rfl) ⟨1588956, by rfl⟩ : syracuseStep 4237217 = 3177913) B3177913
theorem B4237523 : Blo 1883143 4237523 := bstep (se 1 (by rfl) ⟨3178142, by rfl⟩ : syracuseStep 4237523 = 6356285) B6356285
theorem B10725641 : Blo 1883143 10725641 := bstep (se 2 (by rfl) ⟨4022115, by rfl⟩ : syracuseStep 10725641 = 8044231) B8044231
theorem B4237577 : Blo 1883143 4237577 := bstep (se 2 (by rfl) ⟨1589091, by rfl⟩ : syracuseStep 4237577 = 3178183) B3178183
theorem B10320371 : Blo 1883143 10320371 := bstep (se 1 (by rfl) ⟨7740278, by rfl⟩ : syracuseStep 10320371 = 15480557) B15480557
theorem B2824775 : Blo 1883143 2824775 := bstep (se 1 (by rfl) ⟨2118581, by rfl⟩ : syracuseStep 2824775 = 4237163) B4237163
theorem B7150153 : Blo 1883143 7150153 := bstep (se 2 (by rfl) ⟨2681307, by rfl⟩ : syracuseStep 7150153 = 5362615) B5362615
theorem B2824811 : Blo 1883143 2824811 := bstep (se 1 (by rfl) ⟨2118608, by rfl⟩ : syracuseStep 2824811 = 4237217) B4237217
theorem B7447211 : Blo 1883143 7447211 := bstep (se 1 (by rfl) ⟨5585408, by rfl⟩ : syracuseStep 7447211 = 11170817) B11170817
theorem B2825039 : Blo 1883143 2825039 := bstep (se 1 (by rfl) ⟨2118779, by rfl⟩ : syracuseStep 2825039 = 4237559) B4237559
theorem B6974351 : Blo 1883143 6974351 := bstep (se 1 (by rfl) ⟨5230763, by rfl⟩ : syracuseStep 6974351 = 10461527) B10461527
theorem B16090001 : Blo 1883143 16090001 := bstep (se 2 (by rfl) ⟨6033750, by rfl⟩ : syracuseStep 16090001 = 12067501) B12067501
theorem B2118631 : Blo 1883143 2118631 := bstep (se 1 (by rfl) ⟨1588973, by rfl⟩ : syracuseStep 2118631 = 3177947) B3177947
theorem B10726415 : Blo 1883143 10726415 := bstep (se 1 (by rfl) ⟨8044811, by rfl⟩ : syracuseStep 10726415 = 16089623) B16089623
theorem B4766759 : Blo 1883143 4766759 := bstep (se 1 (by rfl) ⟨3575069, by rfl⟩ : syracuseStep 4766759 = 7150139) B7150139
theorem B1883423 : Blo 1883143 1883423 := bstep (se 1 (by rfl) ⟨1412567, by rfl⟩ : syracuseStep 1883423 = 2825135) B2825135
theorem B14300549 : Blo 1883143 14300549 := bstep (se 4 (by rfl) ⟨1340676, by rfl⟩ : syracuseStep 14300549 = 2681353) B2681353
theorem B4767113 : Blo 1883143 4767113 := bstep (se 2 (by rfl) ⟨1787667, by rfl⟩ : syracuseStep 4767113 = 3575335) B3575335
theorem B15691475 : Blo 1883143 15691475 := bstep (se 1 (by rfl) ⟨11768606, by rfl⟩ : syracuseStep 15691475 = 23537213) B23537213
theorem B6033199 : Blo 1883143 6033199 := bstep (se 1 (by rfl) ⟨4524899, by rfl⟩ : syracuseStep 6033199 = 9049799) B9049799
theorem B2383663 : Blo 1883143 2383663 := bstep (se 1 (by rfl) ⟨1787747, by rfl⟩ : syracuseStep 2383663 = 3575495) B3575495
theorem B16088939 : Blo 1883143 16088939 := bstep (se 1 (by rfl) ⟨12066704, by rfl⟩ : syracuseStep 16088939 = 24133409) B24133409
theorem B9533537 : Blo 1883143 9533537 := bstep (se 2 (by rfl) ⟨3575076, by rfl⟩ : syracuseStep 9533537 = 7150153) B7150153
theorem B9533699 : Blo 1883143 9533699 := bstep (se 1 (by rfl) ⟨7150274, by rfl⟩ : syracuseStep 9533699 = 14300549) B14300549
theorem B4964807 : Blo 1883143 4964807 := bstep (se 1 (by rfl) ⟨3723605, by rfl⟩ : syracuseStep 4964807 = 7447211) B7447211
theorem B10725959 : Blo 1883143 10725959 := bstep (se 1 (by rfl) ⟨8044469, by rfl⟩ : syracuseStep 10725959 = 16088939) B16088939
theorem B4649567 : Blo 1883143 4649567 := bstep (se 1 (by rfl) ⟨3487175, by rfl⟩ : syracuseStep 4649567 = 6974351) B6974351
theorem B2824841 : Blo 1883143 2824841 := bstep (se 2 (by rfl) ⟨1059315, by rfl⟩ : syracuseStep 2824841 = 2118631) B2118631
theorem B2825015 : Blo 1883143 2825015 := bstep (se 1 (by rfl) ⟨2118761, by rfl⟩ : syracuseStep 2825015 = 4237523) B4237523
theorem B7150427 : Blo 1883143 7150427 := bstep (se 1 (by rfl) ⟨5362820, by rfl⟩ : syracuseStep 7150427 = 10725641) B10725641
theorem B2825051 : Blo 1883143 2825051 := bstep (se 1 (by rfl) ⟨2118788, by rfl⟩ : syracuseStep 2825051 = 4237577) B4237577
theorem B6880247 : Blo 1883143 6880247 := bstep (se 1 (by rfl) ⟨5160185, by rfl⟩ : syracuseStep 6880247 = 10320371) B10320371
theorem B1883183 : Blo 1883143 1883183 := bstep (se 1 (by rfl) ⟨1412387, by rfl⟩ : syracuseStep 1883183 = 2824775) B2824775
theorem B1883207 : Blo 1883143 1883207 := bstep (se 1 (by rfl) ⟨1412405, by rfl⟩ : syracuseStep 1883207 = 2824811) B2824811
theorem B1883359 : Blo 1883143 1883359 := bstep (se 1 (by rfl) ⟨1412519, by rfl⟩ : syracuseStep 1883359 = 2825039) B2825039
theorem B10726667 : Blo 1883143 10726667 := bstep (se 1 (by rfl) ⟨8045000, by rfl⟩ : syracuseStep 10726667 = 16090001) B16090001
theorem B7150943 : Blo 1883143 7150943 := bstep (se 1 (by rfl) ⟨5363207, by rfl⟩ : syracuseStep 7150943 = 10726415) B10726415
theorem B3177839 : Blo 1883143 3177839 := bstep (se 1 (by rfl) ⟨2383379, by rfl⟩ : syracuseStep 3177839 = 4766759) B4766759
theorem B3178075 : Blo 1883143 3178075 := bstep (se 1 (by rfl) ⟨2383556, by rfl⟩ : syracuseStep 3178075 = 4767113) B4767113
theorem B8044265 : Blo 1883143 8044265 := bstep (se 2 (by rfl) ⟨3016599, by rfl⟩ : syracuseStep 8044265 = 6033199) B6033199
theorem B3178217 : Blo 1883143 3178217 := bstep (se 2 (by rfl) ⟨1191831, by rfl⟩ : syracuseStep 3178217 = 2383663) B2383663
theorem B10460983 : Blo 1883143 10460983 := bstep (se 1 (by rfl) ⟨7845737, by rfl⟩ : syracuseStep 10460983 = 15691475) B15691475
theorem B4237433 : Blo 1883143 4237433 := bstep (se 2 (by rfl) ⟨1589037, by rfl⟩ : syracuseStep 4237433 = 3178075) B3178075
theorem B12398845 : Blo 1883143 12398845 := bstep (se 3 (by rfl) ⟨2324783, by rfl⟩ : syracuseStep 12398845 = 4649567) B4649567
theorem B3309871 : Blo 1883143 3309871 := bstep (se 1 (by rfl) ⟨2482403, by rfl⟩ : syracuseStep 3309871 = 4964807) B4964807
theorem B6355691 : Blo 1883143 6355691 := bstep (se 1 (by rfl) ⟨4766768, by rfl⟩ : syracuseStep 6355691 = 9533537) B9533537
theorem B6355799 : Blo 1883143 6355799 := bstep (se 1 (by rfl) ⟨4766849, by rfl⟩ : syracuseStep 6355799 = 9533699) B9533699
theorem B2118559 : Blo 1883143 2118559 := bstep (se 1 (by rfl) ⟨1588919, by rfl⟩ : syracuseStep 2118559 = 3177839) B3177839
theorem B7150639 : Blo 1883143 7150639 := bstep (se 1 (by rfl) ⟨5362979, by rfl⟩ : syracuseStep 7150639 = 10725959) B10725959
theorem B13947977 : Blo 1883143 13947977 := bstep (se 2 (by rfl) ⟨5230491, by rfl⟩ : syracuseStep 13947977 = 10460983) B10460983
theorem B1883227 : Blo 1883143 1883227 := bstep (se 1 (by rfl) ⟨1412420, by rfl⟩ : syracuseStep 1883227 = 2824841) B2824841
theorem B5362843 : Blo 1883143 5362843 := bstep (se 1 (by rfl) ⟨4022132, by rfl⟩ : syracuseStep 5362843 = 8044265) B8044265
theorem B2118811 : Blo 1883143 2118811 := bstep (se 1 (by rfl) ⟨1589108, by rfl⟩ : syracuseStep 2118811 = 3178217) B3178217
theorem B1883343 : Blo 1883143 1883343 := bstep (se 1 (by rfl) ⟨1412507, by rfl⟩ : syracuseStep 1883343 = 2825015) B2825015
theorem B4766951 : Blo 1883143 4766951 := bstep (se 1 (by rfl) ⟨3575213, by rfl⟩ : syracuseStep 4766951 = 7150427) B7150427
theorem B1883367 : Blo 1883143 1883367 := bstep (se 1 (by rfl) ⟨1412525, by rfl⟩ : syracuseStep 1883367 = 2825051) B2825051
theorem B4586831 : Blo 1883143 4586831 := bstep (se 1 (by rfl) ⟨3440123, by rfl⟩ : syracuseStep 4586831 = 6880247) B6880247
theorem B7151111 : Blo 1883143 7151111 := bstep (se 1 (by rfl) ⟨5363333, by rfl⟩ : syracuseStep 7151111 = 10726667) B10726667
theorem B4767295 : Blo 1883143 4767295 := bstep (se 1 (by rfl) ⟨3575471, by rfl⟩ : syracuseStep 4767295 = 7150943) B7150943
theorem B3057887 : Blo 1883143 3057887 := bstep (se 1 (by rfl) ⟨2293415, by rfl⟩ : syracuseStep 3057887 = 4586831) B4586831
theorem B16531793 : Blo 1883143 16531793 := bstep (se 2 (by rfl) ⟨6199422, by rfl⟩ : syracuseStep 16531793 = 12398845) B12398845
theorem B2824745 : Blo 1883143 2824745 := bstep (se 2 (by rfl) ⟨1059279, by rfl⟩ : syracuseStep 2824745 = 2118559) B2118559
theorem B9298651 : Blo 1883143 9298651 := bstep (se 1 (by rfl) ⟨6973988, by rfl⟩ : syracuseStep 9298651 = 13947977) B13947977
theorem B9534185 : Blo 1883143 9534185 := bstep (se 2 (by rfl) ⟨3575319, by rfl⟩ : syracuseStep 9534185 = 7150639) B7150639
theorem B2824955 : Blo 1883143 2824955 := bstep (se 1 (by rfl) ⟨2118716, by rfl⟩ : syracuseStep 2824955 = 4237433) B4237433
theorem B7150457 : Blo 1883143 7150457 := bstep (se 2 (by rfl) ⟨2681421, by rfl⟩ : syracuseStep 7150457 = 5362843) B5362843
theorem B2825081 : Blo 1883143 2825081 := bstep (se 2 (by rfl) ⟨1059405, by rfl⟩ : syracuseStep 2825081 = 2118811) B2118811
theorem B6356393 : Blo 1883143 6356393 := bstep (se 2 (by rfl) ⟨2383647, by rfl⟩ : syracuseStep 6356393 = 4767295) B4767295
theorem B3177967 : Blo 1883143 3177967 := bstep (se 1 (by rfl) ⟨2383475, by rfl⟩ : syracuseStep 3177967 = 4766951) B4766951
theorem B4767407 : Blo 1883143 4767407 := bstep (se 1 (by rfl) ⟨3575555, by rfl⟩ : syracuseStep 4767407 = 7151111) B7151111
theorem B4413161 : Blo 1883143 4413161 := bstep (se 2 (by rfl) ⟨1654935, by rfl⟩ : syracuseStep 4413161 = 3309871) B3309871
theorem B4237127 : Blo 1883143 4237127 := bstep (se 1 (by rfl) ⟨3177845, by rfl⟩ : syracuseStep 4237127 = 6355691) B6355691
theorem B4237199 : Blo 1883143 4237199 := bstep (se 1 (by rfl) ⟨3177899, by rfl⟩ : syracuseStep 4237199 = 6355799) B6355799
theorem B4237595 : Blo 1883143 4237595 := bstep (se 1 (by rfl) ⟨3178196, by rfl⟩ : syracuseStep 4237595 = 6356393) B6356393
theorem B2824751 : Blo 1883143 2824751 := bstep (se 1 (by rfl) ⟨2118563, by rfl⟩ : syracuseStep 2824751 = 4237127) B4237127
theorem B2824799 : Blo 1883143 2824799 := bstep (se 1 (by rfl) ⟨2118599, by rfl⟩ : syracuseStep 2824799 = 4237199) B4237199
theorem B11768429 : Blo 1883143 11768429 := bstep (se 3 (by rfl) ⟨2206580, by rfl⟩ : syracuseStep 11768429 = 4413161) B4413161
theorem B2038591 : Blo 1883143 2038591 := bstep (se 1 (by rfl) ⟨1528943, by rfl⟩ : syracuseStep 2038591 = 3057887) B3057887
theorem B11021195 : Blo 1883143 11021195 := bstep (se 1 (by rfl) ⟨8265896, by rfl⟩ : syracuseStep 11021195 = 16531793) B16531793
theorem B1883163 : Blo 1883143 1883163 := bstep (se 1 (by rfl) ⟨1412372, by rfl⟩ : syracuseStep 1883163 = 2824745) B2824745
theorem B6356123 : Blo 1883143 6356123 := bstep (se 1 (by rfl) ⟨4767092, by rfl⟩ : syracuseStep 6356123 = 9534185) B9534185
theorem B1883303 : Blo 1883143 1883303 := bstep (se 1 (by rfl) ⟨1412477, by rfl⟩ : syracuseStep 1883303 = 2824955) B2824955
theorem B4766971 : Blo 1883143 4766971 := bstep (se 1 (by rfl) ⟨3575228, by rfl⟩ : syracuseStep 4766971 = 7150457) B7150457
theorem B1883387 : Blo 1883143 1883387 := bstep (se 1 (by rfl) ⟨1412540, by rfl⟩ : syracuseStep 1883387 = 2825081) B2825081
theorem B12398201 : Blo 1883143 12398201 := bstep (se 2 (by rfl) ⟨4649325, by rfl⟩ : syracuseStep 12398201 = 9298651) B9298651
theorem B3178271 : Blo 1883143 3178271 := bstep (se 1 (by rfl) ⟨2383703, by rfl⟩ : syracuseStep 3178271 = 4767407) B4767407
theorem B4237289 : Blo 1883143 4237289 := bstep (se 2 (by rfl) ⟨1588983, by rfl⟩ : syracuseStep 4237289 = 3177967) B3177967
theorem B4237415 : Blo 1883143 4237415 := bstep (se 1 (by rfl) ⟨3178061, by rfl⟩ : syracuseStep 4237415 = 6356123) B6356123
theorem B2824859 : Blo 1883143 2824859 := bstep (se 1 (by rfl) ⟨2118644, by rfl⟩ : syracuseStep 2824859 = 4237289) B4237289
theorem B2825063 : Blo 1883143 2825063 := bstep (se 1 (by rfl) ⟨2118797, by rfl⟩ : syracuseStep 2825063 = 4237595) B4237595
theorem B6355961 : Blo 1883143 6355961 := bstep (se 2 (by rfl) ⟨2383485, by rfl⟩ : syracuseStep 6355961 = 4766971) B4766971
theorem B29389853 : Blo 1883143 29389853 := bstep (se 3 (by rfl) ⟨5510597, by rfl⟩ : syracuseStep 29389853 = 11021195) B11021195
theorem B1883167 : Blo 1883143 1883167 := bstep (se 1 (by rfl) ⟨1412375, by rfl⟩ : syracuseStep 1883167 = 2824751) B2824751
theorem B1883199 : Blo 1883143 1883199 := bstep (se 1 (by rfl) ⟨1412399, by rfl⟩ : syracuseStep 1883199 = 2824799) B2824799
theorem B2118847 : Blo 1883143 2118847 := bstep (se 1 (by rfl) ⟨1589135, by rfl⟩ : syracuseStep 2118847 = 3178271) B3178271
theorem B10872485 : Blo 1883143 10872485 := bstep (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) B2038591
theorem B7845619 : Blo 1883143 7845619 := bstep (se 1 (by rfl) ⟨5884214, by rfl⟩ : syracuseStep 7845619 = 11768429) B11768429
theorem B8265467 : Blo 1883143 8265467 := bstep (se 1 (by rfl) ⟨6199100, by rfl⟩ : syracuseStep 8265467 = 12398201) B12398201
theorem B19593235 : Blo 1883143 19593235 := bstep (se 1 (by rfl) ⟨14694926, by rfl⟩ : syracuseStep 19593235 = 29389853) B29389853
theorem B7248323 : Blo 1883143 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B2824943 : Blo 1883143 2824943 := bstep (se 1 (by rfl) ⟨2118707, by rfl⟩ : syracuseStep 2824943 = 4237415) B4237415
theorem B2825129 : Blo 1883143 2825129 := bstep (se 2 (by rfl) ⟨1059423, by rfl⟩ : syracuseStep 2825129 = 2118847) B2118847
theorem B1883239 : Blo 1883143 1883239 := bstep (se 1 (by rfl) ⟨1412429, by rfl⟩ : syracuseStep 1883239 = 2824859) B2824859
theorem B5510311 : Blo 1883143 5510311 := bstep (se 1 (by rfl) ⟨4132733, by rfl⟩ : syracuseStep 5510311 = 8265467) B8265467
theorem B1883375 : Blo 1883143 1883375 := bstep (se 1 (by rfl) ⟨1412531, by rfl⟩ : syracuseStep 1883375 = 2825063) B2825063
theorem B10460825 : Blo 1883143 10460825 := bstep (se 2 (by rfl) ⟨3922809, by rfl⟩ : syracuseStep 10460825 = 7845619) B7845619
theorem B4237307 : Blo 1883143 4237307 := bstep (se 1 (by rfl) ⟨3177980, by rfl⟩ : syracuseStep 4237307 = 6355961) B6355961
theorem B104497253 : Blo 1883143 104497253 := bstep (se 4 (by rfl) ⟨9796617, by rfl⟩ : syracuseStep 104497253 = 19593235) B19593235
theorem B117553301 : Blo 1883143 117553301 := bstep (se 6 (by rfl) ⟨2755155, by rfl⟩ : syracuseStep 117553301 = 5510311) B5510311
theorem B6973883 : Blo 1883143 6973883 := bstep (se 1 (by rfl) ⟨5230412, by rfl⟩ : syracuseStep 6973883 = 10460825) B10460825
theorem B2824871 : Blo 1883143 2824871 := bstep (se 1 (by rfl) ⟨2118653, by rfl⟩ : syracuseStep 2824871 = 4237307) B4237307
theorem B1883295 : Blo 1883143 1883295 := bstep (se 1 (by rfl) ⟨1412471, by rfl⟩ : syracuseStep 1883295 = 2824943) B2824943
theorem B1883419 : Blo 1883143 1883419 := bstep (se 1 (by rfl) ⟨1412564, by rfl⟩ : syracuseStep 1883419 = 2825129) B2825129
theorem B19328861 : Blo 1883143 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B69664835 : Blo 1883143 69664835 := bstep (se 1 (by rfl) ⟨52248626, by rfl⟩ : syracuseStep 69664835 = 104497253) B104497253
theorem B78368867 : Blo 1883143 78368867 := bstep (se 1 (by rfl) ⟨58776650, by rfl⟩ : syracuseStep 78368867 = 117553301) B117553301
theorem B4649255 : Blo 1883143 4649255 := bstep (se 1 (by rfl) ⟨3486941, by rfl⟩ : syracuseStep 4649255 = 6973883) B6973883
theorem B1883247 : Blo 1883143 1883247 := bstep (se 1 (by rfl) ⟨1412435, by rfl⟩ : syracuseStep 1883247 = 2824871) B2824871
theorem B12885907 : Blo 1883143 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B17181209 : Blo 1883143 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B46443223 : Blo 1883143 46443223 := bstep (se 1 (by rfl) ⟨34832417, by rfl⟩ : syracuseStep 46443223 = 69664835) B69664835
theorem B3099503 : Blo 1883143 3099503 := bstep (se 1 (by rfl) ⟨2324627, by rfl⟩ : syracuseStep 3099503 = 4649255) B4649255
theorem B52245911 : Blo 1883143 52245911 := bstep (se 1 (by rfl) ⟨39184433, by rfl⟩ : syracuseStep 52245911 = 78368867) B78368867
theorem B34830607 : Blo 1883143 34830607 := bstep (se 1 (by rfl) ⟨26122955, by rfl⟩ : syracuseStep 34830607 = 52245911) B52245911
theorem B61924297 : Blo 1883143 61924297 := bstep (se 2 (by rfl) ⟨23221611, by rfl⟩ : syracuseStep 61924297 = 46443223) B46443223
theorem B8265341 : Blo 1883143 8265341 := bstep (se 3 (by rfl) ⟨1549751, by rfl⟩ : syracuseStep 8265341 = 3099503) B3099503
theorem B11454139 : Blo 1883143 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B15272185 : Blo 1883143 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B46440809 : Blo 1883143 46440809 := bstep (se 2 (by rfl) ⟨17415303, by rfl⟩ : syracuseStep 46440809 = 34830607) B34830607
theorem B82565729 : Blo 1883143 82565729 := bstep (se 2 (by rfl) ⟨30962148, by rfl⟩ : syracuseStep 82565729 = 61924297) B61924297
theorem B5510227 : Blo 1883143 5510227 := bstep (se 1 (by rfl) ⟨4132670, by rfl⟩ : syracuseStep 5510227 = 8265341) B8265341
theorem B7346969 : Blo 1883143 7346969 := bstep (se 2 (by rfl) ⟨2755113, by rfl⟩ : syracuseStep 7346969 = 5510227) B5510227
theorem B30960539 : Blo 1883143 30960539 := bstep (se 1 (by rfl) ⟨23220404, by rfl⟩ : syracuseStep 30960539 = 46440809) B46440809
theorem B20362913 : Blo 1883143 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B55043819 : Blo 1883143 55043819 := bstep (se 1 (by rfl) ⟨41282864, by rfl⟩ : syracuseStep 55043819 = 82565729) B82565729
theorem B20640359 : Blo 1883143 20640359 := bstep (se 1 (by rfl) ⟨15480269, by rfl⟩ : syracuseStep 20640359 = 30960539) B30960539
theorem B13575275 : Blo 1883143 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B4897979 : Blo 1883143 4897979 := bstep (se 1 (by rfl) ⟨3673484, by rfl⟩ : syracuseStep 4897979 = 7346969) B7346969
theorem B36695879 : Blo 1883143 36695879 := bstep (se 1 (by rfl) ⟨27521909, by rfl⟩ : syracuseStep 36695879 = 55043819) B55043819
theorem B9050183 : Blo 1883143 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B24463919 : Blo 1883143 24463919 := bstep (se 1 (by rfl) ⟨18347939, by rfl⟩ : syracuseStep 24463919 = 36695879) B36695879
theorem B3265319 : Blo 1883143 3265319 := bstep (se 1 (by rfl) ⟨2448989, by rfl⟩ : syracuseStep 3265319 = 4897979) B4897979
theorem B13760239 : Blo 1883143 13760239 := bstep (se 1 (by rfl) ⟨10320179, by rfl⟩ : syracuseStep 13760239 = 20640359) B20640359
theorem B6033455 : Blo 1883143 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B18346985 : Blo 1883143 18346985 := bstep (se 2 (by rfl) ⟨6880119, by rfl⟩ : syracuseStep 18346985 = 13760239) B13760239
theorem B16309279 : Blo 1883143 16309279 := bstep (se 1 (by rfl) ⟨12231959, by rfl⟩ : syracuseStep 16309279 = 24463919) B24463919
theorem B2176879 : Blo 1883143 2176879 := bstep (se 1 (by rfl) ⟨1632659, by rfl⟩ : syracuseStep 2176879 = 3265319) B3265319
theorem B4022303 : Blo 1883143 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B86982821 : Blo 1883143 86982821 := bstep (se 4 (by rfl) ⟨8154639, by rfl⟩ : syracuseStep 86982821 = 16309279) B16309279
theorem B2902505 : Blo 1883143 2902505 := bstep (se 2 (by rfl) ⟨1088439, by rfl⟩ : syracuseStep 2902505 = 2176879) B2176879
theorem B12231323 : Blo 1883143 12231323 := bstep (se 1 (by rfl) ⟨9173492, by rfl⟩ : syracuseStep 12231323 = 18346985) B18346985
theorem B30960053 : Blo 1883143 30960053 := bstep (se 5 (by rfl) ⟨1451252, by rfl⟩ : syracuseStep 30960053 = 2902505) B2902505
theorem B10726141 : Blo 1883143 10726141 := bstep (se 3 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 10726141 = 4022303) B4022303
theorem B8154215 : Blo 1883143 8154215 := bstep (se 1 (by rfl) ⟨6115661, by rfl⟩ : syracuseStep 8154215 = 12231323) B12231323
theorem B57988547 : Blo 1883143 57988547 := bstep (se 1 (by rfl) ⟨43491410, by rfl⟩ : syracuseStep 57988547 = 86982821) B86982821
theorem B20640035 : Blo 1883143 20640035 := bstep (se 1 (by rfl) ⟨15480026, by rfl⟩ : syracuseStep 20640035 = 30960053) B30960053
theorem B14301521 : Blo 1883143 14301521 := bstep (se 2 (by rfl) ⟨5363070, by rfl⟩ : syracuseStep 14301521 = 10726141) B10726141
theorem B5436143 : Blo 1883143 5436143 := bstep (se 1 (by rfl) ⟨4077107, by rfl⟩ : syracuseStep 5436143 = 8154215) B8154215
theorem B38659031 : Blo 1883143 38659031 := bstep (se 1 (by rfl) ⟨28994273, by rfl⟩ : syracuseStep 38659031 = 57988547) B57988547
theorem B55040093 : Blo 1883143 55040093 := bstep (se 3 (by rfl) ⟨10320017, by rfl⟩ : syracuseStep 55040093 = 20640035) B20640035
theorem B25772687 : Blo 1883143 25772687 := bstep (se 1 (by rfl) ⟨19329515, by rfl⟩ : syracuseStep 25772687 = 38659031) B38659031
theorem B9534347 : Blo 1883143 9534347 := bstep (se 1 (by rfl) ⟨7150760, by rfl⟩ : syracuseStep 9534347 = 14301521) B14301521
theorem B3624095 : Blo 1883143 3624095 := bstep (se 1 (by rfl) ⟨2718071, by rfl⟩ : syracuseStep 3624095 = 5436143) B5436143
theorem B17181791 : Blo 1883143 17181791 := bstep (se 1 (by rfl) ⟨12886343, by rfl⟩ : syracuseStep 17181791 = 25772687) B25772687
theorem B6356231 : Blo 1883143 6356231 := bstep (se 1 (by rfl) ⟨4767173, by rfl⟩ : syracuseStep 6356231 = 9534347) B9534347
theorem B36693395 : Blo 1883143 36693395 := bstep (se 1 (by rfl) ⟨27520046, by rfl⟩ : syracuseStep 36693395 = 55040093) B55040093
theorem B2416063 : Blo 1883143 2416063 := bstep (se 1 (by rfl) ⟨1812047, by rfl⟩ : syracuseStep 2416063 = 3624095) B3624095
theorem B11454527 : Blo 1883143 11454527 := bstep (se 1 (by rfl) ⟨8590895, by rfl⟩ : syracuseStep 11454527 = 17181791) B17181791
theorem B4237487 : Blo 1883143 4237487 := bstep (se 1 (by rfl) ⟨3178115, by rfl⟩ : syracuseStep 4237487 = 6356231) B6356231
theorem B24462263 : Blo 1883143 24462263 := bstep (se 1 (by rfl) ⟨18346697, by rfl⟩ : syracuseStep 24462263 = 36693395) B36693395
theorem B3221417 : Blo 1883143 3221417 := bstep (se 2 (by rfl) ⟨1208031, by rfl⟩ : syracuseStep 3221417 = 2416063) B2416063
theorem B2824991 : Blo 1883143 2824991 := bstep (se 1 (by rfl) ⟨2118743, by rfl⟩ : syracuseStep 2824991 = 4237487) B4237487
theorem B8590445 : Blo 1883143 8590445 := bstep (se 3 (by rfl) ⟨1610708, by rfl⟩ : syracuseStep 8590445 = 3221417) B3221417
theorem B7636351 : Blo 1883143 7636351 := bstep (se 1 (by rfl) ⟨5727263, by rfl⟩ : syracuseStep 7636351 = 11454527) B11454527
theorem B16308175 : Blo 1883143 16308175 := bstep (se 1 (by rfl) ⟨12231131, by rfl⟩ : syracuseStep 16308175 = 24462263) B24462263
theorem B21744233 : Blo 1883143 21744233 := bstep (se 2 (by rfl) ⟨8154087, by rfl⟩ : syracuseStep 21744233 = 16308175) B16308175
theorem B5726963 : Blo 1883143 5726963 := bstep (se 1 (by rfl) ⟨4295222, by rfl⟩ : syracuseStep 5726963 = 8590445) B8590445
theorem B10181801 : Blo 1883143 10181801 := bstep (se 2 (by rfl) ⟨3818175, by rfl⟩ : syracuseStep 10181801 = 7636351) B7636351
theorem B1883327 : Blo 1883143 1883327 := bstep (se 1 (by rfl) ⟨1412495, by rfl⟩ : syracuseStep 1883327 = 2824991) B2824991
theorem B14496155 : Blo 1883143 14496155 := bstep (se 1 (by rfl) ⟨10872116, by rfl⟩ : syracuseStep 14496155 = 21744233) B21744233
theorem B3817975 : Blo 1883143 3817975 := bstep (se 1 (by rfl) ⟨2863481, by rfl⟩ : syracuseStep 3817975 = 5726963) B5726963
theorem B27151469 : Blo 1883143 27151469 := bstep (se 3 (by rfl) ⟨5090900, by rfl⟩ : syracuseStep 27151469 = 10181801) B10181801
theorem B18100979 : Blo 1883143 18100979 := bstep (se 1 (by rfl) ⟨13575734, by rfl⟩ : syracuseStep 18100979 = 27151469) B27151469
theorem B5090633 : Blo 1883143 5090633 := bstep (se 2 (by rfl) ⟨1908987, by rfl⟩ : syracuseStep 5090633 = 3817975) B3817975
theorem B9664103 : Blo 1883143 9664103 := bstep (se 1 (by rfl) ⟨7248077, by rfl⟩ : syracuseStep 9664103 = 14496155) B14496155
theorem B3393755 : Blo 1883143 3393755 := bstep (se 1 (by rfl) ⟨2545316, by rfl⟩ : syracuseStep 3393755 = 5090633) B5090633
theorem B12067319 : Blo 1883143 12067319 := bstep (se 1 (by rfl) ⟨9050489, by rfl⟩ : syracuseStep 12067319 = 18100979) B18100979
theorem B6442735 : Blo 1883143 6442735 := bstep (se 1 (by rfl) ⟨4832051, by rfl⟩ : syracuseStep 6442735 = 9664103) B9664103
theorem B8590313 : Blo 1883143 8590313 := bstep (se 2 (by rfl) ⟨3221367, by rfl⟩ : syracuseStep 8590313 = 6442735) B6442735
theorem B32179517 : Blo 1883143 32179517 := bstep (se 3 (by rfl) ⟨6033659, by rfl⟩ : syracuseStep 32179517 = 12067319) B12067319
theorem B2262503 : Blo 1883143 2262503 := bstep (se 1 (by rfl) ⟨1696877, by rfl⟩ : syracuseStep 2262503 = 3393755) B3393755
theorem B21453011 : Blo 1883143 21453011 := bstep (se 1 (by rfl) ⟨16089758, by rfl⟩ : syracuseStep 21453011 = 32179517) B32179517
theorem B5726875 : Blo 1883143 5726875 := bstep (se 1 (by rfl) ⟨4295156, by rfl⟩ : syracuseStep 5726875 = 8590313) B8590313
theorem B6033341 : Blo 1883143 6033341 := bstep (se 3 (by rfl) ⟨1131251, by rfl⟩ : syracuseStep 6033341 = 2262503) B2262503
theorem B14302007 : Blo 1883143 14302007 := bstep (se 1 (by rfl) ⟨10726505, by rfl⟩ : syracuseStep 14302007 = 21453011) B21453011
theorem B7635833 : Blo 1883143 7635833 := bstep (se 2 (by rfl) ⟨2863437, by rfl⟩ : syracuseStep 7635833 = 5726875) B5726875
theorem B4022227 : Blo 1883143 4022227 := bstep (se 1 (by rfl) ⟨3016670, by rfl⟩ : syracuseStep 4022227 = 6033341) B6033341
theorem B9534671 : Blo 1883143 9534671 := bstep (se 1 (by rfl) ⟨7151003, by rfl⟩ : syracuseStep 9534671 = 14302007) B14302007
theorem B5090555 : Blo 1883143 5090555 := bstep (se 1 (by rfl) ⟨3817916, by rfl⟩ : syracuseStep 5090555 = 7635833) B7635833
theorem B5362969 : Blo 1883143 5362969 := bstep (se 2 (by rfl) ⟨2011113, by rfl⟩ : syracuseStep 5362969 = 4022227) B4022227
theorem B3393703 : Blo 1883143 3393703 := bstep (se 1 (by rfl) ⟨2545277, by rfl⟩ : syracuseStep 3393703 = 5090555) B5090555
theorem B7150625 : Blo 1883143 7150625 := bstep (se 2 (by rfl) ⟨2681484, by rfl⟩ : syracuseStep 7150625 = 5362969) B5362969
theorem B6356447 : Blo 1883143 6356447 := bstep (se 1 (by rfl) ⟨4767335, by rfl⟩ : syracuseStep 6356447 = 9534671) B9534671
theorem B4237631 : Blo 1883143 4237631 := bstep (se 1 (by rfl) ⟨3178223, by rfl⟩ : syracuseStep 4237631 = 6356447) B6356447
theorem B4767083 : Blo 1883143 4767083 := bstep (se 1 (by rfl) ⟨3575312, by rfl⟩ : syracuseStep 4767083 = 7150625) B7150625
theorem B18099749 : Blo 1883143 18099749 := bstep (se 4 (by rfl) ⟨1696851, by rfl⟩ : syracuseStep 18099749 = 3393703) B3393703
theorem B2825087 : Blo 1883143 2825087 := bstep (se 1 (by rfl) ⟨2118815, by rfl⟩ : syracuseStep 2825087 = 4237631) B4237631
theorem B3178055 : Blo 1883143 3178055 := bstep (se 1 (by rfl) ⟨2383541, by rfl⟩ : syracuseStep 3178055 = 4767083) B4767083
theorem B12066499 : Blo 1883143 12066499 := bstep (se 1 (by rfl) ⟨9049874, by rfl⟩ : syracuseStep 12066499 = 18099749) B18099749
theorem B2118703 : Blo 1883143 2118703 := bstep (se 1 (by rfl) ⟨1589027, by rfl⟩ : syracuseStep 2118703 = 3178055) B3178055
theorem B1883391 : Blo 1883143 1883391 := bstep (se 1 (by rfl) ⟨1412543, by rfl⟩ : syracuseStep 1883391 = 2825087) B2825087
theorem B16088665 : Blo 1883143 16088665 := bstep (se 2 (by rfl) ⟨6033249, by rfl⟩ : syracuseStep 16088665 = 12066499) B12066499
theorem B2824937 : Blo 1883143 2824937 := bstep (se 2 (by rfl) ⟨1059351, by rfl⟩ : syracuseStep 2824937 = 2118703) B2118703
theorem B21451553 : Blo 1883143 21451553 := bstep (se 2 (by rfl) ⟨8044332, by rfl⟩ : syracuseStep 21451553 = 16088665) B16088665
theorem B1883291 : Blo 1883143 1883291 := bstep (se 1 (by rfl) ⟨1412468, by rfl⟩ : syracuseStep 1883291 = 2824937) B2824937
theorem B14301035 : Blo 1883143 14301035 := bstep (se 1 (by rfl) ⟨10725776, by rfl⟩ : syracuseStep 14301035 = 21451553) B21451553
theorem B9534023 : Blo 1883143 9534023 := bstep (se 1 (by rfl) ⟨7150517, by rfl⟩ : syracuseStep 9534023 = 14301035) B14301035
theorem B6356015 : Blo 1883143 6356015 := bstep (se 1 (by rfl) ⟨4767011, by rfl⟩ : syracuseStep 6356015 = 9534023) B9534023
theorem B4237343 : Blo 1883143 4237343 := bstep (se 1 (by rfl) ⟨3178007, by rfl⟩ : syracuseStep 4237343 = 6356015) B6356015
theorem B2824895 : Blo 1883143 2824895 := bstep (se 1 (by rfl) ⟨2118671, by rfl⟩ : syracuseStep 2824895 = 4237343) B4237343
theorem B1883263 : Blo 1883143 1883263 := bstep (se 1 (by rfl) ⟨1412447, by rfl⟩ : syracuseStep 1883263 = 2824895) B2824895

theorem C0 (j : ℕ) (h1 : 470785 ≤ j) (h2 : j ≤ 470857) : Blo 1883143 (4 * j + 3) := by
  interval_cases j
  · exact B1883143
  · exact B1883147
  · exact B1883151
  · exact B1883155
  · exact B1883159
  · exact B1883163
  · exact B1883167
  · exact B1883171
  · exact B1883175
  · exact B1883179
  · exact B1883183
  · exact B1883187
  · exact B1883191
  · exact B1883195
  · exact B1883199
  · exact B1883203
  · exact B1883207
  · exact B1883211
  · exact B1883215
  · exact B1883219
  · exact B1883223
  · exact B1883227
  · exact B1883231
  · exact B1883235
  · exact B1883239
  · exact B1883243
  · exact B1883247
  · exact B1883251
  · exact B1883255
  · exact B1883259
  · exact B1883263
  · exact B1883267
  · exact B1883271
  · exact B1883275
  · exact B1883279
  · exact B1883283
  · exact B1883287
  · exact B1883291
  · exact B1883295
  · exact B1883299
  · exact B1883303
  · exact B1883307
  · exact B1883311
  · exact B1883315
  · exact B1883319
  · exact B1883323
  · exact B1883327
  · exact B1883331
  · exact B1883335
  · exact B1883339
  · exact B1883343
  · exact B1883347
  · exact B1883351
  · exact B1883355
  · exact B1883359
  · exact B1883363
  · exact B1883367
  · exact B1883371
  · exact B1883375
  · exact B1883379
  · exact B1883383
  · exact B1883387
  · exact B1883391
  · exact B1883395
  · exact B1883399
  · exact B1883403
  · exact B1883407
  · exact B1883411
  · exact B1883415
  · exact B1883419
  · exact B1883423
  · exact B1883427
  · exact B1883431

theorem solution (m : ℕ) (hlo : 1883143 ≤ m) (hhi : m ≤ 1883431) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 470785 ≤ j := by omega
    have hj2 : j ≤ 470857 := by omega
    have hb : Blo 1883143 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
