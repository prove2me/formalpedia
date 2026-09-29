-- Prove2me | solution 1 for syracuse_descends_range_1875639_1877139
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:15:43.179971+00:00
-- url     : https://prove2.me/submissions/50340ed6-4499-47b4-b23b-d6b35637c920

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


theorem B9502757 : Blo 1875639 9502757 := bbase (se 4 (by rfl) ⟨890883, by rfl⟩ : syracuseStep 9502757 = 1781767) (by norm_num)
theorem B2375725 : Blo 1875639 2375725 := bbase (se 3 (by rfl) ⟨445448, by rfl⟩ : syracuseStep 2375725 = 890897) (by norm_num)
theorem B8011973 : Blo 1875639 8011973 := bbase (se 4 (by rfl) ⟨751122, by rfl⟩ : syracuseStep 8011973 = 1502245) (by norm_num)
theorem B6332741 : Blo 1875639 6332741 := bbase (se 4 (by rfl) ⟨593694, by rfl⟩ : syracuseStep 6332741 = 1187389) (by norm_num)
theorem B4006277 : Blo 1875639 4006277 := bbase (se 4 (by rfl) ⟨375588, by rfl⟩ : syracuseStep 4006277 = 751177) (by norm_num)
theorem B5341589 : Blo 1875639 5341589 := bbase (se 6 (by rfl) ⟨125193, by rfl⟩ : syracuseStep 5341589 = 250387) (by norm_num)
theorem B5489093 : Blo 1875639 5489093 := bbase (se 4 (by rfl) ⟨514602, by rfl⟩ : syracuseStep 5489093 = 1029205) (by norm_num)
theorem B4006397 : Blo 1875639 4006397 := bbase (se 3 (by rfl) ⟨751199, by rfl⟩ : syracuseStep 4006397 = 1502399) (by norm_num)
theorem B12182069 : Blo 1875639 12182069 := bbase (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) (by norm_num)
theorem B2253377 : Blo 1875639 2253377 := bbase (se 2 (by rfl) ⟨845016, by rfl⟩ : syracuseStep 2253377 = 1690033) (by norm_num)
theorem B6333173 : Blo 1875639 6333173 := bbase (se 5 (by rfl) ⟨296867, by rfl⟩ : syracuseStep 6333173 = 593735) (by norm_num)
theorem B5342021 : Blo 1875639 5342021 := bbase (se 4 (by rfl) ⟨500814, by rfl⟩ : syracuseStep 5342021 = 1001629) (by norm_num)
theorem B2253685 : Blo 1875639 2253685 := bbase (se 5 (by rfl) ⟨105641, by rfl⟩ : syracuseStep 2253685 = 211283) (by norm_num)
theorem B2253781 : Blo 1875639 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B2253829 : Blo 1875639 2253829 := bbase (se 4 (by rfl) ⟨211296, by rfl⟩ : syracuseStep 2253829 = 422593) (by norm_num)
theorem B2671717 : Blo 1875639 2671717 := bbase (se 4 (by rfl) ⟨250473, by rfl⟩ : syracuseStep 2671717 = 500947) (by norm_num)
theorem B4007029 : Blo 1875639 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B6333605 : Blo 1875639 6333605 := bbase (se 4 (by rfl) ⟨593775, by rfl⟩ : syracuseStep 6333605 = 1187551) (by norm_num)
theorem B13526261 : Blo 1875639 13526261 := bbase (se 5 (by rfl) ⟨634043, by rfl⟩ : syracuseStep 13526261 = 1268087) (by norm_num)
theorem B4220189 : Blo 1875639 4220189 := bbase (se 3 (by rfl) ⟨791285, by rfl⟩ : syracuseStep 4220189 = 1582571) (by norm_num)
theorem B4220261 : Blo 1875639 4220261 := bbase (se 4 (by rfl) ⟨395649, by rfl⟩ : syracuseStep 4220261 = 791299) (by norm_num)
theorem B3802477 : Blo 1875639 3802477 := bbase (se 3 (by rfl) ⟨712964, by rfl⟩ : syracuseStep 3802477 = 1425929) (by norm_num)
theorem B8562037 : Blo 1875639 8562037 := bbase (se 5 (by rfl) ⟨401345, by rfl⟩ : syracuseStep 8562037 = 802691) (by norm_num)
theorem B4220333 : Blo 1875639 4220333 := bbase (se 3 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 4220333 = 1582625) (by norm_num)
theorem B27059669 : Blo 1875639 27059669 := bbase (se 7 (by rfl) ⟨317105, by rfl⟩ : syracuseStep 27059669 = 634211) (by norm_num)
theorem B4220405 : Blo 1875639 4220405 := bbase (se 5 (by rfl) ⟨197831, by rfl⟩ : syracuseStep 4220405 = 395663) (by norm_num)
theorem B5342773 : Blo 1875639 5342773 := bbase (se 5 (by rfl) ⟨250442, by rfl⟩ : syracuseStep 5342773 = 500885) (by norm_num)
theorem B4220477 : Blo 1875639 4220477 := bbase (se 3 (by rfl) ⟨791339, by rfl⟩ : syracuseStep 4220477 = 1582679) (by norm_num)
theorem B2139733 : Blo 1875639 2139733 := bbase (se 8 (by rfl) ⟨12537, by rfl⟩ : syracuseStep 2139733 = 25075) (by norm_num)
theorem B6334037 : Blo 1875639 6334037 := bbase (se 8 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 6334037 = 74227) (by norm_num)
theorem B2139769 : Blo 1875639 2139769 := bbase (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) (by norm_num)
theorem B4220549 : Blo 1875639 4220549 := bbase (se 4 (by rfl) ⟨395676, by rfl⟩ : syracuseStep 4220549 = 791353) (by norm_num)
theorem B2672309 : Blo 1875639 2672309 := bbase (se 5 (by rfl) ⟨125264, by rfl⟩ : syracuseStep 2672309 = 250529) (by norm_num)
theorem B4220621 : Blo 1875639 4220621 := bbase (se 3 (by rfl) ⟨791366, by rfl⟩ : syracuseStep 4220621 = 1582733) (by norm_num)
theorem B9496277 : Blo 1875639 9496277 := bbase (se 7 (by rfl) ⟨111284, by rfl⟩ : syracuseStep 9496277 = 222569) (by norm_num)
theorem B32057045 : Blo 1875639 32057045 := bbase (se 7 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 32057045 = 751337) (by norm_num)
theorem B1902317 : Blo 1875639 1902317 := bbase (se 3 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 1902317 = 713369) (by norm_num)
theorem B1902341 : Blo 1875639 1902341 := bbase (se 4 (by rfl) ⟨178344, by rfl⟩ : syracuseStep 1902341 = 356689) (by norm_num)
theorem B2672389 : Blo 1875639 2672389 := bbase (se 4 (by rfl) ⟨250536, by rfl⟩ : syracuseStep 2672389 = 501073) (by norm_num)
theorem B4220693 : Blo 1875639 4220693 := bbase (se 6 (by rfl) ⟨98922, by rfl⟩ : syracuseStep 4220693 = 197845) (by norm_num)
theorem B4220765 : Blo 1875639 4220765 := bbase (se 3 (by rfl) ⟨791393, by rfl⟩ : syracuseStep 4220765 = 1582787) (by norm_num)
theorem B2140025 : Blo 1875639 2140025 := bbase (se 2 (by rfl) ⟨802509, by rfl⟩ : syracuseStep 2140025 = 1605019) (by norm_num)
theorem B2672509 : Blo 1875639 2672509 := bbase (se 3 (by rfl) ⟨501095, by rfl⟩ : syracuseStep 2672509 = 1002191) (by norm_num)
theorem B4220837 : Blo 1875639 4220837 := bbase (se 4 (by rfl) ⟨395703, by rfl⟩ : syracuseStep 4220837 = 791407) (by norm_num)
theorem B15214549 : Blo 1875639 15214549 := bbase (se 7 (by rfl) ⟨178295, by rfl⟩ : syracuseStep 15214549 = 356591) (by norm_num)
theorem B2672605 : Blo 1875639 2672605 := bbase (se 3 (by rfl) ⟨501113, by rfl⟩ : syracuseStep 2672605 = 1002227) (by norm_num)
theorem B6760421 : Blo 1875639 6760421 := bbase (se 4 (by rfl) ⟨633789, by rfl⟩ : syracuseStep 6760421 = 1267579) (by norm_num)
theorem B4220909 : Blo 1875639 4220909 := bbase (se 3 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 4220909 = 1582841) (by norm_num)
theorem B4007917 : Blo 1875639 4007917 := bbase (se 3 (by rfl) ⟨751484, by rfl⟩ : syracuseStep 4007917 = 1502969) (by norm_num)
theorem B6334469 : Blo 1875639 6334469 := bbase (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) (by norm_num)
theorem B4220981 : Blo 1875639 4220981 := bbase (se 5 (by rfl) ⟨197858, by rfl⟩ : syracuseStep 4220981 = 395717) (by norm_num)
theorem B4008037 : Blo 1875639 4008037 := bbase (se 4 (by rfl) ⟨375753, by rfl⟩ : syracuseStep 4008037 = 751507) (by norm_num)
theorem B4221053 : Blo 1875639 4221053 := bbase (se 3 (by rfl) ⟨791447, by rfl⟩ : syracuseStep 4221053 = 1582895) (by norm_num)
theorem B4221125 : Blo 1875639 4221125 := bbase (se 4 (by rfl) ⟨395730, by rfl⟩ : syracuseStep 4221125 = 791461) (by norm_num)
theorem B2255045 : Blo 1875639 2255045 := bbase (se 4 (by rfl) ⟨211410, by rfl⟩ : syracuseStep 2255045 = 422821) (by norm_num)
theorem B4221197 : Blo 1875639 4221197 := bbase (se 3 (by rfl) ⟨791474, by rfl⟩ : syracuseStep 4221197 = 1582949) (by norm_num)
theorem B1927441 : Blo 1875639 1927441 := bbase (se 2 (by rfl) ⟨722790, by rfl⟩ : syracuseStep 1927441 = 1445581) (by norm_num)
theorem B4221269 : Blo 1875639 4221269 := bbase (se 10 (by rfl) ⟨6183, by rfl⟩ : syracuseStep 4221269 = 12367) (by norm_num)
theorem B4008293 : Blo 1875639 4008293 := bbase (se 4 (by rfl) ⟨375777, by rfl⟩ : syracuseStep 4008293 = 751555) (by norm_num)
theorem B4221341 : Blo 1875639 4221341 := bbase (se 3 (by rfl) ⟨791501, by rfl⟩ : syracuseStep 4221341 = 1583003) (by norm_num)
theorem B6334901 : Blo 1875639 6334901 := bbase (se 5 (by rfl) ⟨296948, by rfl⟩ : syracuseStep 6334901 = 593897) (by norm_num)
theorem B2853317 : Blo 1875639 2853317 := bbase (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) (by norm_num)
theorem B21121493 : Blo 1875639 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B4221413 : Blo 1875639 4221413 := bbase (se 4 (by rfl) ⟨395757, by rfl⟩ : syracuseStep 4221413 = 791515) (by norm_num)
theorem B4221485 : Blo 1875639 4221485 := bbase (se 3 (by rfl) ⟨791528, by rfl⟩ : syracuseStep 4221485 = 1583057) (by norm_num)
theorem B4221557 : Blo 1875639 4221557 := bbase (se 5 (by rfl) ⟨197885, by rfl⟩ : syracuseStep 4221557 = 395771) (by norm_num)
theorem B1927837 : Blo 1875639 1927837 := bbase (se 3 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 1927837 = 722939) (by norm_num)
theorem B4221629 : Blo 1875639 4221629 := bbase (se 3 (by rfl) ⟨791555, by rfl⟩ : syracuseStep 4221629 = 1583111) (by norm_num)
theorem B4221701 : Blo 1875639 4221701 := bbase (se 4 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 4221701 = 791569) (by norm_num)
theorem B4221773 : Blo 1875639 4221773 := bbase (se 3 (by rfl) ⟨791582, by rfl⟩ : syracuseStep 4221773 = 1583165) (by norm_num)
theorem B6335333 : Blo 1875639 6335333 := bbase (se 4 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 6335333 = 1187875) (by norm_num)
theorem B4221845 : Blo 1875639 4221845 := bbase (se 6 (by rfl) ⟨98949, by rfl⟩ : syracuseStep 4221845 = 197899) (by norm_num)
theorem B4336541 : Blo 1875639 4336541 := bbase (se 3 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 4336541 = 1626203) (by norm_num)
theorem B4508581 : Blo 1875639 4508581 := bbase (se 4 (by rfl) ⟨422679, by rfl⟩ : syracuseStep 4508581 = 845359) (by norm_num)
theorem B3165149 : Blo 1875639 3165149 := bbase (se 3 (by rfl) ⟨593465, by rfl⟩ : syracuseStep 3165149 = 1186931) (by norm_num)
theorem B4221917 : Blo 1875639 4221917 := bbase (se 3 (by rfl) ⟨791609, by rfl⟩ : syracuseStep 4221917 = 1583219) (by norm_num)
theorem B9497573 : Blo 1875639 9497573 := bbase (se 4 (by rfl) ⟨890397, by rfl⟩ : syracuseStep 9497573 = 1780795) (by norm_num)
theorem B17591285 : Blo 1875639 17591285 := bbase (se 5 (by rfl) ⟨824591, by rfl⟩ : syracuseStep 17591285 = 1649183) (by norm_num)
theorem B2853901 : Blo 1875639 2853901 := bbase (se 3 (by rfl) ⟨535106, by rfl⟩ : syracuseStep 2853901 = 1070213) (by norm_num)
theorem B4516901 : Blo 1875639 4516901 := bbase (se 4 (by rfl) ⟨423459, by rfl⟩ : syracuseStep 4516901 = 846919) (by norm_num)
theorem B4221989 : Blo 1875639 4221989 := bbase (se 4 (by rfl) ⟨395811, by rfl⟩ : syracuseStep 4221989 = 791623) (by norm_num)
theorem B3165277 : Blo 1875639 3165277 := bbase (se 3 (by rfl) ⟨593489, by rfl⟩ : syracuseStep 3165277 = 1186979) (by norm_num)
theorem B6761573 : Blo 1875639 6761573 := bbase (se 4 (by rfl) ⟨633897, by rfl⟩ : syracuseStep 6761573 = 1267795) (by norm_num)
theorem B4222061 : Blo 1875639 4222061 := bbase (se 3 (by rfl) ⟨791636, by rfl⟩ : syracuseStep 4222061 = 1583273) (by norm_num)
theorem B3165365 : Blo 1875639 3165365 := bbase (se 5 (by rfl) ⟨148376, by rfl⟩ : syracuseStep 3165365 = 296753) (by norm_num)
theorem B4222133 : Blo 1875639 4222133 := bbase (se 5 (by rfl) ⟨197912, by rfl⟩ : syracuseStep 4222133 = 395825) (by norm_num)
theorem B4222205 : Blo 1875639 4222205 := bbase (se 3 (by rfl) ⟨791663, by rfl⟩ : syracuseStep 4222205 = 1583327) (by norm_num)
theorem B3165493 : Blo 1875639 3165493 := bbase (se 5 (by rfl) ⟨148382, by rfl⟩ : syracuseStep 3165493 = 296765) (by norm_num)
theorem B5705029 : Blo 1875639 5705029 := bbase (se 4 (by rfl) ⟨534846, by rfl⟩ : syracuseStep 5705029 = 1069693) (by norm_num)
theorem B4222277 : Blo 1875639 4222277 := bbase (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) (by norm_num)
theorem B7605589 : Blo 1875639 7605589 := bbase (se 11 (by rfl) ⟨5570, by rfl⟩ : syracuseStep 7605589 = 11141) (by norm_num)
theorem B3165581 : Blo 1875639 3165581 := bbase (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) (by norm_num)
theorem B4222349 : Blo 1875639 4222349 := bbase (se 3 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 4222349 = 1583381) (by norm_num)
theorem B27413909 : Blo 1875639 27413909 := bbase (se 6 (by rfl) ⟨642513, by rfl⟩ : syracuseStep 27413909 = 1285027) (by norm_num)
theorem B4222421 : Blo 1875639 4222421 := bbase (se 7 (by rfl) ⟨49481, by rfl⟩ : syracuseStep 4222421 = 98963) (by norm_num)
theorem B7122437 : Blo 1875639 7122437 := bbase (se 4 (by rfl) ⟨667728, by rfl⟩ : syracuseStep 7122437 = 1335457) (by norm_num)
theorem B3165709 : Blo 1875639 3165709 := bbase (se 3 (by rfl) ⟨593570, by rfl⟩ : syracuseStep 3165709 = 1187141) (by norm_num)
theorem B4222493 : Blo 1875639 4222493 := bbase (se 3 (by rfl) ⟨791717, by rfl⟩ : syracuseStep 4222493 = 1583435) (by norm_num)
theorem B2813477 : Blo 1875639 2813477 := bbase (se 4 (by rfl) ⟨263763, by rfl⟩ : syracuseStep 2813477 = 527527) (by norm_num)
theorem B2813501 : Blo 1875639 2813501 := bbase (se 3 (by rfl) ⟨527531, by rfl⟩ : syracuseStep 2813501 = 1055063) (by norm_num)
theorem B4509245 : Blo 1875639 4509245 := bbase (se 3 (by rfl) ⟨845483, by rfl⟩ : syracuseStep 4509245 = 1690967) (by norm_num)
theorem B2813525 : Blo 1875639 2813525 := bbase (se 8 (by rfl) ⟨16485, by rfl⟩ : syracuseStep 2813525 = 32971) (by norm_num)
theorem B3165797 : Blo 1875639 3165797 := bbase (se 4 (by rfl) ⟨296793, by rfl⟩ : syracuseStep 3165797 = 593587) (by norm_num)
theorem B4222565 : Blo 1875639 4222565 := bbase (se 4 (by rfl) ⟨395865, by rfl⟩ : syracuseStep 4222565 = 791731) (by norm_num)
theorem B2813549 : Blo 1875639 2813549 := bbase (se 3 (by rfl) ⟨527540, by rfl⟩ : syracuseStep 2813549 = 1055081) (by norm_num)
theorem B2813573 : Blo 1875639 2813573 := bbase (se 4 (by rfl) ⟨263772, by rfl⟩ : syracuseStep 2813573 = 527545) (by norm_num)
theorem B2813597 : Blo 1875639 2813597 := bbase (se 3 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 2813597 = 1055099) (by norm_num)
theorem B4222637 : Blo 1875639 4222637 := bbase (se 3 (by rfl) ⟨791744, by rfl⟩ : syracuseStep 4222637 = 1583489) (by norm_num)
theorem B2813621 : Blo 1875639 2813621 := bbase (se 5 (by rfl) ⟨131888, by rfl⟩ : syracuseStep 2813621 = 263777) (by norm_num)
theorem B8679109 : Blo 1875639 8679109 := bbase (se 4 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 8679109 = 1627333) (by norm_num)
theorem B2813645 : Blo 1875639 2813645 := bbase (se 3 (by rfl) ⟨527558, by rfl⟩ : syracuseStep 2813645 = 1055117) (by norm_num)
theorem B2813669 : Blo 1875639 2813669 := bbase (se 4 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 2813669 = 527563) (by norm_num)
theorem B3165925 : Blo 1875639 3165925 := bbase (se 4 (by rfl) ⟨296805, by rfl⟩ : syracuseStep 3165925 = 593611) (by norm_num)
theorem B4222709 : Blo 1875639 4222709 := bbase (se 5 (by rfl) ⟨197939, by rfl⟩ : syracuseStep 4222709 = 395879) (by norm_num)
theorem B2813693 : Blo 1875639 2813693 := bbase (se 3 (by rfl) ⟨527567, by rfl⟩ : syracuseStep 2813693 = 1055135) (by norm_num)
theorem B2813717 : Blo 1875639 2813717 := bbase (se 6 (by rfl) ⟨65946, by rfl⟩ : syracuseStep 2813717 = 131893) (by norm_num)
theorem B7122725 : Blo 1875639 7122725 := bbase (se 4 (by rfl) ⟨667755, by rfl⟩ : syracuseStep 7122725 = 1335511) (by norm_num)
theorem B2813741 : Blo 1875639 2813741 := bbase (se 3 (by rfl) ⟨527576, by rfl⟩ : syracuseStep 2813741 = 1055153) (by norm_num)
theorem B3166013 : Blo 1875639 3166013 := bbase (se 3 (by rfl) ⟨593627, by rfl⟩ : syracuseStep 3166013 = 1187255) (by norm_num)
theorem B4222781 : Blo 1875639 4222781 := bbase (se 3 (by rfl) ⟨791771, by rfl⟩ : syracuseStep 4222781 = 1583543) (by norm_num)
theorem B2813765 : Blo 1875639 2813765 := bbase (se 4 (by rfl) ⟨263790, by rfl⟩ : syracuseStep 2813765 = 527581) (by norm_num)
theorem B2813789 : Blo 1875639 2813789 := bbase (se 3 (by rfl) ⟨527585, by rfl⟩ : syracuseStep 2813789 = 1055171) (by norm_num)
theorem B2813813 : Blo 1875639 2813813 := bbase (se 5 (by rfl) ⟨131897, by rfl⟩ : syracuseStep 2813813 = 263795) (by norm_num)
theorem B4222853 : Blo 1875639 4222853 := bbase (se 4 (by rfl) ⟨395892, by rfl⟩ : syracuseStep 4222853 = 791785) (by norm_num)
theorem B2813837 : Blo 1875639 2813837 := bbase (se 3 (by rfl) ⟨527594, by rfl⟩ : syracuseStep 2813837 = 1055189) (by norm_num)
theorem B2813861 : Blo 1875639 2813861 := bbase (se 4 (by rfl) ⟨263799, by rfl⟩ : syracuseStep 2813861 = 527599) (by norm_num)
theorem B2813885 : Blo 1875639 2813885 := bbase (se 3 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 2813885 = 1055207) (by norm_num)
theorem B3166141 : Blo 1875639 3166141 := bbase (se 3 (by rfl) ⟨593651, by rfl⟩ : syracuseStep 3166141 = 1187303) (by norm_num)
theorem B4222925 : Blo 1875639 4222925 := bbase (se 3 (by rfl) ⟨791798, by rfl⟩ : syracuseStep 4222925 = 1583597) (by norm_num)
theorem B2813909 : Blo 1875639 2813909 := bbase (se 7 (by rfl) ⟨32975, by rfl⟩ : syracuseStep 2813909 = 65951) (by norm_num)
theorem B2813933 : Blo 1875639 2813933 := bbase (se 3 (by rfl) ⟨527612, by rfl⟩ : syracuseStep 2813933 = 1055225) (by norm_num)
theorem B2813957 : Blo 1875639 2813957 := bbase (se 4 (by rfl) ⟨263808, by rfl⟩ : syracuseStep 2813957 = 527617) (by norm_num)
theorem B3166229 : Blo 1875639 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B14250005 : Blo 1875639 14250005 := bbase (se 6 (by rfl) ⟨333984, by rfl⟩ : syracuseStep 14250005 = 667969) (by norm_num)
theorem B4222997 : Blo 1875639 4222997 := bbase (se 6 (by rfl) ⟨98976, by rfl⟩ : syracuseStep 4222997 = 197953) (by norm_num)
theorem B2813981 : Blo 1875639 2813981 := bbase (se 3 (by rfl) ⟨527621, by rfl⟩ : syracuseStep 2813981 = 1055243) (by norm_num)
theorem B2814005 : Blo 1875639 2814005 := bbase (se 5 (by rfl) ⟨131906, by rfl⟩ : syracuseStep 2814005 = 263813) (by norm_num)
theorem B2814029 : Blo 1875639 2814029 := bbase (se 3 (by rfl) ⟨527630, by rfl⟩ : syracuseStep 2814029 = 1055261) (by norm_num)
theorem B4223069 : Blo 1875639 4223069 := bbase (se 3 (by rfl) ⟨791825, by rfl⟩ : syracuseStep 4223069 = 1583651) (by norm_num)
theorem B2814053 : Blo 1875639 2814053 := bbase (se 4 (by rfl) ⟨263817, by rfl⟩ : syracuseStep 2814053 = 527635) (by norm_num)
theorem B2003053 : Blo 1875639 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B2814077 : Blo 1875639 2814077 := bbase (se 3 (by rfl) ⟨527639, by rfl⟩ : syracuseStep 2814077 = 1055279) (by norm_num)
theorem B2814101 : Blo 1875639 2814101 := bbase (se 6 (by rfl) ⟨65955, by rfl⟩ : syracuseStep 2814101 = 131911) (by norm_num)
theorem B3166357 : Blo 1875639 3166357 := bbase (se 6 (by rfl) ⟨74211, by rfl⟩ : syracuseStep 3166357 = 148423) (by norm_num)
theorem B4223141 : Blo 1875639 4223141 := bbase (se 4 (by rfl) ⟨395919, by rfl⟩ : syracuseStep 4223141 = 791839) (by norm_num)
theorem B2814125 : Blo 1875639 2814125 := bbase (se 3 (by rfl) ⟨527648, by rfl⟩ : syracuseStep 2814125 = 1055297) (by norm_num)
theorem B2814149 : Blo 1875639 2814149 := bbase (se 4 (by rfl) ⟨263826, by rfl⟩ : syracuseStep 2814149 = 527653) (by norm_num)
theorem B2814173 : Blo 1875639 2814173 := bbase (se 3 (by rfl) ⟨527657, by rfl⟩ : syracuseStep 2814173 = 1055315) (by norm_num)
theorem B3166445 : Blo 1875639 3166445 := bbase (se 3 (by rfl) ⟨593708, by rfl⟩ : syracuseStep 3166445 = 1187417) (by norm_num)
theorem B4223213 : Blo 1875639 4223213 := bbase (se 3 (by rfl) ⟨791852, by rfl⟩ : syracuseStep 4223213 = 1583705) (by norm_num)
theorem B2814197 : Blo 1875639 2814197 := bbase (se 5 (by rfl) ⟨131915, by rfl⟩ : syracuseStep 2814197 = 263831) (by norm_num)
theorem B9498869 : Blo 1875639 9498869 := bbase (se 5 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 9498869 = 890519) (by norm_num)
theorem B2814221 : Blo 1875639 2814221 := bbase (se 3 (by rfl) ⟨527666, by rfl⟩ : syracuseStep 2814221 = 1055333) (by norm_num)
theorem B2814245 : Blo 1875639 2814245 := bbase (se 4 (by rfl) ⟨263835, by rfl⟩ : syracuseStep 2814245 = 527671) (by norm_num)
theorem B4223285 : Blo 1875639 4223285 := bbase (se 5 (by rfl) ⟨197966, by rfl⟩ : syracuseStep 4223285 = 395933) (by norm_num)
theorem B2814269 : Blo 1875639 2814269 := bbase (se 3 (by rfl) ⟨527675, by rfl⟩ : syracuseStep 2814269 = 1055351) (by norm_num)
theorem B2814293 : Blo 1875639 2814293 := bbase (se 10 (by rfl) ⟨4122, by rfl⟩ : syracuseStep 2814293 = 8245) (by norm_num)
theorem B2814317 : Blo 1875639 2814317 := bbase (se 3 (by rfl) ⟨527684, by rfl⟩ : syracuseStep 2814317 = 1055369) (by norm_num)
theorem B3166573 : Blo 1875639 3166573 := bbase (se 3 (by rfl) ⟨593732, by rfl⟩ : syracuseStep 3166573 = 1187465) (by norm_num)
theorem B8016245 : Blo 1875639 8016245 := bbase (se 5 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 8016245 = 751523) (by norm_num)
theorem B4223357 : Blo 1875639 4223357 := bbase (se 3 (by rfl) ⟨791879, by rfl⟩ : syracuseStep 4223357 = 1583759) (by norm_num)
theorem B2814341 : Blo 1875639 2814341 := bbase (se 4 (by rfl) ⟨263844, by rfl⟩ : syracuseStep 2814341 = 527689) (by norm_num)
theorem B2814365 : Blo 1875639 2814365 := bbase (se 3 (by rfl) ⟨527693, by rfl⟩ : syracuseStep 2814365 = 1055387) (by norm_num)
theorem B2814389 : Blo 1875639 2814389 := bbase (se 5 (by rfl) ⟨131924, by rfl⟩ : syracuseStep 2814389 = 263849) (by norm_num)
theorem B3166661 : Blo 1875639 3166661 := bbase (se 4 (by rfl) ⟨296874, by rfl⟩ : syracuseStep 3166661 = 593749) (by norm_num)
theorem B4223429 : Blo 1875639 4223429 := bbase (se 4 (by rfl) ⟨395946, by rfl⟩ : syracuseStep 4223429 = 791893) (by norm_num)
theorem B2814413 : Blo 1875639 2814413 := bbase (se 3 (by rfl) ⟨527702, by rfl⟩ : syracuseStep 2814413 = 1055405) (by norm_num)
theorem B5706197 : Blo 1875639 5706197 := bbase (se 7 (by rfl) ⟨66869, by rfl⟩ : syracuseStep 5706197 = 133739) (by norm_num)
theorem B2814437 : Blo 1875639 2814437 := bbase (se 4 (by rfl) ⟨263853, by rfl⟩ : syracuseStep 2814437 = 527707) (by norm_num)
theorem B2814461 : Blo 1875639 2814461 := bbase (se 3 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 2814461 = 1055423) (by norm_num)
theorem B4223501 : Blo 1875639 4223501 := bbase (se 3 (by rfl) ⟨791906, by rfl⟩ : syracuseStep 4223501 = 1583813) (by norm_num)
theorem B2814485 : Blo 1875639 2814485 := bbase (se 6 (by rfl) ⟨65964, by rfl⟩ : syracuseStep 2814485 = 131929) (by norm_num)
theorem B4747805 : Blo 1875639 4747805 := bbase (se 3 (by rfl) ⟨890213, by rfl⟩ : syracuseStep 4747805 = 1780427) (by norm_num)
theorem B2003497 : Blo 1875639 2003497 := bbase (se 2 (by rfl) ⟨751311, by rfl⟩ : syracuseStep 2003497 = 1502623) (by norm_num)
theorem B2814509 : Blo 1875639 2814509 := bbase (se 3 (by rfl) ⟨527720, by rfl⟩ : syracuseStep 2814509 = 1055441) (by norm_num)
theorem B2814533 : Blo 1875639 2814533 := bbase (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) (by norm_num)
theorem B3166789 : Blo 1875639 3166789 := bbase (se 4 (by rfl) ⟨296886, by rfl⟩ : syracuseStep 3166789 = 593773) (by norm_num)
theorem B9015893 : Blo 1875639 9015893 := bbase (se 8 (by rfl) ⟨52827, by rfl⟩ : syracuseStep 9015893 = 105655) (by norm_num)
theorem B2814557 : Blo 1875639 2814557 := bbase (se 3 (by rfl) ⟨527729, by rfl⟩ : syracuseStep 2814557 = 1055459) (by norm_num)
theorem B7041637 : Blo 1875639 7041637 := bbase (se 4 (by rfl) ⟨660153, by rfl⟩ : syracuseStep 7041637 = 1320307) (by norm_num)
theorem B2814581 : Blo 1875639 2814581 := bbase (se 5 (by rfl) ⟨131933, by rfl⟩ : syracuseStep 2814581 = 263867) (by norm_num)
theorem B2814605 : Blo 1875639 2814605 := bbase (se 3 (by rfl) ⟨527738, by rfl⟩ : syracuseStep 2814605 = 1055477) (by norm_num)
theorem B3166877 : Blo 1875639 3166877 := bbase (se 3 (by rfl) ⟨593789, by rfl⟩ : syracuseStep 3166877 = 1187579) (by norm_num)
theorem B2003617 : Blo 1875639 2003617 := bbase (se 2 (by rfl) ⟨751356, by rfl⟩ : syracuseStep 2003617 = 1502713) (by norm_num)
theorem B2110117 : Blo 1875639 2110117 := bbase (se 4 (by rfl) ⟨197823, by rfl⟩ : syracuseStep 2110117 = 395647) (by norm_num)
theorem B2814629 : Blo 1875639 2814629 := bbase (se 4 (by rfl) ⟨263871, by rfl⟩ : syracuseStep 2814629 = 527743) (by norm_num)
theorem B2814653 : Blo 1875639 2814653 := bbase (se 3 (by rfl) ⟨527747, by rfl⟩ : syracuseStep 2814653 = 1055495) (by norm_num)
theorem B8557253 : Blo 1875639 8557253 := bbase (se 4 (by rfl) ⟨802242, by rfl⟩ : syracuseStep 8557253 = 1604485) (by norm_num)
theorem B2110153 : Blo 1875639 2110153 := bbase (se 2 (by rfl) ⟨791307, by rfl⟩ : syracuseStep 2110153 = 1582615) (by norm_num)
theorem B2814677 : Blo 1875639 2814677 := bbase (se 7 (by rfl) ⟨32984, by rfl⟩ : syracuseStep 2814677 = 65969) (by norm_num)
theorem B4747997 : Blo 1875639 4747997 := bbase (se 3 (by rfl) ⟨890249, by rfl⟩ : syracuseStep 4747997 = 1780499) (by norm_num)
theorem B2110189 : Blo 1875639 2110189 := bbase (se 3 (by rfl) ⟨395660, by rfl⟩ : syracuseStep 2110189 = 791321) (by norm_num)
theorem B2814701 : Blo 1875639 2814701 := bbase (se 3 (by rfl) ⟨527756, by rfl⟩ : syracuseStep 2814701 = 1055513) (by norm_num)
theorem B2814725 : Blo 1875639 2814725 := bbase (se 4 (by rfl) ⟨263880, by rfl⟩ : syracuseStep 2814725 = 527761) (by norm_num)
theorem B2110225 : Blo 1875639 2110225 := bbase (se 2 (by rfl) ⟨791334, by rfl⟩ : syracuseStep 2110225 = 1582669) (by norm_num)
theorem B2814749 : Blo 1875639 2814749 := bbase (se 3 (by rfl) ⟨527765, by rfl⟩ : syracuseStep 2814749 = 1055531) (by norm_num)
theorem B3167005 : Blo 1875639 3167005 := bbase (se 3 (by rfl) ⟨593813, by rfl⟩ : syracuseStep 3167005 = 1187627) (by norm_num)
theorem B2110261 : Blo 1875639 2110261 := bbase (se 5 (by rfl) ⟨98918, by rfl⟩ : syracuseStep 2110261 = 197837) (by norm_num)
theorem B2814773 : Blo 1875639 2814773 := bbase (se 5 (by rfl) ⟨131942, by rfl⟩ : syracuseStep 2814773 = 263885) (by norm_num)
theorem B2814797 : Blo 1875639 2814797 := bbase (se 3 (by rfl) ⟨527774, by rfl⟩ : syracuseStep 2814797 = 1055549) (by norm_num)
theorem B2110297 : Blo 1875639 2110297 := bbase (se 2 (by rfl) ⟨791361, by rfl⟩ : syracuseStep 2110297 = 1582723) (by norm_num)
theorem B3855205 : Blo 1875639 3855205 := bbase (se 4 (by rfl) ⟨361425, by rfl⟩ : syracuseStep 3855205 = 722851) (by norm_num)
theorem B2814821 : Blo 1875639 2814821 := bbase (se 4 (by rfl) ⟨263889, by rfl⟩ : syracuseStep 2814821 = 527779) (by norm_num)
theorem B9016181 : Blo 1875639 9016181 := bbase (se 5 (by rfl) ⟨422633, by rfl⟩ : syracuseStep 9016181 = 845267) (by norm_num)
theorem B3167093 : Blo 1875639 3167093 := bbase (se 5 (by rfl) ⟨148457, by rfl⟩ : syracuseStep 3167093 = 296915) (by norm_num)
theorem B2110333 : Blo 1875639 2110333 := bbase (se 3 (by rfl) ⟨395687, by rfl⟩ : syracuseStep 2110333 = 791375) (by norm_num)
theorem B2814845 : Blo 1875639 2814845 := bbase (se 3 (by rfl) ⟨527783, by rfl⟩ : syracuseStep 2814845 = 1055567) (by norm_num)
theorem B2814869 : Blo 1875639 2814869 := bbase (se 6 (by rfl) ⟨65973, by rfl⟩ : syracuseStep 2814869 = 131947) (by norm_num)
theorem B2003869 : Blo 1875639 2003869 := bbase (se 3 (by rfl) ⟨375725, by rfl⟩ : syracuseStep 2003869 = 751451) (by norm_num)
theorem B2110369 : Blo 1875639 2110369 := bbase (se 2 (by rfl) ⟨791388, by rfl⟩ : syracuseStep 2110369 = 1582777) (by norm_num)
theorem B2003873 : Blo 1875639 2003873 := bbase (se 2 (by rfl) ⟨751452, by rfl⟩ : syracuseStep 2003873 = 1502905) (by norm_num)
theorem B4813741 : Blo 1875639 4813741 := bbase (se 3 (by rfl) ⟨902576, by rfl⟩ : syracuseStep 4813741 = 1805153) (by norm_num)
theorem B2814893 : Blo 1875639 2814893 := bbase (se 3 (by rfl) ⟨527792, by rfl⟩ : syracuseStep 2814893 = 1055585) (by norm_num)
theorem B2110405 : Blo 1875639 2110405 := bbase (se 4 (by rfl) ⟨197850, by rfl⟩ : syracuseStep 2110405 = 395701) (by norm_num)
theorem B7123909 : Blo 1875639 7123909 := bbase (se 4 (by rfl) ⟨667866, by rfl⟩ : syracuseStep 7123909 = 1335733) (by norm_num)
theorem B2814917 : Blo 1875639 2814917 := bbase (se 4 (by rfl) ⟨263898, by rfl⟩ : syracuseStep 2814917 = 527797) (by norm_num)
theorem B2814941 : Blo 1875639 2814941 := bbase (se 3 (by rfl) ⟨527801, by rfl⟩ : syracuseStep 2814941 = 1055603) (by norm_num)
theorem B2110441 : Blo 1875639 2110441 := bbase (se 2 (by rfl) ⟨791415, by rfl⟩ : syracuseStep 2110441 = 1582831) (by norm_num)
theorem B2814965 : Blo 1875639 2814965 := bbase (se 5 (by rfl) ⟨131951, by rfl⟩ : syracuseStep 2814965 = 263903) (by norm_num)
theorem B3167221 : Blo 1875639 3167221 := bbase (se 5 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 3167221 = 296927) (by norm_num)
theorem B2110477 : Blo 1875639 2110477 := bbase (se 3 (by rfl) ⟨395714, by rfl⟩ : syracuseStep 2110477 = 791429) (by norm_num)
theorem B2814989 : Blo 1875639 2814989 := bbase (se 3 (by rfl) ⟨527810, by rfl⟩ : syracuseStep 2814989 = 1055621) (by norm_num)
theorem B2815013 : Blo 1875639 2815013 := bbase (se 4 (by rfl) ⟨263907, by rfl⟩ : syracuseStep 2815013 = 527815) (by norm_num)
theorem B2536493 : Blo 1875639 2536493 := bbase (se 3 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 2536493 = 951185) (by norm_num)
theorem B2110513 : Blo 1875639 2110513 := bbase (se 2 (by rfl) ⟨791442, by rfl⟩ : syracuseStep 2110513 = 1582885) (by norm_num)
theorem B4748341 : Blo 1875639 4748341 := bbase (se 5 (by rfl) ⟨222578, by rfl⟩ : syracuseStep 4748341 = 445157) (by norm_num)
theorem B2815037 : Blo 1875639 2815037 := bbase (se 3 (by rfl) ⟨527819, by rfl⟩ : syracuseStep 2815037 = 1055639) (by norm_num)
theorem B3167309 : Blo 1875639 3167309 := bbase (se 3 (by rfl) ⟨593870, by rfl⟩ : syracuseStep 3167309 = 1187741) (by norm_num)
theorem B2110549 : Blo 1875639 2110549 := bbase (se 8 (by rfl) ⟨12366, by rfl⟩ : syracuseStep 2110549 = 24733) (by norm_num)
theorem B2815061 : Blo 1875639 2815061 := bbase (se 8 (by rfl) ⟨16494, by rfl⟩ : syracuseStep 2815061 = 32989) (by norm_num)
theorem B2815085 : Blo 1875639 2815085 := bbase (se 3 (by rfl) ⟨527828, by rfl⟩ : syracuseStep 2815085 = 1055657) (by norm_num)
theorem B2110585 : Blo 1875639 2110585 := bbase (se 2 (by rfl) ⟨791469, by rfl⟩ : syracuseStep 2110585 = 1582939) (by norm_num)
theorem B2815109 : Blo 1875639 2815109 := bbase (se 4 (by rfl) ⟨263916, by rfl⟩ : syracuseStep 2815109 = 527833) (by norm_num)
theorem B2110621 : Blo 1875639 2110621 := bbase (se 3 (by rfl) ⟨395741, by rfl⟩ : syracuseStep 2110621 = 791483) (by norm_num)
theorem B2815133 : Blo 1875639 2815133 := bbase (se 3 (by rfl) ⟨527837, by rfl⟩ : syracuseStep 2815133 = 1055675) (by norm_num)
theorem B4748453 : Blo 1875639 4748453 := bbase (se 4 (by rfl) ⟨445167, by rfl⟩ : syracuseStep 4748453 = 890335) (by norm_num)
theorem B2815157 : Blo 1875639 2815157 := bbase (se 5 (by rfl) ⟨131960, by rfl⟩ : syracuseStep 2815157 = 263921) (by norm_num)
theorem B2110657 : Blo 1875639 2110657 := bbase (se 2 (by rfl) ⟨791496, by rfl⟩ : syracuseStep 2110657 = 1582993) (by norm_num)
theorem B2815181 : Blo 1875639 2815181 := bbase (se 3 (by rfl) ⟨527846, by rfl⟩ : syracuseStep 2815181 = 1055693) (by norm_num)
theorem B3167437 : Blo 1875639 3167437 := bbase (se 3 (by rfl) ⟨593894, by rfl⟩ : syracuseStep 3167437 = 1187789) (by norm_num)
theorem B64230613 : Blo 1875639 64230613 := bbase (se 7 (by rfl) ⟨752702, by rfl⟩ : syracuseStep 64230613 = 1505405) (by norm_num)
theorem B2110693 : Blo 1875639 2110693 := bbase (se 4 (by rfl) ⟨197877, by rfl⟩ : syracuseStep 2110693 = 395755) (by norm_num)
theorem B2815205 : Blo 1875639 2815205 := bbase (se 4 (by rfl) ⟨263925, by rfl⟩ : syracuseStep 2815205 = 527851) (by norm_num)
theorem B7124213 : Blo 1875639 7124213 := bbase (se 5 (by rfl) ⟨333947, by rfl⟩ : syracuseStep 7124213 = 667895) (by norm_num)
theorem B10687733 : Blo 1875639 10687733 := bbase (se 5 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 10687733 = 1001975) (by norm_num)
theorem B2815229 : Blo 1875639 2815229 := bbase (se 3 (by rfl) ⟨527855, by rfl⟩ : syracuseStep 2815229 = 1055711) (by norm_num)
theorem B2110729 : Blo 1875639 2110729 := bbase (se 2 (by rfl) ⟨791523, by rfl⟩ : syracuseStep 2110729 = 1583047) (by norm_num)
theorem B2815253 : Blo 1875639 2815253 := bbase (se 6 (by rfl) ⟨65982, by rfl⟩ : syracuseStep 2815253 = 131965) (by norm_num)
theorem B3167525 : Blo 1875639 3167525 := bbase (se 4 (by rfl) ⟨296955, by rfl⟩ : syracuseStep 3167525 = 593911) (by norm_num)
theorem B2110765 : Blo 1875639 2110765 := bbase (se 3 (by rfl) ⟨395768, by rfl⟩ : syracuseStep 2110765 = 791537) (by norm_num)
theorem B2815277 : Blo 1875639 2815277 := bbase (se 3 (by rfl) ⟨527864, by rfl⟩ : syracuseStep 2815277 = 1055729) (by norm_num)
theorem B5862709 : Blo 1875639 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B2815301 : Blo 1875639 2815301 := bbase (se 4 (by rfl) ⟨263934, by rfl⟩ : syracuseStep 2815301 = 527869) (by norm_num)
theorem B2110801 : Blo 1875639 2110801 := bbase (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) (by norm_num)
theorem B18036053 : Blo 1875639 18036053 := bbase (se 13 (by rfl) ⟨3302, by rfl⟩ : syracuseStep 18036053 = 6605) (by norm_num)
theorem B2815325 : Blo 1875639 2815325 := bbase (se 3 (by rfl) ⟨527873, by rfl⟩ : syracuseStep 2815325 = 1055747) (by norm_num)
theorem B4748645 : Blo 1875639 4748645 := bbase (se 4 (by rfl) ⟨445185, by rfl⟩ : syracuseStep 4748645 = 890371) (by norm_num)
theorem B2110837 : Blo 1875639 2110837 := bbase (se 5 (by rfl) ⟨98945, by rfl⟩ : syracuseStep 2110837 = 197891) (by norm_num)
theorem B2815349 : Blo 1875639 2815349 := bbase (se 5 (by rfl) ⟨131969, by rfl⟩ : syracuseStep 2815349 = 263939) (by norm_num)
theorem B2815373 : Blo 1875639 2815373 := bbase (se 3 (by rfl) ⟨527882, by rfl⟩ : syracuseStep 2815373 = 1055765) (by norm_num)
theorem B2110873 : Blo 1875639 2110873 := bbase (se 2 (by rfl) ⟨791577, by rfl⟩ : syracuseStep 2110873 = 1583155) (by norm_num)
theorem B3560861 : Blo 1875639 3560861 := bbase (se 3 (by rfl) ⟨667661, by rfl⟩ : syracuseStep 3560861 = 1335323) (by norm_num)
theorem B4339109 : Blo 1875639 4339109 := bbase (se 4 (by rfl) ⟨406791, by rfl⟩ : syracuseStep 4339109 = 813583) (by norm_num)
theorem B2815397 : Blo 1875639 2815397 := bbase (se 4 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 2815397 = 527887) (by norm_num)
theorem B3167653 : Blo 1875639 3167653 := bbase (se 4 (by rfl) ⟨296967, by rfl⟩ : syracuseStep 3167653 = 593935) (by norm_num)
theorem B2110909 : Blo 1875639 2110909 := bbase (se 3 (by rfl) ⟨395795, by rfl⟩ : syracuseStep 2110909 = 791591) (by norm_num)
theorem B2815421 : Blo 1875639 2815421 := bbase (se 3 (by rfl) ⟨527891, by rfl⟩ : syracuseStep 2815421 = 1055783) (by norm_num)
theorem B2815445 : Blo 1875639 2815445 := bbase (se 7 (by rfl) ⟨32993, by rfl⟩ : syracuseStep 2815445 = 65987) (by norm_num)
theorem B2004437 : Blo 1875639 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B2110945 : Blo 1875639 2110945 := bbase (se 2 (by rfl) ⟨791604, by rfl⟩ : syracuseStep 2110945 = 1583209) (by norm_num)
theorem B2815469 : Blo 1875639 2815469 := bbase (se 3 (by rfl) ⟨527900, by rfl⟩ : syracuseStep 2815469 = 1055801) (by norm_num)
theorem B2110981 : Blo 1875639 2110981 := bbase (se 4 (by rfl) ⟨197904, by rfl⟩ : syracuseStep 2110981 = 395809) (by norm_num)
theorem B9500165 : Blo 1875639 9500165 := bbase (se 4 (by rfl) ⟨890640, by rfl⟩ : syracuseStep 9500165 = 1781281) (by norm_num)
theorem B2815493 : Blo 1875639 2815493 := bbase (se 4 (by rfl) ⟨263952, by rfl⟩ : syracuseStep 2815493 = 527905) (by norm_num)
theorem B2815517 : Blo 1875639 2815517 := bbase (se 3 (by rfl) ⟨527909, by rfl⟩ : syracuseStep 2815517 = 1055819) (by norm_num)
theorem B2111017 : Blo 1875639 2111017 := bbase (se 2 (by rfl) ⟨791631, by rfl⟩ : syracuseStep 2111017 = 1583263) (by norm_num)
theorem B3561013 : Blo 1875639 3561013 := bbase (se 5 (by rfl) ⟨166922, by rfl⟩ : syracuseStep 3561013 = 333845) (by norm_num)
theorem B2815541 : Blo 1875639 2815541 := bbase (se 5 (by rfl) ⟨131978, by rfl⟩ : syracuseStep 2815541 = 263957) (by norm_num)
theorem B2111053 : Blo 1875639 2111053 := bbase (se 3 (by rfl) ⟨395822, by rfl⟩ : syracuseStep 2111053 = 791645) (by norm_num)
theorem B2815565 : Blo 1875639 2815565 := bbase (se 3 (by rfl) ⟨527918, by rfl⟩ : syracuseStep 2815565 = 1055837) (by norm_num)
theorem B2815589 : Blo 1875639 2815589 := bbase (se 4 (by rfl) ⟨263961, by rfl⟩ : syracuseStep 2815589 = 527923) (by norm_num)
theorem B2111089 : Blo 1875639 2111089 := bbase (se 2 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 2111089 = 1583317) (by norm_num)
theorem B2815613 : Blo 1875639 2815613 := bbase (se 3 (by rfl) ⟨527927, by rfl⟩ : syracuseStep 2815613 = 1055855) (by norm_num)
theorem B2111125 : Blo 1875639 2111125 := bbase (se 6 (by rfl) ⟨49479, by rfl⟩ : syracuseStep 2111125 = 98959) (by norm_num)
theorem B2815637 : Blo 1875639 2815637 := bbase (se 6 (by rfl) ⟨65991, by rfl⟩ : syracuseStep 2815637 = 131983) (by norm_num)
theorem B2815661 : Blo 1875639 2815661 := bbase (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) (by norm_num)
theorem B2111161 : Blo 1875639 2111161 := bbase (se 2 (by rfl) ⟨791685, by rfl⟩ : syracuseStep 2111161 = 1583371) (by norm_num)
theorem B4748989 : Blo 1875639 4748989 := bbase (se 3 (by rfl) ⟨890435, by rfl⟩ : syracuseStep 4748989 = 1780871) (by norm_num)
theorem B2815685 : Blo 1875639 2815685 := bbase (se 4 (by rfl) ⟨263970, by rfl⟩ : syracuseStep 2815685 = 527941) (by norm_num)
theorem B2111197 : Blo 1875639 2111197 := bbase (se 3 (by rfl) ⟨395849, by rfl⟩ : syracuseStep 2111197 = 791699) (by norm_num)
theorem B2815709 : Blo 1875639 2815709 := bbase (se 3 (by rfl) ⟨527945, by rfl⟩ : syracuseStep 2815709 = 1055891) (by norm_num)
theorem B2111233 : Blo 1875639 2111233 := bbase (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) (by norm_num)
theorem B10426133 : Blo 1875639 10426133 := bbase (se 6 (by rfl) ⟨244362, by rfl⟩ : syracuseStep 10426133 = 488725) (by norm_num)
theorem B2111269 : Blo 1875639 2111269 := bbase (se 4 (by rfl) ⟨197931, by rfl⟩ : syracuseStep 2111269 = 395863) (by norm_num)
theorem B4749101 : Blo 1875639 4749101 := bbase (se 3 (by rfl) ⟨890456, by rfl⟩ : syracuseStep 4749101 = 1780913) (by norm_num)
theorem B2111305 : Blo 1875639 2111305 := bbase (se 2 (by rfl) ⟨791739, by rfl⟩ : syracuseStep 2111305 = 1583479) (by norm_num)
theorem B3561317 : Blo 1875639 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B2111341 : Blo 1875639 2111341 := bbase (se 3 (by rfl) ⟨395876, by rfl⟩ : syracuseStep 2111341 = 791753) (by norm_num)
theorem B2111377 : Blo 1875639 2111377 := bbase (se 2 (by rfl) ⟨791766, by rfl⟩ : syracuseStep 2111377 = 1583533) (by norm_num)
theorem B2111413 : Blo 1875639 2111413 := bbase (se 5 (by rfl) ⟨98972, by rfl⟩ : syracuseStep 2111413 = 197945) (by norm_num)
theorem B4880333 : Blo 1875639 4880333 := bbase (se 3 (by rfl) ⟨915062, by rfl⟩ : syracuseStep 4880333 = 1830125) (by norm_num)
theorem B3381205 : Blo 1875639 3381205 := bbase (se 7 (by rfl) ⟨39623, by rfl⟩ : syracuseStep 3381205 = 79247) (by norm_num)
theorem B2111449 : Blo 1875639 2111449 := bbase (se 2 (by rfl) ⟨791793, by rfl⟩ : syracuseStep 2111449 = 1583587) (by norm_num)
theorem B2406373 : Blo 1875639 2406373 := bbase (se 4 (by rfl) ⟨225597, by rfl⟩ : syracuseStep 2406373 = 451195) (by norm_num)
theorem B4749293 : Blo 1875639 4749293 := bbase (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) (by norm_num)
theorem B2111485 : Blo 1875639 2111485 := bbase (se 3 (by rfl) ⟨395903, by rfl⟩ : syracuseStep 2111485 = 791807) (by norm_num)
theorem B2111521 : Blo 1875639 2111521 := bbase (se 2 (by rfl) ⟨791820, by rfl⟩ : syracuseStep 2111521 = 1583641) (by norm_num)
theorem B2111557 : Blo 1875639 2111557 := bbase (se 4 (by rfl) ⟨197958, by rfl⟩ : syracuseStep 2111557 = 395917) (by norm_num)
theorem B8018021 : Blo 1875639 8018021 := bbase (se 4 (by rfl) ⟨751689, by rfl⟩ : syracuseStep 8018021 = 1503379) (by norm_num)
theorem B2111593 : Blo 1875639 2111593 := bbase (se 2 (by rfl) ⟨791847, by rfl⟩ : syracuseStep 2111593 = 1583695) (by norm_num)
theorem B2111629 : Blo 1875639 2111629 := bbase (se 3 (by rfl) ⟨395930, by rfl⟩ : syracuseStep 2111629 = 791861) (by norm_num)
theorem B3381421 : Blo 1875639 3381421 := bbase (se 3 (by rfl) ⟨634016, by rfl⟩ : syracuseStep 3381421 = 1268033) (by norm_num)
theorem B2111665 : Blo 1875639 2111665 := bbase (se 2 (by rfl) ⟨791874, by rfl⟩ : syracuseStep 2111665 = 1583749) (by norm_num)
theorem B6330581 : Blo 1875639 6330581 := bbase (se 7 (by rfl) ⟨74186, by rfl⟩ : syracuseStep 6330581 = 148373) (by norm_num)
theorem B66771157 : Blo 1875639 66771157 := bbase (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) (by norm_num)
theorem B2111701 : Blo 1875639 2111701 := bbase (se 7 (by rfl) ⟨24746, by rfl⟩ : syracuseStep 2111701 = 49493) (by norm_num)
theorem B2373877 : Blo 1875639 2373877 := bbase (se 5 (by rfl) ⟨111275, by rfl⟩ : syracuseStep 2373877 = 222551) (by norm_num)
theorem B2111737 : Blo 1875639 2111737 := bbase (se 2 (by rfl) ⟨791901, by rfl⟩ : syracuseStep 2111737 = 1583803) (by norm_num)
theorem B2111773 : Blo 1875639 2111773 := bbase (se 3 (by rfl) ⟨395957, by rfl⟩ : syracuseStep 2111773 = 791915) (by norm_num)
theorem B3004733 : Blo 1875639 3004733 := bbase (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) (by norm_num)
theorem B4749637 : Blo 1875639 4749637 := bbase (se 4 (by rfl) ⟨445278, by rfl⟩ : syracuseStep 4749637 = 890557) (by norm_num)
theorem B3045781 : Blo 1875639 3045781 := bbase (se 6 (by rfl) ⟨71385, by rfl⟩ : syracuseStep 3045781 = 142771) (by norm_num)
theorem B2374049 : Blo 1875639 2374049 := bbase (se 2 (by rfl) ⟨890268, by rfl⟩ : syracuseStep 2374049 = 1780537) (by norm_num)
theorem B4749749 : Blo 1875639 4749749 := bbase (se 5 (by rfl) ⟨222644, by rfl⟩ : syracuseStep 4749749 = 445289) (by norm_num)
theorem B2374105 : Blo 1875639 2374105 := bbase (se 2 (by rfl) ⟨890289, by rfl⟩ : syracuseStep 2374105 = 1780579) (by norm_num)
theorem B3004933 : Blo 1875639 3004933 := bbase (se 4 (by rfl) ⟨281712, by rfl⟩ : syracuseStep 3004933 = 563425) (by norm_num)
theorem B2374201 : Blo 1875639 2374201 := bbase (se 2 (by rfl) ⟨890325, by rfl⟩ : syracuseStep 2374201 = 1780651) (by norm_num)
theorem B3562069 : Blo 1875639 3562069 := bbase (se 8 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 3562069 = 41743) (by norm_num)
theorem B4749941 : Blo 1875639 4749941 := bbase (se 5 (by rfl) ⟨222653, by rfl⟩ : syracuseStep 4749941 = 445307) (by norm_num)
theorem B6331013 : Blo 1875639 6331013 := bbase (se 4 (by rfl) ⟨593532, by rfl⟩ : syracuseStep 6331013 = 1187065) (by norm_num)
theorem B3857053 : Blo 1875639 3857053 := bbase (se 3 (by rfl) ⟨723197, by rfl⟩ : syracuseStep 3857053 = 1446395) (by norm_num)
theorem B2374373 : Blo 1875639 2374373 := bbase (se 4 (by rfl) ⟨222597, by rfl⟩ : syracuseStep 2374373 = 445195) (by norm_num)
theorem B3562213 : Blo 1875639 3562213 := bbase (se 4 (by rfl) ⟨333957, by rfl⟩ : syracuseStep 3562213 = 667915) (by norm_num)
theorem B3005189 : Blo 1875639 3005189 := bbase (se 4 (by rfl) ⟨281736, by rfl⟩ : syracuseStep 3005189 = 563473) (by norm_num)
theorem B9501461 : Blo 1875639 9501461 := bbase (se 6 (by rfl) ⟨222690, by rfl⟩ : syracuseStep 9501461 = 445381) (by norm_num)
theorem B2374429 : Blo 1875639 2374429 := bbase (se 3 (by rfl) ⟨445205, by rfl⟩ : syracuseStep 2374429 = 890411) (by norm_num)
theorem B4881269 : Blo 1875639 4881269 := bbase (se 5 (by rfl) ⟨228809, by rfl⟩ : syracuseStep 4881269 = 457619) (by norm_num)
theorem B2374525 : Blo 1875639 2374525 := bbase (se 3 (by rfl) ⟨445223, by rfl⟩ : syracuseStep 2374525 = 890447) (by norm_num)
theorem B3562373 : Blo 1875639 3562373 := bbase (se 4 (by rfl) ⟨333972, by rfl⟩ : syracuseStep 3562373 = 667945) (by norm_num)
theorem B6011813 : Blo 1875639 6011813 := bbase (se 4 (by rfl) ⟨563607, by rfl⟩ : syracuseStep 6011813 = 1127215) (by norm_num)
theorem B4750285 : Blo 1875639 4750285 := bbase (se 3 (by rfl) ⟨890678, by rfl⟩ : syracuseStep 4750285 = 1781357) (by norm_num)
theorem B3382229 : Blo 1875639 3382229 := bbase (se 7 (by rfl) ⟨39635, by rfl⟩ : syracuseStep 3382229 = 79271) (by norm_num)
theorem B3562517 : Blo 1875639 3562517 := bbase (se 6 (by rfl) ⟨83496, by rfl⟩ : syracuseStep 3562517 = 166993) (by norm_num)
theorem B2374697 : Blo 1875639 2374697 := bbase (se 2 (by rfl) ⟨890511, by rfl⟩ : syracuseStep 2374697 = 1781023) (by norm_num)
theorem B6331445 : Blo 1875639 6331445 := bbase (se 5 (by rfl) ⟨296786, by rfl⟩ : syracuseStep 6331445 = 593573) (by norm_num)
theorem B4750397 : Blo 1875639 4750397 := bbase (se 3 (by rfl) ⟨890699, by rfl⟩ : syracuseStep 4750397 = 1781399) (by norm_num)
theorem B24042581 : Blo 1875639 24042581 := bbase (se 8 (by rfl) ⟨140874, by rfl⟩ : syracuseStep 24042581 = 281749) (by norm_num)
theorem B2374753 : Blo 1875639 2374753 := bbase (se 2 (by rfl) ⟨890532, by rfl⟩ : syracuseStep 2374753 = 1781065) (by norm_num)
theorem B3382373 : Blo 1875639 3382373 := bbase (se 4 (by rfl) ⟨317097, by rfl⟩ : syracuseStep 3382373 = 634195) (by norm_num)
theorem B2374849 : Blo 1875639 2374849 := bbase (se 2 (by rfl) ⟨890568, by rfl⟩ : syracuseStep 2374849 = 1781137) (by norm_num)
theorem B4750589 : Blo 1875639 4750589 := bbase (se 3 (by rfl) ⟨890735, by rfl⟩ : syracuseStep 4750589 = 1781471) (by norm_num)
theorem B2284853 : Blo 1875639 2284853 := bbase (se 5 (by rfl) ⟨107102, by rfl⟩ : syracuseStep 2284853 = 214205) (by norm_num)
theorem B3562805 : Blo 1875639 3562805 := bbase (se 5 (by rfl) ⟨167006, by rfl⟩ : syracuseStep 3562805 = 334013) (by norm_num)
theorem B7126325 : Blo 1875639 7126325 := bbase (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) (by norm_num)
theorem B3382589 : Blo 1875639 3382589 := bbase (se 3 (by rfl) ⟨634235, by rfl⟩ : syracuseStep 3382589 = 1268471) (by norm_num)
theorem B2407745 : Blo 1875639 2407745 := bbase (se 2 (by rfl) ⟨902904, by rfl⟩ : syracuseStep 2407745 = 1805809) (by norm_num)
theorem B2375021 : Blo 1875639 2375021 := bbase (se 3 (by rfl) ⟨445316, by rfl⟩ : syracuseStep 2375021 = 890633) (by norm_num)
theorem B2375077 : Blo 1875639 2375077 := bbase (se 4 (by rfl) ⟨222663, by rfl⟩ : syracuseStep 2375077 = 445327) (by norm_num)
theorem B3562957 : Blo 1875639 3562957 := bbase (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) (by norm_num)
theorem B6331877 : Blo 1875639 6331877 := bbase (se 4 (by rfl) ⟨593613, by rfl⟩ : syracuseStep 6331877 = 1187227) (by norm_num)
theorem B2375173 : Blo 1875639 2375173 := bbase (se 4 (by rfl) ⟨222672, by rfl⟩ : syracuseStep 2375173 = 445345) (by norm_num)
theorem B4062773 : Blo 1875639 4062773 := bbase (se 5 (by rfl) ⟨190442, by rfl⟩ : syracuseStep 4062773 = 380885) (by norm_num)
theorem B4750933 : Blo 1875639 4750933 := bbase (se 8 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 4750933 = 55675) (by norm_num)
theorem B7126613 : Blo 1875639 7126613 := bbase (se 8 (by rfl) ⟨41757, by rfl⟩ : syracuseStep 7126613 = 83515) (by norm_num)
theorem B12025493 : Blo 1875639 12025493 := bbase (se 6 (by rfl) ⟨281847, by rfl⟩ : syracuseStep 12025493 = 563695) (by norm_num)
theorem B2375345 : Blo 1875639 2375345 := bbase (se 2 (by rfl) ⟨890754, by rfl⟩ : syracuseStep 2375345 = 1781509) (by norm_num)
theorem B4751045 : Blo 1875639 4751045 := bbase (se 4 (by rfl) ⟨445410, by rfl⟩ : syracuseStep 4751045 = 890821) (by norm_num)
theorem B2375401 : Blo 1875639 2375401 := bbase (se 2 (by rfl) ⟨890775, by rfl⟩ : syracuseStep 2375401 = 1781551) (by norm_num)
theorem B3563261 : Blo 1875639 3563261 := bbase (se 3 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 3563261 = 1336223) (by norm_num)
theorem B4570933 : Blo 1875639 4570933 := bbase (se 5 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 4570933 = 428525) (by norm_num)
theorem B2375497 : Blo 1875639 2375497 := bbase (se 2 (by rfl) ⟨890811, by rfl⟩ : syracuseStep 2375497 = 1781623) (by norm_num)
theorem B3006317 : Blo 1875639 3006317 := bbase (se 3 (by rfl) ⟨563684, by rfl⟩ : syracuseStep 3006317 = 1127369) (by norm_num)
theorem B4751237 : Blo 1875639 4751237 := bbase (se 4 (by rfl) ⟨445428, by rfl⟩ : syracuseStep 4751237 = 890857) (by norm_num)
theorem B6332309 : Blo 1875639 6332309 := bbase (se 6 (by rfl) ⟨148413, by rfl⟩ : syracuseStep 6332309 = 296827) (by norm_num)
theorem B21372821 : Blo 1875639 21372821 := bbase (se 6 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 21372821 = 1001851) (by norm_num)
theorem B2375669 : Blo 1875639 2375669 := bbase (se 5 (by rfl) ⟨111359, by rfl⟩ : syracuseStep 2375669 = 222719) (by norm_num)
theorem B1875971 : Blo 1875639 1875971 := bstep (se 1 (by rfl) ⟨1406978, by rfl⟩ : syracuseStep 1875971 = 2813957) B2813957
theorem B1875987 : Blo 1875639 1875987 := bstep (se 1 (by rfl) ⟨1406990, by rfl⟩ : syracuseStep 1875987 = 2813981) B2813981
theorem B1876003 : Blo 1875639 1876003 := bstep (se 1 (by rfl) ⟨1407002, by rfl⟩ : syracuseStep 1876003 = 2814005) B2814005
theorem B1876019 : Blo 1875639 1876019 := bstep (se 1 (by rfl) ⟨1407014, by rfl⟩ : syracuseStep 1876019 = 2814029) B2814029
theorem B1876035 : Blo 1875639 1876035 := bstep (se 1 (by rfl) ⟨1407026, by rfl⟩ : syracuseStep 1876035 = 2814053) B2814053
theorem B1876051 : Blo 1875639 1876051 := bstep (se 1 (by rfl) ⟨1407038, by rfl⟩ : syracuseStep 1876051 = 2814077) B2814077
theorem B1876067 : Blo 1875639 1876067 := bstep (se 1 (by rfl) ⟨1407050, by rfl⟩ : syracuseStep 1876067 = 2814101) B2814101
theorem B6332525 : Blo 1875639 6332525 := bstep (se 3 (by rfl) ⟨1187348, by rfl⟩ : syracuseStep 6332525 = 2374697) B2374697
theorem B1876083 : Blo 1875639 1876083 := bstep (se 1 (by rfl) ⟨1407062, by rfl⟩ : syracuseStep 1876083 = 2814125) B2814125
theorem B5341315 : Blo 1875639 5341315 := bstep (se 1 (by rfl) ⟨4005986, by rfl⟩ : syracuseStep 5341315 = 8011973) B8011973
theorem B1876099 : Blo 1875639 1876099 := bstep (se 1 (by rfl) ⟨1407074, by rfl⟩ : syracuseStep 1876099 = 2814149) B2814149
theorem B2670737 : Blo 1875639 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B1876115 : Blo 1875639 1876115 := bstep (se 1 (by rfl) ⟨1407086, by rfl⟩ : syracuseStep 1876115 = 2814173) B2814173
theorem B1876131 : Blo 1875639 1876131 := bstep (se 1 (by rfl) ⟨1407098, by rfl⟩ : syracuseStep 1876131 = 2814197) B2814197
theorem B6332579 : Blo 1875639 6332579 := bstep (se 1 (by rfl) ⟨4749434, by rfl⟩ : syracuseStep 6332579 = 9498869) B9498869
theorem B1876147 : Blo 1875639 1876147 := bstep (se 1 (by rfl) ⟨1407110, by rfl⟩ : syracuseStep 1876147 = 2814221) B2814221
theorem B1876163 : Blo 1875639 1876163 := bstep (se 1 (by rfl) ⟨1407122, by rfl⟩ : syracuseStep 1876163 = 2814245) B2814245
theorem B1876179 : Blo 1875639 1876179 := bstep (se 1 (by rfl) ⟨1407134, by rfl⟩ : syracuseStep 1876179 = 2814269) B2814269
theorem B1876195 : Blo 1875639 1876195 := bstep (se 1 (by rfl) ⟨1407146, by rfl⟩ : syracuseStep 1876195 = 2814293) B2814293
theorem B1876211 : Blo 1875639 1876211 := bstep (se 1 (by rfl) ⟨1407158, by rfl⟩ : syracuseStep 1876211 = 2814317) B2814317
theorem B2670851 : Blo 1875639 2670851 := bstep (se 1 (by rfl) ⟨2003138, by rfl⟩ : syracuseStep 2670851 = 4006277) B4006277
theorem B1876227 : Blo 1875639 1876227 := bstep (se 1 (by rfl) ⟨1407170, by rfl⟩ : syracuseStep 1876227 = 2814341) B2814341
theorem B1876243 : Blo 1875639 1876243 := bstep (se 1 (by rfl) ⟨1407182, by rfl⟩ : syracuseStep 1876243 = 2814365) B2814365
theorem B1876259 : Blo 1875639 1876259 := bstep (se 1 (by rfl) ⟨1407194, by rfl⟩ : syracuseStep 1876259 = 2814389) B2814389
theorem B1876275 : Blo 1875639 1876275 := bstep (se 1 (by rfl) ⟨1407206, by rfl⟩ : syracuseStep 1876275 = 2814413) B2814413
theorem B1876291 : Blo 1875639 1876291 := bstep (se 1 (by rfl) ⟨1407218, by rfl⟩ : syracuseStep 1876291 = 2814437) B2814437
theorem B2670931 : Blo 1875639 2670931 := bstep (se 1 (by rfl) ⟨2003198, by rfl⟩ : syracuseStep 2670931 = 4006397) B4006397
theorem B1876307 : Blo 1875639 1876307 := bstep (se 1 (by rfl) ⟨1407230, by rfl⟩ : syracuseStep 1876307 = 2814461) B2814461
theorem B1876323 : Blo 1875639 1876323 := bstep (se 1 (by rfl) ⟨1407242, by rfl⟩ : syracuseStep 1876323 = 2814485) B2814485
theorem B1876339 : Blo 1875639 1876339 := bstep (se 1 (by rfl) ⟨1407254, by rfl⟩ : syracuseStep 1876339 = 2814509) B2814509
theorem B1876355 : Blo 1875639 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B1876371 : Blo 1875639 1876371 := bstep (se 1 (by rfl) ⟨1407278, by rfl⟩ : syracuseStep 1876371 = 2814557) B2814557
theorem B1876387 : Blo 1875639 1876387 := bstep (se 1 (by rfl) ⟨1407290, by rfl⟩ : syracuseStep 1876387 = 2814581) B2814581
theorem B6332849 : Blo 1875639 6332849 := bstep (se 2 (by rfl) ⟨2374818, by rfl⟩ : syracuseStep 6332849 = 4749637) B4749637
theorem B1876403 : Blo 1875639 1876403 := bstep (se 1 (by rfl) ⟨1407302, by rfl⟩ : syracuseStep 1876403 = 2814605) B2814605
theorem B1876419 : Blo 1875639 1876419 := bstep (se 1 (by rfl) ⟨1407314, by rfl⟩ : syracuseStep 1876419 = 2814629) B2814629
theorem B1876435 : Blo 1875639 1876435 := bstep (se 1 (by rfl) ⟨1407326, by rfl⟩ : syracuseStep 1876435 = 2814653) B2814653
theorem B1876451 : Blo 1875639 1876451 := bstep (se 1 (by rfl) ⟨1407338, by rfl⟩ : syracuseStep 1876451 = 2814677) B2814677
theorem B1876467 : Blo 1875639 1876467 := bstep (se 1 (by rfl) ⟨1407350, by rfl⟩ : syracuseStep 1876467 = 2814701) B2814701
theorem B1876483 : Blo 1875639 1876483 := bstep (se 1 (by rfl) ⟨1407362, by rfl⟩ : syracuseStep 1876483 = 2814725) B2814725
theorem B6013453 : Blo 1875639 6013453 := bstep (se 3 (by rfl) ⟨1127522, by rfl⟩ : syracuseStep 6013453 = 2255045) B2255045
theorem B1876499 : Blo 1875639 1876499 := bstep (se 1 (by rfl) ⟨1407374, by rfl⟩ : syracuseStep 1876499 = 2814749) B2814749
theorem B1876515 : Blo 1875639 1876515 := bstep (se 1 (by rfl) ⟨1407386, by rfl⟩ : syracuseStep 1876515 = 2814773) B2814773
theorem B1876531 : Blo 1875639 1876531 := bstep (se 1 (by rfl) ⟨1407398, by rfl⟩ : syracuseStep 1876531 = 2814797) B2814797
theorem B1876547 : Blo 1875639 1876547 := bstep (se 1 (by rfl) ⟨1407410, by rfl⟩ : syracuseStep 1876547 = 2814821) B2814821
theorem B1876563 : Blo 1875639 1876563 := bstep (se 1 (by rfl) ⟨1407422, by rfl⟩ : syracuseStep 1876563 = 2814845) B2814845
theorem B1876579 : Blo 1875639 1876579 := bstep (se 1 (by rfl) ⟨1407434, by rfl⟩ : syracuseStep 1876579 = 2814869) B2814869
theorem B1876595 : Blo 1875639 1876595 := bstep (se 1 (by rfl) ⟨1407446, by rfl⟩ : syracuseStep 1876595 = 2814893) B2814893
theorem B1876611 : Blo 1875639 1876611 := bstep (se 1 (by rfl) ⟨1407458, by rfl⟩ : syracuseStep 1876611 = 2814917) B2814917
theorem B1876627 : Blo 1875639 1876627 := bstep (se 1 (by rfl) ⟨1407470, by rfl⟩ : syracuseStep 1876627 = 2814941) B2814941
theorem B1876643 : Blo 1875639 1876643 := bstep (se 1 (by rfl) ⟨1407482, by rfl⟩ : syracuseStep 1876643 = 2814965) B2814965
theorem B4006577 : Blo 1875639 4006577 := bstep (se 2 (by rfl) ⟨1502466, by rfl⟩ : syracuseStep 4006577 = 3004933) B3004933
theorem B1876659 : Blo 1875639 1876659 := bstep (se 1 (by rfl) ⟨1407494, by rfl⟩ : syracuseStep 1876659 = 2814989) B2814989
theorem B1876675 : Blo 1875639 1876675 := bstep (se 1 (by rfl) ⟨1407506, by rfl⟩ : syracuseStep 1876675 = 2815013) B2815013
theorem B1876691 : Blo 1875639 1876691 := bstep (se 1 (by rfl) ⟨1407518, by rfl⟩ : syracuseStep 1876691 = 2815037) B2815037
theorem B1876707 : Blo 1875639 1876707 := bstep (se 1 (by rfl) ⟨1407530, by rfl⟩ : syracuseStep 1876707 = 2815061) B2815061
theorem B1876723 : Blo 1875639 1876723 := bstep (se 1 (by rfl) ⟨1407542, by rfl⟩ : syracuseStep 1876723 = 2815085) B2815085
theorem B1876739 : Blo 1875639 1876739 := bstep (se 1 (by rfl) ⟨1407554, by rfl⟩ : syracuseStep 1876739 = 2815109) B2815109
theorem B1876755 : Blo 1875639 1876755 := bstep (se 1 (by rfl) ⟨1407566, by rfl⟩ : syracuseStep 1876755 = 2815133) B2815133
theorem B1876771 : Blo 1875639 1876771 := bstep (se 1 (by rfl) ⟨1407578, by rfl⟩ : syracuseStep 1876771 = 2815157) B2815157
theorem B1876787 : Blo 1875639 1876787 := bstep (se 1 (by rfl) ⟨1407590, by rfl⟩ : syracuseStep 1876787 = 2815181) B2815181
theorem B1876803 : Blo 1875639 1876803 := bstep (se 1 (by rfl) ⟨1407602, by rfl⟩ : syracuseStep 1876803 = 2815205) B2815205
theorem B8012621 : Blo 1875639 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B1876819 : Blo 1875639 1876819 := bstep (se 1 (by rfl) ⟨1407614, by rfl⟩ : syracuseStep 1876819 = 2815229) B2815229
theorem B1876835 : Blo 1875639 1876835 := bstep (se 1 (by rfl) ⟨1407626, by rfl⟩ : syracuseStep 1876835 = 2815253) B2815253
theorem B1876851 : Blo 1875639 1876851 := bstep (se 1 (by rfl) ⟨1407638, by rfl⟩ : syracuseStep 1876851 = 2815277) B2815277
theorem B2671489 : Blo 1875639 2671489 := bstep (se 2 (by rfl) ⟨1001808, by rfl⟩ : syracuseStep 2671489 = 2003617) B2003617
theorem B1876867 : Blo 1875639 1876867 := bstep (se 1 (by rfl) ⟨1407650, by rfl⟩ : syracuseStep 1876867 = 2815301) B2815301
theorem B1876883 : Blo 1875639 1876883 := bstep (se 1 (by rfl) ⟨1407662, by rfl⟩ : syracuseStep 1876883 = 2815325) B2815325
theorem B1876899 : Blo 1875639 1876899 := bstep (se 1 (by rfl) ⟨1407674, by rfl⟩ : syracuseStep 1876899 = 2815349) B2815349
theorem B1876915 : Blo 1875639 1876915 := bstep (se 1 (by rfl) ⟨1407686, by rfl⟩ : syracuseStep 1876915 = 2815373) B2815373
theorem B1876931 : Blo 1875639 1876931 := bstep (se 1 (by rfl) ⟨1407698, by rfl⟩ : syracuseStep 1876931 = 2815397) B2815397
theorem B6333389 : Blo 1875639 6333389 := bstep (se 3 (by rfl) ⟨1187510, by rfl⟩ : syracuseStep 6333389 = 2375021) B2375021
theorem B1876947 : Blo 1875639 1876947 := bstep (se 1 (by rfl) ⟨1407710, by rfl⟩ : syracuseStep 1876947 = 2815421) B2815421
theorem B1876963 : Blo 1875639 1876963 := bstep (se 1 (by rfl) ⟨1407722, by rfl⟩ : syracuseStep 1876963 = 2815445) B2815445
theorem B18039779 : Blo 1875639 18039779 := bstep (se 1 (by rfl) ⟨13529834, by rfl⟩ : syracuseStep 18039779 = 27059669) B27059669
theorem B1876979 : Blo 1875639 1876979 := bstep (se 1 (by rfl) ⟨1407734, by rfl⟩ : syracuseStep 1876979 = 2815469) B2815469
theorem B6333443 : Blo 1875639 6333443 := bstep (se 1 (by rfl) ⟨4750082, by rfl⟩ : syracuseStep 6333443 = 9500165) B9500165
theorem B1876995 : Blo 1875639 1876995 := bstep (se 1 (by rfl) ⟨1407746, by rfl⟩ : syracuseStep 1876995 = 2815493) B2815493
theorem B1877011 : Blo 1875639 1877011 := bstep (se 1 (by rfl) ⟨1407758, by rfl⟩ : syracuseStep 1877011 = 2815517) B2815517
theorem B1877027 : Blo 1875639 1877027 := bstep (se 1 (by rfl) ⟨1407770, by rfl⟩ : syracuseStep 1877027 = 2815541) B2815541
theorem B1877043 : Blo 1875639 1877043 := bstep (se 1 (by rfl) ⟨1407782, by rfl⟩ : syracuseStep 1877043 = 2815565) B2815565
theorem B1877059 : Blo 1875639 1877059 := bstep (se 1 (by rfl) ⟨1407794, by rfl⟩ : syracuseStep 1877059 = 2815589) B2815589
theorem B9495629 : Blo 1875639 9495629 := bstep (se 3 (by rfl) ⟨1780430, by rfl⟩ : syracuseStep 9495629 = 3560861) B3560861
theorem B1877075 : Blo 1875639 1877075 := bstep (se 1 (by rfl) ⟨1407806, by rfl⟩ : syracuseStep 1877075 = 2815613) B2815613
theorem B1877091 : Blo 1875639 1877091 := bstep (se 1 (by rfl) ⟨1407818, by rfl⟩ : syracuseStep 1877091 = 2815637) B2815637
theorem B1877107 : Blo 1875639 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B1877123 : Blo 1875639 1877123 := bstep (se 1 (by rfl) ⟨1407842, by rfl⟩ : syracuseStep 1877123 = 2815685) B2815685
theorem B1877139 : Blo 1875639 1877139 := bstep (se 1 (by rfl) ⟨1407854, by rfl⟩ : syracuseStep 1877139 = 2815709) B2815709
theorem B6333713 : Blo 1875639 6333713 := bstep (se 2 (by rfl) ⟨2375142, by rfl⟩ : syracuseStep 6333713 = 4750285) B4750285
theorem B3253555 : Blo 1875639 3253555 := bstep (se 1 (by rfl) ⟨2440166, by rfl⟩ : syracuseStep 3253555 = 4880333) B4880333
theorem B4506947 : Blo 1875639 4506947 := bstep (se 1 (by rfl) ⟨3380210, by rfl⟩ : syracuseStep 4506947 = 6760421) B6760421
theorem B4220369 : Blo 1875639 4220369 := bstep (se 2 (by rfl) ⟨1582638, by rfl⟩ : syracuseStep 4220369 = 3165277) B3165277
theorem B4220387 : Blo 1875639 4220387 := bstep (se 1 (by rfl) ⟨3165290, by rfl⟩ : syracuseStep 4220387 = 6330581) B6330581
theorem B5342705 : Blo 1875639 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B2672195 : Blo 1875639 2672195 := bstep (se 1 (by rfl) ⟨2004146, by rfl⟩ : syracuseStep 2672195 = 4008293) B4008293
theorem B4220657 : Blo 1875639 4220657 := bstep (se 2 (by rfl) ⟨1582746, by rfl⟩ : syracuseStep 4220657 = 3165493) B3165493
theorem B4220675 : Blo 1875639 4220675 := bstep (se 1 (by rfl) ⟨3165506, by rfl⟩ : syracuseStep 4220675 = 6331013) B6331013
theorem B6334253 : Blo 1875639 6334253 := bstep (se 3 (by rfl) ⟨1187672, by rfl⟩ : syracuseStep 6334253 = 2375345) B2375345
theorem B6334307 : Blo 1875639 6334307 := bstep (se 1 (by rfl) ⟨4750730, by rfl⟩ : syracuseStep 6334307 = 9501461) B9501461
theorem B4007875 : Blo 1875639 4007875 := bstep (se 1 (by rfl) ⟨3005906, by rfl⟩ : syracuseStep 4007875 = 6011813) B6011813
theorem B2254819 : Blo 1875639 2254819 := bstep (se 1 (by rfl) ⟨1691114, by rfl⟩ : syracuseStep 2254819 = 3382229) B3382229
theorem B5072909 : Blo 1875639 5072909 := bstep (se 3 (by rfl) ⟨951170, by rfl⟩ : syracuseStep 5072909 = 1902341) B1902341
theorem B4220945 : Blo 1875639 4220945 := bstep (se 2 (by rfl) ⟨1582854, by rfl⟩ : syracuseStep 4220945 = 3165709) B3165709
theorem B4220963 : Blo 1875639 4220963 := bstep (se 1 (by rfl) ⟨3165722, by rfl⟩ : syracuseStep 4220963 = 6331445) B6331445
theorem B4507715 : Blo 1875639 4507715 := bstep (se 1 (by rfl) ⟨3380786, by rfl⟩ : syracuseStep 4507715 = 6761573) B6761573
theorem B2254915 : Blo 1875639 2254915 := bstep (se 1 (by rfl) ⟨1691186, by rfl⟩ : syracuseStep 2254915 = 3382373) B3382373
theorem B2852977 : Blo 1875639 2852977 := bstep (se 2 (by rfl) ⟨1069866, by rfl⟩ : syracuseStep 2852977 = 2139733) B2139733
theorem B6334577 : Blo 1875639 6334577 := bstep (se 2 (by rfl) ⟨2375466, by rfl⟩ : syracuseStep 6334577 = 4750933) B4750933
theorem B2853025 : Blo 1875639 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B2255059 : Blo 1875639 2255059 := bstep (se 1 (by rfl) ⟨1691294, by rfl⟩ : syracuseStep 2255059 = 3382589) B3382589
theorem B4221233 : Blo 1875639 4221233 := bstep (se 2 (by rfl) ⟨1582962, by rfl⟩ : syracuseStep 4221233 = 3165925) B3165925
theorem B4221251 : Blo 1875639 4221251 := bstep (se 1 (by rfl) ⟨3165938, by rfl⟩ : syracuseStep 4221251 = 6331877) B6331877
theorem B5343661 : Blo 1875639 5343661 := bstep (se 3 (by rfl) ⟨1001936, by rfl⟩ : syracuseStep 5343661 = 2003873) B2003873
theorem B4221521 : Blo 1875639 4221521 := bstep (se 2 (by rfl) ⟨1583070, by rfl⟩ : syracuseStep 4221521 = 3166141) B3166141
theorem B4221539 : Blo 1875639 4221539 := bstep (se 1 (by rfl) ⟨3166154, by rfl⟩ : syracuseStep 4221539 = 6332309) B6332309
theorem B14248547 : Blo 1875639 14248547 := bstep (se 1 (by rfl) ⟨10686410, by rfl⟩ : syracuseStep 14248547 = 21372821) B21372821
theorem B20286065 : Blo 1875639 20286065 := bstep (se 2 (by rfl) ⟨7607274, by rfl⟩ : syracuseStep 20286065 = 15214549) B15214549
theorem B4508273 : Blo 1875639 4508273 := bstep (se 2 (by rfl) ⟨1690602, by rfl⟩ : syracuseStep 4508273 = 3381205) B3381205
theorem B6335117 : Blo 1875639 6335117 := bstep (se 3 (by rfl) ⟨1187834, by rfl⟩ : syracuseStep 6335117 = 2375669) B2375669
theorem B5343889 : Blo 1875639 5343889 := bstep (se 2 (by rfl) ⟨2003958, by rfl⟩ : syracuseStep 5343889 = 4007917) B4007917
theorem B6335171 : Blo 1875639 6335171 := bstep (se 1 (by rfl) ⟨4751378, by rfl⟩ : syracuseStep 6335171 = 9502757) B9502757
theorem B5344049 : Blo 1875639 5344049 := bstep (se 2 (by rfl) ⟨2004018, by rfl⟩ : syracuseStep 5344049 = 4008037) B4008037
theorem B4221809 : Blo 1875639 4221809 := bstep (se 2 (by rfl) ⟨1583178, by rfl⟩ : syracuseStep 4221809 = 3166357) B3166357
theorem B4221827 : Blo 1875639 4221827 := bstep (se 1 (by rfl) ⟨3166370, by rfl⟩ : syracuseStep 4221827 = 6332741) B6332741
theorem B10685317 : Blo 1875639 10685317 := bstep (se 4 (by rfl) ⟨1001748, by rfl⟩ : syracuseStep 10685317 = 2003497) B2003497
theorem B4508561 : Blo 1875639 4508561 := bstep (se 2 (by rfl) ⟨1690710, by rfl⟩ : syracuseStep 4508561 = 3381421) B3381421
theorem B5344163 : Blo 1875639 5344163 := bstep (se 1 (by rfl) ⟨4008122, by rfl⟩ : syracuseStep 5344163 = 8016245) B8016245
theorem B3804131 : Blo 1875639 3804131 := bstep (se 1 (by rfl) ⟨2853098, by rfl⟩ : syracuseStep 3804131 = 5706197) B5706197
theorem B3165169 : Blo 1875639 3165169 := bstep (se 2 (by rfl) ⟨1186938, by rfl⟩ : syracuseStep 3165169 = 2373877) B2373877
theorem B3165203 : Blo 1875639 3165203 := bstep (se 1 (by rfl) ⟨2373902, by rfl⟩ : syracuseStep 3165203 = 4747805) B4747805
theorem B8121379 : Blo 1875639 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B5704835 : Blo 1875639 5704835 := bstep (se 1 (by rfl) ⟨4278626, by rfl⟩ : syracuseStep 5704835 = 8557253) B8557253
theorem B4222097 : Blo 1875639 4222097 := bstep (se 2 (by rfl) ⟨1583286, by rfl⟩ : syracuseStep 4222097 = 3166573) B3166573
theorem B3165331 : Blo 1875639 3165331 := bstep (se 1 (by rfl) ⟨2373998, by rfl⟩ : syracuseStep 3165331 = 4747997) B4747997
theorem B4222115 : Blo 1875639 4222115 := bstep (se 1 (by rfl) ⟨3166586, by rfl⟩ : syracuseStep 4222115 = 6333173) B6333173
theorem B37555397 : Blo 1875639 37555397 := bstep (se 4 (by rfl) ⟨3520818, by rfl⟩ : syracuseStep 37555397 = 7041637) B7041637
theorem B3165473 : Blo 1875639 3165473 := bstep (se 2 (by rfl) ⟨1187052, by rfl⟩ : syracuseStep 3165473 = 2374105) B2374105
theorem B3165601 : Blo 1875639 3165601 := bstep (se 2 (by rfl) ⟨1187100, by rfl⟩ : syracuseStep 3165601 = 2374201) B2374201
theorem B4222385 : Blo 1875639 4222385 := bstep (se 2 (by rfl) ⟨1583394, by rfl⟩ : syracuseStep 4222385 = 3166789) B3166789
theorem B3165635 : Blo 1875639 3165635 := bstep (se 1 (by rfl) ⟨2374226, by rfl⟩ : syracuseStep 3165635 = 4748453) B4748453
theorem B4222403 : Blo 1875639 4222403 := bstep (se 1 (by rfl) ⟨3166802, by rfl⟩ : syracuseStep 4222403 = 6333605) B6333605
theorem B2813459 : Blo 1875639 2813459 := bstep (se 1 (by rfl) ⟨2110094, by rfl⟩ : syracuseStep 2813459 = 4220189) B4220189
theorem B2813489 : Blo 1875639 2813489 := bstep (se 2 (by rfl) ⟨1055058, by rfl⟩ : syracuseStep 2813489 = 2110117) B2110117
theorem B2813507 : Blo 1875639 2813507 := bstep (se 1 (by rfl) ⟨2110130, by rfl⟩ : syracuseStep 2813507 = 4220261) B4220261
theorem B3165763 : Blo 1875639 3165763 := bstep (se 1 (by rfl) ⟨2374322, by rfl⟩ : syracuseStep 3165763 = 4748645) B4748645
theorem B2813537 : Blo 1875639 2813537 := bstep (se 2 (by rfl) ⟨1055076, by rfl⟩ : syracuseStep 2813537 = 2110153) B2110153
theorem B2813555 : Blo 1875639 2813555 := bstep (se 1 (by rfl) ⟨2110166, by rfl⟩ : syracuseStep 2813555 = 4220333) B4220333
theorem B2813585 : Blo 1875639 2813585 := bstep (se 2 (by rfl) ⟨1055094, by rfl⟩ : syracuseStep 2813585 = 2110189) B2110189
theorem B2813603 : Blo 1875639 2813603 := bstep (se 1 (by rfl) ⟨2110202, by rfl⟩ : syracuseStep 2813603 = 4220405) B4220405
theorem B2813633 : Blo 1875639 2813633 := bstep (se 2 (by rfl) ⟨1055112, by rfl⟩ : syracuseStep 2813633 = 2110225) B2110225
theorem B3165905 : Blo 1875639 3165905 := bstep (se 2 (by rfl) ⟨1187214, by rfl⟩ : syracuseStep 3165905 = 2374429) B2374429
theorem B4222673 : Blo 1875639 4222673 := bstep (se 2 (by rfl) ⟨1583502, by rfl⟩ : syracuseStep 4222673 = 3167005) B3167005
theorem B2813651 : Blo 1875639 2813651 := bstep (se 1 (by rfl) ⟨2110238, by rfl⟩ : syracuseStep 2813651 = 4220477) B4220477
theorem B4222691 : Blo 1875639 4222691 := bstep (se 1 (by rfl) ⟨3167018, by rfl⟩ : syracuseStep 4222691 = 6334037) B6334037
theorem B2813681 : Blo 1875639 2813681 := bstep (se 2 (by rfl) ⟨1055130, by rfl⟩ : syracuseStep 2813681 = 2110261) B2110261
theorem B2813699 : Blo 1875639 2813699 := bstep (se 1 (by rfl) ⟨2110274, by rfl⟩ : syracuseStep 2813699 = 4220549) B4220549
theorem B11570957 : Blo 1875639 11570957 := bstep (se 3 (by rfl) ⟨2169554, by rfl⟩ : syracuseStep 11570957 = 4339109) B4339109
theorem B2813729 : Blo 1875639 2813729 := bstep (se 2 (by rfl) ⟨1055148, by rfl⟩ : syracuseStep 2813729 = 2110297) B2110297
theorem B5140273 : Blo 1875639 5140273 := bstep (se 2 (by rfl) ⟨1927602, by rfl⟩ : syracuseStep 5140273 = 3855205) B3855205
theorem B2813747 : Blo 1875639 2813747 := bstep (se 1 (by rfl) ⟨2110310, by rfl⟩ : syracuseStep 2813747 = 4220621) B4220621
theorem B2813777 : Blo 1875639 2813777 := bstep (se 2 (by rfl) ⟨1055166, by rfl⟩ : syracuseStep 2813777 = 2110333) B2110333
theorem B3166033 : Blo 1875639 3166033 := bstep (se 2 (by rfl) ⟨1187262, by rfl⟩ : syracuseStep 3166033 = 2374525) B2374525
theorem B2813795 : Blo 1875639 2813795 := bstep (se 1 (by rfl) ⟨2110346, by rfl⟩ : syracuseStep 2813795 = 4220693) B4220693
theorem B6950755 : Blo 1875639 6950755 := bstep (se 1 (by rfl) ⟨5213066, by rfl⟩ : syracuseStep 6950755 = 10426133) B10426133
theorem B3166067 : Blo 1875639 3166067 := bstep (se 1 (by rfl) ⟨2374550, by rfl⟩ : syracuseStep 3166067 = 4749101) B4749101
theorem B2813825 : Blo 1875639 2813825 := bstep (se 2 (by rfl) ⟨1055184, by rfl⟩ : syracuseStep 2813825 = 2110369) B2110369
theorem B56323981 : Blo 1875639 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B5345165 : Blo 1875639 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B6418321 : Blo 1875639 6418321 := bstep (se 2 (by rfl) ⟨2406870, by rfl⟩ : syracuseStep 6418321 = 4813741) B4813741
theorem B2813843 : Blo 1875639 2813843 := bstep (se 1 (by rfl) ⟨2110382, by rfl⟩ : syracuseStep 2813843 = 4220765) B4220765
theorem B2813873 : Blo 1875639 2813873 := bstep (se 2 (by rfl) ⟨1055202, by rfl⟩ : syracuseStep 2813873 = 2110405) B2110405
theorem B9498545 : Blo 1875639 9498545 := bstep (se 2 (by rfl) ⟨3561954, by rfl⟩ : syracuseStep 9498545 = 7123909) B7123909
theorem B2813891 : Blo 1875639 2813891 := bstep (se 1 (by rfl) ⟨2110418, by rfl⟩ : syracuseStep 2813891 = 4220837) B4220837
theorem B2813921 : Blo 1875639 2813921 := bstep (se 2 (by rfl) ⟨1055220, by rfl⟩ : syracuseStep 2813921 = 2110441) B2110441
theorem B4222961 : Blo 1875639 4222961 := bstep (se 2 (by rfl) ⟨1583610, by rfl⟩ : syracuseStep 4222961 = 3167221) B3167221
theorem B2813939 : Blo 1875639 2813939 := bstep (se 1 (by rfl) ⟨2110454, by rfl⟩ : syracuseStep 2813939 = 4220909) B4220909
theorem B3166195 : Blo 1875639 3166195 := bstep (se 1 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 3166195 = 4749293) B4749293
theorem B4222979 : Blo 1875639 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B2813969 : Blo 1875639 2813969 := bstep (se 2 (by rfl) ⟨1055238, by rfl⟩ : syracuseStep 2813969 = 2110477) B2110477
theorem B3805201 : Blo 1875639 3805201 := bstep (se 2 (by rfl) ⟨1426950, by rfl⟩ : syracuseStep 3805201 = 2853901) B2853901
theorem B2813987 : Blo 1875639 2813987 := bstep (se 1 (by rfl) ⟨2110490, by rfl⟩ : syracuseStep 2813987 = 4220981) B4220981
theorem B2814017 : Blo 1875639 2814017 := bstep (se 2 (by rfl) ⟨1055256, by rfl⟩ : syracuseStep 2814017 = 2110513) B2110513
theorem B5345347 : Blo 1875639 5345347 := bstep (se 1 (by rfl) ⟨4009010, by rfl⟩ : syracuseStep 5345347 = 8018021) B8018021
theorem B2814035 : Blo 1875639 2814035 := bstep (se 1 (by rfl) ⟨2110526, by rfl⟩ : syracuseStep 2814035 = 4221053) B4221053
theorem B2814065 : Blo 1875639 2814065 := bstep (se 2 (by rfl) ⟨1055274, by rfl⟩ : syracuseStep 2814065 = 2110549) B2110549
theorem B3166337 : Blo 1875639 3166337 := bstep (se 2 (by rfl) ⟨1187376, by rfl⟩ : syracuseStep 3166337 = 2374753) B2374753
theorem B2814083 : Blo 1875639 2814083 := bstep (se 1 (by rfl) ⟨2110562, by rfl⟩ : syracuseStep 2814083 = 4221125) B4221125
theorem B2814113 : Blo 1875639 2814113 := bstep (se 2 (by rfl) ⟨1055292, by rfl⟩ : syracuseStep 2814113 = 2110585) B2110585
theorem B6009005 : Blo 1875639 6009005 := bstep (se 3 (by rfl) ⟨1126688, by rfl⟩ : syracuseStep 6009005 = 2253377) B2253377
theorem B2814131 : Blo 1875639 2814131 := bstep (se 1 (by rfl) ⟨2110598, by rfl⟩ : syracuseStep 2814131 = 4221197) B4221197
theorem B2814161 : Blo 1875639 2814161 := bstep (se 2 (by rfl) ⟨1055310, by rfl⟩ : syracuseStep 2814161 = 2110621) B2110621
theorem B2814179 : Blo 1875639 2814179 := bstep (se 1 (by rfl) ⟨2110634, by rfl⟩ : syracuseStep 2814179 = 4221269) B4221269
theorem B2814209 : Blo 1875639 2814209 := bstep (se 2 (by rfl) ⟨1055328, by rfl⟩ : syracuseStep 2814209 = 2110657) B2110657
theorem B3166465 : Blo 1875639 3166465 := bstep (se 2 (by rfl) ⟨1187424, by rfl⟩ : syracuseStep 3166465 = 2374849) B2374849
theorem B4223249 : Blo 1875639 4223249 := bstep (se 2 (by rfl) ⟨1583718, by rfl⟩ : syracuseStep 4223249 = 3167437) B3167437
theorem B2814227 : Blo 1875639 2814227 := bstep (se 1 (by rfl) ⟨2110670, by rfl⟩ : syracuseStep 2814227 = 4221341) B4221341
theorem B3166499 : Blo 1875639 3166499 := bstep (se 1 (by rfl) ⟨2374874, by rfl⟩ : syracuseStep 3166499 = 4749749) B4749749
theorem B4223267 : Blo 1875639 4223267 := bstep (se 1 (by rfl) ⟨3167450, by rfl⟩ : syracuseStep 4223267 = 6334901) B6334901
theorem B2814257 : Blo 1875639 2814257 := bstep (se 2 (by rfl) ⟨1055346, by rfl⟩ : syracuseStep 2814257 = 2110693) B2110693
theorem B2814275 : Blo 1875639 2814275 := bstep (se 1 (by rfl) ⟨2110706, by rfl⟩ : syracuseStep 2814275 = 4221413) B4221413
theorem B2814305 : Blo 1875639 2814305 := bstep (se 2 (by rfl) ⟨1055364, by rfl⟩ : syracuseStep 2814305 = 2110729) B2110729
theorem B2814323 : Blo 1875639 2814323 := bstep (se 1 (by rfl) ⟨2110742, by rfl⟩ : syracuseStep 2814323 = 4221485) B4221485
theorem B2814353 : Blo 1875639 2814353 := bstep (se 2 (by rfl) ⟨1055382, by rfl⟩ : syracuseStep 2814353 = 2110765) B2110765
theorem B2814371 : Blo 1875639 2814371 := bstep (se 1 (by rfl) ⟨2110778, by rfl⟩ : syracuseStep 2814371 = 4221557) B4221557
theorem B3166627 : Blo 1875639 3166627 := bstep (se 1 (by rfl) ⟨2374970, by rfl⟩ : syracuseStep 3166627 = 4749941) B4749941
theorem B7606705 : Blo 1875639 7606705 := bstep (se 2 (by rfl) ⟨2852514, by rfl⟩ : syracuseStep 7606705 = 5705029) B5705029
theorem B2814401 : Blo 1875639 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B2814419 : Blo 1875639 2814419 := bstep (se 1 (by rfl) ⟨2110814, by rfl⟩ : syracuseStep 2814419 = 4221629) B4221629
theorem B2814449 : Blo 1875639 2814449 := bstep (se 2 (by rfl) ⟨1055418, by rfl⟩ : syracuseStep 2814449 = 2110837) B2110837
theorem B11416049 : Blo 1875639 11416049 := bstep (se 2 (by rfl) ⟨4281018, by rfl⟩ : syracuseStep 11416049 = 8562037) B8562037
theorem B2003459 : Blo 1875639 2003459 := bstep (se 1 (by rfl) ⟨1502594, by rfl⟩ : syracuseStep 2003459 = 3005189) B3005189
theorem B2814467 : Blo 1875639 2814467 := bstep (se 1 (by rfl) ⟨2110850, by rfl⟩ : syracuseStep 2814467 = 4221701) B4221701
theorem B2814497 : Blo 1875639 2814497 := bstep (se 2 (by rfl) ⟨1055436, by rfl⟩ : syracuseStep 2814497 = 2110873) B2110873
theorem B3166769 : Blo 1875639 3166769 := bstep (se 2 (by rfl) ⟨1187538, by rfl⟩ : syracuseStep 3166769 = 2375077) B2375077
theorem B4223537 : Blo 1875639 4223537 := bstep (se 2 (by rfl) ⟨1583826, by rfl⟩ : syracuseStep 4223537 = 3167653) B3167653
theorem B2814515 : Blo 1875639 2814515 := bstep (se 1 (by rfl) ⟨2110886, by rfl⟩ : syracuseStep 2814515 = 4221773) B4221773
theorem B4223555 : Blo 1875639 4223555 := bstep (se 1 (by rfl) ⟨3167666, by rfl⟩ : syracuseStep 4223555 = 6335333) B6335333
theorem B2814545 : Blo 1875639 2814545 := bstep (se 2 (by rfl) ⟨1055454, by rfl⟩ : syracuseStep 2814545 = 2110909) B2110909
theorem B2814563 : Blo 1875639 2814563 := bstep (se 1 (by rfl) ⟨2110922, by rfl⟩ : syracuseStep 2814563 = 4221845) B4221845
theorem B2814593 : Blo 1875639 2814593 := bstep (se 2 (by rfl) ⟨1055472, by rfl⟩ : syracuseStep 2814593 = 2110945) B2110945
theorem B2110099 : Blo 1875639 2110099 := bstep (se 1 (by rfl) ⟨1582574, by rfl⟩ : syracuseStep 2110099 = 3165149) B3165149
theorem B2814611 : Blo 1875639 2814611 := bstep (se 1 (by rfl) ⟨2110958, by rfl⟩ : syracuseStep 2814611 = 4221917) B4221917
theorem B11727523 : Blo 1875639 11727523 := bstep (se 1 (by rfl) ⟨8795642, by rfl⟩ : syracuseStep 11727523 = 17591285) B17591285
theorem B2814641 : Blo 1875639 2814641 := bstep (se 2 (by rfl) ⟨1055490, by rfl⟩ : syracuseStep 2814641 = 2110981) B2110981
theorem B3166897 : Blo 1875639 3166897 := bstep (se 2 (by rfl) ⟨1187586, by rfl⟩ : syracuseStep 3166897 = 2375173) B2375173
theorem B3011267 : Blo 1875639 3011267 := bstep (se 1 (by rfl) ⟨2258450, by rfl⟩ : syracuseStep 3011267 = 4516901) B4516901
theorem B2814659 : Blo 1875639 2814659 := bstep (se 1 (by rfl) ⟨2110994, by rfl⟩ : syracuseStep 2814659 = 4221989) B4221989
theorem B3166931 : Blo 1875639 3166931 := bstep (se 1 (by rfl) ⟨2375198, by rfl⟩ : syracuseStep 3166931 = 4750397) B4750397
theorem B2814689 : Blo 1875639 2814689 := bstep (se 2 (by rfl) ⟨1055508, by rfl⟩ : syracuseStep 2814689 = 2111017) B2111017
theorem B16028387 : Blo 1875639 16028387 := bstep (se 1 (by rfl) ⟨12021290, by rfl⟩ : syracuseStep 16028387 = 24042581) B24042581
theorem B4748017 : Blo 1875639 4748017 := bstep (se 2 (by rfl) ⟨1780506, by rfl⟩ : syracuseStep 4748017 = 3561013) B3561013
theorem B7123697 : Blo 1875639 7123697 := bstep (se 2 (by rfl) ⟨2671386, by rfl⟩ : syracuseStep 7123697 = 5342773) B5342773
theorem B2814707 : Blo 1875639 2814707 := bstep (se 1 (by rfl) ⟨2111030, by rfl⟩ : syracuseStep 2814707 = 4222061) B4222061
theorem B2814737 : Blo 1875639 2814737 := bstep (se 2 (by rfl) ⟨1055526, by rfl⟩ : syracuseStep 2814737 = 2111053) B2111053
theorem B51335957 : Blo 1875639 51335957 := bstep (se 6 (by rfl) ⟨1203186, by rfl⟩ : syracuseStep 51335957 = 2406373) B2406373
theorem B2110243 : Blo 1875639 2110243 := bstep (se 1 (by rfl) ⟨1582682, by rfl⟩ : syracuseStep 2110243 = 3165365) B3165365
theorem B2814755 : Blo 1875639 2814755 := bstep (se 1 (by rfl) ⟨2111066, by rfl⟩ : syracuseStep 2814755 = 4222133) B4222133
theorem B2814785 : Blo 1875639 2814785 := bstep (se 2 (by rfl) ⟨1055544, by rfl⟩ : syracuseStep 2814785 = 2111089) B2111089
theorem B10687301 : Blo 1875639 10687301 := bstep (se 4 (by rfl) ⟨1001934, by rfl⟩ : syracuseStep 10687301 = 2003869) B2003869
theorem B2814803 : Blo 1875639 2814803 := bstep (se 1 (by rfl) ⟨2111102, by rfl⟩ : syracuseStep 2814803 = 4222205) B4222205
theorem B3167059 : Blo 1875639 3167059 := bstep (se 1 (by rfl) ⟨2375294, by rfl⟩ : syracuseStep 3167059 = 4750589) B4750589
theorem B2814833 : Blo 1875639 2814833 := bstep (se 2 (by rfl) ⟨1055562, by rfl⟩ : syracuseStep 2814833 = 2111125) B2111125
theorem B2814851 : Blo 1875639 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B2814881 : Blo 1875639 2814881 := bstep (se 2 (by rfl) ⟨1055580, by rfl⟩ : syracuseStep 2814881 = 2111161) B2111161
theorem B11572145 : Blo 1875639 11572145 := bstep (se 2 (by rfl) ⟨4339554, by rfl⟩ : syracuseStep 11572145 = 8679109) B8679109
theorem B2110387 : Blo 1875639 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B2814899 : Blo 1875639 2814899 := bstep (se 1 (by rfl) ⟨2111174, by rfl⟩ : syracuseStep 2814899 = 4222349) B4222349
theorem B2814929 : Blo 1875639 2814929 := bstep (se 2 (by rfl) ⟨1055598, by rfl⟩ : syracuseStep 2814929 = 2111197) B2111197
theorem B2814947 : Blo 1875639 2814947 := bstep (se 1 (by rfl) ⟨2111210, by rfl⟩ : syracuseStep 2814947 = 4222421) B4222421
theorem B3167201 : Blo 1875639 3167201 := bstep (se 2 (by rfl) ⟨1187700, by rfl⟩ : syracuseStep 3167201 = 2375401) B2375401
theorem B5706733 : Blo 1875639 5706733 := bstep (se 3 (by rfl) ⟨1070012, by rfl⟩ : syracuseStep 5706733 = 2140025) B2140025
theorem B2814977 : Blo 1875639 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B4748291 : Blo 1875639 4748291 := bstep (se 1 (by rfl) ⟨3561218, by rfl⟩ : syracuseStep 4748291 = 7122437) B7122437
theorem B2814995 : Blo 1875639 2814995 := bstep (se 1 (by rfl) ⟨2111246, by rfl⟩ : syracuseStep 2814995 = 4222493) B4222493
theorem B2708515 : Blo 1875639 2708515 := bstep (se 1 (by rfl) ⟨2031386, by rfl⟩ : syracuseStep 2708515 = 4062773) B4062773
theorem B2815025 : Blo 1875639 2815025 := bstep (se 2 (by rfl) ⟨1055634, by rfl⟩ : syracuseStep 2815025 = 2111269) B2111269
theorem B2110531 : Blo 1875639 2110531 := bstep (se 1 (by rfl) ⟨1582898, by rfl⟩ : syracuseStep 2110531 = 3165797) B3165797
theorem B2815043 : Blo 1875639 2815043 := bstep (se 1 (by rfl) ⟨2111282, by rfl⟩ : syracuseStep 2815043 = 4222565) B4222565
theorem B2815073 : Blo 1875639 2815073 := bstep (se 2 (by rfl) ⟨1055652, by rfl⟩ : syracuseStep 2815073 = 2111305) B2111305
theorem B3167329 : Blo 1875639 3167329 := bstep (se 2 (by rfl) ⟨1187748, by rfl⟩ : syracuseStep 3167329 = 2375497) B2375497
theorem B8016995 : Blo 1875639 8016995 := bstep (se 1 (by rfl) ⟨6012746, by rfl⟩ : syracuseStep 8016995 = 12025493) B12025493
theorem B2815091 : Blo 1875639 2815091 := bstep (se 1 (by rfl) ⟨2111318, by rfl⟩ : syracuseStep 2815091 = 4222637) B4222637
theorem B3167363 : Blo 1875639 3167363 := bstep (se 1 (by rfl) ⟨2375522, by rfl⟩ : syracuseStep 3167363 = 4751045) B4751045
theorem B2815121 : Blo 1875639 2815121 := bstep (se 2 (by rfl) ⟨1055670, by rfl⟩ : syracuseStep 2815121 = 2111341) B2111341
theorem B2815139 : Blo 1875639 2815139 := bstep (se 1 (by rfl) ⟨2111354, by rfl⟩ : syracuseStep 2815139 = 4222709) B4222709
theorem B4748483 : Blo 1875639 4748483 := bstep (se 1 (by rfl) ⟨3561362, by rfl⟩ : syracuseStep 4748483 = 7122725) B7122725
theorem B2815169 : Blo 1875639 2815169 := bstep (se 2 (by rfl) ⟨1055688, by rfl⟩ : syracuseStep 2815169 = 2111377) B2111377
theorem B2110675 : Blo 1875639 2110675 := bstep (se 1 (by rfl) ⟨1583006, by rfl⟩ : syracuseStep 2110675 = 3166013) B3166013
theorem B2815187 : Blo 1875639 2815187 := bstep (se 1 (by rfl) ⟨2111390, by rfl⟩ : syracuseStep 2815187 = 4222781) B4222781
theorem B2815217 : Blo 1875639 2815217 := bstep (se 2 (by rfl) ⟨1055706, by rfl⟩ : syracuseStep 2815217 = 2111413) B2111413
theorem B2004211 : Blo 1875639 2004211 := bstep (se 1 (by rfl) ⟨1503158, by rfl⟩ : syracuseStep 2004211 = 3006317) B3006317
theorem B2815235 : Blo 1875639 2815235 := bstep (se 1 (by rfl) ⟨2111426, by rfl⟩ : syracuseStep 2815235 = 4222853) B4222853
theorem B3167491 : Blo 1875639 3167491 := bstep (se 1 (by rfl) ⟨2375618, by rfl⟩ : syracuseStep 3167491 = 4751237) B4751237
theorem B2815265 : Blo 1875639 2815265 := bstep (se 2 (by rfl) ⟨1055724, by rfl⟩ : syracuseStep 2815265 = 2111449) B2111449
theorem B2815283 : Blo 1875639 2815283 := bstep (se 1 (by rfl) ⟨2111462, by rfl⟩ : syracuseStep 2815283 = 4222925) B4222925
theorem B2815313 : Blo 1875639 2815313 := bstep (se 2 (by rfl) ⟨1055742, by rfl⟩ : syracuseStep 2815313 = 2111485) B2111485
theorem B2110819 : Blo 1875639 2110819 := bstep (se 1 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 2110819 = 3166229) B3166229
theorem B9500003 : Blo 1875639 9500003 := bstep (se 1 (by rfl) ⟨7125002, by rfl⟩ : syracuseStep 9500003 = 14250005) B14250005
theorem B2815331 : Blo 1875639 2815331 := bstep (se 1 (by rfl) ⟨2111498, by rfl⟩ : syracuseStep 2815331 = 4222997) B4222997
theorem B2815361 : Blo 1875639 2815361 := bstep (se 2 (by rfl) ⟨1055760, by rfl⟩ : syracuseStep 2815361 = 2111521) B2111521
theorem B3167633 : Blo 1875639 3167633 := bstep (se 2 (by rfl) ⟨1187862, by rfl⟩ : syracuseStep 3167633 = 2375725) B2375725
theorem B2815379 : Blo 1875639 2815379 := bstep (se 1 (by rfl) ⟨2111534, by rfl⟩ : syracuseStep 2815379 = 4223069) B4223069
theorem B2815409 : Blo 1875639 2815409 := bstep (se 2 (by rfl) ⟨1055778, by rfl⟩ : syracuseStep 2815409 = 2111557) B2111557
theorem B2815427 : Blo 1875639 2815427 := bstep (se 1 (by rfl) ⟨2111570, by rfl⟩ : syracuseStep 2815427 = 4223141) B4223141
theorem B6763981 : Blo 1875639 6763981 := bstep (se 3 (by rfl) ⟨1268246, by rfl⟩ : syracuseStep 6763981 = 2536493) B2536493
theorem B2815457 : Blo 1875639 2815457 := bstep (se 2 (by rfl) ⟨1055796, by rfl⟩ : syracuseStep 2815457 = 2111593) B2111593
theorem B2110963 : Blo 1875639 2110963 := bstep (se 1 (by rfl) ⟨1583222, by rfl⟩ : syracuseStep 2110963 = 3166445) B3166445
theorem B2815475 : Blo 1875639 2815475 := bstep (se 1 (by rfl) ⟨2111606, by rfl⟩ : syracuseStep 2815475 = 4223213) B4223213
theorem B2815505 : Blo 1875639 2815505 := bstep (se 2 (by rfl) ⟨1055814, by rfl⟩ : syracuseStep 2815505 = 2111629) B2111629
theorem B2815523 : Blo 1875639 2815523 := bstep (se 1 (by rfl) ⟨2111642, by rfl⟩ : syracuseStep 2815523 = 4223285) B4223285
theorem B2815553 : Blo 1875639 2815553 := bstep (se 2 (by rfl) ⟨1055832, by rfl⟩ : syracuseStep 2815553 = 2111665) B2111665
theorem B2815571 : Blo 1875639 2815571 := bstep (se 1 (by rfl) ⟨2111678, by rfl⟩ : syracuseStep 2815571 = 4223357) B4223357
theorem B3561059 : Blo 1875639 3561059 := bstep (se 1 (by rfl) ⟨2670794, by rfl⟩ : syracuseStep 3561059 = 5341589) B5341589
theorem B89028209 : Blo 1875639 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B2815601 : Blo 1875639 2815601 := bstep (se 2 (by rfl) ⟨1055850, by rfl⟩ : syracuseStep 2815601 = 2111701) B2111701
theorem B2111107 : Blo 1875639 2111107 := bstep (se 1 (by rfl) ⟨1583330, by rfl⟩ : syracuseStep 2111107 = 3166661) B3166661
theorem B2815619 : Blo 1875639 2815619 := bstep (se 1 (by rfl) ⟨2111714, by rfl⟩ : syracuseStep 2815619 = 4223429) B4223429
theorem B2815649 : Blo 1875639 2815649 := bstep (se 2 (by rfl) ⟨1055868, by rfl⟩ : syracuseStep 2815649 = 2111737) B2111737
theorem B2815667 : Blo 1875639 2815667 := bstep (se 1 (by rfl) ⟨2111750, by rfl⟩ : syracuseStep 2815667 = 4223501) B4223501
theorem B2815697 : Blo 1875639 2815697 := bstep (se 2 (by rfl) ⟨1055886, by rfl⟩ : syracuseStep 2815697 = 2111773) B2111773
theorem B6010595 : Blo 1875639 6010595 := bstep (se 1 (by rfl) ⟨4507946, by rfl⟩ : syracuseStep 6010595 = 9015893) B9015893
theorem B2111251 : Blo 1875639 2111251 := bstep (se 1 (by rfl) ⟨1583438, by rfl⟩ : syracuseStep 2111251 = 3166877) B3166877
theorem B3561347 : Blo 1875639 3561347 := bstep (se 1 (by rfl) ⟨2671010, by rfl⟩ : syracuseStep 3561347 = 5342021) B5342021
theorem B6010787 : Blo 1875639 6010787 := bstep (se 1 (by rfl) ⟨4508090, by rfl⟩ : syracuseStep 6010787 = 9016181) B9016181
theorem B2111395 : Blo 1875639 2111395 := bstep (se 1 (by rfl) ⟨1583546, by rfl⟩ : syracuseStep 2111395 = 3167093) B3167093
theorem B2111539 : Blo 1875639 2111539 := bstep (se 1 (by rfl) ⟨1583654, by rfl⟩ : syracuseStep 2111539 = 3167309) B3167309
theorem B4749425 : Blo 1875639 4749425 := bstep (se 2 (by rfl) ⟨1781034, by rfl⟩ : syracuseStep 4749425 = 3562069) B3562069
theorem B6092941 : Blo 1875639 6092941 := bstep (se 3 (by rfl) ⟨1142426, by rfl⟩ : syracuseStep 6092941 = 2284853) B2284853
theorem B9500813 : Blo 1875639 9500813 := bstep (se 3 (by rfl) ⟨1781402, by rfl⟩ : syracuseStep 9500813 = 3562805) B3562805
theorem B4749475 : Blo 1875639 4749475 := bstep (se 1 (by rfl) ⟨3562106, by rfl⟩ : syracuseStep 4749475 = 7124213) B7124213
theorem B9017507 : Blo 1875639 9017507 := bstep (se 1 (by rfl) ⟨6763130, by rfl⟩ : syracuseStep 9017507 = 13526261) B13526261
theorem B7125155 : Blo 1875639 7125155 := bstep (se 1 (by rfl) ⟨5343866, by rfl⟩ : syracuseStep 7125155 = 10687733) B10687733
theorem B6420653 : Blo 1875639 6420653 := bstep (se 3 (by rfl) ⟨1203872, by rfl⟩ : syracuseStep 6420653 = 2407745) B2407745
theorem B2111683 : Blo 1875639 2111683 := bstep (se 1 (by rfl) ⟨1583762, by rfl⟩ : syracuseStep 2111683 = 3167525) B3167525
theorem B2570449 : Blo 1875639 2570449 := bstep (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) B1927837
theorem B5142737 : Blo 1875639 5142737 := bstep (se 2 (by rfl) ⟨1928526, by rfl⟩ : syracuseStep 5142737 = 3857053) B3857053
theorem B12024035 : Blo 1875639 12024035 := bstep (se 1 (by rfl) ⟨9018026, by rfl⟩ : syracuseStep 12024035 = 18036053) B18036053
theorem B4749617 : Blo 1875639 4749617 := bstep (se 2 (by rfl) ⟨1781106, by rfl⟩ : syracuseStep 4749617 = 3562213) B3562213
theorem B6330797 : Blo 1875639 6330797 := bstep (se 3 (by rfl) ⟨1187024, by rfl⟩ : syracuseStep 6330797 = 2374049) B2374049
theorem B342563269 : Blo 1875639 342563269 := bstep (se 4 (by rfl) ⟨32115306, by rfl⟩ : syracuseStep 342563269 = 64230613) B64230613
theorem B6330851 : Blo 1875639 6330851 := bstep (se 1 (by rfl) ⟨4748138, by rfl⟩ : syracuseStep 6330851 = 9496277) B9496277
theorem B21371363 : Blo 1875639 21371363 := bstep (se 1 (by rfl) ⟨16028522, by rfl⟩ : syracuseStep 21371363 = 32057045) B32057045
theorem B3004913 : Blo 1875639 3004913 := bstep (se 2 (by rfl) ⟨1126842, by rfl⟩ : syracuseStep 3004913 = 2253685) B2253685
theorem B14637581 : Blo 1875639 14637581 := bstep (se 3 (by rfl) ⟨2744546, by rfl⟩ : syracuseStep 14637581 = 5489093) B5489093
theorem B7608845 : Blo 1875639 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B6011441 : Blo 1875639 6011441 := bstep (se 2 (by rfl) ⟨2254290, by rfl⟩ : syracuseStep 6011441 = 4508581) B4508581
theorem B2374211 : Blo 1875639 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B3005041 : Blo 1875639 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B3005105 : Blo 1875639 3005105 := bstep (se 2 (by rfl) ⟨1126914, by rfl⟩ : syracuseStep 3005105 = 2253829) B2253829
theorem B6331121 : Blo 1875639 6331121 := bstep (se 2 (by rfl) ⟨2374170, by rfl⟩ : syracuseStep 6331121 = 4748341) B4748341
theorem B10279685 : Blo 1875639 10279685 := bstep (se 4 (by rfl) ⟨963720, by rfl⟩ : syracuseStep 10279685 = 1927441) B1927441
theorem B3562289 : Blo 1875639 3562289 := bstep (se 2 (by rfl) ⟨1335858, by rfl⟩ : syracuseStep 3562289 = 2671717) B2671717
theorem B31267781 : Blo 1875639 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B10140785 : Blo 1875639 10140785 := bstep (se 2 (by rfl) ⟨3802794, by rfl⟩ : syracuseStep 10140785 = 7605589) B7605589
theorem B7126157 : Blo 1875639 7126157 := bstep (se 3 (by rfl) ⟨1336154, by rfl⟩ : syracuseStep 7126157 = 2672309) B2672309
theorem B5069969 : Blo 1875639 5069969 := bstep (se 2 (by rfl) ⟨1901238, by rfl⟩ : syracuseStep 5069969 = 3802477) B3802477
theorem B2374915 : Blo 1875639 2374915 := bstep (se 1 (by rfl) ⟨1781186, by rfl⟩ : syracuseStep 2374915 = 3562373) B3562373
theorem B6331661 : Blo 1875639 6331661 := bstep (se 3 (by rfl) ⟨1187186, by rfl⟩ : syracuseStep 6331661 = 2374373) B2374373
theorem B4750609 : Blo 1875639 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B2891027 : Blo 1875639 2891027 := bstep (se 1 (by rfl) ⟨2168270, by rfl⟩ : syracuseStep 2891027 = 4336541) B4336541
theorem B6331715 : Blo 1875639 6331715 := bstep (se 1 (by rfl) ⟨4748786, by rfl⟩ : syracuseStep 6331715 = 9497573) B9497573
theorem B2375011 : Blo 1875639 2375011 := bstep (se 1 (by rfl) ⟨1781258, by rfl⟩ : syracuseStep 2375011 = 3562517) B3562517
theorem B16244165 : Blo 1875639 16244165 := bstep (se 4 (by rfl) ⟨1522890, by rfl⟩ : syracuseStep 16244165 = 3045781) B3045781
theorem B4750883 : Blo 1875639 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B6331985 : Blo 1875639 6331985 := bstep (se 2 (by rfl) ⟨2374494, by rfl⟩ : syracuseStep 6331985 = 4748989) B4748989
theorem B18275939 : Blo 1875639 18275939 := bstep (se 1 (by rfl) ⟨13706954, by rfl⟩ : syracuseStep 18275939 = 27413909) B27413909
theorem B13016717 : Blo 1875639 13016717 := bstep (se 3 (by rfl) ⟨2440634, by rfl⟩ : syracuseStep 13016717 = 4881269) B4881269
theorem B3563185 : Blo 1875639 3563185 := bstep (se 2 (by rfl) ⟨1336194, by rfl⟩ : syracuseStep 3563185 = 2672389) B2672389
theorem B1875651 : Blo 1875639 1875651 := bstep (se 1 (by rfl) ⟨1406738, by rfl⟩ : syracuseStep 1875651 = 2813477) B2813477
theorem B1875667 : Blo 1875639 1875667 := bstep (se 1 (by rfl) ⟨1406750, by rfl⟩ : syracuseStep 1875667 = 2813501) B2813501
theorem B3006163 : Blo 1875639 3006163 := bstep (se 1 (by rfl) ⟨2254622, by rfl⟩ : syracuseStep 3006163 = 4509245) B4509245
theorem B1875683 : Blo 1875639 1875683 := bstep (se 1 (by rfl) ⟨1406762, by rfl⟩ : syracuseStep 1875683 = 2813525) B2813525
theorem B4751075 : Blo 1875639 4751075 := bstep (se 1 (by rfl) ⟨3563306, by rfl⟩ : syracuseStep 4751075 = 7126613) B7126613
theorem B6094577 : Blo 1875639 6094577 := bstep (se 2 (by rfl) ⟨2285466, by rfl⟩ : syracuseStep 6094577 = 4570933) B4570933
theorem B1875699 : Blo 1875639 1875699 := bstep (se 1 (by rfl) ⟨1406774, by rfl⟩ : syracuseStep 1875699 = 2813549) B2813549
theorem B1875715 : Blo 1875639 1875715 := bstep (se 1 (by rfl) ⟨1406786, by rfl⟩ : syracuseStep 1875715 = 2813573) B2813573
theorem B1875731 : Blo 1875639 1875731 := bstep (se 1 (by rfl) ⟨1406798, by rfl⟩ : syracuseStep 1875731 = 2813597) B2813597
theorem B1875747 : Blo 1875639 1875747 := bstep (se 1 (by rfl) ⟨1406810, by rfl⟩ : syracuseStep 1875747 = 2813621) B2813621
theorem B1875763 : Blo 1875639 1875763 := bstep (se 1 (by rfl) ⟨1406822, by rfl⟩ : syracuseStep 1875763 = 2813645) B2813645
theorem B20291381 : Blo 1875639 20291381 := bstep (se 5 (by rfl) ⟨951158, by rfl⟩ : syracuseStep 20291381 = 1902317) B1902317
theorem B1875779 : Blo 1875639 1875779 := bstep (se 1 (by rfl) ⟨1406834, by rfl⟩ : syracuseStep 1875779 = 2813669) B2813669
theorem B14253893 : Blo 1875639 14253893 := bstep (se 4 (by rfl) ⟨1336302, by rfl⟩ : syracuseStep 14253893 = 2672605) B2672605
theorem B3563345 : Blo 1875639 3563345 := bstep (se 2 (by rfl) ⟨1336254, by rfl⟩ : syracuseStep 3563345 = 2672509) B2672509
theorem B1875795 : Blo 1875639 1875795 := bstep (se 1 (by rfl) ⟨1406846, by rfl⟩ : syracuseStep 1875795 = 2813693) B2813693
theorem B2375507 : Blo 1875639 2375507 := bstep (se 1 (by rfl) ⟨1781630, by rfl⟩ : syracuseStep 2375507 = 3563261) B3563261
theorem B1875811 : Blo 1875639 1875811 := bstep (se 1 (by rfl) ⟨1406858, by rfl⟩ : syracuseStep 1875811 = 2813717) B2813717
theorem B1875827 : Blo 1875639 1875827 := bstep (se 1 (by rfl) ⟨1406870, by rfl⟩ : syracuseStep 1875827 = 2813741) B2813741
theorem B1875843 : Blo 1875639 1875843 := bstep (se 1 (by rfl) ⟨1406882, by rfl⟩ : syracuseStep 1875843 = 2813765) B2813765
theorem B1875859 : Blo 1875639 1875859 := bstep (se 1 (by rfl) ⟨1406894, by rfl⟩ : syracuseStep 1875859 = 2813789) B2813789
theorem B1875875 : Blo 1875639 1875875 := bstep (se 1 (by rfl) ⟨1406906, by rfl⟩ : syracuseStep 1875875 = 2813813) B2813813
theorem B1875891 : Blo 1875639 1875891 := bstep (se 1 (by rfl) ⟨1406918, by rfl⟩ : syracuseStep 1875891 = 2813837) B2813837
theorem B1875907 : Blo 1875639 1875907 := bstep (se 1 (by rfl) ⟨1406930, by rfl⟩ : syracuseStep 1875907 = 2813861) B2813861
theorem B1875923 : Blo 1875639 1875923 := bstep (se 1 (by rfl) ⟨1406942, by rfl⟩ : syracuseStep 1875923 = 2813885) B2813885
theorem B1875939 : Blo 1875639 1875939 := bstep (se 1 (by rfl) ⟨1406954, by rfl⟩ : syracuseStep 1875939 = 2813909) B2813909
theorem B1875955 : Blo 1875639 1875955 := bstep (se 1 (by rfl) ⟨1406966, by rfl⟩ : syracuseStep 1875955 = 2813933) B2813933
theorem B1875979 : Blo 1875639 1875979 := bstep (se 1 (by rfl) ⟨1406984, by rfl⟩ : syracuseStep 1875979 = 2813969) B2813969
theorem B1875991 : Blo 1875639 1875991 := bstep (se 1 (by rfl) ⟨1406993, by rfl⟩ : syracuseStep 1875991 = 2813987) B2813987
theorem B1876011 : Blo 1875639 1876011 := bstep (se 1 (by rfl) ⟨1407008, by rfl⟩ : syracuseStep 1876011 = 2814017) B2814017
theorem B1876023 : Blo 1875639 1876023 := bstep (se 1 (by rfl) ⟨1407017, by rfl⟩ : syracuseStep 1876023 = 2814035) B2814035
theorem B1876043 : Blo 1875639 1876043 := bstep (se 1 (by rfl) ⟨1407032, by rfl⟩ : syracuseStep 1876043 = 2814065) B2814065
theorem B1876055 : Blo 1875639 1876055 := bstep (se 1 (by rfl) ⟨1407041, by rfl⟩ : syracuseStep 1876055 = 2814083) B2814083
theorem B3006553 : Blo 1875639 3006553 := bstep (se 2 (by rfl) ⟨1127457, by rfl⟩ : syracuseStep 3006553 = 2254915) B2254915
theorem B7127129 : Blo 1875639 7127129 := bstep (se 2 (by rfl) ⟨2672673, by rfl⟩ : syracuseStep 7127129 = 5345347) B5345347
theorem B1876075 : Blo 1875639 1876075 := bstep (se 1 (by rfl) ⟨1407056, by rfl⟩ : syracuseStep 1876075 = 2814113) B2814113
theorem B1876087 : Blo 1875639 1876087 := bstep (se 1 (by rfl) ⟨1407065, by rfl⟩ : syracuseStep 1876087 = 2814131) B2814131
theorem B1876107 : Blo 1875639 1876107 := bstep (se 1 (by rfl) ⟨1407080, by rfl⟩ : syracuseStep 1876107 = 2814161) B2814161
theorem B1876119 : Blo 1875639 1876119 := bstep (se 1 (by rfl) ⟨1407089, by rfl⟩ : syracuseStep 1876119 = 2814179) B2814179
theorem B1876139 : Blo 1875639 1876139 := bstep (se 1 (by rfl) ⟨1407104, by rfl⟩ : syracuseStep 1876139 = 2814209) B2814209
theorem B1876151 : Blo 1875639 1876151 := bstep (se 1 (by rfl) ⟨1407113, by rfl⟩ : syracuseStep 1876151 = 2814227) B2814227
theorem B1876171 : Blo 1875639 1876171 := bstep (se 1 (by rfl) ⟨1407128, by rfl⟩ : syracuseStep 1876171 = 2814257) B2814257
theorem B1876183 : Blo 1875639 1876183 := bstep (se 1 (by rfl) ⟨1407137, by rfl⟩ : syracuseStep 1876183 = 2814275) B2814275
theorem B6332633 : Blo 1875639 6332633 := bstep (se 2 (by rfl) ⟨2374737, by rfl⟩ : syracuseStep 6332633 = 4749475) B4749475
theorem B1876203 : Blo 1875639 1876203 := bstep (se 1 (by rfl) ⟨1407152, by rfl⟩ : syracuseStep 1876203 = 2814305) B2814305
theorem B1876215 : Blo 1875639 1876215 := bstep (se 1 (by rfl) ⟨1407161, by rfl⟩ : syracuseStep 1876215 = 2814323) B2814323
theorem B1876235 : Blo 1875639 1876235 := bstep (se 1 (by rfl) ⟨1407176, by rfl⟩ : syracuseStep 1876235 = 2814353) B2814353
theorem B1876247 : Blo 1875639 1876247 := bstep (se 1 (by rfl) ⟨1407185, by rfl⟩ : syracuseStep 1876247 = 2814371) B2814371
theorem B1876267 : Blo 1875639 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B1876279 : Blo 1875639 1876279 := bstep (se 1 (by rfl) ⟨1407209, by rfl⟩ : syracuseStep 1876279 = 2814419) B2814419
theorem B1876299 : Blo 1875639 1876299 := bstep (se 1 (by rfl) ⟨1407224, by rfl⟩ : syracuseStep 1876299 = 2814449) B2814449
theorem B7610699 : Blo 1875639 7610699 := bstep (se 1 (by rfl) ⟨5708024, by rfl⟩ : syracuseStep 7610699 = 11416049) B11416049
theorem B1876311 : Blo 1875639 1876311 := bstep (se 1 (by rfl) ⟨1407233, by rfl⟩ : syracuseStep 1876311 = 2814467) B2814467
theorem B15212893 : Blo 1875639 15212893 := bstep (se 3 (by rfl) ⟨2852417, by rfl⟩ : syracuseStep 15212893 = 5704835) B5704835
theorem B1876331 : Blo 1875639 1876331 := bstep (se 1 (by rfl) ⟨1407248, by rfl⟩ : syracuseStep 1876331 = 2814497) B2814497
theorem B1876343 : Blo 1875639 1876343 := bstep (se 1 (by rfl) ⟨1407257, by rfl⟩ : syracuseStep 1876343 = 2814515) B2814515
theorem B1876363 : Blo 1875639 1876363 := bstep (se 1 (by rfl) ⟨1407272, by rfl⟩ : syracuseStep 1876363 = 2814545) B2814545
theorem B1876375 : Blo 1875639 1876375 := bstep (se 1 (by rfl) ⟨1407281, by rfl⟩ : syracuseStep 1876375 = 2814563) B2814563
theorem B1876395 : Blo 1875639 1876395 := bstep (se 1 (by rfl) ⟨1407296, by rfl⟩ : syracuseStep 1876395 = 2814593) B2814593
theorem B1876407 : Blo 1875639 1876407 := bstep (se 1 (by rfl) ⟨1407305, by rfl⟩ : syracuseStep 1876407 = 2814611) B2814611
theorem B2671051 : Blo 1875639 2671051 := bstep (se 1 (by rfl) ⟨2003288, by rfl⟩ : syracuseStep 2671051 = 4006577) B4006577
theorem B16024013 : Blo 1875639 16024013 := bstep (se 3 (by rfl) ⟨3004502, by rfl⟩ : syracuseStep 16024013 = 6009005) B6009005
theorem B1876427 : Blo 1875639 1876427 := bstep (se 1 (by rfl) ⟨1407320, by rfl⟩ : syracuseStep 1876427 = 2814641) B2814641
theorem B1876439 : Blo 1875639 1876439 := bstep (se 1 (by rfl) ⟨1407329, by rfl⟩ : syracuseStep 1876439 = 2814659) B2814659
theorem B1876459 : Blo 1875639 1876459 := bstep (se 1 (by rfl) ⟨1407344, by rfl⟩ : syracuseStep 1876459 = 2814689) B2814689
theorem B1876471 : Blo 1875639 1876471 := bstep (se 1 (by rfl) ⟨1407353, by rfl⟩ : syracuseStep 1876471 = 2814707) B2814707
theorem B1876491 : Blo 1875639 1876491 := bstep (se 1 (by rfl) ⟨1407368, by rfl⟩ : syracuseStep 1876491 = 2814737) B2814737
theorem B1876503 : Blo 1875639 1876503 := bstep (se 1 (by rfl) ⟨1407377, by rfl⟩ : syracuseStep 1876503 = 2814755) B2814755
theorem B1876523 : Blo 1875639 1876523 := bstep (se 1 (by rfl) ⟨1407392, by rfl⟩ : syracuseStep 1876523 = 2814785) B2814785
theorem B1876535 : Blo 1875639 1876535 := bstep (se 1 (by rfl) ⟨1407401, by rfl⟩ : syracuseStep 1876535 = 2814803) B2814803
theorem B10142273 : Blo 1875639 10142273 := bstep (se 2 (by rfl) ⟨3803352, by rfl⟩ : syracuseStep 10142273 = 7606705) B7606705
theorem B1876555 : Blo 1875639 1876555 := bstep (se 1 (by rfl) ⟨1407416, by rfl⟩ : syracuseStep 1876555 = 2814833) B2814833
theorem B1876567 : Blo 1875639 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B1876587 : Blo 1875639 1876587 := bstep (se 1 (by rfl) ⟨1407440, by rfl⟩ : syracuseStep 1876587 = 2814881) B2814881
theorem B1876599 : Blo 1875639 1876599 := bstep (se 1 (by rfl) ⟨1407449, by rfl⟩ : syracuseStep 1876599 = 2814899) B2814899
theorem B1876619 : Blo 1875639 1876619 := bstep (se 1 (by rfl) ⟨1407464, by rfl⟩ : syracuseStep 1876619 = 2814929) B2814929
theorem B1876631 : Blo 1875639 1876631 := bstep (se 1 (by rfl) ⟨1407473, by rfl⟩ : syracuseStep 1876631 = 2814947) B2814947
theorem B12026519 : Blo 1875639 12026519 := bstep (se 1 (by rfl) ⟨9019889, by rfl⟩ : syracuseStep 12026519 = 18039779) B18039779
theorem B1876651 : Blo 1875639 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B1876663 : Blo 1875639 1876663 := bstep (se 1 (by rfl) ⟨1407497, by rfl⟩ : syracuseStep 1876663 = 2814995) B2814995
theorem B1876683 : Blo 1875639 1876683 := bstep (se 1 (by rfl) ⟨1407512, by rfl⟩ : syracuseStep 1876683 = 2815025) B2815025
theorem B1876695 : Blo 1875639 1876695 := bstep (se 1 (by rfl) ⟨1407521, by rfl⟩ : syracuseStep 1876695 = 2815043) B2815043
theorem B1876715 : Blo 1875639 1876715 := bstep (se 1 (by rfl) ⟨1407536, by rfl⟩ : syracuseStep 1876715 = 2815073) B2815073
theorem B1876727 : Blo 1875639 1876727 := bstep (se 1 (by rfl) ⟨1407545, by rfl⟩ : syracuseStep 1876727 = 2815091) B2815091
theorem B1876747 : Blo 1875639 1876747 := bstep (se 1 (by rfl) ⟨1407560, by rfl⟩ : syracuseStep 1876747 = 2815121) B2815121
theorem B1876759 : Blo 1875639 1876759 := bstep (se 1 (by rfl) ⟨1407569, by rfl⟩ : syracuseStep 1876759 = 2815139) B2815139
theorem B1876779 : Blo 1875639 1876779 := bstep (se 1 (by rfl) ⟨1407584, by rfl⟩ : syracuseStep 1876779 = 2815169) B2815169
theorem B1876791 : Blo 1875639 1876791 := bstep (se 1 (by rfl) ⟨1407593, by rfl⟩ : syracuseStep 1876791 = 2815187) B2815187
theorem B4006721 : Blo 1875639 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B1876811 : Blo 1875639 1876811 := bstep (se 1 (by rfl) ⟨1407608, by rfl⟩ : syracuseStep 1876811 = 2815217) B2815217
theorem B1876823 : Blo 1875639 1876823 := bstep (se 1 (by rfl) ⟨1407617, by rfl⟩ : syracuseStep 1876823 = 2815235) B2815235
theorem B62546789 : Blo 1875639 62546789 := bstep (se 4 (by rfl) ⟨5863761, by rfl⟩ : syracuseStep 62546789 = 11727523) B11727523
theorem B1876843 : Blo 1875639 1876843 := bstep (se 1 (by rfl) ⟨1407632, by rfl⟩ : syracuseStep 1876843 = 2815265) B2815265
theorem B1876855 : Blo 1875639 1876855 := bstep (se 1 (by rfl) ⟨1407641, by rfl⟩ : syracuseStep 1876855 = 2815283) B2815283
theorem B1876875 : Blo 1875639 1876875 := bstep (se 1 (by rfl) ⟨1407656, by rfl⟩ : syracuseStep 1876875 = 2815313) B2815313
theorem B6333335 : Blo 1875639 6333335 := bstep (se 1 (by rfl) ⟨4750001, by rfl⟩ : syracuseStep 6333335 = 9500003) B9500003
theorem B1876887 : Blo 1875639 1876887 := bstep (se 1 (by rfl) ⟨1407665, by rfl⟩ : syracuseStep 1876887 = 2815331) B2815331
theorem B1876907 : Blo 1875639 1876907 := bstep (se 1 (by rfl) ⟨1407680, by rfl⟩ : syracuseStep 1876907 = 2815361) B2815361
theorem B1876919 : Blo 1875639 1876919 := bstep (se 1 (by rfl) ⟨1407689, by rfl⟩ : syracuseStep 1876919 = 2815379) B2815379
theorem B1876939 : Blo 1875639 1876939 := bstep (se 1 (by rfl) ⟨1407704, by rfl⟩ : syracuseStep 1876939 = 2815409) B2815409
theorem B1876951 : Blo 1875639 1876951 := bstep (se 1 (by rfl) ⟨1407713, by rfl⟩ : syracuseStep 1876951 = 2815427) B2815427
theorem B1876971 : Blo 1875639 1876971 := bstep (se 1 (by rfl) ⟨1407728, by rfl⟩ : syracuseStep 1876971 = 2815457) B2815457
theorem B1876983 : Blo 1875639 1876983 := bstep (se 1 (by rfl) ⟨1407737, by rfl⟩ : syracuseStep 1876983 = 2815475) B2815475
theorem B1877003 : Blo 1875639 1877003 := bstep (se 1 (by rfl) ⟨1407752, by rfl⟩ : syracuseStep 1877003 = 2815505) B2815505
theorem B1877015 : Blo 1875639 1877015 := bstep (se 1 (by rfl) ⟨1407761, by rfl⟩ : syracuseStep 1877015 = 2815523) B2815523
theorem B1877035 : Blo 1875639 1877035 := bstep (se 1 (by rfl) ⟨1407776, by rfl⟩ : syracuseStep 1877035 = 2815553) B2815553
theorem B1877047 : Blo 1875639 1877047 := bstep (se 1 (by rfl) ⟨1407785, by rfl⟩ : syracuseStep 1877047 = 2815571) B2815571
theorem B59352139 : Blo 1875639 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B1877067 : Blo 1875639 1877067 := bstep (se 1 (by rfl) ⟨1407800, by rfl⟩ : syracuseStep 1877067 = 2815601) B2815601
theorem B1877079 : Blo 1875639 1877079 := bstep (se 1 (by rfl) ⟨1407809, by rfl⟩ : syracuseStep 1877079 = 2815619) B2815619
theorem B12026981 : Blo 1875639 12026981 := bstep (se 4 (by rfl) ⟨1127529, by rfl⟩ : syracuseStep 12026981 = 2255059) B2255059
theorem B1877099 : Blo 1875639 1877099 := bstep (se 1 (by rfl) ⟨1407824, by rfl⟩ : syracuseStep 1877099 = 2815649) B2815649
theorem B1877111 : Blo 1875639 1877111 := bstep (se 1 (by rfl) ⟨1407833, by rfl⟩ : syracuseStep 1877111 = 2815667) B2815667
theorem B1877131 : Blo 1875639 1877131 := bstep (se 1 (by rfl) ⟨1407848, by rfl⟩ : syracuseStep 1877131 = 2815697) B2815697
theorem B4007063 : Blo 1875639 4007063 := bstep (se 1 (by rfl) ⟨3005297, by rfl⟩ : syracuseStep 4007063 = 6010595) B6010595
theorem B14247089 : Blo 1875639 14247089 := bstep (se 2 (by rfl) ⟨5342658, by rfl⟩ : syracuseStep 14247089 = 10685317) B10685317
theorem B4220225 : Blo 1875639 4220225 := bstep (se 2 (by rfl) ⟨1582584, by rfl⟩ : syracuseStep 4220225 = 3165169) B3165169
theorem B5342557 : Blo 1875639 5342557 := bstep (se 3 (by rfl) ⟨1001729, by rfl⟩ : syracuseStep 5342557 = 2003459) B2003459
theorem B6333875 : Blo 1875639 6333875 := bstep (se 1 (by rfl) ⟨4750406, by rfl⟩ : syracuseStep 6333875 = 9500813) B9500813
theorem B4220441 : Blo 1875639 4220441 := bstep (se 2 (by rfl) ⟨1582665, by rfl⟩ : syracuseStep 4220441 = 3165331) B3165331
theorem B4220531 : Blo 1875639 4220531 := bstep (se 1 (by rfl) ⟨3165398, by rfl⟩ : syracuseStep 4220531 = 6330797) B6330797
theorem B4220567 : Blo 1875639 4220567 := bstep (se 1 (by rfl) ⟨3165425, by rfl⟩ : syracuseStep 4220567 = 6330851) B6330851
theorem B14247575 : Blo 1875639 14247575 := bstep (se 1 (by rfl) ⟨10685681, by rfl⟩ : syracuseStep 14247575 = 21371363) B21371363
theorem B2672281 : Blo 1875639 2672281 := bstep (se 2 (by rfl) ⟨1002105, by rfl⟩ : syracuseStep 2672281 = 2004211) B2004211
theorem B9758387 : Blo 1875639 9758387 := bstep (se 1 (by rfl) ⟨7318790, by rfl⟩ : syracuseStep 9758387 = 14637581) B14637581
theorem B5072563 : Blo 1875639 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B6334145 : Blo 1875639 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B4007627 : Blo 1875639 4007627 := bstep (se 1 (by rfl) ⟨3005720, by rfl⟩ : syracuseStep 4007627 = 6011441) B6011441
theorem B8013613 : Blo 1875639 8013613 := bstep (se 3 (by rfl) ⟨1502552, by rfl⟩ : syracuseStep 8013613 = 3005105) B3005105
theorem B4220747 : Blo 1875639 4220747 := bstep (se 1 (by rfl) ⟨3165560, by rfl⟩ : syracuseStep 4220747 = 6331121) B6331121
theorem B8030045 : Blo 1875639 8030045 := bstep (se 3 (by rfl) ⟨1505633, by rfl⟩ : syracuseStep 8030045 = 3011267) B3011267
theorem B37070693 : Blo 1875639 37070693 := bstep (se 4 (by rfl) ⟨3475377, by rfl⟩ : syracuseStep 37070693 = 6950755) B6950755
theorem B4220801 : Blo 1875639 4220801 := bstep (se 2 (by rfl) ⟨1582800, by rfl⟩ : syracuseStep 4220801 = 3165601) B3165601
theorem B300394565 : Blo 1875639 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B6760523 : Blo 1875639 6760523 := bstep (se 1 (by rfl) ⟨5070392, by rfl⟩ : syracuseStep 6760523 = 10140785) B10140785
theorem B4221017 : Blo 1875639 4221017 := bstep (se 2 (by rfl) ⟨1582881, by rfl⟩ : syracuseStep 4221017 = 3165763) B3165763
theorem B25036931 : Blo 1875639 25036931 := bstep (se 1 (by rfl) ⟨18777698, by rfl⟩ : syracuseStep 25036931 = 37555397) B37555397
theorem B4221107 : Blo 1875639 4221107 := bstep (se 1 (by rfl) ⟨3165830, by rfl⟩ : syracuseStep 4221107 = 6331661) B6331661
theorem B1927351 : Blo 1875639 1927351 := bstep (se 1 (by rfl) ⟨1445513, by rfl⟩ : syracuseStep 1927351 = 2891027) B2891027
theorem B21366989 : Blo 1875639 21366989 := bstep (se 3 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 21366989 = 8012621) B8012621
theorem B4221143 : Blo 1875639 4221143 := bstep (se 1 (by rfl) ⟨3165857, by rfl⟩ : syracuseStep 4221143 = 6331715) B6331715
theorem B6334685 : Blo 1875639 6334685 := bstep (se 3 (by rfl) ⟨1187753, by rfl⟩ : syracuseStep 6334685 = 2375507) B2375507
theorem B4008217 : Blo 1875639 4008217 := bstep (se 2 (by rfl) ⟨1503081, by rfl⟩ : syracuseStep 4008217 = 3006163) B3006163
theorem B9496925 : Blo 1875639 9496925 := bstep (se 3 (by rfl) ⟨1780673, by rfl⟩ : syracuseStep 9496925 = 3561347) B3561347
theorem B4221323 : Blo 1875639 4221323 := bstep (se 1 (by rfl) ⟨3165992, by rfl⟩ : syracuseStep 4221323 = 6331985) B6331985
theorem B12183959 : Blo 1875639 12183959 := bstep (se 1 (by rfl) ⟨9137969, by rfl⟩ : syracuseStep 12183959 = 18275939) B18275939
theorem B8677811 : Blo 1875639 8677811 := bstep (se 1 (by rfl) ⟨6508358, by rfl⟩ : syracuseStep 8677811 = 13016717) B13016717
theorem B4221377 : Blo 1875639 4221377 := bstep (se 2 (by rfl) ⟨1583016, by rfl⟩ : syracuseStep 4221377 = 3166033) B3166033
theorem B13527587 : Blo 1875639 13527587 := bstep (se 1 (by rfl) ⟨10145690, by rfl⟩ : syracuseStep 13527587 = 20291381) B20291381
theorem B5343833 : Blo 1875639 5343833 := bstep (se 2 (by rfl) ⟨2003937, by rfl⟩ : syracuseStep 5343833 = 4007875) B4007875
theorem B10144349 : Blo 1875639 10144349 := bstep (se 3 (by rfl) ⟨1902065, by rfl⟩ : syracuseStep 10144349 = 3804131) B3804131
theorem B4221593 : Blo 1875639 4221593 := bstep (se 2 (by rfl) ⟨1583097, by rfl⟩ : syracuseStep 4221593 = 3166195) B3166195
theorem B5073601 : Blo 1875639 5073601 := bstep (se 2 (by rfl) ⟨1902600, by rfl⟩ : syracuseStep 5073601 = 3805201) B3805201
theorem B13527757 : Blo 1875639 13527757 := bstep (se 3 (by rfl) ⟨2536454, by rfl⟩ : syracuseStep 13527757 = 5072909) B5072909
theorem B4221683 : Blo 1875639 4221683 := bstep (se 1 (by rfl) ⟨3166262, by rfl⟩ : syracuseStep 4221683 = 6332525) B6332525
theorem B4221719 : Blo 1875639 4221719 := bstep (se 1 (by rfl) ⟨3166289, by rfl⟩ : syracuseStep 4221719 = 6332579) B6332579
theorem B3803969 : Blo 1875639 3803969 := bstep (se 2 (by rfl) ⟨1426488, by rfl⟩ : syracuseStep 3803969 = 2852977) B2852977
theorem B7121753 : Blo 1875639 7121753 := bstep (se 2 (by rfl) ⟨2670657, by rfl⟩ : syracuseStep 7121753 = 5341315) B5341315
theorem B3427265 : Blo 1875639 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B4221899 : Blo 1875639 4221899 := bstep (se 1 (by rfl) ⟨3166424, by rfl⟩ : syracuseStep 4221899 = 6332849) B6332849
theorem B4221953 : Blo 1875639 4221953 := bstep (se 2 (by rfl) ⟨1583232, by rfl⟩ : syracuseStep 4221953 = 3166465) B3166465
theorem B7121965 : Blo 1875639 7121965 := bstep (se 3 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 7121965 = 2670737) B2670737
theorem B10685591 : Blo 1875639 10685591 := bstep (se 1 (by rfl) ⟨8014193, by rfl⟩ : syracuseStep 10685591 = 16028387) B16028387
theorem B4222169 : Blo 1875639 4222169 := bstep (se 2 (by rfl) ⟨1583313, by rfl⟩ : syracuseStep 4222169 = 3166627) B3166627
theorem B4222259 : Blo 1875639 4222259 := bstep (se 1 (by rfl) ⟨3166694, by rfl⟩ : syracuseStep 4222259 = 6333389) B6333389
theorem B3165527 : Blo 1875639 3165527 := bstep (se 1 (by rfl) ⟨2374145, by rfl⟩ : syracuseStep 3165527 = 4748291) B4748291
theorem B4222295 : Blo 1875639 4222295 := bstep (se 1 (by rfl) ⟨3166721, by rfl⟩ : syracuseStep 4222295 = 6333443) B6333443
theorem B7122269 : Blo 1875639 7122269 := bstep (se 3 (by rfl) ⟨1335425, by rfl⟩ : syracuseStep 7122269 = 2670851) B2670851
theorem B3165655 : Blo 1875639 3165655 := bstep (se 1 (by rfl) ⟨2374241, by rfl⟩ : syracuseStep 3165655 = 4748483) B4748483
theorem B15216133 : Blo 1875639 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B4222475 : Blo 1875639 4222475 := bstep (se 1 (by rfl) ⟨3166856, by rfl⟩ : syracuseStep 4222475 = 6333713) B6333713
theorem B2813465 : Blo 1875639 2813465 := bstep (se 2 (by rfl) ⟨1055049, by rfl⟩ : syracuseStep 2813465 = 2110099) B2110099
theorem B4222529 : Blo 1875639 4222529 := bstep (se 2 (by rfl) ⟨1583448, by rfl⟩ : syracuseStep 4222529 = 3166897) B3166897
theorem B2813579 : Blo 1875639 2813579 := bstep (se 1 (by rfl) ⟨2110184, by rfl⟩ : syracuseStep 2813579 = 4220369) B4220369
theorem B2813591 : Blo 1875639 2813591 := bstep (se 1 (by rfl) ⟨2110193, by rfl⟩ : syracuseStep 2813591 = 4220387) B4220387
theorem B2813657 : Blo 1875639 2813657 := bstep (se 2 (by rfl) ⟨1055121, by rfl⟩ : syracuseStep 2813657 = 2110243) B2110243
theorem B4222745 : Blo 1875639 4222745 := bstep (se 2 (by rfl) ⟨1583529, by rfl⟩ : syracuseStep 4222745 = 3167059) B3167059
theorem B2813771 : Blo 1875639 2813771 := bstep (se 1 (by rfl) ⟨2110328, by rfl⟩ : syracuseStep 2813771 = 4220657) B4220657
theorem B2813783 : Blo 1875639 2813783 := bstep (se 1 (by rfl) ⟨2110337, by rfl⟩ : syracuseStep 2813783 = 4220675) B4220675
theorem B4222835 : Blo 1875639 4222835 := bstep (se 1 (by rfl) ⟨3167126, by rfl⟩ : syracuseStep 4222835 = 6334253) B6334253
theorem B4222871 : Blo 1875639 4222871 := bstep (se 1 (by rfl) ⟨3167153, by rfl⟩ : syracuseStep 4222871 = 6334307) B6334307
theorem B2813849 : Blo 1875639 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B2813963 : Blo 1875639 2813963 := bstep (se 1 (by rfl) ⟨2110472, by rfl⟩ : syracuseStep 2813963 = 4220945) B4220945
theorem B2813975 : Blo 1875639 2813975 := bstep (se 1 (by rfl) ⟨2110481, by rfl⟩ : syracuseStep 2813975 = 4220963) B4220963
theorem B3166283 : Blo 1875639 3166283 := bstep (se 1 (by rfl) ⟨2374712, by rfl⟩ : syracuseStep 3166283 = 4749425) B4749425
theorem B4223051 : Blo 1875639 4223051 := bstep (se 1 (by rfl) ⟨3167288, by rfl⟩ : syracuseStep 4223051 = 6334577) B6334577
theorem B2814041 : Blo 1875639 2814041 := bstep (se 2 (by rfl) ⟨1055265, by rfl⟩ : syracuseStep 2814041 = 2110531) B2110531
theorem B4280435 : Blo 1875639 4280435 := bstep (se 1 (by rfl) ⟨3210326, by rfl⟩ : syracuseStep 4280435 = 6420653) B6420653
theorem B4223105 : Blo 1875639 4223105 := bstep (se 2 (by rfl) ⟨1583664, by rfl⟩ : syracuseStep 4223105 = 3167329) B3167329
theorem B3428491 : Blo 1875639 3428491 := bstep (se 1 (by rfl) ⟨2571368, by rfl⟩ : syracuseStep 3428491 = 5142737) B5142737
theorem B8016023 : Blo 1875639 8016023 := bstep (se 1 (by rfl) ⟨6012017, by rfl⟩ : syracuseStep 8016023 = 12024035) B12024035
theorem B2814155 : Blo 1875639 2814155 := bstep (se 1 (by rfl) ⟨2110616, by rfl⟩ : syracuseStep 2814155 = 4221233) B4221233
theorem B3166411 : Blo 1875639 3166411 := bstep (se 1 (by rfl) ⟨2374808, by rfl⟩ : syracuseStep 3166411 = 4749617) B4749617
theorem B2814167 : Blo 1875639 2814167 := bstep (se 1 (by rfl) ⟨2110625, by rfl⟩ : syracuseStep 2814167 = 4221251) B4221251
theorem B2814233 : Blo 1875639 2814233 := bstep (se 2 (by rfl) ⟨1055337, by rfl⟩ : syracuseStep 2814233 = 2110675) B2110675
theorem B2003275 : Blo 1875639 2003275 := bstep (se 1 (by rfl) ⟨1502456, by rfl⟩ : syracuseStep 2003275 = 3004913) B3004913
theorem B3166553 : Blo 1875639 3166553 := bstep (se 2 (by rfl) ⟨1187457, by rfl⟩ : syracuseStep 3166553 = 2374915) B2374915
theorem B4223321 : Blo 1875639 4223321 := bstep (se 2 (by rfl) ⟨1583745, by rfl⟩ : syracuseStep 4223321 = 3167491) B3167491
theorem B2814347 : Blo 1875639 2814347 := bstep (se 1 (by rfl) ⟨2110760, by rfl⟩ : syracuseStep 2814347 = 4221521) B4221521
theorem B2814359 : Blo 1875639 2814359 := bstep (se 1 (by rfl) ⟨2110769, by rfl⟩ : syracuseStep 2814359 = 4221539) B4221539
theorem B9499031 : Blo 1875639 9499031 := bstep (se 1 (by rfl) ⟨7124273, by rfl⟩ : syracuseStep 9499031 = 14248547) B14248547
theorem B4338073 : Blo 1875639 4338073 := bstep (se 2 (by rfl) ⟨1626777, by rfl⟩ : syracuseStep 4338073 = 3253555) B3253555
theorem B4223411 : Blo 1875639 4223411 := bstep (se 1 (by rfl) ⟨3167558, by rfl⟩ : syracuseStep 4223411 = 6335117) B6335117
theorem B4223447 : Blo 1875639 4223447 := bstep (se 1 (by rfl) ⟨3167585, by rfl⟩ : syracuseStep 4223447 = 6335171) B6335171
theorem B2814425 : Blo 1875639 2814425 := bstep (se 2 (by rfl) ⟨1055409, by rfl⟩ : syracuseStep 2814425 = 2110819) B2110819
theorem B3166681 : Blo 1875639 3166681 := bstep (se 2 (by rfl) ⟨1187505, by rfl⟩ : syracuseStep 3166681 = 2375011) B2375011
theorem B6853123 : Blo 1875639 6853123 := bstep (se 1 (by rfl) ⟨5139842, by rfl⟩ : syracuseStep 6853123 = 10279685) B10279685
theorem B2814539 : Blo 1875639 2814539 := bstep (se 1 (by rfl) ⟨2110904, by rfl⟩ : syracuseStep 2814539 = 4221809) B4221809
theorem B2814551 : Blo 1875639 2814551 := bstep (se 1 (by rfl) ⟨2110913, by rfl⟩ : syracuseStep 2814551 = 4221827) B4221827
theorem B20845187 : Blo 1875639 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B2814617 : Blo 1875639 2814617 := bstep (se 2 (by rfl) ⟨1055481, by rfl⟩ : syracuseStep 2814617 = 2110963) B2110963
theorem B2110135 : Blo 1875639 2110135 := bstep (se 1 (by rfl) ⟨1582601, by rfl⟩ : syracuseStep 2110135 = 3165203) B3165203
theorem B34231045 : Blo 1875639 34231045 := bstep (se 4 (by rfl) ⟨3209160, by rfl⟩ : syracuseStep 34231045 = 6418321) B6418321
theorem B3379979 : Blo 1875639 3379979 := bstep (se 1 (by rfl) ⟨2534984, by rfl⟩ : syracuseStep 3379979 = 5069969) B5069969
theorem B2814731 : Blo 1875639 2814731 := bstep (se 1 (by rfl) ⟨2111048, by rfl⟩ : syracuseStep 2814731 = 4222097) B4222097
theorem B2814743 : Blo 1875639 2814743 := bstep (se 1 (by rfl) ⟨2111057, by rfl⟩ : syracuseStep 2814743 = 4222115) B4222115
theorem B2814809 : Blo 1875639 2814809 := bstep (se 2 (by rfl) ⟨1055553, by rfl⟩ : syracuseStep 2814809 = 2111107) B2111107
theorem B2110315 : Blo 1875639 2110315 := bstep (se 1 (by rfl) ⟨1582736, by rfl⟩ : syracuseStep 2110315 = 3165473) B3165473
theorem B2814923 : Blo 1875639 2814923 := bstep (se 1 (by rfl) ⟨2111192, by rfl⟩ : syracuseStep 2814923 = 4222385) B4222385
theorem B2110423 : Blo 1875639 2110423 := bstep (se 1 (by rfl) ⟨1582817, by rfl⟩ : syracuseStep 2110423 = 3165635) B3165635
theorem B2814935 : Blo 1875639 2814935 := bstep (se 1 (by rfl) ⟨2111201, by rfl⟩ : syracuseStep 2814935 = 4222403) B4222403
theorem B3167255 : Blo 1875639 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B2815001 : Blo 1875639 2815001 := bstep (se 2 (by rfl) ⟨1055625, by rfl⟩ : syracuseStep 2815001 = 2111251) B2111251
theorem B12022829 : Blo 1875639 12022829 := bstep (se 3 (by rfl) ⟨2254280, by rfl⟩ : syracuseStep 12022829 = 4508561) B4508561
theorem B6853697 : Blo 1875639 6853697 := bstep (se 2 (by rfl) ⟨2570136, by rfl⟩ : syracuseStep 6853697 = 5140273) B5140273
theorem B16028765 : Blo 1875639 16028765 := bstep (se 3 (by rfl) ⟨3005393, by rfl⟩ : syracuseStep 16028765 = 6010787) B6010787
theorem B2110603 : Blo 1875639 2110603 := bstep (se 1 (by rfl) ⟨1582952, by rfl⟩ : syracuseStep 2110603 = 3165905) B3165905
theorem B2815115 : Blo 1875639 2815115 := bstep (se 1 (by rfl) ⟨2111336, by rfl⟩ : syracuseStep 2815115 = 4222673) B4222673
theorem B2815127 : Blo 1875639 2815127 := bstep (se 1 (by rfl) ⟨2111345, by rfl⟩ : syracuseStep 2815127 = 4222691) B4222691
theorem B3167383 : Blo 1875639 3167383 := bstep (se 1 (by rfl) ⟨2375537, by rfl⟩ : syracuseStep 3167383 = 4751075) B4751075
theorem B7713971 : Blo 1875639 7713971 := bstep (se 1 (by rfl) ⟨5785478, by rfl⟩ : syracuseStep 7713971 = 11570957) B11570957
theorem B2815193 : Blo 1875639 2815193 := bstep (se 2 (by rfl) ⟨1055697, by rfl⟩ : syracuseStep 2815193 = 2111395) B2111395
theorem B2110711 : Blo 1875639 2110711 := bstep (se 1 (by rfl) ⟨1583033, by rfl⟩ : syracuseStep 2110711 = 3166067) B3166067
theorem B2815307 : Blo 1875639 2815307 := bstep (se 1 (by rfl) ⟨2111480, by rfl⟩ : syracuseStep 2815307 = 4222961) B4222961
theorem B2815319 : Blo 1875639 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B2815385 : Blo 1875639 2815385 := bstep (se 2 (by rfl) ⟨1055769, by rfl⟩ : syracuseStep 2815385 = 2111539) B2111539
theorem B2110891 : Blo 1875639 2110891 := bstep (se 1 (by rfl) ⟨1583168, by rfl⟩ : syracuseStep 2110891 = 3166337) B3166337
theorem B2815499 : Blo 1875639 2815499 := bstep (se 1 (by rfl) ⟨2111624, by rfl⟩ : syracuseStep 2815499 = 4223249) B4223249
theorem B8123921 : Blo 1875639 8123921 := bstep (se 2 (by rfl) ⟨3046470, by rfl⟩ : syracuseStep 8123921 = 6092941) B6092941
theorem B2110999 : Blo 1875639 2110999 := bstep (se 1 (by rfl) ⟨1583249, by rfl⟩ : syracuseStep 2110999 = 3166499) B3166499
theorem B2815511 : Blo 1875639 2815511 := bstep (se 1 (by rfl) ⟨2111633, by rfl⟩ : syracuseStep 2815511 = 4223267) B4223267
theorem B2815577 : Blo 1875639 2815577 := bstep (se 2 (by rfl) ⟨1055841, by rfl⟩ : syracuseStep 2815577 = 2111683) B2111683
theorem B21378653 : Blo 1875639 21378653 := bstep (se 3 (by rfl) ⟨4008497, by rfl⟩ : syracuseStep 21378653 = 8016995) B8016995
theorem B2111179 : Blo 1875639 2111179 := bstep (se 1 (by rfl) ⟨1583384, by rfl⟩ : syracuseStep 2111179 = 3166769) B3166769
theorem B2815691 : Blo 1875639 2815691 := bstep (se 1 (by rfl) ⟨2111768, by rfl⟩ : syracuseStep 2815691 = 4223537) B4223537
theorem B2815703 : Blo 1875639 2815703 := bstep (se 1 (by rfl) ⟨2111777, by rfl⟩ : syracuseStep 2815703 = 4223555) B4223555
theorem B3561241 : Blo 1875639 3561241 := bstep (se 2 (by rfl) ⟨1335465, by rfl⟩ : syracuseStep 3561241 = 2670931) B2670931
theorem B2111287 : Blo 1875639 2111287 := bstep (se 1 (by rfl) ⟨1583465, by rfl⟩ : syracuseStep 2111287 = 3166931) B3166931
theorem B4749131 : Blo 1875639 4749131 := bstep (se 1 (by rfl) ⟨3561848, by rfl⟩ : syracuseStep 4749131 = 7123697) B7123697
theorem B34223971 : Blo 1875639 34223971 := bstep (se 1 (by rfl) ⟨25667978, by rfl⟩ : syracuseStep 34223971 = 51335957) B51335957
theorem B7124867 : Blo 1875639 7124867 := bstep (se 1 (by rfl) ⟨5343650, by rfl⟩ : syracuseStep 7124867 = 10687301) B10687301
theorem B7124881 : Blo 1875639 7124881 := bstep (se 2 (by rfl) ⟨2671830, by rfl⟩ : syracuseStep 7124881 = 5343661) B5343661
theorem B456751025 : Blo 1875639 456751025 := bstep (se 2 (by rfl) ⟨171281634, by rfl⟩ : syracuseStep 456751025 = 342563269) B342563269
theorem B7714763 : Blo 1875639 7714763 := bstep (se 1 (by rfl) ⟨5786072, by rfl⟩ : syracuseStep 7714763 = 11572145) B11572145
theorem B2111467 : Blo 1875639 2111467 := bstep (se 1 (by rfl) ⟨1583600, by rfl⟩ : syracuseStep 2111467 = 3167201) B3167201
theorem B8017937 : Blo 1875639 8017937 := bstep (se 2 (by rfl) ⟨3006726, by rfl⟩ : syracuseStep 8017937 = 6013453) B6013453
theorem B6330419 : Blo 1875639 6330419 := bstep (se 1 (by rfl) ⟨4747814, by rfl⟩ : syracuseStep 6330419 = 9495629) B9495629
theorem B2111575 : Blo 1875639 2111575 := bstep (se 1 (by rfl) ⟨1583681, by rfl⟩ : syracuseStep 2111575 = 3167363) B3167363
theorem B7125185 : Blo 1875639 7125185 := bstep (se 2 (by rfl) ⟨2671944, by rfl⟩ : syracuseStep 7125185 = 5343889) B5343889
theorem B3004631 : Blo 1875639 3004631 := bstep (se 1 (by rfl) ⟨2253473, by rfl⟩ : syracuseStep 3004631 = 4506947) B4506947
theorem B2111755 : Blo 1875639 2111755 := bstep (se 1 (by rfl) ⟨1583816, by rfl⟩ : syracuseStep 2111755 = 3167633) B3167633
theorem B6330689 : Blo 1875639 6330689 := bstep (se 2 (by rfl) ⟨2374008, by rfl⟩ : syracuseStep 6330689 = 4748017) B4748017
theorem B3561803 : Blo 1875639 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B2374039 : Blo 1875639 2374039 := bstep (se 1 (by rfl) ⟨1780529, by rfl⟩ : syracuseStep 2374039 = 3561059) B3561059
theorem B3561985 : Blo 1875639 3561985 := bstep (se 2 (by rfl) ⟨1335744, by rfl⟩ : syracuseStep 3561985 = 2671489) B2671489
theorem B43317773 : Blo 1875639 43317773 := bstep (se 3 (by rfl) ⟨8122082, by rfl⟩ : syracuseStep 43317773 = 16244165) B16244165
theorem B7608977 : Blo 1875639 7608977 := bstep (se 2 (by rfl) ⟨2853366, by rfl⟩ : syracuseStep 7608977 = 5706733) B5706733
theorem B3005143 : Blo 1875639 3005143 := bstep (se 1 (by rfl) ⟨2253857, by rfl⟩ : syracuseStep 3005143 = 4507715) B4507715
theorem B10828505 : Blo 1875639 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B3611353 : Blo 1875639 3611353 := bstep (se 2 (by rfl) ⟨1354257, by rfl⟩ : syracuseStep 3611353 = 2708515) B2708515
theorem B6011671 : Blo 1875639 6011671 := bstep (se 1 (by rfl) ⟨4508753, by rfl⟩ : syracuseStep 6011671 = 9017507) B9017507
theorem B4750103 : Blo 1875639 4750103 := bstep (se 1 (by rfl) ⟨3562577, by rfl⟩ : syracuseStep 4750103 = 7125155) B7125155
theorem B6331229 : Blo 1875639 6331229 := bstep (se 3 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 6331229 = 2374211) B2374211
theorem B7125853 : Blo 1875639 7125853 := bstep (se 3 (by rfl) ⟨1336097, by rfl⟩ : syracuseStep 7125853 = 2672195) B2672195
theorem B13524043 : Blo 1875639 13524043 := bstep (se 1 (by rfl) ⟨10143032, by rfl⟩ : syracuseStep 13524043 = 20286065) B20286065
theorem B3005515 : Blo 1875639 3005515 := bstep (se 1 (by rfl) ⟨2254136, by rfl⟩ : syracuseStep 3005515 = 4508273) B4508273
theorem B2374859 : Blo 1875639 2374859 := bstep (se 1 (by rfl) ⟨1781144, by rfl⟩ : syracuseStep 2374859 = 3562289) B3562289
theorem B3562699 : Blo 1875639 3562699 := bstep (se 1 (by rfl) ⟨2672024, by rfl⟩ : syracuseStep 3562699 = 5344049) B5344049
theorem B9018641 : Blo 1875639 9018641 := bstep (se 2 (by rfl) ⟨3381990, by rfl⟩ : syracuseStep 9018641 = 6763981) B6763981
theorem B3562775 : Blo 1875639 3562775 := bstep (se 1 (by rfl) ⟨2672081, by rfl⟩ : syracuseStep 3562775 = 5344163) B5344163
theorem B4750771 : Blo 1875639 4750771 := bstep (se 1 (by rfl) ⟨3563078, by rfl⟩ : syracuseStep 4750771 = 7126157) B7126157
theorem B4750913 : Blo 1875639 4750913 := bstep (se 2 (by rfl) ⟨1781592, by rfl⟩ : syracuseStep 4750913 = 3563185) B3563185
theorem B1875639 : Blo 1875639 1875639 := bstep (se 1 (by rfl) ⟨1406729, by rfl⟩ : syracuseStep 1875639 = 2813459) B2813459
theorem B1875659 : Blo 1875639 1875659 := bstep (se 1 (by rfl) ⟨1406744, by rfl⟩ : syracuseStep 1875659 = 2813489) B2813489
theorem B1875671 : Blo 1875639 1875671 := bstep (se 1 (by rfl) ⟨1406753, by rfl⟩ : syracuseStep 1875671 = 2813507) B2813507
theorem B1875691 : Blo 1875639 1875691 := bstep (se 1 (by rfl) ⟨1406768, by rfl⟩ : syracuseStep 1875691 = 2813537) B2813537
theorem B1875703 : Blo 1875639 1875703 := bstep (se 1 (by rfl) ⟨1406777, by rfl⟩ : syracuseStep 1875703 = 2813555) B2813555
theorem B1875723 : Blo 1875639 1875723 := bstep (se 1 (by rfl) ⟨1406792, by rfl⟩ : syracuseStep 1875723 = 2813585) B2813585
theorem B1875735 : Blo 1875639 1875735 := bstep (se 1 (by rfl) ⟨1406801, by rfl⟩ : syracuseStep 1875735 = 2813603) B2813603
theorem B1875755 : Blo 1875639 1875755 := bstep (se 1 (by rfl) ⟨1406816, by rfl⟩ : syracuseStep 1875755 = 2813633) B2813633
theorem B1875767 : Blo 1875639 1875767 := bstep (se 1 (by rfl) ⟨1406825, by rfl⟩ : syracuseStep 1875767 = 2813651) B2813651
theorem B1875787 : Blo 1875639 1875787 := bstep (se 1 (by rfl) ⟨1406840, by rfl⟩ : syracuseStep 1875787 = 2813681) B2813681
theorem B4063051 : Blo 1875639 4063051 := bstep (se 1 (by rfl) ⟨3047288, by rfl⟩ : syracuseStep 4063051 = 6094577) B6094577
theorem B1875799 : Blo 1875639 1875799 := bstep (se 1 (by rfl) ⟨1406849, by rfl⟩ : syracuseStep 1875799 = 2813699) B2813699
theorem B1875819 : Blo 1875639 1875819 := bstep (se 1 (by rfl) ⟨1406864, by rfl⟩ : syracuseStep 1875819 = 2813729) B2813729
theorem B1875831 : Blo 1875639 1875831 := bstep (se 1 (by rfl) ⟨1406873, by rfl⟩ : syracuseStep 1875831 = 2813747) B2813747
theorem B9502595 : Blo 1875639 9502595 := bstep (se 1 (by rfl) ⟨7126946, by rfl⟩ : syracuseStep 9502595 = 14253893) B14253893
theorem B1875851 : Blo 1875639 1875851 := bstep (se 1 (by rfl) ⟨1406888, by rfl⟩ : syracuseStep 1875851 = 2813777) B2813777
theorem B2375563 : Blo 1875639 2375563 := bstep (se 1 (by rfl) ⟨1781672, by rfl⟩ : syracuseStep 2375563 = 3563345) B3563345
theorem B1875863 : Blo 1875639 1875863 := bstep (se 1 (by rfl) ⟨1406897, by rfl⟩ : syracuseStep 1875863 = 2813795) B2813795
theorem B1875883 : Blo 1875639 1875883 := bstep (se 1 (by rfl) ⟨1406912, by rfl⟩ : syracuseStep 1875883 = 2813825) B2813825
theorem B3563443 : Blo 1875639 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B1875895 : Blo 1875639 1875895 := bstep (se 1 (by rfl) ⟨1406921, by rfl⟩ : syracuseStep 1875895 = 2813843) B2813843
theorem B1875915 : Blo 1875639 1875915 := bstep (se 1 (by rfl) ⟨1406936, by rfl⟩ : syracuseStep 1875915 = 2813873) B2813873
theorem B6332363 : Blo 1875639 6332363 := bstep (se 1 (by rfl) ⟨4749272, by rfl⟩ : syracuseStep 6332363 = 9498545) B9498545
theorem B1875927 : Blo 1875639 1875927 := bstep (se 1 (by rfl) ⟨1406945, by rfl⟩ : syracuseStep 1875927 = 2813891) B2813891
theorem B3006425 : Blo 1875639 3006425 := bstep (se 2 (by rfl) ⟨1127409, by rfl⟩ : syracuseStep 3006425 = 2254819) B2254819
theorem B1875947 : Blo 1875639 1875947 := bstep (se 1 (by rfl) ⟨1406960, by rfl⟩ : syracuseStep 1875947 = 2813921) B2813921
theorem B1875959 : Blo 1875639 1875959 := bstep (se 1 (by rfl) ⟨1406969, by rfl⟩ : syracuseStep 1875959 = 2813939) B2813939
theorem B1875975 : Blo 1875639 1875975 := bstep (se 1 (by rfl) ⟨1406981, by rfl⟩ : syracuseStep 1875975 = 2813963) B2813963
theorem B1875983 : Blo 1875639 1875983 := bstep (se 1 (by rfl) ⟨1406987, by rfl⟩ : syracuseStep 1875983 = 2813975) B2813975
theorem B1876027 : Blo 1875639 1876027 := bstep (se 1 (by rfl) ⟨1407020, by rfl⟩ : syracuseStep 1876027 = 2814041) B2814041
theorem B4751419 : Blo 1875639 4751419 := bstep (se 1 (by rfl) ⟨3563564, by rfl⟩ : syracuseStep 4751419 = 7127129) B7127129
theorem B1876103 : Blo 1875639 1876103 := bstep (se 1 (by rfl) ⟨1407077, by rfl⟩ : syracuseStep 1876103 = 2814155) B2814155
theorem B1876111 : Blo 1875639 1876111 := bstep (se 1 (by rfl) ⟨1407083, by rfl⟩ : syracuseStep 1876111 = 2814167) B2814167
theorem B4571321 : Blo 1875639 4571321 := bstep (se 2 (by rfl) ⟨1714245, by rfl⟩ : syracuseStep 4571321 = 3428491) B3428491
theorem B1876155 : Blo 1875639 1876155 := bstep (se 1 (by rfl) ⟨1407116, by rfl⟩ : syracuseStep 1876155 = 2814233) B2814233
theorem B1876231 : Blo 1875639 1876231 := bstep (se 1 (by rfl) ⟨1407173, by rfl⟩ : syracuseStep 1876231 = 2814347) B2814347
theorem B1876239 : Blo 1875639 1876239 := bstep (se 1 (by rfl) ⟨1407179, by rfl⟩ : syracuseStep 1876239 = 2814359) B2814359
theorem B6332687 : Blo 1875639 6332687 := bstep (se 1 (by rfl) ⟨4749515, by rfl⟩ : syracuseStep 6332687 = 9499031) B9499031
theorem B10682675 : Blo 1875639 10682675 := bstep (se 1 (by rfl) ⟨8012006, by rfl⟩ : syracuseStep 10682675 = 16024013) B16024013
theorem B1876283 : Blo 1875639 1876283 := bstep (se 1 (by rfl) ⟨1407212, by rfl⟩ : syracuseStep 1876283 = 2814425) B2814425
theorem B1876359 : Blo 1875639 1876359 := bstep (se 1 (by rfl) ⟨1407269, by rfl⟩ : syracuseStep 1876359 = 2814539) B2814539
theorem B1876367 : Blo 1875639 1876367 := bstep (se 1 (by rfl) ⟨1407275, by rfl⟩ : syracuseStep 1876367 = 2814551) B2814551
theorem B1876411 : Blo 1875639 1876411 := bstep (se 1 (by rfl) ⟨1407308, by rfl⟩ : syracuseStep 1876411 = 2814617) B2814617
theorem B20283857 : Blo 1875639 20283857 := bstep (se 2 (by rfl) ⟨7606446, by rfl⟩ : syracuseStep 20283857 = 15212893) B15212893
theorem B1876487 : Blo 1875639 1876487 := bstep (se 1 (by rfl) ⟨1407365, by rfl⟩ : syracuseStep 1876487 = 2814731) B2814731
theorem B1876495 : Blo 1875639 1876495 := bstep (se 1 (by rfl) ⟨1407371, by rfl⟩ : syracuseStep 1876495 = 2814743) B2814743
theorem B6332957 : Blo 1875639 6332957 := bstep (se 3 (by rfl) ⟨1187429, by rfl⟩ : syracuseStep 6332957 = 2374859) B2374859
theorem B5784097 : Blo 1875639 5784097 := bstep (se 2 (by rfl) ⟨2169036, by rfl⟩ : syracuseStep 5784097 = 4338073) B4338073
theorem B2671147 : Blo 1875639 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B1876539 : Blo 1875639 1876539 := bstep (se 1 (by rfl) ⟨1407404, by rfl⟩ : syracuseStep 1876539 = 2814809) B2814809
theorem B1876615 : Blo 1875639 1876615 := bstep (se 1 (by rfl) ⟨1407461, by rfl⟩ : syracuseStep 1876615 = 2814923) B2814923
theorem B1876623 : Blo 1875639 1876623 := bstep (se 1 (by rfl) ⟨1407467, by rfl⟩ : syracuseStep 1876623 = 2814935) B2814935
theorem B1876667 : Blo 1875639 1876667 := bstep (se 1 (by rfl) ⟨1407500, by rfl⟩ : syracuseStep 1876667 = 2815001) B2815001
theorem B1876743 : Blo 1875639 1876743 := bstep (se 1 (by rfl) ⟨1407557, by rfl⟩ : syracuseStep 1876743 = 2815115) B2815115
theorem B2671375 : Blo 1875639 2671375 := bstep (se 1 (by rfl) ⟨2003531, by rfl⟩ : syracuseStep 2671375 = 4007063) B4007063
theorem B1876751 : Blo 1875639 1876751 := bstep (se 1 (by rfl) ⟨1407563, by rfl⟩ : syracuseStep 1876751 = 2815127) B2815127
theorem B1876795 : Blo 1875639 1876795 := bstep (se 1 (by rfl) ⟨1407596, by rfl⟩ : syracuseStep 1876795 = 2815193) B2815193
theorem B1876871 : Blo 1875639 1876871 := bstep (se 1 (by rfl) ⟨1407653, by rfl⟩ : syracuseStep 1876871 = 2815307) B2815307
theorem B1876879 : Blo 1875639 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B1876923 : Blo 1875639 1876923 := bstep (se 1 (by rfl) ⟨1407692, by rfl⟩ : syracuseStep 1876923 = 2815385) B2815385
theorem B1876999 : Blo 1875639 1876999 := bstep (se 1 (by rfl) ⟨1407749, by rfl⟩ : syracuseStep 1876999 = 2815499) B2815499
theorem B5415947 : Blo 1875639 5415947 := bstep (se 1 (by rfl) ⟨4061960, by rfl⟩ : syracuseStep 5415947 = 8123921) B8123921
theorem B1877007 : Blo 1875639 1877007 := bstep (se 1 (by rfl) ⟨1407755, by rfl⟩ : syracuseStep 1877007 = 2815511) B2815511
theorem B1877051 : Blo 1875639 1877051 := bstep (se 1 (by rfl) ⟨1407788, by rfl⟩ : syracuseStep 1877051 = 2815577) B2815577
theorem B6505591 : Blo 1875639 6505591 := bstep (se 1 (by rfl) ⟨4879193, by rfl⟩ : syracuseStep 6505591 = 9758387) B9758387
theorem B2671751 : Blo 1875639 2671751 := bstep (se 1 (by rfl) ⟨2003813, by rfl⟩ : syracuseStep 2671751 = 4007627) B4007627
theorem B1877127 : Blo 1875639 1877127 := bstep (se 1 (by rfl) ⟨1407845, by rfl⟩ : syracuseStep 1877127 = 2815691) B2815691
theorem B1877135 : Blo 1875639 1877135 := bstep (se 1 (by rfl) ⟨1407851, by rfl⟩ : syracuseStep 1877135 = 2815703) B2815703
theorem B4220279 : Blo 1875639 4220279 := bstep (se 1 (by rfl) ⟨3165209, by rfl⟩ : syracuseStep 4220279 = 6330419) B6330419
theorem B200263043 : Blo 1875639 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B4507015 : Blo 1875639 4507015 := bstep (se 1 (by rfl) ⟨3380261, by rfl⟩ : syracuseStep 4507015 = 6760523) B6760523
theorem B9495953 : Blo 1875639 9495953 := bstep (se 2 (by rfl) ⟨3560982, by rfl⟩ : syracuseStep 9495953 = 7121965) B7121965
theorem B79136185 : Blo 1875639 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B18032057 : Blo 1875639 18032057 := bstep (se 2 (by rfl) ⟨6762021, by rfl⟩ : syracuseStep 18032057 = 13524043) B13524043
theorem B4220459 : Blo 1875639 4220459 := bstep (se 1 (by rfl) ⟨3165344, by rfl⟩ : syracuseStep 4220459 = 6330689) B6330689
theorem B28878515 : Blo 1875639 28878515 := bstep (se 1 (by rfl) ⟨21658886, by rfl⟩ : syracuseStep 28878515 = 43317773) B43317773
theorem B10684133 : Blo 1875639 10684133 := bstep (se 4 (by rfl) ⟨1001637, by rfl⟩ : syracuseStep 10684133 = 2003275) B2003275
theorem B5072651 : Blo 1875639 5072651 := bstep (se 1 (by rfl) ⟨3804488, by rfl⟩ : syracuseStep 5072651 = 7608977) B7608977
theorem B7219003 : Blo 1875639 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B4220819 : Blo 1875639 4220819 := bstep (se 1 (by rfl) ⟨3165614, by rfl⟩ : syracuseStep 4220819 = 6331229) B6331229
theorem B6334361 : Blo 1875639 6334361 := bstep (se 2 (by rfl) ⟨2375385, by rfl⟩ : syracuseStep 6334361 = 4750771) B4750771
theorem B4220873 : Blo 1875639 4220873 := bstep (se 2 (by rfl) ⟨1582827, by rfl⟩ : syracuseStep 4220873 = 3165655) B3165655
theorem B9013277 : Blo 1875639 9013277 := bstep (se 3 (by rfl) ⟨1689989, by rfl⟩ : syracuseStep 9013277 = 3379979) B3379979
theorem B10143917 : Blo 1875639 10143917 := bstep (se 3 (by rfl) ⟨1901984, by rfl⟩ : syracuseStep 10143917 = 3803969) B3803969
theorem B166791437 : Blo 1875639 166791437 := bstep (se 3 (by rfl) ⟨31273394, by rfl⟩ : syracuseStep 166791437 = 62546789) B62546789
theorem B10684817 : Blo 1875639 10684817 := bstep (se 2 (by rfl) ⟨4006806, by rfl⟩ : syracuseStep 10684817 = 8013613) B8013613
theorem B5417401 : Blo 1875639 5417401 := bstep (se 2 (by rfl) ⟨2031525, by rfl⟩ : syracuseStep 5417401 = 4063051) B4063051
theorem B45631961 : Blo 1875639 45631961 := bstep (se 2 (by rfl) ⟨17111985, by rfl⟩ : syracuseStep 45631961 = 34223971) B34223971
theorem B6335063 : Blo 1875639 6335063 := bstep (se 1 (by rfl) ⟨4751297, by rfl⟩ : syracuseStep 6335063 = 9502595) B9502595
theorem B4221575 : Blo 1875639 4221575 := bstep (se 1 (by rfl) ⟨3166181, by rfl⟩ : syracuseStep 4221575 = 6332363) B6332363
theorem B2853623 : Blo 1875639 2853623 := bstep (se 1 (by rfl) ⟨2140217, by rfl⟩ : syracuseStep 2853623 = 4280435) B4280435
theorem B5344015 : Blo 1875639 5344015 := bstep (se 1 (by rfl) ⟨4008011, by rfl⟩ : syracuseStep 5344015 = 8016023) B8016023
theorem B4008737 : Blo 1875639 4008737 := bstep (se 2 (by rfl) ⟨1503276, by rfl⟩ : syracuseStep 4008737 = 3006553) B3006553
theorem B4221755 : Blo 1875639 4221755 := bstep (se 1 (by rfl) ⟨3166316, by rfl⟩ : syracuseStep 4221755 = 6332633) B6332633
theorem B5073799 : Blo 1875639 5073799 := bstep (se 1 (by rfl) ⟨3805349, by rfl⟩ : syracuseStep 5073799 = 7610699) B7610699
theorem B4221881 : Blo 1875639 4221881 := bstep (se 2 (by rfl) ⟨1583205, by rfl⟩ : syracuseStep 4221881 = 3166411) B3166411
theorem B5344289 : Blo 1875639 5344289 := bstep (se 2 (by rfl) ⟨2004108, by rfl⟩ : syracuseStep 5344289 = 4008217) B4008217
theorem B13896791 : Blo 1875639 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B3165385 : Blo 1875639 3165385 := bstep (se 2 (by rfl) ⟨1187019, by rfl⟩ : syracuseStep 3165385 = 2374039) B2374039
theorem B4222223 : Blo 1875639 4222223 := bstep (se 1 (by rfl) ⟨3166667, by rfl⟩ : syracuseStep 4222223 = 6333335) B6333335
theorem B4222241 : Blo 1875639 4222241 := bstep (se 2 (by rfl) ⟨1583340, by rfl⟩ : syracuseStep 4222241 = 3166681) B3166681
theorem B9137497 : Blo 1875639 9137497 := bstep (se 2 (by rfl) ⟨3426561, by rfl⟩ : syracuseStep 9137497 = 6853123) B6853123
theorem B8015219 : Blo 1875639 8015219 := bstep (se 1 (by rfl) ⟨6011414, by rfl⟩ : syracuseStep 8015219 = 12022829) B12022829
theorem B10685843 : Blo 1875639 10685843 := bstep (se 1 (by rfl) ⟨8014382, by rfl⟩ : syracuseStep 10685843 = 16028765) B16028765
theorem B9498059 : Blo 1875639 9498059 := bstep (se 1 (by rfl) ⟨7123544, by rfl⟩ : syracuseStep 9498059 = 14247089) B14247089
theorem B2813483 : Blo 1875639 2813483 := bstep (se 1 (by rfl) ⟨2110112, by rfl⟩ : syracuseStep 2813483 = 4220225) B4220225
theorem B2813513 : Blo 1875639 2813513 := bstep (se 2 (by rfl) ⟨1055067, by rfl⟩ : syracuseStep 2813513 = 2110135) B2110135
theorem B27053669 : Blo 1875639 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B4222583 : Blo 1875639 4222583 := bstep (se 1 (by rfl) ⟨3166937, by rfl⟩ : syracuseStep 4222583 = 6333875) B6333875
theorem B45641393 : Blo 1875639 45641393 := bstep (se 2 (by rfl) ⟨17115522, by rfl⟩ : syracuseStep 45641393 = 34231045) B34231045
theorem B2813627 : Blo 1875639 2813627 := bstep (se 1 (by rfl) ⟨2110220, by rfl⟩ : syracuseStep 2813627 = 4220441) B4220441
theorem B8015561 : Blo 1875639 8015561 := bstep (se 2 (by rfl) ⟨3005835, by rfl⟩ : syracuseStep 8015561 = 6011671) B6011671
theorem B2813687 : Blo 1875639 2813687 := bstep (se 1 (by rfl) ⟨2110265, by rfl⟩ : syracuseStep 2813687 = 4220531) B4220531
theorem B2813711 : Blo 1875639 2813711 := bstep (se 1 (by rfl) ⟨2110283, by rfl⟩ : syracuseStep 2813711 = 4220567) B4220567
theorem B9498383 : Blo 1875639 9498383 := bstep (se 1 (by rfl) ⟨7123787, by rfl⟩ : syracuseStep 9498383 = 14247575) B14247575
theorem B16027429 : Blo 1875639 16027429 := bstep (se 4 (by rfl) ⟨1502571, by rfl⟩ : syracuseStep 16027429 = 3005143) B3005143
theorem B4222763 : Blo 1875639 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B2813753 : Blo 1875639 2813753 := bstep (se 2 (by rfl) ⟨1055157, by rfl⟩ : syracuseStep 2813753 = 2110315) B2110315
theorem B2813831 : Blo 1875639 2813831 := bstep (se 1 (by rfl) ⟨2110373, by rfl⟩ : syracuseStep 2813831 = 4220747) B4220747
theorem B3166087 : Blo 1875639 3166087 := bstep (se 1 (by rfl) ⟨2374565, by rfl⟩ : syracuseStep 3166087 = 4749131) B4749131
theorem B5353363 : Blo 1875639 5353363 := bstep (se 1 (by rfl) ⟨4015022, by rfl⟩ : syracuseStep 5353363 = 8030045) B8030045
theorem B2813867 : Blo 1875639 2813867 := bstep (se 1 (by rfl) ⟨2110400, by rfl⟩ : syracuseStep 2813867 = 4220801) B4220801
theorem B2813897 : Blo 1875639 2813897 := bstep (se 2 (by rfl) ⟨1055211, by rfl⟩ : syracuseStep 2813897 = 2110423) B2110423
theorem B304500683 : Blo 1875639 304500683 := bstep (se 1 (by rfl) ⟨228375512, by rfl⟩ : syracuseStep 304500683 = 456751025) B456751025
theorem B5345291 : Blo 1875639 5345291 := bstep (se 1 (by rfl) ⟨4008968, by rfl⟩ : syracuseStep 5345291 = 8017937) B8017937
theorem B2814011 : Blo 1875639 2814011 := bstep (se 1 (by rfl) ⟨2110508, by rfl⟩ : syracuseStep 2814011 = 4221017) B4221017
theorem B16691287 : Blo 1875639 16691287 := bstep (se 1 (by rfl) ⟨12518465, by rfl⟩ : syracuseStep 16691287 = 25036931) B25036931
theorem B2814071 : Blo 1875639 2814071 := bstep (se 1 (by rfl) ⟨2110553, by rfl⟩ : syracuseStep 2814071 = 4221107) B4221107
theorem B2003087 : Blo 1875639 2003087 := bstep (se 1 (by rfl) ⟨1502315, by rfl⟩ : syracuseStep 2003087 = 3004631) B3004631
theorem B2814095 : Blo 1875639 2814095 := bstep (se 1 (by rfl) ⟨2110571, by rfl⟩ : syracuseStep 2814095 = 4221143) B4221143
theorem B4223123 : Blo 1875639 4223123 := bstep (se 1 (by rfl) ⟨3167342, by rfl⟩ : syracuseStep 4223123 = 6334685) B6334685
theorem B27046061 : Blo 1875639 27046061 := bstep (se 3 (by rfl) ⟨5071136, by rfl⟩ : syracuseStep 27046061 = 10142273) B10142273
theorem B2814137 : Blo 1875639 2814137 := bstep (se 2 (by rfl) ⟨1055301, by rfl⟩ : syracuseStep 2814137 = 2110603) B2110603
theorem B4223177 : Blo 1875639 4223177 := bstep (se 2 (by rfl) ⟨1583691, by rfl⟩ : syracuseStep 4223177 = 3167383) B3167383
theorem B2814215 : Blo 1875639 2814215 := bstep (se 1 (by rfl) ⟨2110661, by rfl⟩ : syracuseStep 2814215 = 4221323) B4221323
theorem B8122639 : Blo 1875639 8122639 := bstep (se 1 (by rfl) ⟨6091979, by rfl⟩ : syracuseStep 8122639 = 12183959) B12183959
theorem B2814251 : Blo 1875639 2814251 := bstep (se 1 (by rfl) ⟨2110688, by rfl⟩ : syracuseStep 2814251 = 4221377) B4221377
theorem B2814281 : Blo 1875639 2814281 := bstep (se 2 (by rfl) ⟨1055355, by rfl⟩ : syracuseStep 2814281 = 2110711) B2110711
theorem B6762899 : Blo 1875639 6762899 := bstep (se 1 (by rfl) ⟨5072174, by rfl⟩ : syracuseStep 6762899 = 10144349) B10144349
theorem B2814395 : Blo 1875639 2814395 := bstep (se 1 (by rfl) ⟨2110796, by rfl⟩ : syracuseStep 2814395 = 4221593) B4221593
theorem B7123409 : Blo 1875639 7123409 := bstep (se 2 (by rfl) ⟨2671278, by rfl⟩ : syracuseStep 7123409 = 5342557) B5342557
theorem B2814455 : Blo 1875639 2814455 := bstep (se 1 (by rfl) ⟨2110841, by rfl⟩ : syracuseStep 2814455 = 4221683) B4221683
theorem B2814479 : Blo 1875639 2814479 := bstep (se 1 (by rfl) ⟨2110859, by rfl⟩ : syracuseStep 2814479 = 4221719) B4221719
theorem B3166735 : Blo 1875639 3166735 := bstep (se 1 (by rfl) ⟨2375051, by rfl⟩ : syracuseStep 3166735 = 4750103) B4750103
theorem B2814521 : Blo 1875639 2814521 := bstep (se 2 (by rfl) ⟨1055445, by rfl⟩ : syracuseStep 2814521 = 2110891) B2110891
theorem B4747835 : Blo 1875639 4747835 := bstep (se 1 (by rfl) ⟨3560876, by rfl⟩ : syracuseStep 4747835 = 7121753) B7121753
theorem B2814599 : Blo 1875639 2814599 := bstep (se 1 (by rfl) ⟨2110949, by rfl⟩ : syracuseStep 2814599 = 4221899) B4221899
theorem B2814635 : Blo 1875639 2814635 := bstep (se 1 (by rfl) ⟨2110976, by rfl⟩ : syracuseStep 2814635 = 4221953) B4221953
theorem B20288177 : Blo 1875639 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B2814665 : Blo 1875639 2814665 := bstep (se 2 (by rfl) ⟨1055499, by rfl⟩ : syracuseStep 2814665 = 2110999) B2110999
theorem B7123727 : Blo 1875639 7123727 := bstep (se 1 (by rfl) ⟨5342795, by rfl⟩ : syracuseStep 7123727 = 10685591) B10685591
theorem B2814779 : Blo 1875639 2814779 := bstep (se 1 (by rfl) ⟨2111084, by rfl⟩ : syracuseStep 2814779 = 4222169) B4222169
theorem B2814839 : Blo 1875639 2814839 := bstep (se 1 (by rfl) ⟨2111129, by rfl⟩ : syracuseStep 2814839 = 4222259) B4222259
theorem B2110351 : Blo 1875639 2110351 := bstep (se 1 (by rfl) ⟨1582763, by rfl⟩ : syracuseStep 2110351 = 3165527) B3165527
theorem B2814863 : Blo 1875639 2814863 := bstep (se 1 (by rfl) ⟨2111147, by rfl⟩ : syracuseStep 2814863 = 4222295) B4222295
theorem B4748179 : Blo 1875639 4748179 := bstep (se 1 (by rfl) ⟨3561134, by rfl⟩ : syracuseStep 4748179 = 7122269) B7122269
theorem B2814905 : Blo 1875639 2814905 := bstep (se 2 (by rfl) ⟨1055589, by rfl⟩ : syracuseStep 2814905 = 2111179) B2111179
theorem B2814983 : Blo 1875639 2814983 := bstep (se 1 (by rfl) ⟨2111237, by rfl⟩ : syracuseStep 2814983 = 4222475) B4222475
theorem B4748321 : Blo 1875639 4748321 := bstep (se 2 (by rfl) ⟨1780620, by rfl⟩ : syracuseStep 4748321 = 3561241) B3561241
theorem B2815019 : Blo 1875639 2815019 := bstep (se 1 (by rfl) ⟨2111264, by rfl⟩ : syracuseStep 2815019 = 4222529) B4222529
theorem B3167275 : Blo 1875639 3167275 := bstep (se 1 (by rfl) ⟨2375456, by rfl⟩ : syracuseStep 3167275 = 4750913) B4750913
theorem B2815049 : Blo 1875639 2815049 := bstep (se 2 (by rfl) ⟨1055643, by rfl⟩ : syracuseStep 2815049 = 2111287) B2111287
theorem B3167417 : Blo 1875639 3167417 := bstep (se 2 (by rfl) ⟨1187781, by rfl⟩ : syracuseStep 3167417 = 2375563) B2375563
theorem B2815163 : Blo 1875639 2815163 := bstep (se 1 (by rfl) ⟨2111372, by rfl⟩ : syracuseStep 2815163 = 4222745) B4222745
theorem B9499841 : Blo 1875639 9499841 := bstep (se 2 (by rfl) ⟨3562440, by rfl⟩ : syracuseStep 9499841 = 7124881) B7124881
theorem B2815223 : Blo 1875639 2815223 := bstep (se 1 (by rfl) ⟨2111417, by rfl⟩ : syracuseStep 2815223 = 4222835) B4222835
theorem B2815247 : Blo 1875639 2815247 := bstep (se 1 (by rfl) ⟨2111435, by rfl⟩ : syracuseStep 2815247 = 4222871) B4222871
theorem B2815289 : Blo 1875639 2815289 := bstep (se 2 (by rfl) ⟨1055733, by rfl⟩ : syracuseStep 2815289 = 2111467) B2111467
theorem B2004283 : Blo 1875639 2004283 := bstep (se 1 (by rfl) ⟨1503212, by rfl⟩ : syracuseStep 2004283 = 3006425) B3006425
theorem B2110855 : Blo 1875639 2110855 := bstep (se 1 (by rfl) ⟨1583141, by rfl⟩ : syracuseStep 2110855 = 3166283) B3166283
theorem B2815367 : Blo 1875639 2815367 := bstep (se 1 (by rfl) ⟨2111525, by rfl⟩ : syracuseStep 2815367 = 4223051) B4223051
theorem B2815403 : Blo 1875639 2815403 := bstep (se 1 (by rfl) ⟨2111552, by rfl⟩ : syracuseStep 2815403 = 4223105) B4223105
theorem B2815433 : Blo 1875639 2815433 := bstep (se 2 (by rfl) ⟨1055787, by rfl⟩ : syracuseStep 2815433 = 2111575) B2111575
theorem B2111035 : Blo 1875639 2111035 := bstep (se 1 (by rfl) ⟨1583276, by rfl⟩ : syracuseStep 2111035 = 3166553) B3166553
theorem B2815547 : Blo 1875639 2815547 := bstep (se 1 (by rfl) ⟨2111660, by rfl⟩ : syracuseStep 2815547 = 4223321) B4223321
theorem B2569801 : Blo 1875639 2569801 := bstep (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) B1927351
theorem B2815607 : Blo 1875639 2815607 := bstep (se 1 (by rfl) ⟨2111705, by rfl⟩ : syracuseStep 2815607 = 4223411) B4223411
theorem B2815631 : Blo 1875639 2815631 := bstep (se 1 (by rfl) ⟨2111723, by rfl⟩ : syracuseStep 2815631 = 4223447) B4223447
theorem B2815673 : Blo 1875639 2815673 := bstep (se 2 (by rfl) ⟨1055877, by rfl⟩ : syracuseStep 2815673 = 2111755) B2111755
theorem B16029413 : Blo 1875639 16029413 := bstep (se 4 (by rfl) ⟨1502757, by rfl⟩ : syracuseStep 16029413 = 3005515) B3005515
theorem B8017679 : Blo 1875639 8017679 := bstep (se 1 (by rfl) ⟨6013259, by rfl⟩ : syracuseStep 8017679 = 12026519) B12026519
theorem B3561401 : Blo 1875639 3561401 := bstep (se 2 (by rfl) ⟨1335525, by rfl⟩ : syracuseStep 3561401 = 2671051) B2671051
theorem B4749313 : Blo 1875639 4749313 := bstep (se 2 (by rfl) ⟨1780992, by rfl⟩ : syracuseStep 4749313 = 3561985) B3561985
theorem B2111503 : Blo 1875639 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B4569131 : Blo 1875639 4569131 := bstep (se 1 (by rfl) ⟨3426848, by rfl⟩ : syracuseStep 4569131 = 6853697) B6853697
theorem B24049709 : Blo 1875639 24049709 := bstep (se 3 (by rfl) ⟨4509320, by rfl⟩ : syracuseStep 24049709 = 9018641) B9018641
theorem B8017987 : Blo 1875639 8017987 := bstep (se 1 (by rfl) ⟨6013490, by rfl⟩ : syracuseStep 8017987 = 12026981) B12026981
theorem B5142647 : Blo 1875639 5142647 := bstep (se 1 (by rfl) ⟨3856985, by rfl⟩ : syracuseStep 5142647 = 7713971) B7713971
theorem B6764801 : Blo 1875639 6764801 := bstep (se 2 (by rfl) ⟨2536800, by rfl⟩ : syracuseStep 6764801 = 5073601) B5073601
theorem B18037009 : Blo 1875639 18037009 := bstep (se 2 (by rfl) ⟨6763878, by rfl⟩ : syracuseStep 18037009 = 13527757) B13527757
theorem B4815137 : Blo 1875639 4815137 := bstep (se 2 (by rfl) ⟨1805676, by rfl⟩ : syracuseStep 4815137 = 3611353) B3611353
theorem B14252435 : Blo 1875639 14252435 := bstep (se 1 (by rfl) ⟨10689326, by rfl⟩ : syracuseStep 14252435 = 21378653) B21378653
theorem B9501137 : Blo 1875639 9501137 := bstep (se 2 (by rfl) ⟨3562926, by rfl⟩ : syracuseStep 9501137 = 7125853) B7125853
theorem B23140829 : Blo 1875639 23140829 := bstep (se 3 (by rfl) ⟨4338905, by rfl⟩ : syracuseStep 23140829 = 8677811) B8677811
theorem B24713795 : Blo 1875639 24713795 := bstep (se 1 (by rfl) ⟨18535346, by rfl⟩ : syracuseStep 24713795 = 37070693) B37070693
theorem B4749911 : Blo 1875639 4749911 := bstep (se 1 (by rfl) ⟨3562433, by rfl⟩ : syracuseStep 4749911 = 7124867) B7124867
theorem B5143175 : Blo 1875639 5143175 := bstep (se 1 (by rfl) ⟨3857381, by rfl⟩ : syracuseStep 5143175 = 7714763) B7714763
theorem B4750123 : Blo 1875639 4750123 := bstep (se 1 (by rfl) ⟨3562592, by rfl⟩ : syracuseStep 4750123 = 7125185) B7125185
theorem B14244659 : Blo 1875639 14244659 := bstep (se 1 (by rfl) ⟨10683494, by rfl⟩ : syracuseStep 14244659 = 21366989) B21366989
theorem B2374535 : Blo 1875639 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B6331283 : Blo 1875639 6331283 := bstep (se 1 (by rfl) ⟨4748462, by rfl⟩ : syracuseStep 6331283 = 9496925) B9496925
theorem B4750265 : Blo 1875639 4750265 := bstep (se 2 (by rfl) ⟨1781349, by rfl⟩ : syracuseStep 4750265 = 3562699) B3562699
theorem B9018391 : Blo 1875639 9018391 := bstep (se 1 (by rfl) ⟨6763793, by rfl⟩ : syracuseStep 9018391 = 13527587) B13527587
theorem B3562555 : Blo 1875639 3562555 := bstep (se 1 (by rfl) ⟨2671916, by rfl⟩ : syracuseStep 3562555 = 5343833) B5343833
theorem B2284843 : Blo 1875639 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B2375183 : Blo 1875639 2375183 := bstep (se 1 (by rfl) ⟨1781387, by rfl⟩ : syracuseStep 2375183 = 3562775) B3562775
theorem B3563041 : Blo 1875639 3563041 := bstep (se 2 (by rfl) ⟨1336140, by rfl⟩ : syracuseStep 3563041 = 2672281) B2672281
theorem B1875643 : Blo 1875639 1875643 := bstep (se 1 (by rfl) ⟨1406732, by rfl⟩ : syracuseStep 1875643 = 2813465) B2813465
theorem B1875719 : Blo 1875639 1875719 := bstep (se 1 (by rfl) ⟨1406789, by rfl⟩ : syracuseStep 1875719 = 2813579) B2813579
theorem B1875727 : Blo 1875639 1875727 := bstep (se 1 (by rfl) ⟨1406795, by rfl⟩ : syracuseStep 1875727 = 2813591) B2813591
theorem B1875771 : Blo 1875639 1875771 := bstep (se 1 (by rfl) ⟨1406828, by rfl⟩ : syracuseStep 1875771 = 2813657) B2813657
theorem B1875847 : Blo 1875639 1875847 := bstep (se 1 (by rfl) ⟨1406885, by rfl⟩ : syracuseStep 1875847 = 2813771) B2813771
theorem B1875855 : Blo 1875639 1875855 := bstep (se 1 (by rfl) ⟨1406891, by rfl⟩ : syracuseStep 1875855 = 2813783) B2813783
theorem B4751257 : Blo 1875639 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B1875899 : Blo 1875639 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B6332417 : Blo 1875639 6332417 := bstep (se 2 (by rfl) ⟨2374656, by rfl⟩ : syracuseStep 6332417 = 4749313) B4749313
theorem B3563527 : Blo 1875639 3563527 := bstep (se 1 (by rfl) ⟨2672645, by rfl⟩ : syracuseStep 3563527 = 5345291) B5345291
theorem B1876007 : Blo 1875639 1876007 := bstep (se 1 (by rfl) ⟨1407005, by rfl⟩ : syracuseStep 1876007 = 2814011) B2814011
theorem B1876047 : Blo 1875639 1876047 := bstep (se 1 (by rfl) ⟨1407035, by rfl⟩ : syracuseStep 1876047 = 2814071) B2814071
theorem B10690649 : Blo 1875639 10690649 := bstep (se 2 (by rfl) ⟨4008993, by rfl⟩ : syracuseStep 10690649 = 8017987) B8017987
theorem B1876063 : Blo 1875639 1876063 := bstep (se 1 (by rfl) ⟨1407047, by rfl⟩ : syracuseStep 1876063 = 2814095) B2814095
theorem B18030707 : Blo 1875639 18030707 := bstep (se 1 (by rfl) ⟨13523030, by rfl⟩ : syracuseStep 18030707 = 27046061) B27046061
theorem B1876091 : Blo 1875639 1876091 := bstep (se 1 (by rfl) ⟨1407068, by rfl⟩ : syracuseStep 1876091 = 2814137) B2814137
theorem B1876143 : Blo 1875639 1876143 := bstep (se 1 (by rfl) ⟨1407107, by rfl⟩ : syracuseStep 1876143 = 2814215) B2814215
theorem B1876167 : Blo 1875639 1876167 := bstep (se 1 (by rfl) ⟨1407125, by rfl⟩ : syracuseStep 1876167 = 2814251) B2814251
theorem B1876187 : Blo 1875639 1876187 := bstep (se 1 (by rfl) ⟨1407140, by rfl⟩ : syracuseStep 1876187 = 2814281) B2814281
theorem B14246117 : Blo 1875639 14246117 := bstep (se 4 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 14246117 = 2671147) B2671147
theorem B1876263 : Blo 1875639 1876263 := bstep (se 1 (by rfl) ⟨1407197, by rfl⟩ : syracuseStep 1876263 = 2814395) B2814395
theorem B13713725 : Blo 1875639 13713725 := bstep (se 3 (by rfl) ⟨2571323, by rfl⟩ : syracuseStep 13713725 = 5142647) B5142647
theorem B1876303 : Blo 1875639 1876303 := bstep (se 1 (by rfl) ⟨1407227, by rfl⟩ : syracuseStep 1876303 = 2814455) B2814455
theorem B1876319 : Blo 1875639 1876319 := bstep (se 1 (by rfl) ⟨1407239, by rfl⟩ : syracuseStep 1876319 = 2814479) B2814479
theorem B10830185 : Blo 1875639 10830185 := bstep (se 2 (by rfl) ⟨4061319, by rfl⟩ : syracuseStep 10830185 = 8122639) B8122639
theorem B1876347 : Blo 1875639 1876347 := bstep (se 1 (by rfl) ⟨1407260, by rfl⟩ : syracuseStep 1876347 = 2814521) B2814521
theorem B5341565 : Blo 1875639 5341565 := bstep (se 3 (by rfl) ⟨1001543, by rfl⟩ : syracuseStep 5341565 = 2003087) B2003087
theorem B1876399 : Blo 1875639 1876399 := bstep (se 1 (by rfl) ⟨1407299, by rfl⟩ : syracuseStep 1876399 = 2814599) B2814599
theorem B1876423 : Blo 1875639 1876423 := bstep (se 1 (by rfl) ⟨1407317, by rfl⟩ : syracuseStep 1876423 = 2814635) B2814635
theorem B13525451 : Blo 1875639 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B1876443 : Blo 1875639 1876443 := bstep (se 1 (by rfl) ⟨1407332, by rfl⟩ : syracuseStep 1876443 = 2814665) B2814665
theorem B12190189 : Blo 1875639 12190189 := bstep (se 3 (by rfl) ⟨2285660, by rfl⟩ : syracuseStep 12190189 = 4571321) B4571321
theorem B1876519 : Blo 1875639 1876519 := bstep (se 1 (by rfl) ⟨1407389, by rfl⟩ : syracuseStep 1876519 = 2814779) B2814779
theorem B1876559 : Blo 1875639 1876559 := bstep (se 1 (by rfl) ⟨1407419, by rfl⟩ : syracuseStep 1876559 = 2814839) B2814839
theorem B1876575 : Blo 1875639 1876575 := bstep (se 1 (by rfl) ⟨1407431, by rfl⟩ : syracuseStep 1876575 = 2814863) B2814863
theorem B1876603 : Blo 1875639 1876603 := bstep (se 1 (by rfl) ⟨1407452, by rfl⟩ : syracuseStep 1876603 = 2814905) B2814905
theorem B1876655 : Blo 1875639 1876655 := bstep (se 1 (by rfl) ⟨1407491, by rfl⟩ : syracuseStep 1876655 = 2814983) B2814983
theorem B1876679 : Blo 1875639 1876679 := bstep (se 1 (by rfl) ⟨1407509, by rfl⟩ : syracuseStep 1876679 = 2815019) B2815019
theorem B1876699 : Blo 1875639 1876699 := bstep (se 1 (by rfl) ⟨1407524, by rfl⟩ : syracuseStep 1876699 = 2815049) B2815049
theorem B1876775 : Blo 1875639 1876775 := bstep (se 1 (by rfl) ⟨1407581, by rfl⟩ : syracuseStep 1876775 = 2815163) B2815163
theorem B6333227 : Blo 1875639 6333227 := bstep (se 1 (by rfl) ⟨4749920, by rfl⟩ : syracuseStep 6333227 = 9499841) B9499841
theorem B1876815 : Blo 1875639 1876815 := bstep (se 1 (by rfl) ⟨1407611, by rfl⟩ : syracuseStep 1876815 = 2815223) B2815223
theorem B1876831 : Blo 1875639 1876831 := bstep (se 1 (by rfl) ⟨1407623, by rfl⟩ : syracuseStep 1876831 = 2815247) B2815247
theorem B1876859 : Blo 1875639 1876859 := bstep (se 1 (by rfl) ⟨1407644, by rfl⟩ : syracuseStep 1876859 = 2815289) B2815289
theorem B1876911 : Blo 1875639 1876911 := bstep (se 1 (by rfl) ⟨1407683, by rfl⟩ : syracuseStep 1876911 = 2815367) B2815367
theorem B1876935 : Blo 1875639 1876935 := bstep (se 1 (by rfl) ⟨1407701, by rfl⟩ : syracuseStep 1876935 = 2815403) B2815403
theorem B1876955 : Blo 1875639 1876955 := bstep (se 1 (by rfl) ⟨1407716, by rfl⟩ : syracuseStep 1876955 = 2815433) B2815433
theorem B1877031 : Blo 1875639 1877031 := bstep (se 1 (by rfl) ⟨1407773, by rfl⟩ : syracuseStep 1877031 = 2815547) B2815547
theorem B6333497 : Blo 1875639 6333497 := bstep (se 2 (by rfl) ⟨2375061, by rfl⟩ : syracuseStep 6333497 = 4750123) B4750123
theorem B1877071 : Blo 1875639 1877071 := bstep (se 1 (by rfl) ⟨1407803, by rfl⟩ : syracuseStep 1877071 = 2815607) B2815607
theorem B1877087 : Blo 1875639 1877087 := bstep (se 1 (by rfl) ⟨1407815, by rfl⟩ : syracuseStep 1877087 = 2815631) B2815631
theorem B19252343 : Blo 1875639 19252343 := bstep (se 1 (by rfl) ⟨14439257, by rfl⟩ : syracuseStep 19252343 = 28878515) B28878515
theorem B1877115 : Blo 1875639 1877115 := bstep (se 1 (by rfl) ⟨1407836, by rfl⟩ : syracuseStep 1877115 = 2815673) B2815673
theorem B16033139 : Blo 1875639 16033139 := bstep (se 1 (by rfl) ⟨12024854, by rfl⟩ : syracuseStep 16033139 = 24049709) B24049709
theorem B6333821 : Blo 1875639 6333821 := bstep (se 3 (by rfl) ⟨1187591, by rfl⟩ : syracuseStep 6333821 = 2375183) B2375183
theorem B4220513 : Blo 1875639 4220513 := bstep (se 2 (by rfl) ⟨1582692, by rfl⟩ : syracuseStep 4220513 = 3165385) B3165385
theorem B6334091 : Blo 1875639 6334091 := bstep (se 1 (by rfl) ⟨4750568, by rfl⟩ : syracuseStep 6334091 = 9501137) B9501137
theorem B12183329 : Blo 1875639 12183329 := bstep (se 2 (by rfl) ⟨4568748, by rfl⟩ : syracuseStep 12183329 = 9137497) B9137497
theorem B1902415 : Blo 1875639 1902415 := bstep (se 1 (by rfl) ⟨1426811, by rfl⟩ : syracuseStep 1902415 = 2853623) B2853623
theorem B51968116565 : Blo 1875639 51968116565 := bstep (se 9 (by rfl) ⟨152250341, by rfl⟩ : syracuseStep 51968116565 = 304500683) B304500683
theorem B9496439 : Blo 1875639 9496439 := bstep (se 1 (by rfl) ⟨7122329, by rfl⟩ : syracuseStep 9496439 = 14244659) B14244659
theorem B105514913 : Blo 1875639 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B4220855 : Blo 1875639 4220855 := bstep (se 1 (by rfl) ⟨3165641, by rfl⟩ : syracuseStep 4220855 = 6331283) B6331283
theorem B3426401 : Blo 1875639 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B5343479 : Blo 1875639 5343479 := bstep (se 1 (by rfl) ⟨4007609, by rfl⟩ : syracuseStep 5343479 = 8015219) B8015219
theorem B30427595 : Blo 1875639 30427595 := bstep (se 1 (by rfl) ⟨22820696, by rfl⟩ : syracuseStep 30427595 = 45641393) B45641393
theorem B5343707 : Blo 1875639 5343707 := bstep (se 1 (by rfl) ⟨4007780, by rfl⟩ : syracuseStep 5343707 = 8015561) B8015561
theorem B4221449 : Blo 1875639 4221449 := bstep (se 2 (by rfl) ⟨1583043, by rfl⟩ : syracuseStep 4221449 = 3166087) B3166087
theorem B7137817 : Blo 1875639 7137817 := bstep (se 2 (by rfl) ⟨2676681, by rfl⟩ : syracuseStep 7137817 = 5353363) B5353363
theorem B6335009 : Blo 1875639 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B72157877 : Blo 1875639 72157877 := bstep (se 5 (by rfl) ⟨3382400, by rfl⟩ : syracuseStep 72157877 = 6764801) B6764801
theorem B6335225 : Blo 1875639 6335225 := bstep (se 2 (by rfl) ⟨2375709, by rfl⟩ : syracuseStep 6335225 = 4751419) B4751419
theorem B4221791 : Blo 1875639 4221791 := bstep (se 1 (by rfl) ⟨3166343, by rfl⟩ : syracuseStep 4221791 = 6332687) B6332687
theorem B7121783 : Blo 1875639 7121783 := bstep (se 1 (by rfl) ⟨5341337, by rfl⟩ : syracuseStep 7121783 = 10682675) B10682675
theorem B4221971 : Blo 1875639 4221971 := bstep (se 1 (by rfl) ⟨3166478, by rfl⟩ : syracuseStep 4221971 = 6332957) B6332957
theorem B3165223 : Blo 1875639 3165223 := bstep (se 1 (by rfl) ⟨2373917, by rfl⟩ : syracuseStep 3165223 = 4747835) B4747835
theorem B4222313 : Blo 1875639 4222313 := bstep (se 2 (by rfl) ⟨1583367, by rfl⟩ : syracuseStep 4222313 = 3166735) B3166735
theorem B3165547 : Blo 1875639 3165547 := bstep (se 1 (by rfl) ⟨2374160, by rfl⟩ : syracuseStep 3165547 = 4748321) B4748321
theorem B7712129 : Blo 1875639 7712129 := bstep (se 2 (by rfl) ⟨2892048, by rfl⟩ : syracuseStep 7712129 = 5784097) B5784097
theorem B12840365 : Blo 1875639 12840365 := bstep (se 3 (by rfl) ⟨2407568, by rfl⟩ : syracuseStep 12840365 = 4815137) B4815137
theorem B2813519 : Blo 1875639 2813519 := bstep (se 1 (by rfl) ⟨2110139, by rfl⟩ : syracuseStep 2813519 = 4220279) B4220279
theorem B12021371 : Blo 1875639 12021371 := bstep (se 1 (by rfl) ⟨9016028, by rfl⟩ : syracuseStep 12021371 = 18032057) B18032057
theorem B2813639 : Blo 1875639 2813639 := bstep (se 1 (by rfl) ⟨2110229, by rfl⟩ : syracuseStep 2813639 = 4220459) B4220459
theorem B18034397 : Blo 1875639 18034397 := bstep (se 3 (by rfl) ⟨3381449, by rfl⟩ : syracuseStep 18034397 = 6762899) B6762899
theorem B7122755 : Blo 1875639 7122755 := bstep (se 1 (by rfl) ⟨5342066, by rfl⟩ : syracuseStep 7122755 = 10684133) B10684133
theorem B10686275 : Blo 1875639 10686275 := bstep (se 1 (by rfl) ⟨8014706, by rfl⟩ : syracuseStep 10686275 = 16029413) B16029413
theorem B5345119 : Blo 1875639 5345119 := bstep (se 1 (by rfl) ⟨4008839, by rfl⟩ : syracuseStep 5345119 = 8017679) B8017679
theorem B2813801 : Blo 1875639 2813801 := bstep (se 2 (by rfl) ⟨1055175, by rfl⟩ : syracuseStep 2813801 = 2110351) B2110351
theorem B2813879 : Blo 1875639 2813879 := bstep (se 1 (by rfl) ⟨2110409, by rfl⟩ : syracuseStep 2813879 = 4220819) B4220819
theorem B4222907 : Blo 1875639 4222907 := bstep (se 1 (by rfl) ⟨3167180, by rfl⟩ : syracuseStep 4222907 = 6334361) B6334361
theorem B2813915 : Blo 1875639 2813915 := bstep (se 1 (by rfl) ⟨2110436, by rfl⟩ : syracuseStep 2813915 = 4220873) B4220873
theorem B6008851 : Blo 1875639 6008851 := bstep (se 1 (by rfl) ⟨4506638, by rfl⟩ : syracuseStep 6008851 = 9013277) B9013277
theorem B4223033 : Blo 1875639 4223033 := bstep (se 2 (by rfl) ⟨1583637, by rfl⟩ : syracuseStep 4223033 = 3167275) B3167275
theorem B6762611 : Blo 1875639 6762611 := bstep (se 1 (by rfl) ⟨5071958, by rfl⟩ : syracuseStep 6762611 = 10143917) B10143917
theorem B111194291 : Blo 1875639 111194291 := bstep (se 1 (by rfl) ⟨83395718, by rfl⟩ : syracuseStep 111194291 = 166791437) B166791437
theorem B7123211 : Blo 1875639 7123211 := bstep (se 1 (by rfl) ⟨5342408, by rfl⟩ : syracuseStep 7123211 = 10684817) B10684817
theorem B30421307 : Blo 1875639 30421307 := bstep (se 1 (by rfl) ⟨22815980, by rfl⟩ : syracuseStep 30421307 = 45631961) B45631961
theorem B3166607 : Blo 1875639 3166607 := bstep (se 1 (by rfl) ⟨2374955, by rfl⟩ : syracuseStep 3166607 = 4749911) B4749911
theorem B4223375 : Blo 1875639 4223375 := bstep (se 1 (by rfl) ⟨3167531, by rfl⟩ : syracuseStep 4223375 = 6335063) B6335063
theorem B2814383 : Blo 1875639 2814383 := bstep (se 1 (by rfl) ⟨2110787, by rfl⟩ : syracuseStep 2814383 = 4221575) B4221575
theorem B3428783 : Blo 1875639 3428783 := bstep (se 1 (by rfl) ⟨2571587, by rfl⟩ : syracuseStep 3428783 = 5143175) B5143175
theorem B6009353 : Blo 1875639 6009353 := bstep (se 2 (by rfl) ⟨2253507, by rfl⟩ : syracuseStep 6009353 = 4507015) B4507015
theorem B2814473 : Blo 1875639 2814473 := bstep (se 2 (by rfl) ⟨1055427, by rfl⟩ : syracuseStep 2814473 = 2110855) B2110855
theorem B2814503 : Blo 1875639 2814503 := bstep (se 1 (by rfl) ⟨2110877, by rfl⟩ : syracuseStep 2814503 = 4221755) B4221755
theorem B2814587 : Blo 1875639 2814587 := bstep (se 1 (by rfl) ⟨2110940, by rfl⟩ : syracuseStep 2814587 = 4221881) B4221881
theorem B3166843 : Blo 1875639 3166843 := bstep (se 1 (by rfl) ⟨2375132, by rfl⟩ : syracuseStep 3166843 = 4750265) B4750265
theorem B2814713 : Blo 1875639 2814713 := bstep (se 2 (by rfl) ⟨1055517, by rfl⟩ : syracuseStep 2814713 = 2111035) B2111035
theorem B2814815 : Blo 1875639 2814815 := bstep (se 1 (by rfl) ⟨2111111, by rfl⟩ : syracuseStep 2814815 = 4222223) B4222223
theorem B2814827 : Blo 1875639 2814827 := bstep (se 1 (by rfl) ⟨2111120, by rfl⟩ : syracuseStep 2814827 = 4222241) B4222241
theorem B7123895 : Blo 1875639 7123895 := bstep (se 1 (by rfl) ⟨5342921, by rfl⟩ : syracuseStep 7123895 = 10685843) B10685843
theorem B21369905 : Blo 1875639 21369905 := bstep (se 2 (by rfl) ⟨8013714, by rfl⟩ : syracuseStep 21369905 = 16027429) B16027429
theorem B18035779 : Blo 1875639 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B2815055 : Blo 1875639 2815055 := bstep (se 1 (by rfl) ⟨2111291, by rfl⟩ : syracuseStep 2815055 = 4222583) B4222583
theorem B2815175 : Blo 1875639 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B2815337 : Blo 1875639 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B2815415 : Blo 1875639 2815415 := bstep (se 1 (by rfl) ⟨2111561, by rfl⟩ : syracuseStep 2815415 = 4223123) B4223123
theorem B22255049 : Blo 1875639 22255049 := bstep (se 2 (by rfl) ⟨8345643, by rfl⟩ : syracuseStep 22255049 = 16691287) B16691287
theorem B2815451 : Blo 1875639 2815451 := bstep (se 1 (by rfl) ⟨2111588, by rfl⟩ : syracuseStep 2815451 = 4223177) B4223177
theorem B13522571 : Blo 1875639 13522571 := bstep (se 1 (by rfl) ⟨10141928, by rfl⟩ : syracuseStep 13522571 = 20283857) B20283857
theorem B4748939 : Blo 1875639 4748939 := bstep (se 1 (by rfl) ⟨3561704, by rfl⟩ : syracuseStep 4748939 = 7123409) B7123409
theorem B7124669 : Blo 1875639 7124669 := bstep (se 3 (by rfl) ⟨1335875, by rfl⟩ : syracuseStep 7124669 = 2671751) B2671751
theorem B24049345 : Blo 1875639 24049345 := bstep (se 2 (by rfl) ⟨9018504, by rfl⟩ : syracuseStep 24049345 = 18037009) B18037009
theorem B4749151 : Blo 1875639 4749151 := bstep (se 1 (by rfl) ⟨3561863, by rfl⟩ : syracuseStep 4749151 = 7123727) B7123727
theorem B7223201 : Blo 1875639 7223201 := bstep (se 2 (by rfl) ⟨2708700, by rfl⟩ : syracuseStep 7223201 = 5417401) B5417401
theorem B3610631 : Blo 1875639 3610631 := bstep (se 1 (by rfl) ⟨2707973, by rfl⟩ : syracuseStep 3610631 = 5415947) B5415947
theorem B2111611 : Blo 1875639 2111611 := bstep (se 1 (by rfl) ⟨1583708, by rfl⟩ : syracuseStep 2111611 = 3167417) B3167417
theorem B6330635 : Blo 1875639 6330635 := bstep (se 1 (by rfl) ⟨4747976, by rfl⟩ : syracuseStep 6330635 = 9495953) B9495953
theorem B534034781 : Blo 1875639 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B3561833 : Blo 1875639 3561833 := bstep (se 2 (by rfl) ⟨1335687, by rfl⟩ : syracuseStep 3561833 = 2671375) B2671375
theorem B7125353 : Blo 1875639 7125353 := bstep (se 2 (by rfl) ⟨2672007, by rfl⟩ : syracuseStep 7125353 = 5344015) B5344015
theorem B3381767 : Blo 1875639 3381767 := bstep (se 1 (by rfl) ⟨2536325, by rfl⟩ : syracuseStep 3381767 = 5072651) B5072651
theorem B6765065 : Blo 1875639 6765065 := bstep (se 2 (by rfl) ⟨2536899, by rfl⟩ : syracuseStep 6765065 = 5073799) B5073799
theorem B6330905 : Blo 1875639 6330905 := bstep (se 2 (by rfl) ⟨2374089, by rfl⟩ : syracuseStep 6330905 = 4748179) B4748179
theorem B61708877 : Blo 1875639 61708877 := bstep (se 3 (by rfl) ⟨11570414, by rfl⟩ : syracuseStep 61708877 = 23140829) B23140829
theorem B2374267 : Blo 1875639 2374267 := bstep (se 1 (by rfl) ⟨1780700, by rfl⟩ : syracuseStep 2374267 = 3561401) B3561401
theorem B3046087 : Blo 1875639 3046087 := bstep (se 1 (by rfl) ⟨2284565, by rfl⟩ : syracuseStep 3046087 = 4569131) B4569131
theorem B12024521 : Blo 1875639 12024521 := bstep (se 2 (by rfl) ⟨4509195, by rfl⟩ : syracuseStep 12024521 = 9018391) B9018391
theorem B4750073 : Blo 1875639 4750073 := bstep (se 2 (by rfl) ⟨1781277, by rfl⟩ : syracuseStep 4750073 = 3562555) B3562555
theorem B8674121 : Blo 1875639 8674121 := bstep (se 2 (by rfl) ⟨3252795, by rfl⟩ : syracuseStep 8674121 = 6505591) B6505591
theorem B65903453 : Blo 1875639 65903453 := bstep (se 3 (by rfl) ⟨12356897, by rfl⟩ : syracuseStep 65903453 = 24713795) B24713795
theorem B9501623 : Blo 1875639 9501623 := bstep (se 1 (by rfl) ⟨7126217, by rfl⟩ : syracuseStep 9501623 = 14252435) B14252435
theorem B10689509 : Blo 1875639 10689509 := bstep (se 4 (by rfl) ⟨1002141, by rfl⟩ : syracuseStep 10689509 = 2004283) B2004283
theorem B3046457 : Blo 1875639 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B3562859 : Blo 1875639 3562859 := bstep (se 1 (by rfl) ⟨2672144, by rfl⟩ : syracuseStep 3562859 = 5344289) B5344289
theorem B4750721 : Blo 1875639 4750721 := bstep (se 2 (by rfl) ⟨1781520, by rfl⟩ : syracuseStep 4750721 = 3563041) B3563041
theorem B9264527 : Blo 1875639 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B10689965 : Blo 1875639 10689965 := bstep (se 3 (by rfl) ⟨2004368, by rfl⟩ : syracuseStep 10689965 = 4008737) B4008737
theorem B6332039 : Blo 1875639 6332039 := bstep (se 1 (by rfl) ⟨4749029, by rfl⟩ : syracuseStep 6332039 = 9498059) B9498059
theorem B6332093 : Blo 1875639 6332093 := bstep (se 3 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 6332093 = 2374535) B2374535
theorem B1875655 : Blo 1875639 1875655 := bstep (se 1 (by rfl) ⟨1406741, by rfl⟩ : syracuseStep 1875655 = 2813483) B2813483
theorem B1875675 : Blo 1875639 1875675 := bstep (se 1 (by rfl) ⟨1406756, by rfl⟩ : syracuseStep 1875675 = 2813513) B2813513
theorem B9625337 : Blo 1875639 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B1875751 : Blo 1875639 1875751 := bstep (se 1 (by rfl) ⟨1406813, by rfl⟩ : syracuseStep 1875751 = 2813627) B2813627
theorem B1875791 : Blo 1875639 1875791 := bstep (se 1 (by rfl) ⟨1406843, by rfl⟩ : syracuseStep 1875791 = 2813687) B2813687
theorem B6332255 : Blo 1875639 6332255 := bstep (se 1 (by rfl) ⟨4749191, by rfl⟩ : syracuseStep 6332255 = 9498383) B9498383
theorem B1875807 : Blo 1875639 1875807 := bstep (se 1 (by rfl) ⟨1406855, by rfl⟩ : syracuseStep 1875807 = 2813711) B2813711
theorem B1875835 : Blo 1875639 1875835 := bstep (se 1 (by rfl) ⟨1406876, by rfl⟩ : syracuseStep 1875835 = 2813753) B2813753
theorem B1875887 : Blo 1875639 1875887 := bstep (se 1 (by rfl) ⟨1406915, by rfl⟩ : syracuseStep 1875887 = 2813831) B2813831
theorem B1875911 : Blo 1875639 1875911 := bstep (se 1 (by rfl) ⟨1406933, by rfl⟩ : syracuseStep 1875911 = 2813867) B2813867
theorem B1875931 : Blo 1875639 1875931 := bstep (se 1 (by rfl) ⟨1406948, by rfl⟩ : syracuseStep 1875931 = 2813897) B2813897
theorem B4751369 : Blo 1875639 4751369 := bstep (se 2 (by rfl) ⟨1781763, by rfl⟩ : syracuseStep 4751369 = 3563527) B3563527
theorem B8011801 : Blo 1875639 8011801 := bstep (se 2 (by rfl) ⟨3004425, by rfl⟩ : syracuseStep 8011801 = 6008851) B6008851
theorem B7127099 : Blo 1875639 7127099 := bstep (se 1 (by rfl) ⟨5345324, by rfl⟩ : syracuseStep 7127099 = 10690649) B10690649
theorem B74129527 : Blo 1875639 74129527 := bstep (se 1 (by rfl) ⟨55597145, by rfl⟩ : syracuseStep 74129527 = 111194291) B111194291
theorem B1876255 : Blo 1875639 1876255 := bstep (se 1 (by rfl) ⟨1407191, by rfl⟩ : syracuseStep 1876255 = 2814383) B2814383
theorem B2285855 : Blo 1875639 2285855 := bstep (se 1 (by rfl) ⟨1714391, by rfl⟩ : syracuseStep 2285855 = 3428783) B3428783
theorem B4006235 : Blo 1875639 4006235 := bstep (se 1 (by rfl) ⟨3004676, by rfl⟩ : syracuseStep 4006235 = 6009353) B6009353
theorem B1876315 : Blo 1875639 1876315 := bstep (se 1 (by rfl) ⟨1407236, by rfl⟩ : syracuseStep 1876315 = 2814473) B2814473
theorem B1876335 : Blo 1875639 1876335 := bstep (se 1 (by rfl) ⟨1407251, by rfl⟩ : syracuseStep 1876335 = 2814503) B2814503
theorem B1876391 : Blo 1875639 1876391 := bstep (se 1 (by rfl) ⟨1407293, by rfl⟩ : syracuseStep 1876391 = 2814587) B2814587
theorem B1876475 : Blo 1875639 1876475 := bstep (se 1 (by rfl) ⟨1407356, by rfl⟩ : syracuseStep 1876475 = 2814713) B2814713
theorem B152273429 : Blo 1875639 152273429 := bstep (se 6 (by rfl) ⟨3568908, by rfl⟩ : syracuseStep 152273429 = 7137817) B7137817
theorem B1876543 : Blo 1875639 1876543 := bstep (se 1 (by rfl) ⟨1407407, by rfl⟩ : syracuseStep 1876543 = 2814815) B2814815
theorem B1876551 : Blo 1875639 1876551 := bstep (se 1 (by rfl) ⟨1407413, by rfl⟩ : syracuseStep 1876551 = 2814827) B2814827
theorem B16253585 : Blo 1875639 16253585 := bstep (se 2 (by rfl) ⟨6095094, by rfl⟩ : syracuseStep 16253585 = 12190189) B12190189
theorem B14246603 : Blo 1875639 14246603 := bstep (se 1 (by rfl) ⟨10684952, by rfl⟩ : syracuseStep 14246603 = 21369905) B21369905
theorem B1876703 : Blo 1875639 1876703 := bstep (se 1 (by rfl) ⟨1407527, by rfl⟩ : syracuseStep 1876703 = 2815055) B2815055
theorem B1876783 : Blo 1875639 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B36569933 : Blo 1875639 36569933 := bstep (se 3 (by rfl) ⟨6856862, by rfl⟩ : syracuseStep 36569933 = 13713725) B13713725
theorem B1876891 : Blo 1875639 1876891 := bstep (se 1 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 1876891 = 2815337) B2815337
theorem B1876943 : Blo 1875639 1876943 := bstep (se 1 (by rfl) ⟨1407707, by rfl⟩ : syracuseStep 1876943 = 2815415) B2815415
theorem B14836699 : Blo 1875639 14836699 := bstep (se 1 (by rfl) ⟨11127524, by rfl⟩ : syracuseStep 14836699 = 22255049) B22255049
theorem B1876967 : Blo 1875639 1876967 := bstep (se 1 (by rfl) ⟨1407725, by rfl⟩ : syracuseStep 1876967 = 2815451) B2815451
theorem B34645411043 : Blo 1875639 34645411043 := bstep (se 1 (by rfl) ⟨25984058282, by rfl⟩ : syracuseStep 34645411043 = 51968116565) B51968116565
theorem B4220297 : Blo 1875639 4220297 := bstep (se 2 (by rfl) ⟨1582611, by rfl⟩ : syracuseStep 4220297 = 3165223) B3165223
theorem B4220423 : Blo 1875639 4220423 := bstep (se 1 (by rfl) ⟨3165317, by rfl⟩ : syracuseStep 4220423 = 6330635) B6330635
theorem B20285063 : Blo 1875639 20285063 := bstep (se 1 (by rfl) ⟨15213797, by rfl⟩ : syracuseStep 20285063 = 30427595) B30427595
theorem B2254511 : Blo 1875639 2254511 := bstep (se 1 (by rfl) ⟨1690883, by rfl⟩ : syracuseStep 2254511 = 3381767) B3381767
theorem B4220603 : Blo 1875639 4220603 := bstep (se 1 (by rfl) ⟨3165452, by rfl⟩ : syracuseStep 4220603 = 6330905) B6330905
theorem B48105251 : Blo 1875639 48105251 := bstep (se 1 (by rfl) ⟨36078938, by rfl⟩ : syracuseStep 48105251 = 72157877) B72157877
theorem B4220729 : Blo 1875639 4220729 := bstep (se 2 (by rfl) ⟨1582773, by rfl⟩ : syracuseStep 4220729 = 3165547) B3165547
theorem B43935635 : Blo 1875639 43935635 := bstep (se 1 (by rfl) ⟨32951726, by rfl⟩ : syracuseStep 43935635 = 65903453) B65903453
theorem B6334415 : Blo 1875639 6334415 := bstep (se 1 (by rfl) ⟨4750811, by rfl⟩ : syracuseStep 6334415 = 9501623) B9501623
theorem B32065793 : Blo 1875639 32065793 := bstep (se 2 (by rfl) ⟨12024672, by rfl⟩ : syracuseStep 32065793 = 24049345) B24049345
theorem B8014247 : Blo 1875639 8014247 := bstep (se 1 (by rfl) ⟨6010685, by rfl⟩ : syracuseStep 8014247 = 12021371) B12021371
theorem B281373101 : Blo 1875639 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B4221359 : Blo 1875639 4221359 := bstep (se 1 (by rfl) ⟨3166019, by rfl⟩ : syracuseStep 4221359 = 6332039) B6332039
theorem B4221395 : Blo 1875639 4221395 := bstep (se 1 (by rfl) ⟨3166046, by rfl⟩ : syracuseStep 4221395 = 6332093) B6332093
theorem B6416891 : Blo 1875639 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B4221503 : Blo 1875639 4221503 := bstep (se 1 (by rfl) ⟨3166127, by rfl⟩ : syracuseStep 4221503 = 6332255) B6332255
theorem B4221611 : Blo 1875639 4221611 := bstep (se 1 (by rfl) ⟨3166208, by rfl⟩ : syracuseStep 4221611 = 6332417) B6332417
theorem B12020471 : Blo 1875639 12020471 := bstep (se 1 (by rfl) ⟨9015353, by rfl⟩ : syracuseStep 12020471 = 18030707) B18030707
theorem B4508407 : Blo 1875639 4508407 := bstep (se 1 (by rfl) ⟨3381305, by rfl⟩ : syracuseStep 4508407 = 6762611) B6762611
theorem B9497411 : Blo 1875639 9497411 := bstep (se 1 (by rfl) ⟨7123058, by rfl⟩ : syracuseStep 9497411 = 14246117) B14246117
theorem B7220123 : Blo 1875639 7220123 := bstep (se 1 (by rfl) ⟨5415092, by rfl⟩ : syracuseStep 7220123 = 10830185) B10830185
theorem B9137069 : Blo 1875639 9137069 := bstep (se 3 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 9137069 = 3426401) B3426401
theorem B4222151 : Blo 1875639 4222151 := bstep (se 1 (by rfl) ⟨3166613, by rfl⟩ : syracuseStep 4222151 = 6333227) B6333227
theorem B4222331 : Blo 1875639 4222331 := bstep (se 1 (by rfl) ⟨3166748, by rfl⟩ : syracuseStep 4222331 = 6333497) B6333497
theorem B3165689 : Blo 1875639 3165689 := bstep (se 2 (by rfl) ⟨1187133, by rfl⟩ : syracuseStep 3165689 = 2374267) B2374267
theorem B4222457 : Blo 1875639 4222457 := bstep (se 2 (by rfl) ⟨1583421, by rfl⟩ : syracuseStep 4222457 = 3166843) B3166843
theorem B4222547 : Blo 1875639 4222547 := bstep (se 1 (by rfl) ⟨3166910, by rfl⟩ : syracuseStep 4222547 = 6333821) B6333821
theorem B9498221 : Blo 1875639 9498221 := bstep (se 3 (by rfl) ⟨1780916, by rfl⟩ : syracuseStep 9498221 = 3561833) B3561833
theorem B20565677 : Blo 1875639 20565677 := bstep (se 3 (by rfl) ⟨3856064, by rfl⟩ : syracuseStep 20565677 = 7712129) B7712129
theorem B2813675 : Blo 1875639 2813675 := bstep (se 1 (by rfl) ⟨2110256, by rfl⟩ : syracuseStep 2813675 = 4220513) B4220513
theorem B9015047 : Blo 1875639 9015047 := bstep (se 1 (by rfl) ⟨6761285, by rfl⟩ : syracuseStep 9015047 = 13522571) B13522571
theorem B3165959 : Blo 1875639 3165959 := bstep (se 1 (by rfl) ⟨2374469, by rfl⟩ : syracuseStep 3165959 = 4748939) B4748939
theorem B4222727 : Blo 1875639 4222727 := bstep (se 1 (by rfl) ⟨3167045, by rfl⟩ : syracuseStep 4222727 = 6334091) B6334091
theorem B2813903 : Blo 1875639 2813903 := bstep (se 1 (by rfl) ⟨2110427, by rfl⟩ : syracuseStep 2813903 = 4220855) B4220855
theorem B24047705 : Blo 1875639 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B2814299 : Blo 1875639 2814299 := bstep (se 1 (by rfl) ⟨2110724, by rfl⟩ : syracuseStep 2814299 = 4221449) B4221449
theorem B4510043 : Blo 1875639 4510043 := bstep (se 1 (by rfl) ⟨3382532, by rfl⟩ : syracuseStep 4510043 = 6765065) B6765065
theorem B4223339 : Blo 1875639 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B8016347 : Blo 1875639 8016347 := bstep (se 1 (by rfl) ⟨6012260, by rfl⟩ : syracuseStep 8016347 = 12024521) B12024521
theorem B3166715 : Blo 1875639 3166715 := bstep (se 1 (by rfl) ⟨2375036, by rfl⟩ : syracuseStep 3166715 = 4750073) B4750073
theorem B4223483 : Blo 1875639 4223483 := bstep (se 1 (by rfl) ⟨3167612, by rfl⟩ : syracuseStep 4223483 = 6335225) B6335225
theorem B2814527 : Blo 1875639 2814527 := bstep (se 1 (by rfl) ⟨2110895, by rfl⟩ : syracuseStep 2814527 = 4221791) B4221791
theorem B4747855 : Blo 1875639 4747855 := bstep (se 1 (by rfl) ⟨3560891, by rfl⟩ : syracuseStep 4747855 = 7121783) B7121783
theorem B2814647 : Blo 1875639 2814647 := bstep (se 1 (by rfl) ⟨2110985, by rfl⟩ : syracuseStep 2814647 = 4221971) B4221971
theorem B2814875 : Blo 1875639 2814875 := bstep (se 1 (by rfl) ⟨2111156, by rfl⟩ : syracuseStep 2814875 = 4222313) B4222313
theorem B3167147 : Blo 1875639 3167147 := bstep (se 1 (by rfl) ⟨2375360, by rfl⟩ : syracuseStep 3167147 = 4750721) B4750721
theorem B2536553 : Blo 1875639 2536553 := bstep (se 2 (by rfl) ⟨951207, by rfl⟩ : syracuseStep 2536553 = 1902415) B1902415
theorem B12022931 : Blo 1875639 12022931 := bstep (se 1 (by rfl) ⟨9017198, by rfl⟩ : syracuseStep 12022931 = 18034397) B18034397
theorem B4748503 : Blo 1875639 4748503 := bstep (se 1 (by rfl) ⟨3561377, by rfl⟩ : syracuseStep 4748503 = 7122755) B7122755
theorem B7124183 : Blo 1875639 7124183 := bstep (se 1 (by rfl) ⟨5343137, by rfl⟩ : syracuseStep 7124183 = 10686275) B10686275
theorem B2815271 : Blo 1875639 2815271 := bstep (se 1 (by rfl) ⟨2111453, by rfl⟩ : syracuseStep 2815271 = 4222907) B4222907
theorem B2815355 : Blo 1875639 2815355 := bstep (se 1 (by rfl) ⟨2111516, by rfl⟩ : syracuseStep 2815355 = 4223033) B4223033
theorem B8123885 : Blo 1875639 8123885 := bstep (se 3 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 8123885 = 3046457) B3046457
theorem B2815481 : Blo 1875639 2815481 := bstep (se 2 (by rfl) ⟨1055805, by rfl⟩ : syracuseStep 2815481 = 2111611) B2111611
theorem B4748807 : Blo 1875639 4748807 := bstep (se 1 (by rfl) ⟨3561605, by rfl⟩ : syracuseStep 4748807 = 7123211) B7123211
theorem B20280871 : Blo 1875639 20280871 := bstep (se 1 (by rfl) ⟨15210653, by rfl⟩ : syracuseStep 20280871 = 30421307) B30421307
theorem B2111071 : Blo 1875639 2111071 := bstep (se 1 (by rfl) ⟨1583303, by rfl⟩ : syracuseStep 2111071 = 3166607) B3166607
theorem B2815583 : Blo 1875639 2815583 := bstep (se 1 (by rfl) ⟨2111687, by rfl⟩ : syracuseStep 2815583 = 4223375) B4223375
theorem B9016967 : Blo 1875639 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B4749263 : Blo 1875639 4749263 := bstep (se 1 (by rfl) ⟨3561947, by rfl⟩ : syracuseStep 4749263 = 7123895) B7123895
theorem B12834895 : Blo 1875639 12834895 := bstep (se 1 (by rfl) ⟨9626171, by rfl⟩ : syracuseStep 12834895 = 19252343) B19252343
theorem B10688759 : Blo 1875639 10688759 := bstep (se 1 (by rfl) ⟨8016569, by rfl⟩ : syracuseStep 10688759 = 16033139) B16033139
theorem B4061449 : Blo 1875639 4061449 := bstep (se 2 (by rfl) ⟨1523043, by rfl⟩ : syracuseStep 4061449 = 3046087) B3046087
theorem B14244173 : Blo 1875639 14244173 := bstep (se 3 (by rfl) ⟨2670782, by rfl⟩ : syracuseStep 14244173 = 5341565) B5341565
theorem B4749779 : Blo 1875639 4749779 := bstep (se 1 (by rfl) ⟨3562334, by rfl⟩ : syracuseStep 4749779 = 7124669) B7124669
theorem B6330959 : Blo 1875639 6330959 := bstep (se 1 (by rfl) ⟨4748219, by rfl⟩ : syracuseStep 6330959 = 9496439) B9496439
theorem B4815467 : Blo 1875639 4815467 := bstep (se 1 (by rfl) ⟨3611600, by rfl⟩ : syracuseStep 4815467 = 7223201) B7223201
theorem B2407087 : Blo 1875639 2407087 := bstep (se 1 (by rfl) ⟨1805315, by rfl⟩ : syracuseStep 2407087 = 3610631) B3610631
theorem B3562319 : Blo 1875639 3562319 := bstep (se 1 (by rfl) ⟨2671739, by rfl⟩ : syracuseStep 3562319 = 5343479) B5343479
theorem B356023187 : Blo 1875639 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B4750235 : Blo 1875639 4750235 := bstep (se 1 (by rfl) ⟨3562676, by rfl⟩ : syracuseStep 4750235 = 7125353) B7125353
theorem B3562471 : Blo 1875639 3562471 := bstep (se 1 (by rfl) ⟨2671853, by rfl⟩ : syracuseStep 3562471 = 5343707) B5343707
theorem B41139251 : Blo 1875639 41139251 := bstep (se 1 (by rfl) ⟨30854438, by rfl⟩ : syracuseStep 41139251 = 61708877) B61708877
theorem B5782747 : Blo 1875639 5782747 := bstep (se 1 (by rfl) ⟨4337060, by rfl⟩ : syracuseStep 5782747 = 8674121) B8674121
theorem B7126339 : Blo 1875639 7126339 := bstep (se 1 (by rfl) ⟨5344754, by rfl⟩ : syracuseStep 7126339 = 10689509) B10689509
theorem B32488877 : Blo 1875639 32488877 := bstep (se 3 (by rfl) ⟨6091664, by rfl⟩ : syracuseStep 32488877 = 12183329) B12183329
theorem B2375239 : Blo 1875639 2375239 := bstep (se 1 (by rfl) ⟨1781429, by rfl⟩ : syracuseStep 2375239 = 3562859) B3562859
theorem B6176351 : Blo 1875639 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B8560243 : Blo 1875639 8560243 := bstep (se 1 (by rfl) ⟨6420182, by rfl⟩ : syracuseStep 8560243 = 12840365) B12840365
theorem B7126643 : Blo 1875639 7126643 := bstep (se 1 (by rfl) ⟨5344982, by rfl⟩ : syracuseStep 7126643 = 10689965) B10689965
theorem B1875679 : Blo 1875639 1875679 := bstep (se 1 (by rfl) ⟨1406759, by rfl⟩ : syracuseStep 1875679 = 2813519) B2813519
theorem B6332201 : Blo 1875639 6332201 := bstep (se 2 (by rfl) ⟨2374575, by rfl⟩ : syracuseStep 6332201 = 4749151) B4749151
theorem B7126825 : Blo 1875639 7126825 := bstep (se 2 (by rfl) ⟨2672559, by rfl⟩ : syracuseStep 7126825 = 5345119) B5345119
theorem B1875759 : Blo 1875639 1875759 := bstep (se 1 (by rfl) ⟨1406819, by rfl⟩ : syracuseStep 1875759 = 2813639) B2813639
theorem B1875867 : Blo 1875639 1875867 := bstep (se 1 (by rfl) ⟨1406900, by rfl⟩ : syracuseStep 1875867 = 2813801) B2813801
theorem B1875919 : Blo 1875639 1875919 := bstep (se 1 (by rfl) ⟨1406939, by rfl⟩ : syracuseStep 1875919 = 2813879) B2813879
theorem B1875943 : Blo 1875639 1875943 := bstep (se 1 (by rfl) ⟨1406957, by rfl⟩ : syracuseStep 1875943 = 2813915) B2813915
theorem B10682401 : Blo 1875639 10682401 := bstep (se 2 (by rfl) ⟨4005900, by rfl⟩ : syracuseStep 10682401 = 8011801) B8011801
theorem B4751399 : Blo 1875639 4751399 := bstep (se 1 (by rfl) ⟨3563549, by rfl⟩ : syracuseStep 4751399 = 7127099) B7127099
theorem B16031803 : Blo 1875639 16031803 := bstep (se 1 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 16031803 = 24047705) B24047705
theorem B17113193 : Blo 1875639 17113193 := bstep (se 2 (by rfl) ⟨6417447, by rfl⟩ : syracuseStep 17113193 = 12834895) B12834895
theorem B2670823 : Blo 1875639 2670823 := bstep (se 1 (by rfl) ⟨2003117, by rfl⟩ : syracuseStep 2670823 = 4006235) B4006235
theorem B1876199 : Blo 1875639 1876199 := bstep (se 1 (by rfl) ⟨1407149, by rfl⟩ : syracuseStep 1876199 = 2814299) B2814299
theorem B3006695 : Blo 1875639 3006695 := bstep (se 1 (by rfl) ⟨2255021, by rfl⟩ : syracuseStep 3006695 = 4510043) B4510043
theorem B5415265 : Blo 1875639 5415265 := bstep (se 2 (by rfl) ⟨2030724, by rfl⟩ : syracuseStep 5415265 = 4061449) B4061449
theorem B101515619 : Blo 1875639 101515619 := bstep (se 1 (by rfl) ⟨76136714, by rfl⟩ : syracuseStep 101515619 = 152273429) B152273429
theorem B1876351 : Blo 1875639 1876351 := bstep (se 1 (by rfl) ⟨1407263, by rfl⟩ : syracuseStep 1876351 = 2814527) B2814527
theorem B1876431 : Blo 1875639 1876431 := bstep (se 1 (by rfl) ⟨1407323, by rfl⟩ : syracuseStep 1876431 = 2814647) B2814647
theorem B24379955 : Blo 1875639 24379955 := bstep (se 1 (by rfl) ⟨18284966, by rfl⟩ : syracuseStep 24379955 = 36569933) B36569933
theorem B1876583 : Blo 1875639 1876583 := bstep (se 1 (by rfl) ⟨1407437, by rfl⟩ : syracuseStep 1876583 = 2814875) B2814875
theorem B1876847 : Blo 1875639 1876847 := bstep (se 1 (by rfl) ⟨1407635, by rfl⟩ : syracuseStep 1876847 = 2815271) B2815271
theorem B12837797 : Blo 1875639 12837797 := bstep (se 4 (by rfl) ⟨1203543, by rfl⟩ : syracuseStep 12837797 = 2407087) B2407087
theorem B1876903 : Blo 1875639 1876903 := bstep (se 1 (by rfl) ⟨1407677, by rfl⟩ : syracuseStep 1876903 = 2815355) B2815355
theorem B5415923 : Blo 1875639 5415923 := bstep (se 1 (by rfl) ⟨4061942, by rfl⟩ : syracuseStep 5415923 = 8123885) B8123885
theorem B1876987 : Blo 1875639 1876987 := bstep (se 1 (by rfl) ⟨1407740, by rfl⟩ : syracuseStep 1876987 = 2815481) B2815481
theorem B1877055 : Blo 1875639 1877055 := bstep (se 1 (by rfl) ⟨1407791, by rfl⟩ : syracuseStep 1877055 = 2815583) B2815583
theorem B9496115 : Blo 1875639 9496115 := bstep (se 1 (by rfl) ⟨7122086, by rfl⟩ : syracuseStep 9496115 = 14244173) B14244173
theorem B5342831 : Blo 1875639 5342831 := bstep (se 1 (by rfl) ⟨4007123, by rfl⟩ : syracuseStep 5342831 = 8014247) B8014247
theorem B187582067 : Blo 1875639 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B7710329 : Blo 1875639 7710329 := bstep (se 2 (by rfl) ⟨2891373, by rfl⟩ : syracuseStep 7710329 = 5782747) B5782747
theorem B4277927 : Blo 1875639 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B24045245 : Blo 1875639 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B4220639 : Blo 1875639 4220639 := bstep (se 1 (by rfl) ⟨3165479, by rfl⟩ : syracuseStep 4220639 = 6330959) B6330959
theorem B8013647 : Blo 1875639 8013647 := bstep (se 1 (by rfl) ⟨6010235, by rfl⟩ : syracuseStep 8013647 = 12020471) B12020471
theorem B237348791 : Blo 1875639 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B11413657 : Blo 1875639 11413657 := bstep (se 2 (by rfl) ⟨4280121, by rfl⟩ : syracuseStep 11413657 = 8560243) B8560243
theorem B4221467 : Blo 1875639 4221467 := bstep (se 1 (by rfl) ⟨3166100, by rfl⟩ : syracuseStep 4221467 = 6332201) B6332201
theorem B98839369 : Blo 1875639 98839369 := bstep (se 2 (by rfl) ⟨37064763, by rfl⟩ : syracuseStep 98839369 = 74129527) B74129527
theorem B5344231 : Blo 1875639 5344231 := bstep (se 1 (by rfl) ⟨4008173, by rfl⟩ : syracuseStep 5344231 = 8016347) B8016347
theorem B24382453 : Blo 1875639 24382453 := bstep (se 5 (by rfl) ⟨1142927, by rfl⟩ : syracuseStep 24382453 = 2285855) B2285855
theorem B9497735 : Blo 1875639 9497735 := bstep (se 1 (by rfl) ⟨7123301, by rfl⟩ : syracuseStep 9497735 = 14246603) B14246603
theorem B8015287 : Blo 1875639 8015287 := bstep (se 1 (by rfl) ⟨6011465, by rfl⟩ : syracuseStep 8015287 = 12022931) B12022931
theorem B2813531 : Blo 1875639 2813531 := bstep (se 1 (by rfl) ⟨2110148, by rfl⟩ : syracuseStep 2813531 = 4220297) B4220297
theorem B2813615 : Blo 1875639 2813615 := bstep (se 1 (by rfl) ⟨2110211, by rfl⟩ : syracuseStep 2813615 = 4220423) B4220423
theorem B3165871 : Blo 1875639 3165871 := bstep (se 1 (by rfl) ⟨2374403, by rfl⟩ : syracuseStep 3165871 = 4748807) B4748807
theorem B2813735 : Blo 1875639 2813735 := bstep (se 1 (by rfl) ⟨2110301, by rfl⟩ : syracuseStep 2813735 = 4220603) B4220603
theorem B2813819 : Blo 1875639 2813819 := bstep (se 1 (by rfl) ⟨2110364, by rfl⟩ : syracuseStep 2813819 = 4220729) B4220729
theorem B29290423 : Blo 1875639 29290423 := bstep (se 1 (by rfl) ⟨21967817, by rfl⟩ : syracuseStep 29290423 = 43935635) B43935635
theorem B3166175 : Blo 1875639 3166175 := bstep (se 1 (by rfl) ⟨2374631, by rfl⟩ : syracuseStep 3166175 = 4749263) B4749263
theorem B4222943 : Blo 1875639 4222943 := bstep (se 1 (by rfl) ⟨3167207, by rfl⟩ : syracuseStep 4222943 = 6334415) B6334415
theorem B21377195 : Blo 1875639 21377195 := bstep (se 1 (by rfl) ⟨16032896, by rfl⟩ : syracuseStep 21377195 = 32065793) B32065793
theorem B2814239 : Blo 1875639 2814239 := bstep (se 1 (by rfl) ⟨2110679, by rfl⟩ : syracuseStep 2814239 = 4221359) B4221359
theorem B2814263 : Blo 1875639 2814263 := bstep (se 1 (by rfl) ⟨2110697, by rfl⟩ : syracuseStep 2814263 = 4221395) B4221395
theorem B3166519 : Blo 1875639 3166519 := bstep (se 1 (by rfl) ⟨2374889, by rfl⟩ : syracuseStep 3166519 = 4749779) B4749779
theorem B2814335 : Blo 1875639 2814335 := bstep (se 1 (by rfl) ⟨2110751, by rfl⟩ : syracuseStep 2814335 = 4221503) B4221503
theorem B2814407 : Blo 1875639 2814407 := bstep (se 1 (by rfl) ⟨2110805, by rfl⟩ : syracuseStep 2814407 = 4221611) B4221611
theorem B54841805 : Blo 1875639 54841805 := bstep (se 3 (by rfl) ⟨10282838, by rfl⟩ : syracuseStep 54841805 = 20565677) B20565677
theorem B4813415 : Blo 1875639 4813415 := bstep (se 1 (by rfl) ⟨3610061, by rfl⟩ : syracuseStep 4813415 = 7220123) B7220123
theorem B3166823 : Blo 1875639 3166823 := bstep (se 1 (by rfl) ⟨2375117, by rfl⟩ : syracuseStep 3166823 = 4750235) B4750235
theorem B6091379 : Blo 1875639 6091379 := bstep (se 1 (by rfl) ⟨4568534, by rfl⟩ : syracuseStep 6091379 = 9137069) B9137069
theorem B3166985 : Blo 1875639 3166985 := bstep (se 2 (by rfl) ⟨1187619, by rfl⟩ : syracuseStep 3166985 = 2375239) B2375239
theorem B2814761 : Blo 1875639 2814761 := bstep (se 2 (by rfl) ⟨1055535, by rfl⟩ : syracuseStep 2814761 = 2111071) B2111071
theorem B2814767 : Blo 1875639 2814767 := bstep (se 1 (by rfl) ⟨2111075, by rfl⟩ : syracuseStep 2814767 = 4222151) B4222151
theorem B9499517 : Blo 1875639 9499517 := bstep (se 3 (by rfl) ⟨1781159, by rfl⟩ : syracuseStep 9499517 = 3562319) B3562319
theorem B2814887 : Blo 1875639 2814887 := bstep (se 1 (by rfl) ⟨2111165, by rfl⟩ : syracuseStep 2814887 = 4222331) B4222331
theorem B2110459 : Blo 1875639 2110459 := bstep (se 1 (by rfl) ⟨1582844, by rfl⟩ : syracuseStep 2110459 = 3165689) B3165689
theorem B2814971 : Blo 1875639 2814971 := bstep (se 1 (by rfl) ⟨2111228, by rfl⟩ : syracuseStep 2814971 = 4222457) B4222457
theorem B2815031 : Blo 1875639 2815031 := bstep (se 1 (by rfl) ⟨2111273, by rfl⟩ : syracuseStep 2815031 = 4222547) B4222547
theorem B4117567 : Blo 1875639 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B6010031 : Blo 1875639 6010031 := bstep (se 1 (by rfl) ⟨4507523, by rfl⟩ : syracuseStep 6010031 = 9015047) B9015047
theorem B2110639 : Blo 1875639 2110639 := bstep (se 1 (by rfl) ⟨1582979, by rfl⟩ : syracuseStep 2110639 = 3165959) B3165959
theorem B2815151 : Blo 1875639 2815151 := bstep (se 1 (by rfl) ⟨2111363, by rfl⟩ : syracuseStep 2815151 = 4222727) B4222727
theorem B3167579 : Blo 1875639 3167579 := bstep (se 1 (by rfl) ⟨2375684, by rfl⟩ : syracuseStep 3167579 = 4751369) B4751369
theorem B2815559 : Blo 1875639 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B6764141 : Blo 1875639 6764141 := bstep (se 3 (by rfl) ⟨1268276, by rfl⟩ : syracuseStep 6764141 = 2536553) B2536553
theorem B2111143 : Blo 1875639 2111143 := bstep (se 1 (by rfl) ⟨1583357, by rfl⟩ : syracuseStep 2111143 = 3166715) B3166715
theorem B2815655 : Blo 1875639 2815655 := bstep (se 1 (by rfl) ⟨2111741, by rfl⟩ : syracuseStep 2815655 = 4223483) B4223483
theorem B10835723 : Blo 1875639 10835723 := bstep (se 1 (by rfl) ⟨8126792, by rfl⟩ : syracuseStep 10835723 = 16253585) B16253585
theorem B2111431 : Blo 1875639 2111431 := bstep (se 1 (by rfl) ⟨1583573, by rfl⟩ : syracuseStep 2111431 = 3167147) B3167147
theorem B6330473 : Blo 1875639 6330473 := bstep (se 2 (by rfl) ⟨2373927, by rfl⟩ : syracuseStep 6330473 = 4747855) B4747855
theorem B4749455 : Blo 1875639 4749455 := bstep (se 1 (by rfl) ⟨3562091, by rfl⟩ : syracuseStep 4749455 = 7124183) B7124183
theorem B23096940695 : Blo 1875639 23096940695 := bstep (se 1 (by rfl) ⟨17322705521, by rfl⟩ : syracuseStep 23096940695 = 34645411043) B34645411043
theorem B6011209 : Blo 1875639 6011209 := bstep (se 2 (by rfl) ⟨2254203, by rfl⟩ : syracuseStep 6011209 = 4508407) B4508407
theorem B13523375 : Blo 1875639 13523375 := bstep (se 1 (by rfl) ⟨10142531, by rfl⟩ : syracuseStep 13523375 = 20285063) B20285063
theorem B32070167 : Blo 1875639 32070167 := bstep (se 1 (by rfl) ⟨24052625, by rfl⟩ : syracuseStep 32070167 = 48105251) B48105251
theorem B19782265 : Blo 1875639 19782265 := bstep (se 2 (by rfl) ⟨7418349, by rfl⟩ : syracuseStep 19782265 = 14836699) B14836699
theorem B4749961 : Blo 1875639 4749961 := bstep (se 2 (by rfl) ⟨1781235, by rfl⟩ : syracuseStep 4749961 = 3562471) B3562471
theorem B7125839 : Blo 1875639 7125839 := bstep (se 1 (by rfl) ⟨5344379, by rfl⟩ : syracuseStep 7125839 = 10688759) B10688759
theorem B6331337 : Blo 1875639 6331337 := bstep (se 2 (by rfl) ⟨2374251, by rfl⟩ : syracuseStep 6331337 = 4748503) B4748503
theorem B3210311 : Blo 1875639 3210311 := bstep (se 1 (by rfl) ⟨2407733, by rfl⟩ : syracuseStep 3210311 = 4815467) B4815467
theorem B9501785 : Blo 1875639 9501785 := bstep (se 2 (by rfl) ⟨3563169, by rfl⟩ : syracuseStep 9501785 = 7126339) B7126339
theorem B6012029 : Blo 1875639 6012029 := bstep (se 3 (by rfl) ⟨1127255, by rfl⟩ : syracuseStep 6012029 = 2254511) B2254511
theorem B6331607 : Blo 1875639 6331607 := bstep (se 1 (by rfl) ⟨4748705, by rfl⟩ : syracuseStep 6331607 = 9497411) B9497411
theorem B27426167 : Blo 1875639 27426167 := bstep (se 1 (by rfl) ⟨20569625, by rfl⟩ : syracuseStep 27426167 = 41139251) B41139251
theorem B27041161 : Blo 1875639 27041161 := bstep (se 2 (by rfl) ⟨10140435, by rfl⟩ : syracuseStep 27041161 = 20280871) B20280871
theorem B21659251 : Blo 1875639 21659251 := bstep (se 1 (by rfl) ⟨16244438, by rfl⟩ : syracuseStep 21659251 = 32488877) B32488877
theorem B9502433 : Blo 1875639 9502433 := bstep (se 2 (by rfl) ⟨3563412, by rfl⟩ : syracuseStep 9502433 = 7126825) B7126825
theorem B6332147 : Blo 1875639 6332147 := bstep (se 1 (by rfl) ⟨4749110, by rfl⟩ : syracuseStep 6332147 = 9498221) B9498221
theorem B4751095 : Blo 1875639 4751095 := bstep (se 1 (by rfl) ⟨3563321, by rfl⟩ : syracuseStep 4751095 = 7126643) B7126643
theorem B1875783 : Blo 1875639 1875783 := bstep (se 1 (by rfl) ⟨1406837, by rfl⟩ : syracuseStep 1875783 = 2813675) B2813675
theorem B1875935 : Blo 1875639 1875935 := bstep (se 1 (by rfl) ⟨1406951, by rfl⟩ : syracuseStep 1875935 = 2813903) B2813903
theorem B8560829 : Blo 1875639 8560829 := bstep (se 3 (by rfl) ⟨1605155, by rfl⟩ : syracuseStep 8560829 = 3210311) B3210311
theorem B1876159 : Blo 1875639 1876159 := bstep (se 1 (by rfl) ⟨1407119, by rfl⟩ : syracuseStep 1876159 = 2814239) B2814239
theorem B1876175 : Blo 1875639 1876175 := bstep (se 1 (by rfl) ⟨1407131, by rfl⟩ : syracuseStep 1876175 = 2814263) B2814263
theorem B1876223 : Blo 1875639 1876223 := bstep (se 1 (by rfl) ⟨1407167, by rfl⟩ : syracuseStep 1876223 = 2814335) B2814335
theorem B1876271 : Blo 1875639 1876271 := bstep (se 1 (by rfl) ⟨1407203, by rfl⟩ : syracuseStep 1876271 = 2814407) B2814407
theorem B36561203 : Blo 1875639 36561203 := bstep (se 1 (by rfl) ⟨27420902, by rfl⟩ : syracuseStep 36561203 = 54841805) B54841805
theorem B16032077 : Blo 1875639 16032077 := bstep (se 3 (by rfl) ⟨3006014, by rfl⟩ : syracuseStep 16032077 = 6012029) B6012029
theorem B16253303 : Blo 1875639 16253303 := bstep (se 1 (by rfl) ⟨12189977, by rfl⟩ : syracuseStep 16253303 = 24379955) B24379955
theorem B1876507 : Blo 1875639 1876507 := bstep (se 1 (by rfl) ⟨1407380, by rfl⟩ : syracuseStep 1876507 = 2814761) B2814761
theorem B1876511 : Blo 1875639 1876511 := bstep (se 1 (by rfl) ⟨1407383, by rfl⟩ : syracuseStep 1876511 = 2814767) B2814767
theorem B6333011 : Blo 1875639 6333011 := bstep (se 1 (by rfl) ⟨4749758, by rfl⟩ : syracuseStep 6333011 = 9499517) B9499517
theorem B1876591 : Blo 1875639 1876591 := bstep (se 1 (by rfl) ⟨1407443, by rfl⟩ : syracuseStep 1876591 = 2814887) B2814887
theorem B1876647 : Blo 1875639 1876647 := bstep (se 1 (by rfl) ⟨1407485, by rfl⟩ : syracuseStep 1876647 = 2814971) B2814971
theorem B1876687 : Blo 1875639 1876687 := bstep (se 1 (by rfl) ⟨1407515, by rfl⟩ : syracuseStep 1876687 = 2815031) B2815031
theorem B4006687 : Blo 1875639 4006687 := bstep (se 1 (by rfl) ⟨3005015, by rfl⟩ : syracuseStep 4006687 = 6010031) B6010031
theorem B1876767 : Blo 1875639 1876767 := bstep (se 1 (by rfl) ⟨1407575, by rfl⟩ : syracuseStep 1876767 = 2815151) B2815151
theorem B6333281 : Blo 1875639 6333281 := bstep (se 2 (by rfl) ⟨2374980, by rfl⟩ : syracuseStep 6333281 = 4749961) B4749961
theorem B1877039 : Blo 1875639 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B131785825 : Blo 1875639 131785825 := bstep (se 2 (by rfl) ⟨49419684, by rfl⟩ : syracuseStep 131785825 = 98839369) B98839369
theorem B2851951 : Blo 1875639 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B1877103 : Blo 1875639 1877103 := bstep (se 1 (by rfl) ⟨1407827, by rfl⟩ : syracuseStep 1877103 = 2815655) B2815655
theorem B36062333 : Blo 1875639 36062333 := bstep (se 3 (by rfl) ⟨6761687, by rfl⟩ : syracuseStep 36062333 = 13523375) B13523375
theorem B5342431 : Blo 1875639 5342431 := bstep (se 1 (by rfl) ⟨4006823, by rfl⟩ : syracuseStep 5342431 = 8013647) B8013647
theorem B4220315 : Blo 1875639 4220315 := bstep (se 1 (by rfl) ⟨3165236, by rfl⟩ : syracuseStep 4220315 = 6330473) B6330473
theorem B5490089 : Blo 1875639 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B36054881 : Blo 1875639 36054881 := bstep (se 2 (by rfl) ⟨13520580, by rfl⟩ : syracuseStep 36054881 = 27041161) B27041161
theorem B4220891 : Blo 1875639 4220891 := bstep (se 1 (by rfl) ⟨3165668, by rfl⟩ : syracuseStep 4220891 = 6331337) B6331337
theorem B6334523 : Blo 1875639 6334523 := bstep (se 1 (by rfl) ⟨4750892, by rfl⟩ : syracuseStep 6334523 = 9501785) B9501785
theorem B4221071 : Blo 1875639 4221071 := bstep (se 1 (by rfl) ⟨3165803, by rfl⟩ : syracuseStep 4221071 = 6331607) B6331607
theorem B28879001 : Blo 1875639 28879001 := bstep (se 2 (by rfl) ⟨10829625, by rfl⟩ : syracuseStep 28879001 = 21659251) B21659251
theorem B4221161 : Blo 1875639 4221161 := bstep (se 2 (by rfl) ⟨1582935, by rfl⟩ : syracuseStep 4221161 = 3165871) B3165871
theorem B6334793 : Blo 1875639 6334793 := bstep (se 2 (by rfl) ⟨2375547, by rfl⟩ : syracuseStep 6334793 = 4751095) B4751095
theorem B6334955 : Blo 1875639 6334955 := bstep (se 1 (by rfl) ⟨4751216, by rfl⟩ : syracuseStep 6334955 = 9502433) B9502433
theorem B4221431 : Blo 1875639 4221431 := bstep (se 1 (by rfl) ⟨3166073, by rfl⟩ : syracuseStep 4221431 = 6332147) B6332147
theorem B39053897 : Blo 1875639 39053897 := bstep (se 2 (by rfl) ⟨14645211, by rfl⟩ : syracuseStep 39053897 = 29290423) B29290423
theorem B21375737 : Blo 1875639 21375737 := bstep (se 2 (by rfl) ⟨8015901, by rfl⟩ : syracuseStep 21375737 = 16031803) B16031803
theorem B67677079 : Blo 1875639 67677079 := bstep (se 1 (by rfl) ⟨50757809, by rfl⟩ : syracuseStep 67677079 = 101515619) B101515619
theorem B4222025 : Blo 1875639 4222025 := bstep (se 2 (by rfl) ⟨1583259, by rfl⟩ : syracuseStep 4222025 = 3166519) B3166519
theorem B8014945 : Blo 1875639 8014945 := bstep (se 2 (by rfl) ⟨3005604, by rfl⟩ : syracuseStep 8014945 = 6011209) B6011209
theorem B7220353 : Blo 1875639 7220353 := bstep (se 2 (by rfl) ⟨2707632, by rfl⟩ : syracuseStep 7220353 = 5415265) B5415265
theorem B4509427 : Blo 1875639 4509427 := bstep (se 1 (by rfl) ⟨3382070, by rfl⟩ : syracuseStep 4509427 = 6764141) B6764141
theorem B125054711 : Blo 1875639 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B2813759 : Blo 1875639 2813759 := bstep (se 1 (by rfl) ⟨2110319, by rfl⟩ : syracuseStep 2813759 = 4220639) B4220639
theorem B158232527 : Blo 1875639 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B32509937 : Blo 1875639 32509937 := bstep (se 2 (by rfl) ⟨12191226, by rfl⟩ : syracuseStep 32509937 = 24382453) B24382453
theorem B2813945 : Blo 1875639 2813945 := bstep (se 2 (by rfl) ⟨1055229, by rfl⟩ : syracuseStep 2813945 = 2110459) B2110459
theorem B3166303 : Blo 1875639 3166303 := bstep (se 1 (by rfl) ⟨2374727, by rfl⟩ : syracuseStep 3166303 = 4749455) B4749455
theorem B2814185 : Blo 1875639 2814185 := bstep (se 2 (by rfl) ⟨1055319, by rfl⟩ : syracuseStep 2814185 = 2110639) B2110639
theorem B2814311 : Blo 1875639 2814311 := bstep (se 1 (by rfl) ⟨2110733, by rfl⟩ : syracuseStep 2814311 = 4221467) B4221467
theorem B10687049 : Blo 1875639 10687049 := bstep (se 2 (by rfl) ⟨4007643, by rfl⟩ : syracuseStep 10687049 = 8015287) B8015287
theorem B2814857 : Blo 1875639 2814857 := bstep (se 2 (by rfl) ⟨1055571, by rfl⟩ : syracuseStep 2814857 = 2111143) B2111143
theorem B2815241 : Blo 1875639 2815241 := bstep (se 2 (by rfl) ⟨1055715, by rfl⟩ : syracuseStep 2815241 = 2111431) B2111431
theorem B2110783 : Blo 1875639 2110783 := bstep (se 1 (by rfl) ⟨1583087, by rfl⟩ : syracuseStep 2110783 = 3166175) B3166175
theorem B2815295 : Blo 1875639 2815295 := bstep (se 1 (by rfl) ⟨2111471, by rfl⟩ : syracuseStep 2815295 = 4222943) B4222943
theorem B3167599 : Blo 1875639 3167599 := bstep (se 1 (by rfl) ⟨2375699, by rfl⟩ : syracuseStep 3167599 = 4751399) B4751399
theorem B14243201 : Blo 1875639 14243201 := bstep (se 2 (by rfl) ⟨5341200, by rfl⟩ : syracuseStep 14243201 = 10682401) B10682401
theorem B11408795 : Blo 1875639 11408795 := bstep (se 1 (by rfl) ⟨8556596, by rfl⟩ : syracuseStep 11408795 = 17113193) B17113193
theorem B14251463 : Blo 1875639 14251463 := bstep (se 1 (by rfl) ⟨10688597, by rfl⟩ : syracuseStep 14251463 = 21377195) B21377195
theorem B2004463 : Blo 1875639 2004463 := bstep (se 1 (by rfl) ⟨1503347, by rfl⟩ : syracuseStep 2004463 = 3006695) B3006695
theorem B15218209 : Blo 1875639 15218209 := bstep (se 2 (by rfl) ⟨5706828, by rfl⟩ : syracuseStep 15218209 = 11413657) B11413657
theorem B3561097 : Blo 1875639 3561097 := bstep (se 2 (by rfl) ⟨1335411, by rfl⟩ : syracuseStep 3561097 = 2670823) B2670823
theorem B3208943 : Blo 1875639 3208943 := bstep (se 1 (by rfl) ⟨2406707, by rfl⟩ : syracuseStep 3208943 = 4813415) B4813415
theorem B2111215 : Blo 1875639 2111215 := bstep (se 1 (by rfl) ⟨1583411, by rfl⟩ : syracuseStep 2111215 = 3166823) B3166823
theorem B4060919 : Blo 1875639 4060919 := bstep (se 1 (by rfl) ⟨3045689, by rfl⟩ : syracuseStep 4060919 = 6091379) B6091379
theorem B2111323 : Blo 1875639 2111323 := bstep (se 1 (by rfl) ⟨1583492, by rfl⟩ : syracuseStep 2111323 = 3166985) B3166985
theorem B8558531 : Blo 1875639 8558531 := bstep (se 1 (by rfl) ⟨6418898, by rfl⟩ : syracuseStep 8558531 = 12837797) B12837797
theorem B26376353 : Blo 1875639 26376353 := bstep (se 2 (by rfl) ⟨9891132, by rfl⟩ : syracuseStep 26376353 = 19782265) B19782265
theorem B2111719 : Blo 1875639 2111719 := bstep (se 1 (by rfl) ⟨1583789, by rfl⟩ : syracuseStep 2111719 = 3167579) B3167579
theorem B6330743 : Blo 1875639 6330743 := bstep (se 1 (by rfl) ⟨4748057, by rfl⟩ : syracuseStep 6330743 = 9496115) B9496115
theorem B3561887 : Blo 1875639 3561887 := bstep (se 1 (by rfl) ⟨2671415, by rfl⟩ : syracuseStep 3561887 = 5342831) B5342831
theorem B16030163 : Blo 1875639 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B7223815 : Blo 1875639 7223815 := bstep (se 1 (by rfl) ⟨5417861, by rfl⟩ : syracuseStep 7223815 = 10835723) B10835723
theorem B7125641 : Blo 1875639 7125641 := bstep (se 2 (by rfl) ⟨2672115, by rfl⟩ : syracuseStep 7125641 = 5344231) B5344231
theorem B15397960463 : Blo 1875639 15397960463 := bstep (se 1 (by rfl) ⟨11548470347, by rfl⟩ : syracuseStep 15397960463 = 23096940695) B23096940695
theorem B20560877 : Blo 1875639 20560877 := bstep (se 3 (by rfl) ⟨3855164, by rfl⟩ : syracuseStep 20560877 = 7710329) B7710329
theorem B21380111 : Blo 1875639 21380111 := bstep (se 1 (by rfl) ⟨16035083, by rfl⟩ : syracuseStep 21380111 = 32070167) B32070167
theorem B4750559 : Blo 1875639 4750559 := bstep (se 1 (by rfl) ⟨3562919, by rfl⟩ : syracuseStep 4750559 = 7125839) B7125839
theorem B6331823 : Blo 1875639 6331823 := bstep (se 1 (by rfl) ⟨4748867, by rfl⟩ : syracuseStep 6331823 = 9497735) B9497735
theorem B18284111 : Blo 1875639 18284111 := bstep (se 1 (by rfl) ⟨13713083, by rfl⟩ : syracuseStep 18284111 = 27426167) B27426167
theorem B1875687 : Blo 1875639 1875687 := bstep (se 1 (by rfl) ⟨1406765, by rfl⟩ : syracuseStep 1875687 = 2813531) B2813531
theorem B1875743 : Blo 1875639 1875743 := bstep (se 1 (by rfl) ⟨1406807, by rfl⟩ : syracuseStep 1875743 = 2813615) B2813615
theorem B1875823 : Blo 1875639 1875823 := bstep (se 1 (by rfl) ⟨1406867, by rfl⟩ : syracuseStep 1875823 = 2813735) B2813735
theorem B1875879 : Blo 1875639 1875879 := bstep (se 1 (by rfl) ⟨1406909, by rfl⟩ : syracuseStep 1875879 = 2813819) B2813819
theorem B14442461 : Blo 1875639 14442461 := bstep (se 3 (by rfl) ⟨2707961, by rfl⟩ : syracuseStep 14442461 = 5415923) B5415923
theorem B1876123 : Blo 1875639 1876123 := bstep (se 1 (by rfl) ⟨1407092, by rfl⟩ : syracuseStep 1876123 = 2814185) B2814185
theorem B1876207 : Blo 1875639 1876207 := bstep (se 1 (by rfl) ⟨1407155, by rfl⟩ : syracuseStep 1876207 = 2814311) B2814311
theorem B1876571 : Blo 1875639 1876571 := bstep (se 1 (by rfl) ⟨1407428, by rfl⟩ : syracuseStep 1876571 = 2814857) B2814857
theorem B1876827 : Blo 1875639 1876827 := bstep (se 1 (by rfl) ⟨1407620, by rfl⟩ : syracuseStep 1876827 = 2815241) B2815241
theorem B1876863 : Blo 1875639 1876863 := bstep (se 1 (by rfl) ⟨1407647, by rfl⟩ : syracuseStep 1876863 = 2815295) B2815295
theorem B9495467 : Blo 1875639 9495467 := bstep (se 1 (by rfl) ⟨7121600, by rfl⟩ : syracuseStep 9495467 = 14243201) B14243201
theorem B5342249 : Blo 1875639 5342249 := bstep (se 2 (by rfl) ⟨2003343, by rfl⟩ : syracuseStep 5342249 = 4006687) B4006687
theorem B2139295 : Blo 1875639 2139295 := bstep (se 1 (by rfl) ⟨1604471, by rfl⟩ : syracuseStep 2139295 = 3208943) B3208943
theorem B90236105 : Blo 1875639 90236105 := bstep (se 2 (by rfl) ⟨33838539, by rfl⟩ : syracuseStep 90236105 = 67677079) B67677079
theorem B24036587 : Blo 1875639 24036587 := bstep (se 1 (by rfl) ⟨18027440, by rfl⟩ : syracuseStep 24036587 = 36054881) B36054881
theorem B19252667 : Blo 1875639 19252667 := bstep (se 1 (by rfl) ⟨14439500, by rfl⟩ : syracuseStep 19252667 = 28879001) B28879001
theorem B3802601 : Blo 1875639 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B9627137 : Blo 1875639 9627137 := bstep (se 2 (by rfl) ⟨3610176, by rfl⟩ : syracuseStep 9627137 = 7220353) B7220353
theorem B4220495 : Blo 1875639 4220495 := bstep (se 1 (by rfl) ⟨3165371, by rfl⟩ : syracuseStep 4220495 = 6330743) B6330743
theorem B26035931 : Blo 1875639 26035931 := bstep (se 1 (by rfl) ⟨19526948, by rfl⟩ : syracuseStep 26035931 = 39053897) B39053897
theorem B10265306975 : Blo 1875639 10265306975 := bstep (se 1 (by rfl) ⟨7698980231, by rfl⟩ : syracuseStep 10265306975 = 15397960463) B15397960463
theorem B2672617 : Blo 1875639 2672617 := bstep (se 2 (by rfl) ⟨1002231, by rfl⟩ : syracuseStep 2672617 = 2004463) B2004463
theorem B13707251 : Blo 1875639 13707251 := bstep (se 1 (by rfl) ⟨10280438, by rfl⟩ : syracuseStep 13707251 = 20560877) B20560877
theorem B4221215 : Blo 1875639 4221215 := bstep (se 1 (by rfl) ⟨3165911, by rfl⟩ : syracuseStep 4221215 = 6331823) B6331823
theorem B9628307 : Blo 1875639 9628307 := bstep (se 1 (by rfl) ⟨7221230, by rfl⟩ : syracuseStep 9628307 = 14442461) B14442461
theorem B4221737 : Blo 1875639 4221737 := bstep (se 2 (by rfl) ⟨1583151, by rfl⟩ : syracuseStep 4221737 = 3166303) B3166303
theorem B24374135 : Blo 1875639 24374135 := bstep (se 1 (by rfl) ⟨18280601, by rfl⟩ : syracuseStep 24374135 = 36561203) B36561203
theorem B4222007 : Blo 1875639 4222007 := bstep (se 1 (by rfl) ⟨3166505, by rfl⟩ : syracuseStep 4222007 = 6333011) B6333011
theorem B4222187 : Blo 1875639 4222187 := bstep (se 1 (by rfl) ⟨3166640, by rfl⟩ : syracuseStep 4222187 = 6333281) B6333281
theorem B2813543 : Blo 1875639 2813543 := bstep (se 1 (by rfl) ⟨2110157, by rfl⟩ : syracuseStep 2813543 = 4220315) B4220315
theorem B7605863 : Blo 1875639 7605863 := bstep (se 1 (by rfl) ⟨5704397, by rfl⟩ : syracuseStep 7605863 = 11408795) B11408795
theorem B5705687 : Blo 1875639 5705687 := bstep (se 1 (by rfl) ⟨4279265, by rfl⟩ : syracuseStep 5705687 = 8558531) B8558531
theorem B2813927 : Blo 1875639 2813927 := bstep (se 1 (by rfl) ⟨2110445, by rfl⟩ : syracuseStep 2813927 = 4220891) B4220891
theorem B4223015 : Blo 1875639 4223015 := bstep (se 1 (by rfl) ⟨3167261, by rfl⟩ : syracuseStep 4223015 = 6334523) B6334523
theorem B2814047 : Blo 1875639 2814047 := bstep (se 1 (by rfl) ⟨2110535, by rfl⟩ : syracuseStep 2814047 = 4221071) B4221071
theorem B17584235 : Blo 1875639 17584235 := bstep (se 1 (by rfl) ⟨13188176, by rfl⟩ : syracuseStep 17584235 = 26376353) B26376353
theorem B10686593 : Blo 1875639 10686593 := bstep (se 2 (by rfl) ⟨4007472, by rfl⟩ : syracuseStep 10686593 = 8014945) B8014945
theorem B175714433 : Blo 1875639 175714433 := bstep (se 2 (by rfl) ⟨65892912, by rfl⟩ : syracuseStep 175714433 = 131785825) B131785825
theorem B2814107 : Blo 1875639 2814107 := bstep (se 1 (by rfl) ⟨2110580, by rfl⟩ : syracuseStep 2814107 = 4221161) B4221161
theorem B4223195 : Blo 1875639 4223195 := bstep (se 1 (by rfl) ⟨3167396, by rfl⟩ : syracuseStep 4223195 = 6334793) B6334793
theorem B7123241 : Blo 1875639 7123241 := bstep (se 2 (by rfl) ⟨2671215, by rfl⟩ : syracuseStep 7123241 = 5342431) B5342431
theorem B10686775 : Blo 1875639 10686775 := bstep (se 1 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 10686775 = 16030163) B16030163
theorem B4223303 : Blo 1875639 4223303 := bstep (se 1 (by rfl) ⟨3167477, by rfl⟩ : syracuseStep 4223303 = 6334955) B6334955
theorem B2814287 : Blo 1875639 2814287 := bstep (se 1 (by rfl) ⟨2110715, by rfl⟩ : syracuseStep 2814287 = 4221431) B4221431
theorem B2814377 : Blo 1875639 2814377 := bstep (se 2 (by rfl) ⟨1055391, by rfl⟩ : syracuseStep 2814377 = 2110783) B2110783
theorem B4223465 : Blo 1875639 4223465 := bstep (se 2 (by rfl) ⟨1583799, by rfl⟩ : syracuseStep 4223465 = 3167599) B3167599
theorem B14250491 : Blo 1875639 14250491 := bstep (se 1 (by rfl) ⟨10687868, by rfl⟩ : syracuseStep 14250491 = 21375737) B21375737
theorem B2814683 : Blo 1875639 2814683 := bstep (se 1 (by rfl) ⟨2111012, by rfl⟩ : syracuseStep 2814683 = 4222025) B4222025
theorem B3167039 : Blo 1875639 3167039 := bstep (se 1 (by rfl) ⟨2375279, by rfl⟩ : syracuseStep 3167039 = 4750559) B4750559
theorem B4748129 : Blo 1875639 4748129 := bstep (se 2 (by rfl) ⟨1780548, by rfl⟩ : syracuseStep 4748129 = 3561097) B3561097
theorem B2814953 : Blo 1875639 2814953 := bstep (se 2 (by rfl) ⟨1055607, by rfl⟩ : syracuseStep 2814953 = 2111215) B2111215
theorem B2815097 : Blo 1875639 2815097 := bstep (se 2 (by rfl) ⟨1055661, by rfl⟩ : syracuseStep 2815097 = 2111323) B2111323
theorem B21673291 : Blo 1875639 21673291 := bstep (se 1 (by rfl) ⟨16254968, by rfl⟩ : syracuseStep 21673291 = 32509937) B32509937
theorem B10688051 : Blo 1875639 10688051 := bstep (se 1 (by rfl) ⟨8016038, by rfl⟩ : syracuseStep 10688051 = 16032077) B16032077
theorem B2815625 : Blo 1875639 2815625 := bstep (se 2 (by rfl) ⟨1055859, by rfl⟩ : syracuseStep 2815625 = 2111719) B2111719
theorem B7124699 : Blo 1875639 7124699 := bstep (se 1 (by rfl) ⟨5343524, by rfl⟩ : syracuseStep 7124699 = 10687049) B10687049
theorem B22828877 : Blo 1875639 22828877 := bstep (se 3 (by rfl) ⟨4280414, by rfl⟩ : syracuseStep 22828877 = 8560829) B8560829
theorem B9631753 : Blo 1875639 9631753 := bstep (se 2 (by rfl) ⟨3611907, by rfl⟩ : syracuseStep 9631753 = 7223815) B7223815
theorem B24041555 : Blo 1875639 24041555 := bstep (se 1 (by rfl) ⟨18031166, by rfl⟩ : syracuseStep 24041555 = 36062333) B36062333
theorem B3660059 : Blo 1875639 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B9500975 : Blo 1875639 9500975 := bstep (se 1 (by rfl) ⟨7125731, by rfl⟩ : syracuseStep 9500975 = 14251463) B14251463
theorem B43342141 : Blo 1875639 43342141 := bstep (se 3 (by rfl) ⟨8126651, by rfl⟩ : syracuseStep 43342141 = 16253303) B16253303
theorem B2374591 : Blo 1875639 2374591 := bstep (se 1 (by rfl) ⟨1780943, by rfl⟩ : syracuseStep 2374591 = 3561887) B3561887
theorem B4750427 : Blo 1875639 4750427 := bstep (se 1 (by rfl) ⟨3562820, by rfl⟩ : syracuseStep 4750427 = 7125641) B7125641
theorem B10829117 : Blo 1875639 10829117 := bstep (se 3 (by rfl) ⟨2030459, by rfl⟩ : syracuseStep 10829117 = 4060919) B4060919
theorem B14253407 : Blo 1875639 14253407 := bstep (se 1 (by rfl) ⟨10690055, by rfl⟩ : syracuseStep 14253407 = 21380111) B21380111
theorem B20290945 : Blo 1875639 20290945 := bstep (se 2 (by rfl) ⟨7609104, by rfl⟩ : syracuseStep 20290945 = 15218209) B15218209
theorem B6012569 : Blo 1875639 6012569 := bstep (se 2 (by rfl) ⟨2254713, by rfl⟩ : syracuseStep 6012569 = 4509427) B4509427
theorem B12189407 : Blo 1875639 12189407 := bstep (se 1 (by rfl) ⟨9142055, by rfl⟩ : syracuseStep 12189407 = 18284111) B18284111
theorem B83369807 : Blo 1875639 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B1875839 : Blo 1875639 1875839 := bstep (se 1 (by rfl) ⟨1406879, by rfl⟩ : syracuseStep 1875839 = 2813759) B2813759
theorem B105488351 : Blo 1875639 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B1875963 : Blo 1875639 1875963 := bstep (se 1 (by rfl) ⟨1406972, by rfl⟩ : syracuseStep 1875963 = 2813945) B2813945
theorem B1876031 : Blo 1875639 1876031 := bstep (se 1 (by rfl) ⟨1407023, by rfl⟩ : syracuseStep 1876031 = 2814047) B2814047
theorem B11722823 : Blo 1875639 11722823 := bstep (se 1 (by rfl) ⟨8792117, by rfl⟩ : syracuseStep 11722823 = 17584235) B17584235
theorem B1876071 : Blo 1875639 1876071 := bstep (se 1 (by rfl) ⟨1407053, by rfl⟩ : syracuseStep 1876071 = 2814107) B2814107
theorem B1876191 : Blo 1875639 1876191 := bstep (se 1 (by rfl) ⟨1407143, by rfl⟩ : syracuseStep 1876191 = 2814287) B2814287
theorem B1876251 : Blo 1875639 1876251 := bstep (se 1 (by rfl) ⟨1407188, by rfl⟩ : syracuseStep 1876251 = 2814377) B2814377
theorem B1876455 : Blo 1875639 1876455 := bstep (se 1 (by rfl) ⟨1407341, by rfl⟩ : syracuseStep 1876455 = 2814683) B2814683
theorem B1876635 : Blo 1875639 1876635 := bstep (se 1 (by rfl) ⟨1407476, by rfl⟩ : syracuseStep 1876635 = 2814953) B2814953
theorem B1876731 : Blo 1875639 1876731 := bstep (se 1 (by rfl) ⟨1407548, by rfl⟩ : syracuseStep 1876731 = 2815097) B2815097
theorem B16024391 : Blo 1875639 16024391 := bstep (se 1 (by rfl) ⟨12018293, by rfl⟩ : syracuseStep 16024391 = 24036587) B24036587
theorem B1877083 : Blo 1875639 1877083 := bstep (se 1 (by rfl) ⟨1407812, by rfl⟩ : syracuseStep 1877083 = 2815625) B2815625
theorem B6333983 : Blo 1875639 6333983 := bstep (se 1 (by rfl) ⟨4750487, by rfl⟩ : syracuseStep 6333983 = 9500975) B9500975
theorem B2852393 : Blo 1875639 2852393 := bstep (se 2 (by rfl) ⟨1069647, by rfl⟩ : syracuseStep 2852393 = 2139295) B2139295
theorem B69429149 : Blo 1875639 69429149 := bstep (se 3 (by rfl) ⟨13017965, by rfl⟩ : syracuseStep 69429149 = 26035931) B26035931
theorem B7219411 : Blo 1875639 7219411 := bstep (se 1 (by rfl) ⟨5414558, by rfl⟩ : syracuseStep 7219411 = 10829117) B10829117
theorem B4008379 : Blo 1875639 4008379 := bstep (se 1 (by rfl) ⟨3006284, by rfl⟩ : syracuseStep 4008379 = 6012569) B6012569
theorem B15215165 : Blo 1875639 15215165 := bstep (se 3 (by rfl) ⟨2852843, by rfl⟩ : syracuseStep 15215165 = 5705687) B5705687
theorem B14249033 : Blo 1875639 14249033 := bstep (se 2 (by rfl) ⟨5343387, by rfl⟩ : syracuseStep 14249033 = 10686775) B10686775
theorem B57789521 : Blo 1875639 57789521 := bstep (se 2 (by rfl) ⟨21671070, by rfl⟩ : syracuseStep 57789521 = 43342141) B43342141
theorem B3165419 : Blo 1875639 3165419 := bstep (se 1 (by rfl) ⟨2374064, by rfl⟩ : syracuseStep 3165419 = 4748129) B4748129
theorem B60157403 : Blo 1875639 60157403 := bstep (se 1 (by rfl) ⟨45118052, by rfl⟩ : syracuseStep 60157403 = 90236105) B90236105
theorem B2535067 : Blo 1875639 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B6418091 : Blo 1875639 6418091 := bstep (se 1 (by rfl) ⟨4813568, by rfl⟩ : syracuseStep 6418091 = 9627137) B9627137
theorem B2813663 : Blo 1875639 2813663 := bstep (se 1 (by rfl) ⟨2110247, by rfl⟩ : syracuseStep 2813663 = 4220495) B4220495
theorem B3166121 : Blo 1875639 3166121 := bstep (se 2 (by rfl) ⟨1187295, by rfl⟩ : syracuseStep 3166121 = 2374591) B2374591
theorem B9138167 : Blo 1875639 9138167 := bstep (se 1 (by rfl) ⟨6853625, by rfl⟩ : syracuseStep 9138167 = 13707251) B13707251
theorem B16027703 : Blo 1875639 16027703 := bstep (se 1 (by rfl) ⟨12020777, by rfl⟩ : syracuseStep 16027703 = 24041555) B24041555
theorem B2814143 : Blo 1875639 2814143 := bstep (se 1 (by rfl) ⟨2110607, by rfl⟩ : syracuseStep 2814143 = 4221215) B4221215
theorem B6418871 : Blo 1875639 6418871 := bstep (se 1 (by rfl) ⟨4814153, by rfl⟩ : syracuseStep 6418871 = 9628307) B9628307
theorem B28897721 : Blo 1875639 28897721 := bstep (se 2 (by rfl) ⟨10836645, by rfl⟩ : syracuseStep 28897721 = 21673291) B21673291
theorem B27054593 : Blo 1875639 27054593 := bstep (se 2 (by rfl) ⟨10145472, by rfl⟩ : syracuseStep 27054593 = 20290945) B20290945
theorem B2814491 : Blo 1875639 2814491 := bstep (se 1 (by rfl) ⟨2110868, by rfl⟩ : syracuseStep 2814491 = 4221737) B4221737
theorem B16249423 : Blo 1875639 16249423 := bstep (se 1 (by rfl) ⟨12187067, by rfl⟩ : syracuseStep 16249423 = 24374135) B24374135
theorem B2814671 : Blo 1875639 2814671 := bstep (se 1 (by rfl) ⟨2111003, by rfl⟩ : syracuseStep 2814671 = 4222007) B4222007
theorem B3166951 : Blo 1875639 3166951 := bstep (se 1 (by rfl) ⟨2375213, by rfl⟩ : syracuseStep 3166951 = 4750427) B4750427
theorem B2814791 : Blo 1875639 2814791 := bstep (se 1 (by rfl) ⟨2111093, by rfl⟩ : syracuseStep 2814791 = 4222187) B4222187
theorem B55579871 : Blo 1875639 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B70325567 : Blo 1875639 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B2815343 : Blo 1875639 2815343 := bstep (se 1 (by rfl) ⟨2111507, by rfl⟩ : syracuseStep 2815343 = 4223015) B4223015
theorem B51369349 : Blo 1875639 51369349 := bstep (se 4 (by rfl) ⟨4815876, by rfl⟩ : syracuseStep 51369349 = 9631753) B9631753
theorem B7124395 : Blo 1875639 7124395 := bstep (se 1 (by rfl) ⟨5343296, by rfl⟩ : syracuseStep 7124395 = 10686593) B10686593
theorem B117142955 : Blo 1875639 117142955 := bstep (se 1 (by rfl) ⟨87857216, by rfl⟩ : syracuseStep 117142955 = 175714433) B175714433
theorem B2815463 : Blo 1875639 2815463 := bstep (se 1 (by rfl) ⟨2111597, by rfl⟩ : syracuseStep 2815463 = 4223195) B4223195
theorem B4748827 : Blo 1875639 4748827 := bstep (se 1 (by rfl) ⟨3561620, by rfl⟩ : syracuseStep 4748827 = 7123241) B7123241
theorem B2815535 : Blo 1875639 2815535 := bstep (se 1 (by rfl) ⟨2111651, by rfl⟩ : syracuseStep 2815535 = 4223303) B4223303
theorem B2815643 : Blo 1875639 2815643 := bstep (se 1 (by rfl) ⟨2111732, by rfl⟩ : syracuseStep 2815643 = 4223465) B4223465
theorem B9500327 : Blo 1875639 9500327 := bstep (se 1 (by rfl) ⟨7125245, by rfl⟩ : syracuseStep 9500327 = 14250491) B14250491
theorem B2111359 : Blo 1875639 2111359 := bstep (se 1 (by rfl) ⟨1583519, by rfl⟩ : syracuseStep 2111359 = 3167039) B3167039
theorem B6330311 : Blo 1875639 6330311 := bstep (se 1 (by rfl) ⟨4747733, by rfl⟩ : syracuseStep 6330311 = 9495467) B9495467
theorem B3561499 : Blo 1875639 3561499 := bstep (se 1 (by rfl) ⟨2671124, by rfl⟩ : syracuseStep 3561499 = 5342249) B5342249
theorem B12835111 : Blo 1875639 12835111 := bstep (se 1 (by rfl) ⟨9626333, by rfl⟩ : syracuseStep 12835111 = 19252667) B19252667
theorem B7125367 : Blo 1875639 7125367 := bstep (se 1 (by rfl) ⟨5344025, by rfl⟩ : syracuseStep 7125367 = 10688051) B10688051
theorem B4749799 : Blo 1875639 4749799 := bstep (se 1 (by rfl) ⟨3562349, by rfl⟩ : syracuseStep 4749799 = 7124699) B7124699
theorem B15219251 : Blo 1875639 15219251 := bstep (se 1 (by rfl) ⟨11414438, by rfl⟩ : syracuseStep 15219251 = 22828877) B22828877
theorem B6843537983 : Blo 1875639 6843537983 := bstep (se 1 (by rfl) ⟨5132653487, by rfl⟩ : syracuseStep 6843537983 = 10265306975) B10265306975
theorem B2440039 : Blo 1875639 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B32505085 : Blo 1875639 32505085 := bstep (se 3 (by rfl) ⟨6094703, by rfl⟩ : syracuseStep 32505085 = 12189407) B12189407
theorem B9502271 : Blo 1875639 9502271 := bstep (se 1 (by rfl) ⟨7126703, by rfl⟩ : syracuseStep 9502271 = 14253407) B14253407
theorem B1875695 : Blo 1875639 1875695 := bstep (se 1 (by rfl) ⟨1406771, by rfl⟩ : syracuseStep 1875695 = 2813543) B2813543
theorem B5070575 : Blo 1875639 5070575 := bstep (se 1 (by rfl) ⟨3802931, by rfl⟩ : syracuseStep 5070575 = 7605863) B7605863
theorem B3563489 : Blo 1875639 3563489 := bstep (se 2 (by rfl) ⟨1336308, by rfl⟩ : syracuseStep 3563489 = 2672617) B2672617
theorem B1875951 : Blo 1875639 1875951 := bstep (se 1 (by rfl) ⟨1406963, by rfl⟩ : syracuseStep 1875951 = 2813927) B2813927
theorem B7815215 : Blo 1875639 7815215 := bstep (se 1 (by rfl) ⟨5861411, by rfl⟩ : syracuseStep 7815215 = 11722823) B11722823
theorem B1876095 : Blo 1875639 1876095 := bstep (se 1 (by rfl) ⟨1407071, by rfl⟩ : syracuseStep 1876095 = 2814143) B2814143
theorem B1876327 : Blo 1875639 1876327 := bstep (se 1 (by rfl) ⟨1407245, by rfl⟩ : syracuseStep 1876327 = 2814491) B2814491
theorem B17113481 : Blo 1875639 17113481 := bstep (se 2 (by rfl) ⟨6417555, by rfl⟩ : syracuseStep 17113481 = 12835111) B12835111
theorem B1876447 : Blo 1875639 1876447 := bstep (se 1 (by rfl) ⟨1407335, by rfl⟩ : syracuseStep 1876447 = 2814671) B2814671
theorem B10682927 : Blo 1875639 10682927 := bstep (se 1 (by rfl) ⟨8012195, by rfl⟩ : syracuseStep 10682927 = 16024391) B16024391
theorem B1876527 : Blo 1875639 1876527 := bstep (se 1 (by rfl) ⟨1407395, by rfl⟩ : syracuseStep 1876527 = 2814791) B2814791
theorem B6333065 : Blo 1875639 6333065 := bstep (se 2 (by rfl) ⟨2374899, by rfl⟩ : syracuseStep 6333065 = 4749799) B4749799
theorem B37053247 : Blo 1875639 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B46883711 : Blo 1875639 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B1876895 : Blo 1875639 1876895 := bstep (se 1 (by rfl) ⟨1407671, by rfl⟩ : syracuseStep 1876895 = 2815343) B2815343
theorem B78095303 : Blo 1875639 78095303 := bstep (se 1 (by rfl) ⟨58571477, by rfl⟩ : syracuseStep 78095303 = 117142955) B117142955
theorem B1876975 : Blo 1875639 1876975 := bstep (se 1 (by rfl) ⟨1407731, by rfl⟩ : syracuseStep 1876975 = 2815463) B2815463
theorem B1877023 : Blo 1875639 1877023 := bstep (se 1 (by rfl) ⟨1407767, by rfl⟩ : syracuseStep 1877023 = 2815535) B2815535
theorem B38503525 : Blo 1875639 38503525 := bstep (se 4 (by rfl) ⟨3609705, by rfl⟩ : syracuseStep 38503525 = 7219411) B7219411
theorem B1877095 : Blo 1875639 1877095 := bstep (se 1 (by rfl) ⟨1407821, by rfl⟩ : syracuseStep 1877095 = 2815643) B2815643
theorem B6333551 : Blo 1875639 6333551 := bstep (se 1 (by rfl) ⟨4750163, by rfl⟩ : syracuseStep 6333551 = 9500327) B9500327
theorem B3253385 : Blo 1875639 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B46286099 : Blo 1875639 46286099 := bstep (se 1 (by rfl) ⟨34714574, by rfl⟩ : syracuseStep 46286099 = 69429149) B69429149
theorem B4220207 : Blo 1875639 4220207 := bstep (se 1 (by rfl) ⟨3165155, by rfl⟩ : syracuseStep 4220207 = 6330311) B6330311
theorem B10143443 : Blo 1875639 10143443 := bstep (se 1 (by rfl) ⟨7607582, by rfl⟩ : syracuseStep 10143443 = 15215165) B15215165
theorem B6334847 : Blo 1875639 6334847 := bstep (se 1 (by rfl) ⟨4751135, by rfl⟩ : syracuseStep 6334847 = 9502271) B9502271
theorem B4278727 : Blo 1875639 4278727 := bstep (se 1 (by rfl) ⟨3209045, by rfl⟩ : syracuseStep 4278727 = 6418091) B6418091
theorem B10685135 : Blo 1875639 10685135 := bstep (se 1 (by rfl) ⟨8013851, by rfl⟩ : syracuseStep 10685135 = 16027703) B16027703
theorem B4279247 : Blo 1875639 4279247 := bstep (se 1 (by rfl) ⟨3209435, by rfl⟩ : syracuseStep 4279247 = 6418871) B6418871
theorem B5344505 : Blo 1875639 5344505 := bstep (se 2 (by rfl) ⟨2004189, by rfl⟩ : syracuseStep 5344505 = 4008379) B4008379
theorem B4222601 : Blo 1875639 4222601 := bstep (se 2 (by rfl) ⟨1583475, by rfl⟩ : syracuseStep 4222601 = 3166951) B3166951
theorem B4222655 : Blo 1875639 4222655 := bstep (se 1 (by rfl) ⟨3166991, by rfl⟩ : syracuseStep 4222655 = 6333983) B6333983
theorem B7606381 : Blo 1875639 7606381 := bstep (se 3 (by rfl) ⟨1426196, by rfl⟩ : syracuseStep 7606381 = 2852393) B2852393
theorem B43340113 : Blo 1875639 43340113 := bstep (se 2 (by rfl) ⟨16252542, by rfl⟩ : syracuseStep 43340113 = 32505085) B32505085
theorem B10146167 : Blo 1875639 10146167 := bstep (se 1 (by rfl) ⟨7609625, by rfl⟩ : syracuseStep 10146167 = 15219251) B15219251
theorem B4562358655 : Blo 1875639 4562358655 := bstep (se 1 (by rfl) ⟨3421768991, by rfl⟩ : syracuseStep 4562358655 = 6843537983) B6843537983
theorem B9499193 : Blo 1875639 9499193 := bstep (se 2 (by rfl) ⟨3562197, by rfl⟩ : syracuseStep 9499193 = 7124395) B7124395
theorem B9499355 : Blo 1875639 9499355 := bstep (se 1 (by rfl) ⟨7124516, by rfl⟩ : syracuseStep 9499355 = 14249033) B14249033
theorem B2110279 : Blo 1875639 2110279 := bstep (se 1 (by rfl) ⟨1582709, by rfl⟩ : syracuseStep 2110279 = 3165419) B3165419
theorem B3380089 : Blo 1875639 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B40104935 : Blo 1875639 40104935 := bstep (se 1 (by rfl) ⟨30078701, by rfl⟩ : syracuseStep 40104935 = 60157403) B60157403
theorem B3380383 : Blo 1875639 3380383 := bstep (se 1 (by rfl) ⟨2535287, by rfl⟩ : syracuseStep 3380383 = 5070575) B5070575
theorem B2815145 : Blo 1875639 2815145 := bstep (se 2 (by rfl) ⟨1055679, by rfl⟩ : syracuseStep 2815145 = 2111359) B2111359
theorem B2110747 : Blo 1875639 2110747 := bstep (se 1 (by rfl) ⟨1583060, by rfl⟩ : syracuseStep 2110747 = 3166121) B3166121
theorem B6092111 : Blo 1875639 6092111 := bstep (se 1 (by rfl) ⟨4569083, by rfl⟩ : syracuseStep 6092111 = 9138167) B9138167
theorem B4748665 : Blo 1875639 4748665 := bstep (se 2 (by rfl) ⟨1780749, by rfl⟩ : syracuseStep 4748665 = 3561499) B3561499
theorem B19265147 : Blo 1875639 19265147 := bstep (se 1 (by rfl) ⟨14448860, by rfl⟩ : syracuseStep 19265147 = 28897721) B28897721
theorem B18036395 : Blo 1875639 18036395 := bstep (se 1 (by rfl) ⟨13527296, by rfl⟩ : syracuseStep 18036395 = 27054593) B27054593
theorem B9500489 : Blo 1875639 9500489 := bstep (se 2 (by rfl) ⟨3562683, by rfl⟩ : syracuseStep 9500489 = 7125367) B7125367
theorem B21665897 : Blo 1875639 21665897 := bstep (se 2 (by rfl) ⟨8124711, by rfl⟩ : syracuseStep 21665897 = 16249423) B16249423
theorem B68492465 : Blo 1875639 68492465 := bstep (se 2 (by rfl) ⟨25684674, by rfl⟩ : syracuseStep 68492465 = 51369349) B51369349
theorem B6331769 : Blo 1875639 6331769 := bstep (se 2 (by rfl) ⟨2374413, by rfl⟩ : syracuseStep 6331769 = 4748827) B4748827
theorem B38526347 : Blo 1875639 38526347 := bstep (se 1 (by rfl) ⟨28894760, by rfl⟩ : syracuseStep 38526347 = 57789521) B57789521
theorem B1875775 : Blo 1875639 1875775 := bstep (se 1 (by rfl) ⟨1406831, by rfl⟩ : syracuseStep 1875775 = 2813663) B2813663
theorem B2375659 : Blo 1875639 2375659 := bstep (se 1 (by rfl) ⟨1781744, by rfl⟩ : syracuseStep 2375659 = 3563489) B3563489
theorem B20840573 : Blo 1875639 20840573 := bstep (se 3 (by rfl) ⟨3907607, by rfl⟩ : syracuseStep 20840573 = 7815215) B7815215
theorem B10141841 : Blo 1875639 10141841 := bstep (se 2 (by rfl) ⟨3803190, by rfl⟩ : syracuseStep 10141841 = 7606381) B7606381
theorem B8675693 : Blo 1875639 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B6332795 : Blo 1875639 6332795 := bstep (se 1 (by rfl) ⟨4749596, by rfl⟩ : syracuseStep 6332795 = 9499193) B9499193
theorem B57786817 : Blo 1875639 57786817 := bstep (se 2 (by rfl) ⟨21670056, by rfl⟩ : syracuseStep 57786817 = 43340113) B43340113
theorem B6332903 : Blo 1875639 6332903 := bstep (se 1 (by rfl) ⟨4749677, by rfl⟩ : syracuseStep 6332903 = 9499355) B9499355
theorem B1876763 : Blo 1875639 1876763 := bstep (se 1 (by rfl) ⟨1407572, by rfl⟩ : syracuseStep 1876763 = 2815145) B2815145
theorem B16245629 : Blo 1875639 16245629 := bstep (se 3 (by rfl) ⟨3046055, by rfl⟩ : syracuseStep 16245629 = 6092111) B6092111
theorem B4506785 : Blo 1875639 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B6333659 : Blo 1875639 6333659 := bstep (se 1 (by rfl) ⟨4750244, by rfl⟩ : syracuseStep 6333659 = 9500489) B9500489
theorem B14443931 : Blo 1875639 14443931 := bstep (se 1 (by rfl) ⟨10832948, by rfl⟩ : syracuseStep 14443931 = 21665897) B21665897
theorem B4507177 : Blo 1875639 4507177 := bstep (se 2 (by rfl) ⟨1690191, by rfl⟩ : syracuseStep 4507177 = 3380383) B3380383
theorem B2852831 : Blo 1875639 2852831 := bstep (se 1 (by rfl) ⟨2139623, by rfl⟩ : syracuseStep 2852831 = 4279247) B4279247
theorem B4221179 : Blo 1875639 4221179 := bstep (se 1 (by rfl) ⟨3165884, by rfl⟩ : syracuseStep 4221179 = 6331769) B6331769
theorem B25684231 : Blo 1875639 25684231 := bstep (se 1 (by rfl) ⟨19263173, by rfl⟩ : syracuseStep 25684231 = 38526347) B38526347
theorem B7121951 : Blo 1875639 7121951 := bstep (se 1 (by rfl) ⟨5341463, by rfl⟩ : syracuseStep 7121951 = 10682927) B10682927
theorem B4222043 : Blo 1875639 4222043 := bstep (se 1 (by rfl) ⟨3166532, by rfl⟩ : syracuseStep 4222043 = 6333065) B6333065
theorem B6083144873 : Blo 1875639 6083144873 := bstep (se 2 (by rfl) ⟨2281179327, by rfl⟩ : syracuseStep 6083144873 = 4562358655) B4562358655
theorem B31255807 : Blo 1875639 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B52063535 : Blo 1875639 52063535 := bstep (se 1 (by rfl) ⟨39047651, by rfl⟩ : syracuseStep 52063535 = 78095303) B78095303
theorem B4222367 : Blo 1875639 4222367 := bstep (se 1 (by rfl) ⟨3166775, by rfl⟩ : syracuseStep 4222367 = 6333551) B6333551
theorem B2813471 : Blo 1875639 2813471 := bstep (se 1 (by rfl) ⟨2110103, by rfl⟩ : syracuseStep 2813471 = 4220207) B4220207
theorem B2813705 : Blo 1875639 2813705 := bstep (se 2 (by rfl) ⟨1055139, by rfl⟩ : syracuseStep 2813705 = 2110279) B2110279
theorem B6762295 : Blo 1875639 6762295 := bstep (se 1 (by rfl) ⟨5071721, by rfl⟩ : syracuseStep 6762295 = 10143443) B10143443
theorem B4223231 : Blo 1875639 4223231 := bstep (se 1 (by rfl) ⟨3167423, by rfl⟩ : syracuseStep 4223231 = 6334847) B6334847
theorem B2814329 : Blo 1875639 2814329 := bstep (se 2 (by rfl) ⟨1055373, by rfl⟩ : syracuseStep 2814329 = 2110747) B2110747
theorem B7123423 : Blo 1875639 7123423 := bstep (se 1 (by rfl) ⟨5342567, by rfl⟩ : syracuseStep 7123423 = 10685135) B10685135
theorem B22819877 : Blo 1875639 22819877 := bstep (se 4 (by rfl) ⟨2139363, by rfl⟩ : syracuseStep 22819877 = 4278727) B4278727
theorem B2815067 : Blo 1875639 2815067 := bstep (se 1 (by rfl) ⟨2111300, by rfl⟩ : syracuseStep 2815067 = 4222601) B4222601
theorem B2815103 : Blo 1875639 2815103 := bstep (se 1 (by rfl) ⟨2111327, by rfl⟩ : syracuseStep 2815103 = 4222655) B4222655
theorem B3167545 : Blo 1875639 3167545 := bstep (se 2 (by rfl) ⟨1187829, by rfl⟩ : syracuseStep 3167545 = 2375659) B2375659
theorem B6764111 : Blo 1875639 6764111 := bstep (se 1 (by rfl) ⟨5073083, by rfl⟩ : syracuseStep 6764111 = 10146167) B10146167
theorem B11408987 : Blo 1875639 11408987 := bstep (se 1 (by rfl) ⟨8556740, by rfl⟩ : syracuseStep 11408987 = 17113481) B17113481
theorem B26736623 : Blo 1875639 26736623 := bstep (se 1 (by rfl) ⟨20052467, by rfl⟩ : syracuseStep 26736623 = 40104935) B40104935
theorem B30857399 : Blo 1875639 30857399 := bstep (se 1 (by rfl) ⟨23143049, by rfl⟩ : syracuseStep 30857399 = 46286099) B46286099
theorem B12843431 : Blo 1875639 12843431 := bstep (se 1 (by rfl) ⟨9632573, by rfl⟩ : syracuseStep 12843431 = 19265147) B19265147
theorem B49404329 : Blo 1875639 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B12024263 : Blo 1875639 12024263 := bstep (se 1 (by rfl) ⟨9018197, by rfl⟩ : syracuseStep 12024263 = 18036395) B18036395
theorem B51338033 : Blo 1875639 51338033 := bstep (se 2 (by rfl) ⟨19251762, by rfl⟩ : syracuseStep 51338033 = 38503525) B38503525
theorem B6331553 : Blo 1875639 6331553 := bstep (se 2 (by rfl) ⟨2374332, by rfl⟩ : syracuseStep 6331553 = 4748665) B4748665
theorem B45661643 : Blo 1875639 45661643 := bstep (se 1 (by rfl) ⟨34246232, by rfl⟩ : syracuseStep 45661643 = 68492465) B68492465
theorem B3563003 : Blo 1875639 3563003 := bstep (se 1 (by rfl) ⟨2672252, by rfl⟩ : syracuseStep 3563003 = 5344505) B5344505
theorem B13893715 : Blo 1875639 13893715 := bstep (se 1 (by rfl) ⟨10420286, by rfl⟩ : syracuseStep 13893715 = 20840573) B20840573
theorem B5783795 : Blo 1875639 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B1876219 : Blo 1875639 1876219 := bstep (se 1 (by rfl) ⟨1407164, by rfl⟩ : syracuseStep 1876219 = 2814329) B2814329
theorem B10830419 : Blo 1875639 10830419 := bstep (se 1 (by rfl) ⟨8122814, by rfl⟩ : syracuseStep 10830419 = 16245629) B16245629
theorem B15213251 : Blo 1875639 15213251 := bstep (se 1 (by rfl) ⟨11409938, by rfl⟩ : syracuseStep 15213251 = 22819877) B22819877
theorem B1876711 : Blo 1875639 1876711 := bstep (se 1 (by rfl) ⟨1407533, by rfl⟩ : syracuseStep 1876711 = 2815067) B2815067
theorem B1876735 : Blo 1875639 1876735 := bstep (se 1 (by rfl) ⟨1407551, by rfl⟩ : syracuseStep 1876735 = 2815103) B2815103
theorem B1901887 : Blo 1875639 1901887 := bstep (se 1 (by rfl) ⟨1426415, by rfl⟩ : syracuseStep 1901887 = 2852831) B2852831
theorem B20571599 : Blo 1875639 20571599 := bstep (se 1 (by rfl) ⟨15428699, by rfl⟩ : syracuseStep 20571599 = 30857399) B30857399
theorem B8562287 : Blo 1875639 8562287 := bstep (se 1 (by rfl) ⟨6421715, by rfl⟩ : syracuseStep 8562287 = 12843431) B12843431
theorem B41674409 : Blo 1875639 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B4221035 : Blo 1875639 4221035 := bstep (se 1 (by rfl) ⟨3165776, by rfl⟩ : syracuseStep 4221035 = 6331553) B6331553
theorem B285190645 : Blo 1875639 285190645 := bstep (se 5 (by rfl) ⟨13368311, by rfl⟩ : syracuseStep 285190645 = 26736623) B26736623
theorem B6761227 : Blo 1875639 6761227 := bstep (se 1 (by rfl) ⟨5070920, by rfl⟩ : syracuseStep 6761227 = 10141841) B10141841
theorem B4221863 : Blo 1875639 4221863 := bstep (se 1 (by rfl) ⟨3166397, by rfl⟩ : syracuseStep 4221863 = 6332795) B6332795
theorem B4221935 : Blo 1875639 4221935 := bstep (se 1 (by rfl) ⟨3166451, by rfl⟩ : syracuseStep 4221935 = 6332903) B6332903
theorem B34245641 : Blo 1875639 34245641 := bstep (se 2 (by rfl) ⟨12842115, by rfl⟩ : syracuseStep 34245641 = 25684231) B25684231
theorem B77049089 : Blo 1875639 77049089 := bstep (se 2 (by rfl) ⟨28893408, by rfl⟩ : syracuseStep 77049089 = 57786817) B57786817
theorem B9497897 : Blo 1875639 9497897 := bstep (se 2 (by rfl) ⟨3561711, by rfl⟩ : syracuseStep 9497897 = 7123423) B7123423
theorem B4222439 : Blo 1875639 4222439 := bstep (se 1 (by rfl) ⟨3166829, by rfl⟩ : syracuseStep 4222439 = 6333659) B6333659
theorem B9629287 : Blo 1875639 9629287 := bstep (se 1 (by rfl) ⟨7221965, by rfl⟩ : syracuseStep 9629287 = 14443931) B14443931
theorem B4509407 : Blo 1875639 4509407 := bstep (se 1 (by rfl) ⟨3382055, by rfl⟩ : syracuseStep 4509407 = 6764111) B6764111
theorem B7605991 : Blo 1875639 7605991 := bstep (se 1 (by rfl) ⟨5704493, by rfl⟩ : syracuseStep 7605991 = 11408987) B11408987
theorem B2814119 : Blo 1875639 2814119 := bstep (se 1 (by rfl) ⟨2110589, by rfl⟩ : syracuseStep 2814119 = 4221179) B4221179
theorem B32936219 : Blo 1875639 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B8016175 : Blo 1875639 8016175 := bstep (se 1 (by rfl) ⟨6012131, by rfl⟩ : syracuseStep 8016175 = 12024263) B12024263
theorem B4223393 : Blo 1875639 4223393 := bstep (se 2 (by rfl) ⟨1583772, by rfl⟩ : syracuseStep 4223393 = 3167545) B3167545
theorem B4747967 : Blo 1875639 4747967 := bstep (se 1 (by rfl) ⟨3560975, by rfl⟩ : syracuseStep 4747967 = 7121951) B7121951
theorem B6009569 : Blo 1875639 6009569 := bstep (se 2 (by rfl) ⟨2253588, by rfl⟩ : syracuseStep 6009569 = 4507177) B4507177
theorem B2814695 : Blo 1875639 2814695 := bstep (se 1 (by rfl) ⟨2111021, by rfl⟩ : syracuseStep 2814695 = 4222043) B4222043
theorem B4055429915 : Blo 1875639 4055429915 := bstep (se 1 (by rfl) ⟨3041572436, by rfl⟩ : syracuseStep 4055429915 = 6083144873) B6083144873
theorem B2814911 : Blo 1875639 2814911 := bstep (se 1 (by rfl) ⟨2111183, by rfl⟩ : syracuseStep 2814911 = 4222367) B4222367
theorem B9016393 : Blo 1875639 9016393 := bstep (se 2 (by rfl) ⟨3381147, by rfl⟩ : syracuseStep 9016393 = 6762295) B6762295
theorem B2815487 : Blo 1875639 2815487 := bstep (se 1 (by rfl) ⟨2111615, by rfl⟩ : syracuseStep 2815487 = 4223231) B4223231
theorem B3004523 : Blo 1875639 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B34225355 : Blo 1875639 34225355 := bstep (se 1 (by rfl) ⟨25669016, by rfl⟩ : syracuseStep 34225355 = 51338033) B51338033
theorem B34709023 : Blo 1875639 34709023 := bstep (se 1 (by rfl) ⟨26031767, by rfl⟩ : syracuseStep 34709023 = 52063535) B52063535
theorem B30441095 : Blo 1875639 30441095 := bstep (se 1 (by rfl) ⟨22830821, by rfl⟩ : syracuseStep 30441095 = 45661643) B45661643
theorem B2375335 : Blo 1875639 2375335 := bstep (se 1 (by rfl) ⟨1781501, by rfl⟩ : syracuseStep 2375335 = 3563003) B3563003
theorem B1875647 : Blo 1875639 1875647 := bstep (se 1 (by rfl) ⟨1406735, by rfl⟩ : syracuseStep 1875647 = 2813471) B2813471
theorem B1875803 : Blo 1875639 1875803 := bstep (se 1 (by rfl) ⟨1406852, by rfl⟩ : syracuseStep 1875803 = 2813705) B2813705
theorem B1876079 : Blo 1875639 1876079 := bstep (se 1 (by rfl) ⟨1407059, by rfl⟩ : syracuseStep 1876079 = 2814119) B2814119
theorem B10142167 : Blo 1875639 10142167 := bstep (se 1 (by rfl) ⟨7606625, by rfl⟩ : syracuseStep 10142167 = 15213251) B15213251
theorem B4006379 : Blo 1875639 4006379 := bstep (se 1 (by rfl) ⟨3004784, by rfl⟩ : syracuseStep 4006379 = 6009569) B6009569
theorem B1876463 : Blo 1875639 1876463 := bstep (se 1 (by rfl) ⟨1407347, by rfl⟩ : syracuseStep 1876463 = 2814695) B2814695
theorem B51356197 : Blo 1875639 51356197 := bstep (se 4 (by rfl) ⟨4814643, by rfl⟩ : syracuseStep 51356197 = 9629287) B9629287
theorem B1876607 : Blo 1875639 1876607 := bstep (se 1 (by rfl) ⟨1407455, by rfl⟩ : syracuseStep 1876607 = 2814911) B2814911
theorem B13714399 : Blo 1875639 13714399 := bstep (se 1 (by rfl) ⟨10285799, by rfl⟩ : syracuseStep 13714399 = 20571599) B20571599
theorem B1876991 : Blo 1875639 1876991 := bstep (se 1 (by rfl) ⟨1407743, by rfl⟩ : syracuseStep 1876991 = 2815487) B2815487
theorem B22832765 : Blo 1875639 22832765 := bstep (se 3 (by rfl) ⟨4281143, by rfl⟩ : syracuseStep 22832765 = 8562287) B8562287
theorem B10143397 : Blo 1875639 10143397 := bstep (se 4 (by rfl) ⟨950943, by rfl⟩ : syracuseStep 10143397 = 1901887) B1901887
theorem B46278697 : Blo 1875639 46278697 := bstep (se 2 (by rfl) ⟨17354511, by rfl⟩ : syracuseStep 46278697 = 34709023) B34709023
theorem B22816903 : Blo 1875639 22816903 := bstep (se 1 (by rfl) ⟨17112677, by rfl⟩ : syracuseStep 22816903 = 34225355) B34225355
theorem B51366059 : Blo 1875639 51366059 := bstep (se 1 (by rfl) ⟨38524544, by rfl⟩ : syracuseStep 51366059 = 77049089) B77049089
theorem B20294063 : Blo 1875639 20294063 := bstep (se 1 (by rfl) ⟨15220547, by rfl⟩ : syracuseStep 20294063 = 30441095) B30441095
theorem B18524953 : Blo 1875639 18524953 := bstep (se 2 (by rfl) ⟨6946857, by rfl⟩ : syracuseStep 18524953 = 13893715) B13893715
theorem B21957479 : Blo 1875639 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B7220279 : Blo 1875639 7220279 := bstep (se 1 (by rfl) ⟨5415209, by rfl⟩ : syracuseStep 7220279 = 10830419) B10830419
theorem B3165311 : Blo 1875639 3165311 := bstep (se 1 (by rfl) ⟨2373983, by rfl⟩ : syracuseStep 3165311 = 4747967) B4747967
theorem B9014969 : Blo 1875639 9014969 := bstep (se 2 (by rfl) ⟨3380613, by rfl⟩ : syracuseStep 9014969 = 6761227) B6761227
theorem B27782939 : Blo 1875639 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B2003015 : Blo 1875639 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B2814023 : Blo 1875639 2814023 := bstep (se 1 (by rfl) ⟨2110517, by rfl⟩ : syracuseStep 2814023 = 4221035) B4221035
theorem B12021857 : Blo 1875639 12021857 := bstep (se 2 (by rfl) ⟨4508196, by rfl⟩ : syracuseStep 12021857 = 9016393) B9016393
theorem B2814575 : Blo 1875639 2814575 := bstep (se 1 (by rfl) ⟨2110931, by rfl⟩ : syracuseStep 2814575 = 4221863) B4221863
theorem B2814623 : Blo 1875639 2814623 := bstep (se 1 (by rfl) ⟨2110967, by rfl⟩ : syracuseStep 2814623 = 4221935) B4221935
theorem B3167113 : Blo 1875639 3167113 := bstep (se 2 (by rfl) ⟨1187667, by rfl⟩ : syracuseStep 3167113 = 2375335) B2375335
theorem B2814959 : Blo 1875639 2814959 := bstep (se 1 (by rfl) ⟨2111219, by rfl⟩ : syracuseStep 2814959 = 4222439) B4222439
theorem B3855863 : Blo 1875639 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B2815595 : Blo 1875639 2815595 := bstep (se 1 (by rfl) ⟨2111696, by rfl⟩ : syracuseStep 2815595 = 4223393) B4223393
theorem B10688233 : Blo 1875639 10688233 := bstep (se 2 (by rfl) ⟨4008087, by rfl⟩ : syracuseStep 10688233 = 8016175) B8016175
theorem B2703619943 : Blo 1875639 2703619943 := bstep (se 1 (by rfl) ⟨2027714957, by rfl⟩ : syracuseStep 2703619943 = 4055429915) B4055429915
theorem B380254193 : Blo 1875639 380254193 := bstep (se 2 (by rfl) ⟨142595322, by rfl⟩ : syracuseStep 380254193 = 285190645) B285190645
theorem B22830427 : Blo 1875639 22830427 := bstep (se 1 (by rfl) ⟨17122820, by rfl⟩ : syracuseStep 22830427 = 34245641) B34245641
theorem B6331931 : Blo 1875639 6331931 := bstep (se 1 (by rfl) ⟨4748948, by rfl⟩ : syracuseStep 6331931 = 9497897) B9497897
theorem B10141321 : Blo 1875639 10141321 := bstep (se 2 (by rfl) ⟨3802995, by rfl⟩ : syracuseStep 10141321 = 7605991) B7605991
theorem B3006271 : Blo 1875639 3006271 := bstep (se 1 (by rfl) ⟨2254703, by rfl⟩ : syracuseStep 3006271 = 4509407) B4509407
theorem B1876015 : Blo 1875639 1876015 := bstep (se 1 (by rfl) ⟨1407011, by rfl⟩ : syracuseStep 1876015 = 2814023) B2814023
theorem B5341373 : Blo 1875639 5341373 := bstep (se 3 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 5341373 = 2003015) B2003015
theorem B1876383 : Blo 1875639 1876383 := bstep (se 1 (by rfl) ⟨1407287, by rfl⟩ : syracuseStep 1876383 = 2814575) B2814575
theorem B1876415 : Blo 1875639 1876415 := bstep (se 1 (by rfl) ⟨1407311, by rfl⟩ : syracuseStep 1876415 = 2814623) B2814623
theorem B1876639 : Blo 1875639 1876639 := bstep (se 1 (by rfl) ⟨1407479, by rfl⟩ : syracuseStep 1876639 = 2814959) B2814959
theorem B24699937 : Blo 1875639 24699937 := bstep (se 2 (by rfl) ⟨9262476, by rfl⟩ : syracuseStep 24699937 = 18524953) B18524953
theorem B1877063 : Blo 1875639 1877063 := bstep (se 1 (by rfl) ⟨1407797, by rfl⟩ : syracuseStep 1877063 = 2815595) B2815595
theorem B15221843 : Blo 1875639 15221843 := bstep (se 1 (by rfl) ⟨11416382, by rfl⟩ : syracuseStep 15221843 = 22832765) B22832765
theorem B1802413295 : Blo 1875639 1802413295 := bstep (se 1 (by rfl) ⟨1351809971, by rfl⟩ : syracuseStep 1802413295 = 2703619943) B2703619943
theorem B10683677 : Blo 1875639 10683677 := bstep (se 3 (by rfl) ⟨2003189, by rfl⟩ : syracuseStep 10683677 = 4006379) B4006379
theorem B10282301 : Blo 1875639 10282301 := bstep (se 3 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 10282301 = 3855863) B3855863
theorem B253502795 : Blo 1875639 253502795 := bstep (se 1 (by rfl) ⟨190127096, by rfl⟩ : syracuseStep 253502795 = 380254193) B380254193
theorem B34244039 : Blo 1875639 34244039 := bstep (se 1 (by rfl) ⟨25683029, by rfl⟩ : syracuseStep 34244039 = 51366059) B51366059
theorem B4221287 : Blo 1875639 4221287 := bstep (se 1 (by rfl) ⟨3165965, by rfl⟩ : syracuseStep 4221287 = 6331931) B6331931
theorem B4008361 : Blo 1875639 4008361 := bstep (se 2 (by rfl) ⟨1503135, by rfl⟩ : syracuseStep 4008361 = 3006271) B3006271
theorem B61704929 : Blo 1875639 61704929 := bstep (se 2 (by rfl) ⟨23139348, by rfl⟩ : syracuseStep 61704929 = 46278697) B46278697
theorem B8014571 : Blo 1875639 8014571 := bstep (se 1 (by rfl) ⟨6010928, by rfl⟩ : syracuseStep 8014571 = 12021857) B12021857
theorem B4222817 : Blo 1875639 4222817 := bstep (se 2 (by rfl) ⟨1583556, by rfl⟩ : syracuseStep 4222817 = 3167113) B3167113
theorem B13529375 : Blo 1875639 13529375 := bstep (se 1 (by rfl) ⟨10147031, by rfl⟩ : syracuseStep 13529375 = 20294063) B20294063
theorem B4813519 : Blo 1875639 4813519 := bstep (se 1 (by rfl) ⟨3610139, by rfl⟩ : syracuseStep 4813519 = 7220279) B7220279
theorem B2110207 : Blo 1875639 2110207 := bstep (se 1 (by rfl) ⟨1582655, by rfl⟩ : syracuseStep 2110207 = 3165311) B3165311
theorem B13521761 : Blo 1875639 13521761 := bstep (se 2 (by rfl) ⟨5070660, by rfl⟩ : syracuseStep 13521761 = 10141321) B10141321
theorem B14250977 : Blo 1875639 14250977 := bstep (se 2 (by rfl) ⟨5344116, by rfl⟩ : syracuseStep 14250977 = 10688233) B10688233
theorem B6009979 : Blo 1875639 6009979 := bstep (se 1 (by rfl) ⟨4507484, by rfl⟩ : syracuseStep 6009979 = 9014969) B9014969
theorem B73143461 : Blo 1875639 73143461 := bstep (se 4 (by rfl) ⟨6857199, by rfl⟩ : syracuseStep 73143461 = 13714399) B13714399
theorem B30422537 : Blo 1875639 30422537 := bstep (se 2 (by rfl) ⟨11408451, by rfl⟩ : syracuseStep 30422537 = 22816903) B22816903
theorem B13522889 : Blo 1875639 13522889 := bstep (se 2 (by rfl) ⟨5071083, by rfl⟩ : syracuseStep 13522889 = 10142167) B10142167
theorem B68474929 : Blo 1875639 68474929 := bstep (se 2 (by rfl) ⟨25678098, by rfl⟩ : syracuseStep 68474929 = 51356197) B51356197
theorem B30440569 : Blo 1875639 30440569 := bstep (se 2 (by rfl) ⟨11415213, by rfl⟩ : syracuseStep 30440569 = 22830427) B22830427
theorem B14638319 : Blo 1875639 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B13524529 : Blo 1875639 13524529 := bstep (se 2 (by rfl) ⟨5071698, by rfl⟩ : syracuseStep 13524529 = 10143397) B10143397
theorem B18521959 : Blo 1875639 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B91299905 : Blo 1875639 91299905 := bstep (se 2 (by rfl) ⟨34237464, by rfl⟩ : syracuseStep 91299905 = 68474929) B68474929
theorem B9019583 : Blo 1875639 9019583 := bstep (se 1 (by rfl) ⟨6764687, by rfl⟩ : syracuseStep 9019583 = 13529375) B13529375
theorem B32933249 : Blo 1875639 32933249 := bstep (se 2 (by rfl) ⟨12349968, by rfl⟩ : syracuseStep 32933249 = 24699937) B24699937
theorem B8013305 : Blo 1875639 8013305 := bstep (se 2 (by rfl) ⟨3004989, by rfl⟩ : syracuseStep 8013305 = 6009979) B6009979
theorem B5343047 : Blo 1875639 5343047 := bstep (se 1 (by rfl) ⟨4007285, by rfl⟩ : syracuseStep 5343047 = 8014571) B8014571
theorem B164546477 : Blo 1875639 164546477 := bstep (se 3 (by rfl) ⟨30852464, by rfl⟩ : syracuseStep 164546477 = 61704929) B61704929
theorem B18032705 : Blo 1875639 18032705 := bstep (se 2 (by rfl) ⟨6762264, by rfl⟩ : syracuseStep 18032705 = 13524529) B13524529
theorem B9758879 : Blo 1875639 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B5344481 : Blo 1875639 5344481 := bstep (se 2 (by rfl) ⟨2004180, by rfl⟩ : syracuseStep 5344481 = 4008361) B4008361
theorem B9014507 : Blo 1875639 9014507 := bstep (se 1 (by rfl) ⟨6760880, by rfl⟩ : syracuseStep 9014507 = 13521761) B13521761
theorem B48762307 : Blo 1875639 48762307 := bstep (se 1 (by rfl) ⟨36571730, by rfl⟩ : syracuseStep 48762307 = 73143461) B73143461
theorem B7122451 : Blo 1875639 7122451 := bstep (se 1 (by rfl) ⟨5341838, by rfl⟩ : syracuseStep 7122451 = 10683677) B10683677
theorem B676007453 : Blo 1875639 676007453 := bstep (se 3 (by rfl) ⟨126751397, by rfl⟩ : syracuseStep 676007453 = 253502795) B253502795
theorem B6418025 : Blo 1875639 6418025 := bstep (se 2 (by rfl) ⟨2406759, by rfl⟩ : syracuseStep 6418025 = 4813519) B4813519
theorem B2813609 : Blo 1875639 2813609 := bstep (se 2 (by rfl) ⟨1055103, by rfl⟩ : syracuseStep 2813609 = 2110207) B2110207
theorem B9015259 : Blo 1875639 9015259 := bstep (se 1 (by rfl) ⟨6761444, by rfl⟩ : syracuseStep 9015259 = 13522889) B13522889
theorem B40587425 : Blo 1875639 40587425 := bstep (se 2 (by rfl) ⟨15220284, by rfl⟩ : syracuseStep 40587425 = 30440569) B30440569
theorem B2814191 : Blo 1875639 2814191 := bstep (se 1 (by rfl) ⟨2110643, by rfl⟩ : syracuseStep 2814191 = 4221287) B4221287
theorem B24695945 : Blo 1875639 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B2815211 : Blo 1875639 2815211 := bstep (se 1 (by rfl) ⟨2111408, by rfl⟩ : syracuseStep 2815211 = 4222817) B4222817
theorem B3560915 : Blo 1875639 3560915 := bstep (se 1 (by rfl) ⟨2670686, by rfl⟩ : syracuseStep 3560915 = 5341373) B5341373
theorem B9500651 : Blo 1875639 9500651 := bstep (se 1 (by rfl) ⟨7125488, by rfl⟩ : syracuseStep 9500651 = 14250977) B14250977
theorem B10147895 : Blo 1875639 10147895 := bstep (se 1 (by rfl) ⟨7610921, by rfl⟩ : syracuseStep 10147895 = 15221843) B15221843
theorem B1201608863 : Blo 1875639 1201608863 := bstep (se 1 (by rfl) ⟨901206647, by rfl⟩ : syracuseStep 1201608863 = 1802413295) B1802413295
theorem B6854867 : Blo 1875639 6854867 := bstep (se 1 (by rfl) ⟨5141150, by rfl⟩ : syracuseStep 6854867 = 10282301) B10282301
theorem B22829359 : Blo 1875639 22829359 := bstep (se 1 (by rfl) ⟨17122019, by rfl⟩ : syracuseStep 22829359 = 34244039) B34244039
theorem B20281691 : Blo 1875639 20281691 := bstep (se 1 (by rfl) ⟨15211268, by rfl⟩ : syracuseStep 20281691 = 30422537) B30422537
theorem B60866603 : Blo 1875639 60866603 := bstep (se 1 (by rfl) ⟨45649952, by rfl⟩ : syracuseStep 60866603 = 91299905) B91299905
theorem B27058283 : Blo 1875639 27058283 := bstep (se 1 (by rfl) ⟨20293712, by rfl⟩ : syracuseStep 27058283 = 40587425) B40587425
theorem B6013055 : Blo 1875639 6013055 := bstep (se 1 (by rfl) ⟨4509791, by rfl⟩ : syracuseStep 6013055 = 9019583) B9019583
theorem B1876127 : Blo 1875639 1876127 := bstep (se 1 (by rfl) ⟨1407095, by rfl⟩ : syracuseStep 1876127 = 2814191) B2814191
theorem B1876807 : Blo 1875639 1876807 := bstep (se 1 (by rfl) ⟨1407605, by rfl⟩ : syracuseStep 1876807 = 2815211) B2815211
theorem B54084509 : Blo 1875639 54084509 := bstep (se 3 (by rfl) ⟨10140845, by rfl⟩ : syracuseStep 54084509 = 20281691) B20281691
theorem B21955499 : Blo 1875639 21955499 := bstep (se 1 (by rfl) ⟨16466624, by rfl⟩ : syracuseStep 21955499 = 32933249) B32933249
theorem B5342203 : Blo 1875639 5342203 := bstep (se 1 (by rfl) ⟨4006652, by rfl⟩ : syracuseStep 5342203 = 8013305) B8013305
theorem B6333767 : Blo 1875639 6333767 := bstep (se 1 (by rfl) ⟨4750325, by rfl⟩ : syracuseStep 6333767 = 9500651) B9500651
theorem B801072575 : Blo 1875639 801072575 := bstep (se 1 (by rfl) ⟨600804431, by rfl⟩ : syracuseStep 801072575 = 1201608863) B1201608863
theorem B6505919 : Blo 1875639 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B9496601 : Blo 1875639 9496601 := bstep (se 2 (by rfl) ⟨3561225, by rfl⟩ : syracuseStep 9496601 = 7122451) B7122451
theorem B260065637 : Blo 1875639 260065637 := bstep (se 4 (by rfl) ⟨24381153, by rfl⟩ : syracuseStep 260065637 = 48762307) B48762307
theorem B4278683 : Blo 1875639 4278683 := bstep (se 1 (by rfl) ⟨3209012, by rfl⟩ : syracuseStep 4278683 = 6418025) B6418025
theorem B12020345 : Blo 1875639 12020345 := bstep (se 2 (by rfl) ⟨4507629, by rfl⟩ : syracuseStep 12020345 = 9015259) B9015259
theorem B12021803 : Blo 1875639 12021803 := bstep (se 1 (by rfl) ⟨9016352, by rfl⟩ : syracuseStep 12021803 = 18032705) B18032705
theorem B6009671 : Blo 1875639 6009671 := bstep (se 1 (by rfl) ⟨4507253, by rfl⟩ : syracuseStep 6009671 = 9014507) B9014507
theorem B450671635 : Blo 1875639 450671635 := bstep (se 1 (by rfl) ⟨338003726, by rfl⟩ : syracuseStep 450671635 = 676007453) B676007453
theorem B30439145 : Blo 1875639 30439145 := bstep (se 2 (by rfl) ⟨11414679, by rfl⟩ : syracuseStep 30439145 = 22829359) B22829359
theorem B14251949 : Blo 1875639 14251949 := bstep (se 3 (by rfl) ⟨2672240, by rfl⟩ : syracuseStep 14251949 = 5344481) B5344481
theorem B16463963 : Blo 1875639 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B2373943 : Blo 1875639 2373943 := bstep (se 1 (by rfl) ⟨1780457, by rfl⟩ : syracuseStep 2373943 = 3560915) B3560915
theorem B3562031 : Blo 1875639 3562031 := bstep (se 1 (by rfl) ⟨2671523, by rfl⟩ : syracuseStep 3562031 = 5343047) B5343047
theorem B109697651 : Blo 1875639 109697651 := bstep (se 1 (by rfl) ⟨82273238, by rfl⟩ : syracuseStep 109697651 = 164546477) B164546477
theorem B6765263 : Blo 1875639 6765263 := bstep (se 1 (by rfl) ⟨5073947, by rfl⟩ : syracuseStep 6765263 = 10147895) B10147895
theorem B4569911 : Blo 1875639 4569911 := bstep (se 1 (by rfl) ⟨3427433, by rfl⟩ : syracuseStep 4569911 = 6854867) B6854867
theorem B1875739 : Blo 1875639 1875739 := bstep (se 1 (by rfl) ⟨1406804, by rfl⟩ : syracuseStep 1875739 = 2813609) B2813609
theorem B18038855 : Blo 1875639 18038855 := bstep (se 1 (by rfl) ⟨13529141, by rfl⟩ : syracuseStep 18038855 = 27058283) B27058283
theorem B20292763 : Blo 1875639 20292763 := bstep (se 1 (by rfl) ⟨15219572, by rfl⟩ : syracuseStep 20292763 = 30439145) B30439145
theorem B173377091 : Blo 1875639 173377091 := bstep (se 1 (by rfl) ⟨130032818, by rfl⟩ : syracuseStep 173377091 = 260065637) B260065637
theorem B73131767 : Blo 1875639 73131767 := bstep (se 1 (by rfl) ⟨54848825, by rfl⟩ : syracuseStep 73131767 = 109697651) B109697651
theorem B8013563 : Blo 1875639 8013563 := bstep (se 1 (by rfl) ⟨6010172, by rfl⟩ : syracuseStep 8013563 = 12020345) B12020345
theorem B16025789 : Blo 1875639 16025789 := bstep (se 3 (by rfl) ⟨3004835, by rfl⟩ : syracuseStep 16025789 = 6009671) B6009671
theorem B8014535 : Blo 1875639 8014535 := bstep (se 1 (by rfl) ⟨6010901, by rfl⟩ : syracuseStep 8014535 = 12021803) B12021803
theorem B40577735 : Blo 1875639 40577735 := bstep (se 1 (by rfl) ⟨30433301, by rfl⟩ : syracuseStep 40577735 = 60866603) B60866603
theorem B4008703 : Blo 1875639 4008703 := bstep (se 1 (by rfl) ⟨3006527, by rfl⟩ : syracuseStep 4008703 = 6013055) B6013055
theorem B3165257 : Blo 1875639 3165257 := bstep (se 2 (by rfl) ⟨1186971, by rfl⟩ : syracuseStep 3165257 = 2373943) B2373943
theorem B36056339 : Blo 1875639 36056339 := bstep (se 1 (by rfl) ⟨27042254, by rfl⟩ : syracuseStep 36056339 = 54084509) B54084509
theorem B4222511 : Blo 1875639 4222511 := bstep (se 1 (by rfl) ⟨3166883, by rfl⟩ : syracuseStep 4222511 = 6333767) B6333767
theorem B534048383 : Blo 1875639 534048383 := bstep (se 1 (by rfl) ⟨400536287, by rfl⟩ : syracuseStep 534048383 = 801072575) B801072575
theorem B4337279 : Blo 1875639 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B7122937 : Blo 1875639 7122937 := bstep (se 2 (by rfl) ⟨2671101, by rfl⟩ : syracuseStep 7122937 = 5342203) B5342203
theorem B600895513 : Blo 1875639 600895513 := bstep (se 2 (by rfl) ⟨225335817, by rfl⟩ : syracuseStep 600895513 = 450671635) B450671635
theorem B4510175 : Blo 1875639 4510175 := bstep (se 1 (by rfl) ⟨3382631, by rfl⟩ : syracuseStep 4510175 = 6765263) B6765263
theorem B14636999 : Blo 1875639 14636999 := bstep (se 1 (by rfl) ⟨10977749, by rfl⟩ : syracuseStep 14636999 = 21955499) B21955499
theorem B11409821 : Blo 1875639 11409821 := bstep (se 3 (by rfl) ⟨2139341, by rfl⟩ : syracuseStep 11409821 = 4278683) B4278683
theorem B9501299 : Blo 1875639 9501299 := bstep (se 1 (by rfl) ⟨7125974, by rfl⟩ : syracuseStep 9501299 = 14251949) B14251949
theorem B6331067 : Blo 1875639 6331067 := bstep (se 1 (by rfl) ⟨4748300, by rfl⟩ : syracuseStep 6331067 = 9496601) B9496601
theorem B10975975 : Blo 1875639 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B2374687 : Blo 1875639 2374687 := bstep (se 1 (by rfl) ⟨1781015, by rfl⟩ : syracuseStep 2374687 = 3562031) B3562031
theorem B3046607 : Blo 1875639 3046607 := bstep (se 1 (by rfl) ⟨2284955, by rfl⟩ : syracuseStep 3046607 = 4569911) B4569911
theorem B801194017 : Blo 1875639 801194017 := bstep (se 2 (by rfl) ⟨300447756, by rfl⟩ : syracuseStep 801194017 = 600895513) B600895513
theorem B12025903 : Blo 1875639 12025903 := bstep (se 1 (by rfl) ⟨9019427, by rfl⟩ : syracuseStep 12025903 = 18038855) B18038855
theorem B5342375 : Blo 1875639 5342375 := bstep (se 1 (by rfl) ⟨4006781, by rfl⟩ : syracuseStep 5342375 = 8013563) B8013563
theorem B12027133 : Blo 1875639 12027133 := bstep (se 3 (by rfl) ⟨2255087, by rfl⟩ : syracuseStep 12027133 = 4510175) B4510175
theorem B9757999 : Blo 1875639 9757999 := bstep (se 1 (by rfl) ⟨7318499, by rfl⟩ : syracuseStep 9757999 = 14636999) B14636999
theorem B10683859 : Blo 1875639 10683859 := bstep (se 1 (by rfl) ⟨8012894, by rfl⟩ : syracuseStep 10683859 = 16025789) B16025789
theorem B6334199 : Blo 1875639 6334199 := bstep (se 1 (by rfl) ⟨4750649, by rfl⟩ : syracuseStep 6334199 = 9501299) B9501299
theorem B4220711 : Blo 1875639 4220711 := bstep (se 1 (by rfl) ⟨3165533, by rfl⟩ : syracuseStep 4220711 = 6331067) B6331067
theorem B5343023 : Blo 1875639 5343023 := bstep (se 1 (by rfl) ⟨4007267, by rfl⟩ : syracuseStep 5343023 = 8014535) B8014535
theorem B27051823 : Blo 1875639 27051823 := bstep (se 1 (by rfl) ⟨20288867, by rfl⟩ : syracuseStep 27051823 = 40577735) B40577735
theorem B24037559 : Blo 1875639 24037559 := bstep (se 1 (by rfl) ⟨18028169, by rfl⟩ : syracuseStep 24037559 = 36056339) B36056339
theorem B9497249 : Blo 1875639 9497249 := bstep (se 2 (by rfl) ⟨3561468, by rfl⟩ : syracuseStep 9497249 = 7122937) B7122937
theorem B5344937 : Blo 1875639 5344937 := bstep (se 2 (by rfl) ⟨2004351, by rfl⟩ : syracuseStep 5344937 = 4008703) B4008703
theorem B115584727 : Blo 1875639 115584727 := bstep (se 1 (by rfl) ⟨86688545, by rfl⟩ : syracuseStep 115584727 = 173377091) B173377091
theorem B48754511 : Blo 1875639 48754511 := bstep (se 1 (by rfl) ⟨36565883, by rfl⟩ : syracuseStep 48754511 = 73131767) B73131767
theorem B3166249 : Blo 1875639 3166249 := bstep (se 2 (by rfl) ⟨1187343, by rfl⟩ : syracuseStep 3166249 = 2374687) B2374687
theorem B7606547 : Blo 1875639 7606547 := bstep (se 1 (by rfl) ⟨5704910, by rfl⟩ : syracuseStep 7606547 = 11409821) B11409821
theorem B2110171 : Blo 1875639 2110171 := bstep (se 1 (by rfl) ⟨1582628, by rfl⟩ : syracuseStep 2110171 = 3165257) B3165257
theorem B2815007 : Blo 1875639 2815007 := bstep (se 1 (by rfl) ⟨2111255, by rfl⟩ : syracuseStep 2815007 = 4222511) B4222511
theorem B58538533 : Blo 1875639 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B27057017 : Blo 1875639 27057017 := bstep (se 2 (by rfl) ⟨10146381, by rfl⟩ : syracuseStep 27057017 = 20292763) B20292763
theorem B2031071 : Blo 1875639 2031071 := bstep (se 1 (by rfl) ⟨1523303, by rfl⟩ : syracuseStep 2031071 = 3046607) B3046607
theorem B2891519 : Blo 1875639 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B356032255 : Blo 1875639 356032255 := bstep (se 1 (by rfl) ⟨267024191, by rfl⟩ : syracuseStep 356032255 = 534048383) B534048383
theorem B5071031 : Blo 1875639 5071031 := bstep (se 1 (by rfl) ⟨3803273, by rfl⟩ : syracuseStep 5071031 = 7606547) B7606547
theorem B1876671 : Blo 1875639 1876671 := bstep (se 1 (by rfl) ⟨1407503, by rfl⟩ : syracuseStep 1876671 = 2815007) B2815007
theorem B5416189 : Blo 1875639 5416189 := bstep (se 3 (by rfl) ⟨1015535, by rfl⟩ : syracuseStep 5416189 = 2031071) B2031071
theorem B16025039 : Blo 1875639 16025039 := bstep (se 1 (by rfl) ⟨12018779, by rfl⟩ : syracuseStep 16025039 = 24037559) B24037559
theorem B14248061 : Blo 1875639 14248061 := bstep (se 3 (by rfl) ⟨2671511, by rfl⟩ : syracuseStep 14248061 = 5343023) B5343023
theorem B4221665 : Blo 1875639 4221665 := bstep (se 2 (by rfl) ⟨1583124, by rfl⟩ : syracuseStep 4221665 = 3166249) B3166249
theorem B16034537 : Blo 1875639 16034537 := bstep (se 2 (by rfl) ⟨6012951, by rfl⟩ : syracuseStep 16034537 = 12025903) B12025903
theorem B2813561 : Blo 1875639 2813561 := bstep (se 2 (by rfl) ⟨1055085, by rfl⟩ : syracuseStep 2813561 = 2110171) B2110171
theorem B4222799 : Blo 1875639 4222799 := bstep (se 1 (by rfl) ⟨3167099, by rfl⟩ : syracuseStep 4222799 = 6334199) B6334199
theorem B2813807 : Blo 1875639 2813807 := bstep (se 1 (by rfl) ⟨2110355, by rfl⟩ : syracuseStep 2813807 = 4220711) B4220711
theorem B16036177 : Blo 1875639 16036177 := bstep (se 2 (by rfl) ⟨6013566, by rfl⟩ : syracuseStep 16036177 = 12027133) B12027133
theorem B154112969 : Blo 1875639 154112969 := bstep (se 2 (by rfl) ⟨57792363, by rfl⟩ : syracuseStep 154112969 = 115584727) B115584727
theorem B32503007 : Blo 1875639 32503007 := bstep (se 1 (by rfl) ⟨24377255, by rfl⟩ : syracuseStep 32503007 = 48754511) B48754511
theorem B1068258689 : Blo 1875639 1068258689 := bstep (se 2 (by rfl) ⟨400597008, by rfl⟩ : syracuseStep 1068258689 = 801194017) B801194017
theorem B78051377 : Blo 1875639 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B3561583 : Blo 1875639 3561583 := bstep (se 1 (by rfl) ⟨2671187, by rfl⟩ : syracuseStep 3561583 = 5342375) B5342375
theorem B52042661 : Blo 1875639 52042661 := bstep (se 4 (by rfl) ⟨4878999, by rfl⟩ : syracuseStep 52042661 = 9757999) B9757999
theorem B6331499 : Blo 1875639 6331499 := bstep (se 1 (by rfl) ⟨4748624, by rfl⟩ : syracuseStep 6331499 = 9497249) B9497249
theorem B18038011 : Blo 1875639 18038011 := bstep (se 1 (by rfl) ⟨13528508, by rfl⟩ : syracuseStep 18038011 = 27057017) B27057017
theorem B14245145 : Blo 1875639 14245145 := bstep (se 2 (by rfl) ⟨5341929, by rfl⟩ : syracuseStep 14245145 = 10683859) B10683859
theorem B474709673 : Blo 1875639 474709673 := bstep (se 2 (by rfl) ⟨178016127, by rfl⟩ : syracuseStep 474709673 = 356032255) B356032255
theorem B36069097 : Blo 1875639 36069097 := bstep (se 2 (by rfl) ⟨13525911, by rfl⟩ : syracuseStep 36069097 = 27051823) B27051823
theorem B3563291 : Blo 1875639 3563291 := bstep (se 1 (by rfl) ⟨2672468, by rfl⟩ : syracuseStep 3563291 = 5344937) B5344937
theorem B30842869 : Blo 1875639 30842869 := bstep (se 5 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 30842869 = 2891519) B2891519
theorem B21381569 : Blo 1875639 21381569 := bstep (se 2 (by rfl) ⟨8018088, by rfl⟩ : syracuseStep 21381569 = 16036177) B16036177
theorem B21668671 : Blo 1875639 21668671 := bstep (se 1 (by rfl) ⟨16251503, by rfl⟩ : syracuseStep 21668671 = 32503007) B32503007
theorem B712172459 : Blo 1875639 712172459 := bstep (se 1 (by rfl) ⟨534129344, by rfl⟩ : syracuseStep 712172459 = 1068258689) B1068258689
theorem B10683359 : Blo 1875639 10683359 := bstep (se 1 (by rfl) ⟨8012519, by rfl⟩ : syracuseStep 10683359 = 16025039) B16025039
theorem B28886341 : Blo 1875639 28886341 := bstep (se 4 (by rfl) ⟨2708094, by rfl⟩ : syracuseStep 28886341 = 5416189) B5416189
theorem B34695107 : Blo 1875639 34695107 := bstep (se 1 (by rfl) ⟨26021330, by rfl⟩ : syracuseStep 34695107 = 52042661) B52042661
theorem B4220999 : Blo 1875639 4220999 := bstep (se 1 (by rfl) ⟨3165749, by rfl⟩ : syracuseStep 4220999 = 6331499) B6331499
theorem B9496763 : Blo 1875639 9496763 := bstep (se 1 (by rfl) ⟨7122572, by rfl⟩ : syracuseStep 9496763 = 14245145) B14245145
theorem B9498707 : Blo 1875639 9498707 := bstep (se 1 (by rfl) ⟨7124030, by rfl⟩ : syracuseStep 9498707 = 14248061) B14248061
theorem B2814443 : Blo 1875639 2814443 := bstep (se 1 (by rfl) ⟨2110832, by rfl⟩ : syracuseStep 2814443 = 4221665) B4221665
theorem B48092129 : Blo 1875639 48092129 := bstep (se 2 (by rfl) ⟨18034548, by rfl⟩ : syracuseStep 48092129 = 36069097) B36069097
theorem B2815199 : Blo 1875639 2815199 := bstep (se 1 (by rfl) ⟨2111399, by rfl⟩ : syracuseStep 2815199 = 4222799) B4222799
theorem B3380687 : Blo 1875639 3380687 := bstep (se 1 (by rfl) ⟨2535515, by rfl⟩ : syracuseStep 3380687 = 5071031) B5071031
theorem B4748777 : Blo 1875639 4748777 := bstep (se 2 (by rfl) ⟨1780791, by rfl⟩ : syracuseStep 4748777 = 3561583) B3561583
theorem B102741979 : Blo 1875639 102741979 := bstep (se 1 (by rfl) ⟨77056484, by rfl⟩ : syracuseStep 102741979 = 154112969) B154112969
theorem B52034251 : Blo 1875639 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B24050681 : Blo 1875639 24050681 := bstep (se 2 (by rfl) ⟨9019005, by rfl⟩ : syracuseStep 24050681 = 18038011) B18038011
theorem B10689691 : Blo 1875639 10689691 := bstep (se 1 (by rfl) ⟨8017268, by rfl⟩ : syracuseStep 10689691 = 16034537) B16034537
theorem B9502109 : Blo 1875639 9502109 := bstep (se 3 (by rfl) ⟨1781645, by rfl⟩ : syracuseStep 9502109 = 3563291) B3563291
theorem B1875707 : Blo 1875639 1875707 := bstep (se 1 (by rfl) ⟨1406780, by rfl⟩ : syracuseStep 1875707 = 2813561) B2813561
theorem B316473115 : Blo 1875639 316473115 := bstep (se 1 (by rfl) ⟨237354836, by rfl⟩ : syracuseStep 316473115 = 474709673) B474709673
theorem B1875871 : Blo 1875639 1875871 := bstep (se 1 (by rfl) ⟨1406903, by rfl⟩ : syracuseStep 1875871 = 2813807) B2813807
theorem B41123825 : Blo 1875639 41123825 := bstep (se 2 (by rfl) ⟨15421434, by rfl⟩ : syracuseStep 41123825 = 30842869) B30842869
theorem B6332471 : Blo 1875639 6332471 := bstep (se 1 (by rfl) ⟨4749353, by rfl⟩ : syracuseStep 6332471 = 9498707) B9498707
theorem B14254379 : Blo 1875639 14254379 := bstep (se 1 (by rfl) ⟨10690784, by rfl⟩ : syracuseStep 14254379 = 21381569) B21381569
theorem B1876295 : Blo 1875639 1876295 := bstep (se 1 (by rfl) ⟨1407221, by rfl⟩ : syracuseStep 1876295 = 2814443) B2814443
theorem B1876799 : Blo 1875639 1876799 := bstep (se 1 (by rfl) ⟨1407599, by rfl⟩ : syracuseStep 1876799 = 2815199) B2815199
theorem B69379001 : Blo 1875639 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B2253791 : Blo 1875639 2253791 := bstep (se 1 (by rfl) ⟨1690343, by rfl⟩ : syracuseStep 2253791 = 3380687) B3380687
theorem B16033787 : Blo 1875639 16033787 := bstep (se 1 (by rfl) ⟨12025340, by rfl⟩ : syracuseStep 16033787 = 24050681) B24050681
theorem B6334739 : Blo 1875639 6334739 := bstep (se 1 (by rfl) ⟨4751054, by rfl⟩ : syracuseStep 6334739 = 9502109) B9502109
theorem B421964153 : Blo 1875639 421964153 := bstep (se 2 (by rfl) ⟨158236557, by rfl⟩ : syracuseStep 421964153 = 316473115) B316473115
theorem B136989305 : Blo 1875639 136989305 := bstep (se 2 (by rfl) ⟨51370989, by rfl⟩ : syracuseStep 136989305 = 102741979) B102741979
theorem B7122239 : Blo 1875639 7122239 := bstep (se 1 (by rfl) ⟨5341679, by rfl⟩ : syracuseStep 7122239 = 10683359) B10683359
theorem B3165851 : Blo 1875639 3165851 := bstep (se 1 (by rfl) ⟨2374388, by rfl⟩ : syracuseStep 3165851 = 4748777) B4748777
theorem B23130071 : Blo 1875639 23130071 := bstep (se 1 (by rfl) ⟨17347553, by rfl⟩ : syracuseStep 23130071 = 34695107) B34695107
theorem B2813999 : Blo 1875639 2813999 := bstep (se 1 (by rfl) ⟨2110499, by rfl⟩ : syracuseStep 2813999 = 4220999) B4220999
theorem B38515121 : Blo 1875639 38515121 := bstep (se 2 (by rfl) ⟨14443170, by rfl⟩ : syracuseStep 38515121 = 28886341) B28886341
theorem B27415883 : Blo 1875639 27415883 := bstep (se 1 (by rfl) ⟨20561912, by rfl⟩ : syracuseStep 27415883 = 41123825) B41123825
theorem B32061419 : Blo 1875639 32061419 := bstep (se 1 (by rfl) ⟨24046064, by rfl⟩ : syracuseStep 32061419 = 48092129) B48092129
theorem B28891561 : Blo 1875639 28891561 := bstep (se 2 (by rfl) ⟨10834335, by rfl⟩ : syracuseStep 28891561 = 21668671) B21668671
theorem B6331175 : Blo 1875639 6331175 := bstep (se 1 (by rfl) ⟨4748381, by rfl⟩ : syracuseStep 6331175 = 9496763) B9496763
theorem B14252921 : Blo 1875639 14252921 := bstep (se 2 (by rfl) ⟨5344845, by rfl⟩ : syracuseStep 14252921 = 10689691) B10689691
theorem B1899126557 : Blo 1875639 1899126557 := bstep (se 3 (by rfl) ⟨356086229, by rfl⟩ : syracuseStep 1899126557 = 712172459) B712172459
theorem B1875999 : Blo 1875639 1875999 := bstep (se 1 (by rfl) ⟨1406999, by rfl⟩ : syracuseStep 1875999 = 2813999) B2813999
theorem B9502919 : Blo 1875639 9502919 := bstep (se 1 (by rfl) ⟨7127189, by rfl⟩ : syracuseStep 9502919 = 14254379) B14254379
theorem B46252667 : Blo 1875639 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B18277255 : Blo 1875639 18277255 := bstep (se 1 (by rfl) ⟨13707941, by rfl⟩ : syracuseStep 18277255 = 27415883) B27415883
theorem B21374279 : Blo 1875639 21374279 := bstep (se 1 (by rfl) ⟨16030709, by rfl⟩ : syracuseStep 21374279 = 32061419) B32061419
theorem B91326203 : Blo 1875639 91326203 := bstep (se 1 (by rfl) ⟨68494652, by rfl⟩ : syracuseStep 91326203 = 136989305) B136989305
theorem B4220783 : Blo 1875639 4220783 := bstep (se 1 (by rfl) ⟨3165587, by rfl⟩ : syracuseStep 4220783 = 6331175) B6331175
theorem B1266084371 : Blo 1875639 1266084371 := bstep (se 1 (by rfl) ⟨949563278, by rfl⟩ : syracuseStep 1266084371 = 1899126557) B1899126557
theorem B15420047 : Blo 1875639 15420047 := bstep (se 1 (by rfl) ⟨11565035, by rfl⟩ : syracuseStep 15420047 = 23130071) B23130071
theorem B4221647 : Blo 1875639 4221647 := bstep (se 1 (by rfl) ⟨3166235, by rfl⟩ : syracuseStep 4221647 = 6332471) B6332471
theorem B25676747 : Blo 1875639 25676747 := bstep (se 1 (by rfl) ⟨19257560, by rfl⟩ : syracuseStep 25676747 = 38515121) B38515121
theorem B38522081 : Blo 1875639 38522081 := bstep (se 2 (by rfl) ⟨14445780, by rfl⟩ : syracuseStep 38522081 = 28891561) B28891561
theorem B4223159 : Blo 1875639 4223159 := bstep (se 1 (by rfl) ⟨3167369, by rfl⟩ : syracuseStep 4223159 = 6334739) B6334739
theorem B281309435 : Blo 1875639 281309435 := bstep (se 1 (by rfl) ⟨210982076, by rfl⟩ : syracuseStep 281309435 = 421964153) B421964153
theorem B4748159 : Blo 1875639 4748159 := bstep (se 1 (by rfl) ⟨3561119, by rfl⟩ : syracuseStep 4748159 = 7122239) B7122239
theorem B2110567 : Blo 1875639 2110567 := bstep (se 1 (by rfl) ⟨1582925, by rfl⟩ : syracuseStep 2110567 = 3165851) B3165851
theorem B6010109 : Blo 1875639 6010109 := bstep (se 3 (by rfl) ⟨1126895, by rfl⟩ : syracuseStep 6010109 = 2253791) B2253791
theorem B10689191 : Blo 1875639 10689191 := bstep (se 1 (by rfl) ⟨8016893, by rfl⟩ : syracuseStep 10689191 = 16033787) B16033787
theorem B9501947 : Blo 1875639 9501947 := bstep (se 1 (by rfl) ⟨7126460, by rfl⟩ : syracuseStep 9501947 = 14252921) B14252921
theorem B187539623 : Blo 1875639 187539623 := bstep (se 1 (by rfl) ⟨140654717, by rfl⟩ : syracuseStep 187539623 = 281309435) B281309435
theorem B4006739 : Blo 1875639 4006739 := bstep (se 1 (by rfl) ⟨3005054, by rfl⟩ : syracuseStep 4006739 = 6010109) B6010109
theorem B60884135 : Blo 1875639 60884135 := bstep (se 1 (by rfl) ⟨45663101, by rfl⟩ : syracuseStep 60884135 = 91326203) B91326203
theorem B123340445 : Blo 1875639 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B844056247 : Blo 1875639 844056247 := bstep (se 1 (by rfl) ⟨633042185, by rfl⟩ : syracuseStep 844056247 = 1266084371) B1266084371
theorem B6334631 : Blo 1875639 6334631 := bstep (se 1 (by rfl) ⟨4750973, by rfl⟩ : syracuseStep 6334631 = 9501947) B9501947
theorem B6335279 : Blo 1875639 6335279 := bstep (se 1 (by rfl) ⟨4751459, by rfl⟩ : syracuseStep 6335279 = 9502919) B9502919
theorem B3165439 : Blo 1875639 3165439 := bstep (se 1 (by rfl) ⟨2374079, by rfl⟩ : syracuseStep 3165439 = 4748159) B4748159
theorem B14249519 : Blo 1875639 14249519 := bstep (se 1 (by rfl) ⟨10687139, by rfl⟩ : syracuseStep 14249519 = 21374279) B21374279
theorem B2813855 : Blo 1875639 2813855 := bstep (se 1 (by rfl) ⟨2110391, by rfl⟩ : syracuseStep 2813855 = 4220783) B4220783
theorem B2814089 : Blo 1875639 2814089 := bstep (se 2 (by rfl) ⟨1055283, by rfl⟩ : syracuseStep 2814089 = 2110567) B2110567
theorem B41120125 : Blo 1875639 41120125 := bstep (se 3 (by rfl) ⟨7710023, by rfl⟩ : syracuseStep 41120125 = 15420047) B15420047
theorem B2814431 : Blo 1875639 2814431 := bstep (se 1 (by rfl) ⟨2110823, by rfl⟩ : syracuseStep 2814431 = 4221647) B4221647
theorem B17117831 : Blo 1875639 17117831 := bstep (se 1 (by rfl) ⟨12838373, by rfl⟩ : syracuseStep 17117831 = 25676747) B25676747
theorem B2815439 : Blo 1875639 2815439 := bstep (se 1 (by rfl) ⟨2111579, by rfl⟩ : syracuseStep 2815439 = 4223159) B4223159
theorem B24369673 : Blo 1875639 24369673 := bstep (se 2 (by rfl) ⟨9138627, by rfl⟩ : syracuseStep 24369673 = 18277255) B18277255
theorem B7126127 : Blo 1875639 7126127 := bstep (se 1 (by rfl) ⟨5344595, by rfl⟩ : syracuseStep 7126127 = 10689191) B10689191
theorem B25681387 : Blo 1875639 25681387 := bstep (se 1 (by rfl) ⟨19261040, by rfl⟩ : syracuseStep 25681387 = 38522081) B38522081
theorem B1876059 : Blo 1875639 1876059 := bstep (se 1 (by rfl) ⟨1407044, by rfl⟩ : syracuseStep 1876059 = 2814089) B2814089
theorem B125026415 : Blo 1875639 125026415 := bstep (se 1 (by rfl) ⟨93769811, by rfl⟩ : syracuseStep 125026415 = 187539623) B187539623
theorem B1876287 : Blo 1875639 1876287 := bstep (se 1 (by rfl) ⟨1407215, by rfl⟩ : syracuseStep 1876287 = 2814431) B2814431
theorem B11411887 : Blo 1875639 11411887 := bstep (se 1 (by rfl) ⟨8558915, by rfl⟩ : syracuseStep 11411887 = 17117831) B17117831
theorem B2671159 : Blo 1875639 2671159 := bstep (se 1 (by rfl) ⟨2003369, by rfl⟩ : syracuseStep 2671159 = 4006739) B4006739
theorem B1876959 : Blo 1875639 1876959 := bstep (se 1 (by rfl) ⟨1407719, by rfl⟩ : syracuseStep 1876959 = 2815439) B2815439
theorem B4220585 : Blo 1875639 4220585 := bstep (se 2 (by rfl) ⟨1582719, by rfl⟩ : syracuseStep 4220585 = 3165439) B3165439
theorem B32492897 : Blo 1875639 32492897 := bstep (se 2 (by rfl) ⟨12184836, by rfl⟩ : syracuseStep 32492897 = 24369673) B24369673
theorem B82226963 : Blo 1875639 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B4223087 : Blo 1875639 4223087 := bstep (se 1 (by rfl) ⟨3167315, by rfl⟩ : syracuseStep 4223087 = 6334631) B6334631
theorem B4223519 : Blo 1875639 4223519 := bstep (se 1 (by rfl) ⟨3167639, by rfl⟩ : syracuseStep 4223519 = 6335279) B6335279
theorem B9499679 : Blo 1875639 9499679 := bstep (se 1 (by rfl) ⟨7124759, by rfl⟩ : syracuseStep 9499679 = 14249519) B14249519
theorem B40589423 : Blo 1875639 40589423 := bstep (se 1 (by rfl) ⟨30442067, by rfl⟩ : syracuseStep 40589423 = 60884135) B60884135
theorem B34241849 : Blo 1875639 34241849 := bstep (se 2 (by rfl) ⟨12840693, by rfl⟩ : syracuseStep 34241849 = 25681387) B25681387
theorem B219307333 : Blo 1875639 219307333 := bstep (se 4 (by rfl) ⟨20560062, by rfl⟩ : syracuseStep 219307333 = 41120125) B41120125
theorem B4750751 : Blo 1875639 4750751 := bstep (se 1 (by rfl) ⟨3563063, by rfl⟩ : syracuseStep 4750751 = 7126127) B7126127
theorem B1125408329 : Blo 1875639 1125408329 := bstep (se 2 (by rfl) ⟨422028123, by rfl⟩ : syracuseStep 1125408329 = 844056247) B844056247
theorem B1875903 : Blo 1875639 1875903 := bstep (se 1 (by rfl) ⟨1406927, by rfl⟩ : syracuseStep 1875903 = 2813855) B2813855
theorem B6333119 : Blo 1875639 6333119 := bstep (se 1 (by rfl) ⟨4749839, by rfl⟩ : syracuseStep 6333119 = 9499679) B9499679
theorem B27059615 : Blo 1875639 27059615 := bstep (se 1 (by rfl) ⟨20294711, by rfl⟩ : syracuseStep 27059615 = 40589423) B40589423
theorem B21661931 : Blo 1875639 21661931 := bstep (se 1 (by rfl) ⟨16246448, by rfl⟩ : syracuseStep 21661931 = 32492897) B32492897
theorem B15215849 : Blo 1875639 15215849 := bstep (se 2 (by rfl) ⟨5705943, by rfl⟩ : syracuseStep 15215849 = 11411887) B11411887
theorem B2813723 : Blo 1875639 2813723 := bstep (se 1 (by rfl) ⟨2110292, by rfl⟩ : syracuseStep 2813723 = 4220585) B4220585
theorem B292409777 : Blo 1875639 292409777 := bstep (se 2 (by rfl) ⟨109653666, by rfl⟩ : syracuseStep 292409777 = 219307333) B219307333
theorem B22827899 : Blo 1875639 22827899 := bstep (se 1 (by rfl) ⟨17120924, by rfl⟩ : syracuseStep 22827899 = 34241849) B34241849
theorem B3167167 : Blo 1875639 3167167 := bstep (se 1 (by rfl) ⟨2375375, by rfl⟩ : syracuseStep 3167167 = 4750751) B4750751
theorem B54817975 : Blo 1875639 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B83350943 : Blo 1875639 83350943 := bstep (se 1 (by rfl) ⟨62513207, by rfl⟩ : syracuseStep 83350943 = 125026415) B125026415
theorem B2815391 : Blo 1875639 2815391 := bstep (se 1 (by rfl) ⟨2111543, by rfl⟩ : syracuseStep 2815391 = 4223087) B4223087
theorem B2815679 : Blo 1875639 2815679 := bstep (se 1 (by rfl) ⟨2111759, by rfl⟩ : syracuseStep 2815679 = 4223519) B4223519
theorem B3561545 : Blo 1875639 3561545 := bstep (se 2 (by rfl) ⟨1335579, by rfl⟩ : syracuseStep 3561545 = 2671159) B2671159
theorem B750272219 : Blo 1875639 750272219 := bstep (se 1 (by rfl) ⟨562704164, by rfl⟩ : syracuseStep 750272219 = 1125408329) B1125408329
theorem B55567295 : Blo 1875639 55567295 := bstep (se 1 (by rfl) ⟨41675471, by rfl⟩ : syracuseStep 55567295 = 83350943) B83350943
theorem B1876927 : Blo 1875639 1876927 := bstep (se 1 (by rfl) ⟨1407695, by rfl⟩ : syracuseStep 1876927 = 2815391) B2815391
theorem B18039743 : Blo 1875639 18039743 := bstep (se 1 (by rfl) ⟨13529807, by rfl⟩ : syracuseStep 18039743 = 27059615) B27059615
theorem B1877119 : Blo 1875639 1877119 := bstep (se 1 (by rfl) ⟨1407839, by rfl⟩ : syracuseStep 1877119 = 2815679) B2815679
theorem B73090633 : Blo 1875639 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B10143899 : Blo 1875639 10143899 := bstep (se 1 (by rfl) ⟨7607924, by rfl⟩ : syracuseStep 10143899 = 15215849) B15215849
theorem B500181479 : Blo 1875639 500181479 := bstep (se 1 (by rfl) ⟨375136109, by rfl⟩ : syracuseStep 500181479 = 750272219) B750272219
theorem B4222079 : Blo 1875639 4222079 := bstep (se 1 (by rfl) ⟨3166559, by rfl⟩ : syracuseStep 4222079 = 6333119) B6333119
theorem B57765149 : Blo 1875639 57765149 := bstep (se 3 (by rfl) ⟨10830965, by rfl⟩ : syracuseStep 57765149 = 21661931) B21661931
theorem B779759405 : Blo 1875639 779759405 := bstep (se 3 (by rfl) ⟨146204888, by rfl⟩ : syracuseStep 779759405 = 292409777) B292409777
theorem B4222889 : Blo 1875639 4222889 := bstep (se 2 (by rfl) ⟨1583583, by rfl⟩ : syracuseStep 4222889 = 3167167) B3167167
theorem B15218599 : Blo 1875639 15218599 := bstep (se 1 (by rfl) ⟨11413949, by rfl⟩ : syracuseStep 15218599 = 22827899) B22827899
theorem B2374363 : Blo 1875639 2374363 := bstep (se 1 (by rfl) ⟨1780772, by rfl⟩ : syracuseStep 2374363 = 3561545) B3561545
theorem B1875815 : Blo 1875639 1875815 := bstep (se 1 (by rfl) ⟨1406861, by rfl⟩ : syracuseStep 1875815 = 2813723) B2813723
theorem B37044863 : Blo 1875639 37044863 := bstep (se 1 (by rfl) ⟨27783647, by rfl⟩ : syracuseStep 37044863 = 55567295) B55567295
theorem B12026495 : Blo 1875639 12026495 := bstep (se 1 (by rfl) ⟨9019871, by rfl⟩ : syracuseStep 12026495 = 18039743) B18039743
theorem B97454177 : Blo 1875639 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B3165817 : Blo 1875639 3165817 := bstep (se 2 (by rfl) ⟨1187181, by rfl⟩ : syracuseStep 3165817 = 2374363) B2374363
theorem B6762599 : Blo 1875639 6762599 := bstep (se 1 (by rfl) ⟨5071949, by rfl⟩ : syracuseStep 6762599 = 10143899) B10143899
theorem B2814719 : Blo 1875639 2814719 := bstep (se 1 (by rfl) ⟨2111039, by rfl⟩ : syracuseStep 2814719 = 4222079) B4222079
theorem B2815259 : Blo 1875639 2815259 := bstep (se 1 (by rfl) ⟨2111444, by rfl⟩ : syracuseStep 2815259 = 4222889) B4222889
theorem B333454319 : Blo 1875639 333454319 := bstep (se 1 (by rfl) ⟨250090739, by rfl⟩ : syracuseStep 333454319 = 500181479) B500181479
theorem B38510099 : Blo 1875639 38510099 := bstep (se 1 (by rfl) ⟨28882574, by rfl⟩ : syracuseStep 38510099 = 57765149) B57765149
theorem B519839603 : Blo 1875639 519839603 := bstep (se 1 (by rfl) ⟨389879702, by rfl⟩ : syracuseStep 519839603 = 779759405) B779759405
theorem B20291465 : Blo 1875639 20291465 := bstep (se 2 (by rfl) ⟨7609299, by rfl⟩ : syracuseStep 20291465 = 15218599) B15218599
theorem B1876479 : Blo 1875639 1876479 := bstep (se 1 (by rfl) ⟨1407359, by rfl⟩ : syracuseStep 1876479 = 2814719) B2814719
theorem B1876839 : Blo 1875639 1876839 := bstep (se 1 (by rfl) ⟨1407629, by rfl⟩ : syracuseStep 1876839 = 2815259) B2815259
theorem B4221089 : Blo 1875639 4221089 := bstep (se 2 (by rfl) ⟨1582908, by rfl⟩ : syracuseStep 4221089 = 3165817) B3165817
theorem B13527643 : Blo 1875639 13527643 := bstep (se 1 (by rfl) ⟨10145732, by rfl⟩ : syracuseStep 13527643 = 20291465) B20291465
theorem B4508399 : Blo 1875639 4508399 := bstep (se 1 (by rfl) ⟨3381299, by rfl⟩ : syracuseStep 4508399 = 6762599) B6762599
theorem B222302879 : Blo 1875639 222302879 := bstep (se 1 (by rfl) ⟨166727159, by rfl⟩ : syracuseStep 222302879 = 333454319) B333454319
theorem B346559735 : Blo 1875639 346559735 := bstep (se 1 (by rfl) ⟨259919801, by rfl⟩ : syracuseStep 346559735 = 519839603) B519839603
theorem B24696575 : Blo 1875639 24696575 := bstep (se 1 (by rfl) ⟨18522431, by rfl⟩ : syracuseStep 24696575 = 37044863) B37044863
theorem B8017663 : Blo 1875639 8017663 := bstep (se 1 (by rfl) ⟨6013247, by rfl⟩ : syracuseStep 8017663 = 12026495) B12026495
theorem B64969451 : Blo 1875639 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B25673399 : Blo 1875639 25673399 := bstep (se 1 (by rfl) ⟨19255049, by rfl⟩ : syracuseStep 25673399 = 38510099) B38510099
theorem B148201919 : Blo 1875639 148201919 := bstep (se 1 (by rfl) ⟨111151439, by rfl⟩ : syracuseStep 148201919 = 222302879) B222302879
theorem B43312967 : Blo 1875639 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B17115599 : Blo 1875639 17115599 := bstep (se 1 (by rfl) ⟨12836699, by rfl⟩ : syracuseStep 17115599 = 25673399) B25673399
theorem B924159293 : Blo 1875639 924159293 := bstep (se 3 (by rfl) ⟨173279867, by rfl⟩ : syracuseStep 924159293 = 346559735) B346559735
theorem B2814059 : Blo 1875639 2814059 := bstep (se 1 (by rfl) ⟨2110544, by rfl⟩ : syracuseStep 2814059 = 4221089) B4221089
theorem B18036857 : Blo 1875639 18036857 := bstep (se 2 (by rfl) ⟨6763821, by rfl⟩ : syracuseStep 18036857 = 13527643) B13527643
theorem B16464383 : Blo 1875639 16464383 := bstep (se 1 (by rfl) ⟨12348287, by rfl⟩ : syracuseStep 16464383 = 24696575) B24696575
theorem B3005599 : Blo 1875639 3005599 := bstep (se 1 (by rfl) ⟨2254199, by rfl⟩ : syracuseStep 3005599 = 4508399) B4508399
theorem B10690217 : Blo 1875639 10690217 := bstep (se 2 (by rfl) ⟨4008831, by rfl⟩ : syracuseStep 10690217 = 8017663) B8017663
theorem B1876039 : Blo 1875639 1876039 := bstep (se 1 (by rfl) ⟨1407029, by rfl⟩ : syracuseStep 1876039 = 2814059) B2814059
theorem B4007465 : Blo 1875639 4007465 := bstep (se 2 (by rfl) ⟨1502799, by rfl⟩ : syracuseStep 4007465 = 3005599) B3005599
theorem B616106195 : Blo 1875639 616106195 := bstep (se 1 (by rfl) ⟨462079646, by rfl⟩ : syracuseStep 616106195 = 924159293) B924159293
theorem B98801279 : Blo 1875639 98801279 := bstep (se 1 (by rfl) ⟨74100959, by rfl⟩ : syracuseStep 98801279 = 148201919) B148201919
theorem B28875311 : Blo 1875639 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B12024571 : Blo 1875639 12024571 := bstep (se 1 (by rfl) ⟨9018428, by rfl⟩ : syracuseStep 12024571 = 18036857) B18036857
theorem B11410399 : Blo 1875639 11410399 := bstep (se 1 (by rfl) ⟨8557799, by rfl⟩ : syracuseStep 11410399 = 17115599) B17115599
theorem B10976255 : Blo 1875639 10976255 := bstep (se 1 (by rfl) ⟨8232191, by rfl⟩ : syracuseStep 10976255 = 16464383) B16464383
theorem B7126811 : Blo 1875639 7126811 := bstep (se 1 (by rfl) ⟨5345108, by rfl⟩ : syracuseStep 7126811 = 10690217) B10690217
theorem B16032761 : Blo 1875639 16032761 := bstep (se 2 (by rfl) ⟨6012285, by rfl⟩ : syracuseStep 16032761 = 12024571) B12024571
theorem B2671643 : Blo 1875639 2671643 := bstep (se 1 (by rfl) ⟨2003732, by rfl⟩ : syracuseStep 2671643 = 4007465) B4007465
theorem B7317503 : Blo 1875639 7317503 := bstep (se 1 (by rfl) ⟨5488127, by rfl⟩ : syracuseStep 7317503 = 10976255) B10976255
theorem B65867519 : Blo 1875639 65867519 := bstep (se 1 (by rfl) ⟨49400639, by rfl⟩ : syracuseStep 65867519 = 98801279) B98801279
theorem B60855461 : Blo 1875639 60855461 := bstep (se 4 (by rfl) ⟨5705199, by rfl⟩ : syracuseStep 60855461 = 11410399) B11410399
theorem B410737463 : Blo 1875639 410737463 := bstep (se 1 (by rfl) ⟨308053097, by rfl⟩ : syracuseStep 410737463 = 616106195) B616106195
theorem B19250207 : Blo 1875639 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B4751207 : Blo 1875639 4751207 := bstep (se 1 (by rfl) ⟨3563405, by rfl⟩ : syracuseStep 4751207 = 7126811) B7126811
theorem B175646717 : Blo 1875639 175646717 := bstep (se 3 (by rfl) ⟨32933759, by rfl⟩ : syracuseStep 175646717 = 65867519) B65867519
theorem B40570307 : Blo 1875639 40570307 := bstep (se 1 (by rfl) ⟨30427730, by rfl⟩ : syracuseStep 40570307 = 60855461) B60855461
theorem B4878335 : Blo 1875639 4878335 := bstep (se 1 (by rfl) ⟨3658751, by rfl⟩ : syracuseStep 4878335 = 7317503) B7317503
theorem B12833471 : Blo 1875639 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B3167471 : Blo 1875639 3167471 := bstep (se 1 (by rfl) ⟨2375603, by rfl⟩ : syracuseStep 3167471 = 4751207) B4751207
theorem B7124381 : Blo 1875639 7124381 := bstep (se 3 (by rfl) ⟨1335821, by rfl⟩ : syracuseStep 7124381 = 2671643) B2671643
theorem B10688507 : Blo 1875639 10688507 := bstep (se 1 (by rfl) ⟨8016380, by rfl⟩ : syracuseStep 10688507 = 16032761) B16032761
theorem B273824975 : Blo 1875639 273824975 := bstep (se 1 (by rfl) ⟨205368731, by rfl⟩ : syracuseStep 273824975 = 410737463) B410737463
theorem B117097811 : Blo 1875639 117097811 := bstep (se 1 (by rfl) ⟨87823358, by rfl⟩ : syracuseStep 117097811 = 175646717) B175646717
theorem B8555647 : Blo 1875639 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B27046871 : Blo 1875639 27046871 := bstep (se 1 (by rfl) ⟨20285153, by rfl⟩ : syracuseStep 27046871 = 40570307) B40570307
theorem B2111647 : Blo 1875639 2111647 := bstep (se 1 (by rfl) ⟨1583735, by rfl⟩ : syracuseStep 2111647 = 3167471) B3167471
theorem B4749587 : Blo 1875639 4749587 := bstep (se 1 (by rfl) ⟨3562190, by rfl⟩ : syracuseStep 4749587 = 7124381) B7124381
theorem B7125671 : Blo 1875639 7125671 := bstep (se 1 (by rfl) ⟨5344253, by rfl⟩ : syracuseStep 7125671 = 10688507) B10688507
theorem B182549983 : Blo 1875639 182549983 := bstep (se 1 (by rfl) ⟨136912487, by rfl⟩ : syracuseStep 182549983 = 273824975) B273824975
theorem B3252223 : Blo 1875639 3252223 := bstep (se 1 (by rfl) ⟨2439167, by rfl⟩ : syracuseStep 3252223 = 4878335) B4878335
theorem B18031247 : Blo 1875639 18031247 := bstep (se 1 (by rfl) ⟨13523435, by rfl⟩ : syracuseStep 18031247 = 27046871) B27046871
theorem B4336297 : Blo 1875639 4336297 := bstep (se 2 (by rfl) ⟨1626111, by rfl⟩ : syracuseStep 4336297 = 3252223) B3252223
theorem B78065207 : Blo 1875639 78065207 := bstep (se 1 (by rfl) ⟨58548905, by rfl⟩ : syracuseStep 78065207 = 117097811) B117097811
theorem B11407529 : Blo 1875639 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B3166391 : Blo 1875639 3166391 := bstep (se 1 (by rfl) ⟨2374793, by rfl⟩ : syracuseStep 3166391 = 4749587) B4749587
theorem B2815529 : Blo 1875639 2815529 := bstep (se 2 (by rfl) ⟨1055823, by rfl⟩ : syracuseStep 2815529 = 2111647) B2111647
theorem B4750447 : Blo 1875639 4750447 := bstep (se 1 (by rfl) ⟨3562835, by rfl⟩ : syracuseStep 4750447 = 7125671) B7125671
theorem B243399977 : Blo 1875639 243399977 := bstep (se 2 (by rfl) ⟨91274991, by rfl⟩ : syracuseStep 243399977 = 182549983) B182549983
theorem B23126917 : Blo 1875639 23126917 := bstep (se 4 (by rfl) ⟨2168148, by rfl⟩ : syracuseStep 23126917 = 4336297) B4336297
theorem B1877019 : Blo 1875639 1877019 := bstep (se 1 (by rfl) ⟨1407764, by rfl⟩ : syracuseStep 1877019 = 2815529) B2815529
theorem B6333929 : Blo 1875639 6333929 := bstep (se 2 (by rfl) ⟨2375223, by rfl⟩ : syracuseStep 6333929 = 4750447) B4750447
theorem B7605019 : Blo 1875639 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B12020831 : Blo 1875639 12020831 := bstep (se 1 (by rfl) ⟨9015623, by rfl⟩ : syracuseStep 12020831 = 18031247) B18031247
theorem B2110927 : Blo 1875639 2110927 := bstep (se 1 (by rfl) ⟨1583195, by rfl⟩ : syracuseStep 2110927 = 3166391) B3166391
theorem B162266651 : Blo 1875639 162266651 := bstep (se 1 (by rfl) ⟨121699988, by rfl⟩ : syracuseStep 162266651 = 243399977) B243399977
theorem B52043471 : Blo 1875639 52043471 := bstep (se 1 (by rfl) ⟨39032603, by rfl⟩ : syracuseStep 52043471 = 78065207) B78065207
theorem B30835889 : Blo 1875639 30835889 := bstep (se 2 (by rfl) ⟨11563458, by rfl⟩ : syracuseStep 30835889 = 23126917) B23126917
theorem B40560101 : Blo 1875639 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B8013887 : Blo 1875639 8013887 := bstep (se 1 (by rfl) ⟨6010415, by rfl⟩ : syracuseStep 8013887 = 12020831) B12020831
theorem B108177767 : Blo 1875639 108177767 := bstep (se 1 (by rfl) ⟨81133325, by rfl⟩ : syracuseStep 108177767 = 162266651) B162266651
theorem B34695647 : Blo 1875639 34695647 := bstep (se 1 (by rfl) ⟨26021735, by rfl⟩ : syracuseStep 34695647 = 52043471) B52043471
theorem B4222619 : Blo 1875639 4222619 := bstep (se 1 (by rfl) ⟨3166964, by rfl⟩ : syracuseStep 4222619 = 6333929) B6333929
theorem B2814569 : Blo 1875639 2814569 := bstep (se 2 (by rfl) ⟨1055463, by rfl⟩ : syracuseStep 2814569 = 2110927) B2110927
theorem B1876379 : Blo 1875639 1876379 := bstep (se 1 (by rfl) ⟨1407284, by rfl⟩ : syracuseStep 1876379 = 2814569) B2814569
theorem B5342591 : Blo 1875639 5342591 := bstep (se 1 (by rfl) ⟨4006943, by rfl⟩ : syracuseStep 5342591 = 8013887) B8013887
theorem B20557259 : Blo 1875639 20557259 := bstep (se 1 (by rfl) ⟨15417944, by rfl⟩ : syracuseStep 20557259 = 30835889) B30835889
theorem B72118511 : Blo 1875639 72118511 := bstep (se 1 (by rfl) ⟨54088883, by rfl⟩ : syracuseStep 72118511 = 108177767) B108177767
theorem B23130431 : Blo 1875639 23130431 := bstep (se 1 (by rfl) ⟨17347823, by rfl⟩ : syracuseStep 23130431 = 34695647) B34695647
theorem B2815079 : Blo 1875639 2815079 := bstep (se 1 (by rfl) ⟨2111309, by rfl⟩ : syracuseStep 2815079 = 4222619) B4222619
theorem B27040067 : Blo 1875639 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B48079007 : Blo 1875639 48079007 := bstep (se 1 (by rfl) ⟨36059255, by rfl⟩ : syracuseStep 48079007 = 72118511) B72118511
theorem B1876719 : Blo 1875639 1876719 := bstep (se 1 (by rfl) ⟨1407539, by rfl⟩ : syracuseStep 1876719 = 2815079) B2815079
theorem B15420287 : Blo 1875639 15420287 := bstep (se 1 (by rfl) ⟨11565215, by rfl⟩ : syracuseStep 15420287 = 23130431) B23130431
theorem B18026711 : Blo 1875639 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B3561727 : Blo 1875639 3561727 := bstep (se 1 (by rfl) ⟨2671295, by rfl⟩ : syracuseStep 3561727 = 5342591) B5342591
theorem B13704839 : Blo 1875639 13704839 := bstep (se 1 (by rfl) ⟨10278629, by rfl⟩ : syracuseStep 13704839 = 20557259) B20557259
theorem B12017807 : Blo 1875639 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B9136559 : Blo 1875639 9136559 := bstep (se 1 (by rfl) ⟨6852419, by rfl⟩ : syracuseStep 9136559 = 13704839) B13704839
theorem B32052671 : Blo 1875639 32052671 := bstep (se 1 (by rfl) ⟨24039503, by rfl⟩ : syracuseStep 32052671 = 48079007) B48079007
theorem B4748969 : Blo 1875639 4748969 := bstep (se 2 (by rfl) ⟨1780863, by rfl⟩ : syracuseStep 4748969 = 3561727) B3561727
theorem B10280191 : Blo 1875639 10280191 := bstep (se 1 (by rfl) ⟨7710143, by rfl⟩ : syracuseStep 10280191 = 15420287) B15420287
theorem B8011871 : Blo 1875639 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B24364157 : Blo 1875639 24364157 := bstep (se 3 (by rfl) ⟨4568279, by rfl⟩ : syracuseStep 24364157 = 9136559) B9136559
theorem B13706921 : Blo 1875639 13706921 := bstep (se 2 (by rfl) ⟨5140095, by rfl⟩ : syracuseStep 13706921 = 10280191) B10280191
theorem B21368447 : Blo 1875639 21368447 := bstep (se 1 (by rfl) ⟨16026335, by rfl⟩ : syracuseStep 21368447 = 32052671) B32052671
theorem B3165979 : Blo 1875639 3165979 := bstep (se 1 (by rfl) ⟨2374484, by rfl⟩ : syracuseStep 3165979 = 4748969) B4748969
theorem B5341247 : Blo 1875639 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B64971085 : Blo 1875639 64971085 := bstep (se 3 (by rfl) ⟨12182078, by rfl⟩ : syracuseStep 64971085 = 24364157) B24364157
theorem B4221305 : Blo 1875639 4221305 := bstep (se 2 (by rfl) ⟨1582989, by rfl⟩ : syracuseStep 4221305 = 3165979) B3165979
theorem B9137947 : Blo 1875639 9137947 := bstep (se 1 (by rfl) ⟨6853460, by rfl⟩ : syracuseStep 9137947 = 13706921) B13706921
theorem B14245631 : Blo 1875639 14245631 := bstep (se 1 (by rfl) ⟨10684223, by rfl⟩ : syracuseStep 14245631 = 21368447) B21368447
theorem B12183929 : Blo 1875639 12183929 := bstep (se 2 (by rfl) ⟨4568973, by rfl⟩ : syracuseStep 12183929 = 9137947) B9137947
theorem B9497087 : Blo 1875639 9497087 := bstep (se 1 (by rfl) ⟨7122815, by rfl⟩ : syracuseStep 9497087 = 14245631) B14245631
theorem B2814203 : Blo 1875639 2814203 := bstep (se 1 (by rfl) ⟨2110652, by rfl⟩ : syracuseStep 2814203 = 4221305) B4221305
theorem B3560831 : Blo 1875639 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B86628113 : Blo 1875639 86628113 := bstep (se 2 (by rfl) ⟨32485542, by rfl⟩ : syracuseStep 86628113 = 64971085) B64971085
theorem B1876135 : Blo 1875639 1876135 := bstep (se 1 (by rfl) ⟨1407101, by rfl⟩ : syracuseStep 1876135 = 2814203) B2814203
theorem B8122619 : Blo 1875639 8122619 := bstep (se 1 (by rfl) ⟨6091964, by rfl⟩ : syracuseStep 8122619 = 12183929) B12183929
theorem B2373887 : Blo 1875639 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B57752075 : Blo 1875639 57752075 := bstep (se 1 (by rfl) ⟨43314056, by rfl⟩ : syracuseStep 57752075 = 86628113) B86628113
theorem B6331391 : Blo 1875639 6331391 := bstep (se 1 (by rfl) ⟨4748543, by rfl⟩ : syracuseStep 6331391 = 9497087) B9497087
theorem B21660317 : Blo 1875639 21660317 := bstep (se 3 (by rfl) ⟨4061309, by rfl⟩ : syracuseStep 21660317 = 8122619) B8122619
theorem B4220927 : Blo 1875639 4220927 := bstep (se 1 (by rfl) ⟨3165695, by rfl⟩ : syracuseStep 4220927 = 6331391) B6331391
theorem B154005533 : Blo 1875639 154005533 := bstep (se 3 (by rfl) ⟨28876037, by rfl⟩ : syracuseStep 154005533 = 57752075) B57752075
theorem B6330365 : Blo 1875639 6330365 := bstep (se 3 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 6330365 = 2373887) B2373887
theorem B102670355 : Blo 1875639 102670355 := bstep (se 1 (by rfl) ⟨77002766, by rfl⟩ : syracuseStep 102670355 = 154005533) B154005533
theorem B4220243 : Blo 1875639 4220243 := bstep (se 1 (by rfl) ⟨3165182, by rfl⟩ : syracuseStep 4220243 = 6330365) B6330365
theorem B2813951 : Blo 1875639 2813951 := bstep (se 1 (by rfl) ⟨2110463, by rfl⟩ : syracuseStep 2813951 = 4220927) B4220927
theorem B14440211 : Blo 1875639 14440211 := bstep (se 1 (by rfl) ⟨10830158, by rfl⟩ : syracuseStep 14440211 = 21660317) B21660317
theorem B9626807 : Blo 1875639 9626807 := bstep (se 1 (by rfl) ⟨7220105, by rfl⟩ : syracuseStep 9626807 = 14440211) B14440211
theorem B1875967 : Blo 1875639 1875967 := bstep (se 1 (by rfl) ⟨1406975, by rfl⟩ : syracuseStep 1875967 = 2813951) B2813951
theorem B273787613 : Blo 1875639 273787613 := bstep (se 3 (by rfl) ⟨51335177, by rfl⟩ : syracuseStep 273787613 = 102670355) B102670355
theorem B2813495 : Blo 1875639 2813495 := bstep (se 1 (by rfl) ⟨2110121, by rfl⟩ : syracuseStep 2813495 = 4220243) B4220243
theorem B25671485 : Blo 1875639 25671485 := bstep (se 3 (by rfl) ⟨4813403, by rfl⟩ : syracuseStep 25671485 = 9626807) B9626807
theorem B182525075 : Blo 1875639 182525075 := bstep (se 1 (by rfl) ⟨136893806, by rfl⟩ : syracuseStep 182525075 = 273787613) B273787613
theorem B1875663 : Blo 1875639 1875663 := bstep (se 1 (by rfl) ⟨1406747, by rfl⟩ : syracuseStep 1875663 = 2813495) B2813495
theorem B17114323 : Blo 1875639 17114323 := bstep (se 1 (by rfl) ⟨12835742, by rfl⟩ : syracuseStep 17114323 = 25671485) B25671485
theorem B121683383 : Blo 1875639 121683383 := bstep (se 1 (by rfl) ⟨91262537, by rfl⟩ : syracuseStep 121683383 = 182525075) B182525075
theorem B22819097 : Blo 1875639 22819097 := bstep (se 2 (by rfl) ⟨8557161, by rfl⟩ : syracuseStep 22819097 = 17114323) B17114323
theorem B81122255 : Blo 1875639 81122255 := bstep (se 1 (by rfl) ⟨60841691, by rfl⟩ : syracuseStep 81122255 = 121683383) B121683383
theorem B15212731 : Blo 1875639 15212731 := bstep (se 1 (by rfl) ⟨11409548, by rfl⟩ : syracuseStep 15212731 = 22819097) B22819097
theorem B54081503 : Blo 1875639 54081503 := bstep (se 1 (by rfl) ⟨40561127, by rfl⟩ : syracuseStep 54081503 = 81122255) B81122255
theorem B20283641 : Blo 1875639 20283641 := bstep (se 2 (by rfl) ⟨7606365, by rfl⟩ : syracuseStep 20283641 = 15212731) B15212731
theorem B36054335 : Blo 1875639 36054335 := bstep (se 1 (by rfl) ⟨27040751, by rfl⟩ : syracuseStep 36054335 = 54081503) B54081503
theorem B24036223 : Blo 1875639 24036223 := bstep (se 1 (by rfl) ⟨18027167, by rfl⟩ : syracuseStep 24036223 = 36054335) B36054335
theorem B13522427 : Blo 1875639 13522427 := bstep (se 1 (by rfl) ⟨10141820, by rfl⟩ : syracuseStep 13522427 = 20283641) B20283641
theorem B32048297 : Blo 1875639 32048297 := bstep (se 2 (by rfl) ⟨12018111, by rfl⟩ : syracuseStep 32048297 = 24036223) B24036223
theorem B9014951 : Blo 1875639 9014951 := bstep (se 1 (by rfl) ⟨6761213, by rfl⟩ : syracuseStep 9014951 = 13522427) B13522427
theorem B21365531 : Blo 1875639 21365531 := bstep (se 1 (by rfl) ⟨16024148, by rfl⟩ : syracuseStep 21365531 = 32048297) B32048297
theorem B6009967 : Blo 1875639 6009967 := bstep (se 1 (by rfl) ⟨4507475, by rfl⟩ : syracuseStep 6009967 = 9014951) B9014951
theorem B8013289 : Blo 1875639 8013289 := bstep (se 2 (by rfl) ⟨3004983, by rfl⟩ : syracuseStep 8013289 = 6009967) B6009967
theorem B14243687 : Blo 1875639 14243687 := bstep (se 1 (by rfl) ⟨10682765, by rfl⟩ : syracuseStep 14243687 = 21365531) B21365531
theorem B9495791 : Blo 1875639 9495791 := bstep (se 1 (by rfl) ⟨7121843, by rfl⟩ : syracuseStep 9495791 = 14243687) B14243687
theorem B10684385 : Blo 1875639 10684385 := bstep (se 2 (by rfl) ⟨4006644, by rfl⟩ : syracuseStep 10684385 = 8013289) B8013289
theorem B7122923 : Blo 1875639 7122923 := bstep (se 1 (by rfl) ⟨5342192, by rfl⟩ : syracuseStep 7122923 = 10684385) B10684385
theorem B6330527 : Blo 1875639 6330527 := bstep (se 1 (by rfl) ⟨4747895, by rfl⟩ : syracuseStep 6330527 = 9495791) B9495791
theorem B4220351 : Blo 1875639 4220351 := bstep (se 1 (by rfl) ⟨3165263, by rfl⟩ : syracuseStep 4220351 = 6330527) B6330527
theorem B4748615 : Blo 1875639 4748615 := bstep (se 1 (by rfl) ⟨3561461, by rfl⟩ : syracuseStep 4748615 = 7122923) B7122923
theorem B3165743 : Blo 1875639 3165743 := bstep (se 1 (by rfl) ⟨2374307, by rfl⟩ : syracuseStep 3165743 = 4748615) B4748615
theorem B2813567 : Blo 1875639 2813567 := bstep (se 1 (by rfl) ⟨2110175, by rfl⟩ : syracuseStep 2813567 = 4220351) B4220351
theorem B2110495 : Blo 1875639 2110495 := bstep (se 1 (by rfl) ⟨1582871, by rfl⟩ : syracuseStep 2110495 = 3165743) B3165743
theorem B1875711 : Blo 1875639 1875711 := bstep (se 1 (by rfl) ⟨1406783, by rfl⟩ : syracuseStep 1875711 = 2813567) B2813567
theorem B2813993 : Blo 1875639 2813993 := bstep (se 2 (by rfl) ⟨1055247, by rfl⟩ : syracuseStep 2813993 = 2110495) B2110495
theorem B1875995 : Blo 1875639 1875995 := bstep (se 1 (by rfl) ⟨1406996, by rfl⟩ : syracuseStep 1875995 = 2813993) B2813993

theorem C0 (j : ℕ) (h1 : 468909 ≤ j) (h2 : j ≤ 469284) : Blo 1875639 (4 * j + 3) := by
  interval_cases j
  · exact B1875639
  · exact B1875643
  · exact B1875647
  · exact B1875651
  · exact B1875655
  · exact B1875659
  · exact B1875663
  · exact B1875667
  · exact B1875671
  · exact B1875675
  · exact B1875679
  · exact B1875683
  · exact B1875687
  · exact B1875691
  · exact B1875695
  · exact B1875699
  · exact B1875703
  · exact B1875707
  · exact B1875711
  · exact B1875715
  · exact B1875719
  · exact B1875723
  · exact B1875727
  · exact B1875731
  · exact B1875735
  · exact B1875739
  · exact B1875743
  · exact B1875747
  · exact B1875751
  · exact B1875755
  · exact B1875759
  · exact B1875763
  · exact B1875767
  · exact B1875771
  · exact B1875775
  · exact B1875779
  · exact B1875783
  · exact B1875787
  · exact B1875791
  · exact B1875795
  · exact B1875799
  · exact B1875803
  · exact B1875807
  · exact B1875811
  · exact B1875815
  · exact B1875819
  · exact B1875823
  · exact B1875827
  · exact B1875831
  · exact B1875835
  · exact B1875839
  · exact B1875843
  · exact B1875847
  · exact B1875851
  · exact B1875855
  · exact B1875859
  · exact B1875863
  · exact B1875867
  · exact B1875871
  · exact B1875875
  · exact B1875879
  · exact B1875883
  · exact B1875887
  · exact B1875891
  · exact B1875895
  · exact B1875899
  · exact B1875903
  · exact B1875907
  · exact B1875911
  · exact B1875915
  · exact B1875919
  · exact B1875923
  · exact B1875927
  · exact B1875931
  · exact B1875935
  · exact B1875939
  · exact B1875943
  · exact B1875947
  · exact B1875951
  · exact B1875955
  · exact B1875959
  · exact B1875963
  · exact B1875967
  · exact B1875971
  · exact B1875975
  · exact B1875979
  · exact B1875983
  · exact B1875987
  · exact B1875991
  · exact B1875995
  · exact B1875999
  · exact B1876003
  · exact B1876007
  · exact B1876011
  · exact B1876015
  · exact B1876019
  · exact B1876023
  · exact B1876027
  · exact B1876031
  · exact B1876035
  · exact B1876039
  · exact B1876043
  · exact B1876047
  · exact B1876051
  · exact B1876055
  · exact B1876059
  · exact B1876063
  · exact B1876067
  · exact B1876071
  · exact B1876075
  · exact B1876079
  · exact B1876083
  · exact B1876087
  · exact B1876091
  · exact B1876095
  · exact B1876099
  · exact B1876103
  · exact B1876107
  · exact B1876111
  · exact B1876115
  · exact B1876119
  · exact B1876123
  · exact B1876127
  · exact B1876131
  · exact B1876135
  · exact B1876139
  · exact B1876143
  · exact B1876147
  · exact B1876151
  · exact B1876155
  · exact B1876159
  · exact B1876163
  · exact B1876167
  · exact B1876171
  · exact B1876175
  · exact B1876179
  · exact B1876183
  · exact B1876187
  · exact B1876191
  · exact B1876195
  · exact B1876199
  · exact B1876203
  · exact B1876207
  · exact B1876211
  · exact B1876215
  · exact B1876219
  · exact B1876223
  · exact B1876227
  · exact B1876231
  · exact B1876235
  · exact B1876239
  · exact B1876243
  · exact B1876247
  · exact B1876251
  · exact B1876255
  · exact B1876259
  · exact B1876263
  · exact B1876267
  · exact B1876271
  · exact B1876275
  · exact B1876279
  · exact B1876283
  · exact B1876287
  · exact B1876291
  · exact B1876295
  · exact B1876299
  · exact B1876303
  · exact B1876307
  · exact B1876311
  · exact B1876315
  · exact B1876319
  · exact B1876323
  · exact B1876327
  · exact B1876331
  · exact B1876335
  · exact B1876339
  · exact B1876343
  · exact B1876347
  · exact B1876351
  · exact B1876355
  · exact B1876359
  · exact B1876363
  · exact B1876367
  · exact B1876371
  · exact B1876375
  · exact B1876379
  · exact B1876383
  · exact B1876387
  · exact B1876391
  · exact B1876395
  · exact B1876399
  · exact B1876403
  · exact B1876407
  · exact B1876411
  · exact B1876415
  · exact B1876419
  · exact B1876423
  · exact B1876427
  · exact B1876431
  · exact B1876435
  · exact B1876439
  · exact B1876443
  · exact B1876447
  · exact B1876451
  · exact B1876455
  · exact B1876459
  · exact B1876463
  · exact B1876467
  · exact B1876471
  · exact B1876475
  · exact B1876479
  · exact B1876483
  · exact B1876487
  · exact B1876491
  · exact B1876495
  · exact B1876499
  · exact B1876503
  · exact B1876507
  · exact B1876511
  · exact B1876515
  · exact B1876519
  · exact B1876523
  · exact B1876527
  · exact B1876531
  · exact B1876535
  · exact B1876539
  · exact B1876543
  · exact B1876547
  · exact B1876551
  · exact B1876555
  · exact B1876559
  · exact B1876563
  · exact B1876567
  · exact B1876571
  · exact B1876575
  · exact B1876579
  · exact B1876583
  · exact B1876587
  · exact B1876591
  · exact B1876595
  · exact B1876599
  · exact B1876603
  · exact B1876607
  · exact B1876611
  · exact B1876615
  · exact B1876619
  · exact B1876623
  · exact B1876627
  · exact B1876631
  · exact B1876635
  · exact B1876639
  · exact B1876643
  · exact B1876647
  · exact B1876651
  · exact B1876655
  · exact B1876659
  · exact B1876663
  · exact B1876667
  · exact B1876671
  · exact B1876675
  · exact B1876679
  · exact B1876683
  · exact B1876687
  · exact B1876691
  · exact B1876695
  · exact B1876699
  · exact B1876703
  · exact B1876707
  · exact B1876711
  · exact B1876715
  · exact B1876719
  · exact B1876723
  · exact B1876727
  · exact B1876731
  · exact B1876735
  · exact B1876739
  · exact B1876743
  · exact B1876747
  · exact B1876751
  · exact B1876755
  · exact B1876759
  · exact B1876763
  · exact B1876767
  · exact B1876771
  · exact B1876775
  · exact B1876779
  · exact B1876783
  · exact B1876787
  · exact B1876791
  · exact B1876795
  · exact B1876799
  · exact B1876803
  · exact B1876807
  · exact B1876811
  · exact B1876815
  · exact B1876819
  · exact B1876823
  · exact B1876827
  · exact B1876831
  · exact B1876835
  · exact B1876839
  · exact B1876843
  · exact B1876847
  · exact B1876851
  · exact B1876855
  · exact B1876859
  · exact B1876863
  · exact B1876867
  · exact B1876871
  · exact B1876875
  · exact B1876879
  · exact B1876883
  · exact B1876887
  · exact B1876891
  · exact B1876895
  · exact B1876899
  · exact B1876903
  · exact B1876907
  · exact B1876911
  · exact B1876915
  · exact B1876919
  · exact B1876923
  · exact B1876927
  · exact B1876931
  · exact B1876935
  · exact B1876939
  · exact B1876943
  · exact B1876947
  · exact B1876951
  · exact B1876955
  · exact B1876959
  · exact B1876963
  · exact B1876967
  · exact B1876971
  · exact B1876975
  · exact B1876979
  · exact B1876983
  · exact B1876987
  · exact B1876991
  · exact B1876995
  · exact B1876999
  · exact B1877003
  · exact B1877007
  · exact B1877011
  · exact B1877015
  · exact B1877019
  · exact B1877023
  · exact B1877027
  · exact B1877031
  · exact B1877035
  · exact B1877039
  · exact B1877043
  · exact B1877047
  · exact B1877051
  · exact B1877055
  · exact B1877059
  · exact B1877063
  · exact B1877067
  · exact B1877071
  · exact B1877075
  · exact B1877079
  · exact B1877083
  · exact B1877087
  · exact B1877091
  · exact B1877095
  · exact B1877099
  · exact B1877103
  · exact B1877107
  · exact B1877111
  · exact B1877115
  · exact B1877119
  · exact B1877123
  · exact B1877127
  · exact B1877131
  · exact B1877135
  · exact B1877139

theorem solution (m : ℕ) (hlo : 1875639 ≤ m) (hhi : m ≤ 1877139) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 468909 ≤ j := by omega
    have hj2 : j ≤ 469284 := by omega
    have hb : Blo 1875639 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
