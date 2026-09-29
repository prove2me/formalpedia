-- Prove2me | solution 1 for syracuse_descends_range_1803603_1805603
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:51:20.597147+00:00
-- url     : https://prove2.me/submissions/58f29769-64b9-4f15-8f68-39451d105edf

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


theorem B5488661 : Blo 1803603 5488661 := bbase (se 6 (by rfl) ⟨128640, by rfl⟩ : syracuseStep 5488661 = 257281) (by norm_num)
theorem B6504533 : Blo 1803603 6504533 := bbase (se 8 (by rfl) ⟨38112, by rfl⟩ : syracuseStep 6504533 = 76225) (by norm_num)
theorem B3424349 : Blo 1803603 3424349 := bbase (se 3 (by rfl) ⟨642065, by rfl⟩ : syracuseStep 3424349 = 1284131) (by norm_num)
theorem B2891909 : Blo 1803603 2891909 := bbase (se 4 (by rfl) ⟨271116, by rfl⟩ : syracuseStep 2891909 = 542233) (by norm_num)
theorem B4759717 : Blo 1803603 4759717 := bbase (se 4 (by rfl) ⟨446223, by rfl⟩ : syracuseStep 4759717 = 892447) (by norm_num)
theorem B3424493 : Blo 1803603 3424493 := bbase (se 3 (by rfl) ⟨642092, by rfl⟩ : syracuseStep 3424493 = 1284185) (by norm_num)
theorem B4333837 : Blo 1803603 4333837 := bbase (se 3 (by rfl) ⟨812594, by rfl⟩ : syracuseStep 4333837 = 1625189) (by norm_num)
theorem B15835445 : Blo 1803603 15835445 := bbase (se 5 (by rfl) ⟨742286, by rfl⟩ : syracuseStep 15835445 = 1484573) (by norm_num)
theorem B10281269 : Blo 1803603 10281269 := bbase (se 5 (by rfl) ⟨481934, by rfl⟩ : syracuseStep 10281269 = 963869) (by norm_num)
theorem B14639413 : Blo 1803603 14639413 := bbase (se 5 (by rfl) ⟨686222, by rfl⟩ : syracuseStep 14639413 = 1372445) (by norm_num)
theorem B3473741 : Blo 1803603 3473741 := bbase (se 3 (by rfl) ⟨651326, by rfl⟩ : syracuseStep 3473741 = 1302653) (by norm_num)
theorem B2892133 : Blo 1803603 2892133 := bbase (se 4 (by rfl) ⟨271137, by rfl⟩ : syracuseStep 2892133 = 542275) (by norm_num)
theorem B5136853 : Blo 1803603 5136853 := bbase (se 7 (by rfl) ⟨60197, by rfl⟩ : syracuseStep 5136853 = 120395) (by norm_num)
theorem B13705685 : Blo 1803603 13705685 := bbase (se 7 (by rfl) ⟨160613, by rfl⟩ : syracuseStep 13705685 = 321227) (by norm_num)
theorem B3424781 : Blo 1803603 3424781 := bbase (se 3 (by rfl) ⟨642146, by rfl⟩ : syracuseStep 3424781 = 1284293) (by norm_num)
theorem B8667749 : Blo 1803603 8667749 := bbase (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) (by norm_num)
theorem B9134693 : Blo 1803603 9134693 := bbase (se 4 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 9134693 = 1712755) (by norm_num)
theorem B5137013 : Blo 1803603 5137013 := bbase (se 5 (by rfl) ⟨240797, by rfl⟩ : syracuseStep 5137013 = 481595) (by norm_num)
theorem B3424933 : Blo 1803603 3424933 := bbase (se 4 (by rfl) ⟨321087, by rfl⟩ : syracuseStep 3424933 = 642175) (by norm_num)
theorem B3252901 : Blo 1803603 3252901 := bbase (se 4 (by rfl) ⟨304959, by rfl⟩ : syracuseStep 3252901 = 609919) (by norm_num)
theorem B6087365 : Blo 1803603 6087365 := bbase (se 4 (by rfl) ⟨570690, by rfl⟩ : syracuseStep 6087365 = 1141381) (by norm_num)
theorem B7709381 : Blo 1803603 7709381 := bbase (se 4 (by rfl) ⟨722754, by rfl⟩ : syracuseStep 7709381 = 1445509) (by norm_num)
theorem B3252973 : Blo 1803603 3252973 := bbase (se 3 (by rfl) ⟨609932, by rfl⟩ : syracuseStep 3252973 = 1219865) (by norm_num)
theorem B2745085 : Blo 1803603 2745085 := bbase (se 3 (by rfl) ⟨514703, by rfl⟩ : syracuseStep 2745085 = 1029407) (by norm_num)
theorem B5137253 : Blo 1803603 5137253 := bbase (se 4 (by rfl) ⟨481617, by rfl⟩ : syracuseStep 5137253 = 963235) (by norm_num)
theorem B13697909 : Blo 1803603 13697909 := bbase (se 5 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 13697909 = 1284179) (by norm_num)
theorem B2057113 : Blo 1803603 2057113 := bbase (se 2 (by rfl) ⟨771417, by rfl⟩ : syracuseStep 2057113 = 1542835) (by norm_num)
theorem B4334509 : Blo 1803603 4334509 := bbase (se 3 (by rfl) ⟨812720, by rfl⟩ : syracuseStep 4334509 = 1625441) (by norm_num)
theorem B3425237 : Blo 1803603 3425237 := bbase (se 7 (by rfl) ⟨40139, by rfl⟩ : syracuseStep 3425237 = 80279) (by norm_num)
theorem B5137445 : Blo 1803603 5137445 := bbase (se 4 (by rfl) ⟨481635, by rfl⟩ : syracuseStep 5137445 = 963271) (by norm_num)
theorem B6087797 : Blo 1803603 6087797 := bbase (se 5 (by rfl) ⟨285365, by rfl⟩ : syracuseStep 6087797 = 570731) (by norm_num)
theorem B4334741 : Blo 1803603 4334741 := bbase (se 6 (by rfl) ⟨101595, by rfl⟩ : syracuseStep 4334741 = 203191) (by norm_num)
theorem B4334789 : Blo 1803603 4334789 := bbase (se 4 (by rfl) ⟨406386, by rfl⟩ : syracuseStep 4334789 = 812773) (by norm_num)
theorem B10020181 : Blo 1803603 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B4875653 : Blo 1803603 4875653 := bbase (se 4 (by rfl) ⟨457092, by rfl⟩ : syracuseStep 4875653 = 914185) (by norm_num)
theorem B5858693 : Blo 1803603 5858693 := bbase (se 4 (by rfl) ⟨549252, by rfl⟩ : syracuseStep 5858693 = 1098505) (by norm_num)
theorem B6088229 : Blo 1803603 6088229 := bbase (se 4 (by rfl) ⟨570771, by rfl⟩ : syracuseStep 6088229 = 1141543) (by norm_num)
theorem B1926713 : Blo 1803603 1926713 := bbase (se 2 (by rfl) ⟨722517, by rfl⟩ : syracuseStep 1926713 = 1445035) (by norm_num)
theorem B27829909 : Blo 1803603 27829909 := bbase (se 6 (by rfl) ⟨652263, by rfl⟩ : syracuseStep 27829909 = 1304527) (by norm_num)
theorem B3425989 : Blo 1803603 3425989 := bbase (se 4 (by rfl) ⟨321186, by rfl⟩ : syracuseStep 3425989 = 642373) (by norm_num)
theorem B6850277 : Blo 1803603 6850277 := bbase (se 4 (by rfl) ⟨642213, by rfl⟩ : syracuseStep 6850277 = 1284427) (by norm_num)
theorem B8234741 : Blo 1803603 8234741 := bbase (se 5 (by rfl) ⟨386003, by rfl⟩ : syracuseStep 8234741 = 772007) (by norm_num)
theorem B2057989 : Blo 1803603 2057989 := bbase (se 4 (by rfl) ⟨192936, by rfl⟩ : syracuseStep 2057989 = 385873) (by norm_num)
theorem B1828645 : Blo 1803603 1828645 := bbase (se 4 (by rfl) ⟨171435, by rfl⟩ : syracuseStep 1828645 = 342871) (by norm_num)
theorem B3426133 : Blo 1803603 3426133 := bbase (se 9 (by rfl) ⟨10037, by rfl⟩ : syracuseStep 3426133 = 20075) (by norm_num)
theorem B9135989 : Blo 1803603 9135989 := bbase (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) (by norm_num)
theorem B6088661 : Blo 1803603 6088661 := bbase (se 7 (by rfl) ⟨71351, by rfl⟩ : syracuseStep 6088661 = 142703) (by norm_num)
theorem B1927157 : Blo 1803603 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B3426293 : Blo 1803603 3426293 := bbase (se 5 (by rfl) ⟨160607, by rfl⟩ : syracuseStep 3426293 = 321215) (by norm_num)
theorem B2705405 : Blo 1803603 2705405 := bbase (se 3 (by rfl) ⟨507263, by rfl⟩ : syracuseStep 2705405 = 1014527) (by norm_num)
theorem B6850565 : Blo 1803603 6850565 := bbase (se 4 (by rfl) ⟨642240, by rfl⟩ : syracuseStep 6850565 = 1284481) (by norm_num)
theorem B5138437 : Blo 1803603 5138437 := bbase (se 4 (by rfl) ⟨481728, by rfl⟩ : syracuseStep 5138437 = 963457) (by norm_num)
theorem B2705429 : Blo 1803603 2705429 := bbase (se 6 (by rfl) ⟨63408, by rfl⟩ : syracuseStep 2705429 = 126817) (by norm_num)
theorem B2705453 : Blo 1803603 2705453 := bbase (se 3 (by rfl) ⟨507272, by rfl⟩ : syracuseStep 2705453 = 1014545) (by norm_num)
theorem B2705477 : Blo 1803603 2705477 := bbase (se 4 (by rfl) ⟨253638, by rfl⟩ : syracuseStep 2705477 = 507277) (by norm_num)
theorem B2705501 : Blo 1803603 2705501 := bbase (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) (by norm_num)
theorem B2705525 : Blo 1803603 2705525 := bbase (se 5 (by rfl) ⟨126821, by rfl⟩ : syracuseStep 2705525 = 253643) (by norm_num)
theorem B3426437 : Blo 1803603 3426437 := bbase (se 4 (by rfl) ⟨321228, by rfl⟩ : syracuseStep 3426437 = 642457) (by norm_num)
theorem B2705549 : Blo 1803603 2705549 := bbase (se 3 (by rfl) ⟨507290, by rfl⟩ : syracuseStep 2705549 = 1014581) (by norm_num)
theorem B2705573 : Blo 1803603 2705573 := bbase (se 4 (by rfl) ⟨253647, by rfl⟩ : syracuseStep 2705573 = 507295) (by norm_num)
theorem B3852461 : Blo 1803603 3852461 := bbase (se 3 (by rfl) ⟨722336, by rfl⟩ : syracuseStep 3852461 = 1444673) (by norm_num)
theorem B3852469 : Blo 1803603 3852469 := bbase (se 5 (by rfl) ⟨180584, by rfl⟩ : syracuseStep 3852469 = 361169) (by norm_num)
theorem B2705597 : Blo 1803603 2705597 := bbase (se 3 (by rfl) ⟨507299, by rfl⟩ : syracuseStep 2705597 = 1014599) (by norm_num)
theorem B2705621 : Blo 1803603 2705621 := bbase (se 7 (by rfl) ⟨31706, by rfl⟩ : syracuseStep 2705621 = 63413) (by norm_num)
theorem B2705645 : Blo 1803603 2705645 := bbase (se 3 (by rfl) ⟨507308, by rfl⟩ : syracuseStep 2705645 = 1014617) (by norm_num)
theorem B1927405 : Blo 1803603 1927405 := bbase (se 3 (by rfl) ⟨361388, by rfl⟩ : syracuseStep 1927405 = 722777) (by norm_num)
theorem B2705669 : Blo 1803603 2705669 := bbase (se 4 (by rfl) ⟨253656, by rfl⟩ : syracuseStep 2705669 = 507313) (by norm_num)
theorem B7817477 : Blo 1803603 7817477 := bbase (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) (by norm_num)
theorem B2705693 : Blo 1803603 2705693 := bbase (se 3 (by rfl) ⟨507317, by rfl⟩ : syracuseStep 2705693 = 1014635) (by norm_num)
theorem B2705717 : Blo 1803603 2705717 := bbase (se 5 (by rfl) ⟨126830, by rfl⟩ : syracuseStep 2705717 = 253661) (by norm_num)
theorem B2705741 : Blo 1803603 2705741 := bbase (se 3 (by rfl) ⟨507326, by rfl⟩ : syracuseStep 2705741 = 1014653) (by norm_num)
theorem B2705765 : Blo 1803603 2705765 := bbase (se 4 (by rfl) ⟨253665, by rfl⟩ : syracuseStep 2705765 = 507331) (by norm_num)
theorem B2705789 : Blo 1803603 2705789 := bbase (se 3 (by rfl) ⟨507335, by rfl⟩ : syracuseStep 2705789 = 1014671) (by norm_num)
theorem B6089093 : Blo 1803603 6089093 := bbase (se 4 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 6089093 = 1141705) (by norm_num)
theorem B2705813 : Blo 1803603 2705813 := bbase (se 6 (by rfl) ⟨63417, by rfl⟩ : syracuseStep 2705813 = 126835) (by norm_num)
theorem B4114837 : Blo 1803603 4114837 := bbase (se 6 (by rfl) ⟨96441, by rfl⟩ : syracuseStep 4114837 = 192883) (by norm_num)
theorem B3426725 : Blo 1803603 3426725 := bbase (se 4 (by rfl) ⟨321255, by rfl⟩ : syracuseStep 3426725 = 642511) (by norm_num)
theorem B2705837 : Blo 1803603 2705837 := bbase (se 3 (by rfl) ⟨507344, by rfl⟩ : syracuseStep 2705837 = 1014689) (by norm_num)
theorem B2705861 : Blo 1803603 2705861 := bbase (se 4 (by rfl) ⟨253674, by rfl⟩ : syracuseStep 2705861 = 507349) (by norm_num)
theorem B2705885 : Blo 1803603 2705885 := bbase (se 3 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 2705885 = 1014707) (by norm_num)
theorem B2705909 : Blo 1803603 2705909 := bbase (se 5 (by rfl) ⟨126839, by rfl⟩ : syracuseStep 2705909 = 253679) (by norm_num)
theorem B2705933 : Blo 1803603 2705933 := bbase (se 3 (by rfl) ⟨507362, by rfl⟩ : syracuseStep 2705933 = 1014725) (by norm_num)
theorem B2705957 : Blo 1803603 2705957 := bbase (se 4 (by rfl) ⟨253683, by rfl⟩ : syracuseStep 2705957 = 507367) (by norm_num)
theorem B4336181 : Blo 1803603 4336181 := bbase (se 5 (by rfl) ⟨203258, by rfl⟩ : syracuseStep 4336181 = 406517) (by norm_num)
theorem B2705981 : Blo 1803603 2705981 := bbase (se 3 (by rfl) ⟨507371, by rfl⟩ : syracuseStep 2705981 = 1014743) (by norm_num)
theorem B3426877 : Blo 1803603 3426877 := bbase (se 3 (by rfl) ⟨642539, by rfl⟩ : syracuseStep 3426877 = 1285079) (by norm_num)
theorem B2706005 : Blo 1803603 2706005 := bbase (se 8 (by rfl) ⟨15855, by rfl⟩ : syracuseStep 2706005 = 31711) (by norm_num)
theorem B4115029 : Blo 1803603 4115029 := bbase (se 8 (by rfl) ⟨24111, by rfl⟩ : syracuseStep 4115029 = 48223) (by norm_num)
theorem B4565605 : Blo 1803603 4565605 := bbase (se 4 (by rfl) ⟨428025, by rfl⟩ : syracuseStep 4565605 = 856051) (by norm_num)
theorem B2706029 : Blo 1803603 2706029 := bbase (se 3 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 2706029 = 1014761) (by norm_num)
theorem B2706053 : Blo 1803603 2706053 := bbase (se 4 (by rfl) ⟨253692, by rfl⟩ : syracuseStep 2706053 = 507385) (by norm_num)
theorem B2058905 : Blo 1803603 2058905 := bbase (se 2 (by rfl) ⟨772089, by rfl⟩ : syracuseStep 2058905 = 1544179) (by norm_num)
theorem B2706077 : Blo 1803603 2706077 := bbase (se 3 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 2706077 = 1014779) (by norm_num)
theorem B1927837 : Blo 1803603 1927837 := bbase (se 3 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 1927837 = 722939) (by norm_num)
theorem B2706101 : Blo 1803603 2706101 := bbase (se 5 (by rfl) ⟨126848, by rfl⟩ : syracuseStep 2706101 = 253697) (by norm_num)
theorem B2706125 : Blo 1803603 2706125 := bbase (se 3 (by rfl) ⟨507398, by rfl⟩ : syracuseStep 2706125 = 1014797) (by norm_num)
theorem B4565717 : Blo 1803603 4565717 := bbase (se 7 (by rfl) ⟨53504, by rfl⟩ : syracuseStep 4565717 = 107009) (by norm_num)
theorem B2706149 : Blo 1803603 2706149 := bbase (se 4 (by rfl) ⟨253701, by rfl⟩ : syracuseStep 2706149 = 507403) (by norm_num)
theorem B1927909 : Blo 1803603 1927909 := bbase (se 4 (by rfl) ⟨180741, by rfl⟩ : syracuseStep 1927909 = 361483) (by norm_num)
theorem B4336373 : Blo 1803603 4336373 := bbase (se 5 (by rfl) ⟨203267, by rfl⟩ : syracuseStep 4336373 = 406535) (by norm_num)
theorem B2706173 : Blo 1803603 2706173 := bbase (se 3 (by rfl) ⟨507407, by rfl⟩ : syracuseStep 2706173 = 1014815) (by norm_num)
theorem B2706197 : Blo 1803603 2706197 := bbase (se 6 (by rfl) ⟨63426, by rfl⟩ : syracuseStep 2706197 = 126853) (by norm_num)
theorem B2706221 : Blo 1803603 2706221 := bbase (se 3 (by rfl) ⟨507416, by rfl⟩ : syracuseStep 2706221 = 1014833) (by norm_num)
theorem B6089525 : Blo 1803603 6089525 := bbase (se 5 (by rfl) ⟨285446, by rfl⟩ : syracuseStep 6089525 = 570893) (by norm_num)
theorem B2706245 : Blo 1803603 2706245 := bbase (se 4 (by rfl) ⟨253710, by rfl⟩ : syracuseStep 2706245 = 507421) (by norm_num)
theorem B2706269 : Blo 1803603 2706269 := bbase (se 3 (by rfl) ⟨507425, by rfl⟩ : syracuseStep 2706269 = 1014851) (by norm_num)
theorem B3427181 : Blo 1803603 3427181 := bbase (se 3 (by rfl) ⟨642596, by rfl⟩ : syracuseStep 3427181 = 1285193) (by norm_num)
theorem B2706293 : Blo 1803603 2706293 := bbase (se 5 (by rfl) ⟨126857, by rfl⟩ : syracuseStep 2706293 = 253715) (by norm_num)
theorem B2706317 : Blo 1803603 2706317 := bbase (se 3 (by rfl) ⟨507434, by rfl⟩ : syracuseStep 2706317 = 1014869) (by norm_num)
theorem B4565909 : Blo 1803603 4565909 := bbase (se 6 (by rfl) ⟨107013, by rfl⟩ : syracuseStep 4565909 = 214027) (by norm_num)
theorem B2706341 : Blo 1803603 2706341 := bbase (se 4 (by rfl) ⟨253719, by rfl⟩ : syracuseStep 2706341 = 507439) (by norm_num)
theorem B2706365 : Blo 1803603 2706365 := bbase (se 3 (by rfl) ⟨507443, by rfl⟩ : syracuseStep 2706365 = 1014887) (by norm_num)
theorem B2706389 : Blo 1803603 2706389 := bbase (se 7 (by rfl) ⟨31715, by rfl⟩ : syracuseStep 2706389 = 63431) (by norm_num)
theorem B2706413 : Blo 1803603 2706413 := bbase (se 3 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 2706413 = 1014905) (by norm_num)
theorem B4058117 : Blo 1803603 4058117 := bbase (se 4 (by rfl) ⟨380448, by rfl⟩ : syracuseStep 4058117 = 760897) (by norm_num)
theorem B2706437 : Blo 1803603 2706437 := bbase (se 4 (by rfl) ⟨253728, by rfl⟩ : syracuseStep 2706437 = 507457) (by norm_num)
theorem B2706461 : Blo 1803603 2706461 := bbase (se 3 (by rfl) ⟨507461, by rfl⟩ : syracuseStep 2706461 = 1014923) (by norm_num)
theorem B10275893 : Blo 1803603 10275893 := bbase (se 5 (by rfl) ⟨481682, by rfl⟩ : syracuseStep 10275893 = 963365) (by norm_num)
theorem B2706485 : Blo 1803603 2706485 := bbase (se 5 (by rfl) ⟨126866, by rfl⟩ : syracuseStep 2706485 = 253733) (by norm_num)
theorem B4058189 : Blo 1803603 4058189 := bbase (se 3 (by rfl) ⟨760910, by rfl⟩ : syracuseStep 4058189 = 1521821) (by norm_num)
theorem B2706509 : Blo 1803603 2706509 := bbase (se 3 (by rfl) ⟨507470, by rfl⟩ : syracuseStep 2706509 = 1014941) (by norm_num)
theorem B3296333 : Blo 1803603 3296333 := bbase (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) (by norm_num)
theorem B5139541 : Blo 1803603 5139541 := bbase (se 8 (by rfl) ⟨30114, by rfl⟩ : syracuseStep 5139541 = 60229) (by norm_num)
theorem B2706533 : Blo 1803603 2706533 := bbase (se 4 (by rfl) ⟨253737, by rfl⟩ : syracuseStep 2706533 = 507475) (by norm_num)
theorem B11562101 : Blo 1803603 11562101 := bbase (se 5 (by rfl) ⟨541973, by rfl⟩ : syracuseStep 11562101 = 1083947) (by norm_num)
theorem B2706557 : Blo 1803603 2706557 := bbase (se 3 (by rfl) ⟨507479, by rfl⟩ : syracuseStep 2706557 = 1014959) (by norm_num)
theorem B9137285 : Blo 1803603 9137285 := bbase (se 4 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 9137285 = 1713241) (by norm_num)
theorem B4058261 : Blo 1803603 4058261 := bbase (se 6 (by rfl) ⟨95115, by rfl⟩ : syracuseStep 4058261 = 190231) (by norm_num)
theorem B2706581 : Blo 1803603 2706581 := bbase (se 6 (by rfl) ⟨63435, by rfl⟩ : syracuseStep 2706581 = 126871) (by norm_num)
theorem B3656869 : Blo 1803603 3656869 := bbase (se 4 (by rfl) ⟨342831, by rfl⟩ : syracuseStep 3656869 = 685663) (by norm_num)
theorem B6851749 : Blo 1803603 6851749 := bbase (se 4 (by rfl) ⟨642351, by rfl⟩ : syracuseStep 6851749 = 1284703) (by norm_num)
theorem B2706605 : Blo 1803603 2706605 := bbase (se 3 (by rfl) ⟨507488, by rfl⟩ : syracuseStep 2706605 = 1014977) (by norm_num)
theorem B2706629 : Blo 1803603 2706629 := bbase (se 4 (by rfl) ⟨253746, by rfl⟩ : syracuseStep 2706629 = 507493) (by norm_num)
theorem B4058333 : Blo 1803603 4058333 := bbase (se 3 (by rfl) ⟨760937, by rfl⟩ : syracuseStep 4058333 = 1521875) (by norm_num)
theorem B2706653 : Blo 1803603 2706653 := bbase (se 3 (by rfl) ⟨507497, by rfl⟩ : syracuseStep 2706653 = 1014995) (by norm_num)
theorem B6089957 : Blo 1803603 6089957 := bbase (se 4 (by rfl) ⟨570933, by rfl⟩ : syracuseStep 6089957 = 1141867) (by norm_num)
theorem B4566253 : Blo 1803603 4566253 := bbase (se 3 (by rfl) ⟨856172, by rfl⟩ : syracuseStep 4566253 = 1712345) (by norm_num)
theorem B2706677 : Blo 1803603 2706677 := bbase (se 5 (by rfl) ⟨126875, by rfl⟩ : syracuseStep 2706677 = 253751) (by norm_num)
theorem B2706701 : Blo 1803603 2706701 := bbase (se 3 (by rfl) ⟨507506, by rfl⟩ : syracuseStep 2706701 = 1015013) (by norm_num)
theorem B3853597 : Blo 1803603 3853597 := bbase (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) (by norm_num)
theorem B4058405 : Blo 1803603 4058405 := bbase (se 4 (by rfl) ⟨380475, by rfl⟩ : syracuseStep 4058405 = 760951) (by norm_num)
theorem B2706725 : Blo 1803603 2706725 := bbase (se 4 (by rfl) ⟨253755, by rfl⟩ : syracuseStep 2706725 = 507511) (by norm_num)
theorem B2706749 : Blo 1803603 2706749 := bbase (se 3 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 2706749 = 1015031) (by norm_num)
theorem B2706773 : Blo 1803603 2706773 := bbase (se 11 (by rfl) ⟨1982, by rfl⟩ : syracuseStep 2706773 = 3965) (by norm_num)
theorem B4566365 : Blo 1803603 4566365 := bbase (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) (by norm_num)
theorem B4058477 : Blo 1803603 4058477 := bbase (se 3 (by rfl) ⟨760964, by rfl⟩ : syracuseStep 4058477 = 1521929) (by norm_num)
theorem B2706797 : Blo 1803603 2706797 := bbase (se 3 (by rfl) ⟨507524, by rfl⟩ : syracuseStep 2706797 = 1015049) (by norm_num)
theorem B8228213 : Blo 1803603 8228213 := bbase (se 5 (by rfl) ⟨385697, by rfl⟩ : syracuseStep 8228213 = 771395) (by norm_num)
theorem B2706821 : Blo 1803603 2706821 := bbase (se 4 (by rfl) ⟨253764, by rfl⟩ : syracuseStep 2706821 = 507529) (by norm_num)
theorem B2706845 : Blo 1803603 2706845 := bbase (se 3 (by rfl) ⟨507533, by rfl⟩ : syracuseStep 2706845 = 1015067) (by norm_num)
theorem B4058549 : Blo 1803603 4058549 := bbase (se 5 (by rfl) ⟨190244, by rfl⟩ : syracuseStep 4058549 = 380489) (by norm_num)
theorem B2706869 : Blo 1803603 2706869 := bbase (se 5 (by rfl) ⟨126884, by rfl⟩ : syracuseStep 2706869 = 253769) (by norm_num)
theorem B2706893 : Blo 1803603 2706893 := bbase (se 3 (by rfl) ⟨507542, by rfl⟩ : syracuseStep 2706893 = 1015085) (by norm_num)
theorem B6852053 : Blo 1803603 6852053 := bbase (se 7 (by rfl) ⟨80297, by rfl⟩ : syracuseStep 6852053 = 160595) (by norm_num)
theorem B2706917 : Blo 1803603 2706917 := bbase (se 4 (by rfl) ⟨253773, by rfl⟩ : syracuseStep 2706917 = 507547) (by norm_num)
theorem B4058621 : Blo 1803603 4058621 := bbase (se 3 (by rfl) ⟨760991, by rfl⟩ : syracuseStep 4058621 = 1521983) (by norm_num)
theorem B2706941 : Blo 1803603 2706941 := bbase (se 3 (by rfl) ⟨507551, by rfl⟩ : syracuseStep 2706941 = 1015103) (by norm_num)
theorem B2706965 : Blo 1803603 2706965 := bbase (se 6 (by rfl) ⟨63444, by rfl⟩ : syracuseStep 2706965 = 126889) (by norm_num)
theorem B4566557 : Blo 1803603 4566557 := bbase (se 3 (by rfl) ⟨856229, by rfl⟩ : syracuseStep 4566557 = 1712459) (by norm_num)
theorem B2706989 : Blo 1803603 2706989 := bbase (se 3 (by rfl) ⟨507560, by rfl⟩ : syracuseStep 2706989 = 1015121) (by norm_num)
theorem B4058693 : Blo 1803603 4058693 := bbase (se 4 (by rfl) ⟨380502, by rfl⟩ : syracuseStep 4058693 = 761005) (by norm_num)
theorem B2707013 : Blo 1803603 2707013 := bbase (se 4 (by rfl) ⟨253782, by rfl⟩ : syracuseStep 2707013 = 507565) (by norm_num)
theorem B2707037 : Blo 1803603 2707037 := bbase (se 3 (by rfl) ⟨507569, by rfl⟩ : syracuseStep 2707037 = 1015139) (by norm_num)
theorem B2707061 : Blo 1803603 2707061 := bbase (se 5 (by rfl) ⟨126893, by rfl⟩ : syracuseStep 2707061 = 253787) (by norm_num)
theorem B4058765 : Blo 1803603 4058765 := bbase (se 3 (by rfl) ⟨761018, by rfl⟩ : syracuseStep 4058765 = 1522037) (by norm_num)
theorem B2707085 : Blo 1803603 2707085 := bbase (se 3 (by rfl) ⟨507578, by rfl⟩ : syracuseStep 2707085 = 1015157) (by norm_num)
theorem B3853973 : Blo 1803603 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B6090389 : Blo 1803603 6090389 := bbase (se 6 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 6090389 = 285487) (by norm_num)
theorem B2707109 : Blo 1803603 2707109 := bbase (se 4 (by rfl) ⟨253791, by rfl⟩ : syracuseStep 2707109 = 507583) (by norm_num)
theorem B8670901 : Blo 1803603 8670901 := bbase (se 5 (by rfl) ⟨406448, by rfl⟩ : syracuseStep 8670901 = 812897) (by norm_num)
theorem B2707133 : Blo 1803603 2707133 := bbase (se 3 (by rfl) ⟨507587, by rfl⟩ : syracuseStep 2707133 = 1015175) (by norm_num)
theorem B7720645 : Blo 1803603 7720645 := bbase (se 4 (by rfl) ⟨723810, by rfl⟩ : syracuseStep 7720645 = 1447621) (by norm_num)
theorem B4058837 : Blo 1803603 4058837 := bbase (se 7 (by rfl) ⟨47564, by rfl⟩ : syracuseStep 4058837 = 95129) (by norm_num)
theorem B2707157 : Blo 1803603 2707157 := bbase (se 7 (by rfl) ⟨31724, by rfl⟩ : syracuseStep 2707157 = 63449) (by norm_num)
theorem B4878053 : Blo 1803603 4878053 := bbase (se 4 (by rfl) ⟨457317, by rfl⟩ : syracuseStep 4878053 = 914635) (by norm_num)
theorem B2707181 : Blo 1803603 2707181 := bbase (se 3 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 2707181 = 1015193) (by norm_num)
theorem B2707205 : Blo 1803603 2707205 := bbase (se 4 (by rfl) ⟨253800, by rfl⟩ : syracuseStep 2707205 = 507601) (by norm_num)
theorem B4058909 : Blo 1803603 4058909 := bbase (se 3 (by rfl) ⟨761045, by rfl⟩ : syracuseStep 4058909 = 1522091) (by norm_num)
theorem B2707229 : Blo 1803603 2707229 := bbase (se 3 (by rfl) ⟨507605, by rfl⟩ : syracuseStep 2707229 = 1015211) (by norm_num)
theorem B2707253 : Blo 1803603 2707253 := bbase (se 5 (by rfl) ⟨126902, by rfl⟩ : syracuseStep 2707253 = 253805) (by norm_num)
theorem B2707277 : Blo 1803603 2707277 := bbase (se 3 (by rfl) ⟨507614, by rfl⟩ : syracuseStep 2707277 = 1015229) (by norm_num)
theorem B4058981 : Blo 1803603 4058981 := bbase (se 4 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 4058981 = 761059) (by norm_num)
theorem B2707301 : Blo 1803603 2707301 := bbase (se 4 (by rfl) ⟨253809, by rfl⟩ : syracuseStep 2707301 = 507619) (by norm_num)
theorem B4566901 : Blo 1803603 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B2707325 : Blo 1803603 2707325 := bbase (se 3 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 2707325 = 1015247) (by norm_num)
theorem B2707349 : Blo 1803603 2707349 := bbase (se 6 (by rfl) ⟨63453, by rfl⟩ : syracuseStep 2707349 = 126907) (by norm_num)
theorem B4059053 : Blo 1803603 4059053 := bbase (se 3 (by rfl) ⟨761072, by rfl⟩ : syracuseStep 4059053 = 1522145) (by norm_num)
theorem B2707373 : Blo 1803603 2707373 := bbase (se 3 (by rfl) ⟨507632, by rfl⟩ : syracuseStep 2707373 = 1015265) (by norm_num)
theorem B2568125 : Blo 1803603 2568125 := bbase (se 3 (by rfl) ⟨481523, by rfl⟩ : syracuseStep 2568125 = 963047) (by norm_num)
theorem B2707397 : Blo 1803603 2707397 := bbase (se 4 (by rfl) ⟨253818, by rfl⟩ : syracuseStep 2707397 = 507637) (by norm_num)
theorem B2707421 : Blo 1803603 2707421 := bbase (se 3 (by rfl) ⟨507641, by rfl⟩ : syracuseStep 2707421 = 1015283) (by norm_num)
theorem B4567013 : Blo 1803603 4567013 := bbase (se 4 (by rfl) ⟨428157, by rfl⟩ : syracuseStep 4567013 = 856315) (by norm_num)
theorem B4059125 : Blo 1803603 4059125 := bbase (se 5 (by rfl) ⟨190271, by rfl⟩ : syracuseStep 4059125 = 380543) (by norm_num)
theorem B2707445 : Blo 1803603 2707445 := bbase (se 5 (by rfl) ⟨126911, by rfl⟩ : syracuseStep 2707445 = 253823) (by norm_num)
theorem B2166793 : Blo 1803603 2166793 := bbase (se 2 (by rfl) ⟨812547, by rfl⟩ : syracuseStep 2166793 = 1625095) (by norm_num)
theorem B2707469 : Blo 1803603 2707469 := bbase (se 3 (by rfl) ⟨507650, by rfl⟩ : syracuseStep 2707469 = 1015301) (by norm_num)
theorem B2707493 : Blo 1803603 2707493 := bbase (se 4 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 2707493 = 507655) (by norm_num)
theorem B4059197 : Blo 1803603 4059197 := bbase (se 3 (by rfl) ⟨761099, by rfl⟩ : syracuseStep 4059197 = 1522199) (by norm_num)
theorem B2707517 : Blo 1803603 2707517 := bbase (se 3 (by rfl) ⟨507659, by rfl⟩ : syracuseStep 2707517 = 1015319) (by norm_num)
theorem B6090821 : Blo 1803603 6090821 := bbase (se 4 (by rfl) ⟨571014, by rfl⟩ : syracuseStep 6090821 = 1142029) (by norm_num)
theorem B2707541 : Blo 1803603 2707541 := bbase (se 8 (by rfl) ⟨15864, by rfl⟩ : syracuseStep 2707541 = 31729) (by norm_num)
theorem B2707565 : Blo 1803603 2707565 := bbase (se 3 (by rfl) ⟨507668, by rfl⟩ : syracuseStep 2707565 = 1015337) (by norm_num)
theorem B4059269 : Blo 1803603 4059269 := bbase (se 4 (by rfl) ⟨380556, by rfl⟩ : syracuseStep 4059269 = 761113) (by norm_num)
theorem B2707589 : Blo 1803603 2707589 := bbase (se 4 (by rfl) ⟨253836, by rfl⟩ : syracuseStep 2707589 = 507673) (by norm_num)
theorem B2707613 : Blo 1803603 2707613 := bbase (se 3 (by rfl) ⟨507677, by rfl⟩ : syracuseStep 2707613 = 1015355) (by norm_num)
theorem B4567205 : Blo 1803603 4567205 := bbase (se 4 (by rfl) ⟨428175, by rfl⟩ : syracuseStep 4567205 = 856351) (by norm_num)
theorem B15413429 : Blo 1803603 15413429 := bbase (se 5 (by rfl) ⟨722504, by rfl⟩ : syracuseStep 15413429 = 1445009) (by norm_num)
theorem B2707637 : Blo 1803603 2707637 := bbase (se 5 (by rfl) ⟨126920, by rfl⟩ : syracuseStep 2707637 = 253841) (by norm_num)
theorem B4059341 : Blo 1803603 4059341 := bbase (se 3 (by rfl) ⟨761126, by rfl⟩ : syracuseStep 4059341 = 1522253) (by norm_num)
theorem B2707661 : Blo 1803603 2707661 := bbase (se 3 (by rfl) ⟨507686, by rfl⟩ : syracuseStep 2707661 = 1015373) (by norm_num)
theorem B10277077 : Blo 1803603 10277077 := bbase (se 7 (by rfl) ⟨120434, by rfl⟩ : syracuseStep 10277077 = 240869) (by norm_num)
theorem B2707685 : Blo 1803603 2707685 := bbase (se 4 (by rfl) ⟨253845, by rfl⟩ : syracuseStep 2707685 = 507691) (by norm_num)
theorem B2707709 : Blo 1803603 2707709 := bbase (se 3 (by rfl) ⟨507695, by rfl⟩ : syracuseStep 2707709 = 1015391) (by norm_num)
theorem B3657997 : Blo 1803603 3657997 := bbase (se 3 (by rfl) ⟨685874, by rfl⟩ : syracuseStep 3657997 = 1371749) (by norm_num)
theorem B4059413 : Blo 1803603 4059413 := bbase (se 6 (by rfl) ⟨95142, by rfl⟩ : syracuseStep 4059413 = 190285) (by norm_num)
theorem B3961109 : Blo 1803603 3961109 := bbase (se 6 (by rfl) ⟨92838, by rfl⟩ : syracuseStep 3961109 = 185677) (by norm_num)
theorem B2707733 : Blo 1803603 2707733 := bbase (se 6 (by rfl) ⟨63462, by rfl⟩ : syracuseStep 2707733 = 126925) (by norm_num)
theorem B12521749 : Blo 1803603 12521749 := bbase (se 6 (by rfl) ⟨293478, by rfl⟩ : syracuseStep 12521749 = 586957) (by norm_num)
theorem B2707757 : Blo 1803603 2707757 := bbase (se 3 (by rfl) ⟨507704, by rfl⟩ : syracuseStep 2707757 = 1015409) (by norm_num)
theorem B9761077 : Blo 1803603 9761077 := bbase (se 5 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 9761077 = 915101) (by norm_num)
theorem B5779781 : Blo 1803603 5779781 := bbase (se 4 (by rfl) ⟨541854, by rfl⟩ : syracuseStep 5779781 = 1083709) (by norm_num)
theorem B2707781 : Blo 1803603 2707781 := bbase (se 4 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 2707781 = 507709) (by norm_num)
theorem B19501397 : Blo 1803603 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B3043669 : Blo 1803603 3043669 := bbase (se 10 (by rfl) ⟨4458, by rfl⟩ : syracuseStep 3043669 = 8917) (by norm_num)
theorem B3658069 : Blo 1803603 3658069 := bbase (se 10 (by rfl) ⟨5358, by rfl⟩ : syracuseStep 3658069 = 10717) (by norm_num)
theorem B4059485 : Blo 1803603 4059485 := bbase (se 3 (by rfl) ⟨761153, by rfl⟩ : syracuseStep 4059485 = 1522307) (by norm_num)
theorem B2707805 : Blo 1803603 2707805 := bbase (se 3 (by rfl) ⟨507713, by rfl⟩ : syracuseStep 2707805 = 1015427) (by norm_num)
theorem B2707829 : Blo 1803603 2707829 := bbase (se 5 (by rfl) ⟨126929, by rfl⟩ : syracuseStep 2707829 = 253859) (by norm_num)
theorem B2707853 : Blo 1803603 2707853 := bbase (se 3 (by rfl) ⟨507722, by rfl⟩ : syracuseStep 2707853 = 1015445) (by norm_num)
theorem B3297677 : Blo 1803603 3297677 := bbase (se 3 (by rfl) ⟨618314, by rfl⟩ : syracuseStep 3297677 = 1236629) (by norm_num)
theorem B4944277 : Blo 1803603 4944277 := bbase (se 6 (by rfl) ⟨115881, by rfl⟩ : syracuseStep 4944277 = 231763) (by norm_num)
theorem B9138581 : Blo 1803603 9138581 := bbase (se 6 (by rfl) ⟨214185, by rfl⟩ : syracuseStep 9138581 = 428371) (by norm_num)
theorem B4059557 : Blo 1803603 4059557 := bbase (se 4 (by rfl) ⟨380583, by rfl⟩ : syracuseStep 4059557 = 761167) (by norm_num)
theorem B2707877 : Blo 1803603 2707877 := bbase (se 4 (by rfl) ⟨253863, by rfl⟩ : syracuseStep 2707877 = 507727) (by norm_num)
theorem B3043757 : Blo 1803603 3043757 := bbase (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) (by norm_num)
theorem B2707901 : Blo 1803603 2707901 := bbase (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) (by norm_num)
theorem B2707925 : Blo 1803603 2707925 := bbase (se 7 (by rfl) ⟨31733, by rfl⟩ : syracuseStep 2707925 = 63467) (by norm_num)
theorem B2568677 : Blo 1803603 2568677 := bbase (se 4 (by rfl) ⟨240813, by rfl⟩ : syracuseStep 2568677 = 481627) (by norm_num)
theorem B4059629 : Blo 1803603 4059629 := bbase (se 3 (by rfl) ⟨761180, by rfl⟩ : syracuseStep 4059629 = 1522361) (by norm_num)
theorem B2707949 : Blo 1803603 2707949 := bbase (se 3 (by rfl) ⟨507740, by rfl⟩ : syracuseStep 2707949 = 1015481) (by norm_num)
theorem B6091253 : Blo 1803603 6091253 := bbase (se 5 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 6091253 = 571055) (by norm_num)
theorem B4567549 : Blo 1803603 4567549 := bbase (se 3 (by rfl) ⟨856415, by rfl⟩ : syracuseStep 4567549 = 1712831) (by norm_num)
theorem B2707973 : Blo 1803603 2707973 := bbase (se 4 (by rfl) ⟨253872, by rfl⟩ : syracuseStep 2707973 = 507745) (by norm_num)
theorem B2347537 : Blo 1803603 2347537 := bbase (se 2 (by rfl) ⟨880326, by rfl⟩ : syracuseStep 2347537 = 1760653) (by norm_num)
theorem B2707997 : Blo 1803603 2707997 := bbase (se 3 (by rfl) ⟨507749, by rfl⟩ : syracuseStep 2707997 = 1015499) (by norm_num)
theorem B3043885 : Blo 1803603 3043885 := bbase (se 3 (by rfl) ⟨570728, by rfl⟩ : syracuseStep 3043885 = 1141457) (by norm_num)
theorem B4059701 : Blo 1803603 4059701 := bbase (se 5 (by rfl) ⟨190298, by rfl⟩ : syracuseStep 4059701 = 380597) (by norm_num)
theorem B2708021 : Blo 1803603 2708021 := bbase (se 5 (by rfl) ⟨126938, by rfl⟩ : syracuseStep 2708021 = 253877) (by norm_num)
theorem B5141045 : Blo 1803603 5141045 := bbase (se 5 (by rfl) ⟨240986, by rfl⟩ : syracuseStep 5141045 = 481973) (by norm_num)
theorem B2708045 : Blo 1803603 2708045 := bbase (se 3 (by rfl) ⟨507758, by rfl⟩ : syracuseStep 2708045 = 1015517) (by norm_num)
theorem B2708069 : Blo 1803603 2708069 := bbase (se 4 (by rfl) ⟨253881, by rfl⟩ : syracuseStep 2708069 = 507763) (by norm_num)
theorem B4567661 : Blo 1803603 4567661 := bbase (se 3 (by rfl) ⟨856436, by rfl⟩ : syracuseStep 4567661 = 1712873) (by norm_num)
theorem B4059773 : Blo 1803603 4059773 := bbase (se 3 (by rfl) ⟨761207, by rfl⟩ : syracuseStep 4059773 = 1522415) (by norm_num)
theorem B2708093 : Blo 1803603 2708093 := bbase (se 3 (by rfl) ⟨507767, by rfl⟩ : syracuseStep 2708093 = 1015535) (by norm_num)
theorem B3043973 : Blo 1803603 3043973 := bbase (se 4 (by rfl) ⟨285372, by rfl⟩ : syracuseStep 3043973 = 570745) (by norm_num)
theorem B2708117 : Blo 1803603 2708117 := bbase (se 6 (by rfl) ⟨63471, by rfl⟩ : syracuseStep 2708117 = 126943) (by norm_num)
theorem B2708141 : Blo 1803603 2708141 := bbase (se 3 (by rfl) ⟨507776, by rfl⟩ : syracuseStep 2708141 = 1015553) (by norm_num)
theorem B4059845 : Blo 1803603 4059845 := bbase (se 4 (by rfl) ⟨380610, by rfl⟩ : syracuseStep 4059845 = 761221) (by norm_num)
theorem B2708165 : Blo 1803603 2708165 := bbase (se 4 (by rfl) ⟨253890, by rfl⟩ : syracuseStep 2708165 = 507781) (by norm_num)
theorem B2708189 : Blo 1803603 2708189 := bbase (se 3 (by rfl) ⟨507785, by rfl⟩ : syracuseStep 2708189 = 1015571) (by norm_num)
theorem B2929397 : Blo 1803603 2929397 := bbase (se 5 (by rfl) ⟨137315, by rfl⟩ : syracuseStep 2929397 = 274631) (by norm_num)
theorem B2708213 : Blo 1803603 2708213 := bbase (se 5 (by rfl) ⟨126947, by rfl⟩ : syracuseStep 2708213 = 253895) (by norm_num)
theorem B3044101 : Blo 1803603 3044101 := bbase (se 4 (by rfl) ⟨285384, by rfl⟩ : syracuseStep 3044101 = 570769) (by norm_num)
theorem B4059917 : Blo 1803603 4059917 := bbase (se 3 (by rfl) ⟨761234, by rfl⟩ : syracuseStep 4059917 = 1522469) (by norm_num)
theorem B2708237 : Blo 1803603 2708237 := bbase (se 3 (by rfl) ⟨507794, by rfl⟩ : syracuseStep 2708237 = 1015589) (by norm_num)
theorem B2708261 : Blo 1803603 2708261 := bbase (se 4 (by rfl) ⟨253899, by rfl⟩ : syracuseStep 2708261 = 507799) (by norm_num)
theorem B4567853 : Blo 1803603 4567853 := bbase (se 3 (by rfl) ⟨856472, by rfl⟩ : syracuseStep 4567853 = 1712945) (by norm_num)
theorem B9130805 : Blo 1803603 9130805 := bbase (se 5 (by rfl) ⟨428006, by rfl⟩ : syracuseStep 9130805 = 856013) (by norm_num)
theorem B2708285 : Blo 1803603 2708285 := bbase (se 3 (by rfl) ⟨507803, by rfl⟩ : syracuseStep 2708285 = 1015607) (by norm_num)
theorem B4059989 : Blo 1803603 4059989 := bbase (se 9 (by rfl) ⟨11894, by rfl⟩ : syracuseStep 4059989 = 23789) (by norm_num)
theorem B2708309 : Blo 1803603 2708309 := bbase (se 9 (by rfl) ⟨7934, by rfl⟩ : syracuseStep 2708309 = 15869) (by norm_num)
theorem B3044189 : Blo 1803603 3044189 := bbase (se 3 (by rfl) ⟨570785, by rfl⟩ : syracuseStep 3044189 = 1141571) (by norm_num)
theorem B2708333 : Blo 1803603 2708333 := bbase (se 3 (by rfl) ⟨507812, by rfl⟩ : syracuseStep 2708333 = 1015625) (by norm_num)
theorem B2315129 : Blo 1803603 2315129 := bbase (se 2 (by rfl) ⟨868173, by rfl⟩ : syracuseStep 2315129 = 1736347) (by norm_num)
theorem B2708357 : Blo 1803603 2708357 := bbase (se 4 (by rfl) ⟨253908, by rfl⟩ : syracuseStep 2708357 = 507817) (by norm_num)
theorem B4060061 : Blo 1803603 4060061 := bbase (se 3 (by rfl) ⟨761261, by rfl⟩ : syracuseStep 4060061 = 1522523) (by norm_num)
theorem B2347933 : Blo 1803603 2347933 := bbase (se 3 (by rfl) ⟨440237, by rfl⟩ : syracuseStep 2347933 = 880475) (by norm_num)
theorem B2708381 : Blo 1803603 2708381 := bbase (se 3 (by rfl) ⟨507821, by rfl⟩ : syracuseStep 2708381 = 1015643) (by norm_num)
theorem B6091685 : Blo 1803603 6091685 := bbase (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) (by norm_num)
theorem B3085237 : Blo 1803603 3085237 := bbase (se 5 (by rfl) ⟨144620, by rfl⟩ : syracuseStep 3085237 = 289241) (by norm_num)
theorem B2708405 : Blo 1803603 2708405 := bbase (se 5 (by rfl) ⟨126956, by rfl⟩ : syracuseStep 2708405 = 253913) (by norm_num)
theorem B3044317 : Blo 1803603 3044317 := bbase (se 3 (by rfl) ⟨570809, by rfl⟩ : syracuseStep 3044317 = 1141619) (by norm_num)
theorem B4060133 : Blo 1803603 4060133 := bbase (se 4 (by rfl) ⟨380637, by rfl⟩ : syracuseStep 4060133 = 761275) (by norm_num)
theorem B6591493 : Blo 1803603 6591493 := bbase (se 4 (by rfl) ⟨617952, by rfl⟩ : syracuseStep 6591493 = 1235905) (by norm_num)
theorem B7705621 : Blo 1803603 7705621 := bbase (se 6 (by rfl) ⟨180600, by rfl⟩ : syracuseStep 7705621 = 361201) (by norm_num)
theorem B2167841 : Blo 1803603 2167841 := bbase (se 2 (by rfl) ⟨812940, by rfl⟩ : syracuseStep 2167841 = 1625881) (by norm_num)
theorem B4060205 : Blo 1803603 4060205 := bbase (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) (by norm_num)
theorem B3044405 : Blo 1803603 3044405 := bbase (se 5 (by rfl) ⟨142706, by rfl⟩ : syracuseStep 3044405 = 285413) (by norm_num)
theorem B4060277 : Blo 1803603 4060277 := bbase (se 5 (by rfl) ⟨190325, by rfl⟩ : syracuseStep 4060277 = 380651) (by norm_num)
theorem B2970749 : Blo 1803603 2970749 := bbase (se 3 (by rfl) ⟨557015, by rfl⟩ : syracuseStep 2970749 = 1114031) (by norm_num)
theorem B4568197 : Blo 1803603 4568197 := bbase (se 4 (by rfl) ⟨428268, by rfl⟩ : syracuseStep 4568197 = 856537) (by norm_num)
theorem B2471077 : Blo 1803603 2471077 := bbase (se 4 (by rfl) ⟨231663, by rfl⟩ : syracuseStep 2471077 = 463327) (by norm_num)
theorem B3044533 : Blo 1803603 3044533 := bbase (se 5 (by rfl) ⟨142712, by rfl⟩ : syracuseStep 3044533 = 285425) (by norm_num)
theorem B4060349 : Blo 1803603 4060349 := bbase (se 3 (by rfl) ⟨761315, by rfl⟩ : syracuseStep 4060349 = 1522631) (by norm_num)
theorem B2569429 : Blo 1803603 2569429 := bbase (se 7 (by rfl) ⟨30110, by rfl⟩ : syracuseStep 2569429 = 60221) (by norm_num)
theorem B2282737 : Blo 1803603 2282737 := bbase (se 2 (by rfl) ⟨856026, by rfl⟩ : syracuseStep 2282737 = 1712053) (by norm_num)
theorem B4568309 : Blo 1803603 4568309 := bbase (se 5 (by rfl) ⟨214139, by rfl⟩ : syracuseStep 4568309 = 428279) (by norm_num)
theorem B2315509 : Blo 1803603 2315509 := bbase (se 5 (by rfl) ⟨108539, by rfl⟩ : syracuseStep 2315509 = 217079) (by norm_num)
theorem B3855613 : Blo 1803603 3855613 := bbase (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) (by norm_num)
theorem B4060421 : Blo 1803603 4060421 := bbase (se 4 (by rfl) ⟨380664, by rfl⟩ : syracuseStep 4060421 = 761329) (by norm_num)
theorem B3044621 : Blo 1803603 3044621 := bbase (se 3 (by rfl) ⟨570866, by rfl⟩ : syracuseStep 3044621 = 1141733) (by norm_num)
theorem B4060493 : Blo 1803603 4060493 := bbase (se 3 (by rfl) ⟨761342, by rfl⟩ : syracuseStep 4060493 = 1522685) (by norm_num)
theorem B2282833 : Blo 1803603 2282833 := bbase (se 2 (by rfl) ⟨856062, by rfl⟩ : syracuseStep 2282833 = 1712125) (by norm_num)
theorem B2168149 : Blo 1803603 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B6092117 : Blo 1803603 6092117 := bbase (se 13 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 6092117 = 2231) (by norm_num)
theorem B3044749 : Blo 1803603 3044749 := bbase (se 3 (by rfl) ⟨570890, by rfl⟩ : syracuseStep 3044749 = 1141781) (by norm_num)
theorem B4060565 : Blo 1803603 4060565 := bbase (se 6 (by rfl) ⟨95169, by rfl⟩ : syracuseStep 4060565 = 190339) (by norm_num)
theorem B3659165 : Blo 1803603 3659165 := bbase (se 3 (by rfl) ⟨686093, by rfl⟩ : syracuseStep 3659165 = 1372187) (by norm_num)
theorem B4568501 : Blo 1803603 4568501 := bbase (se 5 (by rfl) ⟨214148, by rfl⟩ : syracuseStep 4568501 = 428297) (by norm_num)
theorem B4117949 : Blo 1803603 4117949 := bbase (se 3 (by rfl) ⟨772115, by rfl⟩ : syracuseStep 4117949 = 1544231) (by norm_num)
theorem B4060637 : Blo 1803603 4060637 := bbase (se 3 (by rfl) ⟨761369, by rfl⟩ : syracuseStep 4060637 = 1522739) (by norm_num)
theorem B3044837 : Blo 1803603 3044837 := bbase (se 4 (by rfl) ⟨285453, by rfl⟩ : syracuseStep 3044837 = 570907) (by norm_num)
theorem B3659237 : Blo 1803603 3659237 := bbase (se 4 (by rfl) ⟨343053, by rfl⟩ : syracuseStep 3659237 = 686107) (by norm_num)
theorem B6174197 : Blo 1803603 6174197 := bbase (se 5 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 6174197 = 578831) (by norm_num)
theorem B2283005 : Blo 1803603 2283005 := bbase (se 3 (by rfl) ⟨428063, by rfl⟩ : syracuseStep 2283005 = 856127) (by norm_num)
theorem B2168317 : Blo 1803603 2168317 := bbase (se 3 (by rfl) ⟨406559, by rfl⟩ : syracuseStep 2168317 = 813119) (by norm_num)
theorem B6854165 : Blo 1803603 6854165 := bbase (se 6 (by rfl) ⟨160644, by rfl⟩ : syracuseStep 6854165 = 321289) (by norm_num)
theorem B2029081 : Blo 1803603 2029081 := bbase (se 2 (by rfl) ⟨760905, by rfl⟩ : syracuseStep 2029081 = 1521811) (by norm_num)
theorem B4060709 : Blo 1803603 4060709 := bbase (se 4 (by rfl) ⟨380691, by rfl⟩ : syracuseStep 4060709 = 761383) (by norm_num)
theorem B2283061 : Blo 1803603 2283061 := bbase (se 5 (by rfl) ⟨107018, by rfl⟩ : syracuseStep 2283061 = 214037) (by norm_num)
theorem B2029117 : Blo 1803603 2029117 := bbase (se 3 (by rfl) ⟨380459, by rfl⟩ : syracuseStep 2029117 = 760919) (by norm_num)
theorem B5781061 : Blo 1803603 5781061 := bbase (se 4 (by rfl) ⟨541974, by rfl⟩ : syracuseStep 5781061 = 1083949) (by norm_num)
theorem B2029153 : Blo 1803603 2029153 := bbase (se 2 (by rfl) ⟨760932, by rfl⟩ : syracuseStep 2029153 = 1521865) (by norm_num)
theorem B3044965 : Blo 1803603 3044965 := bbase (se 4 (by rfl) ⟨285465, by rfl⟩ : syracuseStep 3044965 = 570931) (by norm_num)
theorem B4060781 : Blo 1803603 4060781 := bbase (se 3 (by rfl) ⟨761396, by rfl⟩ : syracuseStep 4060781 = 1522793) (by norm_num)
theorem B2029189 : Blo 1803603 2029189 := bbase (se 4 (by rfl) ⟨190236, by rfl⟩ : syracuseStep 2029189 = 380473) (by norm_num)
theorem B3905165 : Blo 1803603 3905165 := bbase (se 3 (by rfl) ⟨732218, by rfl⟩ : syracuseStep 3905165 = 1464437) (by norm_num)
theorem B2283157 : Blo 1803603 2283157 := bbase (se 6 (by rfl) ⟨53511, by rfl⟩ : syracuseStep 2283157 = 107023) (by norm_num)
theorem B9139877 : Blo 1803603 9139877 := bbase (se 4 (by rfl) ⟨856863, by rfl⟩ : syracuseStep 9139877 = 1713727) (by norm_num)
theorem B2029225 : Blo 1803603 2029225 := bbase (se 2 (by rfl) ⟨760959, by rfl⟩ : syracuseStep 2029225 = 1521919) (by norm_num)
theorem B4060853 : Blo 1803603 4060853 := bbase (se 5 (by rfl) ⟨190352, by rfl⟩ : syracuseStep 4060853 = 380705) (by norm_num)
theorem B3045053 : Blo 1803603 3045053 := bbase (se 3 (by rfl) ⟨570947, by rfl⟩ : syracuseStep 3045053 = 1141895) (by norm_num)
theorem B2168513 : Blo 1803603 2168513 := bbase (se 2 (by rfl) ⟨813192, by rfl⟩ : syracuseStep 2168513 = 1626385) (by norm_num)
theorem B2029261 : Blo 1803603 2029261 := bbase (se 3 (by rfl) ⟨380486, by rfl⟩ : syracuseStep 2029261 = 760973) (by norm_num)
theorem B3471077 : Blo 1803603 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B2029297 : Blo 1803603 2029297 := bbase (se 2 (by rfl) ⟨760986, by rfl⟩ : syracuseStep 2029297 = 1521973) (by norm_num)
theorem B4060925 : Blo 1803603 4060925 := bbase (se 3 (by rfl) ⟨761423, by rfl⟩ : syracuseStep 4060925 = 1522847) (by norm_num)
theorem B6092549 : Blo 1803603 6092549 := bbase (se 4 (by rfl) ⟨571176, by rfl⟩ : syracuseStep 6092549 = 1142353) (by norm_num)
theorem B4568845 : Blo 1803603 4568845 := bbase (se 3 (by rfl) ⟨856658, by rfl⟩ : syracuseStep 4568845 = 1713317) (by norm_num)
theorem B2029333 : Blo 1803603 2029333 := bbase (se 6 (by rfl) ⟨47562, by rfl⟩ : syracuseStep 2029333 = 95125) (by norm_num)
theorem B6854453 : Blo 1803603 6854453 := bbase (se 5 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 6854453 = 642605) (by norm_num)
theorem B2029369 : Blo 1803603 2029369 := bbase (se 2 (by rfl) ⟨761013, by rfl⟩ : syracuseStep 2029369 = 1522027) (by norm_num)
theorem B3045181 : Blo 1803603 3045181 := bbase (se 3 (by rfl) ⟨570971, by rfl⟩ : syracuseStep 3045181 = 1141943) (by norm_num)
theorem B2283329 : Blo 1803603 2283329 := bbase (se 2 (by rfl) ⟨856248, by rfl⟩ : syracuseStep 2283329 = 1712497) (by norm_num)
theorem B4060997 : Blo 1803603 4060997 := bbase (se 4 (by rfl) ⟨380718, by rfl⟩ : syracuseStep 4060997 = 761437) (by norm_num)
theorem B2029405 : Blo 1803603 2029405 := bbase (se 3 (by rfl) ⟨380513, by rfl⟩ : syracuseStep 2029405 = 761027) (by norm_num)
theorem B2283385 : Blo 1803603 2283385 := bbase (se 2 (by rfl) ⟨856269, by rfl⟩ : syracuseStep 2283385 = 1712539) (by norm_num)
theorem B4568957 : Blo 1803603 4568957 := bbase (se 3 (by rfl) ⟨856679, by rfl⟩ : syracuseStep 4568957 = 1713359) (by norm_num)
theorem B2029441 : Blo 1803603 2029441 := bbase (se 2 (by rfl) ⟨761040, by rfl⟩ : syracuseStep 2029441 = 1522081) (by norm_num)
theorem B4061069 : Blo 1803603 4061069 := bbase (se 3 (by rfl) ⟨761450, by rfl⟩ : syracuseStep 4061069 = 1522901) (by norm_num)
theorem B3045269 : Blo 1803603 3045269 := bbase (se 6 (by rfl) ⟨71373, by rfl⟩ : syracuseStep 3045269 = 142747) (by norm_num)
theorem B2029477 : Blo 1803603 2029477 := bbase (se 4 (by rfl) ⟨190263, by rfl⟩ : syracuseStep 2029477 = 380527) (by norm_num)
theorem B2029513 : Blo 1803603 2029513 := bbase (se 2 (by rfl) ⟨761067, by rfl⟩ : syracuseStep 2029513 = 1522135) (by norm_num)
theorem B2889685 : Blo 1803603 2889685 := bbase (se 7 (by rfl) ⟨33863, by rfl⟩ : syracuseStep 2889685 = 67727) (by norm_num)
theorem B4061141 : Blo 1803603 4061141 := bbase (se 7 (by rfl) ⟨47591, by rfl⟩ : syracuseStep 4061141 = 95183) (by norm_num)
theorem B2283481 : Blo 1803603 2283481 := bbase (se 2 (by rfl) ⟨856305, by rfl⟩ : syracuseStep 2283481 = 1712611) (by norm_num)
theorem B2029549 : Blo 1803603 2029549 := bbase (se 3 (by rfl) ⟨380540, by rfl⟩ : syracuseStep 2029549 = 761081) (by norm_num)
theorem B2570221 : Blo 1803603 2570221 := bbase (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) (by norm_num)
theorem B6944773 : Blo 1803603 6944773 := bbase (se 4 (by rfl) ⟨651072, by rfl⟩ : syracuseStep 6944773 = 1302145) (by norm_num)
theorem B2029585 : Blo 1803603 2029585 := bbase (se 2 (by rfl) ⟨761094, by rfl⟩ : syracuseStep 2029585 = 1522189) (by norm_num)
theorem B3045397 : Blo 1803603 3045397 := bbase (se 6 (by rfl) ⟨71376, by rfl⟩ : syracuseStep 3045397 = 142753) (by norm_num)
theorem B4061213 : Blo 1803603 4061213 := bbase (se 3 (by rfl) ⟨761477, by rfl⟩ : syracuseStep 4061213 = 1522955) (by norm_num)
theorem B2029621 : Blo 1803603 2029621 := bbase (se 5 (by rfl) ⟨95138, by rfl⟩ : syracuseStep 2029621 = 190277) (by norm_num)
theorem B4569149 : Blo 1803603 4569149 := bbase (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) (by norm_num)
theorem B9132101 : Blo 1803603 9132101 := bbase (se 4 (by rfl) ⟨856134, by rfl⟩ : syracuseStep 9132101 = 1712269) (by norm_num)
theorem B18782293 : Blo 1803603 18782293 := bbase (se 8 (by rfl) ⟨110052, by rfl⟩ : syracuseStep 18782293 = 220105) (by norm_num)
theorem B2029657 : Blo 1803603 2029657 := bbase (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) (by norm_num)
theorem B4061285 : Blo 1803603 4061285 := bbase (se 4 (by rfl) ⟨380745, by rfl⟩ : syracuseStep 4061285 = 761491) (by norm_num)
theorem B3045485 : Blo 1803603 3045485 := bbase (se 3 (by rfl) ⟨571028, by rfl⟩ : syracuseStep 3045485 = 1142057) (by norm_num)
theorem B2029693 : Blo 1803603 2029693 := bbase (se 3 (by rfl) ⟨380567, by rfl⟩ : syracuseStep 2029693 = 761135) (by norm_num)
theorem B2283653 : Blo 1803603 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B10279061 : Blo 1803603 10279061 := bbase (se 6 (by rfl) ⟨240915, by rfl⟩ : syracuseStep 10279061 = 481831) (by norm_num)
theorem B2029729 : Blo 1803603 2029729 := bbase (se 2 (by rfl) ⟨761148, by rfl⟩ : syracuseStep 2029729 = 1522297) (by norm_num)
theorem B4061357 : Blo 1803603 4061357 := bbase (se 3 (by rfl) ⟨761504, by rfl⟩ : syracuseStep 4061357 = 1523009) (by norm_num)
theorem B6092981 : Blo 1803603 6092981 := bbase (se 5 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 6092981 = 571217) (by norm_num)
theorem B2283709 : Blo 1803603 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B2029765 : Blo 1803603 2029765 := bbase (se 4 (by rfl) ⟨190290, by rfl⟩ : syracuseStep 2029765 = 380581) (by norm_num)
theorem B2029801 : Blo 1803603 2029801 := bbase (se 2 (by rfl) ⟨761175, by rfl⟩ : syracuseStep 2029801 = 1522351) (by norm_num)
theorem B3045613 : Blo 1803603 3045613 := bbase (se 3 (by rfl) ⟨571052, by rfl⟩ : syracuseStep 3045613 = 1142105) (by norm_num)
theorem B11565301 : Blo 1803603 11565301 := bbase (se 5 (by rfl) ⟨542123, by rfl⟩ : syracuseStep 11565301 = 1084247) (by norm_num)
theorem B4061429 : Blo 1803603 4061429 := bbase (se 5 (by rfl) ⟨190379, by rfl⟩ : syracuseStep 4061429 = 380759) (by norm_num)
theorem B2029837 : Blo 1803603 2029837 := bbase (se 3 (by rfl) ⟨380594, by rfl⟩ : syracuseStep 2029837 = 761189) (by norm_num)
theorem B2283805 : Blo 1803603 2283805 := bbase (se 3 (by rfl) ⟨428213, by rfl⟩ : syracuseStep 2283805 = 856427) (by norm_num)
theorem B2029873 : Blo 1803603 2029873 := bbase (se 2 (by rfl) ⟨761202, by rfl⟩ : syracuseStep 2029873 = 1522405) (by norm_num)
theorem B4061501 : Blo 1803603 4061501 := bbase (se 3 (by rfl) ⟨761531, by rfl⟩ : syracuseStep 4061501 = 1523063) (by norm_num)
theorem B2570557 : Blo 1803603 2570557 := bbase (se 3 (by rfl) ⟨481979, by rfl⟩ : syracuseStep 2570557 = 963959) (by norm_num)
theorem B3045701 : Blo 1803603 3045701 := bbase (se 4 (by rfl) ⟨285534, by rfl⟩ : syracuseStep 3045701 = 571069) (by norm_num)
theorem B9263429 : Blo 1803603 9263429 := bbase (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) (by norm_num)
theorem B2029909 : Blo 1803603 2029909 := bbase (se 10 (by rfl) ⟨2973, by rfl⟩ : syracuseStep 2029909 = 5947) (by norm_num)
theorem B6256997 : Blo 1803603 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B2029945 : Blo 1803603 2029945 := bbase (se 2 (by rfl) ⟨761229, by rfl⟩ : syracuseStep 2029945 = 1522459) (by norm_num)
theorem B4061573 : Blo 1803603 4061573 := bbase (se 4 (by rfl) ⟨380772, by rfl⟩ : syracuseStep 4061573 = 761545) (by norm_num)
theorem B4569493 : Blo 1803603 4569493 := bbase (se 6 (by rfl) ⟨107097, by rfl⟩ : syracuseStep 4569493 = 214195) (by norm_num)
theorem B2029981 : Blo 1803603 2029981 := bbase (se 3 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 2029981 = 761243) (by norm_num)
theorem B2030017 : Blo 1803603 2030017 := bbase (se 2 (by rfl) ⟨761256, by rfl⟩ : syracuseStep 2030017 = 1522513) (by norm_num)
theorem B3045829 : Blo 1803603 3045829 := bbase (se 4 (by rfl) ⟨285546, by rfl⟩ : syracuseStep 3045829 = 571093) (by norm_num)
theorem B2283977 : Blo 1803603 2283977 := bbase (se 2 (by rfl) ⟨856491, by rfl⟩ : syracuseStep 2283977 = 1712983) (by norm_num)
theorem B4061645 : Blo 1803603 4061645 := bbase (se 3 (by rfl) ⟨761558, by rfl⟩ : syracuseStep 4061645 = 1523117) (by norm_num)
theorem B6683093 : Blo 1803603 6683093 := bbase (se 7 (by rfl) ⟨78317, by rfl⟩ : syracuseStep 6683093 = 156635) (by norm_num)
theorem B7707109 : Blo 1803603 7707109 := bbase (se 4 (by rfl) ⟨722541, by rfl⟩ : syracuseStep 7707109 = 1445083) (by norm_num)
theorem B2030053 : Blo 1803603 2030053 := bbase (se 4 (by rfl) ⟨190317, by rfl⟩ : syracuseStep 2030053 = 380635) (by norm_num)
theorem B2742773 : Blo 1803603 2742773 := bbase (se 5 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 2742773 = 257135) (by norm_num)
theorem B7707125 : Blo 1803603 7707125 := bbase (se 5 (by rfl) ⟨361271, by rfl⟩ : syracuseStep 7707125 = 722543) (by norm_num)
theorem B2890237 : Blo 1803603 2890237 := bbase (se 3 (by rfl) ⟨541919, by rfl⟩ : syracuseStep 2890237 = 1083839) (by norm_num)
theorem B2284033 : Blo 1803603 2284033 := bbase (se 2 (by rfl) ⟨856512, by rfl⟩ : syracuseStep 2284033 = 1713025) (by norm_num)
theorem B4569605 : Blo 1803603 4569605 := bbase (se 4 (by rfl) ⟨428400, by rfl⟩ : syracuseStep 4569605 = 856801) (by norm_num)
theorem B2030089 : Blo 1803603 2030089 := bbase (se 2 (by rfl) ⟨761283, by rfl⟩ : syracuseStep 2030089 = 1522567) (by norm_num)
theorem B4061717 : Blo 1803603 4061717 := bbase (se 6 (by rfl) ⟨95196, by rfl⟩ : syracuseStep 4061717 = 190393) (by norm_num)
theorem B2570773 : Blo 1803603 2570773 := bbase (se 6 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 2570773 = 120505) (by norm_num)
theorem B3045917 : Blo 1803603 3045917 := bbase (se 3 (by rfl) ⟨571109, by rfl⟩ : syracuseStep 3045917 = 1142219) (by norm_num)
theorem B2030125 : Blo 1803603 2030125 := bbase (se 3 (by rfl) ⟨380648, by rfl⟩ : syracuseStep 2030125 = 761297) (by norm_num)
theorem B2030161 : Blo 1803603 2030161 := bbase (se 2 (by rfl) ⟨761310, by rfl⟩ : syracuseStep 2030161 = 1522621) (by norm_num)
theorem B4061789 : Blo 1803603 4061789 := bbase (se 3 (by rfl) ⟨761585, by rfl⟩ : syracuseStep 4061789 = 1523171) (by norm_num)
theorem B2284129 : Blo 1803603 2284129 := bbase (se 2 (by rfl) ⟨856548, by rfl⟩ : syracuseStep 2284129 = 1713097) (by norm_num)
theorem B6093413 : Blo 1803603 6093413 := bbase (se 4 (by rfl) ⟨571257, by rfl⟩ : syracuseStep 6093413 = 1142515) (by norm_num)
theorem B2030197 : Blo 1803603 2030197 := bbase (se 5 (by rfl) ⟨95165, by rfl⟩ : syracuseStep 2030197 = 190331) (by norm_num)
theorem B2030233 : Blo 1803603 2030233 := bbase (se 2 (by rfl) ⟨761337, by rfl⟩ : syracuseStep 2030233 = 1522675) (by norm_num)
theorem B3046045 : Blo 1803603 3046045 := bbase (se 3 (by rfl) ⟨571133, by rfl⟩ : syracuseStep 3046045 = 1142267) (by norm_num)
theorem B4061861 : Blo 1803603 4061861 := bbase (se 4 (by rfl) ⟨380799, by rfl⟩ : syracuseStep 4061861 = 761599) (by norm_num)
theorem B2030269 : Blo 1803603 2030269 := bbase (se 3 (by rfl) ⟨380675, by rfl⟩ : syracuseStep 2030269 = 761351) (by norm_num)
theorem B4569797 : Blo 1803603 4569797 := bbase (se 4 (by rfl) ⟨428418, by rfl⟩ : syracuseStep 4569797 = 856837) (by norm_num)
theorem B2030305 : Blo 1803603 2030305 := bbase (se 2 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 2030305 = 1522729) (by norm_num)
theorem B4061933 : Blo 1803603 4061933 := bbase (se 3 (by rfl) ⟨761612, by rfl⟩ : syracuseStep 4061933 = 1523225) (by norm_num)
theorem B8674037 : Blo 1803603 8674037 := bbase (se 5 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 8674037 = 813191) (by norm_num)
theorem B3046133 : Blo 1803603 3046133 := bbase (se 5 (by rfl) ⟨142787, by rfl⟩ : syracuseStep 3046133 = 285575) (by norm_num)
theorem B2890493 : Blo 1803603 2890493 := bbase (se 3 (by rfl) ⟨541967, by rfl⟩ : syracuseStep 2890493 = 1083935) (by norm_num)
theorem B2030341 : Blo 1803603 2030341 := bbase (se 4 (by rfl) ⟨190344, by rfl⟩ : syracuseStep 2030341 = 380689) (by norm_num)
theorem B2284301 : Blo 1803603 2284301 := bbase (se 3 (by rfl) ⟨428306, by rfl⟩ : syracuseStep 2284301 = 856613) (by norm_num)
theorem B2030377 : Blo 1803603 2030377 := bbase (se 2 (by rfl) ⟨761391, by rfl⟩ : syracuseStep 2030377 = 1522783) (by norm_num)
theorem B4062005 : Blo 1803603 4062005 := bbase (se 5 (by rfl) ⟨190406, by rfl⟩ : syracuseStep 4062005 = 380813) (by norm_num)
theorem B2284357 : Blo 1803603 2284357 := bbase (se 4 (by rfl) ⟨214158, by rfl⟩ : syracuseStep 2284357 = 428317) (by norm_num)
theorem B2030413 : Blo 1803603 2030413 := bbase (se 3 (by rfl) ⟨380702, by rfl⟩ : syracuseStep 2030413 = 761405) (by norm_num)
theorem B2030449 : Blo 1803603 2030449 := bbase (se 2 (by rfl) ⟨761418, by rfl⟩ : syracuseStep 2030449 = 1522837) (by norm_num)
theorem B3046261 : Blo 1803603 3046261 := bbase (se 5 (by rfl) ⟨142793, by rfl⟩ : syracuseStep 3046261 = 285587) (by norm_num)
theorem B4062077 : Blo 1803603 4062077 := bbase (se 3 (by rfl) ⟨761639, by rfl⟩ : syracuseStep 4062077 = 1523279) (by norm_num)
theorem B2030485 : Blo 1803603 2030485 := bbase (se 6 (by rfl) ⟨47589, by rfl⟩ : syracuseStep 2030485 = 95179) (by norm_num)
theorem B5782421 : Blo 1803603 5782421 := bbase (se 6 (by rfl) ⟨135525, by rfl⟩ : syracuseStep 5782421 = 271051) (by norm_num)
theorem B2284453 : Blo 1803603 2284453 := bbase (se 4 (by rfl) ⟨214167, by rfl⟩ : syracuseStep 2284453 = 428335) (by norm_num)
theorem B2030521 : Blo 1803603 2030521 := bbase (se 2 (by rfl) ⟨761445, by rfl⟩ : syracuseStep 2030521 = 1522891) (by norm_num)
theorem B4062149 : Blo 1803603 4062149 := bbase (se 4 (by rfl) ⟨380826, by rfl⟩ : syracuseStep 4062149 = 761653) (by norm_num)
theorem B3046349 : Blo 1803603 3046349 := bbase (se 3 (by rfl) ⟨571190, by rfl⟩ : syracuseStep 3046349 = 1142381) (by norm_num)
theorem B3521485 : Blo 1803603 3521485 := bbase (se 3 (by rfl) ⟨660278, by rfl⟩ : syracuseStep 3521485 = 1320557) (by norm_num)
theorem B6855637 : Blo 1803603 6855637 := bbase (se 7 (by rfl) ⟨80339, by rfl⟩ : syracuseStep 6855637 = 160679) (by norm_num)
theorem B2030557 : Blo 1803603 2030557 := bbase (se 3 (by rfl) ⟨380729, by rfl⟩ : syracuseStep 2030557 = 761459) (by norm_num)
theorem B2931677 : Blo 1803603 2931677 := bbase (se 3 (by rfl) ⟨549689, by rfl⟩ : syracuseStep 2931677 = 1099379) (by norm_num)
theorem B2030593 : Blo 1803603 2030593 := bbase (se 2 (by rfl) ⟨761472, by rfl⟩ : syracuseStep 2030593 = 1522945) (by norm_num)
theorem B4062221 : Blo 1803603 4062221 := bbase (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) (by norm_num)
theorem B5782549 : Blo 1803603 5782549 := bbase (se 6 (by rfl) ⟨135528, by rfl⟩ : syracuseStep 5782549 = 271057) (by norm_num)
theorem B6093845 : Blo 1803603 6093845 := bbase (se 6 (by rfl) ⟨142824, by rfl⟩ : syracuseStep 6093845 = 285649) (by norm_num)
theorem B4570141 : Blo 1803603 4570141 := bbase (se 3 (by rfl) ⟨856901, by rfl⟩ : syracuseStep 4570141 = 1713803) (by norm_num)
theorem B2030629 : Blo 1803603 2030629 := bbase (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) (by norm_num)
theorem B2030665 : Blo 1803603 2030665 := bbase (se 2 (by rfl) ⟨761499, by rfl⟩ : syracuseStep 2030665 = 1522999) (by norm_num)
theorem B3046477 : Blo 1803603 3046477 := bbase (se 3 (by rfl) ⟨571214, by rfl⟩ : syracuseStep 3046477 = 1142429) (by norm_num)
theorem B2284625 : Blo 1803603 2284625 := bbase (se 2 (by rfl) ⟨856734, by rfl⟩ : syracuseStep 2284625 = 1713469) (by norm_num)
theorem B15416405 : Blo 1803603 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B4062293 : Blo 1803603 4062293 := bbase (se 8 (by rfl) ⟨23802, by rfl⟩ : syracuseStep 4062293 = 47605) (by norm_num)
theorem B2030701 : Blo 1803603 2030701 := bbase (se 3 (by rfl) ⟨380756, by rfl⟩ : syracuseStep 2030701 = 761513) (by norm_num)
theorem B14630005 : Blo 1803603 14630005 := bbase (se 5 (by rfl) ⟨685781, by rfl⟩ : syracuseStep 14630005 = 1371563) (by norm_num)
theorem B2284681 : Blo 1803603 2284681 := bbase (se 2 (by rfl) ⟨856755, by rfl⟩ : syracuseStep 2284681 = 1713511) (by norm_num)
theorem B4570253 : Blo 1803603 4570253 := bbase (se 3 (by rfl) ⟨856922, by rfl⟩ : syracuseStep 4570253 = 1713845) (by norm_num)
theorem B2030737 : Blo 1803603 2030737 := bbase (se 2 (by rfl) ⟨761526, by rfl⟩ : syracuseStep 2030737 = 1523053) (by norm_num)
theorem B4062365 : Blo 1803603 4062365 := bbase (se 3 (by rfl) ⟨761693, by rfl⟩ : syracuseStep 4062365 = 1523387) (by norm_num)
theorem B2604197 : Blo 1803603 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B3046565 : Blo 1803603 3046565 := bbase (se 4 (by rfl) ⟨285615, by rfl⟩ : syracuseStep 3046565 = 571231) (by norm_num)
theorem B2030773 : Blo 1803603 2030773 := bbase (se 5 (by rfl) ⟨95192, by rfl⟩ : syracuseStep 2030773 = 190385) (by norm_num)
theorem B2030809 : Blo 1803603 2030809 := bbase (se 2 (by rfl) ⟨761553, by rfl⟩ : syracuseStep 2030809 = 1523107) (by norm_num)
theorem B4062437 : Blo 1803603 4062437 := bbase (se 4 (by rfl) ⟨380853, by rfl⟩ : syracuseStep 4062437 = 761707) (by norm_num)
theorem B2284777 : Blo 1803603 2284777 := bbase (se 2 (by rfl) ⟨856791, by rfl⟩ : syracuseStep 2284777 = 1713583) (by norm_num)
theorem B2604277 : Blo 1803603 2604277 := bbase (se 5 (by rfl) ⟨122075, by rfl⟩ : syracuseStep 2604277 = 244151) (by norm_num)
theorem B2030845 : Blo 1803603 2030845 := bbase (se 3 (by rfl) ⟨380783, by rfl⟩ : syracuseStep 2030845 = 761567) (by norm_num)
theorem B5782805 : Blo 1803603 5782805 := bbase (se 6 (by rfl) ⟨135534, by rfl⟩ : syracuseStep 5782805 = 271069) (by norm_num)
theorem B2030881 : Blo 1803603 2030881 := bbase (se 2 (by rfl) ⟨761580, by rfl⟩ : syracuseStep 2030881 = 1523161) (by norm_num)
theorem B3046693 : Blo 1803603 3046693 := bbase (se 4 (by rfl) ⟨285627, by rfl⟩ : syracuseStep 3046693 = 571255) (by norm_num)
theorem B4062509 : Blo 1803603 4062509 := bbase (se 3 (by rfl) ⟨761720, by rfl⟩ : syracuseStep 4062509 = 1523441) (by norm_num)
theorem B2030917 : Blo 1803603 2030917 := bbase (se 4 (by rfl) ⟨190398, by rfl⟩ : syracuseStep 2030917 = 380797) (by norm_num)
theorem B9133397 : Blo 1803603 9133397 := bbase (se 11 (by rfl) ⟨6689, by rfl⟩ : syracuseStep 9133397 = 13379) (by norm_num)
theorem B3087701 : Blo 1803603 3087701 := bbase (se 11 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 3087701 = 4523) (by norm_num)
theorem B2030953 : Blo 1803603 2030953 := bbase (se 2 (by rfl) ⟨761607, by rfl⟩ : syracuseStep 2030953 = 1523215) (by norm_num)
theorem B4062581 : Blo 1803603 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B3046781 : Blo 1803603 3046781 := bbase (se 3 (by rfl) ⟨571271, by rfl⟩ : syracuseStep 3046781 = 1142543) (by norm_num)
theorem B2030989 : Blo 1803603 2030989 := bbase (se 3 (by rfl) ⟨380810, by rfl⟩ : syracuseStep 2030989 = 761621) (by norm_num)
theorem B2473357 : Blo 1803603 2473357 := bbase (se 3 (by rfl) ⟨463754, by rfl⟩ : syracuseStep 2473357 = 927509) (by norm_num)
theorem B2284949 : Blo 1803603 2284949 := bbase (se 6 (by rfl) ⟨53553, by rfl⟩ : syracuseStep 2284949 = 107107) (by norm_num)
theorem B2031025 : Blo 1803603 2031025 := bbase (se 2 (by rfl) ⟨761634, by rfl⟩ : syracuseStep 2031025 = 1523269) (by norm_num)
theorem B2891197 : Blo 1803603 2891197 := bbase (se 3 (by rfl) ⟨542099, by rfl⟩ : syracuseStep 2891197 = 1084199) (by norm_num)
theorem B2285005 : Blo 1803603 2285005 := bbase (se 3 (by rfl) ⟨428438, by rfl⟩ : syracuseStep 2285005 = 856877) (by norm_num)
theorem B2031061 : Blo 1803603 2031061 := bbase (se 7 (by rfl) ⟨23801, by rfl⟩ : syracuseStep 2031061 = 47603) (by norm_num)
theorem B2031097 : Blo 1803603 2031097 := bbase (se 2 (by rfl) ⟨761661, by rfl⟩ : syracuseStep 2031097 = 1523323) (by norm_num)
theorem B3046909 : Blo 1803603 3046909 := bbase (se 3 (by rfl) ⟨571295, by rfl⟩ : syracuseStep 3046909 = 1142591) (by norm_num)
theorem B2031133 : Blo 1803603 2031133 := bbase (se 3 (by rfl) ⟨380837, by rfl⟩ : syracuseStep 2031133 = 761675) (by norm_num)
theorem B2285101 : Blo 1803603 2285101 := bbase (se 3 (by rfl) ⟨428456, by rfl⟩ : syracuseStep 2285101 = 856913) (by norm_num)
theorem B2031169 : Blo 1803603 2031169 := bbase (se 2 (by rfl) ⟨761688, by rfl⟩ : syracuseStep 2031169 = 1523377) (by norm_num)
theorem B18775637 : Blo 1803603 18775637 := bbase (se 8 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 18775637 = 220027) (by norm_num)
theorem B2031205 : Blo 1803603 2031205 := bbase (se 4 (by rfl) ⟨190425, by rfl⟩ : syracuseStep 2031205 = 380851) (by norm_num)
theorem B2031241 : Blo 1803603 2031241 := bbase (se 2 (by rfl) ⟨761715, by rfl⟩ : syracuseStep 2031241 = 1523431) (by norm_num)
theorem B6848165 : Blo 1803603 6848165 := bbase (se 4 (by rfl) ⟨642015, by rfl⟩ : syracuseStep 6848165 = 1284031) (by norm_num)
theorem B2031277 : Blo 1803603 2031277 := bbase (se 3 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 2031277 = 761729) (by norm_num)
theorem B12353269 : Blo 1803603 12353269 := bbase (se 5 (by rfl) ⟨579059, by rfl⟩ : syracuseStep 12353269 = 1158119) (by norm_num)
theorem B3424045 : Blo 1803603 3424045 := bbase (se 3 (by rfl) ⟨642008, by rfl⟩ : syracuseStep 3424045 = 1284017) (by norm_num)
theorem B2891621 : Blo 1803603 2891621 := bbase (se 4 (by rfl) ⟨271089, by rfl⟩ : syracuseStep 2891621 = 542179) (by norm_num)
theorem B3424189 : Blo 1803603 3424189 := bbase (se 3 (by rfl) ⟨642035, by rfl⟩ : syracuseStep 3424189 = 1284071) (by norm_num)
theorem B25043057 : Blo 1803603 25043057 := bstep (se 2 (by rfl) ⟨9391146, by rfl⟩ : syracuseStep 25043057 = 18782293) B18782293
theorem B8790221 : Blo 1803603 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B13000931 : Blo 1803603 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B5136625 : Blo 1803603 5136625 := bstep (se 2 (by rfl) ⟨1926234, by rfl⟩ : syracuseStep 5136625 = 3852469) B3852469
theorem B16695665 : Blo 1803603 16695665 := bstep (se 2 (by rfl) ⟨6260874, by rfl⟩ : syracuseStep 16695665 = 12521749) B12521749
theorem B3424675 : Blo 1803603 3424675 := bstep (se 1 (by rfl) ⟨2568506, by rfl⟩ : syracuseStep 3424675 = 5137013) B5137013
theorem B10273229 : Blo 1803603 10273229 := bstep (se 3 (by rfl) ⟨1926230, by rfl⟩ : syracuseStep 10273229 = 3852461) B3852461
theorem B6087203 : Blo 1803603 6087203 := bstep (se 1 (by rfl) ⟨4565402, by rfl⟩ : syracuseStep 6087203 = 9130805) B9130805
theorem B3424835 : Blo 1803603 3424835 := bstep (se 1 (by rfl) ⟨2568626, by rfl⟩ : syracuseStep 3424835 = 5137253) B5137253
theorem B6849137 : Blo 1803603 6849137 := bstep (se 2 (by rfl) ⟨2568426, by rfl⟩ : syracuseStep 6849137 = 5136853) B5136853
theorem B3130049 : Blo 1803603 3130049 := bstep (se 2 (by rfl) ⟨1173768, by rfl⟩ : syracuseStep 3130049 = 2347537) B2347537
theorem B6087473 : Blo 1803603 6087473 := bstep (se 2 (by rfl) ⟨2282802, by rfl⟩ : syracuseStep 6087473 = 4565605) B4565605
theorem B2745299 : Blo 1803603 2745299 := bstep (se 1 (by rfl) ⟨2058974, by rfl⟩ : syracuseStep 2745299 = 4117949) B4117949
theorem B3130577 : Blo 1803603 3130577 := bstep (se 2 (by rfl) ⟨1173966, by rfl⟩ : syracuseStep 3130577 = 2347933) B2347933
theorem B4113649 : Blo 1803603 4113649 := bstep (se 2 (by rfl) ⟨1542618, by rfl⟩ : syracuseStep 4113649 = 3085237) B3085237
theorem B6849805 : Blo 1803603 6849805 := bstep (se 3 (by rfl) ⟨1284338, by rfl⟩ : syracuseStep 6849805 = 2568677) B2568677
theorem B6088013 : Blo 1803603 6088013 := bstep (se 3 (by rfl) ⟨1141502, by rfl⟩ : syracuseStep 6088013 = 2283005) B2283005
theorem B1803603 : Blo 1803603 1803603 := bstep (se 1 (by rfl) ⟨1352702, by rfl⟩ : syracuseStep 1803603 = 2705405) B2705405
theorem B1803619 : Blo 1803603 1803619 := bstep (se 1 (by rfl) ⟨1352714, by rfl⟩ : syracuseStep 1803619 = 2705429) B2705429
theorem B10274161 : Blo 1803603 10274161 := bstep (se 2 (by rfl) ⟨3852810, by rfl⟩ : syracuseStep 10274161 = 7705621) B7705621
theorem B7710065 : Blo 1803603 7710065 := bstep (se 2 (by rfl) ⟨2891274, by rfl⟩ : syracuseStep 7710065 = 5782549) B5782549
theorem B1803635 : Blo 1803603 1803635 := bstep (se 1 (by rfl) ⟨1352726, by rfl⟩ : syracuseStep 1803635 = 2705453) B2705453
theorem B1803651 : Blo 1803603 1803651 := bstep (se 1 (by rfl) ⟨1352738, by rfl⟩ : syracuseStep 1803651 = 2705477) B2705477
theorem B6088067 : Blo 1803603 6088067 := bstep (se 1 (by rfl) ⟨4566050, by rfl⟩ : syracuseStep 6088067 = 9132101) B9132101
theorem B1803667 : Blo 1803603 1803667 := bstep (se 1 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 1803667 = 2705501) B2705501
theorem B1803683 : Blo 1803603 1803683 := bstep (se 1 (by rfl) ⟨1352762, by rfl⟩ : syracuseStep 1803683 = 2705525) B2705525
theorem B1803699 : Blo 1803603 1803699 := bstep (se 1 (by rfl) ⟨1352774, by rfl⟩ : syracuseStep 1803699 = 2705549) B2705549
theorem B1803715 : Blo 1803603 1803715 := bstep (se 1 (by rfl) ⟨1352786, by rfl⟩ : syracuseStep 1803715 = 2705573) B2705573
theorem B1803731 : Blo 1803603 1803731 := bstep (se 1 (by rfl) ⟨1352798, by rfl⟩ : syracuseStep 1803731 = 2705597) B2705597
theorem B1803747 : Blo 1803603 1803747 := bstep (se 1 (by rfl) ⟨1352810, by rfl⟩ : syracuseStep 1803747 = 2705621) B2705621
theorem B5137901 : Blo 1803603 5137901 := bstep (se 3 (by rfl) ⟨963356, by rfl⟩ : syracuseStep 5137901 = 1926713) B1926713
theorem B19506673 : Blo 1803603 19506673 := bstep (se 2 (by rfl) ⟨7315002, by rfl⟩ : syracuseStep 19506673 = 14630005) B14630005
theorem B1803763 : Blo 1803603 1803763 := bstep (se 1 (by rfl) ⟨1352822, by rfl⟩ : syracuseStep 1803763 = 2705645) B2705645
theorem B1803779 : Blo 1803603 1803779 := bstep (se 1 (by rfl) ⟨1352834, by rfl⟩ : syracuseStep 1803779 = 2705669) B2705669
theorem B1803795 : Blo 1803603 1803795 := bstep (se 1 (by rfl) ⟨1352846, by rfl⟩ : syracuseStep 1803795 = 2705693) B2705693
theorem B1803811 : Blo 1803603 1803811 := bstep (se 1 (by rfl) ⟨1352858, by rfl⟩ : syracuseStep 1803811 = 2705717) B2705717
theorem B9135665 : Blo 1803603 9135665 := bstep (se 2 (by rfl) ⟨3425874, by rfl⟩ : syracuseStep 9135665 = 6851749) B6851749
theorem B1803827 : Blo 1803603 1803827 := bstep (se 1 (by rfl) ⟨1352870, by rfl⟩ : syracuseStep 1803827 = 2705741) B2705741
theorem B1803843 : Blo 1803603 1803843 := bstep (se 1 (by rfl) ⟨1352882, by rfl⟩ : syracuseStep 1803843 = 2705765) B2705765
theorem B4171331 : Blo 1803603 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B1803859 : Blo 1803603 1803859 := bstep (se 1 (by rfl) ⟨1352894, by rfl⟩ : syracuseStep 1803859 = 2705789) B2705789
theorem B1803875 : Blo 1803603 1803875 := bstep (se 1 (by rfl) ⟨1352906, by rfl⟩ : syracuseStep 1803875 = 2705813) B2705813
theorem B3425905 : Blo 1803603 3425905 := bstep (se 2 (by rfl) ⟨1284714, by rfl⟩ : syracuseStep 3425905 = 2569429) B2569429
theorem B1803891 : Blo 1803603 1803891 := bstep (se 1 (by rfl) ⟨1352918, by rfl⟩ : syracuseStep 1803891 = 2705837) B2705837
theorem B1803907 : Blo 1803603 1803907 := bstep (se 1 (by rfl) ⟨1352930, by rfl⟩ : syracuseStep 1803907 = 2705861) B2705861
theorem B6088337 : Blo 1803603 6088337 := bstep (se 2 (by rfl) ⟨2283126, by rfl⟩ : syracuseStep 6088337 = 4566253) B4566253
theorem B1803923 : Blo 1803603 1803923 := bstep (se 1 (by rfl) ⟨1352942, by rfl⟩ : syracuseStep 1803923 = 2705885) B2705885
theorem B1803939 : Blo 1803603 1803939 := bstep (se 1 (by rfl) ⟨1352954, by rfl⟩ : syracuseStep 1803939 = 2705909) B2705909
theorem B5138083 : Blo 1803603 5138083 := bstep (se 1 (by rfl) ⟨3853562, by rfl⟩ : syracuseStep 5138083 = 7707125) B7707125
theorem B1803955 : Blo 1803603 1803955 := bstep (se 1 (by rfl) ⟨1352966, by rfl⟩ : syracuseStep 1803955 = 2705933) B2705933
theorem B1803971 : Blo 1803603 1803971 := bstep (se 1 (by rfl) ⟨1352978, by rfl⟩ : syracuseStep 1803971 = 2705957) B2705957
theorem B5138129 : Blo 1803603 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B1803987 : Blo 1803603 1803987 := bstep (se 1 (by rfl) ⟨1352990, by rfl⟩ : syracuseStep 1803987 = 2705981) B2705981
theorem B1804003 : Blo 1803603 1804003 := bstep (se 1 (by rfl) ⟨1353002, by rfl⟩ : syracuseStep 1804003 = 2706005) B2706005
theorem B5490413 : Blo 1803603 5490413 := bstep (se 3 (by rfl) ⟨1029452, by rfl⟩ : syracuseStep 5490413 = 2058905) B2058905
theorem B1804019 : Blo 1803603 1804019 := bstep (se 1 (by rfl) ⟨1353014, by rfl⟩ : syracuseStep 1804019 = 2706029) B2706029
theorem B1804035 : Blo 1803603 1804035 := bstep (se 1 (by rfl) ⟨1353026, by rfl⟩ : syracuseStep 1804035 = 2706053) B2706053
theorem B1804051 : Blo 1803603 1804051 := bstep (se 1 (by rfl) ⟨1353038, by rfl⟩ : syracuseStep 1804051 = 2706077) B2706077
theorem B1804067 : Blo 1803603 1804067 := bstep (se 1 (by rfl) ⟨1353050, by rfl⟩ : syracuseStep 1804067 = 2706101) B2706101
theorem B1804083 : Blo 1803603 1804083 := bstep (se 1 (by rfl) ⟨1353062, by rfl⟩ : syracuseStep 1804083 = 2706125) B2706125
theorem B1804099 : Blo 1803603 1804099 := bstep (se 1 (by rfl) ⟨1353074, by rfl⟩ : syracuseStep 1804099 = 2706149) B2706149
theorem B1804115 : Blo 1803603 1804115 := bstep (se 1 (by rfl) ⟨1353086, by rfl⟩ : syracuseStep 1804115 = 2706173) B2706173
theorem B1926995 : Blo 1803603 1926995 := bstep (se 1 (by rfl) ⟨1445246, by rfl⟩ : syracuseStep 1926995 = 2890493) B2890493
theorem B1804131 : Blo 1803603 1804131 := bstep (se 1 (by rfl) ⟨1353098, by rfl⟩ : syracuseStep 1804131 = 2706197) B2706197
theorem B1804147 : Blo 1803603 1804147 := bstep (se 1 (by rfl) ⟨1353110, by rfl⟩ : syracuseStep 1804147 = 2706221) B2706221
theorem B1804163 : Blo 1803603 1804163 := bstep (se 1 (by rfl) ⟨1353122, by rfl⟩ : syracuseStep 1804163 = 2706245) B2706245
theorem B1804179 : Blo 1803603 1804179 := bstep (se 1 (by rfl) ⟨1353134, by rfl⟩ : syracuseStep 1804179 = 2706269) B2706269
theorem B1804195 : Blo 1803603 1804195 := bstep (se 1 (by rfl) ⟨1353146, by rfl⟩ : syracuseStep 1804195 = 2706293) B2706293
theorem B1804211 : Blo 1803603 1804211 := bstep (se 1 (by rfl) ⟨1353158, by rfl⟩ : syracuseStep 1804211 = 2706317) B2706317
theorem B1804227 : Blo 1803603 1804227 := bstep (se 1 (by rfl) ⟨1353170, by rfl⟩ : syracuseStep 1804227 = 2706341) B2706341
theorem B1804243 : Blo 1803603 1804243 := bstep (se 1 (by rfl) ⟨1353182, by rfl⟩ : syracuseStep 1804243 = 2706365) B2706365
theorem B1804259 : Blo 1803603 1804259 := bstep (se 1 (by rfl) ⟨1353194, by rfl⟩ : syracuseStep 1804259 = 2706389) B2706389
theorem B1804275 : Blo 1803603 1804275 := bstep (se 1 (by rfl) ⟨1353206, by rfl⟩ : syracuseStep 1804275 = 2706413) B2706413
theorem B2705411 : Blo 1803603 2705411 := bstep (se 1 (by rfl) ⟨2029058, by rfl⟩ : syracuseStep 2705411 = 4058117) B4058117
theorem B1804291 : Blo 1803603 1804291 := bstep (se 1 (by rfl) ⟨1353218, by rfl⟩ : syracuseStep 1804291 = 2706437) B2706437
theorem B1804307 : Blo 1803603 1804307 := bstep (se 1 (by rfl) ⟨1353230, by rfl⟩ : syracuseStep 1804307 = 2706461) B2706461
theorem B2705441 : Blo 1803603 2705441 := bstep (se 2 (by rfl) ⟨1014540, by rfl⟩ : syracuseStep 2705441 = 2029081) B2029081
theorem B6850595 : Blo 1803603 6850595 := bstep (se 1 (by rfl) ⟨5137946, by rfl⟩ : syracuseStep 6850595 = 10275893) B10275893
theorem B1804323 : Blo 1803603 1804323 := bstep (se 1 (by rfl) ⟨1353242, by rfl⟩ : syracuseStep 1804323 = 2706485) B2706485
theorem B2705459 : Blo 1803603 2705459 := bstep (se 1 (by rfl) ⟨2029094, by rfl⟩ : syracuseStep 2705459 = 4058189) B4058189
theorem B1804339 : Blo 1803603 1804339 := bstep (se 1 (by rfl) ⟨1353254, by rfl⟩ : syracuseStep 1804339 = 2706509) B2706509
theorem B1804355 : Blo 1803603 1804355 := bstep (se 1 (by rfl) ⟨1353266, by rfl⟩ : syracuseStep 1804355 = 2706533) B2706533
theorem B2705489 : Blo 1803603 2705489 := bstep (se 2 (by rfl) ⟨1014558, by rfl⟩ : syracuseStep 2705489 = 2029117) B2029117
theorem B1804371 : Blo 1803603 1804371 := bstep (se 1 (by rfl) ⟨1353278, by rfl⟩ : syracuseStep 1804371 = 2706557) B2706557
theorem B2705507 : Blo 1803603 2705507 := bstep (se 1 (by rfl) ⟨2029130, by rfl⟩ : syracuseStep 2705507 = 4058261) B4058261
theorem B1804387 : Blo 1803603 1804387 := bstep (se 1 (by rfl) ⟨1353290, by rfl⟩ : syracuseStep 1804387 = 2706581) B2706581
theorem B1804403 : Blo 1803603 1804403 := bstep (se 1 (by rfl) ⟨1353302, by rfl⟩ : syracuseStep 1804403 = 2706605) B2706605
theorem B2705537 : Blo 1803603 2705537 := bstep (se 2 (by rfl) ⟨1014576, by rfl⟩ : syracuseStep 2705537 = 2029153) B2029153
theorem B1804419 : Blo 1803603 1804419 := bstep (se 1 (by rfl) ⟨1353314, by rfl⟩ : syracuseStep 1804419 = 2706629) B2706629
theorem B2705555 : Blo 1803603 2705555 := bstep (se 1 (by rfl) ⟨2029166, by rfl⟩ : syracuseStep 2705555 = 4058333) B4058333
theorem B1804435 : Blo 1803603 1804435 := bstep (se 1 (by rfl) ⟨1353326, by rfl⟩ : syracuseStep 1804435 = 2706653) B2706653
theorem B1804451 : Blo 1803603 1804451 := bstep (se 1 (by rfl) ⟨1353338, by rfl⟩ : syracuseStep 1804451 = 2706677) B2706677
theorem B6088877 : Blo 1803603 6088877 := bstep (se 3 (by rfl) ⟨1141664, by rfl⟩ : syracuseStep 6088877 = 2283329) B2283329
theorem B2705585 : Blo 1803603 2705585 := bstep (se 2 (by rfl) ⟨1014594, by rfl⟩ : syracuseStep 2705585 = 2029189) B2029189
theorem B1804467 : Blo 1803603 1804467 := bstep (se 1 (by rfl) ⟨1353350, by rfl⟩ : syracuseStep 1804467 = 2706701) B2706701
theorem B2705603 : Blo 1803603 2705603 := bstep (se 1 (by rfl) ⟨2029202, by rfl⟩ : syracuseStep 2705603 = 4058405) B4058405
theorem B1804483 : Blo 1803603 1804483 := bstep (se 1 (by rfl) ⟨1353362, by rfl⟩ : syracuseStep 1804483 = 2706725) B2706725
theorem B1804499 : Blo 1803603 1804499 := bstep (se 1 (by rfl) ⟨1353374, by rfl⟩ : syracuseStep 1804499 = 2706749) B2706749
theorem B2705633 : Blo 1803603 2705633 := bstep (se 2 (by rfl) ⟨1014612, by rfl⟩ : syracuseStep 2705633 = 2029225) B2029225
theorem B6088931 : Blo 1803603 6088931 := bstep (se 1 (by rfl) ⟨4566698, by rfl⟩ : syracuseStep 6088931 = 9133397) B9133397
theorem B1804515 : Blo 1803603 1804515 := bstep (se 1 (by rfl) ⟨1353386, by rfl⟩ : syracuseStep 1804515 = 2706773) B2706773
theorem B2058467 : Blo 1803603 2058467 := bstep (se 1 (by rfl) ⟨1543850, by rfl⟩ : syracuseStep 2058467 = 3087701) B3087701
theorem B11561201 : Blo 1803603 11561201 := bstep (se 2 (by rfl) ⟨4335450, by rfl⟩ : syracuseStep 11561201 = 8670901) B8670901
theorem B2705651 : Blo 1803603 2705651 := bstep (se 1 (by rfl) ⟨2029238, by rfl⟩ : syracuseStep 2705651 = 4058477) B4058477
theorem B1804531 : Blo 1803603 1804531 := bstep (se 1 (by rfl) ⟨1353398, by rfl⟩ : syracuseStep 1804531 = 2706797) B2706797
theorem B1804547 : Blo 1803603 1804547 := bstep (se 1 (by rfl) ⟨1353410, by rfl⟩ : syracuseStep 1804547 = 2706821) B2706821
theorem B2705681 : Blo 1803603 2705681 := bstep (se 2 (by rfl) ⟨1014630, by rfl⟩ : syracuseStep 2705681 = 2029261) B2029261
theorem B1804563 : Blo 1803603 1804563 := bstep (se 1 (by rfl) ⟨1353422, by rfl⟩ : syracuseStep 1804563 = 2706845) B2706845
theorem B2705699 : Blo 1803603 2705699 := bstep (se 1 (by rfl) ⟨2029274, by rfl⟩ : syracuseStep 2705699 = 4058549) B4058549
theorem B1804579 : Blo 1803603 1804579 := bstep (se 1 (by rfl) ⟨1353434, by rfl⟩ : syracuseStep 1804579 = 2706869) B2706869
theorem B1804595 : Blo 1803603 1804595 := bstep (se 1 (by rfl) ⟨1353446, by rfl⟩ : syracuseStep 1804595 = 2706893) B2706893
theorem B2705729 : Blo 1803603 2705729 := bstep (se 2 (by rfl) ⟨1014648, by rfl⟩ : syracuseStep 2705729 = 2029297) B2029297
theorem B1804611 : Blo 1803603 1804611 := bstep (se 1 (by rfl) ⟨1353458, by rfl⟩ : syracuseStep 1804611 = 2706917) B2706917
theorem B15419717 : Blo 1803603 15419717 := bstep (se 4 (by rfl) ⟨1445598, by rfl⟩ : syracuseStep 15419717 = 2891197) B2891197
theorem B2705747 : Blo 1803603 2705747 := bstep (se 1 (by rfl) ⟨2029310, by rfl⟩ : syracuseStep 2705747 = 4058621) B4058621
theorem B1804627 : Blo 1803603 1804627 := bstep (se 1 (by rfl) ⟨1353470, by rfl⟩ : syracuseStep 1804627 = 2706941) B2706941
theorem B1804643 : Blo 1803603 1804643 := bstep (se 1 (by rfl) ⟨1353482, by rfl⟩ : syracuseStep 1804643 = 2706965) B2706965
theorem B2705777 : Blo 1803603 2705777 := bstep (se 2 (by rfl) ⟨1014666, by rfl⟩ : syracuseStep 2705777 = 2029333) B2029333
theorem B1804659 : Blo 1803603 1804659 := bstep (se 1 (by rfl) ⟨1353494, by rfl⟩ : syracuseStep 1804659 = 2706989) B2706989
theorem B2705795 : Blo 1803603 2705795 := bstep (se 1 (by rfl) ⟨2029346, by rfl⟩ : syracuseStep 2705795 = 4058693) B4058693
theorem B1804675 : Blo 1803603 1804675 := bstep (se 1 (by rfl) ⟨1353506, by rfl⟩ : syracuseStep 1804675 = 2707013) B2707013
theorem B4565393 : Blo 1803603 4565393 := bstep (se 2 (by rfl) ⟨1712022, by rfl⟩ : syracuseStep 4565393 = 3424045) B3424045
theorem B1804691 : Blo 1803603 1804691 := bstep (se 1 (by rfl) ⟨1353518, by rfl⟩ : syracuseStep 1804691 = 2707037) B2707037
theorem B2705825 : Blo 1803603 2705825 := bstep (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) B2029369
theorem B1804707 : Blo 1803603 1804707 := bstep (se 1 (by rfl) ⟨1353530, by rfl⟩ : syracuseStep 1804707 = 2707061) B2707061
theorem B2705843 : Blo 1803603 2705843 := bstep (se 1 (by rfl) ⟨2029382, by rfl⟩ : syracuseStep 2705843 = 4058765) B4058765
theorem B1804723 : Blo 1803603 1804723 := bstep (se 1 (by rfl) ⟨1353542, by rfl⟩ : syracuseStep 1804723 = 2707085) B2707085
theorem B4565443 : Blo 1803603 4565443 := bstep (se 1 (by rfl) ⟨3424082, by rfl⟩ : syracuseStep 4565443 = 6848165) B6848165
theorem B1804739 : Blo 1803603 1804739 := bstep (se 1 (by rfl) ⟨1353554, by rfl⟩ : syracuseStep 1804739 = 2707109) B2707109
theorem B15411653 : Blo 1803603 15411653 := bstep (se 4 (by rfl) ⟨1444842, by rfl⟩ : syracuseStep 15411653 = 2889685) B2889685
theorem B2705873 : Blo 1803603 2705873 := bstep (se 2 (by rfl) ⟨1014702, by rfl⟩ : syracuseStep 2705873 = 2029405) B2029405
theorem B1804755 : Blo 1803603 1804755 := bstep (se 1 (by rfl) ⟨1353566, by rfl⟩ : syracuseStep 1804755 = 2707133) B2707133
theorem B2705891 : Blo 1803603 2705891 := bstep (se 1 (by rfl) ⟨2029418, by rfl⟩ : syracuseStep 2705891 = 4058837) B4058837
theorem B1804771 : Blo 1803603 1804771 := bstep (se 1 (by rfl) ⟨1353578, by rfl⟩ : syracuseStep 1804771 = 2707157) B2707157
theorem B6089201 : Blo 1803603 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B1804787 : Blo 1803603 1804787 := bstep (se 1 (by rfl) ⟨1353590, by rfl⟩ : syracuseStep 1804787 = 2707181) B2707181
theorem B2705921 : Blo 1803603 2705921 := bstep (se 2 (by rfl) ⟨1014720, by rfl⟩ : syracuseStep 2705921 = 2029441) B2029441
theorem B1804803 : Blo 1803603 1804803 := bstep (se 1 (by rfl) ⟨1353602, by rfl⟩ : syracuseStep 1804803 = 2707205) B2707205
theorem B2705939 : Blo 1803603 2705939 := bstep (se 1 (by rfl) ⟨2029454, by rfl⟩ : syracuseStep 2705939 = 4058909) B4058909
theorem B1804819 : Blo 1803603 1804819 := bstep (se 1 (by rfl) ⟨1353614, by rfl⟩ : syracuseStep 1804819 = 2707229) B2707229
theorem B1804835 : Blo 1803603 1804835 := bstep (se 1 (by rfl) ⟨1353626, by rfl⟩ : syracuseStep 1804835 = 2707253) B2707253
theorem B2705969 : Blo 1803603 2705969 := bstep (se 2 (by rfl) ⟨1014738, by rfl⟩ : syracuseStep 2705969 = 2029477) B2029477
theorem B20556341 : Blo 1803603 20556341 := bstep (se 5 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 20556341 = 1927157) B1927157
theorem B1804851 : Blo 1803603 1804851 := bstep (se 1 (by rfl) ⟨1353638, by rfl⟩ : syracuseStep 1804851 = 2707277) B2707277
theorem B2705987 : Blo 1803603 2705987 := bstep (se 1 (by rfl) ⟨2029490, by rfl⟩ : syracuseStep 2705987 = 4058981) B4058981
theorem B1804867 : Blo 1803603 1804867 := bstep (se 1 (by rfl) ⟨1353650, by rfl⟩ : syracuseStep 1804867 = 2707301) B2707301
theorem B1927747 : Blo 1803603 1927747 := bstep (se 1 (by rfl) ⟨1445810, by rfl⟩ : syracuseStep 1927747 = 2891621) B2891621
theorem B4565585 : Blo 1803603 4565585 := bstep (se 2 (by rfl) ⟨1712094, by rfl⟩ : syracuseStep 4565585 = 3424189) B3424189
theorem B1804883 : Blo 1803603 1804883 := bstep (se 1 (by rfl) ⟨1353662, by rfl⟩ : syracuseStep 1804883 = 2707325) B2707325
theorem B2706017 : Blo 1803603 2706017 := bstep (se 2 (by rfl) ⟨1014756, by rfl⟩ : syracuseStep 2706017 = 2029513) B2029513
theorem B1804899 : Blo 1803603 1804899 := bstep (se 1 (by rfl) ⟨1353674, by rfl⟩ : syracuseStep 1804899 = 2707349) B2707349
theorem B2706035 : Blo 1803603 2706035 := bstep (se 1 (by rfl) ⟨2029526, by rfl⟩ : syracuseStep 2706035 = 4059053) B4059053
theorem B1804915 : Blo 1803603 1804915 := bstep (se 1 (by rfl) ⟨1353686, by rfl⟩ : syracuseStep 1804915 = 2707373) B2707373
theorem B1804931 : Blo 1803603 1804931 := bstep (se 1 (by rfl) ⟨1353698, by rfl⟩ : syracuseStep 1804931 = 2707397) B2707397
theorem B2706065 : Blo 1803603 2706065 := bstep (se 2 (by rfl) ⟨1014774, by rfl⟩ : syracuseStep 2706065 = 2029549) B2029549
theorem B3426961 : Blo 1803603 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B1804947 : Blo 1803603 1804947 := bstep (se 1 (by rfl) ⟨1353710, by rfl⟩ : syracuseStep 1804947 = 2707421) B2707421
theorem B2706083 : Blo 1803603 2706083 := bstep (se 1 (by rfl) ⟨2029562, by rfl⟩ : syracuseStep 2706083 = 4059125) B4059125
theorem B1804963 : Blo 1803603 1804963 := bstep (se 1 (by rfl) ⟨1353722, by rfl⟩ : syracuseStep 1804963 = 2707445) B2707445
theorem B6851249 : Blo 1803603 6851249 := bstep (se 2 (by rfl) ⟨2569218, by rfl⟩ : syracuseStep 6851249 = 5138437) B5138437
theorem B9259697 : Blo 1803603 9259697 := bstep (se 2 (by rfl) ⟨3472386, by rfl⟩ : syracuseStep 9259697 = 6944773) B6944773
theorem B1804979 : Blo 1803603 1804979 := bstep (se 1 (by rfl) ⟨1353734, by rfl⟩ : syracuseStep 1804979 = 2707469) B2707469
theorem B2706113 : Blo 1803603 2706113 := bstep (se 2 (by rfl) ⟨1014792, by rfl⟩ : syracuseStep 2706113 = 2029585) B2029585
theorem B1804995 : Blo 1803603 1804995 := bstep (se 1 (by rfl) ⟨1353746, by rfl⟩ : syracuseStep 1804995 = 2707493) B2707493
theorem B2706131 : Blo 1803603 2706131 := bstep (se 1 (by rfl) ⟨2029598, by rfl⟩ : syracuseStep 2706131 = 4059197) B4059197
theorem B1805011 : Blo 1803603 1805011 := bstep (se 1 (by rfl) ⟨1353758, by rfl⟩ : syracuseStep 1805011 = 2707517) B2707517
theorem B4336355 : Blo 1803603 4336355 := bstep (se 1 (by rfl) ⟨3252266, by rfl⟩ : syracuseStep 4336355 = 6504533) B6504533
theorem B1805027 : Blo 1803603 1805027 := bstep (se 1 (by rfl) ⟨1353770, by rfl⟩ : syracuseStep 1805027 = 2707541) B2707541
theorem B2706161 : Blo 1803603 2706161 := bstep (se 2 (by rfl) ⟨1014810, by rfl⟩ : syracuseStep 2706161 = 2029621) B2029621
theorem B1805043 : Blo 1803603 1805043 := bstep (se 1 (by rfl) ⟨1353782, by rfl⟩ : syracuseStep 1805043 = 2707565) B2707565
theorem B2706179 : Blo 1803603 2706179 := bstep (se 1 (by rfl) ⟨2029634, by rfl⟩ : syracuseStep 2706179 = 4059269) B4059269
theorem B1805059 : Blo 1803603 1805059 := bstep (se 1 (by rfl) ⟨1353794, by rfl⟩ : syracuseStep 1805059 = 2707589) B2707589
theorem B13699853 : Blo 1803603 13699853 := bstep (se 3 (by rfl) ⟨2568722, by rfl⟩ : syracuseStep 13699853 = 5137445) B5137445
theorem B1805075 : Blo 1803603 1805075 := bstep (se 1 (by rfl) ⟨1353806, by rfl⟩ : syracuseStep 1805075 = 2707613) B2707613
theorem B2706209 : Blo 1803603 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B10275619 : Blo 1803603 10275619 := bstep (se 1 (by rfl) ⟨7706714, by rfl⟩ : syracuseStep 10275619 = 15413429) B15413429
theorem B1805091 : Blo 1803603 1805091 := bstep (se 1 (by rfl) ⟨1353818, by rfl⟩ : syracuseStep 1805091 = 2707637) B2707637
theorem B2706227 : Blo 1803603 2706227 := bstep (se 1 (by rfl) ⟨2029670, by rfl⟩ : syracuseStep 2706227 = 4059341) B4059341
theorem B1805107 : Blo 1803603 1805107 := bstep (se 1 (by rfl) ⟨1353830, by rfl⟩ : syracuseStep 1805107 = 2707661) B2707661
theorem B1805123 : Blo 1803603 1805123 := bstep (se 1 (by rfl) ⟨1353842, by rfl⟩ : syracuseStep 1805123 = 2707685) B2707685
theorem B2706257 : Blo 1803603 2706257 := bstep (se 2 (by rfl) ⟨1014846, by rfl⟩ : syracuseStep 2706257 = 2029693) B2029693
theorem B1805139 : Blo 1803603 1805139 := bstep (se 1 (by rfl) ⟨1353854, by rfl⟩ : syracuseStep 1805139 = 2707709) B2707709
theorem B2706275 : Blo 1803603 2706275 := bstep (se 1 (by rfl) ⟨2029706, by rfl⟩ : syracuseStep 2706275 = 4059413) B4059413
theorem B2640739 : Blo 1803603 2640739 := bstep (se 1 (by rfl) ⟨1980554, by rfl⟩ : syracuseStep 2640739 = 3961109) B3961109
theorem B1805155 : Blo 1803603 1805155 := bstep (se 1 (by rfl) ⟨1353866, by rfl⟩ : syracuseStep 1805155 = 2707733) B2707733
theorem B1805171 : Blo 1803603 1805171 := bstep (se 1 (by rfl) ⟨1353878, by rfl⟩ : syracuseStep 1805171 = 2707757) B2707757
theorem B2706305 : Blo 1803603 2706305 := bstep (se 2 (by rfl) ⟨1014864, by rfl⟩ : syracuseStep 2706305 = 2029729) B2029729
theorem B3853187 : Blo 1803603 3853187 := bstep (se 1 (by rfl) ⟨2889890, by rfl⟩ : syracuseStep 3853187 = 5779781) B5779781
theorem B1805187 : Blo 1803603 1805187 := bstep (se 1 (by rfl) ⟨1353890, by rfl⟩ : syracuseStep 1805187 = 2707781) B2707781
theorem B2706323 : Blo 1803603 2706323 := bstep (se 1 (by rfl) ⟨2029742, by rfl⟩ : syracuseStep 2706323 = 4059485) B4059485
theorem B1805203 : Blo 1803603 1805203 := bstep (se 1 (by rfl) ⟨1353902, by rfl⟩ : syracuseStep 1805203 = 2707805) B2707805
theorem B1805219 : Blo 1803603 1805219 := bstep (se 1 (by rfl) ⟨1353914, by rfl⟩ : syracuseStep 1805219 = 2707829) B2707829
theorem B2706353 : Blo 1803603 2706353 := bstep (se 2 (by rfl) ⟨1014882, by rfl⟩ : syracuseStep 2706353 = 2029765) B2029765
theorem B1805235 : Blo 1803603 1805235 := bstep (se 1 (by rfl) ⟨1353926, by rfl⟩ : syracuseStep 1805235 = 2707853) B2707853
theorem B2706371 : Blo 1803603 2706371 := bstep (se 1 (by rfl) ⟨2029778, by rfl⟩ : syracuseStep 2706371 = 4059557) B4059557
theorem B1805251 : Blo 1803603 1805251 := bstep (se 1 (by rfl) ⟨1353938, by rfl⟩ : syracuseStep 1805251 = 2707877) B2707877
theorem B1805267 : Blo 1803603 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B2706401 : Blo 1803603 2706401 := bstep (se 2 (by rfl) ⟨1014900, by rfl⟩ : syracuseStep 2706401 = 2029801) B2029801
theorem B9137123 : Blo 1803603 9137123 := bstep (se 1 (by rfl) ⟨6852842, by rfl⟩ : syracuseStep 9137123 = 13705685) B13705685
theorem B1805283 : Blo 1803603 1805283 := bstep (se 1 (by rfl) ⟨1353962, by rfl⟩ : syracuseStep 1805283 = 2707925) B2707925
theorem B15420401 : Blo 1803603 15420401 := bstep (se 2 (by rfl) ⟨5782650, by rfl⟩ : syracuseStep 15420401 = 11565301) B11565301
theorem B2706419 : Blo 1803603 2706419 := bstep (se 1 (by rfl) ⟨2029814, by rfl⟩ : syracuseStep 2706419 = 4059629) B4059629
theorem B1805299 : Blo 1803603 1805299 := bstep (se 1 (by rfl) ⟨1353974, by rfl⟩ : syracuseStep 1805299 = 2707949) B2707949
theorem B1805315 : Blo 1803603 1805315 := bstep (se 1 (by rfl) ⟨1353986, by rfl⟩ : syracuseStep 1805315 = 2707973) B2707973
theorem B6089741 : Blo 1803603 6089741 := bstep (se 3 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 6089741 = 2283653) B2283653
theorem B7711757 : Blo 1803603 7711757 := bstep (se 3 (by rfl) ⟨1445954, by rfl⟩ : syracuseStep 7711757 = 2891909) B2891909
theorem B5778449 : Blo 1803603 5778449 := bstep (se 2 (by rfl) ⟨2166918, by rfl⟩ : syracuseStep 5778449 = 4333837) B4333837
theorem B2706449 : Blo 1803603 2706449 := bstep (se 2 (by rfl) ⟨1014918, by rfl⟩ : syracuseStep 2706449 = 2029837) B2029837
theorem B4877329 : Blo 1803603 4877329 := bstep (se 2 (by rfl) ⟨1828998, by rfl⟩ : syracuseStep 4877329 = 3657997) B3657997
theorem B1805331 : Blo 1803603 1805331 := bstep (se 1 (by rfl) ⟨1353998, by rfl⟩ : syracuseStep 1805331 = 2707997) B2707997
theorem B2706467 : Blo 1803603 2706467 := bstep (se 1 (by rfl) ⟨2029850, by rfl⟩ : syracuseStep 2706467 = 4059701) B4059701
theorem B1805347 : Blo 1803603 1805347 := bstep (se 1 (by rfl) ⟨1354010, by rfl⟩ : syracuseStep 1805347 = 2708021) B2708021
theorem B3427363 : Blo 1803603 3427363 := bstep (se 1 (by rfl) ⟨2570522, by rfl⟩ : syracuseStep 3427363 = 5141045) B5141045
theorem B1805363 : Blo 1803603 1805363 := bstep (se 1 (by rfl) ⟨1354022, by rfl⟩ : syracuseStep 1805363 = 2708045) B2708045
theorem B2706497 : Blo 1803603 2706497 := bstep (se 2 (by rfl) ⟨1014936, by rfl⟩ : syracuseStep 2706497 = 2029873) B2029873
theorem B5778499 : Blo 1803603 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B6089795 : Blo 1803603 6089795 := bstep (se 1 (by rfl) ⟨4567346, by rfl⟩ : syracuseStep 6089795 = 9134693) B9134693
theorem B1805379 : Blo 1803603 1805379 := bstep (se 1 (by rfl) ⟨1354034, by rfl⟩ : syracuseStep 1805379 = 2708069) B2708069
theorem B3427409 : Blo 1803603 3427409 := bstep (se 2 (by rfl) ⟨1285278, by rfl⟩ : syracuseStep 3427409 = 2570557) B2570557
theorem B2706515 : Blo 1803603 2706515 := bstep (se 1 (by rfl) ⟨2029886, by rfl⟩ : syracuseStep 2706515 = 4059773) B4059773
theorem B1805395 : Blo 1803603 1805395 := bstep (se 1 (by rfl) ⟨1354046, by rfl⟩ : syracuseStep 1805395 = 2708093) B2708093
theorem B1805411 : Blo 1803603 1805411 := bstep (se 1 (by rfl) ⟨1354058, by rfl⟩ : syracuseStep 1805411 = 2708117) B2708117
theorem B4058225 : Blo 1803603 4058225 := bstep (se 2 (by rfl) ⟨1521834, by rfl⟩ : syracuseStep 4058225 = 3043669) B3043669
theorem B2706545 : Blo 1803603 2706545 := bstep (se 2 (by rfl) ⟨1014954, by rfl⟩ : syracuseStep 2706545 = 2029909) B2029909
theorem B4877425 : Blo 1803603 4877425 := bstep (se 2 (by rfl) ⟨1829034, by rfl⟩ : syracuseStep 4877425 = 3658069) B3658069
theorem B1805427 : Blo 1803603 1805427 := bstep (se 1 (by rfl) ⟨1354070, by rfl⟩ : syracuseStep 1805427 = 2708141) B2708141
theorem B4058243 : Blo 1803603 4058243 := bstep (se 1 (by rfl) ⟨3043682, by rfl⟩ : syracuseStep 4058243 = 6087365) B6087365
theorem B2706563 : Blo 1803603 2706563 := bstep (se 1 (by rfl) ⟨2029922, by rfl⟩ : syracuseStep 2706563 = 4059845) B4059845
theorem B5139587 : Blo 1803603 5139587 := bstep (se 1 (by rfl) ⟨3854690, by rfl⟩ : syracuseStep 5139587 = 7709381) B7709381
theorem B1805443 : Blo 1803603 1805443 := bstep (se 1 (by rfl) ⟨1354082, by rfl⟩ : syracuseStep 1805443 = 2708165) B2708165
theorem B1805459 : Blo 1803603 1805459 := bstep (se 1 (by rfl) ⟨1354094, by rfl⟩ : syracuseStep 1805459 = 2708189) B2708189
theorem B2706593 : Blo 1803603 2706593 := bstep (se 2 (by rfl) ⟨1014972, by rfl⟩ : syracuseStep 2706593 = 2029945) B2029945
theorem B1805475 : Blo 1803603 1805475 := bstep (se 1 (by rfl) ⟨1354106, by rfl⟩ : syracuseStep 1805475 = 2708213) B2708213
theorem B2706611 : Blo 1803603 2706611 := bstep (se 1 (by rfl) ⟨2029958, by rfl⟩ : syracuseStep 2706611 = 4059917) B4059917
theorem B1805491 : Blo 1803603 1805491 := bstep (se 1 (by rfl) ⟨1354118, by rfl⟩ : syracuseStep 1805491 = 2708237) B2708237
theorem B1805507 : Blo 1803603 1805507 := bstep (se 1 (by rfl) ⟨1354130, by rfl⟩ : syracuseStep 1805507 = 2708261) B2708261
theorem B2706641 : Blo 1803603 2706641 := bstep (se 2 (by rfl) ⟨1014990, by rfl⟩ : syracuseStep 2706641 = 2029981) B2029981
theorem B1805523 : Blo 1803603 1805523 := bstep (se 1 (by rfl) ⟨1354142, by rfl⟩ : syracuseStep 1805523 = 2708285) B2708285
theorem B2706659 : Blo 1803603 2706659 := bstep (se 1 (by rfl) ⟨2029994, by rfl⟩ : syracuseStep 2706659 = 4059989) B4059989
theorem B1805539 : Blo 1803603 1805539 := bstep (se 1 (by rfl) ⟨1354154, by rfl⟩ : syracuseStep 1805539 = 2708309) B2708309
theorem B1805555 : Blo 1803603 1805555 := bstep (se 1 (by rfl) ⟨1354166, by rfl⟩ : syracuseStep 1805555 = 2708333) B2708333
theorem B2706689 : Blo 1803603 2706689 := bstep (se 2 (by rfl) ⟨1015008, by rfl⟩ : syracuseStep 2706689 = 2030017) B2030017
theorem B1805571 : Blo 1803603 1805571 := bstep (se 1 (by rfl) ⟨1354178, by rfl⟩ : syracuseStep 1805571 = 2708357) B2708357
theorem B2706707 : Blo 1803603 2706707 := bstep (se 1 (by rfl) ⟨2030030, by rfl⟩ : syracuseStep 2706707 = 4060061) B4060061
theorem B1805587 : Blo 1803603 1805587 := bstep (se 1 (by rfl) ⟨1354190, by rfl⟩ : syracuseStep 1805587 = 2708381) B2708381
theorem B1805603 : Blo 1803603 1805603 := bstep (se 1 (by rfl) ⟨1354202, by rfl⟩ : syracuseStep 1805603 = 2708405) B2708405
theorem B10276145 : Blo 1803603 10276145 := bstep (se 2 (by rfl) ⟨3853554, by rfl⟩ : syracuseStep 10276145 = 7707109) B7707109
theorem B2706737 : Blo 1803603 2706737 := bstep (se 2 (by rfl) ⟨1015026, by rfl⟩ : syracuseStep 2706737 = 2030053) B2030053
theorem B2706755 : Blo 1803603 2706755 := bstep (se 1 (by rfl) ⟨2030066, by rfl⟩ : syracuseStep 2706755 = 4060133) B4060133
theorem B3853649 : Blo 1803603 3853649 := bstep (se 2 (by rfl) ⟨1445118, by rfl⟩ : syracuseStep 3853649 = 2890237) B2890237
theorem B6090065 : Blo 1803603 6090065 := bstep (se 2 (by rfl) ⟨2283774, by rfl⟩ : syracuseStep 6090065 = 4567549) B4567549
theorem B2706785 : Blo 1803603 2706785 := bstep (se 2 (by rfl) ⟨1015044, by rfl⟩ : syracuseStep 2706785 = 2030089) B2030089
theorem B3427697 : Blo 1803603 3427697 := bstep (se 2 (by rfl) ⟨1285386, by rfl⟩ : syracuseStep 3427697 = 2570773) B2570773
theorem B2706803 : Blo 1803603 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B4058513 : Blo 1803603 4058513 := bstep (se 2 (by rfl) ⟨1521942, by rfl⟩ : syracuseStep 4058513 = 3043885) B3043885
theorem B2706833 : Blo 1803603 2706833 := bstep (se 2 (by rfl) ⟨1015062, by rfl⟩ : syracuseStep 2706833 = 2030125) B2030125
theorem B4058531 : Blo 1803603 4058531 := bstep (se 1 (by rfl) ⟨3043898, by rfl⟩ : syracuseStep 4058531 = 6087797) B6087797
theorem B2706851 : Blo 1803603 2706851 := bstep (se 1 (by rfl) ⟨2030138, by rfl⟩ : syracuseStep 2706851 = 4060277) B4060277
theorem B2706881 : Blo 1803603 2706881 := bstep (se 2 (by rfl) ⟨1015080, by rfl⟩ : syracuseStep 2706881 = 2030161) B2030161
theorem B2706899 : Blo 1803603 2706899 := bstep (se 1 (by rfl) ⟨2030174, by rfl⟩ : syracuseStep 2706899 = 4060349) B4060349
theorem B2706929 : Blo 1803603 2706929 := bstep (se 2 (by rfl) ⟨1015098, by rfl⟩ : syracuseStep 2706929 = 2030197) B2030197
theorem B2706947 : Blo 1803603 2706947 := bstep (se 1 (by rfl) ⟨2030210, by rfl⟩ : syracuseStep 2706947 = 4060421) B4060421
theorem B2706977 : Blo 1803603 2706977 := bstep (se 2 (by rfl) ⟨1015116, by rfl⟩ : syracuseStep 2706977 = 2030233) B2030233
theorem B4566577 : Blo 1803603 4566577 := bstep (se 2 (by rfl) ⟨1712466, by rfl⟩ : syracuseStep 4566577 = 3424933) B3424933
theorem B4337201 : Blo 1803603 4337201 := bstep (se 2 (by rfl) ⟨1626450, by rfl⟩ : syracuseStep 4337201 = 3252901) B3252901
theorem B2706995 : Blo 1803603 2706995 := bstep (se 1 (by rfl) ⟨2030246, by rfl⟩ : syracuseStep 2706995 = 4060493) B4060493
theorem B2707025 : Blo 1803603 2707025 := bstep (se 2 (by rfl) ⟨1015134, by rfl⟩ : syracuseStep 2707025 = 2030269) B2030269
theorem B2707043 : Blo 1803603 2707043 := bstep (se 1 (by rfl) ⟨2030282, by rfl⟩ : syracuseStep 2707043 = 4060565) B4060565
theorem B2707073 : Blo 1803603 2707073 := bstep (se 2 (by rfl) ⟨1015152, by rfl⟩ : syracuseStep 2707073 = 2030305) B2030305
theorem B4337297 : Blo 1803603 4337297 := bstep (se 2 (by rfl) ⟨1626486, by rfl⟩ : syracuseStep 4337297 = 3252973) B3252973
theorem B2707091 : Blo 1803603 2707091 := bstep (se 1 (by rfl) ⟨2030318, by rfl⟩ : syracuseStep 2707091 = 4060637) B4060637
theorem B4116131 : Blo 1803603 4116131 := bstep (se 1 (by rfl) ⟨3087098, by rfl⟩ : syracuseStep 4116131 = 6174197) B6174197
theorem B4058801 : Blo 1803603 4058801 := bstep (se 2 (by rfl) ⟨1522050, by rfl⟩ : syracuseStep 4058801 = 3044101) B3044101
theorem B2707121 : Blo 1803603 2707121 := bstep (se 2 (by rfl) ⟨1015170, by rfl⟩ : syracuseStep 2707121 = 2030341) B2030341
theorem B4058819 : Blo 1803603 4058819 := bstep (se 1 (by rfl) ⟨3044114, by rfl⟩ : syracuseStep 4058819 = 6088229) B6088229
theorem B2707139 : Blo 1803603 2707139 := bstep (se 1 (by rfl) ⟨2030354, by rfl⟩ : syracuseStep 2707139 = 4060709) B4060709
theorem B8793805 : Blo 1803603 8793805 := bstep (se 3 (by rfl) ⟨1648838, by rfl⟩ : syracuseStep 8793805 = 3297677) B3297677
theorem B2707169 : Blo 1803603 2707169 := bstep (se 2 (by rfl) ⟨1015188, by rfl⟩ : syracuseStep 2707169 = 2030377) B2030377
theorem B2707187 : Blo 1803603 2707187 := bstep (se 1 (by rfl) ⟨2030390, by rfl⟩ : syracuseStep 2707187 = 4060781) B4060781
theorem B9137933 : Blo 1803603 9137933 := bstep (se 3 (by rfl) ⟨1713362, by rfl⟩ : syracuseStep 9137933 = 3426725) B3426725
theorem B2707217 : Blo 1803603 2707217 := bstep (se 2 (by rfl) ⟨1015206, by rfl⟩ : syracuseStep 2707217 = 2030413) B2030413
theorem B2707235 : Blo 1803603 2707235 := bstep (se 1 (by rfl) ⟨2030426, by rfl⟩ : syracuseStep 2707235 = 4060853) B4060853
theorem B4566851 : Blo 1803603 4566851 := bstep (se 1 (by rfl) ⟨3425138, by rfl⟩ : syracuseStep 4566851 = 6850277) B6850277
theorem B2314051 : Blo 1803603 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B2707265 : Blo 1803603 2707265 := bstep (se 2 (by rfl) ⟨1015224, by rfl⟩ : syracuseStep 2707265 = 2030449) B2030449
theorem B2707283 : Blo 1803603 2707283 := bstep (se 1 (by rfl) ⟨2030462, by rfl⟩ : syracuseStep 2707283 = 4060925) B4060925
theorem B6090605 : Blo 1803603 6090605 := bstep (se 3 (by rfl) ⟨1141988, by rfl⟩ : syracuseStep 6090605 = 2283977) B2283977
theorem B2707313 : Blo 1803603 2707313 := bstep (se 2 (by rfl) ⟨1015242, by rfl⟩ : syracuseStep 2707313 = 2030485) B2030485
theorem B2707331 : Blo 1803603 2707331 := bstep (se 1 (by rfl) ⟨2030498, by rfl⟩ : syracuseStep 2707331 = 4060997) B4060997
theorem B5779345 : Blo 1803603 5779345 := bstep (se 2 (by rfl) ⟨2167254, by rfl⟩ : syracuseStep 5779345 = 4334509) B4334509
theorem B2707361 : Blo 1803603 2707361 := bstep (se 2 (by rfl) ⟨1015260, by rfl⟩ : syracuseStep 2707361 = 2030521) B2030521
theorem B6090659 : Blo 1803603 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B2707379 : Blo 1803603 2707379 := bstep (se 1 (by rfl) ⟨2030534, by rfl⟩ : syracuseStep 2707379 = 4061069) B4061069
theorem B12349381 : Blo 1803603 12349381 := bstep (se 4 (by rfl) ⟨1157754, by rfl⟩ : syracuseStep 12349381 = 2315509) B2315509
theorem B4059089 : Blo 1803603 4059089 := bstep (se 2 (by rfl) ⟨1522158, by rfl⟩ : syracuseStep 4059089 = 3044317) B3044317
theorem B2707409 : Blo 1803603 2707409 := bstep (se 2 (by rfl) ⟨1015278, by rfl⟩ : syracuseStep 2707409 = 2030557) B2030557
theorem B4059107 : Blo 1803603 4059107 := bstep (se 1 (by rfl) ⟨3044330, by rfl⟩ : syracuseStep 4059107 = 6088661) B6088661
theorem B2707427 : Blo 1803603 2707427 := bstep (se 1 (by rfl) ⟨2030570, by rfl⟩ : syracuseStep 2707427 = 4061141) B4061141
theorem B2707457 : Blo 1803603 2707457 := bstep (se 2 (by rfl) ⟨1015296, by rfl⟩ : syracuseStep 2707457 = 2030593) B2030593
theorem B4567043 : Blo 1803603 4567043 := bstep (se 1 (by rfl) ⟨3425282, by rfl⟩ : syracuseStep 4567043 = 6850565) B6850565
theorem B2707475 : Blo 1803603 2707475 := bstep (se 1 (by rfl) ⟨2030606, by rfl⟩ : syracuseStep 2707475 = 4061213) B4061213
theorem B2707505 : Blo 1803603 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B2707523 : Blo 1803603 2707523 := bstep (se 1 (by rfl) ⟨2030642, by rfl⟩ : syracuseStep 2707523 = 4061285) B4061285
theorem B2707553 : Blo 1803603 2707553 := bstep (se 2 (by rfl) ⟨1015332, by rfl⟩ : syracuseStep 2707553 = 2030665) B2030665
theorem B6852707 : Blo 1803603 6852707 := bstep (se 1 (by rfl) ⟨5139530, by rfl⟩ : syracuseStep 6852707 = 10279061) B10279061
theorem B6852721 : Blo 1803603 6852721 := bstep (se 2 (by rfl) ⟨2569770, by rfl⟩ : syracuseStep 6852721 = 5139541) B5139541
theorem B2707571 : Blo 1803603 2707571 := bstep (se 1 (by rfl) ⟨2030678, by rfl⟩ : syracuseStep 2707571 = 4061357) B4061357
theorem B2707601 : Blo 1803603 2707601 := bstep (se 2 (by rfl) ⟨1015350, by rfl⟩ : syracuseStep 2707601 = 2030701) B2030701
theorem B2707619 : Blo 1803603 2707619 := bstep (se 1 (by rfl) ⟨2030714, by rfl⟩ : syracuseStep 2707619 = 4061429) B4061429
theorem B6090929 : Blo 1803603 6090929 := bstep (se 2 (by rfl) ⟨2284098, by rfl⟩ : syracuseStep 6090929 = 4568197) B4568197
theorem B2707649 : Blo 1803603 2707649 := bstep (se 2 (by rfl) ⟨1015368, by rfl⟩ : syracuseStep 2707649 = 2030737) B2030737
theorem B9752773 : Blo 1803603 9752773 := bstep (se 4 (by rfl) ⟨914322, by rfl⟩ : syracuseStep 9752773 = 1828645) B1828645
theorem B2707667 : Blo 1803603 2707667 := bstep (se 1 (by rfl) ⟨2030750, by rfl⟩ : syracuseStep 2707667 = 4061501) B4061501
theorem B4059377 : Blo 1803603 4059377 := bstep (se 2 (by rfl) ⟨1522266, by rfl⟩ : syracuseStep 4059377 = 3044533) B3044533
theorem B2707697 : Blo 1803603 2707697 := bstep (se 2 (by rfl) ⟨1015386, by rfl⟩ : syracuseStep 2707697 = 2030773) B2030773
theorem B4059395 : Blo 1803603 4059395 := bstep (se 1 (by rfl) ⟨3044546, by rfl⟩ : syracuseStep 4059395 = 6089093) B6089093
theorem B2707715 : Blo 1803603 2707715 := bstep (se 1 (by rfl) ⟨2030786, by rfl⟩ : syracuseStep 2707715 = 4061573) B4061573
theorem B2707745 : Blo 1803603 2707745 := bstep (se 2 (by rfl) ⟨1015404, by rfl⟩ : syracuseStep 2707745 = 2030809) B2030809
theorem B2707763 : Blo 1803603 2707763 := bstep (se 1 (by rfl) ⟨2030822, by rfl⟩ : syracuseStep 2707763 = 4061645) B4061645
theorem B3043649 : Blo 1803603 3043649 := bstep (se 2 (by rfl) ⟨1141368, by rfl⟩ : syracuseStep 3043649 = 2282737) B2282737
theorem B2707793 : Blo 1803603 2707793 := bstep (se 2 (by rfl) ⟨1015422, by rfl⟩ : syracuseStep 2707793 = 2030845) B2030845
theorem B5140817 : Blo 1803603 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B2707811 : Blo 1803603 2707811 := bstep (se 1 (by rfl) ⟨2030858, by rfl⟩ : syracuseStep 2707811 = 4061717) B4061717
theorem B2707841 : Blo 1803603 2707841 := bstep (se 2 (by rfl) ⟨1015440, by rfl⟩ : syracuseStep 2707841 = 2030881) B2030881
theorem B2707859 : Blo 1803603 2707859 := bstep (se 1 (by rfl) ⟨2030894, by rfl⟩ : syracuseStep 2707859 = 4061789) B4061789
theorem B2707889 : Blo 1803603 2707889 := bstep (se 2 (by rfl) ⟨1015458, by rfl⟩ : syracuseStep 2707889 = 2030917) B2030917
theorem B3043777 : Blo 1803603 3043777 := bstep (se 2 (by rfl) ⟨1141416, by rfl⟩ : syracuseStep 3043777 = 2282833) B2282833
theorem B2707907 : Blo 1803603 2707907 := bstep (se 1 (by rfl) ⟨2030930, by rfl⟩ : syracuseStep 2707907 = 4061861) B4061861
theorem B2707937 : Blo 1803603 2707937 := bstep (se 2 (by rfl) ⟨1015476, by rfl⟩ : syracuseStep 2707937 = 2030953) B2030953
theorem B3043811 : Blo 1803603 3043811 := bstep (se 1 (by rfl) ⟨2282858, by rfl⟩ : syracuseStep 3043811 = 4565717) B4565717
theorem B2707955 : Blo 1803603 2707955 := bstep (se 1 (by rfl) ⟨2030966, by rfl⟩ : syracuseStep 2707955 = 4061933) B4061933
theorem B4059665 : Blo 1803603 4059665 := bstep (se 2 (by rfl) ⟨1522374, by rfl⟩ : syracuseStep 4059665 = 3044749) B3044749
theorem B2707985 : Blo 1803603 2707985 := bstep (se 2 (by rfl) ⟨1015494, by rfl⟩ : syracuseStep 2707985 = 2030989) B2030989
theorem B3297809 : Blo 1803603 3297809 := bstep (se 2 (by rfl) ⟨1236678, by rfl⟩ : syracuseStep 3297809 = 2473357) B2473357
theorem B4059683 : Blo 1803603 4059683 := bstep (se 1 (by rfl) ⟨3044762, by rfl⟩ : syracuseStep 4059683 = 6089525) B6089525
theorem B2708003 : Blo 1803603 2708003 := bstep (se 1 (by rfl) ⟨2031002, by rfl⟩ : syracuseStep 2708003 = 4062005) B4062005
theorem B2708033 : Blo 1803603 2708033 := bstep (se 2 (by rfl) ⟨1015512, by rfl⟩ : syracuseStep 2708033 = 2031025) B2031025
theorem B2708051 : Blo 1803603 2708051 := bstep (se 1 (by rfl) ⟨2031038, by rfl⟩ : syracuseStep 2708051 = 4062077) B4062077
theorem B3043939 : Blo 1803603 3043939 := bstep (se 1 (by rfl) ⟨2282954, by rfl⟩ : syracuseStep 3043939 = 4565909) B4565909
theorem B3854947 : Blo 1803603 3854947 := bstep (se 1 (by rfl) ⟨2891210, by rfl⟩ : syracuseStep 3854947 = 5782421) B5782421
theorem B2708081 : Blo 1803603 2708081 := bstep (se 2 (by rfl) ⟨1015530, by rfl⟩ : syracuseStep 2708081 = 2031061) B2031061
theorem B2708099 : Blo 1803603 2708099 := bstep (se 1 (by rfl) ⟨2031074, by rfl⟩ : syracuseStep 2708099 = 4062149) B4062149
theorem B7811725 : Blo 1803603 7811725 := bstep (se 3 (by rfl) ⟨1464698, by rfl⟩ : syracuseStep 7811725 = 2929397) B2929397
theorem B11563661 : Blo 1803603 11563661 := bstep (se 3 (by rfl) ⟨2168186, by rfl⟩ : syracuseStep 11563661 = 4336373) B4336373
theorem B21959309 : Blo 1803603 21959309 := bstep (se 3 (by rfl) ⟨4117370, by rfl⟩ : syracuseStep 21959309 = 8234741) B8234741
theorem B1954451 : Blo 1803603 1954451 := bstep (se 1 (by rfl) ⟨1465838, by rfl⟩ : syracuseStep 1954451 = 2931677) B2931677
theorem B2708129 : Blo 1803603 2708129 := bstep (se 2 (by rfl) ⟨1015548, by rfl⟩ : syracuseStep 2708129 = 2031097) B2031097
theorem B23130805 : Blo 1803603 23130805 := bstep (se 5 (by rfl) ⟨1084256, by rfl⟩ : syracuseStep 23130805 = 2168513) B2168513
theorem B2708147 : Blo 1803603 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B6091469 : Blo 1803603 6091469 := bstep (se 3 (by rfl) ⟨1142150, by rfl⟩ : syracuseStep 6091469 = 2284301) B2284301
theorem B2708177 : Blo 1803603 2708177 := bstep (se 2 (by rfl) ⟨1015566, by rfl⟩ : syracuseStep 2708177 = 2031133) B2031133
theorem B10277603 : Blo 1803603 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B2708195 : Blo 1803603 2708195 := bstep (se 1 (by rfl) ⟨2031146, by rfl⟩ : syracuseStep 2708195 = 4062293) B4062293
theorem B3044081 : Blo 1803603 3044081 := bstep (se 2 (by rfl) ⟨1141530, by rfl⟩ : syracuseStep 3044081 = 2283061) B2283061
theorem B6091523 : Blo 1803603 6091523 := bstep (se 1 (by rfl) ⟨4568642, by rfl⟩ : syracuseStep 6091523 = 9137285) B9137285
theorem B2708225 : Blo 1803603 2708225 := bstep (se 2 (by rfl) ⟨1015584, by rfl⟩ : syracuseStep 2708225 = 2031169) B2031169
theorem B2708243 : Blo 1803603 2708243 := bstep (se 1 (by rfl) ⟨2031182, by rfl⟩ : syracuseStep 2708243 = 4062365) B4062365
theorem B4059953 : Blo 1803603 4059953 := bstep (se 2 (by rfl) ⟨1522482, by rfl⟩ : syracuseStep 4059953 = 3044965) B3044965
theorem B2708273 : Blo 1803603 2708273 := bstep (se 2 (by rfl) ⟨1015602, by rfl⟩ : syracuseStep 2708273 = 2031205) B2031205
theorem B4059971 : Blo 1803603 4059971 := bstep (se 1 (by rfl) ⟨3044978, by rfl⟩ : syracuseStep 4059971 = 6089957) B6089957
theorem B2708291 : Blo 1803603 2708291 := bstep (se 1 (by rfl) ⟨2031218, by rfl⟩ : syracuseStep 2708291 = 4062437) B4062437
theorem B2708321 : Blo 1803603 2708321 := bstep (se 2 (by rfl) ⟨1015620, by rfl⟩ : syracuseStep 2708321 = 2031241) B2031241
theorem B3855203 : Blo 1803603 3855203 := bstep (se 1 (by rfl) ⟨2891402, by rfl⟩ : syracuseStep 3855203 = 5782805) B5782805
theorem B3044209 : Blo 1803603 3044209 := bstep (se 2 (by rfl) ⟨1141578, by rfl⟩ : syracuseStep 3044209 = 2283157) B2283157
theorem B37106545 : Blo 1803603 37106545 := bstep (se 2 (by rfl) ⟨13914954, by rfl⟩ : syracuseStep 37106545 = 27829909) B27829909
theorem B2708339 : Blo 1803603 2708339 := bstep (se 1 (by rfl) ⟨2031254, by rfl⟩ : syracuseStep 2708339 = 4062509) B4062509
theorem B2708369 : Blo 1803603 2708369 := bstep (se 2 (by rfl) ⟨1015638, by rfl⟩ : syracuseStep 2708369 = 2031277) B2031277
theorem B3044243 : Blo 1803603 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B5485475 : Blo 1803603 5485475 := bstep (se 1 (by rfl) ⟨4114106, by rfl⟩ : syracuseStep 5485475 = 8228213) B8228213
theorem B2708387 : Blo 1803603 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B10294193 : Blo 1803603 10294193 := bstep (se 2 (by rfl) ⟨3860322, by rfl⟩ : syracuseStep 10294193 = 7720645) B7720645
theorem B4567985 : Blo 1803603 4567985 := bstep (se 2 (by rfl) ⟨1712994, by rfl⟩ : syracuseStep 4567985 = 3425989) B3425989
theorem B4568035 : Blo 1803603 4568035 := bstep (se 1 (by rfl) ⟨3426026, by rfl⟩ : syracuseStep 4568035 = 6852053) B6852053
theorem B6173677 : Blo 1803603 6173677 := bstep (se 3 (by rfl) ⟨1157564, by rfl⟩ : syracuseStep 6173677 = 2315129) B2315129
theorem B16471025 : Blo 1803603 16471025 := bstep (se 2 (by rfl) ⟨6176634, by rfl⟩ : syracuseStep 16471025 = 12353269) B12353269
theorem B6091793 : Blo 1803603 6091793 := bstep (se 2 (by rfl) ⟨2284422, by rfl⟩ : syracuseStep 6091793 = 4568845) B4568845
theorem B3044371 : Blo 1803603 3044371 := bstep (se 1 (by rfl) ⟨2283278, by rfl⟩ : syracuseStep 3044371 = 4566557) B4566557
theorem B18781253 : Blo 1803603 18781253 := bstep (se 4 (by rfl) ⟨1760742, by rfl⟩ : syracuseStep 18781253 = 3521485) B3521485
theorem B4060241 : Blo 1803603 4060241 := bstep (se 2 (by rfl) ⟨1522590, by rfl⟩ : syracuseStep 4060241 = 3045181) B3045181
theorem B2569315 : Blo 1803603 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B4060259 : Blo 1803603 4060259 := bstep (se 1 (by rfl) ⟨3045194, by rfl⟩ : syracuseStep 4060259 = 6090389) B6090389
theorem B4568177 : Blo 1803603 4568177 := bstep (se 2 (by rfl) ⟨1713066, by rfl⟩ : syracuseStep 4568177 = 3426133) B3426133
theorem B3044513 : Blo 1803603 3044513 := bstep (se 2 (by rfl) ⟨1141692, by rfl⟩ : syracuseStep 3044513 = 2283385) B2283385
theorem B3044641 : Blo 1803603 3044641 := bstep (se 2 (by rfl) ⟨1141740, by rfl⟩ : syracuseStep 3044641 = 2283481) B2283481
theorem B3044675 : Blo 1803603 3044675 := bstep (se 1 (by rfl) ⟨2283506, by rfl⟩ : syracuseStep 3044675 = 4567013) B4567013
theorem B3659107 : Blo 1803603 3659107 := bstep (se 1 (by rfl) ⟨2744330, by rfl⟩ : syracuseStep 3659107 = 5488661) B5488661
theorem B4060529 : Blo 1803603 4060529 := bstep (se 2 (by rfl) ⟨1522698, by rfl⟩ : syracuseStep 4060529 = 3045397) B3045397
theorem B4060547 : Blo 1803603 4060547 := bstep (se 1 (by rfl) ⟨3045410, by rfl⟩ : syracuseStep 4060547 = 6090821) B6090821
theorem B11556229 : Blo 1803603 11556229 := bstep (se 4 (by rfl) ⟨1083396, by rfl⟩ : syracuseStep 11556229 = 2166793) B2166793
theorem B2282899 : Blo 1803603 2282899 := bstep (se 1 (by rfl) ⟨1712174, by rfl⟩ : syracuseStep 2282899 = 3424349) B3424349
theorem B5780909 : Blo 1803603 5780909 := bstep (se 3 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 5780909 = 2167841) B2167841
theorem B3044803 : Blo 1803603 3044803 := bstep (se 1 (by rfl) ⟨2283602, by rfl⟩ : syracuseStep 3044803 = 4567205) B4567205
theorem B2282995 : Blo 1803603 2282995 := bstep (se 1 (by rfl) ⟨1712246, by rfl⟩ : syracuseStep 2282995 = 3424493) B3424493
theorem B10556963 : Blo 1803603 10556963 := bstep (se 1 (by rfl) ⟨7917722, by rfl⟩ : syracuseStep 10556963 = 15835445) B15835445
theorem B6854179 : Blo 1803603 6854179 := bstep (se 1 (by rfl) ⟨5140634, by rfl⟩ : syracuseStep 6854179 = 10281269) B10281269
theorem B6092333 : Blo 1803603 6092333 := bstep (se 3 (by rfl) ⟨1142312, by rfl⟩ : syracuseStep 6092333 = 2284625) B2284625
theorem B6346289 : Blo 1803603 6346289 := bstep (se 2 (by rfl) ⟨2379858, by rfl⟩ : syracuseStep 6346289 = 4759717) B4759717
theorem B2315827 : Blo 1803603 2315827 := bstep (se 1 (by rfl) ⟨1736870, by rfl⟩ : syracuseStep 2315827 = 3473741) B3473741
theorem B3044945 : Blo 1803603 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B6092387 : Blo 1803603 6092387 := bstep (se 1 (by rfl) ⟨4569290, by rfl⟩ : syracuseStep 6092387 = 9138581) B9138581
theorem B13702769 : Blo 1803603 13702769 := bstep (se 2 (by rfl) ⟨5138538, by rfl⟩ : syracuseStep 13702769 = 10277077) B10277077
theorem B2029171 : Blo 1803603 2029171 := bstep (se 1 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 2029171 = 3043757) B3043757
theorem B4060817 : Blo 1803603 4060817 := bstep (se 2 (by rfl) ⟨1522806, by rfl⟩ : syracuseStep 4060817 = 3045613) B3045613
theorem B4060835 : Blo 1803603 4060835 := bstep (se 1 (by rfl) ⟨3045626, by rfl⟩ : syracuseStep 4060835 = 6091253) B6091253
theorem B30832325 : Blo 1803603 30832325 := bstep (se 4 (by rfl) ⟨2890530, by rfl⟩ : syracuseStep 30832325 = 5781061) B5781061
theorem B3045073 : Blo 1803603 3045073 := bstep (se 2 (by rfl) ⟨1141902, by rfl⟩ : syracuseStep 3045073 = 2283805) B2283805
theorem B19519217 : Blo 1803603 19519217 := bstep (se 2 (by rfl) ⟨7319706, by rfl⟩ : syracuseStep 19519217 = 14639413) B14639413
theorem B3045107 : Blo 1803603 3045107 := bstep (se 1 (by rfl) ⟨2283830, by rfl⟩ : syracuseStep 3045107 = 4567661) B4567661
theorem B13014769 : Blo 1803603 13014769 := bstep (se 2 (by rfl) ⟨4880538, by rfl⟩ : syracuseStep 13014769 = 9761077) B9761077
theorem B2029315 : Blo 1803603 2029315 := bstep (se 1 (by rfl) ⟨1521986, by rfl⟩ : syracuseStep 2029315 = 3043973) B3043973
theorem B6944525 : Blo 1803603 6944525 := bstep (se 3 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 6944525 = 2604197) B2604197
theorem B3856177 : Blo 1803603 3856177 := bstep (se 2 (by rfl) ⟨1446066, by rfl⟩ : syracuseStep 3856177 = 2892133) B2892133
theorem B5486449 : Blo 1803603 5486449 := bstep (se 2 (by rfl) ⟨2057418, by rfl⟩ : syracuseStep 5486449 = 4114837) B4114837
theorem B6592369 : Blo 1803603 6592369 := bstep (se 2 (by rfl) ⟨2472138, by rfl⟩ : syracuseStep 6592369 = 4944277) B4944277
theorem B3045235 : Blo 1803603 3045235 := bstep (se 1 (by rfl) ⟨2283926, by rfl⟩ : syracuseStep 3045235 = 4567853) B4567853
theorem B6092657 : Blo 1803603 6092657 := bstep (se 2 (by rfl) ⟨2284746, by rfl⟩ : syracuseStep 6092657 = 4569493) B4569493
theorem B2029459 : Blo 1803603 2029459 := bstep (se 1 (by rfl) ⟨1522094, by rfl⟩ : syracuseStep 2029459 = 3044189) B3044189
theorem B9131939 : Blo 1803603 9131939 := bstep (se 1 (by rfl) ⟨6848954, by rfl⟩ : syracuseStep 9131939 = 13697909) B13697909
theorem B4061105 : Blo 1803603 4061105 := bstep (se 2 (by rfl) ⟨1522914, by rfl⟩ : syracuseStep 4061105 = 3045829) B3045829
theorem B4061123 : Blo 1803603 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B2283491 : Blo 1803603 2283491 := bstep (se 1 (by rfl) ⟨1712618, by rfl⟩ : syracuseStep 2283491 = 3425237) B3425237
theorem B3045377 : Blo 1803603 3045377 := bstep (se 2 (by rfl) ⟨1142016, by rfl⟩ : syracuseStep 3045377 = 2284033) B2284033
theorem B20846605 : Blo 1803603 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B2029603 : Blo 1803603 2029603 := bstep (se 1 (by rfl) ⟨1522202, by rfl⟩ : syracuseStep 2029603 = 3044405) B3044405
theorem B4569169 : Blo 1803603 4569169 := bstep (se 2 (by rfl) ⟨1713438, by rfl⟩ : syracuseStep 4569169 = 3426877) B3426877
theorem B1980499 : Blo 1803603 1980499 := bstep (se 1 (by rfl) ⟨1485374, by rfl⟩ : syracuseStep 1980499 = 2970749) B2970749
theorem B2889827 : Blo 1803603 2889827 := bstep (se 1 (by rfl) ⟨2167370, by rfl⟩ : syracuseStep 2889827 = 4334741) B4334741
theorem B5486705 : Blo 1803603 5486705 := bstep (se 2 (by rfl) ⟨2057514, by rfl⟩ : syracuseStep 5486705 = 4115029) B4115029
theorem B3045505 : Blo 1803603 3045505 := bstep (se 2 (by rfl) ⟨1142064, by rfl⟩ : syracuseStep 3045505 = 2284129) B2284129
theorem B2889859 : Blo 1803603 2889859 := bstep (se 1 (by rfl) ⟨2167394, by rfl⟩ : syracuseStep 2889859 = 4334789) B4334789
theorem B3045539 : Blo 1803603 3045539 := bstep (se 1 (by rfl) ⟨2284154, by rfl⟩ : syracuseStep 3045539 = 4568309) B4568309
theorem B2029747 : Blo 1803603 2029747 := bstep (se 1 (by rfl) ⟨1522310, by rfl⟩ : syracuseStep 2029747 = 3044621) B3044621
theorem B13179077 : Blo 1803603 13179077 := bstep (se 4 (by rfl) ⟨1235538, by rfl⟩ : syracuseStep 13179077 = 2471077) B2471077
theorem B19503301 : Blo 1803603 19503301 := bstep (se 4 (by rfl) ⟨1828434, by rfl⟩ : syracuseStep 19503301 = 3656869) B3656869
theorem B4061393 : Blo 1803603 4061393 := bstep (se 2 (by rfl) ⟨1523022, by rfl⟩ : syracuseStep 4061393 = 3046045) B3046045
theorem B2570449 : Blo 1803603 2570449 := bstep (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) B1927837
theorem B4061411 : Blo 1803603 4061411 := bstep (se 1 (by rfl) ⟨3046058, by rfl⟩ : syracuseStep 4061411 = 6092117) B6092117
theorem B3250435 : Blo 1803603 3250435 := bstep (se 1 (by rfl) ⟨2437826, by rfl⟩ : syracuseStep 3250435 = 4875653) B4875653
theorem B3905795 : Blo 1803603 3905795 := bstep (se 1 (by rfl) ⟨2929346, by rfl⟩ : syracuseStep 3905795 = 5858693) B5858693
theorem B2439443 : Blo 1803603 2439443 := bstep (se 1 (by rfl) ⟨1829582, by rfl⟩ : syracuseStep 2439443 = 3659165) B3659165
theorem B3045667 : Blo 1803603 3045667 := bstep (se 1 (by rfl) ⟨2284250, by rfl⟩ : syracuseStep 3045667 = 4568501) B4568501
theorem B2570545 : Blo 1803603 2570545 := bstep (se 2 (by rfl) ⟨963954, by rfl⟩ : syracuseStep 2570545 = 1927909) B1927909
theorem B2029891 : Blo 1803603 2029891 := bstep (se 1 (by rfl) ⟨1522418, by rfl⟩ : syracuseStep 2029891 = 3044837) B3044837
theorem B2439491 : Blo 1803603 2439491 := bstep (se 1 (by rfl) ⟨1829618, by rfl⟩ : syracuseStep 2439491 = 3659237) B3659237
theorem B3660113 : Blo 1803603 3660113 := bstep (se 2 (by rfl) ⟨1372542, by rfl⟩ : syracuseStep 3660113 = 2745085) B2745085
theorem B4569443 : Blo 1803603 4569443 := bstep (se 1 (by rfl) ⟨3427082, by rfl⟩ : syracuseStep 4569443 = 6854165) B6854165
theorem B6093197 : Blo 1803603 6093197 := bstep (se 3 (by rfl) ⟨1142474, by rfl⟩ : syracuseStep 6093197 = 2284949) B2284949
theorem B3045809 : Blo 1803603 3045809 := bstep (se 2 (by rfl) ⟨1142178, by rfl⟩ : syracuseStep 3045809 = 2284357) B2284357
theorem B2603443 : Blo 1803603 2603443 := bstep (se 1 (by rfl) ⟨1952582, by rfl⟩ : syracuseStep 2603443 = 3905165) B3905165
theorem B6093251 : Blo 1803603 6093251 := bstep (se 1 (by rfl) ⟨4569938, by rfl⟩ : syracuseStep 6093251 = 9139877) B9139877
theorem B2030035 : Blo 1803603 2030035 := bstep (se 1 (by rfl) ⟨1522526, by rfl⟩ : syracuseStep 2030035 = 3045053) B3045053
theorem B4061681 : Blo 1803603 4061681 := bstep (se 2 (by rfl) ⟨1523130, by rfl⟩ : syracuseStep 4061681 = 3046261) B3046261
theorem B4061699 : Blo 1803603 4061699 := bstep (se 1 (by rfl) ⟨3046274, by rfl⟩ : syracuseStep 4061699 = 6092549) B6092549
theorem B2742817 : Blo 1803603 2742817 := bstep (se 2 (by rfl) ⟨1028556, by rfl⟩ : syracuseStep 2742817 = 2057113) B2057113
theorem B4569635 : Blo 1803603 4569635 := bstep (se 1 (by rfl) ⟨3427226, by rfl⟩ : syracuseStep 4569635 = 6854453) B6854453
theorem B3045937 : Blo 1803603 3045937 := bstep (se 2 (by rfl) ⟨1142226, by rfl⟩ : syracuseStep 3045937 = 2284453) B2284453
theorem B10279493 : Blo 1803603 10279493 := bstep (se 4 (by rfl) ⟨963702, by rfl⟩ : syracuseStep 10279493 = 1927405) B1927405
theorem B3045971 : Blo 1803603 3045971 := bstep (se 1 (by rfl) ⟨2284478, by rfl⟩ : syracuseStep 3045971 = 4568957) B4568957
theorem B2030179 : Blo 1803603 2030179 := bstep (se 1 (by rfl) ⟨1522634, by rfl⟩ : syracuseStep 2030179 = 3045269) B3045269
theorem B9140849 : Blo 1803603 9140849 := bstep (se 2 (by rfl) ⟨3427818, by rfl⟩ : syracuseStep 9140849 = 6855637) B6855637
theorem B7314061 : Blo 1803603 7314061 := bstep (se 3 (by rfl) ⟨1371386, by rfl⟩ : syracuseStep 7314061 = 2742773) B2742773
theorem B2284195 : Blo 1803603 2284195 := bstep (se 1 (by rfl) ⟨1713146, by rfl⟩ : syracuseStep 2284195 = 3426293) B3426293
theorem B8788657 : Blo 1803603 8788657 := bstep (se 2 (by rfl) ⟨3295746, by rfl⟩ : syracuseStep 8788657 = 6591493) B6591493
theorem B9132749 : Blo 1803603 9132749 := bstep (se 3 (by rfl) ⟨1712390, by rfl⟩ : syracuseStep 9132749 = 3424781) B3424781
theorem B6093521 : Blo 1803603 6093521 := bstep (se 2 (by rfl) ⟨2285070, by rfl⟩ : syracuseStep 6093521 = 4570141) B4570141
theorem B3046099 : Blo 1803603 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B2030323 : Blo 1803603 2030323 := bstep (se 1 (by rfl) ⟨1522742, by rfl⟩ : syracuseStep 2030323 = 3045485) B3045485
theorem B2284291 : Blo 1803603 2284291 := bstep (se 1 (by rfl) ⟨1713218, by rfl⟩ : syracuseStep 2284291 = 3426437) B3426437
theorem B4061969 : Blo 1803603 4061969 := bstep (se 2 (by rfl) ⟨1523238, by rfl⟩ : syracuseStep 4061969 = 3046477) B3046477
theorem B4061987 : Blo 1803603 4061987 := bstep (se 1 (by rfl) ⟨3046490, by rfl⟩ : syracuseStep 4061987 = 6092981) B6092981
theorem B3046241 : Blo 1803603 3046241 := bstep (se 2 (by rfl) ⟨1142340, by rfl⟩ : syracuseStep 3046241 = 2284681) B2284681
theorem B2030467 : Blo 1803603 2030467 := bstep (se 1 (by rfl) ⟨1522850, by rfl⟩ : syracuseStep 2030467 = 3045701) B3045701
theorem B6175619 : Blo 1803603 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B3046369 : Blo 1803603 3046369 := bstep (se 2 (by rfl) ⟨1142388, by rfl⟩ : syracuseStep 3046369 = 2284777) B2284777
theorem B4455395 : Blo 1803603 4455395 := bstep (se 1 (by rfl) ⟨3341546, by rfl⟩ : syracuseStep 4455395 = 6683093) B6683093
theorem B3472369 : Blo 1803603 3472369 := bstep (se 2 (by rfl) ⟨1302138, by rfl⟩ : syracuseStep 3472369 = 2604277) B2604277
theorem B3046403 : Blo 1803603 3046403 := bstep (se 1 (by rfl) ⟨2284802, by rfl⟩ : syracuseStep 3046403 = 4569605) B4569605
theorem B2030611 : Blo 1803603 2030611 := bstep (se 1 (by rfl) ⟨1522958, by rfl⟩ : syracuseStep 2030611 = 3045917) B3045917
theorem B2890787 : Blo 1803603 2890787 := bstep (se 1 (by rfl) ⟨2168090, by rfl⟩ : syracuseStep 2890787 = 4336181) B4336181
theorem B4062257 : Blo 1803603 4062257 := bstep (se 2 (by rfl) ⟨1523346, by rfl⟩ : syracuseStep 4062257 = 3046693) B3046693
theorem B4062275 : Blo 1803603 4062275 := bstep (se 1 (by rfl) ⟨3046706, by rfl⟩ : syracuseStep 4062275 = 6093413) B6093413
theorem B13360241 : Blo 1803603 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B2890865 : Blo 1803603 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B3046531 : Blo 1803603 3046531 := bstep (se 1 (by rfl) ⟨2284898, by rfl⟩ : syracuseStep 3046531 = 4569797) B4569797
theorem B5782691 : Blo 1803603 5782691 := bstep (se 1 (by rfl) ⟨4337018, by rfl⟩ : syracuseStep 5782691 = 8674037) B8674037
theorem B2030755 : Blo 1803603 2030755 := bstep (se 1 (by rfl) ⟨1523066, by rfl⟩ : syracuseStep 2030755 = 3046133) B3046133
theorem B2284787 : Blo 1803603 2284787 := bstep (se 1 (by rfl) ⟨1713590, by rfl⟩ : syracuseStep 2284787 = 3427181) B3427181
theorem B3046673 : Blo 1803603 3046673 := bstep (se 2 (by rfl) ⟨1142502, by rfl⟩ : syracuseStep 3046673 = 2285005) B2285005
theorem B2030899 : Blo 1803603 2030899 := bstep (se 1 (by rfl) ⟨1523174, by rfl⟩ : syracuseStep 2030899 = 3046349) B3046349
theorem B2891089 : Blo 1803603 2891089 := bstep (se 2 (by rfl) ⟨1084158, by rfl⟩ : syracuseStep 2891089 = 2168317) B2168317
theorem B4062545 : Blo 1803603 4062545 := bstep (se 2 (by rfl) ⟨1523454, by rfl⟩ : syracuseStep 4062545 = 3046909) B3046909
theorem B4062563 : Blo 1803603 4062563 := bstep (se 1 (by rfl) ⟨3046922, by rfl⟩ : syracuseStep 4062563 = 6093845) B6093845
theorem B3046801 : Blo 1803603 3046801 := bstep (se 2 (by rfl) ⟨1142550, by rfl⟩ : syracuseStep 3046801 = 2285101) B2285101
theorem B7708067 : Blo 1803603 7708067 := bstep (se 1 (by rfl) ⟨5781050, by rfl⟩ : syracuseStep 7708067 = 11562101) B11562101
theorem B3046835 : Blo 1803603 3046835 := bstep (se 1 (by rfl) ⟨2285126, by rfl⟩ : syracuseStep 3046835 = 4570253) B4570253
theorem B2031043 : Blo 1803603 2031043 := bstep (se 1 (by rfl) ⟨1523282, by rfl⟩ : syracuseStep 2031043 = 3046565) B3046565
theorem B2031187 : Blo 1803603 2031187 := bstep (se 1 (by rfl) ⟨1523390, by rfl⟩ : syracuseStep 2031187 = 3046781) B3046781
theorem B2743985 : Blo 1803603 2743985 := bstep (se 2 (by rfl) ⟨1028994, by rfl⟩ : syracuseStep 2743985 = 2057989) B2057989
theorem B12517091 : Blo 1803603 12517091 := bstep (se 1 (by rfl) ⟨9387818, by rfl⟩ : syracuseStep 12517091 = 18775637) B18775637
theorem B3252035 : Blo 1803603 3252035 := bstep (se 1 (by rfl) ⟨2439026, by rfl⟩ : syracuseStep 3252035 = 4878053) B4878053
theorem B6848333 : Blo 1803603 6848333 := bstep (se 3 (by rfl) ⟨1284062, by rfl⟩ : syracuseStep 6848333 = 2568125) B2568125
theorem B27795473 : Blo 1803603 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B16695371 : Blo 1803603 16695371 := bstep (se 1 (by rfl) ⟨12521528, by rfl⟩ : syracuseStep 16695371 = 25043057) B25043057
theorem B7708765 : Blo 1803603 7708765 := bstep (se 3 (by rfl) ⟨1445393, by rfl⟩ : syracuseStep 7708765 = 2890787) B2890787
theorem B8667287 : Blo 1803603 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B35627309 : Blo 1803603 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B6848819 : Blo 1803603 6848819 := bstep (se 1 (by rfl) ⟨5136614, by rfl⟩ : syracuseStep 6848819 = 10273229) B10273229
theorem B6848833 : Blo 1803603 6848833 := bstep (se 2 (by rfl) ⟨2568312, by rfl⟩ : syracuseStep 6848833 = 5136625) B5136625
theorem B4333913 : Blo 1803603 4333913 := bstep (se 2 (by rfl) ⟨1625217, by rfl⟩ : syracuseStep 4333913 = 3250435) B3250435
theorem B7709107 : Blo 1803603 7709107 := bstep (se 1 (by rfl) ⟨5781830, by rfl⟩ : syracuseStep 7709107 = 11563661) B11563661
theorem B14639539 : Blo 1803603 14639539 := bstep (se 1 (by rfl) ⟨10979654, by rfl⟩ : syracuseStep 14639539 = 21959309) B21959309
theorem B6087257 : Blo 1803603 6087257 := bstep (se 2 (by rfl) ⟨2282721, by rfl⟩ : syracuseStep 6087257 = 4565443) B4565443
theorem B5489245 : Blo 1803603 5489245 := bstep (se 3 (by rfl) ⟨1029233, by rfl⟩ : syracuseStep 5489245 = 2058467) B2058467
theorem B6505181 : Blo 1803603 6505181 := bstep (se 3 (by rfl) ⟨1219721, by rfl⟩ : syracuseStep 6505181 = 2439443) B2439443
theorem B6505309 : Blo 1803603 6505309 := bstep (se 3 (by rfl) ⟨1219745, by rfl⟩ : syracuseStep 6505309 = 2439491) B2439491
theorem B3425267 : Blo 1803603 3425267 := bstep (se 1 (by rfl) ⟨2568950, by rfl⟩ : syracuseStep 3425267 = 5137901) B5137901
theorem B7037975 : Blo 1803603 7037975 := bstep (se 1 (by rfl) ⟨5278481, by rfl⟩ : syracuseStep 7037975 = 10556963) B10556963
theorem B9135179 : Blo 1803603 9135179 := bstep (se 1 (by rfl) ⟨6851384, by rfl⟩ : syracuseStep 9135179 = 13702769) B13702769
theorem B20554883 : Blo 1803603 20554883 := bstep (se 1 (by rfl) ⟨15416162, by rfl⟩ : syracuseStep 20554883 = 30832325) B30832325
theorem B3425419 : Blo 1803603 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B4629683 : Blo 1803603 4629683 := bstep (se 1 (by rfl) ⟨3472262, by rfl⟩ : syracuseStep 4629683 = 6944525) B6944525
theorem B21939461 : Blo 1803603 21939461 := bstep (se 4 (by rfl) ⟨2056824, by rfl⟩ : syracuseStep 21939461 = 4113649) B4113649
theorem B6087959 : Blo 1803603 6087959 := bstep (se 1 (by rfl) ⟨4565969, by rfl⟩ : syracuseStep 6087959 = 9131939) B9131939
theorem B1803607 : Blo 1803603 1803607 := bstep (se 1 (by rfl) ⟨1352705, by rfl⟩ : syracuseStep 1803607 = 2705411) B2705411
theorem B1803627 : Blo 1803603 1803627 := bstep (se 1 (by rfl) ⟨1352720, by rfl⟩ : syracuseStep 1803627 = 2705441) B2705441
theorem B1803639 : Blo 1803603 1803639 := bstep (se 1 (by rfl) ⟨1352729, by rfl⟩ : syracuseStep 1803639 = 2705459) B2705459
theorem B1803659 : Blo 1803603 1803659 := bstep (se 1 (by rfl) ⟨1352744, by rfl⟩ : syracuseStep 1803659 = 2705489) B2705489
theorem B1803671 : Blo 1803603 1803671 := bstep (se 1 (by rfl) ⟨1352753, by rfl⟩ : syracuseStep 1803671 = 2705507) B2705507
theorem B1926551 : Blo 1803603 1926551 := bstep (se 1 (by rfl) ⟨1444913, by rfl⟩ : syracuseStep 1926551 = 2889827) B2889827
theorem B1803691 : Blo 1803603 1803691 := bstep (se 1 (by rfl) ⟨1352768, by rfl⟩ : syracuseStep 1803691 = 2705537) B2705537
theorem B1803703 : Blo 1803603 1803703 := bstep (se 1 (by rfl) ⟨1352777, by rfl⟩ : syracuseStep 1803703 = 2705555) B2705555
theorem B1803723 : Blo 1803603 1803723 := bstep (se 1 (by rfl) ⟨1352792, by rfl⟩ : syracuseStep 1803723 = 2705585) B2705585
theorem B1803735 : Blo 1803603 1803735 := bstep (se 1 (by rfl) ⟨1352801, by rfl⟩ : syracuseStep 1803735 = 2705603) B2705603
theorem B3425753 : Blo 1803603 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B1803755 : Blo 1803603 1803755 := bstep (se 1 (by rfl) ⟨1352816, by rfl⟩ : syracuseStep 1803755 = 2705633) B2705633
theorem B1803767 : Blo 1803603 1803767 := bstep (se 1 (by rfl) ⟨1352825, by rfl⟩ : syracuseStep 1803767 = 2705651) B2705651
theorem B1803787 : Blo 1803603 1803787 := bstep (se 1 (by rfl) ⟨1352840, by rfl⟩ : syracuseStep 1803787 = 2705681) B2705681
theorem B1803799 : Blo 1803603 1803799 := bstep (se 1 (by rfl) ⟨1352849, by rfl⟩ : syracuseStep 1803799 = 2705699) B2705699
theorem B1803819 : Blo 1803603 1803819 := bstep (se 1 (by rfl) ⟨1352864, by rfl⟩ : syracuseStep 1803819 = 2705729) B2705729
theorem B1803831 : Blo 1803603 1803831 := bstep (se 1 (by rfl) ⟨1352873, by rfl⟩ : syracuseStep 1803831 = 2705747) B2705747
theorem B1803851 : Blo 1803603 1803851 := bstep (se 1 (by rfl) ⟨1352888, by rfl⟩ : syracuseStep 1803851 = 2705777) B2705777
theorem B1803863 : Blo 1803603 1803863 := bstep (se 1 (by rfl) ⟨1352897, by rfl⟩ : syracuseStep 1803863 = 2705795) B2705795
theorem B1803883 : Blo 1803603 1803883 := bstep (se 1 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 1803883 = 2705825) B2705825
theorem B1803895 : Blo 1803603 1803895 := bstep (se 1 (by rfl) ⟨1352921, by rfl⟩ : syracuseStep 1803895 = 2705843) B2705843
theorem B10274435 : Blo 1803603 10274435 := bstep (se 1 (by rfl) ⟨7705826, by rfl⟩ : syracuseStep 10274435 = 15411653) B15411653
theorem B1803915 : Blo 1803603 1803915 := bstep (se 1 (by rfl) ⟨1352936, by rfl⟩ : syracuseStep 1803915 = 2705873) B2705873
theorem B1803927 : Blo 1803603 1803927 := bstep (se 1 (by rfl) ⟨1352945, by rfl⟩ : syracuseStep 1803927 = 2705891) B2705891
theorem B1803947 : Blo 1803603 1803947 := bstep (se 1 (by rfl) ⟨1352960, by rfl⟩ : syracuseStep 1803947 = 2705921) B2705921
theorem B1803959 : Blo 1803603 1803959 := bstep (se 1 (by rfl) ⟨1352969, by rfl⟩ : syracuseStep 1803959 = 2705939) B2705939
theorem B1803979 : Blo 1803603 1803979 := bstep (se 1 (by rfl) ⟨1352984, by rfl⟩ : syracuseStep 1803979 = 2705969) B2705969
theorem B1803991 : Blo 1803603 1803991 := bstep (se 1 (by rfl) ⟨1352993, by rfl⟩ : syracuseStep 1803991 = 2705987) B2705987
theorem B5211869 : Blo 1803603 5211869 := bstep (se 3 (by rfl) ⟨977225, by rfl⟩ : syracuseStep 5211869 = 1954451) B1954451
theorem B1804011 : Blo 1803603 1804011 := bstep (se 1 (by rfl) ⟨1353008, by rfl⟩ : syracuseStep 1804011 = 2706017) B2706017
theorem B1804023 : Blo 1803603 1804023 := bstep (se 1 (by rfl) ⟨1353017, by rfl⟩ : syracuseStep 1804023 = 2706035) B2706035
theorem B1804043 : Blo 1803603 1804043 := bstep (se 1 (by rfl) ⟨1353032, by rfl⟩ : syracuseStep 1804043 = 2706065) B2706065
theorem B1804055 : Blo 1803603 1804055 := bstep (se 1 (by rfl) ⟨1353041, by rfl⟩ : syracuseStep 1804055 = 2706083) B2706083
theorem B1804075 : Blo 1803603 1804075 := bstep (se 1 (by rfl) ⟨1353056, by rfl⟩ : syracuseStep 1804075 = 2706113) B2706113
theorem B6088499 : Blo 1803603 6088499 := bstep (se 1 (by rfl) ⟨4566374, by rfl⟩ : syracuseStep 6088499 = 9132749) B9132749
theorem B1804087 : Blo 1803603 1804087 := bstep (se 1 (by rfl) ⟨1353065, by rfl⟩ : syracuseStep 1804087 = 2706131) B2706131
theorem B13698881 : Blo 1803603 13698881 := bstep (se 2 (by rfl) ⟨5137080, by rfl⟩ : syracuseStep 13698881 = 10274161) B10274161
theorem B1804107 : Blo 1803603 1804107 := bstep (se 1 (by rfl) ⟨1353080, by rfl⟩ : syracuseStep 1804107 = 2706161) B2706161
theorem B1804119 : Blo 1803603 1804119 := bstep (se 1 (by rfl) ⟨1353089, by rfl⟩ : syracuseStep 1804119 = 2706179) B2706179
theorem B1804139 : Blo 1803603 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B1804151 : Blo 1803603 1804151 := bstep (se 1 (by rfl) ⟨1353113, by rfl⟩ : syracuseStep 1804151 = 2706227) B2706227
theorem B1804171 : Blo 1803603 1804171 := bstep (se 1 (by rfl) ⟨1353128, by rfl⟩ : syracuseStep 1804171 = 2706257) B2706257
theorem B1804183 : Blo 1803603 1804183 := bstep (se 1 (by rfl) ⟨1353137, by rfl⟩ : syracuseStep 1804183 = 2706275) B2706275
theorem B1804203 : Blo 1803603 1804203 := bstep (se 1 (by rfl) ⟨1353152, by rfl⟩ : syracuseStep 1804203 = 2706305) B2706305
theorem B1804215 : Blo 1803603 1804215 := bstep (se 1 (by rfl) ⟨1353161, by rfl⟩ : syracuseStep 1804215 = 2706323) B2706323
theorem B1804235 : Blo 1803603 1804235 := bstep (se 1 (by rfl) ⟨1353176, by rfl⟩ : syracuseStep 1804235 = 2706353) B2706353
theorem B1804247 : Blo 1803603 1804247 := bstep (se 1 (by rfl) ⟨1353185, by rfl⟩ : syracuseStep 1804247 = 2706371) B2706371
theorem B1804267 : Blo 1803603 1804267 := bstep (se 1 (by rfl) ⟨1353200, by rfl⟩ : syracuseStep 1804267 = 2706401) B2706401
theorem B1804279 : Blo 1803603 1804279 := bstep (se 1 (by rfl) ⟨1353209, by rfl⟩ : syracuseStep 1804279 = 2706419) B2706419
theorem B3852299 : Blo 1803603 3852299 := bstep (se 1 (by rfl) ⟨2889224, by rfl⟩ : syracuseStep 3852299 = 5778449) B5778449
theorem B1804299 : Blo 1803603 1804299 := bstep (se 1 (by rfl) ⟨1353224, by rfl⟩ : syracuseStep 1804299 = 2706449) B2706449
theorem B1804311 : Blo 1803603 1804311 := bstep (se 1 (by rfl) ⟨1353233, by rfl⟩ : syracuseStep 1804311 = 2706467) B2706467
theorem B1804331 : Blo 1803603 1804331 := bstep (se 1 (by rfl) ⟨1353248, by rfl⟩ : syracuseStep 1804331 = 2706497) B2706497
theorem B1804343 : Blo 1803603 1804343 := bstep (se 1 (by rfl) ⟨1353257, by rfl⟩ : syracuseStep 1804343 = 2706515) B2706515
theorem B6088769 : Blo 1803603 6088769 := bstep (se 2 (by rfl) ⟨2283288, by rfl⟩ : syracuseStep 6088769 = 4566577) B4566577
theorem B2705483 : Blo 1803603 2705483 := bstep (se 1 (by rfl) ⟨2029112, by rfl⟩ : syracuseStep 2705483 = 4058225) B4058225
theorem B1804363 : Blo 1803603 1804363 := bstep (se 1 (by rfl) ⟨1353272, by rfl⟩ : syracuseStep 1804363 = 2706545) B2706545
theorem B1927243 : Blo 1803603 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B2705495 : Blo 1803603 2705495 := bstep (se 1 (by rfl) ⟨2029121, by rfl⟩ : syracuseStep 2705495 = 4058243) B4058243
theorem B1804375 : Blo 1803603 1804375 := bstep (se 1 (by rfl) ⟨1353281, by rfl⟩ : syracuseStep 1804375 = 2706563) B2706563
theorem B3426391 : Blo 1803603 3426391 := bstep (se 1 (by rfl) ⟨2569793, by rfl⟩ : syracuseStep 3426391 = 5139587) B5139587
theorem B1804395 : Blo 1803603 1804395 := bstep (se 1 (by rfl) ⟨1353296, by rfl⟩ : syracuseStep 1804395 = 2706593) B2706593
theorem B1804407 : Blo 1803603 1804407 := bstep (se 1 (by rfl) ⟨1353305, by rfl⟩ : syracuseStep 1804407 = 2706611) B2706611
theorem B1804427 : Blo 1803603 1804427 := bstep (se 1 (by rfl) ⟨1353320, by rfl⟩ : syracuseStep 1804427 = 2706641) B2706641
theorem B1804439 : Blo 1803603 1804439 := bstep (se 1 (by rfl) ⟨1353329, by rfl⟩ : syracuseStep 1804439 = 2706659) B2706659
theorem B2705561 : Blo 1803603 2705561 := bstep (se 2 (by rfl) ⟨1014585, by rfl⟩ : syracuseStep 2705561 = 2029171) B2029171
theorem B1804459 : Blo 1803603 1804459 := bstep (se 1 (by rfl) ⟨1353344, by rfl⟩ : syracuseStep 1804459 = 2706689) B2706689
theorem B1804471 : Blo 1803603 1804471 := bstep (se 1 (by rfl) ⟨1353353, by rfl⟩ : syracuseStep 1804471 = 2706707) B2706707
theorem B6850763 : Blo 1803603 6850763 := bstep (se 1 (by rfl) ⟨5138072, by rfl⟩ : syracuseStep 6850763 = 10276145) B10276145
theorem B1804491 : Blo 1803603 1804491 := bstep (se 1 (by rfl) ⟨1353368, by rfl⟩ : syracuseStep 1804491 = 2706737) B2706737
theorem B1804503 : Blo 1803603 1804503 := bstep (se 1 (by rfl) ⟨1353377, by rfl⟩ : syracuseStep 1804503 = 2706755) B2706755
theorem B6850777 : Blo 1803603 6850777 := bstep (se 2 (by rfl) ⟨2569041, by rfl⟩ : syracuseStep 6850777 = 5138083) B5138083
theorem B5138653 : Blo 1803603 5138653 := bstep (se 3 (by rfl) ⟨963497, by rfl⟩ : syracuseStep 5138653 = 1926995) B1926995
theorem B1804523 : Blo 1803603 1804523 := bstep (se 1 (by rfl) ⟨1353392, by rfl⟩ : syracuseStep 1804523 = 2706785) B2706785
theorem B1804535 : Blo 1803603 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B2705675 : Blo 1803603 2705675 := bstep (se 1 (by rfl) ⟨2029256, by rfl⟩ : syracuseStep 2705675 = 4058513) B4058513
theorem B1804555 : Blo 1803603 1804555 := bstep (se 1 (by rfl) ⟨1353416, by rfl⟩ : syracuseStep 1804555 = 2706833) B2706833
theorem B11725073 : Blo 1803603 11725073 := bstep (se 2 (by rfl) ⟨4396902, by rfl⟩ : syracuseStep 11725073 = 8793805) B8793805
theorem B2705687 : Blo 1803603 2705687 := bstep (se 1 (by rfl) ⟨2029265, by rfl⟩ : syracuseStep 2705687 = 4058531) B4058531
theorem B5138711 : Blo 1803603 5138711 := bstep (se 1 (by rfl) ⟨3854033, by rfl⟩ : syracuseStep 5138711 = 7708067) B7708067
theorem B1804567 : Blo 1803603 1804567 := bstep (se 1 (by rfl) ⟨1353425, by rfl⟩ : syracuseStep 1804567 = 2706851) B2706851
theorem B1804587 : Blo 1803603 1804587 := bstep (se 1 (by rfl) ⟨1353440, by rfl⟩ : syracuseStep 1804587 = 2706881) B2706881
theorem B1804599 : Blo 1803603 1804599 := bstep (se 1 (by rfl) ⟨1353449, by rfl⟩ : syracuseStep 1804599 = 2706899) B2706899
theorem B17353025 : Blo 1803603 17353025 := bstep (se 2 (by rfl) ⟨6507384, by rfl⟩ : syracuseStep 17353025 = 13014769) B13014769
theorem B1804619 : Blo 1803603 1804619 := bstep (se 1 (by rfl) ⟨1353464, by rfl⟩ : syracuseStep 1804619 = 2706929) B2706929
theorem B1804631 : Blo 1803603 1804631 := bstep (se 1 (by rfl) ⟨1353473, by rfl⟩ : syracuseStep 1804631 = 2706947) B2706947
theorem B2705753 : Blo 1803603 2705753 := bstep (se 2 (by rfl) ⟨1014657, by rfl⟩ : syracuseStep 2705753 = 2029315) B2029315
theorem B1804651 : Blo 1803603 1804651 := bstep (se 1 (by rfl) ⟨1353488, by rfl⟩ : syracuseStep 1804651 = 2706977) B2706977
theorem B1804663 : Blo 1803603 1804663 := bstep (se 1 (by rfl) ⟨1353497, by rfl⟩ : syracuseStep 1804663 = 2706995) B2706995
theorem B1804683 : Blo 1803603 1804683 := bstep (se 1 (by rfl) ⟨1353512, by rfl⟩ : syracuseStep 1804683 = 2707025) B2707025
theorem B1804695 : Blo 1803603 1804695 := bstep (se 1 (by rfl) ⟨1353521, by rfl⟩ : syracuseStep 1804695 = 2707043) B2707043
theorem B1804715 : Blo 1803603 1804715 := bstep (se 1 (by rfl) ⟨1353536, by rfl⟩ : syracuseStep 1804715 = 2707073) B2707073
theorem B1804727 : Blo 1803603 1804727 := bstep (se 1 (by rfl) ⟨1353545, by rfl⟩ : syracuseStep 1804727 = 2707091) B2707091
theorem B2705867 : Blo 1803603 2705867 := bstep (se 1 (by rfl) ⟨2029400, by rfl⟩ : syracuseStep 2705867 = 4058801) B4058801
theorem B1829323 : Blo 1803603 1829323 := bstep (se 1 (by rfl) ⟨1371992, by rfl⟩ : syracuseStep 1829323 = 2743985) B2743985
theorem B1804747 : Blo 1803603 1804747 := bstep (se 1 (by rfl) ⟨1353560, by rfl⟩ : syracuseStep 1804747 = 2707121) B2707121
theorem B2705879 : Blo 1803603 2705879 := bstep (se 1 (by rfl) ⟨2029409, by rfl⟩ : syracuseStep 2705879 = 4058819) B4058819
theorem B1804759 : Blo 1803603 1804759 := bstep (se 1 (by rfl) ⟨1353569, by rfl⟩ : syracuseStep 1804759 = 2707139) B2707139
theorem B1804779 : Blo 1803603 1804779 := bstep (se 1 (by rfl) ⟨1353584, by rfl⟩ : syracuseStep 1804779 = 2707169) B2707169
theorem B1804791 : Blo 1803603 1804791 := bstep (se 1 (by rfl) ⟨1353593, by rfl⟩ : syracuseStep 1804791 = 2707187) B2707187
theorem B1804811 : Blo 1803603 1804811 := bstep (se 1 (by rfl) ⟨1353608, by rfl⟩ : syracuseStep 1804811 = 2707217) B2707217
theorem B1804823 : Blo 1803603 1804823 := bstep (se 1 (by rfl) ⟨1353617, by rfl⟩ : syracuseStep 1804823 = 2707235) B2707235
theorem B2705945 : Blo 1803603 2705945 := bstep (se 2 (by rfl) ⟨1014729, by rfl⟩ : syracuseStep 2705945 = 2029459) B2029459
theorem B1804843 : Blo 1803603 1804843 := bstep (se 1 (by rfl) ⟨1353632, by rfl⟩ : syracuseStep 1804843 = 2707265) B2707265
theorem B4565555 : Blo 1803603 4565555 := bstep (se 1 (by rfl) ⟨3424166, by rfl⟩ : syracuseStep 4565555 = 6848333) B6848333
theorem B1804855 : Blo 1803603 1804855 := bstep (se 1 (by rfl) ⟨1353641, by rfl⟩ : syracuseStep 1804855 = 2707283) B2707283
theorem B32926277 : Blo 1803603 32926277 := bstep (se 4 (by rfl) ⟨3086838, by rfl⟩ : syracuseStep 32926277 = 6173677) B6173677
theorem B1804875 : Blo 1803603 1804875 := bstep (se 1 (by rfl) ⟨1353656, by rfl⟩ : syracuseStep 1804875 = 2707313) B2707313
theorem B1804887 : Blo 1803603 1804887 := bstep (se 1 (by rfl) ⟨1353665, by rfl⟩ : syracuseStep 1804887 = 2707331) B2707331
theorem B6089309 : Blo 1803603 6089309 := bstep (se 3 (by rfl) ⟨1141745, by rfl⟩ : syracuseStep 6089309 = 2283491) B2283491
theorem B1804907 : Blo 1803603 1804907 := bstep (se 1 (by rfl) ⟨1353680, by rfl⟩ : syracuseStep 1804907 = 2707361) B2707361
theorem B1804919 : Blo 1803603 1804919 := bstep (se 1 (by rfl) ⟨1353689, by rfl⟩ : syracuseStep 1804919 = 2707379) B2707379
theorem B2706059 : Blo 1803603 2706059 := bstep (se 1 (by rfl) ⟨2029544, by rfl⟩ : syracuseStep 2706059 = 4059089) B4059089
theorem B1804939 : Blo 1803603 1804939 := bstep (se 1 (by rfl) ⟨1353704, by rfl⟩ : syracuseStep 1804939 = 2707409) B2707409
theorem B2706071 : Blo 1803603 2706071 := bstep (se 1 (by rfl) ⟨2029553, by rfl⟩ : syracuseStep 2706071 = 4059107) B4059107
theorem B1804951 : Blo 1803603 1804951 := bstep (se 1 (by rfl) ⟨1353713, by rfl⟩ : syracuseStep 1804951 = 2707427) B2707427
theorem B1804971 : Blo 1803603 1804971 := bstep (se 1 (by rfl) ⟨1353728, by rfl⟩ : syracuseStep 1804971 = 2707457) B2707457
theorem B1804983 : Blo 1803603 1804983 := bstep (se 1 (by rfl) ⟨1353737, by rfl⟩ : syracuseStep 1804983 = 2707475) B2707475
theorem B1805003 : Blo 1803603 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B1805015 : Blo 1803603 1805015 := bstep (se 1 (by rfl) ⟨1353761, by rfl⟩ : syracuseStep 1805015 = 2707523) B2707523
theorem B2706137 : Blo 1803603 2706137 := bstep (se 2 (by rfl) ⟨1014801, by rfl⟩ : syracuseStep 2706137 = 2029603) B2029603
theorem B1805035 : Blo 1803603 1805035 := bstep (se 1 (by rfl) ⟨1353776, by rfl⟩ : syracuseStep 1805035 = 2707553) B2707553
theorem B1805047 : Blo 1803603 1805047 := bstep (se 1 (by rfl) ⟨1353785, by rfl⟩ : syracuseStep 1805047 = 2707571) B2707571
theorem B1805067 : Blo 1803603 1805067 := bstep (se 1 (by rfl) ⟨1353800, by rfl⟩ : syracuseStep 1805067 = 2707601) B2707601
theorem B1805079 : Blo 1803603 1805079 := bstep (se 1 (by rfl) ⟨1353809, by rfl⟩ : syracuseStep 1805079 = 2707619) B2707619
theorem B2640665 : Blo 1803603 2640665 := bstep (se 2 (by rfl) ⟨990249, by rfl⟩ : syracuseStep 2640665 = 1980499) B1980499
theorem B1805099 : Blo 1803603 1805099 := bstep (se 1 (by rfl) ⟨1353824, by rfl⟩ : syracuseStep 1805099 = 2707649) B2707649
theorem B5860147 : Blo 1803603 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B1805111 : Blo 1803603 1805111 := bstep (se 1 (by rfl) ⟨1353833, by rfl⟩ : syracuseStep 1805111 = 2707667) B2707667
theorem B9136961 : Blo 1803603 9136961 := bstep (se 2 (by rfl) ⟨3426360, by rfl⟩ : syracuseStep 9136961 = 6852721) B6852721
theorem B2706251 : Blo 1803603 2706251 := bstep (se 1 (by rfl) ⟨2029688, by rfl⟩ : syracuseStep 2706251 = 4059377) B4059377
theorem B1805131 : Blo 1803603 1805131 := bstep (se 1 (by rfl) ⟨1353848, by rfl⟩ : syracuseStep 1805131 = 2707697) B2707697
theorem B2706263 : Blo 1803603 2706263 := bstep (se 1 (by rfl) ⟨2029697, by rfl⟩ : syracuseStep 2706263 = 4059395) B4059395
theorem B1805143 : Blo 1803603 1805143 := bstep (se 1 (by rfl) ⟨1353857, by rfl⟩ : syracuseStep 1805143 = 2707715) B2707715
theorem B3853145 : Blo 1803603 3853145 := bstep (se 2 (by rfl) ⟨1444929, by rfl⟩ : syracuseStep 3853145 = 2889859) B2889859
theorem B1805163 : Blo 1803603 1805163 := bstep (se 1 (by rfl) ⟨1353872, by rfl⟩ : syracuseStep 1805163 = 2707745) B2707745
theorem B1805175 : Blo 1803603 1805175 := bstep (se 1 (by rfl) ⟨1353881, by rfl⟩ : syracuseStep 1805175 = 2707763) B2707763
theorem B1805195 : Blo 1803603 1805195 := bstep (se 1 (by rfl) ⟨1353896, by rfl⟩ : syracuseStep 1805195 = 2707793) B2707793
theorem B3427211 : Blo 1803603 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B1805207 : Blo 1803603 1805207 := bstep (se 1 (by rfl) ⟨1353905, by rfl⟩ : syracuseStep 1805207 = 2707811) B2707811
theorem B2706329 : Blo 1803603 2706329 := bstep (se 2 (by rfl) ⟨1014873, by rfl⟩ : syracuseStep 2706329 = 2029747) B2029747
theorem B1805227 : Blo 1803603 1805227 := bstep (se 1 (by rfl) ⟨1353920, by rfl⟩ : syracuseStep 1805227 = 2707841) B2707841
theorem B26004401 : Blo 1803603 26004401 := bstep (se 2 (by rfl) ⟨9751650, by rfl⟩ : syracuseStep 26004401 = 19503301) B19503301
theorem B13003697 : Blo 1803603 13003697 := bstep (se 2 (by rfl) ⟨4876386, by rfl⟩ : syracuseStep 13003697 = 9752773) B9752773
theorem B1805239 : Blo 1803603 1805239 := bstep (se 1 (by rfl) ⟨1353929, by rfl⟩ : syracuseStep 1805239 = 2707859) B2707859
theorem B3427265 : Blo 1803603 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B1805259 : Blo 1803603 1805259 := bstep (se 1 (by rfl) ⟨1353944, by rfl⟩ : syracuseStep 1805259 = 2707889) B2707889
theorem B1805271 : Blo 1803603 1805271 := bstep (se 1 (by rfl) ⟨1353953, by rfl⟩ : syracuseStep 1805271 = 2707907) B2707907
theorem B1805291 : Blo 1803603 1805291 := bstep (se 1 (by rfl) ⟨1353968, by rfl⟩ : syracuseStep 1805291 = 2707937) B2707937
theorem B1805303 : Blo 1803603 1805303 := bstep (se 1 (by rfl) ⟨1353977, by rfl⟩ : syracuseStep 1805303 = 2707955) B2707955
theorem B2706443 : Blo 1803603 2706443 := bstep (se 1 (by rfl) ⟨2029832, by rfl⟩ : syracuseStep 2706443 = 4059665) B4059665
theorem B1805323 : Blo 1803603 1805323 := bstep (se 1 (by rfl) ⟨1353992, by rfl⟩ : syracuseStep 1805323 = 2707985) B2707985
theorem B2198539 : Blo 1803603 2198539 := bstep (se 1 (by rfl) ⟨1648904, by rfl⟩ : syracuseStep 2198539 = 3297809) B3297809
theorem B4058135 : Blo 1803603 4058135 := bstep (se 1 (by rfl) ⟨3043601, by rfl⟩ : syracuseStep 4058135 = 6087203) B6087203
theorem B2706455 : Blo 1803603 2706455 := bstep (se 1 (by rfl) ⟨2029841, by rfl⟩ : syracuseStep 2706455 = 4059683) B4059683
theorem B1805335 : Blo 1803603 1805335 := bstep (se 1 (by rfl) ⟨1354001, by rfl⟩ : syracuseStep 1805335 = 2708003) B2708003
theorem B1805355 : Blo 1803603 1805355 := bstep (se 1 (by rfl) ⟨1354016, by rfl⟩ : syracuseStep 1805355 = 2708033) B2708033
theorem B1805367 : Blo 1803603 1805367 := bstep (se 1 (by rfl) ⟨1354025, by rfl⟩ : syracuseStep 1805367 = 2708051) B2708051
theorem B4566091 : Blo 1803603 4566091 := bstep (se 1 (by rfl) ⟨3424568, by rfl⟩ : syracuseStep 4566091 = 6849137) B6849137
theorem B1805387 : Blo 1803603 1805387 := bstep (se 1 (by rfl) ⟨1354040, by rfl⟩ : syracuseStep 1805387 = 2708081) B2708081
theorem B1805399 : Blo 1803603 1805399 := bstep (se 1 (by rfl) ⟨1354049, by rfl⟩ : syracuseStep 1805399 = 2708099) B2708099
theorem B2706521 : Blo 1803603 2706521 := bstep (se 2 (by rfl) ⟨1014945, by rfl⟩ : syracuseStep 2706521 = 2029891) B2029891
theorem B1805419 : Blo 1803603 1805419 := bstep (se 1 (by rfl) ⟨1354064, by rfl⟩ : syracuseStep 1805419 = 2708129) B2708129
theorem B1805431 : Blo 1803603 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B1805451 : Blo 1803603 1805451 := bstep (se 1 (by rfl) ⟨1354088, by rfl⟩ : syracuseStep 1805451 = 2708177) B2708177
theorem B6851735 : Blo 1803603 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B1805463 : Blo 1803603 1805463 := bstep (se 1 (by rfl) ⟨1354097, by rfl⟩ : syracuseStep 1805463 = 2708195) B2708195
theorem B1805483 : Blo 1803603 1805483 := bstep (se 1 (by rfl) ⟨1354112, by rfl⟩ : syracuseStep 1805483 = 2708225) B2708225
theorem B1805495 : Blo 1803603 1805495 := bstep (se 1 (by rfl) ⟨1354121, by rfl⟩ : syracuseStep 1805495 = 2708243) B2708243
theorem B4058315 : Blo 1803603 4058315 := bstep (se 1 (by rfl) ⟨3043736, by rfl⟩ : syracuseStep 4058315 = 6087473) B6087473
theorem B2706635 : Blo 1803603 2706635 := bstep (se 1 (by rfl) ⟨2029976, by rfl⟩ : syracuseStep 2706635 = 4059953) B4059953
theorem B1805515 : Blo 1803603 1805515 := bstep (se 1 (by rfl) ⟨1354136, by rfl⟩ : syracuseStep 1805515 = 2708273) B2708273
theorem B2706647 : Blo 1803603 2706647 := bstep (se 1 (by rfl) ⟨2029985, by rfl⟩ : syracuseStep 2706647 = 4059971) B4059971
theorem B1805527 : Blo 1803603 1805527 := bstep (se 1 (by rfl) ⟨1354145, by rfl⟩ : syracuseStep 1805527 = 2708291) B2708291
theorem B4566233 : Blo 1803603 4566233 := bstep (se 2 (by rfl) ⟨1712337, by rfl⟩ : syracuseStep 4566233 = 3424675) B3424675
theorem B1805547 : Blo 1803603 1805547 := bstep (se 1 (by rfl) ⟨1354160, by rfl⟩ : syracuseStep 1805547 = 2708321) B2708321
theorem B1805559 : Blo 1803603 1805559 := bstep (se 1 (by rfl) ⟨1354169, by rfl⟩ : syracuseStep 1805559 = 2708339) B2708339
theorem B4058369 : Blo 1803603 4058369 := bstep (se 2 (by rfl) ⟨1521888, by rfl⟩ : syracuseStep 4058369 = 3043777) B3043777
theorem B1805579 : Blo 1803603 1805579 := bstep (se 1 (by rfl) ⟨1354184, by rfl⟩ : syracuseStep 1805579 = 2708369) B2708369
theorem B3656983 : Blo 1803603 3656983 := bstep (se 1 (by rfl) ⟨2742737, by rfl⟩ : syracuseStep 3656983 = 5485475) B5485475
theorem B1805591 : Blo 1803603 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B2706713 : Blo 1803603 2706713 := bstep (se 2 (by rfl) ⟨1015017, by rfl⟩ : syracuseStep 2706713 = 2030035) B2030035
theorem B1830199 : Blo 1803603 1830199 := bstep (se 1 (by rfl) ⟨1372649, by rfl⟩ : syracuseStep 1830199 = 2745299) B2745299
theorem B10980683 : Blo 1803603 10980683 := bstep (se 1 (by rfl) ⟨8235512, by rfl⟩ : syracuseStep 10980683 = 16471025) B16471025
theorem B3657089 : Blo 1803603 3657089 := bstep (se 2 (by rfl) ⟨1371408, by rfl⟩ : syracuseStep 3657089 = 2742817) B2742817
theorem B12520835 : Blo 1803603 12520835 := bstep (se 1 (by rfl) ⟨9390626, by rfl⟩ : syracuseStep 12520835 = 18781253) B18781253
theorem B2706827 : Blo 1803603 2706827 := bstep (se 1 (by rfl) ⟨2030120, by rfl⟩ : syracuseStep 2706827 = 4060241) B4060241
theorem B2706839 : Blo 1803603 2706839 := bstep (se 1 (by rfl) ⟨2030129, by rfl⟩ : syracuseStep 2706839 = 4060259) B4060259
theorem B4058585 : Blo 1803603 4058585 := bstep (se 2 (by rfl) ⟨1521969, by rfl⟩ : syracuseStep 4058585 = 3043939) B3043939
theorem B2706905 : Blo 1803603 2706905 := bstep (se 2 (by rfl) ⟨1015089, by rfl⟩ : syracuseStep 2706905 = 2030179) B2030179
theorem B5139929 : Blo 1803603 5139929 := bstep (se 2 (by rfl) ⟨1927473, by rfl⟩ : syracuseStep 5139929 = 3854947) B3854947
theorem B9752081 : Blo 1803603 9752081 := bstep (se 2 (by rfl) ⟨3657030, by rfl⟩ : syracuseStep 9752081 = 7314061) B7314061
theorem B10415633 : Blo 1803603 10415633 := bstep (se 2 (by rfl) ⟨3905862, by rfl⟩ : syracuseStep 10415633 = 7811725) B7811725
theorem B9760301 : Blo 1803603 9760301 := bstep (se 3 (by rfl) ⟨1830056, by rfl⟩ : syracuseStep 9760301 = 3660113) B3660113
theorem B4058675 : Blo 1803603 4058675 := bstep (se 1 (by rfl) ⟨3044006, by rfl⟩ : syracuseStep 4058675 = 6088013) B6088013
theorem B11718209 : Blo 1803603 11718209 := bstep (se 2 (by rfl) ⟨4394328, by rfl⟩ : syracuseStep 11718209 = 8788657) B8788657
theorem B2707019 : Blo 1803603 2707019 := bstep (se 1 (by rfl) ⟨2030264, by rfl⟩ : syracuseStep 2707019 = 4060529) B4060529
theorem B5140043 : Blo 1803603 5140043 := bstep (se 1 (by rfl) ⟨3855032, by rfl⟩ : syracuseStep 5140043 = 7710065) B7710065
theorem B4058711 : Blo 1803603 4058711 := bstep (se 1 (by rfl) ⟨3044033, by rfl⟩ : syracuseStep 4058711 = 6088067) B6088067
theorem B2707031 : Blo 1803603 2707031 := bstep (se 1 (by rfl) ⟨2030273, by rfl⟩ : syracuseStep 2707031 = 4060547) B4060547
theorem B3853939 : Blo 1803603 3853939 := bstep (se 1 (by rfl) ⟨2890454, by rfl⟩ : syracuseStep 3853939 = 5780909) B5780909
theorem B2707097 : Blo 1803603 2707097 := bstep (se 2 (by rfl) ⟨1015161, by rfl⟩ : syracuseStep 2707097 = 2030323) B2030323
theorem B6090443 : Blo 1803603 6090443 := bstep (se 1 (by rfl) ⟨4567832, by rfl⟩ : syracuseStep 6090443 = 9135665) B9135665
theorem B4230859 : Blo 1803603 4230859 := bstep (se 1 (by rfl) ⟨3173144, by rfl⟩ : syracuseStep 4230859 = 6346289) B6346289
theorem B2780887 : Blo 1803603 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B13700825 : Blo 1803603 13700825 := bstep (se 2 (by rfl) ⟨5137809, by rfl⟩ : syracuseStep 13700825 = 10275619) B10275619
theorem B4058891 : Blo 1803603 4058891 := bstep (se 1 (by rfl) ⟨3044168, by rfl⟩ : syracuseStep 4058891 = 6088337) B6088337
theorem B2707211 : Blo 1803603 2707211 := bstep (se 1 (by rfl) ⟨2030408, by rfl⟩ : syracuseStep 2707211 = 4060817) B4060817
theorem B2707223 : Blo 1803603 2707223 := bstep (se 1 (by rfl) ⟨2030417, by rfl⟩ : syracuseStep 2707223 = 4060835) B4060835
theorem B4058945 : Blo 1803603 4058945 := bstep (se 2 (by rfl) ⟨1522104, by rfl⟩ : syracuseStep 4058945 = 3044209) B3044209
theorem B49475393 : Blo 1803603 49475393 := bstep (se 2 (by rfl) ⟨18553272, by rfl⟩ : syracuseStep 49475393 = 37106545) B37106545
theorem B13012811 : Blo 1803603 13012811 := bstep (se 1 (by rfl) ⟨9759608, by rfl⟩ : syracuseStep 13012811 = 19519217) B19519217
theorem B2707289 : Blo 1803603 2707289 := bstep (se 2 (by rfl) ⟨1015233, by rfl⟩ : syracuseStep 2707289 = 2030467) B2030467
theorem B2707403 : Blo 1803603 2707403 := bstep (se 1 (by rfl) ⟨2030552, by rfl⟩ : syracuseStep 2707403 = 4061105) B4061105
theorem B2707415 : Blo 1803603 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B6090713 : Blo 1803603 6090713 := bstep (se 2 (by rfl) ⟨2284017, by rfl⟩ : syracuseStep 6090713 = 4568035) B4568035
theorem B4567063 : Blo 1803603 4567063 := bstep (se 1 (by rfl) ⟨3425297, by rfl⟩ : syracuseStep 4567063 = 6850595) B6850595
theorem B4059161 : Blo 1803603 4059161 := bstep (se 2 (by rfl) ⟨1522185, by rfl⟩ : syracuseStep 4059161 = 3044371) B3044371
theorem B2707481 : Blo 1803603 2707481 := bstep (se 2 (by rfl) ⟨1015305, by rfl⟩ : syracuseStep 2707481 = 2030611) B2030611
theorem B3657803 : Blo 1803603 3657803 := bstep (se 1 (by rfl) ⟨2743352, by rfl⟩ : syracuseStep 3657803 = 5486705) B5486705
theorem B7704665 : Blo 1803603 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B4059251 : Blo 1803603 4059251 := bstep (se 1 (by rfl) ⟨3044438, by rfl⟩ : syracuseStep 4059251 = 6088877) B6088877
theorem B8786051 : Blo 1803603 8786051 := bstep (se 1 (by rfl) ⟨6589538, by rfl⟩ : syracuseStep 8786051 = 13179077) B13179077
theorem B2707595 : Blo 1803603 2707595 := bstep (se 1 (by rfl) ⟨2030696, by rfl⟩ : syracuseStep 2707595 = 4061393) B4061393
theorem B4059287 : Blo 1803603 4059287 := bstep (se 1 (by rfl) ⟨3044465, by rfl⟩ : syracuseStep 4059287 = 6088931) B6088931
theorem B2707607 : Blo 1803603 2707607 := bstep (se 1 (by rfl) ⟨2030705, by rfl⟩ : syracuseStep 2707607 = 4061411) B4061411
theorem B2707673 : Blo 1803603 2707673 := bstep (se 2 (by rfl) ⟨1015377, by rfl⟩ : syracuseStep 2707673 = 2030755) B2030755
theorem B13709573 : Blo 1803603 13709573 := bstep (se 4 (by rfl) ⟨1285272, by rfl⟩ : syracuseStep 13709573 = 2570545) B2570545
theorem B3043595 : Blo 1803603 3043595 := bstep (se 1 (by rfl) ⟨2282696, by rfl⟩ : syracuseStep 3043595 = 4565393) B4565393
theorem B4059467 : Blo 1803603 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B2707787 : Blo 1803603 2707787 := bstep (se 1 (by rfl) ⟨2030840, by rfl⟩ : syracuseStep 2707787 = 4061681) B4061681
theorem B2707799 : Blo 1803603 2707799 := bstep (se 1 (by rfl) ⟨2030849, by rfl⟩ : syracuseStep 2707799 = 4061699) B4061699
theorem B12341605 : Blo 1803603 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B4059521 : Blo 1803603 4059521 := bstep (se 2 (by rfl) ⟨1522320, by rfl⟩ : syracuseStep 4059521 = 3044641) B3044641
theorem B6852995 : Blo 1803603 6852995 := bstep (se 1 (by rfl) ⟨5139746, by rfl⟩ : syracuseStep 6852995 = 10279493) B10279493
theorem B3043723 : Blo 1803603 3043723 := bstep (se 1 (by rfl) ⟨2282792, by rfl⟩ : syracuseStep 3043723 = 4565585) B4565585
theorem B2707865 : Blo 1803603 2707865 := bstep (se 2 (by rfl) ⟨1015449, by rfl⟩ : syracuseStep 2707865 = 2030899) B2030899
theorem B3854785 : Blo 1803603 3854785 := bstep (se 2 (by rfl) ⟨1445544, by rfl⟩ : syracuseStep 3854785 = 2891089) B2891089
theorem B4567499 : Blo 1803603 4567499 := bstep (se 1 (by rfl) ⟨3425624, by rfl⟩ : syracuseStep 4567499 = 6851249) B6851249
theorem B6173131 : Blo 1803603 6173131 := bstep (se 1 (by rfl) ⟨4629848, by rfl⟩ : syracuseStep 6173131 = 9259697) B9259697
theorem B4878809 : Blo 1803603 4878809 := bstep (se 2 (by rfl) ⟨1829553, by rfl⟩ : syracuseStep 4878809 = 3659107) B3659107
theorem B2707979 : Blo 1803603 2707979 := bstep (se 1 (by rfl) ⟨2030984, by rfl⟩ : syracuseStep 2707979 = 4061969) B4061969
theorem B2707991 : Blo 1803603 2707991 := bstep (se 1 (by rfl) ⟨2030993, by rfl⟩ : syracuseStep 2707991 = 4061987) B4061987
theorem B3043865 : Blo 1803603 3043865 := bstep (se 2 (by rfl) ⟨1141449, by rfl⟩ : syracuseStep 3043865 = 2282899) B2282899
theorem B2568791 : Blo 1803603 2568791 := bstep (se 1 (by rfl) ⟨1926593, by rfl⟩ : syracuseStep 2568791 = 3853187) B3853187
theorem B4059737 : Blo 1803603 4059737 := bstep (se 2 (by rfl) ⟨1522401, by rfl⟩ : syracuseStep 4059737 = 3044803) B3044803
theorem B4117079 : Blo 1803603 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B2708057 : Blo 1803603 2708057 := bstep (se 2 (by rfl) ⟨1015521, by rfl⟩ : syracuseStep 2708057 = 2031043) B2031043
theorem B2970263 : Blo 1803603 2970263 := bstep (se 1 (by rfl) ⟨2227697, by rfl⟩ : syracuseStep 2970263 = 4455395) B4455395
theorem B6091415 : Blo 1803603 6091415 := bstep (se 1 (by rfl) ⟨4568561, by rfl⟩ : syracuseStep 6091415 = 9137123) B9137123
theorem B3043993 : Blo 1803603 3043993 := bstep (se 2 (by rfl) ⟨1141497, by rfl⟩ : syracuseStep 3043993 = 2282995) B2282995
theorem B4059827 : Blo 1803603 4059827 := bstep (se 1 (by rfl) ⟨3044870, by rfl⟩ : syracuseStep 4059827 = 6089741) B6089741
theorem B5141171 : Blo 1803603 5141171 := bstep (se 1 (by rfl) ⟨3855878, by rfl⟩ : syracuseStep 5141171 = 7711757) B7711757
theorem B2708171 : Blo 1803603 2708171 := bstep (se 1 (by rfl) ⟨2031128, by rfl⟩ : syracuseStep 2708171 = 4062257) B4062257
theorem B4059863 : Blo 1803603 4059863 := bstep (se 1 (by rfl) ⟨3044897, by rfl⟩ : syracuseStep 4059863 = 6089795) B6089795
theorem B2708183 : Blo 1803603 2708183 := bstep (se 1 (by rfl) ⟨2031137, by rfl⟩ : syracuseStep 2708183 = 4062275) B4062275
theorem B9138905 : Blo 1803603 9138905 := bstep (se 2 (by rfl) ⟨3427089, by rfl⟩ : syracuseStep 9138905 = 6854179) B6854179
theorem B3855127 : Blo 1803603 3855127 := bstep (se 1 (by rfl) ⟨2891345, by rfl⟩ : syracuseStep 3855127 = 5782691) B5782691
theorem B2708249 : Blo 1803603 2708249 := bstep (se 2 (by rfl) ⟨1015593, by rfl⟩ : syracuseStep 2708249 = 2031187) B2031187
theorem B4567873 : Blo 1803603 4567873 := bstep (se 2 (by rfl) ⟨1712952, by rfl⟩ : syracuseStep 4567873 = 3425905) B3425905
theorem B8672093 : Blo 1803603 8672093 := bstep (se 3 (by rfl) ⟨1626017, by rfl⟩ : syracuseStep 8672093 = 3252035) B3252035
theorem B2569099 : Blo 1803603 2569099 := bstep (se 1 (by rfl) ⟨1926824, by rfl⟩ : syracuseStep 2569099 = 3853649) B3853649
theorem B4060043 : Blo 1803603 4060043 := bstep (se 1 (by rfl) ⟨3045032, by rfl⟩ : syracuseStep 4060043 = 6090065) B6090065
theorem B2708363 : Blo 1803603 2708363 := bstep (se 1 (by rfl) ⟨2031272, by rfl⟩ : syracuseStep 2708363 = 4062545) B4062545
theorem B2708375 : Blo 1803603 2708375 := bstep (se 1 (by rfl) ⟨2031281, by rfl⟩ : syracuseStep 2708375 = 4062563) B4062563
theorem B4060097 : Blo 1803603 4060097 := bstep (se 2 (by rfl) ⟨1522536, by rfl⟩ : syracuseStep 4060097 = 3045073) B3045073
theorem B5141569 : Blo 1803603 5141569 := bstep (se 2 (by rfl) ⟨1928088, by rfl⟩ : syracuseStep 5141569 = 3856177) B3856177
theorem B8344727 : Blo 1803603 8344727 := bstep (se 1 (by rfl) ⟨6258545, by rfl⟩ : syracuseStep 8344727 = 12517091) B12517091
theorem B4060313 : Blo 1803603 4060313 := bstep (se 2 (by rfl) ⟨1522617, by rfl⟩ : syracuseStep 4060313 = 3045235) B3045235
theorem B6091955 : Blo 1803603 6091955 := bstep (se 1 (by rfl) ⟨4568966, by rfl⟩ : syracuseStep 6091955 = 9137933) B9137933
theorem B7705793 : Blo 1803603 7705793 := bstep (se 2 (by rfl) ⟨2889672, by rfl⟩ : syracuseStep 7705793 = 5779345) B5779345
theorem B3044567 : Blo 1803603 3044567 := bstep (se 1 (by rfl) ⟨2283425, by rfl⟩ : syracuseStep 3044567 = 4566851) B4566851
theorem B4060403 : Blo 1803603 4060403 := bstep (se 1 (by rfl) ⟨3045302, by rfl⟩ : syracuseStep 4060403 = 6090605) B6090605
theorem B18519301 : Blo 1803603 18519301 := bstep (se 4 (by rfl) ⟨1736184, by rfl⟩ : syracuseStep 18519301 = 3472369) B3472369
theorem B4060439 : Blo 1803603 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B3044695 : Blo 1803603 3044695 := bstep (se 1 (by rfl) ⟨2283521, by rfl⟩ : syracuseStep 3044695 = 4567043) B4567043
theorem B4568471 : Blo 1803603 4568471 := bstep (se 1 (by rfl) ⟨3426353, by rfl⟩ : syracuseStep 4568471 = 6852707) B6852707
theorem B6092225 : Blo 1803603 6092225 := bstep (se 2 (by rfl) ⟨2284584, by rfl⟩ : syracuseStep 6092225 = 4569169) B4569169
theorem B4060619 : Blo 1803603 4060619 := bstep (se 1 (by rfl) ⟨3045464, by rfl⟩ : syracuseStep 4060619 = 6090929) B6090929
theorem B4060673 : Blo 1803603 4060673 := bstep (se 2 (by rfl) ⟨1522752, by rfl⟩ : syracuseStep 4060673 = 3045505) B3045505
theorem B2029099 : Blo 1803603 2029099 := bstep (se 1 (by rfl) ⟨1521824, by rfl⟩ : syracuseStep 2029099 = 3043649) B3043649
theorem B11130443 : Blo 1803603 11130443 := bstep (se 1 (by rfl) ⟨8347832, by rfl⟩ : syracuseStep 11130443 = 16695665) B16695665
theorem B2029207 : Blo 1803603 2029207 := bstep (se 1 (by rfl) ⟨1521905, by rfl⟩ : syracuseStep 2029207 = 3043811) B3043811
theorem B2283223 : Blo 1803603 2283223 := bstep (se 1 (by rfl) ⟨1712417, by rfl⟩ : syracuseStep 2283223 = 3424835) B3424835
theorem B4060889 : Blo 1803603 4060889 := bstep (se 2 (by rfl) ⟨1522833, by rfl⟩ : syracuseStep 4060889 = 3045667) B3045667
theorem B4060979 : Blo 1803603 4060979 := bstep (se 1 (by rfl) ⟨3045734, by rfl⟩ : syracuseStep 4060979 = 6091469) B6091469
theorem B2029387 : Blo 1803603 2029387 := bstep (se 1 (by rfl) ⟨1522040, by rfl⟩ : syracuseStep 2029387 = 3044081) B3044081
theorem B4061015 : Blo 1803603 4061015 := bstep (se 1 (by rfl) ⟨3045761, by rfl⟩ : syracuseStep 4061015 = 6091523) B6091523
theorem B2570135 : Blo 1803603 2570135 := bstep (se 1 (by rfl) ⟨1927601, by rfl⟩ : syracuseStep 2570135 = 3855203) B3855203
theorem B3471257 : Blo 1803603 3471257 := bstep (se 2 (by rfl) ⟨1301721, by rfl⟩ : syracuseStep 3471257 = 2603443) B2603443
theorem B2029495 : Blo 1803603 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B6862795 : Blo 1803603 6862795 := bstep (se 1 (by rfl) ⟨5147096, by rfl⟩ : syracuseStep 6862795 = 10294193) B10294193
theorem B3045323 : Blo 1803603 3045323 := bstep (se 1 (by rfl) ⟨2283992, by rfl⟩ : syracuseStep 3045323 = 4567985) B4567985
theorem B6092765 : Blo 1803603 6092765 := bstep (se 3 (by rfl) ⟨1142393, by rfl⟩ : syracuseStep 6092765 = 2284787) B2284787
theorem B4061195 : Blo 1803603 4061195 := bstep (se 1 (by rfl) ⟨3045896, by rfl⟩ : syracuseStep 4061195 = 6091793) B6091793
theorem B4061249 : Blo 1803603 4061249 := bstep (se 2 (by rfl) ⟨1522968, by rfl⟩ : syracuseStep 4061249 = 3045937) B3045937
theorem B3045451 : Blo 1803603 3045451 := bstep (se 1 (by rfl) ⟨2284088, by rfl⟩ : syracuseStep 3045451 = 4568177) B4568177
theorem B2570329 : Blo 1803603 2570329 := bstep (se 2 (by rfl) ⟨963873, by rfl⟩ : syracuseStep 2570329 = 1927747) B1927747
theorem B2029675 : Blo 1803603 2029675 := bstep (se 1 (by rfl) ⟨1522256, by rfl⟩ : syracuseStep 2029675 = 3044513) B3044513
theorem B2087051 : Blo 1803603 2087051 := bstep (se 1 (by rfl) ⟨1565288, by rfl⟩ : syracuseStep 2087051 = 3130577) B3130577
theorem B4569281 : Blo 1803603 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B2029783 : Blo 1803603 2029783 := bstep (se 1 (by rfl) ⟨1522337, by rfl⟩ : syracuseStep 2029783 = 3044675) B3044675
theorem B3045593 : Blo 1803603 3045593 := bstep (se 2 (by rfl) ⟨1142097, by rfl⟩ : syracuseStep 3045593 = 2284195) B2284195
theorem B30841073 : Blo 1803603 30841073 := bstep (se 2 (by rfl) ⟨11565402, by rfl⟩ : syracuseStep 30841073 = 23130805) B23130805
theorem B4061465 : Blo 1803603 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B9140525 : Blo 1803603 9140525 := bstep (se 3 (by rfl) ⟨1713848, by rfl⟩ : syracuseStep 9140525 = 3427697) B3427697
theorem B3045721 : Blo 1803603 3045721 := bstep (se 2 (by rfl) ⟨1142145, by rfl⟩ : syracuseStep 3045721 = 2284291) B2284291
theorem B4061555 : Blo 1803603 4061555 := bstep (se 1 (by rfl) ⟨3046166, by rfl⟩ : syracuseStep 4061555 = 6092333) B6092333
theorem B2029963 : Blo 1803603 2029963 := bstep (se 1 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 2029963 = 3044945) B3044945
theorem B4061591 : Blo 1803603 4061591 := bstep (se 1 (by rfl) ⟨3046193, by rfl⟩ : syracuseStep 4061591 = 6092387) B6092387
theorem B3660275 : Blo 1803603 3660275 := bstep (se 1 (by rfl) ⟨2745206, by rfl⟩ : syracuseStep 3660275 = 5490413) B5490413
theorem B2030071 : Blo 1803603 2030071 := bstep (se 1 (by rfl) ⟨1522553, by rfl⟩ : syracuseStep 2030071 = 3045107) B3045107
theorem B4061771 : Blo 1803603 4061771 := bstep (se 1 (by rfl) ⟨3046328, by rfl⟩ : syracuseStep 4061771 = 6092657) B6092657
theorem B4061825 : Blo 1803603 4061825 := bstep (se 2 (by rfl) ⟨1523184, by rfl⟩ : syracuseStep 4061825 = 3046369) B3046369
theorem B2030251 : Blo 1803603 2030251 := bstep (se 1 (by rfl) ⟨1522688, by rfl⟩ : syracuseStep 2030251 = 3045377) B3045377
theorem B6503105 : Blo 1803603 6503105 := bstep (se 2 (by rfl) ⟨2438664, by rfl⟩ : syracuseStep 6503105 = 4877329) B4877329
theorem B4569817 : Blo 1803603 4569817 := bstep (se 2 (by rfl) ⟨1713681, by rfl⟩ : syracuseStep 4569817 = 3427363) B3427363
theorem B2030359 : Blo 1803603 2030359 := bstep (se 1 (by rfl) ⟨1522769, by rfl⟩ : syracuseStep 2030359 = 3045539) B3045539
theorem B6503233 : Blo 1803603 6503233 := bstep (se 2 (by rfl) ⟨2438712, by rfl⟩ : syracuseStep 6503233 = 4877425) B4877425
theorem B7707467 : Blo 1803603 7707467 := bstep (se 1 (by rfl) ⟨5780600, by rfl⟩ : syracuseStep 7707467 = 11561201) B11561201
theorem B2603863 : Blo 1803603 2603863 := bstep (se 1 (by rfl) ⟨1952897, by rfl⟩ : syracuseStep 2603863 = 3905795) B3905795
theorem B4062041 : Blo 1803603 4062041 := bstep (se 2 (by rfl) ⟨1523265, by rfl⟩ : syracuseStep 4062041 = 3046531) B3046531
theorem B10279811 : Blo 1803603 10279811 := bstep (se 1 (by rfl) ⟨7709858, by rfl⟩ : syracuseStep 10279811 = 15419717) B15419717
theorem B3046295 : Blo 1803603 3046295 := bstep (se 1 (by rfl) ⟨2284721, by rfl⟩ : syracuseStep 3046295 = 4569443) B4569443
theorem B4062131 : Blo 1803603 4062131 := bstep (se 1 (by rfl) ⟨3046598, by rfl⟩ : syracuseStep 4062131 = 6093197) B6093197
theorem B2030539 : Blo 1803603 2030539 := bstep (se 1 (by rfl) ⟨1522904, by rfl⟩ : syracuseStep 2030539 = 3045809) B3045809
theorem B4062167 : Blo 1803603 4062167 := bstep (se 1 (by rfl) ⟨3046625, by rfl⟩ : syracuseStep 4062167 = 6093251) B6093251
theorem B9133073 : Blo 1803603 9133073 := bstep (se 2 (by rfl) ⟨3424902, by rfl⟩ : syracuseStep 9133073 = 6849805) B6849805
theorem B3046423 : Blo 1803603 3046423 := bstep (se 1 (by rfl) ⟨2284817, by rfl⟩ : syracuseStep 3046423 = 4569635) B4569635
theorem B13704227 : Blo 1803603 13704227 := bstep (se 1 (by rfl) ⟨10278170, by rfl⟩ : syracuseStep 13704227 = 20556341) B20556341
theorem B2030647 : Blo 1803603 2030647 := bstep (se 1 (by rfl) ⟨1522985, by rfl⟩ : syracuseStep 2030647 = 3045971) B3045971
theorem B6093899 : Blo 1803603 6093899 := bstep (se 1 (by rfl) ⟨4570424, by rfl⟩ : syracuseStep 6093899 = 9140849) B9140849
theorem B4062347 : Blo 1803603 4062347 := bstep (se 1 (by rfl) ⟨3046760, by rfl⟩ : syracuseStep 4062347 = 6093521) B6093521
theorem B2890903 : Blo 1803603 2890903 := bstep (se 1 (by rfl) ⟨2168177, by rfl⟩ : syracuseStep 2890903 = 4336355) B4336355
theorem B8346797 : Blo 1803603 8346797 := bstep (se 3 (by rfl) ⟨1565024, by rfl⟩ : syracuseStep 8346797 = 3130049) B3130049
theorem B15408305 : Blo 1803603 15408305 := bstep (se 2 (by rfl) ⟨5778114, by rfl⟩ : syracuseStep 15408305 = 11556229) B11556229
theorem B9133235 : Blo 1803603 9133235 := bstep (se 1 (by rfl) ⟨6849926, by rfl⟩ : syracuseStep 9133235 = 13699853) B13699853
theorem B4062401 : Blo 1803603 4062401 := bstep (se 2 (by rfl) ⟨1523400, by rfl⟩ : syracuseStep 4062401 = 3046801) B3046801
theorem B2030827 : Blo 1803603 2030827 := bstep (se 1 (by rfl) ⟨1523120, by rfl⟩ : syracuseStep 2030827 = 3046241) B3046241
theorem B26008897 : Blo 1803603 26008897 := bstep (se 2 (by rfl) ⟨9753336, by rfl⟩ : syracuseStep 26008897 = 19506673) B19506673
theorem B10280267 : Blo 1803603 10280267 := bstep (se 1 (by rfl) ⟨7710200, by rfl⟩ : syracuseStep 10280267 = 15420401) B15420401
theorem B2030935 : Blo 1803603 2030935 := bstep (se 1 (by rfl) ⟨1523201, by rfl⟩ : syracuseStep 2030935 = 3046403) B3046403
theorem B2284939 : Blo 1803603 2284939 := bstep (se 1 (by rfl) ⟨1713704, by rfl⟩ : syracuseStep 2284939 = 3427409) B3427409
theorem B56335765 : Blo 1803603 56335765 := bstep (se 6 (by rfl) ⟨1320369, by rfl⟩ : syracuseStep 56335765 = 2640739) B2640739
theorem B3087769 : Blo 1803603 3087769 := bstep (se 2 (by rfl) ⟨1157913, by rfl⟩ : syracuseStep 3087769 = 2315827) B2315827
theorem B2031115 : Blo 1803603 2031115 := bstep (se 1 (by rfl) ⟨1523336, by rfl⟩ : syracuseStep 2031115 = 3046673) B3046673
theorem B2031223 : Blo 1803603 2031223 := bstep (se 1 (by rfl) ⟨1523417, by rfl⟩ : syracuseStep 2031223 = 3046835) B3046835
theorem B2891467 : Blo 1803603 2891467 := bstep (se 1 (by rfl) ⟨2168600, by rfl⟩ : syracuseStep 2891467 = 4337201) B4337201
theorem B2891531 : Blo 1803603 2891531 := bstep (se 1 (by rfl) ⟨2168648, by rfl⟩ : syracuseStep 2891531 = 4337297) B4337297
theorem B2744087 : Blo 1803603 2744087 := bstep (se 1 (by rfl) ⟨2058065, by rfl⟩ : syracuseStep 2744087 = 4116131) B4116131
theorem B7315265 : Blo 1803603 7315265 := bstep (se 2 (by rfl) ⟨2743224, by rfl⟩ : syracuseStep 7315265 = 5486449) B5486449
theorem B8789825 : Blo 1803603 8789825 := bstep (se 2 (by rfl) ⟨3296184, by rfl⟩ : syracuseStep 8789825 = 6592369) B6592369
theorem B16465841 : Blo 1803603 16465841 := bstep (se 2 (by rfl) ⟨6174690, by rfl⟩ : syracuseStep 16465841 = 12349381) B12349381
theorem B18530315 : Blo 1803603 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B5136443 : Blo 1803603 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B18767933 : Blo 1803603 18767933 := bstep (se 3 (by rfl) ⟨3518987, by rfl⟩ : syracuseStep 18767933 = 7037975) B7037975
theorem B5857367 : Blo 1803603 5857367 := bstep (se 1 (by rfl) ⟨4393025, by rfl⟩ : syracuseStep 5857367 = 8786051) B8786051
theorem B29270261 : Blo 1803603 29270261 := bstep (se 5 (by rfl) ⟨1372043, by rfl⟩ : syracuseStep 29270261 = 2744087) B2744087
theorem B9134369 : Blo 1803603 9134369 := bstep (se 2 (by rfl) ⟨3425388, by rfl⟩ : syracuseStep 9134369 = 6850777) B6850777
theorem B3252539 : Blo 1803603 3252539 := bstep (se 1 (by rfl) ⟨2439404, by rfl⟩ : syracuseStep 3252539 = 4878809) B4878809
theorem B12345821 : Blo 1803603 12345821 := bstep (se 3 (by rfl) ⟨2314841, by rfl⟩ : syracuseStep 12345821 = 4629683) B4629683
theorem B5563151 : Blo 1803603 5563151 := bstep (se 1 (by rfl) ⟨4172363, by rfl⟩ : syracuseStep 5563151 = 8344727) B8344727
theorem B5137195 : Blo 1803603 5137195 := bstep (se 1 (by rfl) ⟨3852896, by rfl⟩ : syracuseStep 5137195 = 7705793) B7705793
theorem B5137469 : Blo 1803603 5137469 := bstep (se 3 (by rfl) ⟨963275, by rfl⟩ : syracuseStep 5137469 = 1926551) B1926551
theorem B6849623 : Blo 1803603 6849623 := bstep (se 1 (by rfl) ⟨5137217, by rfl⟩ : syracuseStep 6849623 = 10274435) B10274435
theorem B3425465 : Blo 1803603 3425465 := bstep (se 2 (by rfl) ⟨1284549, by rfl⟩ : syracuseStep 3425465 = 2569099) B2569099
theorem B9135341 : Blo 1803603 9135341 := bstep (se 3 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 9135341 = 3425753) B3425753
theorem B1803655 : Blo 1803603 1803655 := bstep (se 1 (by rfl) ⟨1352741, by rfl⟩ : syracuseStep 1803655 = 2705483) B2705483
theorem B1803663 : Blo 1803603 1803663 := bstep (se 1 (by rfl) ⟨1352747, by rfl⟩ : syracuseStep 1803663 = 2705495) B2705495
theorem B6088121 : Blo 1803603 6088121 := bstep (se 2 (by rfl) ⟨2283045, by rfl⟩ : syracuseStep 6088121 = 4566091) B4566091
theorem B1803707 : Blo 1803603 1803707 := bstep (se 1 (by rfl) ⟨1352780, by rfl⟩ : syracuseStep 1803707 = 2705561) B2705561
theorem B1803783 : Blo 1803603 1803783 := bstep (se 1 (by rfl) ⟨1352837, by rfl⟩ : syracuseStep 1803783 = 2705675) B2705675
theorem B7816715 : Blo 1803603 7816715 := bstep (se 1 (by rfl) ⟨5862536, by rfl⟩ : syracuseStep 7816715 = 11725073) B11725073
theorem B1803791 : Blo 1803603 1803791 := bstep (se 1 (by rfl) ⟨1352843, by rfl⟩ : syracuseStep 1803791 = 2705687) B2705687
theorem B3425807 : Blo 1803603 3425807 := bstep (se 1 (by rfl) ⟨2569355, by rfl⟩ : syracuseStep 3425807 = 5138711) B5138711
theorem B11568683 : Blo 1803603 11568683 := bstep (se 1 (by rfl) ⟨8676512, by rfl⟩ : syracuseStep 11568683 = 17353025) B17353025
theorem B1803835 : Blo 1803603 1803835 := bstep (se 1 (by rfl) ⟨1352876, by rfl⟩ : syracuseStep 1803835 = 2705753) B2705753
theorem B6850109 : Blo 1803603 6850109 := bstep (se 3 (by rfl) ⟨1284395, by rfl⟩ : syracuseStep 6850109 = 2568791) B2568791
theorem B10978877 : Blo 1803603 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B1803911 : Blo 1803603 1803911 := bstep (se 1 (by rfl) ⟨1352933, by rfl⟩ : syracuseStep 1803911 = 2705867) B2705867
theorem B1803919 : Blo 1803603 1803919 := bstep (se 1 (by rfl) ⟨1352939, by rfl⟩ : syracuseStep 1803919 = 2705879) B2705879
theorem B24692401 : Blo 1803603 24692401 := bstep (se 2 (by rfl) ⟨9259650, by rfl⟩ : syracuseStep 24692401 = 18519301) B18519301
theorem B1803963 : Blo 1803603 1803963 := bstep (se 1 (by rfl) ⟨1352972, by rfl⟩ : syracuseStep 1803963 = 2705945) B2705945
theorem B4875977 : Blo 1803603 4875977 := bstep (se 2 (by rfl) ⟨1828491, by rfl⟩ : syracuseStep 4875977 = 3656983) B3656983
theorem B34678529 : Blo 1803603 34678529 := bstep (se 2 (by rfl) ⟨13004448, by rfl⟩ : syracuseStep 34678529 = 26008897) B26008897
theorem B1804039 : Blo 1803603 1804039 := bstep (se 1 (by rfl) ⟨1353029, by rfl⟩ : syracuseStep 1804039 = 2706059) B2706059
theorem B1804047 : Blo 1803603 1804047 := bstep (se 1 (by rfl) ⟨1353035, by rfl⟩ : syracuseStep 1804047 = 2706071) B2706071
theorem B1804091 : Blo 1803603 1804091 := bstep (se 1 (by rfl) ⟨1353068, by rfl⟩ : syracuseStep 1804091 = 2706137) B2706137
theorem B75114353 : Blo 1803603 75114353 := bstep (se 2 (by rfl) ⟨28167882, by rfl⟩ : syracuseStep 75114353 = 56335765) B56335765
theorem B1804167 : Blo 1803603 1804167 := bstep (se 1 (by rfl) ⟨1353125, by rfl⟩ : syracuseStep 1804167 = 2706251) B2706251
theorem B5138311 : Blo 1803603 5138311 := bstep (se 1 (by rfl) ⟨3853733, by rfl⟩ : syracuseStep 5138311 = 7707467) B7707467
theorem B1804175 : Blo 1803603 1804175 := bstep (se 1 (by rfl) ⟨1353131, by rfl⟩ : syracuseStep 1804175 = 2706263) B2706263
theorem B1804219 : Blo 1803603 1804219 := bstep (se 1 (by rfl) ⟨1353164, by rfl⟩ : syracuseStep 1804219 = 2706329) B2706329
theorem B17336267 : Blo 1803603 17336267 := bstep (se 1 (by rfl) ⟨13002200, by rfl⟩ : syracuseStep 17336267 = 26004401) B26004401
theorem B1804295 : Blo 1803603 1804295 := bstep (se 1 (by rfl) ⟨1353221, by rfl⟩ : syracuseStep 1804295 = 2706443) B2706443
theorem B6088715 : Blo 1803603 6088715 := bstep (se 1 (by rfl) ⟨4566536, by rfl⟩ : syracuseStep 6088715 = 9133073) B9133073
theorem B2705423 : Blo 1803603 2705423 := bstep (se 1 (by rfl) ⟨2029067, by rfl⟩ : syracuseStep 2705423 = 4058135) B4058135
theorem B1804303 : Blo 1803603 1804303 := bstep (se 1 (by rfl) ⟨1353227, by rfl⟩ : syracuseStep 1804303 = 2706455) B2706455
theorem B9136151 : Blo 1803603 9136151 := bstep (se 1 (by rfl) ⟨6852113, by rfl⟩ : syracuseStep 9136151 = 13704227) B13704227
theorem B2705465 : Blo 1803603 2705465 := bstep (se 2 (by rfl) ⟨1014549, by rfl⟩ : syracuseStep 2705465 = 2029099) B2029099
theorem B1804347 : Blo 1803603 1804347 := bstep (se 1 (by rfl) ⟨1353260, by rfl⟩ : syracuseStep 1804347 = 2706521) B2706521
theorem B5564531 : Blo 1803603 5564531 := bstep (se 1 (by rfl) ⟨4173398, by rfl⟩ : syracuseStep 5564531 = 8346797) B8346797
theorem B6088823 : Blo 1803603 6088823 := bstep (se 1 (by rfl) ⟨4566617, by rfl⟩ : syracuseStep 6088823 = 9133235) B9133235
theorem B2705543 : Blo 1803603 2705543 := bstep (se 1 (by rfl) ⟨2029157, by rfl⟩ : syracuseStep 2705543 = 4058315) B4058315
theorem B1804423 : Blo 1803603 1804423 := bstep (se 1 (by rfl) ⟨1353317, by rfl⟩ : syracuseStep 1804423 = 2706635) B2706635
theorem B1804431 : Blo 1803603 1804431 := bstep (se 1 (by rfl) ⟨1353323, by rfl⟩ : syracuseStep 1804431 = 2706647) B2706647
theorem B5138585 : Blo 1803603 5138585 := bstep (se 2 (by rfl) ⟨1926969, by rfl⟩ : syracuseStep 5138585 = 3853939) B3853939
theorem B2705579 : Blo 1803603 2705579 := bstep (se 1 (by rfl) ⟨2029184, by rfl⟩ : syracuseStep 2705579 = 4058369) B4058369
theorem B1804475 : Blo 1803603 1804475 := bstep (se 1 (by rfl) ⟨1353356, by rfl⟩ : syracuseStep 1804475 = 2706713) B2706713
theorem B2705609 : Blo 1803603 2705609 := bstep (se 2 (by rfl) ⟨1014603, by rfl⟩ : syracuseStep 2705609 = 2029207) B2029207
theorem B1804551 : Blo 1803603 1804551 := bstep (se 1 (by rfl) ⟨1353413, by rfl⟩ : syracuseStep 1804551 = 2706827) B2706827
theorem B1804559 : Blo 1803603 1804559 := bstep (se 1 (by rfl) ⟨1353419, by rfl⟩ : syracuseStep 1804559 = 2706839) B2706839
theorem B2705723 : Blo 1803603 2705723 := bstep (se 1 (by rfl) ⟨2029292, by rfl⟩ : syracuseStep 2705723 = 4058585) B4058585
theorem B1804603 : Blo 1803603 1804603 := bstep (se 1 (by rfl) ⟨1353452, by rfl⟩ : syracuseStep 1804603 = 2706905) B2706905
theorem B3426619 : Blo 1803603 3426619 := bstep (se 1 (by rfl) ⟨2569964, by rfl⟩ : syracuseStep 3426619 = 5139929) B5139929
theorem B6506867 : Blo 1803603 6506867 := bstep (se 1 (by rfl) ⟨4880150, by rfl⟩ : syracuseStep 6506867 = 9760301) B9760301
theorem B2705783 : Blo 1803603 2705783 := bstep (se 1 (by rfl) ⟨2029337, by rfl⟩ : syracuseStep 2705783 = 4058675) B4058675
theorem B1804679 : Blo 1803603 1804679 := bstep (se 1 (by rfl) ⟨1353509, by rfl⟩ : syracuseStep 1804679 = 2707019) B2707019
theorem B3426695 : Blo 1803603 3426695 := bstep (se 1 (by rfl) ⟨2570021, by rfl⟩ : syracuseStep 3426695 = 5140043) B5140043
theorem B2705807 : Blo 1803603 2705807 := bstep (se 1 (by rfl) ⟨2029355, by rfl⟩ : syracuseStep 2705807 = 4058711) B4058711
theorem B1804687 : Blo 1803603 1804687 := bstep (se 1 (by rfl) ⟨1353515, by rfl⟩ : syracuseStep 1804687 = 2707031) B2707031
theorem B2705849 : Blo 1803603 2705849 := bstep (se 2 (by rfl) ⟨1014693, by rfl⟩ : syracuseStep 2705849 = 2029387) B2029387
theorem B1804731 : Blo 1803603 1804731 := bstep (se 1 (by rfl) ⟨1353548, by rfl⟩ : syracuseStep 1804731 = 2707097) B2707097
theorem B2705927 : Blo 1803603 2705927 := bstep (se 1 (by rfl) ⟨2029445, by rfl⟩ : syracuseStep 2705927 = 4058891) B4058891
theorem B1804807 : Blo 1803603 1804807 := bstep (se 1 (by rfl) ⟨1353605, by rfl⟩ : syracuseStep 1804807 = 2707211) B2707211
theorem B1927687 : Blo 1803603 1927687 := bstep (se 1 (by rfl) ⟨1445765, by rfl⟩ : syracuseStep 1927687 = 2891531) B2891531
theorem B1804815 : Blo 1803603 1804815 := bstep (se 1 (by rfl) ⟨1353611, by rfl⟩ : syracuseStep 1804815 = 2707223) B2707223
theorem B2705963 : Blo 1803603 2705963 := bstep (se 1 (by rfl) ⟨2029472, by rfl⟩ : syracuseStep 2705963 = 4058945) B4058945
theorem B32983595 : Blo 1803603 32983595 := bstep (se 1 (by rfl) ⟨24737696, by rfl⟩ : syracuseStep 32983595 = 49475393) B49475393
theorem B4876843 : Blo 1803603 4876843 := bstep (se 1 (by rfl) ⟨3657632, by rfl⟩ : syracuseStep 4876843 = 7315265) B7315265
theorem B5859883 : Blo 1803603 5859883 := bstep (se 1 (by rfl) ⟨4394912, by rfl⟩ : syracuseStep 5859883 = 8789825) B8789825
theorem B1804859 : Blo 1803603 1804859 := bstep (se 1 (by rfl) ⟨1353644, by rfl⟩ : syracuseStep 1804859 = 2707289) B2707289
theorem B2705993 : Blo 1803603 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B1804935 : Blo 1803603 1804935 := bstep (se 1 (by rfl) ⟨1353701, by rfl⟩ : syracuseStep 1804935 = 2707403) B2707403
theorem B1804943 : Blo 1803603 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B2706107 : Blo 1803603 2706107 := bstep (se 1 (by rfl) ⟨2029580, by rfl⟩ : syracuseStep 2706107 = 4059161) B4059161
theorem B1804987 : Blo 1803603 1804987 := bstep (se 1 (by rfl) ⟨1353740, by rfl⟩ : syracuseStep 1804987 = 2707481) B2707481
theorem B6089417 : Blo 1803603 6089417 := bstep (se 2 (by rfl) ⟨2283531, by rfl⟩ : syracuseStep 6089417 = 4567063) B4567063
theorem B2706167 : Blo 1803603 2706167 := bstep (se 1 (by rfl) ⟨2029625, by rfl⟩ : syracuseStep 2706167 = 4059251) B4059251
theorem B1805063 : Blo 1803603 1805063 := bstep (se 1 (by rfl) ⟨1353797, by rfl⟩ : syracuseStep 1805063 = 2707595) B2707595
theorem B5778191 : Blo 1803603 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B2706191 : Blo 1803603 2706191 := bstep (se 1 (by rfl) ⟨2029643, by rfl⟩ : syracuseStep 2706191 = 4059287) B4059287
theorem B1805071 : Blo 1803603 1805071 := bstep (se 1 (by rfl) ⟨1353803, by rfl⟩ : syracuseStep 1805071 = 2707607) B2707607
theorem B3427105 : Blo 1803603 3427105 := bstep (se 2 (by rfl) ⟨1285164, by rfl⟩ : syracuseStep 3427105 = 2570329) B2570329
theorem B2706233 : Blo 1803603 2706233 := bstep (se 2 (by rfl) ⟨1014837, by rfl⟩ : syracuseStep 2706233 = 2029675) B2029675
theorem B1805115 : Blo 1803603 1805115 := bstep (se 1 (by rfl) ⟨1353836, by rfl⟩ : syracuseStep 1805115 = 2707673) B2707673
theorem B23751539 : Blo 1803603 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B4565879 : Blo 1803603 4565879 := bstep (se 1 (by rfl) ⟨3424409, by rfl⟩ : syracuseStep 4565879 = 6848819) B6848819
theorem B2706311 : Blo 1803603 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B1805191 : Blo 1803603 1805191 := bstep (se 1 (by rfl) ⟨1353893, by rfl⟩ : syracuseStep 1805191 = 2707787) B2707787
theorem B1805199 : Blo 1803603 1805199 := bstep (se 1 (by rfl) ⟨1353899, by rfl⟩ : syracuseStep 1805199 = 2707799) B2707799
theorem B2706347 : Blo 1803603 2706347 := bstep (se 1 (by rfl) ⟨2029760, by rfl⟩ : syracuseStep 2706347 = 4059521) B4059521
theorem B1805243 : Blo 1803603 1805243 := bstep (se 1 (by rfl) ⟨1353932, by rfl⟩ : syracuseStep 1805243 = 2707865) B2707865
theorem B2706377 : Blo 1803603 2706377 := bstep (se 2 (by rfl) ⟨1014891, by rfl⟩ : syracuseStep 2706377 = 2029783) B2029783
theorem B6851537 : Blo 1803603 6851537 := bstep (se 2 (by rfl) ⟨2569326, by rfl⟩ : syracuseStep 6851537 = 5138653) B5138653
theorem B1805319 : Blo 1803603 1805319 := bstep (se 1 (by rfl) ⟨1353989, by rfl⟩ : syracuseStep 1805319 = 2707979) B2707979
theorem B1805327 : Blo 1803603 1805327 := bstep (se 1 (by rfl) ⟨1353995, by rfl⟩ : syracuseStep 1805327 = 2707991) B2707991
theorem B5565469 : Blo 1803603 5565469 := bstep (se 3 (by rfl) ⟨1043525, by rfl⟩ : syracuseStep 5565469 = 2087051) B2087051
theorem B4058171 : Blo 1803603 4058171 := bstep (se 1 (by rfl) ⟨3043628, by rfl⟩ : syracuseStep 4058171 = 6087257) B6087257
theorem B2706491 : Blo 1803603 2706491 := bstep (se 1 (by rfl) ⟨2029868, by rfl⟩ : syracuseStep 2706491 = 4059737) B4059737
theorem B1805371 : Blo 1803603 1805371 := bstep (se 1 (by rfl) ⟨1354028, by rfl⟩ : syracuseStep 1805371 = 2708057) B2708057
theorem B2706551 : Blo 1803603 2706551 := bstep (se 1 (by rfl) ⟨2029913, by rfl⟩ : syracuseStep 2706551 = 4059827) B4059827
theorem B3427447 : Blo 1803603 3427447 := bstep (se 1 (by rfl) ⟨2570585, by rfl⟩ : syracuseStep 3427447 = 5141171) B5141171
theorem B1805447 : Blo 1803603 1805447 := bstep (se 1 (by rfl) ⟨1354085, by rfl⟩ : syracuseStep 1805447 = 2708171) B2708171
theorem B2706575 : Blo 1803603 2706575 := bstep (se 1 (by rfl) ⟨2029931, by rfl⟩ : syracuseStep 2706575 = 4059863) B4059863
theorem B1805455 : Blo 1803603 1805455 := bstep (se 1 (by rfl) ⟨1354091, by rfl⟩ : syracuseStep 1805455 = 2708183) B2708183
theorem B4336787 : Blo 1803603 4336787 := bstep (se 1 (by rfl) ⟨3252590, by rfl⟩ : syracuseStep 4336787 = 6505181) B6505181
theorem B4058297 : Blo 1803603 4058297 := bstep (se 2 (by rfl) ⟨1521861, by rfl⟩ : syracuseStep 4058297 = 3043723) B3043723
theorem B2706617 : Blo 1803603 2706617 := bstep (se 2 (by rfl) ⟨1014981, by rfl⟩ : syracuseStep 2706617 = 2029963) B2029963
theorem B1805499 : Blo 1803603 1805499 := bstep (se 1 (by rfl) ⟨1354124, by rfl⟩ : syracuseStep 1805499 = 2708249) B2708249
theorem B5139713 : Blo 1803603 5139713 := bstep (se 2 (by rfl) ⟨1927392, by rfl⟩ : syracuseStep 5139713 = 3854785) B3854785
theorem B2706695 : Blo 1803603 2706695 := bstep (se 1 (by rfl) ⟨2030021, by rfl⟩ : syracuseStep 2706695 = 4060043) B4060043
theorem B1805575 : Blo 1803603 1805575 := bstep (se 1 (by rfl) ⟨1354181, by rfl⟩ : syracuseStep 1805575 = 2708363) B2708363
theorem B1805583 : Blo 1803603 1805583 := bstep (se 1 (by rfl) ⟨1354187, by rfl⟩ : syracuseStep 1805583 = 2708375) B2708375
theorem B2706731 : Blo 1803603 2706731 := bstep (se 1 (by rfl) ⟨2030048, by rfl⟩ : syracuseStep 2706731 = 4060097) B4060097
theorem B2706761 : Blo 1803603 2706761 := bstep (se 2 (by rfl) ⟨1015035, by rfl⟩ : syracuseStep 2706761 = 2030071) B2030071
theorem B6090119 : Blo 1803603 6090119 := bstep (se 1 (by rfl) ⟨4567589, by rfl⟩ : syracuseStep 6090119 = 9135179) B9135179
theorem B2706875 : Blo 1803603 2706875 := bstep (se 1 (by rfl) ⟨2030156, by rfl⟩ : syracuseStep 2706875 = 4060313) B4060313
theorem B7318993 : Blo 1803603 7318993 := bstep (se 2 (by rfl) ⟨2744622, by rfl⟩ : syracuseStep 7318993 = 5489245) B5489245
theorem B2706935 : Blo 1803603 2706935 := bstep (se 1 (by rfl) ⟨2030201, by rfl⟩ : syracuseStep 2706935 = 4060403) B4060403
theorem B14626307 : Blo 1803603 14626307 := bstep (se 1 (by rfl) ⟨10969730, by rfl⟩ : syracuseStep 14626307 = 21939461) B21939461
theorem B4058639 : Blo 1803603 4058639 := bstep (se 1 (by rfl) ⟨3043979, by rfl⟩ : syracuseStep 4058639 = 6087959) B6087959
theorem B2706959 : Blo 1803603 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B4058657 : Blo 1803603 4058657 := bstep (se 2 (by rfl) ⟨1521996, by rfl⟩ : syracuseStep 4058657 = 3043993) B3043993
theorem B2707001 : Blo 1803603 2707001 := bstep (se 2 (by rfl) ⟨1015125, by rfl⟩ : syracuseStep 2707001 = 2030251) B2030251
theorem B2707079 : Blo 1803603 2707079 := bstep (se 1 (by rfl) ⟨2030309, by rfl⟩ : syracuseStep 2707079 = 4060619) B4060619
theorem B2707115 : Blo 1803603 2707115 := bstep (se 1 (by rfl) ⟨2030336, by rfl⟩ : syracuseStep 2707115 = 4060673) B4060673
theorem B9752237 : Blo 1803603 9752237 := bstep (se 3 (by rfl) ⟨1828544, by rfl⟩ : syracuseStep 9752237 = 3657089) B3657089
theorem B2707145 : Blo 1803603 2707145 := bstep (se 2 (by rfl) ⟨1015179, by rfl⟩ : syracuseStep 2707145 = 2030359) B2030359
theorem B5140169 : Blo 1803603 5140169 := bstep (se 2 (by rfl) ⟨1927563, by rfl⟩ : syracuseStep 5140169 = 3855127) B3855127
theorem B8670977 : Blo 1803603 8670977 := bstep (se 2 (by rfl) ⟨3251616, by rfl⟩ : syracuseStep 8670977 = 6503233) B6503233
theorem B6090497 : Blo 1803603 6090497 := bstep (se 2 (by rfl) ⟨2283936, by rfl⟩ : syracuseStep 6090497 = 4567873) B4567873
theorem B2707259 : Blo 1803603 2707259 := bstep (se 1 (by rfl) ⟨2030444, by rfl⟩ : syracuseStep 2707259 = 4060889) B4060889
theorem B4058999 : Blo 1803603 4058999 := bstep (se 1 (by rfl) ⟨3044249, by rfl⟩ : syracuseStep 4058999 = 6088499) B6088499
theorem B2707319 : Blo 1803603 2707319 := bstep (se 1 (by rfl) ⟨2030489, by rfl⟩ : syracuseStep 2707319 = 4060979) B4060979
theorem B2707343 : Blo 1803603 2707343 := bstep (se 1 (by rfl) ⟨2030507, by rfl⟩ : syracuseStep 2707343 = 4061015) B4061015
theorem B2707385 : Blo 1803603 2707385 := bstep (se 2 (by rfl) ⟨1015269, by rfl⟩ : syracuseStep 2707385 = 2030539) B2030539
theorem B2314171 : Blo 1803603 2314171 := bstep (se 1 (by rfl) ⟨1735628, by rfl⟩ : syracuseStep 2314171 = 3471257) B3471257
theorem B9760733 : Blo 1803603 9760733 := bstep (se 3 (by rfl) ⟨1830137, by rfl⟩ : syracuseStep 9760733 = 3660275) B3660275
theorem B2568199 : Blo 1803603 2568199 := bstep (se 1 (by rfl) ⟨1926149, by rfl⟩ : syracuseStep 2568199 = 3852299) B3852299
theorem B2707463 : Blo 1803603 2707463 := bstep (se 1 (by rfl) ⟨2030597, by rfl⟩ : syracuseStep 2707463 = 4061195) B4061195
theorem B4059179 : Blo 1803603 4059179 := bstep (se 1 (by rfl) ⟨3044384, by rfl⟩ : syracuseStep 4059179 = 6088769) B6088769
theorem B2707499 : Blo 1803603 2707499 := bstep (se 1 (by rfl) ⟨2030624, by rfl⟩ : syracuseStep 2707499 = 4061249) B4061249
theorem B26005549 : Blo 1803603 26005549 := bstep (se 3 (by rfl) ⟨4876040, by rfl⟩ : syracuseStep 26005549 = 9752081) B9752081
theorem B27775021 : Blo 1803603 27775021 := bstep (se 3 (by rfl) ⟨5207816, by rfl⟩ : syracuseStep 27775021 = 10415633) B10415633
theorem B2707529 : Blo 1803603 2707529 := bstep (se 2 (by rfl) ⟨1015323, by rfl⟩ : syracuseStep 2707529 = 2030647) B2030647
theorem B4567175 : Blo 1803603 4567175 := bstep (se 1 (by rfl) ⟨3425381, by rfl⟩ : syracuseStep 4567175 = 6850763) B6850763
theorem B4567225 : Blo 1803603 4567225 := bstep (se 2 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 4567225 = 3425419) B3425419
theorem B2707643 : Blo 1803603 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B3854537 : Blo 1803603 3854537 := bstep (se 2 (by rfl) ⟨1445451, by rfl⟩ : syracuseStep 3854537 = 2890903) B2890903
theorem B2707703 : Blo 1803603 2707703 := bstep (se 1 (by rfl) ⟨2030777, by rfl⟩ : syracuseStep 2707703 = 4061555) B4061555
theorem B2707727 : Blo 1803603 2707727 := bstep (se 1 (by rfl) ⟨2030795, by rfl⟩ : syracuseStep 2707727 = 4061591) B4061591
theorem B2707769 : Blo 1803603 2707769 := bstep (se 2 (by rfl) ⟨1015413, by rfl⟩ : syracuseStep 2707769 = 2030827) B2030827
theorem B3043703 : Blo 1803603 3043703 := bstep (se 1 (by rfl) ⟨2282777, by rfl⟩ : syracuseStep 3043703 = 4565555) B4565555
theorem B21950851 : Blo 1803603 21950851 := bstep (se 1 (by rfl) ⟨16463138, by rfl⟩ : syracuseStep 21950851 = 32926277) B32926277
theorem B2707847 : Blo 1803603 2707847 := bstep (se 1 (by rfl) ⟨2030885, by rfl⟩ : syracuseStep 2707847 = 4061771) B4061771
theorem B4059539 : Blo 1803603 4059539 := bstep (se 1 (by rfl) ⟨3044654, by rfl⟩ : syracuseStep 4059539 = 6089309) B6089309
theorem B2707883 : Blo 1803603 2707883 := bstep (se 1 (by rfl) ⟨2030912, by rfl⟩ : syracuseStep 2707883 = 4061825) B4061825
theorem B4059593 : Blo 1803603 4059593 := bstep (se 2 (by rfl) ⟨1522347, by rfl⟩ : syracuseStep 4059593 = 3044695) B3044695
theorem B2707913 : Blo 1803603 2707913 := bstep (se 2 (by rfl) ⟨1015467, by rfl⟩ : syracuseStep 2707913 = 2030935) B2030935
theorem B4117025 : Blo 1803603 4117025 := bstep (se 2 (by rfl) ⟨1543884, by rfl⟩ : syracuseStep 4117025 = 3087769) B3087769
theorem B6091307 : Blo 1803603 6091307 := bstep (se 1 (by rfl) ⟨4568480, by rfl⟩ : syracuseStep 6091307 = 9136961) B9136961
theorem B2568763 : Blo 1803603 2568763 := bstep (se 1 (by rfl) ⟨1926572, by rfl⟩ : syracuseStep 2568763 = 3853145) B3853145
theorem B2708027 : Blo 1803603 2708027 := bstep (se 1 (by rfl) ⟨2031020, by rfl⟩ : syracuseStep 2708027 = 4062041) B4062041
theorem B13898317 : Blo 1803603 13898317 := bstep (se 3 (by rfl) ⟨2605934, by rfl⟩ : syracuseStep 13898317 = 5211869) B5211869
theorem B6853207 : Blo 1803603 6853207 := bstep (se 1 (by rfl) ⟨5139905, by rfl⟩ : syracuseStep 6853207 = 10279811) B10279811
theorem B2708087 : Blo 1803603 2708087 := bstep (se 1 (by rfl) ⟨2031065, by rfl⟩ : syracuseStep 2708087 = 4062131) B4062131
theorem B2708111 : Blo 1803603 2708111 := bstep (se 1 (by rfl) ⟨2031083, by rfl⟩ : syracuseStep 2708111 = 4062167) B4062167
theorem B2708153 : Blo 1803603 2708153 := bstep (se 2 (by rfl) ⟨1015557, by rfl⟩ : syracuseStep 2708153 = 2031115) B2031115
theorem B7041773 : Blo 1803603 7041773 := bstep (se 3 (by rfl) ⟨1320332, by rfl⟩ : syracuseStep 7041773 = 2640665) B2640665
theorem B2708231 : Blo 1803603 2708231 := bstep (se 1 (by rfl) ⟨2031173, by rfl⟩ : syracuseStep 2708231 = 4062347) B4062347
theorem B4567823 : Blo 1803603 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B2708267 : Blo 1803603 2708267 := bstep (se 1 (by rfl) ⟨2031200, by rfl⟩ : syracuseStep 2708267 = 4062401) B4062401
theorem B3044155 : Blo 1803603 3044155 := bstep (se 1 (by rfl) ⟨2283116, by rfl⟩ : syracuseStep 3044155 = 4566233) B4566233
theorem B2708297 : Blo 1803603 2708297 := bstep (se 2 (by rfl) ⟨1015611, by rfl⟩ : syracuseStep 2708297 = 2031223) B2031223
theorem B6853511 : Blo 1803603 6853511 := bstep (se 1 (by rfl) ⟨5140133, by rfl⟩ : syracuseStep 6853511 = 10280267) B10280267
theorem B7320455 : Blo 1803603 7320455 := bstep (se 1 (by rfl) ⟨5490341, by rfl⟩ : syracuseStep 7320455 = 10980683) B10980683
theorem B3855289 : Blo 1803603 3855289 := bstep (se 2 (by rfl) ⟨1445733, by rfl⟩ : syracuseStep 3855289 = 2891467) B2891467
theorem B5641145 : Blo 1803603 5641145 := bstep (se 2 (by rfl) ⟨2115429, by rfl⟩ : syracuseStep 5641145 = 4230859) B4230859
theorem B3044297 : Blo 1803603 3044297 := bstep (se 2 (by rfl) ⟨1141611, by rfl⟩ : syracuseStep 3044297 = 2283223) B2283223
theorem B3707849 : Blo 1803603 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B9139229 : Blo 1803603 9139229 := bstep (se 3 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 9139229 = 3427211) B3427211
theorem B7812139 : Blo 1803603 7812139 := bstep (se 1 (by rfl) ⟨5859104, by rfl⟩ : syracuseStep 7812139 = 11718209) B11718209
theorem B6853693 : Blo 1803603 6853693 := bstep (se 3 (by rfl) ⟨1285067, by rfl⟩ : syracuseStep 6853693 = 2570135) B2570135
theorem B4060295 : Blo 1803603 4060295 := bstep (se 1 (by rfl) ⟨3045221, by rfl⟩ : syracuseStep 4060295 = 6090443) B6090443
theorem B4060475 : Blo 1803603 4060475 := bstep (se 1 (by rfl) ⟨3045356, by rfl⟩ : syracuseStep 4060475 = 6090713) B6090713
theorem B11130247 : Blo 1803603 11130247 := bstep (se 1 (by rfl) ⟨8347685, by rfl⟩ : syracuseStep 11130247 = 16695371) B16695371
theorem B4060601 : Blo 1803603 4060601 := bstep (se 2 (by rfl) ⟨1522725, by rfl⟩ : syracuseStep 4060601 = 3045451) B3045451
theorem B2569657 : Blo 1803603 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B4568521 : Blo 1803603 4568521 := bstep (se 2 (by rfl) ⟨1713195, by rfl⟩ : syracuseStep 4568521 = 3426391) B3426391
theorem B10278353 : Blo 1803603 10278353 := bstep (se 2 (by rfl) ⟨3854382, by rfl⟩ : syracuseStep 10278353 = 7708765) B7708765
theorem B9139715 : Blo 1803603 9139715 := bstep (se 1 (by rfl) ⟨6854786, by rfl⟩ : syracuseStep 9139715 = 13709573) B13709573
theorem B2029063 : Blo 1803603 2029063 := bstep (se 1 (by rfl) ⟨1521797, by rfl⟩ : syracuseStep 2029063 = 3043595) B3043595
theorem B9754141 : Blo 1803603 9754141 := bstep (se 3 (by rfl) ⟨1828901, by rfl⟩ : syracuseStep 9754141 = 3657803) B3657803
theorem B2889275 : Blo 1803603 2889275 := bstep (se 1 (by rfl) ⟨2166956, by rfl⟩ : syracuseStep 2889275 = 4333913) B4333913
theorem B4568663 : Blo 1803603 4568663 := bstep (se 1 (by rfl) ⟨3426497, by rfl⟩ : syracuseStep 4568663 = 6852995) B6852995
theorem B3044999 : Blo 1803603 3044999 := bstep (se 1 (by rfl) ⟨2283749, by rfl⟩ : syracuseStep 3044999 = 4567499) B4567499
theorem B2029243 : Blo 1803603 2029243 := bstep (se 1 (by rfl) ⟨1521932, by rfl⟩ : syracuseStep 2029243 = 3043865) B3043865
theorem B9131777 : Blo 1803603 9131777 := bstep (se 2 (by rfl) ⟨3424416, by rfl⟩ : syracuseStep 9131777 = 6848833) B6848833
theorem B1980175 : Blo 1803603 1980175 := bstep (se 1 (by rfl) ⟨1485131, by rfl⟩ : syracuseStep 1980175 = 2970263) B2970263
theorem B4060943 : Blo 1803603 4060943 := bstep (se 1 (by rfl) ⟨3045707, by rfl⟩ : syracuseStep 4060943 = 6091415) B6091415
theorem B4060961 : Blo 1803603 4060961 := bstep (se 2 (by rfl) ⟨1522860, by rfl⟩ : syracuseStep 4060961 = 3045721) B3045721
theorem B16455473 : Blo 1803603 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B6092603 : Blo 1803603 6092603 := bstep (se 1 (by rfl) ⟨4569452, by rfl⟩ : syracuseStep 6092603 = 9138905) B9138905
theorem B5781395 : Blo 1803603 5781395 := bstep (se 1 (by rfl) ⟨4336046, by rfl⟩ : syracuseStep 5781395 = 8672093) B8672093
theorem B10278809 : Blo 1803603 10278809 := bstep (se 2 (by rfl) ⟨3854553, by rfl⟩ : syracuseStep 10278809 = 7709107) B7709107
theorem B19519385 : Blo 1803603 19519385 := bstep (se 2 (by rfl) ⟨7319769, by rfl⟩ : syracuseStep 19519385 = 14639539) B14639539
theorem B8230841 : Blo 1803603 8230841 := bstep (se 2 (by rfl) ⟨3086565, by rfl⟩ : syracuseStep 8230841 = 6173131) B6173131
theorem B13703255 : Blo 1803603 13703255 := bstep (se 1 (by rfl) ⟨10277441, by rfl⟩ : syracuseStep 13703255 = 20554883) B20554883
theorem B4061303 : Blo 1803603 4061303 := bstep (se 1 (by rfl) ⟨3045977, by rfl⟩ : syracuseStep 4061303 = 6091955) B6091955
theorem B2029711 : Blo 1803603 2029711 := bstep (se 1 (by rfl) ⟨1522283, by rfl⟩ : syracuseStep 2029711 = 3044567) B3044567
theorem B3045647 : Blo 1803603 3045647 := bstep (se 1 (by rfl) ⟨2284235, by rfl⟩ : syracuseStep 3045647 = 4568471) B4568471
theorem B6093089 : Blo 1803603 6093089 := bstep (se 2 (by rfl) ⟨2284908, by rfl⟩ : syracuseStep 6093089 = 4569817) B4569817
theorem B4061483 : Blo 1803603 4061483 := bstep (se 1 (by rfl) ⟨3046112, by rfl⟩ : syracuseStep 4061483 = 6092225) B6092225
theorem B7420295 : Blo 1803603 7420295 := bstep (se 1 (by rfl) ⟨5565221, by rfl⟩ : syracuseStep 7420295 = 11130443) B11130443
theorem B7813529 : Blo 1803603 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B3471817 : Blo 1803603 3471817 := bstep (se 2 (by rfl) ⟨1301931, by rfl⟩ : syracuseStep 3471817 = 2603863) B2603863
theorem B8673745 : Blo 1803603 8673745 := bstep (se 2 (by rfl) ⟨3252654, by rfl⟩ : syracuseStep 8673745 = 6505309) B6505309
theorem B9132587 : Blo 1803603 9132587 := bstep (se 1 (by rfl) ⟨6849440, by rfl⟩ : syracuseStep 9132587 = 13698881) B13698881
theorem B2030215 : Blo 1803603 2030215 := bstep (se 1 (by rfl) ⟨1522661, by rfl⟩ : syracuseStep 2030215 = 3045323) B3045323
theorem B4061843 : Blo 1803603 4061843 := bstep (se 1 (by rfl) ⟨3046382, by rfl⟩ : syracuseStep 4061843 = 6092765) B6092765
theorem B2931385 : Blo 1803603 2931385 := bstep (se 2 (by rfl) ⟨1099269, by rfl⟩ : syracuseStep 2931385 = 2198539) B2198539
theorem B4061897 : Blo 1803603 4061897 := bstep (se 2 (by rfl) ⟨1523211, by rfl⟩ : syracuseStep 4061897 = 3046423) B3046423
theorem B6855425 : Blo 1803603 6855425 := bstep (se 2 (by rfl) ⟨2570784, by rfl⟩ : syracuseStep 6855425 = 5141569) B5141569
theorem B3046187 : Blo 1803603 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B2030395 : Blo 1803603 2030395 := bstep (se 1 (by rfl) ⟨1522796, by rfl⟩ : syracuseStep 2030395 = 3045593) B3045593
theorem B20560715 : Blo 1803603 20560715 := bstep (se 1 (by rfl) ⟨15420536, by rfl⟩ : syracuseStep 20560715 = 30841073) B30841073
theorem B6093683 : Blo 1803603 6093683 := bstep (se 1 (by rfl) ⟨4570262, by rfl⟩ : syracuseStep 6093683 = 9140525) B9140525
theorem B2440265 : Blo 1803603 2440265 := bstep (se 2 (by rfl) ⟨915099, by rfl⟩ : syracuseStep 2440265 = 1830199) B1830199
theorem B17341613 : Blo 1803603 17341613 := bstep (se 3 (by rfl) ⟨3251552, by rfl⟩ : syracuseStep 17341613 = 6503105) B6503105
theorem B3046585 : Blo 1803603 3046585 := bstep (se 2 (by rfl) ⟨1142469, by rfl⟩ : syracuseStep 3046585 = 2284939) B2284939
theorem B2030863 : Blo 1803603 2030863 := bstep (se 1 (by rfl) ⟨1523147, by rfl⟩ : syracuseStep 2030863 = 3046295) B3046295
theorem B2284843 : Blo 1803603 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B4062599 : Blo 1803603 4062599 := bstep (se 1 (by rfl) ⟨3046949, by rfl⟩ : syracuseStep 4062599 = 6093899) B6093899
theorem B10272203 : Blo 1803603 10272203 := bstep (se 1 (by rfl) ⟨7704152, by rfl⟩ : syracuseStep 10272203 = 15408305) B15408305
theorem B8347223 : Blo 1803603 8347223 := bstep (se 1 (by rfl) ⟨6260417, by rfl⟩ : syracuseStep 8347223 = 12520835) B12520835
theorem B36601573 : Blo 1803603 36601573 := bstep (se 4 (by rfl) ⟨3431397, by rfl⟩ : syracuseStep 36601573 = 6862795) B6862795
theorem B9756389 : Blo 1803603 9756389 := bstep (se 4 (by rfl) ⟨914661, by rfl⟩ : syracuseStep 9756389 = 1829323) B1829323
theorem B34676525 : Blo 1803603 34676525 := bstep (se 3 (by rfl) ⟨6501848, by rfl⟩ : syracuseStep 34676525 = 13003697) B13003697
theorem B9133883 : Blo 1803603 9133883 := bstep (se 1 (by rfl) ⟨6850412, by rfl⟩ : syracuseStep 9133883 = 13700825) B13700825
theorem B8675207 : Blo 1803603 8675207 := bstep (se 1 (by rfl) ⟨6506405, by rfl⟩ : syracuseStep 8675207 = 13012811) B13012811
theorem B10977227 : Blo 1803603 10977227 := bstep (se 1 (by rfl) ⟨8232920, by rfl⟩ : syracuseStep 10977227 = 16465841) B16465841
theorem B9134045 : Blo 1803603 9134045 := bstep (se 3 (by rfl) ⟨1712633, by rfl⟩ : syracuseStep 9134045 = 3425267) B3425267
theorem B12353543 : Blo 1803603 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B3424265 : Blo 1803603 3424265 := bstep (se 2 (by rfl) ⟨1284099, by rfl⟩ : syracuseStep 3424265 = 2568199) B2568199
theorem B3424295 : Blo 1803603 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B19513507 : Blo 1803603 19513507 := bstep (se 1 (by rfl) ⟨14635130, by rfl⟩ : syracuseStep 19513507 = 29270261) B29270261
theorem B31252709 : Blo 1803603 31252709 := bstep (se 4 (by rfl) ⟨2929941, by rfl⟩ : syracuseStep 31252709 = 5859883) B5859883
theorem B4629089 : Blo 1803603 4629089 := bstep (se 2 (by rfl) ⟨1735908, by rfl⟩ : syracuseStep 4629089 = 3471817) B3471817
theorem B3760763 : Blo 1803603 3760763 := bstep (se 1 (by rfl) ⟨2820572, by rfl⟩ : syracuseStep 3760763 = 5641145) B5641145
theorem B3424979 : Blo 1803603 3424979 := bstep (se 1 (by rfl) ⟨2568734, by rfl⟩ : syracuseStep 3424979 = 5137469) B5137469
theorem B3425017 : Blo 1803603 3425017 := bstep (se 2 (by rfl) ⟨1284381, by rfl⟩ : syracuseStep 3425017 = 2568763) B2568763
theorem B18531089 : Blo 1803603 18531089 := bstep (se 2 (by rfl) ⟨6949158, by rfl⟩ : syracuseStep 18531089 = 13898317) B13898317
theorem B3908513 : Blo 1803603 3908513 := bstep (se 2 (by rfl) ⟨1465692, by rfl⟩ : syracuseStep 3908513 = 2931385) B2931385
theorem B5211143 : Blo 1803603 5211143 := bstep (se 1 (by rfl) ⟨3908357, by rfl⟩ : syracuseStep 5211143 = 7816715) B7816715
theorem B6849593 : Blo 1803603 6849593 := bstep (se 2 (by rfl) ⟨2568597, by rfl⟩ : syracuseStep 6849593 = 5137195) B5137195
theorem B6087851 : Blo 1803603 6087851 := bstep (se 1 (by rfl) ⟨4565888, by rfl⟩ : syracuseStep 6087851 = 9131777) B9131777
theorem B23119019 : Blo 1803603 23119019 := bstep (se 1 (by rfl) ⟨17339264, by rfl⟩ : syracuseStep 23119019 = 34678529) B34678529
theorem B10970315 : Blo 1803603 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B1803615 : Blo 1803603 1803615 := bstep (se 1 (by rfl) ⟨1352711, by rfl⟩ : syracuseStep 1803615 = 2705423) B2705423
theorem B1803643 : Blo 1803603 1803643 := bstep (se 1 (by rfl) ⟨1352732, by rfl⟩ : syracuseStep 1803643 = 2705465) B2705465
theorem B9135503 : Blo 1803603 9135503 := bstep (se 1 (by rfl) ⟨6851627, by rfl⟩ : syracuseStep 9135503 = 13703255) B13703255
theorem B10978733 : Blo 1803603 10978733 := bstep (se 3 (by rfl) ⟨2058512, by rfl⟩ : syracuseStep 10978733 = 4117025) B4117025
theorem B1803695 : Blo 1803603 1803695 := bstep (se 1 (by rfl) ⟨1352771, by rfl⟩ : syracuseStep 1803695 = 2705543) B2705543
theorem B3425723 : Blo 1803603 3425723 := bstep (se 1 (by rfl) ⟨2569292, by rfl⟩ : syracuseStep 3425723 = 5138585) B5138585
theorem B1803719 : Blo 1803603 1803719 := bstep (se 1 (by rfl) ⟨1352789, by rfl⟩ : syracuseStep 1803719 = 2705579) B2705579
theorem B1803739 : Blo 1803603 1803739 := bstep (se 1 (by rfl) ⟨1352804, by rfl⟩ : syracuseStep 1803739 = 2705609) B2705609
theorem B1803815 : Blo 1803603 1803815 := bstep (se 1 (by rfl) ⟨1352861, by rfl⟩ : syracuseStep 1803815 = 2705723) B2705723
theorem B22259261 : Blo 1803603 22259261 := bstep (se 3 (by rfl) ⟨4173611, by rfl⟩ : syracuseStep 22259261 = 8347223) B8347223
theorem B1803855 : Blo 1803603 1803855 := bstep (se 1 (by rfl) ⟨1352891, by rfl⟩ : syracuseStep 1803855 = 2705783) B2705783
theorem B1803871 : Blo 1803603 1803871 := bstep (se 1 (by rfl) ⟨1352903, by rfl⟩ : syracuseStep 1803871 = 2705807) B2705807
theorem B1803899 : Blo 1803603 1803899 := bstep (se 1 (by rfl) ⟨1352924, by rfl⟩ : syracuseStep 1803899 = 2705849) B2705849
theorem B1803951 : Blo 1803603 1803951 := bstep (se 1 (by rfl) ⟨1352963, by rfl⟩ : syracuseStep 1803951 = 2705927) B2705927
theorem B6088391 : Blo 1803603 6088391 := bstep (se 1 (by rfl) ⟨4566293, by rfl⟩ : syracuseStep 6088391 = 9132587) B9132587
theorem B1803975 : Blo 1803603 1803975 := bstep (se 1 (by rfl) ⟨1352981, by rfl⟩ : syracuseStep 1803975 = 2705963) B2705963
theorem B21989063 : Blo 1803603 21989063 := bstep (se 1 (by rfl) ⟨16491797, by rfl⟩ : syracuseStep 21989063 = 32983595) B32983595
theorem B1803995 : Blo 1803603 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B1804071 : Blo 1803603 1804071 := bstep (se 1 (by rfl) ⟨1353053, by rfl⟩ : syracuseStep 1804071 = 2706107) B2706107
theorem B1804111 : Blo 1803603 1804111 := bstep (se 1 (by rfl) ⟨1353083, by rfl⟩ : syracuseStep 1804111 = 2706167) B2706167
theorem B3852127 : Blo 1803603 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B1804127 : Blo 1803603 1804127 := bstep (se 1 (by rfl) ⟨1353095, by rfl⟩ : syracuseStep 1804127 = 2706191) B2706191
theorem B13002605 : Blo 1803603 13002605 := bstep (se 3 (by rfl) ⟨2437988, by rfl⟩ : syracuseStep 13002605 = 4875977) B4875977
theorem B1804155 : Blo 1803603 1804155 := bstep (se 1 (by rfl) ⟨1353116, by rfl⟩ : syracuseStep 1804155 = 2706233) B2706233
theorem B13707143 : Blo 1803603 13707143 := bstep (se 1 (by rfl) ⟨10280357, by rfl⟩ : syracuseStep 13707143 = 20560715) B20560715
theorem B3426209 : Blo 1803603 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B1804207 : Blo 1803603 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B9758657 : Blo 1803603 9758657 := bstep (se 2 (by rfl) ⟨3659496, by rfl⟩ : syracuseStep 9758657 = 7318993) B7318993
theorem B1804231 : Blo 1803603 1804231 := bstep (se 1 (by rfl) ⟨1353173, by rfl⟩ : syracuseStep 1804231 = 2706347) B2706347
theorem B18778061 : Blo 1803603 18778061 := bstep (se 3 (by rfl) ⟨3520886, by rfl⟩ : syracuseStep 18778061 = 7041773) B7041773
theorem B1804251 : Blo 1803603 1804251 := bstep (se 1 (by rfl) ⟨1353188, by rfl⟩ : syracuseStep 1804251 = 2706377) B2706377
theorem B2705417 : Blo 1803603 2705417 := bstep (se 2 (by rfl) ⟨1014531, by rfl⟩ : syracuseStep 2705417 = 2029063) B2029063
theorem B2705447 : Blo 1803603 2705447 := bstep (se 1 (by rfl) ⟨2029085, by rfl⟩ : syracuseStep 2705447 = 4058171) B4058171
theorem B1804327 : Blo 1803603 1804327 := bstep (se 1 (by rfl) ⟨1353245, by rfl⟩ : syracuseStep 1804327 = 2706491) B2706491
theorem B1804367 : Blo 1803603 1804367 := bstep (se 1 (by rfl) ⟨1353275, by rfl⟩ : syracuseStep 1804367 = 2706551) B2706551
theorem B1804383 : Blo 1803603 1804383 := bstep (se 1 (by rfl) ⟨1353287, by rfl⟩ : syracuseStep 1804383 = 2706575) B2706575
theorem B11561075 : Blo 1803603 11561075 := bstep (se 1 (by rfl) ⟨8670806, by rfl⟩ : syracuseStep 11561075 = 17341613) B17341613
theorem B2705531 : Blo 1803603 2705531 := bstep (se 1 (by rfl) ⟨2029148, by rfl⟩ : syracuseStep 2705531 = 4058297) B4058297
theorem B1804411 : Blo 1803603 1804411 := bstep (se 1 (by rfl) ⟨1353308, by rfl⟩ : syracuseStep 1804411 = 2706617) B2706617
theorem B1804463 : Blo 1803603 1804463 := bstep (se 1 (by rfl) ⟨1353347, by rfl⟩ : syracuseStep 1804463 = 2706695) B2706695
theorem B3426475 : Blo 1803603 3426475 := bstep (se 1 (by rfl) ⟨2569856, by rfl⟩ : syracuseStep 3426475 = 5139713) B5139713
theorem B1804487 : Blo 1803603 1804487 := bstep (se 1 (by rfl) ⟨1353365, by rfl⟩ : syracuseStep 1804487 = 2706731) B2706731
theorem B1804507 : Blo 1803603 1804507 := bstep (se 1 (by rfl) ⟨1353380, by rfl⟩ : syracuseStep 1804507 = 2706761) B2706761
theorem B2705657 : Blo 1803603 2705657 := bstep (se 2 (by rfl) ⟨1014621, by rfl⟩ : syracuseStep 2705657 = 2029243) B2029243
theorem B1804583 : Blo 1803603 1804583 := bstep (se 1 (by rfl) ⟨1353437, by rfl⟩ : syracuseStep 1804583 = 2706875) B2706875
theorem B48802097 : Blo 1803603 48802097 := bstep (se 2 (by rfl) ⟨18300786, by rfl⟩ : syracuseStep 48802097 = 36601573) B36601573
theorem B1804623 : Blo 1803603 1804623 := bstep (se 1 (by rfl) ⟨1353467, by rfl⟩ : syracuseStep 1804623 = 2706935) B2706935
theorem B9750871 : Blo 1803603 9750871 := bstep (se 1 (by rfl) ⟨7313153, by rfl⟩ : syracuseStep 9750871 = 14626307) B14626307
theorem B2705759 : Blo 1803603 2705759 := bstep (se 1 (by rfl) ⟨2029319, by rfl⟩ : syracuseStep 2705759 = 4058639) B4058639
theorem B1804639 : Blo 1803603 1804639 := bstep (se 1 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 1804639 = 2706959) B2706959
theorem B2640233 : Blo 1803603 2640233 := bstep (se 2 (by rfl) ⟨990087, by rfl⟩ : syracuseStep 2640233 = 1980175) B1980175
theorem B2705771 : Blo 1803603 2705771 := bstep (se 1 (by rfl) ⟨2029328, by rfl⟩ : syracuseStep 2705771 = 4058657) B4058657
theorem B1804667 : Blo 1803603 1804667 := bstep (se 1 (by rfl) ⟨1353500, by rfl⟩ : syracuseStep 1804667 = 2707001) B2707001
theorem B1804719 : Blo 1803603 1804719 := bstep (se 1 (by rfl) ⟨1353539, by rfl⟩ : syracuseStep 1804719 = 2707079) B2707079
theorem B1804743 : Blo 1803603 1804743 := bstep (se 1 (by rfl) ⟨1353557, by rfl⟩ : syracuseStep 1804743 = 2707115) B2707115
theorem B1804763 : Blo 1803603 1804763 := bstep (se 1 (by rfl) ⟨1353572, by rfl⟩ : syracuseStep 1804763 = 2707145) B2707145
theorem B3426779 : Blo 1803603 3426779 := bstep (se 1 (by rfl) ⟨2570084, by rfl⟩ : syracuseStep 3426779 = 5140169) B5140169
theorem B6851081 : Blo 1803603 6851081 := bstep (se 2 (by rfl) ⟨2569155, by rfl⟩ : syracuseStep 6851081 = 5138311) B5138311
theorem B6089255 : Blo 1803603 6089255 := bstep (se 1 (by rfl) ⟨4566941, by rfl⟩ : syracuseStep 6089255 = 9133883) B9133883
theorem B1804839 : Blo 1803603 1804839 := bstep (se 1 (by rfl) ⟨1353629, by rfl⟩ : syracuseStep 1804839 = 2707259) B2707259
theorem B2705999 : Blo 1803603 2705999 := bstep (se 1 (by rfl) ⟨2029499, by rfl⟩ : syracuseStep 2705999 = 4058999) B4058999
theorem B1804879 : Blo 1803603 1804879 := bstep (se 1 (by rfl) ⟨1353659, by rfl⟩ : syracuseStep 1804879 = 2707319) B2707319
theorem B1804895 : Blo 1803603 1804895 := bstep (se 1 (by rfl) ⟨1353671, by rfl⟩ : syracuseStep 1804895 = 2707343) B2707343
theorem B1804923 : Blo 1803603 1804923 := bstep (se 1 (by rfl) ⟨1353692, by rfl⟩ : syracuseStep 1804923 = 2707385) B2707385
theorem B7318151 : Blo 1803603 7318151 := bstep (se 1 (by rfl) ⟨5488613, by rfl⟩ : syracuseStep 7318151 = 10977227) B10977227
theorem B6089363 : Blo 1803603 6089363 := bstep (se 1 (by rfl) ⟨4567022, by rfl⟩ : syracuseStep 6089363 = 9134045) B9134045
theorem B6507155 : Blo 1803603 6507155 := bstep (se 1 (by rfl) ⟨4880366, by rfl⟩ : syracuseStep 6507155 = 9760733) B9760733
theorem B1804975 : Blo 1803603 1804975 := bstep (se 1 (by rfl) ⟨1353731, by rfl⟩ : syracuseStep 1804975 = 2707463) B2707463
theorem B2706119 : Blo 1803603 2706119 := bstep (se 1 (by rfl) ⟨2029589, by rfl⟩ : syracuseStep 2706119 = 4059179) B4059179
theorem B1804999 : Blo 1803603 1804999 := bstep (se 1 (by rfl) ⟨1353749, by rfl⟩ : syracuseStep 1804999 = 2707499) B2707499
theorem B12511955 : Blo 1803603 12511955 := bstep (se 1 (by rfl) ⟨9383966, by rfl⟩ : syracuseStep 12511955 = 18767933) B18767933
theorem B1805019 : Blo 1803603 1805019 := bstep (se 1 (by rfl) ⟨1353764, by rfl⟩ : syracuseStep 1805019 = 2707529) B2707529
theorem B1805095 : Blo 1803603 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B1805135 : Blo 1803603 1805135 := bstep (se 1 (by rfl) ⟨1353851, by rfl⟩ : syracuseStep 1805135 = 2707703) B2707703
theorem B1805151 : Blo 1803603 1805151 := bstep (se 1 (by rfl) ⟨1353863, by rfl⟩ : syracuseStep 1805151 = 2707727) B2707727
theorem B2706281 : Blo 1803603 2706281 := bstep (se 2 (by rfl) ⟨1014855, by rfl⟩ : syracuseStep 2706281 = 2029711) B2029711
theorem B6089579 : Blo 1803603 6089579 := bstep (se 1 (by rfl) ⟨4567184, by rfl⟩ : syracuseStep 6089579 = 9134369) B9134369
theorem B6507373 : Blo 1803603 6507373 := bstep (se 3 (by rfl) ⟨1220132, by rfl⟩ : syracuseStep 6507373 = 2440265) B2440265
theorem B1805179 : Blo 1803603 1805179 := bstep (se 1 (by rfl) ⟨1353884, by rfl⟩ : syracuseStep 1805179 = 2707769) B2707769
theorem B6089633 : Blo 1803603 6089633 := bstep (se 2 (by rfl) ⟨2283612, by rfl⟩ : syracuseStep 6089633 = 4567225) B4567225
theorem B1805231 : Blo 1803603 1805231 := bstep (se 1 (by rfl) ⟨1353923, by rfl⟩ : syracuseStep 1805231 = 2707847) B2707847
theorem B2706359 : Blo 1803603 2706359 := bstep (se 1 (by rfl) ⟨2029769, by rfl⟩ : syracuseStep 2706359 = 4059539) B4059539
theorem B1805255 : Blo 1803603 1805255 := bstep (se 1 (by rfl) ⟨1353941, by rfl⟩ : syracuseStep 1805255 = 2707883) B2707883
theorem B2706395 : Blo 1803603 2706395 := bstep (se 1 (by rfl) ⟨2029796, by rfl⟩ : syracuseStep 2706395 = 4059593) B4059593
theorem B1805275 : Blo 1803603 1805275 := bstep (se 1 (by rfl) ⟨1353956, by rfl⟩ : syracuseStep 1805275 = 2707913) B2707913
theorem B1805351 : Blo 1803603 1805351 := bstep (se 1 (by rfl) ⟨1354013, by rfl⟩ : syracuseStep 1805351 = 2708027) B2708027
theorem B1805391 : Blo 1803603 1805391 := bstep (se 1 (by rfl) ⟨1354043, by rfl⟩ : syracuseStep 1805391 = 2708087) B2708087
theorem B1805407 : Blo 1803603 1805407 := bstep (se 1 (by rfl) ⟨1354055, by rfl⟩ : syracuseStep 1805407 = 2708111) B2708111
theorem B1805435 : Blo 1803603 1805435 := bstep (se 1 (by rfl) ⟨1354076, by rfl⟩ : syracuseStep 1805435 = 2708153) B2708153
theorem B1805487 : Blo 1803603 1805487 := bstep (se 1 (by rfl) ⟨1354115, by rfl⟩ : syracuseStep 1805487 = 2708231) B2708231
theorem B1805511 : Blo 1803603 1805511 := bstep (se 1 (by rfl) ⟨1354133, by rfl⟩ : syracuseStep 1805511 = 2708267) B2708267
theorem B1805531 : Blo 1803603 1805531 := bstep (se 1 (by rfl) ⟨1354148, by rfl⟩ : syracuseStep 1805531 = 2708297) B2708297
theorem B4566415 : Blo 1803603 4566415 := bstep (se 1 (by rfl) ⟨3424811, by rfl⟩ : syracuseStep 4566415 = 6849623) B6849623
theorem B2706863 : Blo 1803603 2706863 := bstep (se 1 (by rfl) ⟨2030147, by rfl⟩ : syracuseStep 2706863 = 4060295) B4060295
theorem B9137609 : Blo 1803603 9137609 := bstep (se 2 (by rfl) ⟨3426603, by rfl⟩ : syracuseStep 9137609 = 6853207) B6853207
theorem B6090227 : Blo 1803603 6090227 := bstep (se 1 (by rfl) ⟨4567670, by rfl⟩ : syracuseStep 6090227 = 9135341) B9135341
theorem B2706953 : Blo 1803603 2706953 := bstep (se 2 (by rfl) ⟨1015107, by rfl⟩ : syracuseStep 2706953 = 2030215) B2030215
theorem B2706983 : Blo 1803603 2706983 := bstep (se 1 (by rfl) ⟨2030237, by rfl⟩ : syracuseStep 2706983 = 4060475) B4060475
theorem B4058747 : Blo 1803603 4058747 := bstep (se 1 (by rfl) ⟨3044060, by rfl⟩ : syracuseStep 4058747 = 6088121) B6088121
theorem B2707067 : Blo 1803603 2707067 := bstep (se 1 (by rfl) ⟨2030300, by rfl⟩ : syracuseStep 2707067 = 4060601) B4060601
theorem B6852235 : Blo 1803603 6852235 := bstep (se 1 (by rfl) ⟨5139176, by rfl⟩ : syracuseStep 6852235 = 10278353) B10278353
theorem B19787453 : Blo 1803603 19787453 := bstep (se 3 (by rfl) ⟨3710147, by rfl⟩ : syracuseStep 19787453 = 7420295) B7420295
theorem B4566739 : Blo 1803603 4566739 := bstep (se 1 (by rfl) ⟨3425054, by rfl⟩ : syracuseStep 4566739 = 6850109) B6850109
theorem B7319251 : Blo 1803603 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B4058873 : Blo 1803603 4058873 := bstep (se 2 (by rfl) ⟨1522077, by rfl⟩ : syracuseStep 4058873 = 3044155) B3044155
theorem B2707193 : Blo 1803603 2707193 := bstep (se 2 (by rfl) ⟨1015197, by rfl⟩ : syracuseStep 2707193 = 2030395) B2030395
theorem B2707295 : Blo 1803603 2707295 := bstep (se 1 (by rfl) ⟨2030471, by rfl⟩ : syracuseStep 2707295 = 4060943) B4060943
theorem B2707307 : Blo 1803603 2707307 := bstep (se 1 (by rfl) ⟨2030480, by rfl⟩ : syracuseStep 2707307 = 4060961) B4060961
theorem B5140385 : Blo 1803603 5140385 := bstep (se 2 (by rfl) ⟨1927644, by rfl⟩ : syracuseStep 5140385 = 3855289) B3855289
theorem B6852539 : Blo 1803603 6852539 := bstep (se 1 (by rfl) ⟨5139404, by rfl⟩ : syracuseStep 6852539 = 10278809) B10278809
theorem B4059143 : Blo 1803603 4059143 := bstep (se 1 (by rfl) ⟨3044357, by rfl⟩ : syracuseStep 4059143 = 6088715) B6088715
theorem B6090767 : Blo 1803603 6090767 := bstep (se 1 (by rfl) ⟨4568075, by rfl⟩ : syracuseStep 6090767 = 9136151) B9136151
theorem B10416185 : Blo 1803603 10416185 := bstep (se 2 (by rfl) ⟨3906069, by rfl⟩ : syracuseStep 10416185 = 7812139) B7812139
theorem B4059215 : Blo 1803603 4059215 := bstep (se 1 (by rfl) ⟨3044411, by rfl⟩ : syracuseStep 4059215 = 6088823) B6088823
theorem B2707535 : Blo 1803603 2707535 := bstep (se 1 (by rfl) ⟨2030651, by rfl⟩ : syracuseStep 2707535 = 4061303) B4061303
theorem B9138257 : Blo 1803603 9138257 := bstep (se 2 (by rfl) ⟨3426846, by rfl⟩ : syracuseStep 9138257 = 6853693) B6853693
theorem B7704733 : Blo 1803603 7704733 := bstep (se 3 (by rfl) ⟨1444637, by rfl⟩ : syracuseStep 7704733 = 2889275) B2889275
theorem B2707655 : Blo 1803603 2707655 := bstep (se 1 (by rfl) ⟨2030741, by rfl⟩ : syracuseStep 2707655 = 4061483) B4061483
theorem B4337911 : Blo 1803603 4337911 := bstep (se 1 (by rfl) ⟨3253433, by rfl⟩ : syracuseStep 4337911 = 6506867) B6506867
theorem B2707817 : Blo 1803603 2707817 := bstep (se 2 (by rfl) ⟨1015431, by rfl⟩ : syracuseStep 2707817 = 2030863) B2030863
theorem B2707895 : Blo 1803603 2707895 := bstep (se 1 (by rfl) ⟨2030921, by rfl⟩ : syracuseStep 2707895 = 4061843) B4061843
theorem B4059611 : Blo 1803603 4059611 := bstep (se 1 (by rfl) ⟨3044708, by rfl⟩ : syracuseStep 4059611 = 6089417) B6089417
theorem B2707931 : Blo 1803603 2707931 := bstep (se 1 (by rfl) ⟨2030948, by rfl⟩ : syracuseStep 2707931 = 4061897) B4061897
theorem B14840329 : Blo 1803603 14840329 := bstep (se 2 (by rfl) ⟨5565123, by rfl⟩ : syracuseStep 14840329 = 11130247) B11130247
theorem B3043919 : Blo 1803603 3043919 := bstep (se 1 (by rfl) ⟨2282939, by rfl⟩ : syracuseStep 3043919 = 4565879) B4565879
theorem B6091361 : Blo 1803603 6091361 := bstep (se 2 (by rfl) ⟨2284260, by rfl⟩ : syracuseStep 6091361 = 4568521) B4568521
theorem B4567691 : Blo 1803603 4567691 := bstep (se 1 (by rfl) ⟨3425768, by rfl⟩ : syracuseStep 4567691 = 6851537) B6851537
theorem B13005521 : Blo 1803603 13005521 := bstep (se 2 (by rfl) ⟨4877070, by rfl⟩ : syracuseStep 13005521 = 9754141) B9754141
theorem B4060079 : Blo 1803603 4060079 := bstep (se 1 (by rfl) ⟨3045059, by rfl⟩ : syracuseStep 4060079 = 6090119) B6090119
theorem B2708399 : Blo 1803603 2708399 := bstep (se 1 (by rfl) ⟨2031299, by rfl⟩ : syracuseStep 2708399 = 4062599) B4062599
theorem B6501491 : Blo 1803603 6501491 := bstep (se 1 (by rfl) ⟨4876118, by rfl⟩ : syracuseStep 6501491 = 9752237) B9752237
theorem B5780651 : Blo 1803603 5780651 := bstep (se 1 (by rfl) ⟨4335488, by rfl⟩ : syracuseStep 5780651 = 8670977) B8670977
theorem B4060331 : Blo 1803603 4060331 := bstep (se 1 (by rfl) ⟨3045248, by rfl⟩ : syracuseStep 4060331 = 6090497) B6090497
theorem B3085561 : Blo 1803603 3085561 := bstep (se 2 (by rfl) ⟨1157085, by rfl⟩ : syracuseStep 3085561 = 2314171) B2314171
theorem B34674065 : Blo 1803603 34674065 := bstep (se 2 (by rfl) ⟨13002774, by rfl⟩ : syracuseStep 34674065 = 26005549) B26005549
theorem B37033361 : Blo 1803603 37033361 := bstep (se 2 (by rfl) ⟨13887510, by rfl⟩ : syracuseStep 37033361 = 27775021) B27775021
theorem B3044783 : Blo 1803603 3044783 := bstep (se 1 (by rfl) ⟨2283587, by rfl⟩ : syracuseStep 3044783 = 4567175) B4567175
theorem B2569691 : Blo 1803603 2569691 := bstep (se 1 (by rfl) ⟨1927268, by rfl⟩ : syracuseStep 2569691 = 3854537) B3854537
theorem B15619645 : Blo 1803603 15619645 := bstep (se 3 (by rfl) ⟨2928683, by rfl⟩ : syracuseStep 15619645 = 5857367) B5857367
theorem B2029135 : Blo 1803603 2029135 := bstep (se 1 (by rfl) ⟨1521851, by rfl⟩ : syracuseStep 2029135 = 3043703) B3043703
theorem B8230547 : Blo 1803603 8230547 := bstep (se 1 (by rfl) ⟨6172910, by rfl⟩ : syracuseStep 8230547 = 12345821) B12345821
theorem B4060871 : Blo 1803603 4060871 := bstep (se 1 (by rfl) ⟨3045653, by rfl⟩ : syracuseStep 4060871 = 6091307) B6091307
theorem B11564765 : Blo 1803603 11564765 := bstep (se 3 (by rfl) ⟨2168393, by rfl⟩ : syracuseStep 11564765 = 4336787) B4336787
theorem B4568825 : Blo 1803603 4568825 := bstep (se 2 (by rfl) ⟨1713309, by rfl⟩ : syracuseStep 4568825 = 3426619) B3426619
theorem B29267801 : Blo 1803603 29267801 := bstep (se 2 (by rfl) ⟨10975425, by rfl⟩ : syracuseStep 29267801 = 21950851) B21950851
theorem B3045215 : Blo 1803603 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B3708767 : Blo 1803603 3708767 := bstep (se 1 (by rfl) ⟨2781575, by rfl⟩ : syracuseStep 3708767 = 5563151) B5563151
theorem B4569007 : Blo 1803603 4569007 := bstep (se 1 (by rfl) ⟨3426755, by rfl⟩ : syracuseStep 4569007 = 6853511) B6853511
theorem B4880303 : Blo 1803603 4880303 := bstep (se 1 (by rfl) ⟨3660227, by rfl⟩ : syracuseStep 4880303 = 7320455) B7320455
theorem B11564993 : Blo 1803603 11564993 := bstep (se 2 (by rfl) ⟨4336872, by rfl⟩ : syracuseStep 11564993 = 8673745) B8673745
theorem B2029531 : Blo 1803603 2029531 := bstep (se 1 (by rfl) ⟨1522148, by rfl⟩ : syracuseStep 2029531 = 3044297) B3044297
theorem B2471899 : Blo 1803603 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B2570249 : Blo 1803603 2570249 := bstep (se 2 (by rfl) ⟨963843, by rfl⟩ : syracuseStep 2570249 = 1927687) B1927687
theorem B6092819 : Blo 1803603 6092819 := bstep (se 1 (by rfl) ⟨4569614, by rfl⟩ : syracuseStep 6092819 = 9139229) B9139229
theorem B6502457 : Blo 1803603 6502457 := bstep (se 2 (by rfl) ⟨2438421, by rfl⟩ : syracuseStep 6502457 = 4876843) B4876843
theorem B2283643 : Blo 1803603 2283643 := bstep (se 1 (by rfl) ⟨1712732, by rfl⟩ : syracuseStep 2283643 = 3425465) B3425465
theorem B8673437 : Blo 1803603 8673437 := bstep (se 3 (by rfl) ⟨1626269, by rfl⟩ : syracuseStep 8673437 = 3252539) B3252539
theorem B6093143 : Blo 1803603 6093143 := bstep (se 1 (by rfl) ⟨4569857, by rfl⟩ : syracuseStep 6093143 = 9139715) B9139715
theorem B2283871 : Blo 1803603 2283871 := bstep (se 1 (by rfl) ⟨1712903, by rfl⟩ : syracuseStep 2283871 = 3425807) B3425807
theorem B4569473 : Blo 1803603 4569473 := bstep (se 2 (by rfl) ⟨1713552, by rfl⟩ : syracuseStep 4569473 = 3427105) B3427105
theorem B3045775 : Blo 1803603 3045775 := bstep (se 1 (by rfl) ⟨2284331, by rfl⟩ : syracuseStep 3045775 = 4568663) B4568663
theorem B2029999 : Blo 1803603 2029999 := bstep (se 1 (by rfl) ⟨1522499, by rfl⟩ : syracuseStep 2029999 = 3044999) B3044999
theorem B4061735 : Blo 1803603 4061735 := bstep (se 1 (by rfl) ⟨3046301, by rfl⟩ : syracuseStep 4061735 = 6092603) B6092603
theorem B50076235 : Blo 1803603 50076235 := bstep (se 1 (by rfl) ⟨37557176, by rfl⟩ : syracuseStep 50076235 = 75114353) B75114353
theorem B5487227 : Blo 1803603 5487227 := bstep (se 1 (by rfl) ⟨4115420, by rfl⟩ : syracuseStep 5487227 = 8230841) B8230841
theorem B11557511 : Blo 1803603 11557511 := bstep (se 1 (by rfl) ⟨8668133, by rfl⟩ : syracuseStep 11557511 = 17336267) B17336267
theorem B7420625 : Blo 1803603 7420625 := bstep (se 2 (by rfl) ⟨2782734, by rfl⟩ : syracuseStep 7420625 = 5565469) B5565469
theorem B3709687 : Blo 1803603 3709687 := bstep (se 1 (by rfl) ⟨2782265, by rfl⟩ : syracuseStep 3709687 = 5564531) B5564531
theorem B30849821 : Blo 1803603 30849821 := bstep (se 3 (by rfl) ⟨5784341, by rfl⟩ : syracuseStep 30849821 = 11568683) B11568683
theorem B4569929 : Blo 1803603 4569929 := bstep (se 2 (by rfl) ⟨1713723, by rfl⟩ : syracuseStep 4569929 = 3427447) B3427447
theorem B2030431 : Blo 1803603 2030431 := bstep (se 1 (by rfl) ⟨1522823, by rfl⟩ : syracuseStep 2030431 = 3045647) B3045647
theorem B4062059 : Blo 1803603 4062059 := bstep (se 1 (by rfl) ⟨3046544, by rfl⟩ : syracuseStep 4062059 = 6093089) B6093089
theorem B4062113 : Blo 1803603 4062113 := bstep (se 2 (by rfl) ⟨1523292, by rfl⟩ : syracuseStep 4062113 = 3046585) B3046585
theorem B2284463 : Blo 1803603 2284463 := bstep (se 1 (by rfl) ⟨1713347, by rfl⟩ : syracuseStep 2284463 = 3426695) B3426695
theorem B5209019 : Blo 1803603 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B3046457 : Blo 1803603 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B4570283 : Blo 1803603 4570283 := bstep (se 1 (by rfl) ⟨3427712, by rfl⟩ : syracuseStep 4570283 = 6855425) B6855425
theorem B2030791 : Blo 1803603 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B15834359 : Blo 1803603 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B4062455 : Blo 1803603 4062455 := bstep (se 1 (by rfl) ⟨3046841, by rfl⟩ : syracuseStep 4062455 = 6093683) B6093683
theorem B32923201 : Blo 1803603 32923201 := bstep (se 2 (by rfl) ⟨12346200, by rfl⟩ : syracuseStep 32923201 = 24692401) B24692401
theorem B6848135 : Blo 1803603 6848135 := bstep (se 1 (by rfl) ⟨5136101, by rfl⟩ : syracuseStep 6848135 = 10272203) B10272203
theorem B15417053 : Blo 1803603 15417053 := bstep (se 3 (by rfl) ⟨2890697, by rfl⟩ : syracuseStep 15417053 = 5781395) B5781395
theorem B52051693 : Blo 1803603 52051693 := bstep (se 3 (by rfl) ⟨9759692, by rfl⟩ : syracuseStep 52051693 = 19519385) B19519385
theorem B6504259 : Blo 1803603 6504259 := bstep (se 1 (by rfl) ⟨4878194, by rfl⟩ : syracuseStep 6504259 = 9756389) B9756389
theorem B23117683 : Blo 1803603 23117683 := bstep (se 1 (by rfl) ⟨17338262, by rfl⟩ : syracuseStep 23117683 = 34676525) B34676525
theorem B5783471 : Blo 1803603 5783471 := bstep (se 1 (by rfl) ⟨4337603, by rfl⟩ : syracuseStep 5783471 = 8675207) B8675207
theorem B10272977 : Blo 1803603 10272977 := bstep (se 2 (by rfl) ⟨3852366, by rfl⟩ : syracuseStep 10272977 = 7704733) B7704733
theorem B26018009 : Blo 1803603 26018009 := bstep (se 2 (by rfl) ⟨9756753, by rfl⟩ : syracuseStep 26018009 = 19513507) B19513507
theorem B5783881 : Blo 1803603 5783881 := bstep (se 2 (by rfl) ⟨2168955, by rfl⟩ : syracuseStep 5783881 = 4337911) B4337911
theorem B13001161 : Blo 1803603 13001161 := bstep (se 2 (by rfl) ⟨4875435, by rfl⟩ : syracuseStep 13001161 = 9750871) B9750871
theorem B12354059 : Blo 1803603 12354059 := bstep (se 1 (by rfl) ⟨9265544, by rfl⟩ : syracuseStep 12354059 = 18531089) B18531089
theorem B2605675 : Blo 1803603 2605675 := bstep (se 1 (by rfl) ⟨1954256, by rfl⟩ : syracuseStep 2605675 = 3908513) B3908513
theorem B3474095 : Blo 1803603 3474095 := bstep (se 1 (by rfl) ⟨2605571, by rfl⟩ : syracuseStep 3474095 = 5211143) B5211143
theorem B4334327 : Blo 1803603 4334327 := bstep (se 1 (by rfl) ⟨3250745, by rfl⟩ : syracuseStep 4334327 = 6501491) B6501491
theorem B39036005 : Blo 1803603 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B8676497 : Blo 1803603 8676497 := bstep (se 2 (by rfl) ⟨3253686, by rfl⟩ : syracuseStep 8676497 = 6507373) B6507373
theorem B7709843 : Blo 1803603 7709843 := bstep (se 1 (by rfl) ⟨5782382, by rfl⟩ : syracuseStep 7709843 = 11564765) B11564765
theorem B8668403 : Blo 1803603 8668403 := bstep (se 1 (by rfl) ⟨6501302, by rfl⟩ : syracuseStep 8668403 = 13002605) B13002605
theorem B3253535 : Blo 1803603 3253535 := bstep (se 1 (by rfl) ⟨2440151, by rfl⟩ : syracuseStep 3253535 = 4880303) B4880303
theorem B7709995 : Blo 1803603 7709995 := bstep (se 1 (by rfl) ⟨5782496, by rfl⟩ : syracuseStep 7709995 = 11564993) B11564993
theorem B6505771 : Blo 1803603 6505771 := bstep (se 1 (by rfl) ⟨4879328, by rfl⟩ : syracuseStep 6505771 = 9758657) B9758657
theorem B12518707 : Blo 1803603 12518707 := bstep (se 1 (by rfl) ⟨9389030, by rfl⟩ : syracuseStep 12518707 = 18778061) B18778061
theorem B1803611 : Blo 1803603 1803611 := bstep (se 1 (by rfl) ⟨1352708, by rfl⟩ : syracuseStep 1803611 = 2705417) B2705417
theorem B1803631 : Blo 1803603 1803631 := bstep (se 1 (by rfl) ⟨1352723, by rfl⟩ : syracuseStep 1803631 = 2705447) B2705447
theorem B4334971 : Blo 1803603 4334971 := bstep (se 1 (by rfl) ⟨3251228, by rfl⟩ : syracuseStep 4334971 = 6502457) B6502457
theorem B1803687 : Blo 1803603 1803687 := bstep (se 1 (by rfl) ⟨1352765, by rfl⟩ : syracuseStep 1803687 = 2705531) B2705531
theorem B1803771 : Blo 1803603 1803771 := bstep (se 1 (by rfl) ⟨1352828, by rfl⟩ : syracuseStep 1803771 = 2705657) B2705657
theorem B1803839 : Blo 1803603 1803839 := bstep (se 1 (by rfl) ⟨1352879, by rfl⟩ : syracuseStep 1803839 = 2705759) B2705759
theorem B1803847 : Blo 1803603 1803847 := bstep (se 1 (by rfl) ⟨1352885, by rfl⟩ : syracuseStep 1803847 = 2705771) B2705771
theorem B10028701 : Blo 1803603 10028701 := bstep (se 3 (by rfl) ⟨1880381, by rfl⟩ : syracuseStep 10028701 = 3760763) B3760763
theorem B4114081 : Blo 1803603 4114081 := bstep (se 2 (by rfl) ⟨1542780, by rfl⟩ : syracuseStep 4114081 = 3085561) B3085561
theorem B1803999 : Blo 1803603 1803999 := bstep (se 1 (by rfl) ⟨1352999, by rfl⟩ : syracuseStep 1803999 = 2705999) B2705999
theorem B1804079 : Blo 1803603 1804079 := bstep (se 1 (by rfl) ⟨1353059, by rfl⟩ : syracuseStep 1804079 = 2706119) B2706119
theorem B6088553 : Blo 1803603 6088553 := bstep (se 2 (by rfl) ⟨2283207, by rfl⟩ : syracuseStep 6088553 = 4566415) B4566415
theorem B1804187 : Blo 1803603 1804187 := bstep (se 1 (by rfl) ⟨1353140, by rfl⟩ : syracuseStep 1804187 = 2706281) B2706281
theorem B1804239 : Blo 1803603 1804239 := bstep (se 1 (by rfl) ⟨1353179, by rfl⟩ : syracuseStep 1804239 = 2706359) B2706359
theorem B1804263 : Blo 1803603 1804263 := bstep (se 1 (by rfl) ⟨1353197, by rfl⟩ : syracuseStep 1804263 = 2706395) B2706395
theorem B20826193 : Blo 1803603 20826193 := bstep (se 2 (by rfl) ⟨7809822, by rfl⟩ : syracuseStep 20826193 = 15619645) B15619645
theorem B2705513 : Blo 1803603 2705513 := bstep (se 2 (by rfl) ⟨1014567, by rfl⟩ : syracuseStep 2705513 = 2029135) B2029135
theorem B9136313 : Blo 1803603 9136313 := bstep (se 2 (by rfl) ⟨3426117, by rfl⟩ : syracuseStep 9136313 = 6852235) B6852235
theorem B9890045 : Blo 1803603 9890045 := bstep (se 3 (by rfl) ⟨1854383, by rfl⟩ : syracuseStep 9890045 = 3708767) B3708767
theorem B6088985 : Blo 1803603 6088985 := bstep (se 2 (by rfl) ⟨2283369, by rfl⟩ : syracuseStep 6088985 = 4566739) B4566739
theorem B1804575 : Blo 1803603 1804575 := bstep (se 1 (by rfl) ⟨1353431, by rfl⟩ : syracuseStep 1804575 = 2706863) B2706863
theorem B1804635 : Blo 1803603 1804635 := bstep (se 1 (by rfl) ⟨1353476, by rfl⟩ : syracuseStep 1804635 = 2706953) B2706953
theorem B1804655 : Blo 1803603 1804655 := bstep (se 1 (by rfl) ⟨1353491, by rfl⟩ : syracuseStep 1804655 = 2706983) B2706983
theorem B2705831 : Blo 1803603 2705831 := bstep (se 1 (by rfl) ⟨2029373, by rfl⟩ : syracuseStep 2705831 = 4058747) B4058747
theorem B1804711 : Blo 1803603 1804711 := bstep (se 1 (by rfl) ⟨1353533, by rfl⟩ : syracuseStep 1804711 = 2707067) B2707067
theorem B4565423 : Blo 1803603 4565423 := bstep (se 1 (by rfl) ⟨3424067, by rfl⟩ : syracuseStep 4565423 = 6848135) B6848135
theorem B13191635 : Blo 1803603 13191635 := bstep (se 1 (by rfl) ⟨9893726, by rfl⟩ : syracuseStep 13191635 = 19787453) B19787453
theorem B2705915 : Blo 1803603 2705915 := bstep (se 1 (by rfl) ⟨2029436, by rfl⟩ : syracuseStep 2705915 = 4058873) B4058873
theorem B1804795 : Blo 1803603 1804795 := bstep (se 1 (by rfl) ⟨1353596, by rfl⟩ : syracuseStep 1804795 = 2707193) B2707193
theorem B1804863 : Blo 1803603 1804863 := bstep (se 1 (by rfl) ⟨1353647, by rfl⟩ : syracuseStep 1804863 = 2707295) B2707295
theorem B1804871 : Blo 1803603 1804871 := bstep (se 1 (by rfl) ⟨1353653, by rfl⟩ : syracuseStep 1804871 = 2707307) B2707307
theorem B3426923 : Blo 1803603 3426923 := bstep (se 1 (by rfl) ⟨2570192, by rfl⟩ : syracuseStep 3426923 = 5140385) B5140385
theorem B2706041 : Blo 1803603 2706041 := bstep (se 2 (by rfl) ⟨1014765, by rfl⟩ : syracuseStep 2706041 = 2029531) B2029531
theorem B3295865 : Blo 1803603 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B2706095 : Blo 1803603 2706095 := bstep (se 1 (by rfl) ⟨2029571, by rfl⟩ : syracuseStep 2706095 = 4059143) B4059143
theorem B8235695 : Blo 1803603 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B2706143 : Blo 1803603 2706143 := bstep (se 1 (by rfl) ⟨2029607, by rfl⟩ : syracuseStep 2706143 = 4059215) B4059215
theorem B1805023 : Blo 1803603 1805023 := bstep (se 1 (by rfl) ⟨1353767, by rfl⟩ : syracuseStep 1805023 = 2707535) B2707535
theorem B1805103 : Blo 1803603 1805103 := bstep (se 1 (by rfl) ⟨1353827, by rfl⟩ : syracuseStep 1805103 = 2707655) B2707655
theorem B20835139 : Blo 1803603 20835139 := bstep (se 1 (by rfl) ⟨15626354, by rfl⟩ : syracuseStep 20835139 = 31252709) B31252709
theorem B1805211 : Blo 1803603 1805211 := bstep (se 1 (by rfl) ⟨1353908, by rfl⟩ : syracuseStep 1805211 = 2707817) B2707817
theorem B1805263 : Blo 1803603 1805263 := bstep (se 1 (by rfl) ⟨1353947, by rfl⟩ : syracuseStep 1805263 = 2707895) B2707895
theorem B2706407 : Blo 1803603 2706407 := bstep (se 1 (by rfl) ⟨2029805, by rfl⟩ : syracuseStep 2706407 = 4059611) B4059611
theorem B1805287 : Blo 1803603 1805287 := bstep (se 1 (by rfl) ⟨1353965, by rfl⟩ : syracuseStep 1805287 = 2707931) B2707931
theorem B23129165 : Blo 1803603 23129165 := bstep (se 3 (by rfl) ⟨4336718, by rfl⟩ : syracuseStep 23129165 = 8673437) B8673437
theorem B8670347 : Blo 1803603 8670347 := bstep (se 1 (by rfl) ⟨6502760, by rfl⟩ : syracuseStep 8670347 = 13005521) B13005521
theorem B2706665 : Blo 1803603 2706665 := bstep (se 2 (by rfl) ⟨1014999, by rfl⟩ : syracuseStep 2706665 = 2029999) B2029999
theorem B2706719 : Blo 1803603 2706719 := bstep (se 1 (by rfl) ⟨2030039, by rfl⟩ : syracuseStep 2706719 = 4060079) B4060079
theorem B1805599 : Blo 1803603 1805599 := bstep (se 1 (by rfl) ⟨1354199, by rfl⟩ : syracuseStep 1805599 = 2708399) B2708399
theorem B19787105 : Blo 1803603 19787105 := bstep (se 2 (by rfl) ⟨7420164, by rfl⟩ : syracuseStep 19787105 = 14840329) B14840329
theorem B4566395 : Blo 1803603 4566395 := bstep (se 1 (by rfl) ⟨3424796, by rfl⟩ : syracuseStep 4566395 = 6849593) B6849593
theorem B66768313 : Blo 1803603 66768313 := bstep (se 2 (by rfl) ⟨25038117, by rfl⟩ : syracuseStep 66768313 = 50076235) B50076235
theorem B4058567 : Blo 1803603 4058567 := bstep (se 1 (by rfl) ⟨3043925, by rfl⟩ : syracuseStep 4058567 = 6087851) B6087851
theorem B15412679 : Blo 1803603 15412679 := bstep (se 1 (by rfl) ⟨11559509, by rfl⟩ : syracuseStep 15412679 = 23119019) B23119019
theorem B2706887 : Blo 1803603 2706887 := bstep (se 1 (by rfl) ⟨2030165, by rfl⟩ : syracuseStep 2706887 = 4060331) B4060331
theorem B6090335 : Blo 1803603 6090335 := bstep (se 1 (by rfl) ⟨4567751, by rfl⟩ : syracuseStep 6090335 = 9135503) B9135503
theorem B7040621 : Blo 1803603 7040621 := bstep (se 3 (by rfl) ⟨1320116, by rfl⟩ : syracuseStep 7040621 = 2640233) B2640233
theorem B7319155 : Blo 1803603 7319155 := bstep (se 1 (by rfl) ⟨5489366, by rfl⟩ : syracuseStep 7319155 = 10978733) B10978733
theorem B4566689 : Blo 1803603 4566689 := bstep (se 2 (by rfl) ⟨1712508, by rfl⟩ : syracuseStep 4566689 = 3425017) B3425017
theorem B14839507 : Blo 1803603 14839507 := bstep (se 1 (by rfl) ⟨11129630, by rfl⟩ : syracuseStep 14839507 = 22259261) B22259261
theorem B2707241 : Blo 1803603 2707241 := bstep (se 2 (by rfl) ⟨1015215, by rfl⟩ : syracuseStep 2707241 = 2030431) B2030431
theorem B4058927 : Blo 1803603 4058927 := bstep (se 1 (by rfl) ⟨3044195, by rfl⟩ : syracuseStep 4058927 = 6088391) B6088391
theorem B14659375 : Blo 1803603 14659375 := bstep (se 1 (by rfl) ⟨10994531, by rfl⟩ : syracuseStep 14659375 = 21989063) B21989063
theorem B2707247 : Blo 1803603 2707247 := bstep (se 1 (by rfl) ⟨2030435, by rfl⟩ : syracuseStep 2707247 = 4060871) B4060871
theorem B6852509 : Blo 1803603 6852509 := bstep (se 3 (by rfl) ⟨1284845, by rfl⟩ : syracuseStep 6852509 = 2569691) B2569691
theorem B9138095 : Blo 1803603 9138095 := bstep (se 1 (by rfl) ⟨6853571, by rfl⟩ : syracuseStep 9138095 = 13707143) B13707143
theorem B32534731 : Blo 1803603 32534731 := bstep (se 1 (by rfl) ⟨24401048, by rfl⟩ : syracuseStep 32534731 = 48802097) B48802097
theorem B2707721 : Blo 1803603 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B4567387 : Blo 1803603 4567387 := bstep (se 1 (by rfl) ⟨3425540, by rfl⟩ : syracuseStep 4567387 = 6851081) B6851081
theorem B4059503 : Blo 1803603 4059503 := bstep (se 1 (by rfl) ⟨3044627, by rfl⟩ : syracuseStep 4059503 = 6089255) B6089255
theorem B2707823 : Blo 1803603 2707823 := bstep (se 1 (by rfl) ⟨2030867, by rfl⟩ : syracuseStep 2707823 = 4061735) B4061735
theorem B3658151 : Blo 1803603 3658151 := bstep (se 1 (by rfl) ⟨2743613, by rfl⟩ : syracuseStep 3658151 = 5487227) B5487227
theorem B7705007 : Blo 1803603 7705007 := bstep (se 1 (by rfl) ⟨5778755, by rfl⟩ : syracuseStep 7705007 = 11557511) B11557511
theorem B4878767 : Blo 1803603 4878767 := bstep (se 1 (by rfl) ⟨3659075, by rfl⟩ : syracuseStep 4878767 = 7318151) B7318151
theorem B4059575 : Blo 1803603 4059575 := bstep (se 1 (by rfl) ⟨3044681, by rfl⟩ : syracuseStep 4059575 = 6089363) B6089363
theorem B4338103 : Blo 1803603 4338103 := bstep (se 1 (by rfl) ⟨3253577, by rfl⟩ : syracuseStep 4338103 = 6507155) B6507155
theorem B20566547 : Blo 1803603 20566547 := bstep (se 1 (by rfl) ⟨15424910, by rfl⟩ : syracuseStep 20566547 = 30849821) B30849821
theorem B4059719 : Blo 1803603 4059719 := bstep (se 1 (by rfl) ⟨3044789, by rfl⟩ : syracuseStep 4059719 = 6089579) B6089579
theorem B2708039 : Blo 1803603 2708039 := bstep (se 1 (by rfl) ⟨2031029, by rfl⟩ : syracuseStep 2708039 = 4062059) B4062059
theorem B4059755 : Blo 1803603 4059755 := bstep (se 1 (by rfl) ⟨3044816, by rfl⟩ : syracuseStep 4059755 = 6089633) B6089633
theorem B2708075 : Blo 1803603 2708075 := bstep (se 1 (by rfl) ⟨2031056, by rfl⟩ : syracuseStep 2708075 = 4062113) B4062113
theorem B43897601 : Blo 1803603 43897601 := bstep (se 2 (by rfl) ⟨16461600, by rfl⟩ : syracuseStep 43897601 = 32923201) B32923201
theorem B10556239 : Blo 1803603 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B2708303 : Blo 1803603 2708303 := bstep (se 1 (by rfl) ⟨2031227, by rfl⟩ : syracuseStep 2708303 = 4062455) B4062455
theorem B6091739 : Blo 1803603 6091739 := bstep (se 1 (by rfl) ⟨4568804, by rfl⟩ : syracuseStep 6091739 = 9137609) B9137609
theorem B4060151 : Blo 1803603 4060151 := bstep (se 1 (by rfl) ⟨3045113, by rfl⟩ : syracuseStep 4060151 = 6090227) B6090227
theorem B8672345 : Blo 1803603 8672345 := bstep (se 2 (by rfl) ⟨3252129, by rfl⟩ : syracuseStep 8672345 = 6504259) B6504259
theorem B6091901 : Blo 1803603 6091901 := bstep (se 3 (by rfl) ⟨1142231, by rfl⟩ : syracuseStep 6091901 = 2284463) B2284463
theorem B10278035 : Blo 1803603 10278035 := bstep (se 1 (by rfl) ⟨7708526, by rfl⟩ : syracuseStep 10278035 = 15417053) B15417053
theorem B30823577 : Blo 1803603 30823577 := bstep (se 2 (by rfl) ⟨11558841, by rfl⟩ : syracuseStep 30823577 = 23117683) B23117683
theorem B6092009 : Blo 1803603 6092009 := bstep (se 2 (by rfl) ⟨2284503, by rfl⟩ : syracuseStep 6092009 = 4569007) B4569007
theorem B3855647 : Blo 1803603 3855647 := bstep (se 1 (by rfl) ⟨2891735, by rfl⟩ : syracuseStep 3855647 = 5783471) B5783471
theorem B4568359 : Blo 1803603 4568359 := bstep (se 1 (by rfl) ⟨3426269, by rfl⟩ : syracuseStep 4568359 = 6852539) B6852539
theorem B2282843 : Blo 1803603 2282843 := bstep (se 1 (by rfl) ⟨1712132, by rfl⟩ : syracuseStep 2282843 = 3424265) B3424265
theorem B4060511 : Blo 1803603 4060511 := bstep (se 1 (by rfl) ⟨3045383, by rfl⟩ : syracuseStep 4060511 = 6090767) B6090767
theorem B6853997 : Blo 1803603 6853997 := bstep (se 3 (by rfl) ⟨1285124, by rfl⟩ : syracuseStep 6853997 = 2570249) B2570249
theorem B6944123 : Blo 1803603 6944123 := bstep (se 1 (by rfl) ⟨5208092, by rfl⟩ : syracuseStep 6944123 = 10416185) B10416185
theorem B6092171 : Blo 1803603 6092171 := bstep (se 1 (by rfl) ⟨4569128, by rfl⟩ : syracuseStep 6092171 = 9138257) B9138257
theorem B9131453 : Blo 1803603 9131453 := bstep (se 3 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 9131453 = 3424295) B3424295
theorem B3044857 : Blo 1803603 3044857 := bstep (se 2 (by rfl) ⟨1141821, by rfl⟩ : syracuseStep 3044857 = 2283643) B2283643
theorem B4568633 : Blo 1803603 4568633 := bstep (se 2 (by rfl) ⟨1713237, by rfl⟩ : syracuseStep 4568633 = 3426475) B3426475
theorem B2029279 : Blo 1803603 2029279 := bstep (se 1 (by rfl) ⟨1521959, by rfl⟩ : syracuseStep 2029279 = 3043919) B3043919
theorem B3086059 : Blo 1803603 3086059 := bstep (se 1 (by rfl) ⟨2314544, by rfl⟩ : syracuseStep 3086059 = 4629089) B4629089
theorem B4060907 : Blo 1803603 4060907 := bstep (se 1 (by rfl) ⟨3045680, by rfl⟩ : syracuseStep 4060907 = 6091361) B6091361
theorem B3045127 : Blo 1803603 3045127 := bstep (se 1 (by rfl) ⟨2283845, by rfl⟩ : syracuseStep 3045127 = 4567691) B4567691
theorem B15415069 : Blo 1803603 15415069 := bstep (se 3 (by rfl) ⟨2890325, by rfl⟩ : syracuseStep 15415069 = 5780651) B5780651
theorem B3045161 : Blo 1803603 3045161 := bstep (se 2 (by rfl) ⟨1141935, by rfl⟩ : syracuseStep 3045161 = 2283871) B2283871
theorem B2283319 : Blo 1803603 2283319 := bstep (se 1 (by rfl) ⟨1712489, by rfl⟩ : syracuseStep 2283319 = 3424979) B3424979
theorem B4061033 : Blo 1803603 4061033 := bstep (se 2 (by rfl) ⟨1522887, by rfl⟩ : syracuseStep 4061033 = 3045775) B3045775
theorem B7313543 : Blo 1803603 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B23116043 : Blo 1803603 23116043 := bstep (se 1 (by rfl) ⟨17337032, by rfl⟩ : syracuseStep 23116043 = 34674065) B34674065
theorem B24688907 : Blo 1803603 24688907 := bstep (se 1 (by rfl) ⟨18516680, by rfl⟩ : syracuseStep 24688907 = 37033361) B37033361
theorem B2029855 : Blo 1803603 2029855 := bstep (se 1 (by rfl) ⟨1522391, by rfl⟩ : syracuseStep 2029855 = 3044783) B3044783
theorem B2283815 : Blo 1803603 2283815 := bstep (se 1 (by rfl) ⟨1712861, by rfl⟩ : syracuseStep 2283815 = 3425723) B3425723
theorem B4946249 : Blo 1803603 4946249 := bstep (se 2 (by rfl) ⟨1854843, by rfl⟩ : syracuseStep 4946249 = 3709687) B3709687
theorem B5487031 : Blo 1803603 5487031 := bstep (se 1 (by rfl) ⟨4115273, by rfl⟩ : syracuseStep 5487031 = 8230547) B8230547
theorem B3045883 : Blo 1803603 3045883 := bstep (se 1 (by rfl) ⟨2284412, by rfl⟩ : syracuseStep 3045883 = 4568825) B4568825
theorem B19511867 : Blo 1803603 19511867 := bstep (se 1 (by rfl) ⟨14633900, by rfl⟩ : syracuseStep 19511867 = 29267801) B29267801
theorem B2030143 : Blo 1803603 2030143 := bstep (se 1 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 2030143 = 3045215) B3045215
theorem B2284139 : Blo 1803603 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B4061879 : Blo 1803603 4061879 := bstep (se 1 (by rfl) ⟨3046409, by rfl⟩ : syracuseStep 4061879 = 6092819) B6092819
theorem B7707383 : Blo 1803603 7707383 := bstep (se 1 (by rfl) ⟨5780537, by rfl⟩ : syracuseStep 7707383 = 11561075) B11561075
theorem B4062095 : Blo 1803603 4062095 := bstep (se 1 (by rfl) ⟨3046571, by rfl⟩ : syracuseStep 4062095 = 6093143) B6093143
theorem B3046315 : Blo 1803603 3046315 := bstep (se 1 (by rfl) ⟨2284736, by rfl⟩ : syracuseStep 3046315 = 4569473) B4569473
theorem B2284519 : Blo 1803603 2284519 := bstep (se 1 (by rfl) ⟨1713389, by rfl⟩ : syracuseStep 2284519 = 3426779) B3426779
theorem B4947083 : Blo 1803603 4947083 := bstep (se 1 (by rfl) ⟨3710312, by rfl⟩ : syracuseStep 4947083 = 7420625) B7420625
theorem B20544677 : Blo 1803603 20544677 := bstep (se 4 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 20544677 = 3852127) B3852127
theorem B3046619 : Blo 1803603 3046619 := bstep (se 1 (by rfl) ⟨2284964, by rfl⟩ : syracuseStep 3046619 = 4569929) B4569929
theorem B33365213 : Blo 1803603 33365213 := bstep (se 3 (by rfl) ⟨6255977, by rfl⟩ : syracuseStep 33365213 = 12511955) B12511955
theorem B3472679 : Blo 1803603 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B2030971 : Blo 1803603 2030971 := bstep (se 1 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 2030971 = 3046457) B3046457
theorem B3046855 : Blo 1803603 3046855 := bstep (se 1 (by rfl) ⟨2285141, by rfl⟩ : syracuseStep 3046855 = 4570283) B4570283
theorem B69402257 : Blo 1803603 69402257 := bstep (se 2 (by rfl) ⟨26025846, by rfl⟩ : syracuseStep 69402257 = 52051693) B52051693
theorem B6848651 : Blo 1803603 6848651 := bstep (se 1 (by rfl) ⟨5136488, by rfl⟩ : syracuseStep 6848651 = 10272977) B10272977
theorem B5136671 : Blo 1803603 5136671 := bstep (se 1 (by rfl) ⟨3852503, by rfl⟩ : syracuseStep 5136671 = 7705007) B7705007
theorem B3252511 : Blo 1803603 3252511 := bstep (se 1 (by rfl) ⟨2439383, by rfl⟩ : syracuseStep 3252511 = 4878767) B4878767
theorem B5784137 : Blo 1803603 5784137 := bstep (se 2 (by rfl) ⟨2169051, by rfl⟩ : syracuseStep 5784137 = 4338103) B4338103
theorem B17334881 : Blo 1803603 17334881 := bstep (se 2 (by rfl) ⟨6500580, by rfl⟩ : syracuseStep 17334881 = 13001161) B13001161
theorem B10281725 : Blo 1803603 10281725 := bstep (se 3 (by rfl) ⟨1927823, by rfl⟩ : syracuseStep 10281725 = 3855647) B3855647
theorem B5784331 : Blo 1803603 5784331 := bstep (se 1 (by rfl) ⟨4338248, by rfl⟩ : syracuseStep 5784331 = 8676497) B8676497
theorem B3474233 : Blo 1803603 3474233 := bstep (se 2 (by rfl) ⟨1302837, by rfl⟩ : syracuseStep 3474233 = 2605675) B2605675
theorem B13189997 : Blo 1803603 13189997 := bstep (se 3 (by rfl) ⟨2473124, by rfl⟩ : syracuseStep 13189997 = 4946249) B4946249
theorem B6087581 : Blo 1803603 6087581 := bstep (se 3 (by rfl) ⟨1141421, by rfl⟩ : syracuseStep 6087581 = 2282843) B2282843
theorem B4629415 : Blo 1803603 4629415 := bstep (se 1 (by rfl) ⟨3472061, by rfl⟩ : syracuseStep 4629415 = 6944123) B6944123
theorem B52765613 : Blo 1803603 52765613 := bstep (se 3 (by rfl) ⟨9893552, by rfl⟩ : syracuseStep 52765613 = 19787105) B19787105
theorem B6087635 : Blo 1803603 6087635 := bstep (se 1 (by rfl) ⟨4565726, by rfl⟩ : syracuseStep 6087635 = 9131453) B9131453
theorem B27780185 : Blo 1803603 27780185 := bstep (se 2 (by rfl) ⟨10417569, by rfl⟩ : syracuseStep 27780185 = 20835139) B20835139
theorem B79144037 : Blo 1803603 79144037 := bstep (se 4 (by rfl) ⟨7419753, by rfl⟩ : syracuseStep 79144037 = 14839507) B14839507
theorem B14074985 : Blo 1803603 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B1803675 : Blo 1803603 1803675 := bstep (se 1 (by rfl) ⟨1352756, by rfl⟩ : syracuseStep 1803675 = 2705513) B2705513
theorem B4875695 : Blo 1803603 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B15410695 : Blo 1803603 15410695 := bstep (se 1 (by rfl) ⟨11558021, by rfl⟩ : syracuseStep 15410695 = 23116043) B23116043
theorem B16459271 : Blo 1803603 16459271 := bstep (se 1 (by rfl) ⟨12344453, by rfl⟩ : syracuseStep 16459271 = 24688907) B24688907
theorem B1803887 : Blo 1803603 1803887 := bstep (se 1 (by rfl) ⟨1352915, by rfl⟩ : syracuseStep 1803887 = 2705831) B2705831
theorem B1803943 : Blo 1803603 1803943 := bstep (se 1 (by rfl) ⟨1352957, by rfl⟩ : syracuseStep 1803943 = 2705915) B2705915
theorem B1804027 : Blo 1803603 1804027 := bstep (se 1 (by rfl) ⟨1353020, by rfl⟩ : syracuseStep 1804027 = 2706041) B2706041
theorem B2197243 : Blo 1803603 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B1804063 : Blo 1803603 1804063 := bstep (se 1 (by rfl) ⟨1353047, by rfl⟩ : syracuseStep 1804063 = 2706095) B2706095
theorem B1804095 : Blo 1803603 1804095 := bstep (se 1 (by rfl) ⟨1353071, by rfl⟩ : syracuseStep 1804095 = 2706143) B2706143
theorem B5138255 : Blo 1803603 5138255 := bstep (se 1 (by rfl) ⟨3853691, by rfl⟩ : syracuseStep 5138255 = 7707383) B7707383
theorem B89024417 : Blo 1803603 89024417 := bstep (se 2 (by rfl) ⟨33384156, by rfl⟩ : syracuseStep 89024417 = 66768313) B66768313
theorem B1804271 : Blo 1803603 1804271 := bstep (se 1 (by rfl) ⟨1353203, by rfl⟩ : syracuseStep 1804271 = 2706407) B2706407
theorem B15419443 : Blo 1803603 15419443 := bstep (se 1 (by rfl) ⟨11564582, by rfl⟩ : syracuseStep 15419443 = 23129165) B23129165
theorem B22243475 : Blo 1803603 22243475 := bstep (se 1 (by rfl) ⟨16682606, by rfl⟩ : syracuseStep 22243475 = 33365213) B33365213
theorem B1804443 : Blo 1803603 1804443 := bstep (se 1 (by rfl) ⟨1353332, by rfl⟩ : syracuseStep 1804443 = 2706665) B2706665
theorem B9758873 : Blo 1803603 9758873 := bstep (se 2 (by rfl) ⟨3659577, by rfl⟩ : syracuseStep 9758873 = 7319155) B7319155
theorem B1804479 : Blo 1803603 1804479 := bstep (se 1 (by rfl) ⟨1353359, by rfl⟩ : syracuseStep 1804479 = 2706719) B2706719
theorem B13371601 : Blo 1803603 13371601 := bstep (se 2 (by rfl) ⟨5014350, by rfl⟩ : syracuseStep 13371601 = 10028701) B10028701
theorem B29264165 : Blo 1803603 29264165 := bstep (se 4 (by rfl) ⟨2743515, by rfl⟩ : syracuseStep 29264165 = 5487031) B5487031
theorem B2705705 : Blo 1803603 2705705 := bstep (se 2 (by rfl) ⟨1014639, by rfl⟩ : syracuseStep 2705705 = 2029279) B2029279
theorem B2705711 : Blo 1803603 2705711 := bstep (se 1 (by rfl) ⟨2029283, by rfl⟩ : syracuseStep 2705711 = 4058567) B4058567
theorem B10275119 : Blo 1803603 10275119 := bstep (se 1 (by rfl) ⟨7706339, by rfl⟩ : syracuseStep 10275119 = 15412679) B15412679
theorem B1804591 : Blo 1803603 1804591 := bstep (se 1 (by rfl) ⟨1353443, by rfl⟩ : syracuseStep 1804591 = 2706887) B2706887
theorem B4114745 : Blo 1803603 4114745 := bstep (se 2 (by rfl) ⟨1543029, by rfl⟩ : syracuseStep 4114745 = 3086059) B3086059
theorem B1804827 : Blo 1803603 1804827 := bstep (se 1 (by rfl) ⟨1353620, by rfl⟩ : syracuseStep 1804827 = 2707241) B2707241
theorem B2705951 : Blo 1803603 2705951 := bstep (se 1 (by rfl) ⟨2029463, by rfl⟩ : syracuseStep 2705951 = 4058927) B4058927
theorem B1804831 : Blo 1803603 1804831 := bstep (se 1 (by rfl) ⟨1353623, by rfl⟩ : syracuseStep 1804831 = 2707247) B2707247
theorem B17345339 : Blo 1803603 17345339 := bstep (se 1 (by rfl) ⟨13009004, by rfl⟩ : syracuseStep 17345339 = 26018009) B26018009
theorem B1805147 : Blo 1803603 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B2706335 : Blo 1803603 2706335 := bstep (se 1 (by rfl) ⟨2029751, by rfl⟩ : syracuseStep 2706335 = 4059503) B4059503
theorem B1805215 : Blo 1803603 1805215 := bstep (se 1 (by rfl) ⟨1353911, by rfl⟩ : syracuseStep 1805215 = 2707823) B2707823
theorem B43379641 : Blo 1803603 43379641 := bstep (se 2 (by rfl) ⟨16267365, by rfl⟩ : syracuseStep 43379641 = 32534731) B32534731
theorem B2706383 : Blo 1803603 2706383 := bstep (se 1 (by rfl) ⟨2029787, by rfl⟩ : syracuseStep 2706383 = 4059575) B4059575
theorem B2706473 : Blo 1803603 2706473 := bstep (se 2 (by rfl) ⟨1014927, by rfl⟩ : syracuseStep 2706473 = 2029855) B2029855
theorem B2706479 : Blo 1803603 2706479 := bstep (se 1 (by rfl) ⟨2029859, by rfl⟩ : syracuseStep 2706479 = 4059719) B4059719
theorem B1805359 : Blo 1803603 1805359 := bstep (se 1 (by rfl) ⟨1354019, by rfl⟩ : syracuseStep 1805359 = 2708039) B2708039
theorem B2706503 : Blo 1803603 2706503 := bstep (se 1 (by rfl) ⟨2029877, by rfl⟩ : syracuseStep 2706503 = 4059755) B4059755
theorem B1805383 : Blo 1803603 1805383 := bstep (se 1 (by rfl) ⟨1354037, by rfl⟩ : syracuseStep 1805383 = 2708075) B2708075
theorem B7711841 : Blo 1803603 7711841 := bstep (se 2 (by rfl) ⟨2891940, by rfl⟩ : syracuseStep 7711841 = 5783881) B5783881
theorem B6089849 : Blo 1803603 6089849 := bstep (se 2 (by rfl) ⟨2283693, by rfl⟩ : syracuseStep 6089849 = 4567387) B4567387
theorem B29265067 : Blo 1803603 29265067 := bstep (se 1 (by rfl) ⟨21948800, by rfl⟩ : syracuseStep 29265067 = 43897601) B43897601
theorem B1805535 : Blo 1803603 1805535 := bstep (se 1 (by rfl) ⟨1354151, by rfl⟩ : syracuseStep 1805535 = 2708303) B2708303
theorem B2706767 : Blo 1803603 2706767 := bstep (se 1 (by rfl) ⟨2030075, by rfl⟩ : syracuseStep 2706767 = 4060151) B4060151
theorem B2706857 : Blo 1803603 2706857 := bstep (se 2 (by rfl) ⟨1015071, by rfl⟩ : syracuseStep 2706857 = 2030143) B2030143
theorem B6852023 : Blo 1803603 6852023 := bstep (se 1 (by rfl) ⟨5139017, by rfl⟩ : syracuseStep 6852023 = 10278035) B10278035
theorem B5139895 : Blo 1803603 5139895 := bstep (se 1 (by rfl) ⟨3854921, by rfl⟩ : syracuseStep 5139895 = 7709843) B7709843
theorem B20549051 : Blo 1803603 20549051 := bstep (se 1 (by rfl) ⟨15411788, by rfl⟩ : syracuseStep 20549051 = 30823577) B30823577
theorem B6090173 : Blo 1803603 6090173 := bstep (se 3 (by rfl) ⟨1141907, by rfl⟩ : syracuseStep 6090173 = 2283815) B2283815
theorem B9260477 : Blo 1803603 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B5778935 : Blo 1803603 5778935 := bstep (se 1 (by rfl) ⟨4334201, by rfl⟩ : syracuseStep 5778935 = 8668403) B8668403
theorem B2707007 : Blo 1803603 2707007 := bstep (se 1 (by rfl) ⟨2030255, by rfl⟩ : syracuseStep 2707007 = 4060511) B4060511
theorem B2707271 : Blo 1803603 2707271 := bstep (se 1 (by rfl) ⟨2030453, by rfl⟩ : syracuseStep 2707271 = 4060907) B4060907
theorem B4059035 : Blo 1803603 4059035 := bstep (se 1 (by rfl) ⟨3044276, by rfl⟩ : syracuseStep 4059035 = 6088553) B6088553
theorem B2707355 : Blo 1803603 2707355 := bstep (se 1 (by rfl) ⟨2030516, by rfl⟩ : syracuseStep 2707355 = 4061033) B4061033
theorem B32944157 : Blo 1803603 32944157 := bstep (se 3 (by rfl) ⟨6177029, by rfl⟩ : syracuseStep 32944157 = 12354059) B12354059
theorem B6090875 : Blo 1803603 6090875 := bstep (se 1 (by rfl) ⟨4568156, by rfl⟩ : syracuseStep 6090875 = 9136313) B9136313
theorem B4059323 : Blo 1803603 4059323 := bstep (se 1 (by rfl) ⟨3044492, by rfl⟩ : syracuseStep 4059323 = 6088985) B6088985
theorem B6091037 : Blo 1803603 6091037 := bstep (se 3 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 6091037 = 2284139) B2284139
theorem B3043615 : Blo 1803603 3043615 := bstep (se 1 (by rfl) ⟨2282711, by rfl⟩ : syracuseStep 3043615 = 4565423) B4565423
theorem B8794423 : Blo 1803603 8794423 := bstep (se 1 (by rfl) ⟨6595817, by rfl⟩ : syracuseStep 8794423 = 13191635) B13191635
theorem B6091145 : Blo 1803603 6091145 := bstep (se 2 (by rfl) ⟨2284179, by rfl⟩ : syracuseStep 6091145 = 4568359) B4568359
theorem B16691609 : Blo 1803603 16691609 := bstep (se 2 (by rfl) ⟨6259353, by rfl⟩ : syracuseStep 16691609 = 12518707) B12518707
theorem B2707919 : Blo 1803603 2707919 := bstep (se 1 (by rfl) ⟨2030939, by rfl⟩ : syracuseStep 2707919 = 4061879) B4061879
theorem B5779961 : Blo 1803603 5779961 := bstep (se 2 (by rfl) ⟨2167485, by rfl⟩ : syracuseStep 5779961 = 4334971) B4334971
theorem B2707961 : Blo 1803603 2707961 := bstep (se 2 (by rfl) ⟨1015485, by rfl⟩ : syracuseStep 2707961 = 2030971) B2030971
theorem B2708063 : Blo 1803603 2708063 := bstep (se 1 (by rfl) ⟨2031047, by rfl⟩ : syracuseStep 2708063 = 4062095) B4062095
theorem B4059809 : Blo 1803603 4059809 := bstep (se 2 (by rfl) ⟨1522428, by rfl⟩ : syracuseStep 4059809 = 3044857) B3044857
theorem B5780231 : Blo 1803603 5780231 := bstep (se 1 (by rfl) ⟨4335173, by rfl⟩ : syracuseStep 5780231 = 8670347) B8670347
theorem B3298055 : Blo 1803603 3298055 := bstep (se 1 (by rfl) ⟨2473541, by rfl⟩ : syracuseStep 3298055 = 4947083) B4947083
theorem B5485441 : Blo 1803603 5485441 := bstep (se 2 (by rfl) ⟨2057040, by rfl⟩ : syracuseStep 5485441 = 4114081) B4114081
theorem B3044263 : Blo 1803603 3044263 := bstep (se 1 (by rfl) ⟨2283197, by rfl⟩ : syracuseStep 3044263 = 4566395) B4566395
theorem B4060169 : Blo 1803603 4060169 := bstep (se 2 (by rfl) ⟨1522563, by rfl⟩ : syracuseStep 4060169 = 3045127) B3045127
theorem B4060223 : Blo 1803603 4060223 := bstep (se 1 (by rfl) ⟨3045167, by rfl⟩ : syracuseStep 4060223 = 6090335) B6090335
theorem B3044425 : Blo 1803603 3044425 := bstep (se 2 (by rfl) ⟨1141659, by rfl⟩ : syracuseStep 3044425 = 2283319) B2283319
theorem B3044459 : Blo 1803603 3044459 := bstep (se 1 (by rfl) ⟨2283344, by rfl⟩ : syracuseStep 3044459 = 4566689) B4566689
theorem B4568339 : Blo 1803603 4568339 := bstep (se 1 (by rfl) ⟨3426254, by rfl⟩ : syracuseStep 4568339 = 6852509) B6852509
theorem B6092063 : Blo 1803603 6092063 := bstep (se 1 (by rfl) ⟨4569047, by rfl⟩ : syracuseStep 6092063 = 9138095) B9138095
theorem B27768257 : Blo 1803603 27768257 := bstep (se 2 (by rfl) ⟨10413096, by rfl⟩ : syracuseStep 27768257 = 20826193) B20826193
theorem B2438767 : Blo 1803603 2438767 := bstep (se 1 (by rfl) ⟨1829075, by rfl⟩ : syracuseStep 2438767 = 3658151) B3658151
theorem B13711031 : Blo 1803603 13711031 := bstep (se 1 (by rfl) ⟨10283273, by rfl⟩ : syracuseStep 13711031 = 20566547) B20566547
theorem B2889551 : Blo 1803603 2889551 := bstep (se 1 (by rfl) ⟨2167163, by rfl⟩ : syracuseStep 2889551 = 4334327) B4334327
theorem B4061159 : Blo 1803603 4061159 := bstep (se 1 (by rfl) ⟨3045869, by rfl⟩ : syracuseStep 4061159 = 6091739) B6091739
theorem B4061177 : Blo 1803603 4061177 := bstep (se 2 (by rfl) ⟨1522941, by rfl⟩ : syracuseStep 4061177 = 3045883) B3045883
theorem B5781563 : Blo 1803603 5781563 := bstep (se 1 (by rfl) ⟨4336172, by rfl⟩ : syracuseStep 5781563 = 8672345) B8672345
theorem B26024003 : Blo 1803603 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B4061267 : Blo 1803603 4061267 := bstep (se 1 (by rfl) ⟨3045950, by rfl⟩ : syracuseStep 4061267 = 6091901) B6091901
theorem B4061339 : Blo 1803603 4061339 := bstep (se 1 (by rfl) ⟨3046004, by rfl⟩ : syracuseStep 4061339 = 6092009) B6092009
theorem B2169023 : Blo 1803603 2169023 := bstep (se 1 (by rfl) ⟨1626767, by rfl⟩ : syracuseStep 2169023 = 3253535) B3253535
theorem B4569331 : Blo 1803603 4569331 := bstep (se 1 (by rfl) ⟨3426998, by rfl⟩ : syracuseStep 4569331 = 6853997) B6853997
theorem B4061447 : Blo 1803603 4061447 := bstep (se 1 (by rfl) ⟨3046085, by rfl⟩ : syracuseStep 4061447 = 6092171) B6092171
theorem B3045755 : Blo 1803603 3045755 := bstep (se 1 (by rfl) ⟨2284316, by rfl⟩ : syracuseStep 3045755 = 4568633) B4568633
theorem B2030107 : Blo 1803603 2030107 := bstep (se 1 (by rfl) ⟨1522580, by rfl⟩ : syracuseStep 2030107 = 3045161) B3045161
theorem B4061753 : Blo 1803603 4061753 := bstep (se 2 (by rfl) ⟨1523157, by rfl⟩ : syracuseStep 4061753 = 3046315) B3046315
theorem B3046025 : Blo 1803603 3046025 := bstep (se 2 (by rfl) ⟨1142259, by rfl⟩ : syracuseStep 3046025 = 2284519) B2284519
theorem B6593363 : Blo 1803603 6593363 := bstep (se 1 (by rfl) ⟨4945022, by rfl⟩ : syracuseStep 6593363 = 9890045) B9890045
theorem B13007911 : Blo 1803603 13007911 := bstep (se 1 (by rfl) ⟨9755933, by rfl⟩ : syracuseStep 13007911 = 19511867) B19511867
theorem B10279993 : Blo 1803603 10279993 := bstep (se 2 (by rfl) ⟨3854997, by rfl⟩ : syracuseStep 10279993 = 7709995) B7709995
theorem B8674361 : Blo 1803603 8674361 := bstep (se 2 (by rfl) ⟨3252885, by rfl⟩ : syracuseStep 8674361 = 6505771) B6505771
theorem B2284615 : Blo 1803603 2284615 := bstep (se 1 (by rfl) ⟨1713461, by rfl⟩ : syracuseStep 2284615 = 3426923) B3426923
theorem B9264253 : Blo 1803603 9264253 := bstep (se 3 (by rfl) ⟨1737047, by rfl⟩ : syracuseStep 9264253 = 3474095) B3474095
theorem B21961853 : Blo 1803603 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B4062473 : Blo 1803603 4062473 := bstep (se 2 (by rfl) ⟨1523427, by rfl⟩ : syracuseStep 4062473 = 3046855) B3046855
theorem B13696451 : Blo 1803603 13696451 := bstep (se 1 (by rfl) ⟨10272338, by rfl⟩ : syracuseStep 13696451 = 20544677) B20544677
theorem B2031079 : Blo 1803603 2031079 := bstep (se 1 (by rfl) ⟨1523309, by rfl⟩ : syracuseStep 2031079 = 3046619) B3046619
theorem B20553425 : Blo 1803603 20553425 := bstep (se 2 (by rfl) ⟨7707534, by rfl⟩ : syracuseStep 20553425 = 15415069) B15415069
theorem B19545833 : Blo 1803603 19545833 := bstep (se 2 (by rfl) ⟨7329687, by rfl⟩ : syracuseStep 19545833 = 14659375) B14659375
theorem B4693747 : Blo 1803603 4693747 := bstep (se 1 (by rfl) ⟨3520310, by rfl⟩ : syracuseStep 4693747 = 7040621) B7040621
theorem B46268171 : Blo 1803603 46268171 := bstep (se 1 (by rfl) ⟨34701128, by rfl⟩ : syracuseStep 46268171 = 69402257) B69402257
theorem B21962771 : Blo 1803603 21962771 := bstep (se 1 (by rfl) ⟨16472078, by rfl⟩ : syracuseStep 21962771 = 32944157) B32944157
theorem B3424447 : Blo 1803603 3424447 := bstep (se 1 (by rfl) ⟨2568335, by rfl⟩ : syracuseStep 3424447 = 5136671) B5136671
theorem B74080493 : Blo 1803603 74080493 := bstep (se 3 (by rfl) ⟨13890092, by rfl⟩ : syracuseStep 74080493 = 27780185) B27780185
theorem B5784061 : Blo 1803603 5784061 := bstep (se 3 (by rfl) ⟨1084511, by rfl⟩ : syracuseStep 5784061 = 2169023) B2169023
theorem B35177075 : Blo 1803603 35177075 := bstep (se 1 (by rfl) ⟨26382806, by rfl⟩ : syracuseStep 35177075 = 52765613) B52765613
theorem B3425503 : Blo 1803603 3425503 := bstep (se 1 (by rfl) ⟨2569127, by rfl⟩ : syracuseStep 3425503 = 5138255) B5138255
theorem B17343881 : Blo 1803603 17343881 := bstep (se 2 (by rfl) ⟨6503955, by rfl⟩ : syracuseStep 17343881 = 13007911) B13007911
theorem B13706657 : Blo 1803603 13706657 := bstep (se 2 (by rfl) ⟨5139996, by rfl⟩ : syracuseStep 13706657 = 10279993) B10279993
theorem B14828983 : Blo 1803603 14828983 := bstep (se 1 (by rfl) ⟨11121737, by rfl⟩ : syracuseStep 14828983 = 22243475) B22243475
theorem B6505915 : Blo 1803603 6505915 := bstep (se 1 (by rfl) ⟨4879436, by rfl⟩ : syracuseStep 6505915 = 9758873) B9758873
theorem B1803803 : Blo 1803603 1803803 := bstep (se 1 (by rfl) ⟨1352852, by rfl⟩ : syracuseStep 1803803 = 2705705) B2705705
theorem B1803807 : Blo 1803603 1803807 := bstep (se 1 (by rfl) ⟨1352855, by rfl⟩ : syracuseStep 1803807 = 2705711) B2705711
theorem B6850079 : Blo 1803603 6850079 := bstep (se 1 (by rfl) ⟨5137559, by rfl⟩ : syracuseStep 6850079 = 10275119) B10275119
theorem B39020089 : Blo 1803603 39020089 := bstep (se 2 (by rfl) ⟨14632533, by rfl⟩ : syracuseStep 39020089 = 29265067) B29265067
theorem B1803967 : Blo 1803603 1803967 := bstep (se 1 (by rfl) ⟨1352975, by rfl⟩ : syracuseStep 1803967 = 2705951) B2705951
theorem B1804223 : Blo 1803603 1804223 := bstep (se 1 (by rfl) ⟨1353167, by rfl⟩ : syracuseStep 1804223 = 2706335) B2706335
theorem B1804255 : Blo 1803603 1804255 := bstep (se 1 (by rfl) ⟨1353191, by rfl⟩ : syracuseStep 1804255 = 2706383) B2706383
theorem B20547593 : Blo 1803603 20547593 := bstep (se 2 (by rfl) ⟨7705347, by rfl⟩ : syracuseStep 20547593 = 15410695) B15410695
theorem B1804315 : Blo 1803603 1804315 := bstep (se 1 (by rfl) ⟨1353236, by rfl⟩ : syracuseStep 1804315 = 2706473) B2706473
theorem B1804319 : Blo 1803603 1804319 := bstep (se 1 (by rfl) ⟨1353239, by rfl⟩ : syracuseStep 1804319 = 2706479) B2706479
theorem B1804335 : Blo 1803603 1804335 := bstep (se 1 (by rfl) ⟨1353251, by rfl⟩ : syracuseStep 1804335 = 2706503) B2706503
theorem B14641235 : Blo 1803603 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B1804511 : Blo 1803603 1804511 := bstep (se 1 (by rfl) ⟨1353383, by rfl⟩ : syracuseStep 1804511 = 2706767) B2706767
theorem B1804571 : Blo 1803603 1804571 := bstep (se 1 (by rfl) ⟨1353428, by rfl⟩ : syracuseStep 1804571 = 2706857) B2706857
theorem B13699367 : Blo 1803603 13699367 := bstep (se 1 (by rfl) ⟨10274525, by rfl⟩ : syracuseStep 13699367 = 20549051) B20549051
theorem B3852623 : Blo 1803603 3852623 := bstep (se 1 (by rfl) ⟨2889467, by rfl⟩ : syracuseStep 3852623 = 5778935) B5778935
theorem B1804671 : Blo 1803603 1804671 := bstep (se 1 (by rfl) ⟨1353503, by rfl⟩ : syracuseStep 1804671 = 2707007) B2707007
theorem B30845447 : Blo 1803603 30845447 := bstep (se 1 (by rfl) ⟨23134085, by rfl⟩ : syracuseStep 30845447 = 46268171) B46268171
theorem B1804847 : Blo 1803603 1804847 := bstep (se 1 (by rfl) ⟨1353635, by rfl⟩ : syracuseStep 1804847 = 2707271) B2707271
theorem B2706023 : Blo 1803603 2706023 := bstep (se 1 (by rfl) ⟨2029517, by rfl⟩ : syracuseStep 2706023 = 4059035) B4059035
theorem B1804903 : Blo 1803603 1804903 := bstep (se 1 (by rfl) ⟨1353677, by rfl⟩ : syracuseStep 1804903 = 2707355) B2707355
theorem B4565767 : Blo 1803603 4565767 := bstep (se 1 (by rfl) ⟨3424325, by rfl⟩ : syracuseStep 4565767 = 6848651) B6848651
theorem B2706215 : Blo 1803603 2706215 := bstep (se 1 (by rfl) ⟨2029661, by rfl⟩ : syracuseStep 2706215 = 4059323) B4059323
theorem B11127739 : Blo 1803603 11127739 := bstep (se 1 (by rfl) ⟨8345804, by rfl⟩ : syracuseStep 11127739 = 16691609) B16691609
theorem B17828801 : Blo 1803603 17828801 := bstep (se 2 (by rfl) ⟨6685800, by rfl⟩ : syracuseStep 17828801 = 13371601) B13371601
theorem B1805279 : Blo 1803603 1805279 := bstep (se 1 (by rfl) ⟨1353959, by rfl⟩ : syracuseStep 1805279 = 2707919) B2707919
theorem B3853307 : Blo 1803603 3853307 := bstep (se 1 (by rfl) ⟨2889980, by rfl⟩ : syracuseStep 3853307 = 5779961) B5779961
theorem B1805307 : Blo 1803603 1805307 := bstep (se 1 (by rfl) ⟨1353980, by rfl⟩ : syracuseStep 1805307 = 2707961) B2707961
theorem B4058153 : Blo 1803603 4058153 := bstep (se 2 (by rfl) ⟨1521807, by rfl⟩ : syracuseStep 4058153 = 3043615) B3043615
theorem B4336681 : Blo 1803603 4336681 := bstep (se 2 (by rfl) ⟨1626255, by rfl⟩ : syracuseStep 4336681 = 3252511) B3252511
theorem B1805375 : Blo 1803603 1805375 := bstep (se 1 (by rfl) ⟨1354031, by rfl⟩ : syracuseStep 1805375 = 2708063) B2708063
theorem B11725897 : Blo 1803603 11725897 := bstep (se 2 (by rfl) ⟨4397211, by rfl⟩ : syracuseStep 11725897 = 8794423) B8794423
theorem B2706539 : Blo 1803603 2706539 := bstep (se 1 (by rfl) ⟨2029904, by rfl⟩ : syracuseStep 2706539 = 4059809) B4059809
theorem B3853487 : Blo 1803603 3853487 := bstep (se 1 (by rfl) ⟨2890115, by rfl⟩ : syracuseStep 3853487 = 5780231) B5780231
theorem B4058387 : Blo 1803603 4058387 := bstep (se 1 (by rfl) ⟨3043790, by rfl⟩ : syracuseStep 4058387 = 6087581) B6087581
theorem B4058423 : Blo 1803603 4058423 := bstep (se 1 (by rfl) ⟨3043817, by rfl⟩ : syracuseStep 4058423 = 6087635) B6087635
theorem B2706779 : Blo 1803603 2706779 := bstep (se 1 (by rfl) ⟨2030084, by rfl⟩ : syracuseStep 2706779 = 4060169) B4060169
theorem B2706809 : Blo 1803603 2706809 := bstep (se 2 (by rfl) ⟨1015053, by rfl⟩ : syracuseStep 2706809 = 2030107) B2030107
theorem B2706815 : Blo 1803603 2706815 := bstep (se 1 (by rfl) ⟨2030111, by rfl⟩ : syracuseStep 2706815 = 4060223) B4060223
theorem B10972847 : Blo 1803603 10972847 := bstep (se 1 (by rfl) ⟨8229635, by rfl⟩ : syracuseStep 10972847 = 16459271) B16459271
theorem B7712441 : Blo 1803603 7712441 := bstep (se 2 (by rfl) ⟨2892165, by rfl⟩ : syracuseStep 7712441 = 5784331) B5784331
theorem B4059017 : Blo 1803603 4059017 := bstep (se 2 (by rfl) ⟨1522131, by rfl⟩ : syracuseStep 4059017 = 3044263) B3044263
theorem B6172553 : Blo 1803603 6172553 := bstep (se 2 (by rfl) ⟨2314707, by rfl⟩ : syracuseStep 6172553 = 4629415) B4629415
theorem B57839521 : Blo 1803603 57839521 := bstep (se 2 (by rfl) ⟨21689820, by rfl⟩ : syracuseStep 57839521 = 43379641) B43379641
theorem B2707439 : Blo 1803603 2707439 := bstep (se 1 (by rfl) ⟨2030579, by rfl⟩ : syracuseStep 2707439 = 4061159) B4061159
theorem B2707451 : Blo 1803603 2707451 := bstep (se 1 (by rfl) ⟨2030588, by rfl⟩ : syracuseStep 2707451 = 4061177) B4061177
theorem B3854375 : Blo 1803603 3854375 := bstep (se 1 (by rfl) ⟨2890781, by rfl⟩ : syracuseStep 3854375 = 5781563) B5781563
theorem B2707511 : Blo 1803603 2707511 := bstep (se 1 (by rfl) ⟨2030633, by rfl⟩ : syracuseStep 2707511 = 4061267) B4061267
theorem B4059233 : Blo 1803603 4059233 := bstep (se 2 (by rfl) ⟨1522212, by rfl⟩ : syracuseStep 4059233 = 3044425) B3044425
theorem B2707559 : Blo 1803603 2707559 := bstep (se 1 (by rfl) ⟨2030669, by rfl⟩ : syracuseStep 2707559 = 4061339) B4061339
theorem B2707631 : Blo 1803603 2707631 := bstep (se 1 (by rfl) ⟨2030723, by rfl⟩ : syracuseStep 2707631 = 4061447) B4061447
theorem B19509443 : Blo 1803603 19509443 := bstep (se 1 (by rfl) ⟨14632082, by rfl⟩ : syracuseStep 19509443 = 29264165) B29264165
theorem B2707835 : Blo 1803603 2707835 := bstep (se 1 (by rfl) ⟨2030876, by rfl⟩ : syracuseStep 2707835 = 4061753) B4061753
theorem B11563559 : Blo 1803603 11563559 := bstep (se 1 (by rfl) ⟨8672669, by rfl⟩ : syracuseStep 11563559 = 17345339) B17345339
theorem B4395575 : Blo 1803603 4395575 := bstep (se 1 (by rfl) ⟨3296681, by rfl⟩ : syracuseStep 4395575 = 6593363) B6593363
theorem B6853193 : Blo 1803603 6853193 := bstep (se 2 (by rfl) ⟨2569947, by rfl⟩ : syracuseStep 6853193 = 5139895) B5139895
theorem B2708105 : Blo 1803603 2708105 := bstep (se 2 (by rfl) ⟨1015539, by rfl⟩ : syracuseStep 2708105 = 2031079) B2031079
theorem B8794813 : Blo 1803603 8794813 := bstep (se 3 (by rfl) ⟨1649027, by rfl⟩ : syracuseStep 8794813 = 3298055) B3298055
theorem B5141227 : Blo 1803603 5141227 := bstep (se 1 (by rfl) ⟨3855920, by rfl⟩ : syracuseStep 5141227 = 7711841) B7711841
theorem B4059899 : Blo 1803603 4059899 := bstep (se 1 (by rfl) ⟨3044924, by rfl⟩ : syracuseStep 4059899 = 6089849) B6089849
theorem B2708315 : Blo 1803603 2708315 := bstep (se 1 (by rfl) ⟨2031236, by rfl⟩ : syracuseStep 2708315 = 4062473) B4062473
theorem B7705469 : Blo 1803603 7705469 := bstep (se 3 (by rfl) ⟨1444775, by rfl⟩ : syracuseStep 7705469 = 2889551) B2889551
theorem B35173325 : Blo 1803603 35173325 := bstep (se 3 (by rfl) ⟨6594998, by rfl⟩ : syracuseStep 35173325 = 13189997) B13189997
theorem B4568015 : Blo 1803603 4568015 := bstep (se 1 (by rfl) ⟨3426011, by rfl⟩ : syracuseStep 4568015 = 6852023) B6852023
theorem B4060115 : Blo 1803603 4060115 := bstep (se 1 (by rfl) ⟨3045086, by rfl⟩ : syracuseStep 4060115 = 6090173) B6090173
theorem B6173651 : Blo 1803603 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B9130967 : Blo 1803603 9130967 := bstep (se 1 (by rfl) ⟨6848225, by rfl⟩ : syracuseStep 9130967 = 13696451) B13696451
theorem B2929657 : Blo 1803603 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B13702283 : Blo 1803603 13702283 := bstep (se 1 (by rfl) ⟨10276712, by rfl⟩ : syracuseStep 13702283 = 20553425) B20553425
theorem B13030555 : Blo 1803603 13030555 := bstep (se 1 (by rfl) ⟨9772916, by rfl⟩ : syracuseStep 13030555 = 19545833) B19545833
theorem B20559257 : Blo 1803603 20559257 := bstep (se 2 (by rfl) ⟨7709721, by rfl⟩ : syracuseStep 20559257 = 15419443) B15419443
theorem B4060583 : Blo 1803603 4060583 := bstep (se 1 (by rfl) ⟨3045437, by rfl⟩ : syracuseStep 4060583 = 6090875) B6090875
theorem B4060691 : Blo 1803603 4060691 := bstep (se 1 (by rfl) ⟨3045518, by rfl⟩ : syracuseStep 4060691 = 6091037) B6091037
theorem B4060763 : Blo 1803603 4060763 := bstep (se 1 (by rfl) ⟨3045572, by rfl⟩ : syracuseStep 4060763 = 6091145) B6091145
theorem B37533293 : Blo 1803603 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B6092441 : Blo 1803603 6092441 := bstep (se 2 (by rfl) ⟨2284665, by rfl⟩ : syracuseStep 6092441 = 4569331) B4569331
theorem B3856091 : Blo 1803603 3856091 := bstep (se 1 (by rfl) ⟨2892068, by rfl⟩ : syracuseStep 3856091 = 5784137) B5784137
theorem B11556587 : Blo 1803603 11556587 := bstep (se 1 (by rfl) ⟨8667440, by rfl⟩ : syracuseStep 11556587 = 17334881) B17334881
theorem B6854483 : Blo 1803603 6854483 := bstep (se 1 (by rfl) ⟨5140862, by rfl⟩ : syracuseStep 6854483 = 10281725) B10281725
theorem B2316155 : Blo 1803603 2316155 := bstep (se 1 (by rfl) ⟨1737116, by rfl⟩ : syracuseStep 2316155 = 3474233) B3474233
theorem B13006757 : Blo 1803603 13006757 := bstep (se 4 (by rfl) ⟨1219383, by rfl⟩ : syracuseStep 13006757 = 2438767) B2438767
theorem B52762691 : Blo 1803603 52762691 := bstep (se 1 (by rfl) ⟨39572018, by rfl⟩ : syracuseStep 52762691 = 79144037) B79144037
theorem B2029639 : Blo 1803603 2029639 := bstep (se 1 (by rfl) ⟨1522229, by rfl⟩ : syracuseStep 2029639 = 3044459) B3044459
theorem B3045559 : Blo 1803603 3045559 := bstep (se 1 (by rfl) ⟨2284169, by rfl⟩ : syracuseStep 3045559 = 4568339) B4568339
theorem B4061375 : Blo 1803603 4061375 := bstep (se 1 (by rfl) ⟨3046031, by rfl⟩ : syracuseStep 4061375 = 6092063) B6092063
theorem B3250463 : Blo 1803603 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B18512171 : Blo 1803603 18512171 := bstep (se 1 (by rfl) ⟨13884128, by rfl⟩ : syracuseStep 18512171 = 27768257) B27768257
theorem B9140687 : Blo 1803603 9140687 := bstep (se 1 (by rfl) ⟨6855515, by rfl⟩ : syracuseStep 9140687 = 13711031) B13711031
theorem B7313921 : Blo 1803603 7313921 := bstep (se 2 (by rfl) ⟨2742720, by rfl⟩ : syracuseStep 7313921 = 5485441) B5485441
theorem B59349611 : Blo 1803603 59349611 := bstep (se 1 (by rfl) ⟨44512208, by rfl⟩ : syracuseStep 59349611 = 89024417) B89024417
theorem B17349335 : Blo 1803603 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B3046153 : Blo 1803603 3046153 := bstep (se 2 (by rfl) ⟨1142307, by rfl⟩ : syracuseStep 3046153 = 2284615) B2284615
theorem B12352337 : Blo 1803603 12352337 := bstep (se 2 (by rfl) ⟨4632126, by rfl⟩ : syracuseStep 12352337 = 9264253) B9264253
theorem B2743163 : Blo 1803603 2743163 := bstep (se 1 (by rfl) ⟨2057372, by rfl⟩ : syracuseStep 2743163 = 4114745) B4114745
theorem B2030503 : Blo 1803603 2030503 := bstep (se 1 (by rfl) ⟨1522877, by rfl⟩ : syracuseStep 2030503 = 3045755) B3045755
theorem B2030683 : Blo 1803603 2030683 := bstep (se 1 (by rfl) ⟨1523012, by rfl⟩ : syracuseStep 2030683 = 3046025) B3046025
theorem B5782907 : Blo 1803603 5782907 := bstep (se 1 (by rfl) ⟨4337180, by rfl⟩ : syracuseStep 5782907 = 8674361) B8674361
theorem B6258329 : Blo 1803603 6258329 := bstep (se 2 (by rfl) ⟨2346873, by rfl⟩ : syracuseStep 6258329 = 4693747) B4693747
theorem B7709039 : Blo 1803603 7709039 := bstep (se 1 (by rfl) ⟨5781779, by rfl⟩ : syracuseStep 7709039 = 11563559) B11563559
theorem B5136979 : Blo 1803603 5136979 := bstep (se 1 (by rfl) ⟨3852734, by rfl⟩ : syracuseStep 5136979 = 7705469) B7705469
theorem B6087311 : Blo 1803603 6087311 := bstep (se 1 (by rfl) ⟨4565483, by rfl⟩ : syracuseStep 6087311 = 9130967) B9130967
theorem B8667901 : Blo 1803603 8667901 := bstep (se 3 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 8667901 = 3250463) B3250463
theorem B9134855 : Blo 1803603 9134855 := bstep (se 1 (by rfl) ⟨6851141, by rfl⟩ : syracuseStep 9134855 = 13702283) B13702283
theorem B10273661 : Blo 1803603 10273661 := bstep (se 3 (by rfl) ⟨1926311, by rfl⟩ : syracuseStep 10273661 = 3852623) B3852623
theorem B13706171 : Blo 1803603 13706171 := bstep (se 1 (by rfl) ⟨10279628, by rfl⟩ : syracuseStep 13706171 = 20559257) B20559257
theorem B6087689 : Blo 1803603 6087689 := bstep (se 2 (by rfl) ⟨2282883, by rfl⟩ : syracuseStep 6087689 = 4565767) B4565767
theorem B14836985 : Blo 1803603 14836985 := bstep (se 2 (by rfl) ⟨5563869, by rfl⟩ : syracuseStep 14836985 = 11127739) B11127739
theorem B13698395 : Blo 1803603 13698395 := bstep (se 1 (by rfl) ⟨10273796, by rfl⟩ : syracuseStep 13698395 = 20547593) B20547593
theorem B4875947 : Blo 1803603 4875947 := bstep (se 1 (by rfl) ⟨3656960, by rfl⟩ : syracuseStep 4875947 = 7313921) B7313921
theorem B20563631 : Blo 1803603 20563631 := bstep (se 1 (by rfl) ⟨15422723, by rfl⟩ : syracuseStep 20563631 = 30845447) B30845447
theorem B1804015 : Blo 1803603 1804015 := bstep (se 1 (by rfl) ⟨1353011, by rfl⟩ : syracuseStep 1804015 = 2706023) B2706023
theorem B1804143 : Blo 1803603 1804143 := bstep (se 1 (by rfl) ⟨1353107, by rfl⟩ : syracuseStep 1804143 = 2706215) B2706215
theorem B8234891 : Blo 1803603 8234891 := bstep (se 1 (by rfl) ⟨6176168, by rfl⟩ : syracuseStep 8234891 = 12352337) B12352337
theorem B10282909 : Blo 1803603 10282909 := bstep (se 3 (by rfl) ⟨1928045, by rfl⟩ : syracuseStep 10282909 = 3856091) B3856091
theorem B1828775 : Blo 1803603 1828775 := bstep (se 1 (by rfl) ⟨1371581, by rfl⟩ : syracuseStep 1828775 = 2743163) B2743163
theorem B2705435 : Blo 1803603 2705435 := bstep (se 1 (by rfl) ⟨2029076, by rfl⟩ : syracuseStep 2705435 = 4058153) B4058153
theorem B1804359 : Blo 1803603 1804359 := bstep (se 1 (by rfl) ⟨1353269, by rfl⟩ : syracuseStep 1804359 = 2706539) B2706539
theorem B2705591 : Blo 1803603 2705591 := bstep (se 1 (by rfl) ⟨2029193, by rfl⟩ : syracuseStep 2705591 = 4058387) B4058387
theorem B2705615 : Blo 1803603 2705615 := bstep (se 1 (by rfl) ⟨2029211, by rfl⟩ : syracuseStep 2705615 = 4058423) B4058423
theorem B1804519 : Blo 1803603 1804519 := bstep (se 1 (by rfl) ⟨1353389, by rfl⟩ : syracuseStep 1804519 = 2706779) B2706779
theorem B1804539 : Blo 1803603 1804539 := bstep (se 1 (by rfl) ⟨1353404, by rfl⟩ : syracuseStep 1804539 = 2706809) B2706809
theorem B1804543 : Blo 1803603 1804543 := bstep (se 1 (by rfl) ⟨1353407, by rfl⟩ : syracuseStep 1804543 = 2706815) B2706815
theorem B79087909 : Blo 1803603 79087909 := bstep (se 4 (by rfl) ⟨7414491, by rfl⟩ : syracuseStep 79087909 = 14828983) B14828983
theorem B4172219 : Blo 1803603 4172219 := bstep (se 1 (by rfl) ⟨3129164, by rfl⟩ : syracuseStep 4172219 = 6258329) B6258329
theorem B2706011 : Blo 1803603 2706011 := bstep (se 1 (by rfl) ⟨2029508, by rfl⟩ : syracuseStep 2706011 = 4059017) B4059017
theorem B4115035 : Blo 1803603 4115035 := bstep (se 1 (by rfl) ⟨3086276, by rfl⟩ : syracuseStep 4115035 = 6172553) B6172553
theorem B1804959 : Blo 1803603 1804959 := bstep (se 1 (by rfl) ⟨1353719, by rfl⟩ : syracuseStep 1804959 = 2707439) B2707439
theorem B1804967 : Blo 1803603 1804967 := bstep (se 1 (by rfl) ⟨1353725, by rfl⟩ : syracuseStep 1804967 = 2707451) B2707451
theorem B14641847 : Blo 1803603 14641847 := bstep (se 1 (by rfl) ⟨10981385, by rfl⟩ : syracuseStep 14641847 = 21962771) B21962771
theorem B1805007 : Blo 1803603 1805007 := bstep (se 1 (by rfl) ⟨1353755, by rfl⟩ : syracuseStep 1805007 = 2707511) B2707511
theorem B2706155 : Blo 1803603 2706155 := bstep (se 1 (by rfl) ⟨2029616, by rfl⟩ : syracuseStep 2706155 = 4059233) B4059233
theorem B1805039 : Blo 1803603 1805039 := bstep (se 1 (by rfl) ⟨1353779, by rfl⟩ : syracuseStep 1805039 = 2707559) B2707559
theorem B2706185 : Blo 1803603 2706185 := bstep (se 2 (by rfl) ⟨1014819, by rfl⟩ : syracuseStep 2706185 = 2029639) B2029639
theorem B1805087 : Blo 1803603 1805087 := bstep (se 1 (by rfl) ⟨1353815, by rfl⟩ : syracuseStep 1805087 = 2707631) B2707631
theorem B140700509 : Blo 1803603 140700509 := bstep (se 3 (by rfl) ⟨26381345, by rfl⟩ : syracuseStep 140700509 = 52762691) B52762691
theorem B1805223 : Blo 1803603 1805223 := bstep (se 1 (by rfl) ⟨1353917, by rfl⟩ : syracuseStep 1805223 = 2707835) B2707835
theorem B4565929 : Blo 1803603 4565929 := bstep (se 2 (by rfl) ⟨1712223, by rfl⟩ : syracuseStep 4565929 = 3424447) B3424447
theorem B1805403 : Blo 1803603 1805403 := bstep (se 1 (by rfl) ⟨1354052, by rfl⟩ : syracuseStep 1805403 = 2708105) B2708105
theorem B2706599 : Blo 1803603 2706599 := bstep (se 1 (by rfl) ⟨2029949, by rfl⟩ : syracuseStep 2706599 = 4059899) B4059899
theorem B1805543 : Blo 1803603 1805543 := bstep (se 1 (by rfl) ⟨1354157, by rfl⟩ : syracuseStep 1805543 = 2708315) B2708315
theorem B2706743 : Blo 1803603 2706743 := bstep (se 1 (by rfl) ⟨2030057, by rfl⟩ : syracuseStep 2706743 = 4060115) B4060115
theorem B4115767 : Blo 1803603 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B7712081 : Blo 1803603 7712081 := bstep (se 2 (by rfl) ⟨2892030, by rfl⟩ : syracuseStep 7712081 = 5784061) B5784061
theorem B11726417 : Blo 1803603 11726417 := bstep (se 2 (by rfl) ⟨4397406, by rfl⟩ : syracuseStep 11726417 = 8794813) B8794813
theorem B11562587 : Blo 1803603 11562587 := bstep (se 1 (by rfl) ⟨8671940, by rfl⟩ : syracuseStep 11562587 = 17343881) B17343881
theorem B9137771 : Blo 1803603 9137771 := bstep (se 1 (by rfl) ⟨6853328, by rfl⟩ : syracuseStep 9137771 = 13706657) B13706657
theorem B2707055 : Blo 1803603 2707055 := bstep (se 1 (by rfl) ⟨2030291, by rfl⟩ : syracuseStep 2707055 = 4060583) B4060583
theorem B2707127 : Blo 1803603 2707127 := bstep (se 1 (by rfl) ⟨2030345, by rfl⟩ : syracuseStep 2707127 = 4060691) B4060691
theorem B4566719 : Blo 1803603 4566719 := bstep (se 1 (by rfl) ⟨3425039, by rfl⟩ : syracuseStep 4566719 = 6850079) B6850079
theorem B2707175 : Blo 1803603 2707175 := bstep (se 1 (by rfl) ⟨2030381, by rfl⟩ : syracuseStep 2707175 = 4060763) B4060763
theorem B25022195 : Blo 1803603 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B7704391 : Blo 1803603 7704391 := bstep (se 1 (by rfl) ⟨5778293, by rfl⟩ : syracuseStep 7704391 = 11556587) B11556587
theorem B2707337 : Blo 1803603 2707337 := bstep (se 2 (by rfl) ⟨1015251, by rfl⟩ : syracuseStep 2707337 = 2030503) B2030503
theorem B8671171 : Blo 1803603 8671171 := bstep (se 1 (by rfl) ⟨6503378, by rfl⟩ : syracuseStep 8671171 = 13006757) B13006757
theorem B9760823 : Blo 1803603 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B15634529 : Blo 1803603 15634529 := bstep (se 2 (by rfl) ⟨5862948, by rfl⟩ : syracuseStep 15634529 = 11725897) B11725897
theorem B2707577 : Blo 1803603 2707577 := bstep (se 2 (by rfl) ⟨1015341, by rfl⟩ : syracuseStep 2707577 = 2030683) B2030683
theorem B2707583 : Blo 1803603 2707583 := bstep (se 1 (by rfl) ⟨2030687, by rfl⟩ : syracuseStep 2707583 = 4061375) B4061375
theorem B12341447 : Blo 1803603 12341447 := bstep (se 1 (by rfl) ⟨9256085, by rfl⟩ : syracuseStep 12341447 = 18512171) B18512171
theorem B4567337 : Blo 1803603 4567337 := bstep (se 2 (by rfl) ⟨1712751, by rfl⟩ : syracuseStep 4567337 = 3425503) B3425503
theorem B2568871 : Blo 1803603 2568871 := bstep (se 1 (by rfl) ⟨1926653, by rfl⟩ : syracuseStep 2568871 = 3853307) B3853307
theorem B2568991 : Blo 1803603 2568991 := bstep (se 1 (by rfl) ⟨1926743, by rfl⟩ : syracuseStep 2568991 = 3853487) B3853487
theorem B3855271 : Blo 1803603 3855271 := bstep (se 1 (by rfl) ⟨2891453, by rfl⟩ : syracuseStep 3855271 = 5782907) B5782907
theorem B5141627 : Blo 1803603 5141627 := bstep (se 1 (by rfl) ⟨3856220, by rfl⟩ : syracuseStep 5141627 = 7712441) B7712441
theorem B93795533 : Blo 1803603 93795533 := bstep (se 3 (by rfl) ⟨17586662, by rfl⟩ : syracuseStep 93795533 = 35173325) B35173325
theorem B2569583 : Blo 1803603 2569583 := bstep (se 1 (by rfl) ⟨1927187, by rfl⟩ : syracuseStep 2569583 = 3854375) B3854375
theorem B13006295 : Blo 1803603 13006295 := bstep (se 1 (by rfl) ⟨9754721, by rfl⟩ : syracuseStep 13006295 = 19509443) B19509443
theorem B49386995 : Blo 1803603 49386995 := bstep (se 1 (by rfl) ⟨37040246, by rfl⟩ : syracuseStep 49386995 = 74080493) B74080493
theorem B4060745 : Blo 1803603 4060745 := bstep (se 2 (by rfl) ⟨1522779, by rfl⟩ : syracuseStep 4060745 = 3045559) B3045559
theorem B2930383 : Blo 1803603 2930383 := bstep (se 1 (by rfl) ⟨2197787, by rfl⟩ : syracuseStep 2930383 = 4395575) B4395575
theorem B4568795 : Blo 1803603 4568795 := bstep (se 1 (by rfl) ⟨3426596, by rfl⟩ : syracuseStep 4568795 = 6853193) B6853193
theorem B23451383 : Blo 1803603 23451383 := bstep (se 1 (by rfl) ⟨17588537, by rfl⟩ : syracuseStep 23451383 = 35177075) B35177075
theorem B3045343 : Blo 1803603 3045343 := bstep (se 1 (by rfl) ⟨2284007, by rfl⟩ : syracuseStep 3045343 = 4568015) B4568015
theorem B6854969 : Blo 1803603 6854969 := bstep (se 2 (by rfl) ⟨2570613, by rfl⟩ : syracuseStep 6854969 = 5141227) B5141227
theorem B4061537 : Blo 1803603 4061537 := bstep (se 2 (by rfl) ⟨1523076, by rfl⟩ : syracuseStep 4061537 = 3046153) B3046153
theorem B4061627 : Blo 1803603 4061627 := bstep (se 1 (by rfl) ⟨3046220, by rfl⟩ : syracuseStep 4061627 = 6092441) B6092441
theorem B4569655 : Blo 1803603 4569655 := bstep (se 1 (by rfl) ⟨3427241, by rfl⟩ : syracuseStep 4569655 = 6854483) B6854483
theorem B3906209 : Blo 1803603 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B5782241 : Blo 1803603 5782241 := bstep (se 2 (by rfl) ⟨2168340, by rfl⟩ : syracuseStep 5782241 = 4336681) B4336681
theorem B9132911 : Blo 1803603 9132911 := bstep (se 1 (by rfl) ⟨6849683, by rfl⟩ : syracuseStep 9132911 = 13699367) B13699367
theorem B17374073 : Blo 1803603 17374073 := bstep (se 2 (by rfl) ⟨6515277, by rfl⟩ : syracuseStep 17374073 = 13030555) B13030555
theorem B6093791 : Blo 1803603 6093791 := bstep (se 1 (by rfl) ⟨4570343, by rfl⟩ : syracuseStep 6093791 = 9140687) B9140687
theorem B39566407 : Blo 1803603 39566407 := bstep (se 1 (by rfl) ⟨29674805, by rfl⟩ : syracuseStep 39566407 = 59349611) B59349611
theorem B11566223 : Blo 1803603 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B8674553 : Blo 1803603 8674553 := bstep (se 2 (by rfl) ⟨3252957, by rfl⟩ : syracuseStep 8674553 = 6505915) B6505915
theorem B11885867 : Blo 1803603 11885867 := bstep (se 1 (by rfl) ⟨8914400, by rfl⟩ : syracuseStep 11885867 = 17828801) B17828801
theorem B52026785 : Blo 1803603 52026785 := bstep (se 2 (by rfl) ⟨19510044, by rfl⟩ : syracuseStep 52026785 = 39020089) B39020089
theorem B6176413 : Blo 1803603 6176413 := bstep (se 3 (by rfl) ⟨1158077, by rfl⟩ : syracuseStep 6176413 = 2316155) B2316155
theorem B7315231 : Blo 1803603 7315231 := bstep (se 1 (by rfl) ⟨5486423, by rfl⟩ : syracuseStep 7315231 = 10972847) B10972847
theorem B77119361 : Blo 1803603 77119361 := bstep (se 2 (by rfl) ⟨28919760, by rfl⟩ : syracuseStep 77119361 = 57839521) B57839521
theorem B21946853 : Blo 1803603 21946853 := bstep (se 4 (by rfl) ⟨2057517, by rfl⟩ : syracuseStep 21946853 = 4115035) B4115035
theorem B6849107 : Blo 1803603 6849107 := bstep (se 1 (by rfl) ⟨5136830, by rfl⟩ : syracuseStep 6849107 = 10273661) B10273661
theorem B6849305 : Blo 1803603 6849305 := bstep (se 2 (by rfl) ⟨2568489, by rfl⟩ : syracuseStep 6849305 = 5136979) B5136979
theorem B62530355 : Blo 1803603 62530355 := bstep (se 1 (by rfl) ⟨46897766, by rfl⟩ : syracuseStep 62530355 = 93795533) B93795533
theorem B3425161 : Blo 1803603 3425161 := bstep (se 2 (by rfl) ⟨1284435, by rfl⟩ : syracuseStep 3425161 = 2568871) B2568871
theorem B32924663 : Blo 1803603 32924663 := bstep (se 1 (by rfl) ⟨24693497, by rfl⟩ : syracuseStep 32924663 = 49386995) B49386995
theorem B3425321 : Blo 1803603 3425321 := bstep (se 2 (by rfl) ⟨1284495, by rfl⟩ : syracuseStep 3425321 = 2568991) B2568991
theorem B6087905 : Blo 1803603 6087905 := bstep (se 2 (by rfl) ⟨2282964, by rfl⟩ : syracuseStep 6087905 = 4565929) B4565929
theorem B5489927 : Blo 1803603 5489927 := bstep (se 1 (by rfl) ⟨4117445, by rfl⟩ : syracuseStep 5489927 = 8234891) B8234891
theorem B46228805 : Blo 1803603 46228805 := bstep (se 4 (by rfl) ⟨4333950, by rfl⟩ : syracuseStep 46228805 = 8667901) B8667901
theorem B1803623 : Blo 1803603 1803623 := bstep (se 1 (by rfl) ⟨1352717, by rfl⟩ : syracuseStep 1803623 = 2705435) B2705435
theorem B1803727 : Blo 1803603 1803727 := bstep (se 1 (by rfl) ⟨1352795, by rfl⟩ : syracuseStep 1803727 = 2705591) B2705591
theorem B1803743 : Blo 1803603 1803743 := bstep (se 1 (by rfl) ⟨1352807, by rfl⟩ : syracuseStep 1803743 = 2705615) B2705615
theorem B31270445 : Blo 1803603 31270445 := bstep (se 3 (by rfl) ⟨5863208, by rfl⟩ : syracuseStep 31270445 = 11726417) B11726417
theorem B1804007 : Blo 1803603 1804007 := bstep (se 1 (by rfl) ⟨1353005, by rfl⟩ : syracuseStep 1804007 = 2706011) B2706011
theorem B1804103 : Blo 1803603 1804103 := bstep (se 1 (by rfl) ⟨1353077, by rfl⟩ : syracuseStep 1804103 = 2706155) B2706155
theorem B1804123 : Blo 1803603 1804123 := bstep (se 1 (by rfl) ⟨1353092, by rfl⟩ : syracuseStep 1804123 = 2706185) B2706185
theorem B93800339 : Blo 1803603 93800339 := bstep (se 1 (by rfl) ⟨70350254, by rfl⟩ : syracuseStep 93800339 = 140700509) B140700509
theorem B6088607 : Blo 1803603 6088607 := bstep (se 1 (by rfl) ⟨4566455, by rfl⟩ : syracuseStep 6088607 = 9132911) B9132911
theorem B7710815 : Blo 1803603 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B1804399 : Blo 1803603 1804399 := bstep (se 1 (by rfl) ⟨1353299, by rfl⟩ : syracuseStep 1804399 = 2706599) B2706599
theorem B7923911 : Blo 1803603 7923911 := bstep (se 1 (by rfl) ⟨5942933, by rfl⟩ : syracuseStep 7923911 = 11885867) B11885867
theorem B1804495 : Blo 1803603 1804495 := bstep (se 1 (by rfl) ⟨1353371, by rfl⟩ : syracuseStep 1804495 = 2706743) B2706743
theorem B8235217 : Blo 1803603 8235217 := bstep (se 2 (by rfl) ⟨3088206, by rfl⟩ : syracuseStep 8235217 = 6176413) B6176413
theorem B1804703 : Blo 1803603 1804703 := bstep (se 1 (by rfl) ⟨1353527, by rfl⟩ : syracuseStep 1804703 = 2707055) B2707055
theorem B4876733 : Blo 1803603 4876733 := bstep (se 3 (by rfl) ⟨914387, by rfl⟩ : syracuseStep 4876733 = 1828775) B1828775
theorem B1804751 : Blo 1803603 1804751 := bstep (se 1 (by rfl) ⟨1353563, by rfl⟩ : syracuseStep 1804751 = 2707127) B2707127
theorem B1804783 : Blo 1803603 1804783 := bstep (se 1 (by rfl) ⟨1353587, by rfl⟩ : syracuseStep 1804783 = 2707175) B2707175
theorem B16681463 : Blo 1803603 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B11561561 : Blo 1803603 11561561 := bstep (se 2 (by rfl) ⟨4335585, by rfl⟩ : syracuseStep 11561561 = 8671171) B8671171
theorem B1804891 : Blo 1803603 1804891 := bstep (se 1 (by rfl) ⟨1353668, by rfl⟩ : syracuseStep 1804891 = 2707337) B2707337
theorem B6507215 : Blo 1803603 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B10423019 : Blo 1803603 10423019 := bstep (se 1 (by rfl) ⟨7817264, by rfl⟩ : syracuseStep 10423019 = 15634529) B15634529
theorem B1805051 : Blo 1803603 1805051 := bstep (se 1 (by rfl) ⟨1353788, by rfl⟩ : syracuseStep 1805051 = 2707577) B2707577
theorem B1805055 : Blo 1803603 1805055 := bstep (se 1 (by rfl) ⟨1353791, by rfl⟩ : syracuseStep 1805055 = 2707583) B2707583
theorem B8227631 : Blo 1803603 8227631 := bstep (se 1 (by rfl) ⟨6170723, by rfl⟩ : syracuseStep 8227631 = 12341447) B12341447
theorem B5139359 : Blo 1803603 5139359 := bstep (se 1 (by rfl) ⟨3854519, by rfl⟩ : syracuseStep 5139359 = 7709039) B7709039
theorem B105450545 : Blo 1803603 105450545 := bstep (se 2 (by rfl) ⟨39543954, by rfl⟩ : syracuseStep 105450545 = 79087909) B79087909
theorem B4058207 : Blo 1803603 4058207 := bstep (se 1 (by rfl) ⟨3043655, by rfl⟩ : syracuseStep 4058207 = 6087311) B6087311
theorem B6089903 : Blo 1803603 6089903 := bstep (se 1 (by rfl) ⟨4567427, by rfl⟩ : syracuseStep 6089903 = 9134855) B9134855
theorem B9137447 : Blo 1803603 9137447 := bstep (se 1 (by rfl) ⟨6853085, by rfl⟩ : syracuseStep 9137447 = 13706171) B13706171
theorem B4058459 : Blo 1803603 4058459 := bstep (se 1 (by rfl) ⟨3043844, by rfl⟩ : syracuseStep 4058459 = 6087689) B6087689
theorem B3427751 : Blo 1803603 3427751 := bstep (se 1 (by rfl) ⟨2570813, by rfl⟩ : syracuseStep 3427751 = 5141627) B5141627
theorem B9891323 : Blo 1803603 9891323 := bstep (se 1 (by rfl) ⟨7418492, by rfl⟩ : syracuseStep 9891323 = 14836985) B14836985
theorem B6852221 : Blo 1803603 6852221 := bstep (se 3 (by rfl) ⟨1284791, by rfl⟩ : syracuseStep 6852221 = 2569583) B2569583
theorem B8670863 : Blo 1803603 8670863 := bstep (se 1 (by rfl) ⟨6503147, by rfl⟩ : syracuseStep 8670863 = 13006295) B13006295
theorem B2707163 : Blo 1803603 2707163 := bstep (se 1 (by rfl) ⟨2030372, by rfl⟩ : syracuseStep 2707163 = 4060745) B4060745
theorem B13709087 : Blo 1803603 13709087 := bstep (se 1 (by rfl) ⟨10281815, by rfl⟩ : syracuseStep 13709087 = 20563631) B20563631
theorem B15634255 : Blo 1803603 15634255 := bstep (se 1 (by rfl) ⟨11725691, by rfl⟩ : syracuseStep 15634255 = 23451383) B23451383
theorem B5140361 : Blo 1803603 5140361 := bstep (se 2 (by rfl) ⟨1927635, by rfl⟩ : syracuseStep 5140361 = 3855271) B3855271
theorem B2707691 : Blo 1803603 2707691 := bstep (se 1 (by rfl) ⟨2030768, by rfl⟩ : syracuseStep 2707691 = 4061537) B4061537
theorem B2781479 : Blo 1803603 2781479 := bstep (se 1 (by rfl) ⟨2086109, by rfl⟩ : syracuseStep 2781479 = 4172219) B4172219
theorem B2707751 : Blo 1803603 2707751 := bstep (se 1 (by rfl) ⟨2030813, by rfl⟩ : syracuseStep 2707751 = 4061627) B4061627
theorem B9761231 : Blo 1803603 9761231 := bstep (se 1 (by rfl) ⟨7320923, by rfl⟩ : syracuseStep 9761231 = 14641847) B14641847
theorem B3854827 : Blo 1803603 3854827 := bstep (se 1 (by rfl) ⟨2891120, by rfl⟩ : syracuseStep 3854827 = 5782241) B5782241
theorem B5141387 : Blo 1803603 5141387 := bstep (se 1 (by rfl) ⟨3856040, by rfl⟩ : syracuseStep 5141387 = 7712081) B7712081
theorem B46330861 : Blo 1803603 46330861 := bstep (se 3 (by rfl) ⟨8687036, by rfl⟩ : syracuseStep 46330861 = 17374073) B17374073
theorem B9753641 : Blo 1803603 9753641 := bstep (se 2 (by rfl) ⟨3657615, by rfl⟩ : syracuseStep 9753641 = 7315231) B7315231
theorem B6091847 : Blo 1803603 6091847 := bstep (se 1 (by rfl) ⟨4568885, by rfl⟩ : syracuseStep 6091847 = 9137771) B9137771
theorem B3044479 : Blo 1803603 3044479 := bstep (se 1 (by rfl) ⟨2283359, by rfl⟩ : syracuseStep 3044479 = 4566719) B4566719
theorem B13710545 : Blo 1803603 13710545 := bstep (se 2 (by rfl) ⟨5141454, by rfl⟩ : syracuseStep 13710545 = 10282909) B10282909
theorem B4060457 : Blo 1803603 4060457 := bstep (se 2 (by rfl) ⟨1522671, by rfl⟩ : syracuseStep 4060457 = 3045343) B3045343
theorem B3044891 : Blo 1803603 3044891 := bstep (se 1 (by rfl) ⟨2283668, by rfl⟩ : syracuseStep 3044891 = 4567337) B4567337
theorem B23132141 : Blo 1803603 23132141 := bstep (se 3 (by rfl) ⟨4337276, by rfl⟩ : syracuseStep 23132141 = 8674553) B8674553
theorem B6092873 : Blo 1803603 6092873 := bstep (se 2 (by rfl) ⟨2284827, by rfl⟩ : syracuseStep 6092873 = 4569655) B4569655
theorem B9132263 : Blo 1803603 9132263 := bstep (se 1 (by rfl) ⟨6849197, by rfl⟩ : syracuseStep 9132263 = 13698395) B13698395
theorem B15628709 : Blo 1803603 15628709 := bstep (se 4 (by rfl) ⟨1465191, by rfl⟩ : syracuseStep 15628709 = 2930383) B2930383
theorem B3250631 : Blo 1803603 3250631 := bstep (se 1 (by rfl) ⟨2437973, by rfl⟩ : syracuseStep 3250631 = 4875947) B4875947
theorem B3045863 : Blo 1803603 3045863 := bstep (se 1 (by rfl) ⟨2284397, by rfl⟩ : syracuseStep 3045863 = 4568795) B4568795
theorem B52755209 : Blo 1803603 52755209 := bstep (se 2 (by rfl) ⟨19783203, by rfl⟩ : syracuseStep 52755209 = 39566407) B39566407
theorem B4569979 : Blo 1803603 4569979 := bstep (se 1 (by rfl) ⟨3427484, by rfl⟩ : syracuseStep 4569979 = 6854969) B6854969
theorem B5487689 : Blo 1803603 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B2604139 : Blo 1803603 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B4062527 : Blo 1803603 4062527 := bstep (se 1 (by rfl) ⟨3046895, by rfl⟩ : syracuseStep 4062527 = 6093791) B6093791
theorem B34684523 : Blo 1803603 34684523 := bstep (se 1 (by rfl) ⟨26013392, by rfl⟩ : syracuseStep 34684523 = 52026785) B52026785
theorem B7708391 : Blo 1803603 7708391 := bstep (se 1 (by rfl) ⟨5781293, by rfl⟩ : syracuseStep 7708391 = 11562587) B11562587
theorem B10272521 : Blo 1803603 10272521 := bstep (se 2 (by rfl) ⟨3852195, by rfl⟩ : syracuseStep 10272521 = 7704391) B7704391
theorem B51412907 : Blo 1803603 51412907 := bstep (se 1 (by rfl) ⟨38559680, by rfl⟩ : syracuseStep 51412907 = 77119361) B77119361
theorem B20562173 : Blo 1803603 20562173 := bstep (se 3 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 20562173 = 7710815) B7710815
theorem B14631235 : Blo 1803603 14631235 := bstep (se 1 (by rfl) ⟨10973426, by rfl⟩ : syracuseStep 14631235 = 21946853) B21946853
theorem B30819203 : Blo 1803603 30819203 := bstep (se 1 (by rfl) ⟨23114402, by rfl⟩ : syracuseStep 30819203 = 46228805) B46228805
theorem B6088175 : Blo 1803603 6088175 := bstep (se 1 (by rfl) ⟨4566131, by rfl⟩ : syracuseStep 6088175 = 9132263) B9132263
theorem B35170139 : Blo 1803603 35170139 := bstep (se 1 (by rfl) ⟨26377604, by rfl⟩ : syracuseStep 35170139 = 52755209) B52755209
theorem B3426239 : Blo 1803603 3426239 := bstep (se 1 (by rfl) ⟨2569679, by rfl⟩ : syracuseStep 3426239 = 5139359) B5139359
theorem B2705471 : Blo 1803603 2705471 := bstep (se 1 (by rfl) ⟨2029103, by rfl⟩ : syracuseStep 2705471 = 4058207) B4058207
theorem B2705639 : Blo 1803603 2705639 := bstep (se 1 (by rfl) ⟨2029229, by rfl⟩ : syracuseStep 2705639 = 4058459) B4058459
theorem B13707629 : Blo 1803603 13707629 := bstep (se 3 (by rfl) ⟨2570180, by rfl⟩ : syracuseStep 13707629 = 5140361) B5140361
theorem B1804775 : Blo 1803603 1804775 := bstep (se 1 (by rfl) ⟨1353581, by rfl⟩ : syracuseStep 1804775 = 2707163) B2707163
theorem B5138927 : Blo 1803603 5138927 := bstep (se 1 (by rfl) ⟨3854195, by rfl⟩ : syracuseStep 5138927 = 7708391) B7708391
theorem B281201453 : Blo 1803603 281201453 := bstep (se 3 (by rfl) ⟨52725272, by rfl⟩ : syracuseStep 281201453 = 105450545) B105450545
theorem B1805127 : Blo 1803603 1805127 := bstep (se 1 (by rfl) ⟨1353845, by rfl⟩ : syracuseStep 1805127 = 2707691) B2707691
theorem B1805167 : Blo 1803603 1805167 := bstep (se 1 (by rfl) ⟨1353875, by rfl⟩ : syracuseStep 1805167 = 2707751) B2707751
theorem B10980289 : Blo 1803603 10980289 := bstep (se 2 (by rfl) ⟨4117608, by rfl⟩ : syracuseStep 10980289 = 8235217) B8235217
theorem B6507487 : Blo 1803603 6507487 := bstep (se 1 (by rfl) ⟨4880615, by rfl⟩ : syracuseStep 6507487 = 9761231) B9761231
theorem B4566071 : Blo 1803603 4566071 := bstep (se 1 (by rfl) ⟨3424553, by rfl⟩ : syracuseStep 4566071 = 6849107) B6849107
theorem B4566203 : Blo 1803603 4566203 := bstep (se 1 (by rfl) ⟨3424652, by rfl⟩ : syracuseStep 4566203 = 6849305) B6849305
theorem B21130429 : Blo 1803603 21130429 := bstep (se 3 (by rfl) ⟨3961955, by rfl⟩ : syracuseStep 21130429 = 7923911) B7923911
theorem B13888741 : Blo 1803603 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B3427591 : Blo 1803603 3427591 := bstep (se 1 (by rfl) ⟨2570693, by rfl⟩ : syracuseStep 3427591 = 5141387) B5141387
theorem B5139769 : Blo 1803603 5139769 := bstep (se 2 (by rfl) ⟨1927413, by rfl⟩ : syracuseStep 5139769 = 3854827) B3854827
theorem B21949775 : Blo 1803603 21949775 := bstep (se 1 (by rfl) ⟨16462331, by rfl⟩ : syracuseStep 21949775 = 32924663) B32924663
theorem B7417277 : Blo 1803603 7417277 := bstep (se 3 (by rfl) ⟨1390739, by rfl⟩ : syracuseStep 7417277 = 2781479) B2781479
theorem B4058603 : Blo 1803603 4058603 := bstep (se 1 (by rfl) ⟨3043952, by rfl⟩ : syracuseStep 4058603 = 6087905) B6087905
theorem B2706971 : Blo 1803603 2706971 := bstep (se 1 (by rfl) ⟨2030228, by rfl⟩ : syracuseStep 2706971 = 4060457) B4060457
theorem B13004621 : Blo 1803603 13004621 := bstep (se 3 (by rfl) ⟨2438366, by rfl⟩ : syracuseStep 13004621 = 4876733) B4876733
theorem B4566881 : Blo 1803603 4566881 := bstep (se 2 (by rfl) ⟨1712580, by rfl⟩ : syracuseStep 4566881 = 3425161) B3425161
theorem B62533559 : Blo 1803603 62533559 := bstep (se 1 (by rfl) ⟨46900169, by rfl⟩ : syracuseStep 62533559 = 93800339) B93800339
theorem B4059071 : Blo 1803603 4059071 := bstep (se 1 (by rfl) ⟨3044303, by rfl⟩ : syracuseStep 4059071 = 6088607) B6088607
theorem B15421427 : Blo 1803603 15421427 := bstep (se 1 (by rfl) ⟨11566070, by rfl⟩ : syracuseStep 15421427 = 23132141) B23132141
theorem B4059305 : Blo 1803603 4059305 := bstep (se 2 (by rfl) ⟨1522239, by rfl⟩ : syracuseStep 4059305 = 3044479) B3044479
theorem B2167087 : Blo 1803603 2167087 := bstep (se 1 (by rfl) ⟨1625315, by rfl⟩ : syracuseStep 2167087 = 3250631) B3250631
theorem B11120975 : Blo 1803603 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B4338143 : Blo 1803603 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B5485087 : Blo 1803603 5485087 := bstep (se 1 (by rfl) ⟨4113815, by rfl⟩ : syracuseStep 5485087 = 8227631) B8227631
theorem B3658459 : Blo 1803603 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B4059935 : Blo 1803603 4059935 := bstep (se 1 (by rfl) ⟨3044951, by rfl⟩ : syracuseStep 4059935 = 6089903) B6089903
theorem B6091631 : Blo 1803603 6091631 := bstep (se 1 (by rfl) ⟨4568723, by rfl⟩ : syracuseStep 6091631 = 9137447) B9137447
theorem B2708351 : Blo 1803603 2708351 := bstep (se 1 (by rfl) ⟨2031263, by rfl⟩ : syracuseStep 2708351 = 4062527) B4062527
theorem B23123015 : Blo 1803603 23123015 := bstep (se 1 (by rfl) ⟨17342261, by rfl⟩ : syracuseStep 23123015 = 34684523) B34684523
theorem B4568147 : Blo 1803603 4568147 := bstep (se 1 (by rfl) ⟨3426110, by rfl⟩ : syracuseStep 4568147 = 6852221) B6852221
theorem B5780575 : Blo 1803603 5780575 := bstep (se 1 (by rfl) ⟨4335431, by rfl⟩ : syracuseStep 5780575 = 8670863) B8670863
theorem B20845673 : Blo 1803603 20845673 := bstep (se 2 (by rfl) ⟨7817127, by rfl⟩ : syracuseStep 20845673 = 15634255) B15634255
theorem B9139391 : Blo 1803603 9139391 := bstep (se 1 (by rfl) ⟨6854543, by rfl⟩ : syracuseStep 9139391 = 13709087) B13709087
theorem B41686903 : Blo 1803603 41686903 := bstep (se 1 (by rfl) ⟨31265177, by rfl⟩ : syracuseStep 41686903 = 62530355) B62530355
theorem B6502427 : Blo 1803603 6502427 := bstep (se 1 (by rfl) ⟨4876820, by rfl⟩ : syracuseStep 6502427 = 9753641) B9753641
theorem B2283547 : Blo 1803603 2283547 := bstep (se 1 (by rfl) ⟨1712660, by rfl⟩ : syracuseStep 2283547 = 3425321) B3425321
theorem B4061231 : Blo 1803603 4061231 := bstep (se 1 (by rfl) ⟨3045923, by rfl⟩ : syracuseStep 4061231 = 6091847) B6091847
theorem B9140363 : Blo 1803603 9140363 := bstep (se 1 (by rfl) ⟨6855272, by rfl⟩ : syracuseStep 9140363 = 13710545) B13710545
theorem B3659951 : Blo 1803603 3659951 := bstep (se 1 (by rfl) ⟨2744963, by rfl⟩ : syracuseStep 3659951 = 5489927) B5489927
theorem B2029927 : Blo 1803603 2029927 := bstep (se 1 (by rfl) ⟨1522445, by rfl⟩ : syracuseStep 2029927 = 3044891) B3044891
theorem B20846963 : Blo 1803603 20846963 := bstep (se 1 (by rfl) ⟨15635222, by rfl⟩ : syracuseStep 20846963 = 31270445) B31270445
theorem B6093305 : Blo 1803603 6093305 := bstep (se 2 (by rfl) ⟨2284989, by rfl⟩ : syracuseStep 6093305 = 4569979) B4569979
theorem B61774481 : Blo 1803603 61774481 := bstep (se 2 (by rfl) ⟨23165430, by rfl⟩ : syracuseStep 61774481 = 46330861) B46330861
theorem B4061915 : Blo 1803603 4061915 := bstep (se 1 (by rfl) ⟨3046436, by rfl⟩ : syracuseStep 4061915 = 6092873) B6092873
theorem B10419139 : Blo 1803603 10419139 := bstep (se 1 (by rfl) ⟨7814354, by rfl⟩ : syracuseStep 10419139 = 15628709) B15628709
theorem B2030575 : Blo 1803603 2030575 := bstep (se 1 (by rfl) ⟨1522931, by rfl⟩ : syracuseStep 2030575 = 3045863) B3045863
theorem B7707707 : Blo 1803603 7707707 := bstep (se 1 (by rfl) ⟨5780780, by rfl⟩ : syracuseStep 7707707 = 11561561) B11561561
theorem B27794717 : Blo 1803603 27794717 := bstep (se 3 (by rfl) ⟨5211509, by rfl⟩ : syracuseStep 27794717 = 10423019) B10423019
theorem B2285167 : Blo 1803603 2285167 := bstep (se 1 (by rfl) ⟨1713875, by rfl⟩ : syracuseStep 2285167 = 3427751) B3427751
theorem B6594215 : Blo 1803603 6594215 := bstep (se 1 (by rfl) ⟨4945661, by rfl⟩ : syracuseStep 6594215 = 9891323) B9891323
theorem B137101085 : Blo 1803603 137101085 := bstep (se 3 (by rfl) ⟨25706453, by rfl⟩ : syracuseStep 137101085 = 51412907) B51412907
theorem B6848347 : Blo 1803603 6848347 := bstep (se 1 (by rfl) ⟨5136260, by rfl⟩ : syracuseStep 6848347 = 10272521) B10272521
theorem B7413983 : Blo 1803603 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B2892095 : Blo 1803603 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B20546135 : Blo 1803603 20546135 := bstep (se 1 (by rfl) ⟨15409601, by rfl⟩ : syracuseStep 20546135 = 30819203) B30819203
theorem B23446759 : Blo 1803603 23446759 := bstep (se 1 (by rfl) ⟨17585069, by rfl⟩ : syracuseStep 23446759 = 35170139) B35170139
theorem B8676649 : Blo 1803603 8676649 := bstep (se 2 (by rfl) ⟨3253743, by rfl⟩ : syracuseStep 8676649 = 6507487) B6507487
theorem B4334951 : Blo 1803603 4334951 := bstep (se 1 (by rfl) ⟨3251213, by rfl⟩ : syracuseStep 4334951 = 6502427) B6502427
theorem B1803647 : Blo 1803603 1803647 := bstep (se 1 (by rfl) ⟨1352735, by rfl⟩ : syracuseStep 1803647 = 2705471) B2705471
theorem B1803759 : Blo 1803603 1803759 := bstep (se 1 (by rfl) ⟨1352819, by rfl⟩ : syracuseStep 1803759 = 2705639) B2705639
theorem B28173905 : Blo 1803603 28173905 := bstep (se 2 (by rfl) ⟨10565214, by rfl⟩ : syracuseStep 28173905 = 21130429) B21130429
theorem B3425951 : Blo 1803603 3425951 := bstep (se 1 (by rfl) ⟨2569463, by rfl⟩ : syracuseStep 3425951 = 5138927) B5138927
theorem B41182987 : Blo 1803603 41182987 := bstep (se 1 (by rfl) ⟨30887240, by rfl⟩ : syracuseStep 41182987 = 61774481) B61774481
theorem B187467635 : Blo 1803603 187467635 := bstep (se 1 (by rfl) ⟨140600726, by rfl⟩ : syracuseStep 187467635 = 281201453) B281201453
theorem B5138471 : Blo 1803603 5138471 := bstep (se 1 (by rfl) ⟨3853853, by rfl⟩ : syracuseStep 5138471 = 7707707) B7707707
theorem B14633183 : Blo 1803603 14633183 := bstep (se 1 (by rfl) ⟨10974887, by rfl⟩ : syracuseStep 14633183 = 21949775) B21949775
theorem B2705735 : Blo 1803603 2705735 := bstep (se 1 (by rfl) ⟨2029301, by rfl⟩ : syracuseStep 2705735 = 4058603) B4058603
theorem B1804647 : Blo 1803603 1804647 := bstep (se 1 (by rfl) ⟨1353485, by rfl⟩ : syracuseStep 1804647 = 2706971) B2706971
theorem B9136637 : Blo 1803603 9136637 := bstep (se 3 (by rfl) ⟨1713119, by rfl⟩ : syracuseStep 9136637 = 3426239) B3426239
theorem B91400723 : Blo 1803603 91400723 := bstep (se 1 (by rfl) ⟨68550542, by rfl⟩ : syracuseStep 91400723 = 137101085) B137101085
theorem B8669747 : Blo 1803603 8669747 := bstep (se 1 (by rfl) ⟨6502310, by rfl⟩ : syracuseStep 8669747 = 13004621) B13004621
theorem B2706047 : Blo 1803603 2706047 := bstep (se 1 (by rfl) ⟨2029535, by rfl⟩ : syracuseStep 2706047 = 4059071) B4059071
theorem B2706203 : Blo 1803603 2706203 := bstep (se 1 (by rfl) ⟨2029652, by rfl⟩ : syracuseStep 2706203 = 4059305) B4059305
theorem B13708115 : Blo 1803603 13708115 := bstep (se 1 (by rfl) ⟨10281086, by rfl⟩ : syracuseStep 13708115 = 20562173) B20562173
theorem B2706569 : Blo 1803603 2706569 := bstep (se 2 (by rfl) ⟨1014963, by rfl⟩ : syracuseStep 2706569 = 2029927) B2029927
theorem B2706623 : Blo 1803603 2706623 := bstep (se 1 (by rfl) ⟨2029967, by rfl⟩ : syracuseStep 2706623 = 4059935) B4059935
theorem B1805567 : Blo 1803603 1805567 := bstep (se 1 (by rfl) ⟨1354175, by rfl⟩ : syracuseStep 1805567 = 2708351) B2708351
theorem B13897115 : Blo 1803603 13897115 := bstep (se 1 (by rfl) ⟨10422836, by rfl⟩ : syracuseStep 13897115 = 20845673) B20845673
theorem B4877945 : Blo 1803603 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B4058783 : Blo 1803603 4058783 := bstep (se 1 (by rfl) ⟨3044087, by rfl⟩ : syracuseStep 4058783 = 6088175) B6088175
theorem B2707433 : Blo 1803603 2707433 := bstep (se 2 (by rfl) ⟨1015287, by rfl⟩ : syracuseStep 2707433 = 2030575) B2030575
theorem B2707487 : Blo 1803603 2707487 := bstep (se 1 (by rfl) ⟨2030615, by rfl⟩ : syracuseStep 2707487 = 4061231) B4061231
theorem B9138419 : Blo 1803603 9138419 := bstep (se 1 (by rfl) ⟨6853814, by rfl⟩ : syracuseStep 9138419 = 13707629) B13707629
theorem B13897975 : Blo 1803603 13897975 := bstep (se 1 (by rfl) ⟨10423481, by rfl⟩ : syracuseStep 13897975 = 20846963) B20846963
theorem B18518321 : Blo 1803603 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B78033253 : Blo 1803603 78033253 := bstep (se 4 (by rfl) ⟨7315617, by rfl⟩ : syracuseStep 78033253 = 14631235) B14631235
theorem B6853025 : Blo 1803603 6853025 := bstep (se 2 (by rfl) ⟨2569884, by rfl⟩ : syracuseStep 6853025 = 5139769) B5139769
theorem B17584573 : Blo 1803603 17584573 := bstep (se 3 (by rfl) ⟨3297107, by rfl⟩ : syracuseStep 17584573 = 6594215) B6594215
theorem B2707943 : Blo 1803603 2707943 := bstep (se 1 (by rfl) ⟨2030957, by rfl⟩ : syracuseStep 2707943 = 4061915) B4061915
theorem B3044047 : Blo 1803603 3044047 := bstep (se 1 (by rfl) ⟨2283035, by rfl⟩ : syracuseStep 3044047 = 4566071) B4566071
theorem B3044135 : Blo 1803603 3044135 := bstep (se 1 (by rfl) ⟨2283101, by rfl⟩ : syracuseStep 3044135 = 4566203) B4566203
theorem B4944851 : Blo 1803603 4944851 := bstep (se 1 (by rfl) ⟨3708638, by rfl⟩ : syracuseStep 4944851 = 7417277) B7417277
theorem B58561541 : Blo 1803603 58561541 := bstep (se 4 (by rfl) ⟨5490144, by rfl⟩ : syracuseStep 58561541 = 10980289) B10980289
theorem B9131129 : Blo 1803603 9131129 := bstep (se 2 (by rfl) ⟨3424173, by rfl⟩ : syracuseStep 9131129 = 6848347) B6848347
theorem B3044587 : Blo 1803603 3044587 := bstep (se 1 (by rfl) ⟨2283440, by rfl⟩ : syracuseStep 3044587 = 4566881) B4566881
theorem B3044729 : Blo 1803603 3044729 := bstep (se 2 (by rfl) ⟨1141773, by rfl⟩ : syracuseStep 3044729 = 2283547) B2283547
theorem B2889449 : Blo 1803603 2889449 := bstep (se 2 (by rfl) ⟨1083543, by rfl⟩ : syracuseStep 2889449 = 2167087) B2167087
theorem B4061087 : Blo 1803603 4061087 := bstep (se 1 (by rfl) ⟨3045815, by rfl⟩ : syracuseStep 4061087 = 6091631) B6091631
theorem B7313449 : Blo 1803603 7313449 := bstep (se 2 (by rfl) ⟨2742543, by rfl⟩ : syracuseStep 7313449 = 5485087) B5485087
theorem B15415343 : Blo 1803603 15415343 := bstep (se 1 (by rfl) ⟨11561507, by rfl⟩ : syracuseStep 15415343 = 23123015) B23123015
theorem B3045431 : Blo 1803603 3045431 := bstep (se 1 (by rfl) ⟨2284073, by rfl⟩ : syracuseStep 3045431 = 4568147) B4568147
theorem B6092927 : Blo 1803603 6092927 := bstep (se 1 (by rfl) ⟨4569695, by rfl⟩ : syracuseStep 6092927 = 9139391) B9139391
theorem B13892185 : Blo 1803603 13892185 := bstep (se 2 (by rfl) ⟨5209569, by rfl⟩ : syracuseStep 13892185 = 10419139) B10419139
theorem B6093575 : Blo 1803603 6093575 := bstep (se 1 (by rfl) ⟨4570181, by rfl⟩ : syracuseStep 6093575 = 9140363) B9140363
theorem B2439967 : Blo 1803603 2439967 := bstep (se 1 (by rfl) ⟨1829975, by rfl⟩ : syracuseStep 2439967 = 3659951) B3659951
theorem B7707433 : Blo 1803603 7707433 := bstep (se 2 (by rfl) ⟨2890287, by rfl⟩ : syracuseStep 7707433 = 5780575) B5780575
theorem B4062203 : Blo 1803603 4062203 := bstep (se 1 (by rfl) ⟨3046652, by rfl⟩ : syracuseStep 4062203 = 6093305) B6093305
theorem B4570121 : Blo 1803603 4570121 := bstep (se 2 (by rfl) ⟨1713795, by rfl⟩ : syracuseStep 4570121 = 3427591) B3427591
theorem B3046889 : Blo 1803603 3046889 := bstep (se 2 (by rfl) ⟨1142583, by rfl⟩ : syracuseStep 3046889 = 2285167) B2285167
theorem B18529811 : Blo 1803603 18529811 := bstep (se 1 (by rfl) ⟨13897358, by rfl⟩ : syracuseStep 18529811 = 27794717) B27794717
theorem B55582537 : Blo 1803603 55582537 := bstep (se 2 (by rfl) ⟨20843451, by rfl⟩ : syracuseStep 55582537 = 41686903) B41686903
theorem B41689039 : Blo 1803603 41689039 := bstep (se 1 (by rfl) ⟨31266779, by rfl⟩ : syracuseStep 41689039 = 62533559) B62533559
theorem B10280951 : Blo 1803603 10280951 := bstep (se 1 (by rfl) ⟨7710713, by rfl⟩ : syracuseStep 10280951 = 15421427) B15421427
theorem B12345547 : Blo 1803603 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B18530633 : Blo 1803603 18530633 := bstep (se 2 (by rfl) ⟨6948987, by rfl⟩ : syracuseStep 18530633 = 13897975) B13897975
theorem B13697423 : Blo 1803603 13697423 := bstep (se 1 (by rfl) ⟨10273067, by rfl⟩ : syracuseStep 13697423 = 20546135) B20546135
theorem B23446097 : Blo 1803603 23446097 := bstep (se 2 (by rfl) ⟨8792286, by rfl⟩ : syracuseStep 23446097 = 17584573) B17584573
theorem B6087419 : Blo 1803603 6087419 := bstep (se 1 (by rfl) ⟨4565564, by rfl⟩ : syracuseStep 6087419 = 9131129) B9131129
theorem B18522913 : Blo 1803603 18522913 := bstep (se 2 (by rfl) ⟨6946092, by rfl⟩ : syracuseStep 18522913 = 13892185) B13892185
theorem B3253289 : Blo 1803603 3253289 := bstep (se 2 (by rfl) ⟨1219983, by rfl⟩ : syracuseStep 3253289 = 2439967) B2439967
theorem B1926299 : Blo 1803603 1926299 := bstep (se 1 (by rfl) ⟨1444724, by rfl⟩ : syracuseStep 1926299 = 2889449) B2889449
theorem B124978423 : Blo 1803603 124978423 := bstep (se 1 (by rfl) ⟨93733817, by rfl⟩ : syracuseStep 124978423 = 187467635) B187467635
theorem B3425647 : Blo 1803603 3425647 := bstep (se 1 (by rfl) ⟨2569235, by rfl⟩ : syracuseStep 3425647 = 5138471) B5138471
theorem B1803823 : Blo 1803603 1803823 := bstep (se 1 (by rfl) ⟨1352867, by rfl⟩ : syracuseStep 1803823 = 2705735) B2705735
theorem B31262345 : Blo 1803603 31262345 := bstep (se 2 (by rfl) ⟨11723379, by rfl⟩ : syracuseStep 31262345 = 23446759) B23446759
theorem B60933815 : Blo 1803603 60933815 := bstep (se 1 (by rfl) ⟨45700361, by rfl⟩ : syracuseStep 60933815 = 91400723) B91400723
theorem B11568865 : Blo 1803603 11568865 := bstep (se 2 (by rfl) ⟨4338324, by rfl⟩ : syracuseStep 11568865 = 8676649) B8676649
theorem B1804031 : Blo 1803603 1804031 := bstep (se 1 (by rfl) ⟨1353023, by rfl⟩ : syracuseStep 1804031 = 2706047) B2706047
theorem B1804135 : Blo 1803603 1804135 := bstep (se 1 (by rfl) ⟨1353101, by rfl⟩ : syracuseStep 1804135 = 2706203) B2706203
theorem B1804379 : Blo 1803603 1804379 := bstep (se 1 (by rfl) ⟨1353284, by rfl⟩ : syracuseStep 1804379 = 2706569) B2706569
theorem B1804415 : Blo 1803603 1804415 := bstep (se 1 (by rfl) ⟨1353311, by rfl⟩ : syracuseStep 1804415 = 2706623) B2706623
theorem B2705855 : Blo 1803603 2705855 := bstep (se 1 (by rfl) ⟨2029391, by rfl⟩ : syracuseStep 2705855 = 4058783) B4058783
theorem B55585385 : Blo 1803603 55585385 := bstep (se 2 (by rfl) ⟨20844519, by rfl⟩ : syracuseStep 55585385 = 41689039) B41689039
theorem B1804955 : Blo 1803603 1804955 := bstep (se 1 (by rfl) ⟨1353716, by rfl⟩ : syracuseStep 1804955 = 2707433) B2707433
theorem B1804991 : Blo 1803603 1804991 := bstep (se 1 (by rfl) ⟨1353743, by rfl⟩ : syracuseStep 1804991 = 2707487) B2707487
theorem B9751265 : Blo 1803603 9751265 := bstep (se 2 (by rfl) ⟨3656724, by rfl⟩ : syracuseStep 9751265 = 7313449) B7313449
theorem B4942655 : Blo 1803603 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B1928063 : Blo 1803603 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B1805295 : Blo 1803603 1805295 := bstep (se 1 (by rfl) ⟨1353971, by rfl⟩ : syracuseStep 1805295 = 2707943) B2707943
theorem B39021821 : Blo 1803603 39021821 := bstep (se 3 (by rfl) ⟨7316591, by rfl⟩ : syracuseStep 39021821 = 14633183) B14633183
theorem B3296567 : Blo 1803603 3296567 := bstep (se 1 (by rfl) ⟨2472425, by rfl⟩ : syracuseStep 3296567 = 4944851) B4944851
theorem B4058729 : Blo 1803603 4058729 := bstep (se 2 (by rfl) ⟨1522023, by rfl⟩ : syracuseStep 4058729 = 3044047) B3044047
theorem B10276577 : Blo 1803603 10276577 := bstep (se 2 (by rfl) ⟨3853716, by rfl⟩ : syracuseStep 10276577 = 7707433) B7707433
theorem B2707391 : Blo 1803603 2707391 := bstep (se 1 (by rfl) ⟨2030543, by rfl⟩ : syracuseStep 2707391 = 4061087) B4061087
theorem B10276895 : Blo 1803603 10276895 := bstep (se 1 (by rfl) ⟨7707671, by rfl⟩ : syracuseStep 10276895 = 15415343) B15415343
theorem B4059449 : Blo 1803603 4059449 := bstep (se 2 (by rfl) ⟨1522293, by rfl⟩ : syracuseStep 4059449 = 3044587) B3044587
theorem B6091091 : Blo 1803603 6091091 := bstep (se 1 (by rfl) ⟨4568318, by rfl⟩ : syracuseStep 6091091 = 9136637) B9136637
theorem B5779831 : Blo 1803603 5779831 := bstep (se 1 (by rfl) ⟨4334873, by rfl⟩ : syracuseStep 5779831 = 8669747) B8669747
theorem B9138743 : Blo 1803603 9138743 := bstep (se 1 (by rfl) ⟨6854057, by rfl⟩ : syracuseStep 9138743 = 13708115) B13708115
theorem B2708135 : Blo 1803603 2708135 := bstep (se 1 (by rfl) ⟨2031101, by rfl⟩ : syracuseStep 2708135 = 4062203) B4062203
theorem B74110049 : Blo 1803603 74110049 := bstep (se 2 (by rfl) ⟨27791268, by rfl⟩ : syracuseStep 74110049 = 55582537) B55582537
theorem B6853967 : Blo 1803603 6853967 := bstep (se 1 (by rfl) ⟨5140475, by rfl⟩ : syracuseStep 6853967 = 10280951) B10280951
theorem B6092279 : Blo 1803603 6092279 := bstep (se 1 (by rfl) ⟨4569209, by rfl⟩ : syracuseStep 6092279 = 9138419) B9138419
theorem B4568683 : Blo 1803603 4568683 := bstep (se 1 (by rfl) ⟨3426512, by rfl⟩ : syracuseStep 4568683 = 6853025) B6853025
theorem B104044337 : Blo 1803603 104044337 := bstep (se 2 (by rfl) ⟨39016626, by rfl⟩ : syracuseStep 104044337 = 78033253) B78033253
theorem B2029423 : Blo 1803603 2029423 := bstep (se 1 (by rfl) ⟨1522067, by rfl⟩ : syracuseStep 2029423 = 3044135) B3044135
theorem B39041027 : Blo 1803603 39041027 := bstep (se 1 (by rfl) ⟨29280770, by rfl⟩ : syracuseStep 39041027 = 58561541) B58561541
theorem B2889967 : Blo 1803603 2889967 := bstep (se 1 (by rfl) ⟨2167475, by rfl⟩ : syracuseStep 2889967 = 4334951) B4334951
theorem B2029819 : Blo 1803603 2029819 := bstep (se 1 (by rfl) ⟨1522364, by rfl⟩ : syracuseStep 2029819 = 3044729) B3044729
theorem B18782603 : Blo 1803603 18782603 := bstep (se 1 (by rfl) ⟨14086952, by rfl⟩ : syracuseStep 18782603 = 28173905) B28173905
theorem B2283967 : Blo 1803603 2283967 := bstep (se 1 (by rfl) ⟨1712975, by rfl⟩ : syracuseStep 2283967 = 3425951) B3425951
theorem B2030287 : Blo 1803603 2030287 := bstep (se 1 (by rfl) ⟨1522715, by rfl⟩ : syracuseStep 2030287 = 3045431) B3045431
theorem B4061951 : Blo 1803603 4061951 := bstep (se 1 (by rfl) ⟨3046463, by rfl⟩ : syracuseStep 4061951 = 6092927) B6092927
theorem B4062383 : Blo 1803603 4062383 := bstep (se 1 (by rfl) ⟨3046787, by rfl⟩ : syracuseStep 4062383 = 6093575) B6093575
theorem B3046747 : Blo 1803603 3046747 := bstep (se 1 (by rfl) ⟨2285060, by rfl⟩ : syracuseStep 3046747 = 4570121) B4570121
theorem B9264743 : Blo 1803603 9264743 := bstep (se 1 (by rfl) ⟨6948557, by rfl⟩ : syracuseStep 9264743 = 13897115) B13897115
theorem B2031259 : Blo 1803603 2031259 := bstep (se 1 (by rfl) ⟨1523444, by rfl⟩ : syracuseStep 2031259 = 3046889) B3046889
theorem B12353207 : Blo 1803603 12353207 := bstep (se 1 (by rfl) ⟨9264905, by rfl⟩ : syracuseStep 12353207 = 18529811) B18529811
theorem B54910649 : Blo 1803603 54910649 := bstep (se 2 (by rfl) ⟨20591493, by rfl⟩ : syracuseStep 54910649 = 41182987) B41182987
theorem B3251963 : Blo 1803603 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B8675437 : Blo 1803603 8675437 := bstep (se 3 (by rfl) ⟨1626644, by rfl⟩ : syracuseStep 8675437 = 3253289) B3253289
theorem B15630731 : Blo 1803603 15630731 := bstep (se 1 (by rfl) ⟨11723048, by rfl⟩ : syracuseStep 15630731 = 23446097) B23446097
theorem B5136797 : Blo 1803603 5136797 := bstep (se 3 (by rfl) ⟨963149, by rfl⟩ : syracuseStep 5136797 = 1926299) B1926299
theorem B49406699 : Blo 1803603 49406699 := bstep (se 1 (by rfl) ⟨37055024, by rfl⟩ : syracuseStep 49406699 = 74110049) B74110049
theorem B49415021 : Blo 1803603 49415021 := bstep (se 3 (by rfl) ⟨9265316, by rfl⟩ : syracuseStep 49415021 = 18530633) B18530633
theorem B20841563 : Blo 1803603 20841563 := bstep (se 1 (by rfl) ⟨15631172, by rfl⟩ : syracuseStep 20841563 = 31262345) B31262345
theorem B69362891 : Blo 1803603 69362891 := bstep (se 1 (by rfl) ⟨52022168, by rfl⟩ : syracuseStep 69362891 = 104044337) B104044337
theorem B26027351 : Blo 1803603 26027351 := bstep (se 1 (by rfl) ⟨19520513, by rfl⟩ : syracuseStep 26027351 = 39041027) B39041027
theorem B1803903 : Blo 1803603 1803903 := bstep (se 1 (by rfl) ⟨1352927, by rfl⟩ : syracuseStep 1803903 = 2705855) B2705855
theorem B32941885 : Blo 1803603 32941885 := bstep (se 3 (by rfl) ⟨6176603, by rfl⟩ : syracuseStep 32941885 = 12353207) B12353207
theorem B3295103 : Blo 1803603 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B2197711 : Blo 1803603 2197711 := bstep (se 1 (by rfl) ⟨1648283, by rfl⟩ : syracuseStep 2197711 = 3296567) B3296567
theorem B2705819 : Blo 1803603 2705819 := bstep (se 1 (by rfl) ⟨2029364, by rfl⟩ : syracuseStep 2705819 = 4058729) B4058729
theorem B2705897 : Blo 1803603 2705897 := bstep (se 2 (by rfl) ⟨1014711, by rfl⟩ : syracuseStep 2705897 = 2029423) B2029423
theorem B6851051 : Blo 1803603 6851051 := bstep (se 1 (by rfl) ⟨5138288, by rfl⟩ : syracuseStep 6851051 = 10276577) B10276577
theorem B1804927 : Blo 1803603 1804927 := bstep (se 1 (by rfl) ⟨1353695, by rfl⟩ : syracuseStep 1804927 = 2707391) B2707391
theorem B6851263 : Blo 1803603 6851263 := bstep (se 1 (by rfl) ⟨5138447, by rfl⟩ : syracuseStep 6851263 = 10276895) B10276895
theorem B2706299 : Blo 1803603 2706299 := bstep (se 1 (by rfl) ⟨2029724, by rfl⟩ : syracuseStep 2706299 = 4059449) B4059449
theorem B16460729 : Blo 1803603 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B3853289 : Blo 1803603 3853289 := bstep (se 2 (by rfl) ⟨1444983, by rfl⟩ : syracuseStep 3853289 = 2889967) B2889967
theorem B2706425 : Blo 1803603 2706425 := bstep (se 2 (by rfl) ⟨1014909, by rfl⟩ : syracuseStep 2706425 = 2029819) B2029819
theorem B1805423 : Blo 1803603 1805423 := bstep (se 1 (by rfl) ⟨1354067, by rfl⟩ : syracuseStep 1805423 = 2708135) B2708135
theorem B4058279 : Blo 1803603 4058279 := bstep (se 1 (by rfl) ⟨3043709, by rfl⟩ : syracuseStep 4058279 = 6087419) B6087419
theorem B2707049 : Blo 1803603 2707049 := bstep (se 2 (by rfl) ⟨1015143, by rfl⟩ : syracuseStep 2707049 = 2030287) B2030287
theorem B12521735 : Blo 1803603 12521735 := bstep (se 1 (by rfl) ⟨9391301, by rfl⟩ : syracuseStep 12521735 = 18782603) B18782603
theorem B166637897 : Blo 1803603 166637897 := bstep (se 2 (by rfl) ⟨62489211, by rfl⟩ : syracuseStep 166637897 = 124978423) B124978423
theorem B37056923 : Blo 1803603 37056923 := bstep (se 1 (by rfl) ⟨27792692, by rfl⟩ : syracuseStep 37056923 = 55585385) B55585385
theorem B4567529 : Blo 1803603 4567529 := bstep (se 2 (by rfl) ⟨1712823, by rfl⟩ : syracuseStep 4567529 = 3425647) B3425647
theorem B6500843 : Blo 1803603 6500843 := bstep (se 1 (by rfl) ⟨4875632, by rfl⟩ : syracuseStep 6500843 = 9751265) B9751265
theorem B2707967 : Blo 1803603 2707967 := bstep (se 1 (by rfl) ⟨2030975, by rfl⟩ : syracuseStep 2707967 = 4061951) B4061951
theorem B2708255 : Blo 1803603 2708255 := bstep (se 1 (by rfl) ⟨2031191, by rfl⟩ : syracuseStep 2708255 = 4062383) B4062383
theorem B6091577 : Blo 1803603 6091577 := bstep (se 2 (by rfl) ⟨2284341, by rfl⟩ : syracuseStep 6091577 = 4568683) B4568683
theorem B26014547 : Blo 1803603 26014547 := bstep (se 1 (by rfl) ⟨19510910, by rfl⟩ : syracuseStep 26014547 = 39021821) B39021821
theorem B2708345 : Blo 1803603 2708345 := bstep (se 2 (by rfl) ⟨1015629, by rfl⟩ : syracuseStep 2708345 = 2031259) B2031259
theorem B5141501 : Blo 1803603 5141501 := bstep (se 3 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 5141501 = 1928063) B1928063
theorem B36607099 : Blo 1803603 36607099 := bstep (se 1 (by rfl) ⟨27455324, by rfl⟩ : syracuseStep 36607099 = 54910649) B54910649
theorem B2167975 : Blo 1803603 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B4060727 : Blo 1803603 4060727 := bstep (se 1 (by rfl) ⟨3045545, by rfl⟩ : syracuseStep 4060727 = 6091091) B6091091
theorem B9131615 : Blo 1803603 9131615 := bstep (se 1 (by rfl) ⟨6848711, by rfl⟩ : syracuseStep 9131615 = 13697423) B13697423
theorem B6092495 : Blo 1803603 6092495 := bstep (se 1 (by rfl) ⟨4569371, by rfl⟩ : syracuseStep 6092495 = 9138743) B9138743
theorem B7706441 : Blo 1803603 7706441 := bstep (se 2 (by rfl) ⟨2889915, by rfl⟩ : syracuseStep 7706441 = 5779831) B5779831
theorem B3045289 : Blo 1803603 3045289 := bstep (se 2 (by rfl) ⟨1141983, by rfl⟩ : syracuseStep 3045289 = 2283967) B2283967
theorem B4569311 : Blo 1803603 4569311 := bstep (se 1 (by rfl) ⟨3426983, by rfl⟩ : syracuseStep 4569311 = 6853967) B6853967
theorem B4061519 : Blo 1803603 4061519 := bstep (se 1 (by rfl) ⟨3046139, by rfl⟩ : syracuseStep 4061519 = 6092279) B6092279
theorem B24697217 : Blo 1803603 24697217 := bstep (se 2 (by rfl) ⟨9261456, by rfl⟩ : syracuseStep 24697217 = 18522913) B18522913
theorem B40622543 : Blo 1803603 40622543 := bstep (se 1 (by rfl) ⟨30466907, by rfl⟩ : syracuseStep 40622543 = 60933815) B60933815
theorem B4062329 : Blo 1803603 4062329 := bstep (se 2 (by rfl) ⟨1523373, by rfl⟩ : syracuseStep 4062329 = 3046747) B3046747
theorem B15425153 : Blo 1803603 15425153 := bstep (se 2 (by rfl) ⟨5784432, by rfl⟩ : syracuseStep 15425153 = 11568865) B11568865
theorem B6176495 : Blo 1803603 6176495 := bstep (se 1 (by rfl) ⟨4632371, by rfl⟩ : syracuseStep 6176495 = 9264743) B9264743
theorem B11567249 : Blo 1803603 11567249 := bstep (se 2 (by rfl) ⟨4337718, by rfl⟩ : syracuseStep 11567249 = 8675437) B8675437
theorem B8347823 : Blo 1803603 8347823 := bstep (se 1 (by rfl) ⟨6260867, by rfl⟩ : syracuseStep 8347823 = 12521735) B12521735
theorem B111091931 : Blo 1803603 111091931 := bstep (se 1 (by rfl) ⟨83318948, by rfl⟩ : syracuseStep 111091931 = 166637897) B166637897
theorem B10420487 : Blo 1803603 10420487 := bstep (se 1 (by rfl) ⟨7815365, by rfl⟩ : syracuseStep 10420487 = 15630731) B15630731
theorem B3424531 : Blo 1803603 3424531 := bstep (se 1 (by rfl) ⟨2568398, by rfl⟩ : syracuseStep 3424531 = 5136797) B5136797
theorem B4333895 : Blo 1803603 4333895 := bstep (se 1 (by rfl) ⟨3250421, by rfl⟩ : syracuseStep 4333895 = 6500843) B6500843
theorem B17343031 : Blo 1803603 17343031 := bstep (se 1 (by rfl) ⟨13007273, by rfl⟩ : syracuseStep 17343031 = 26014547) B26014547
theorem B17351567 : Blo 1803603 17351567 := bstep (se 1 (by rfl) ⟨13013675, by rfl⟩ : syracuseStep 17351567 = 26027351) B26027351
theorem B9135017 : Blo 1803603 9135017 := bstep (se 2 (by rfl) ⟨3425631, by rfl⟩ : syracuseStep 9135017 = 6851263) B6851263
theorem B6087743 : Blo 1803603 6087743 := bstep (se 1 (by rfl) ⟨4565807, by rfl⟩ : syracuseStep 6087743 = 9131615) B9131615
theorem B48809465 : Blo 1803603 48809465 := bstep (se 2 (by rfl) ⟨18303549, by rfl⟩ : syracuseStep 48809465 = 36607099) B36607099
theorem B1803879 : Blo 1803603 1803879 := bstep (se 1 (by rfl) ⟨1352909, by rfl⟩ : syracuseStep 1803879 = 2705819) B2705819
theorem B1803931 : Blo 1803603 1803931 := bstep (se 1 (by rfl) ⟨1352948, by rfl⟩ : syracuseStep 1803931 = 2705897) B2705897
theorem B1804199 : Blo 1803603 1804199 := bstep (se 1 (by rfl) ⟨1353149, by rfl⟩ : syracuseStep 1804199 = 2706299) B2706299
theorem B1804283 : Blo 1803603 1804283 := bstep (se 1 (by rfl) ⟨1353212, by rfl⟩ : syracuseStep 1804283 = 2706425) B2706425
theorem B2705519 : Blo 1803603 2705519 := bstep (se 1 (by rfl) ⟨2029139, by rfl⟩ : syracuseStep 2705519 = 4058279) B4058279
theorem B1804699 : Blo 1803603 1804699 := bstep (se 1 (by rfl) ⟨1353524, by rfl⟩ : syracuseStep 1804699 = 2707049) B2707049
theorem B10283435 : Blo 1803603 10283435 := bstep (se 1 (by rfl) ⟨7712576, by rfl⟩ : syracuseStep 10283435 = 15425153) B15425153
theorem B10275437 : Blo 1803603 10275437 := bstep (se 3 (by rfl) ⟨1926644, by rfl⟩ : syracuseStep 10275437 = 3853289) B3853289
theorem B55577501 : Blo 1803603 55577501 := bstep (se 3 (by rfl) ⟨10420781, by rfl⟩ : syracuseStep 55577501 = 20841563) B20841563
theorem B1805311 : Blo 1803603 1805311 := bstep (se 1 (by rfl) ⟨1353983, by rfl⟩ : syracuseStep 1805311 = 2707967) B2707967
theorem B1805503 : Blo 1803603 1805503 := bstep (se 1 (by rfl) ⟨1354127, by rfl⟩ : syracuseStep 1805503 = 2708255) B2708255
theorem B32943347 : Blo 1803603 32943347 := bstep (se 1 (by rfl) ⟨24707510, by rfl⟩ : syracuseStep 32943347 = 49415021) B49415021
theorem B1805563 : Blo 1803603 1805563 := bstep (se 1 (by rfl) ⟨1354172, by rfl⟩ : syracuseStep 1805563 = 2708345) B2708345
theorem B3427667 : Blo 1803603 3427667 := bstep (se 1 (by rfl) ⟨2570750, by rfl⟩ : syracuseStep 3427667 = 5141501) B5141501
theorem B11562533 : Blo 1803603 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B2707151 : Blo 1803603 2707151 := bstep (se 1 (by rfl) ⟨2030363, by rfl⟩ : syracuseStep 2707151 = 4060727) B4060727
theorem B35147765 : Blo 1803603 35147765 := bstep (se 5 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 35147765 = 3295103) B3295103
theorem B2707679 : Blo 1803603 2707679 := bstep (se 1 (by rfl) ⟨2030759, by rfl⟩ : syracuseStep 2707679 = 4061519) B4061519
theorem B4567367 : Blo 1803603 4567367 := bstep (se 1 (by rfl) ⟨3425525, by rfl⟩ : syracuseStep 4567367 = 6851051) B6851051
theorem B10973819 : Blo 1803603 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B2708219 : Blo 1803603 2708219 := bstep (se 1 (by rfl) ⟨2031164, by rfl⟩ : syracuseStep 2708219 = 4062329) B4062329
theorem B20550509 : Blo 1803603 20550509 := bstep (se 3 (by rfl) ⟨3853220, by rfl⟩ : syracuseStep 20550509 = 7706441) B7706441
theorem B43922513 : Blo 1803603 43922513 := bstep (se 2 (by rfl) ⟨16470942, by rfl⟩ : syracuseStep 43922513 = 32941885) B32941885
theorem B4117663 : Blo 1803603 4117663 := bstep (se 1 (by rfl) ⟨3088247, by rfl⟩ : syracuseStep 4117663 = 6176495) B6176495
theorem B4060385 : Blo 1803603 4060385 := bstep (se 2 (by rfl) ⟨1522644, by rfl⟩ : syracuseStep 4060385 = 3045289) B3045289
theorem B24704615 : Blo 1803603 24704615 := bstep (se 1 (by rfl) ⟨18528461, by rfl⟩ : syracuseStep 24704615 = 37056923) B37056923
theorem B3045019 : Blo 1803603 3045019 := bstep (se 1 (by rfl) ⟨2283764, by rfl⟩ : syracuseStep 3045019 = 4567529) B4567529
theorem B32937799 : Blo 1803603 32937799 := bstep (se 1 (by rfl) ⟨24703349, by rfl⟩ : syracuseStep 32937799 = 49406699) B49406699
theorem B4061051 : Blo 1803603 4061051 := bstep (se 1 (by rfl) ⟨3045788, by rfl⟩ : syracuseStep 4061051 = 6091577) B6091577
theorem B46241927 : Blo 1803603 46241927 := bstep (se 1 (by rfl) ⟨34681445, by rfl⟩ : syracuseStep 46241927 = 69362891) B69362891
theorem B11721125 : Blo 1803603 11721125 := bstep (se 4 (by rfl) ⟨1098855, by rfl⟩ : syracuseStep 11721125 = 2197711) B2197711
theorem B4061663 : Blo 1803603 4061663 := bstep (se 1 (by rfl) ⟨3046247, by rfl⟩ : syracuseStep 4061663 = 6092495) B6092495
theorem B3046207 : Blo 1803603 3046207 := bstep (se 1 (by rfl) ⟨2284655, by rfl⟩ : syracuseStep 3046207 = 4569311) B4569311
theorem B16464811 : Blo 1803603 16464811 := bstep (se 1 (by rfl) ⟨12348608, by rfl⟩ : syracuseStep 16464811 = 24697217) B24697217
theorem B27081695 : Blo 1803603 27081695 := bstep (se 1 (by rfl) ⟨20311271, by rfl⟩ : syracuseStep 27081695 = 40622543) B40622543
theorem B6946991 : Blo 1803603 6946991 := bstep (se 1 (by rfl) ⟨5210243, by rfl⟩ : syracuseStep 6946991 = 10420487) B10420487
theorem B11567711 : Blo 1803603 11567711 := bstep (se 1 (by rfl) ⟨8675783, by rfl⟩ : syracuseStep 11567711 = 17351567) B17351567
theorem B32539643 : Blo 1803603 32539643 := bstep (se 1 (by rfl) ⟨24404732, by rfl⟩ : syracuseStep 32539643 = 48809465) B48809465
theorem B1803679 : Blo 1803603 1803679 := bstep (se 1 (by rfl) ⟨1352759, by rfl⟩ : syracuseStep 1803679 = 2705519) B2705519
theorem B30827951 : Blo 1803603 30827951 := bstep (se 1 (by rfl) ⟨23120963, by rfl⟩ : syracuseStep 30827951 = 46241927) B46241927
theorem B5490217 : Blo 1803603 5490217 := bstep (se 2 (by rfl) ⟨2058831, by rfl⟩ : syracuseStep 5490217 = 4117663) B4117663
theorem B29263517 : Blo 1803603 29263517 := bstep (se 3 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 29263517 = 10973819) B10973819
theorem B6850291 : Blo 1803603 6850291 := bstep (se 1 (by rfl) ⟨5137718, by rfl⟩ : syracuseStep 6850291 = 10275437) B10275437
theorem B1804767 : Blo 1803603 1804767 := bstep (se 1 (by rfl) ⟨1353575, by rfl⟩ : syracuseStep 1804767 = 2707151) B2707151
theorem B23431843 : Blo 1803603 23431843 := bstep (se 1 (by rfl) ⟨17573882, by rfl⟩ : syracuseStep 23431843 = 35147765) B35147765
theorem B7711499 : Blo 1803603 7711499 := bstep (se 1 (by rfl) ⟨5783624, by rfl⟩ : syracuseStep 7711499 = 11567249) B11567249
theorem B5565215 : Blo 1803603 5565215 := bstep (se 1 (by rfl) ⟨4173911, by rfl⟩ : syracuseStep 5565215 = 8347823) B8347823
theorem B1805119 : Blo 1803603 1805119 := bstep (se 1 (by rfl) ⟨1353839, by rfl⟩ : syracuseStep 1805119 = 2707679) B2707679
theorem B4566041 : Blo 1803603 4566041 := bstep (se 2 (by rfl) ⟨1712265, by rfl⟩ : syracuseStep 4566041 = 3424531) B3424531
theorem B1805479 : Blo 1803603 1805479 := bstep (se 1 (by rfl) ⟨1354109, by rfl⟩ : syracuseStep 1805479 = 2708219) B2708219
theorem B13700339 : Blo 1803603 13700339 := bstep (se 1 (by rfl) ⟨10275254, by rfl⟩ : syracuseStep 13700339 = 20550509) B20550509
theorem B6090011 : Blo 1803603 6090011 := bstep (se 1 (by rfl) ⟨4567508, by rfl⟩ : syracuseStep 6090011 = 9135017) B9135017
theorem B4058495 : Blo 1803603 4058495 := bstep (se 1 (by rfl) ⟨3043871, by rfl⟩ : syracuseStep 4058495 = 6087743) B6087743
theorem B29281675 : Blo 1803603 29281675 := bstep (se 1 (by rfl) ⟨21961256, by rfl⟩ : syracuseStep 29281675 = 43922513) B43922513
theorem B2706923 : Blo 1803603 2706923 := bstep (se 1 (by rfl) ⟨2030192, by rfl⟩ : syracuseStep 2706923 = 4060385) B4060385
theorem B16469743 : Blo 1803603 16469743 := bstep (se 1 (by rfl) ⟨12352307, by rfl⟩ : syracuseStep 16469743 = 24704615) B24704615
theorem B2707367 : Blo 1803603 2707367 := bstep (se 1 (by rfl) ⟨2030525, by rfl⟩ : syracuseStep 2707367 = 4061051) B4061051
theorem B2707775 : Blo 1803603 2707775 := bstep (se 1 (by rfl) ⟨2030831, by rfl⟩ : syracuseStep 2707775 = 4061663) B4061663
theorem B4060025 : Blo 1803603 4060025 := bstep (se 2 (by rfl) ⟨1522509, by rfl⟩ : syracuseStep 4060025 = 3045019) B3045019
theorem B74061287 : Blo 1803603 74061287 := bstep (se 1 (by rfl) ⟨55545965, by rfl⟩ : syracuseStep 74061287 = 111091931) B111091931
theorem B2889263 : Blo 1803603 2889263 := bstep (se 1 (by rfl) ⟨2166947, by rfl⟩ : syracuseStep 2889263 = 4333895) B4333895
theorem B3044911 : Blo 1803603 3044911 := bstep (se 1 (by rfl) ⟨2283683, by rfl⟩ : syracuseStep 3044911 = 4567367) B4567367
theorem B23124041 : Blo 1803603 23124041 := bstep (se 2 (by rfl) ⟨8671515, by rfl⟩ : syracuseStep 23124041 = 17343031) B17343031
theorem B4061609 : Blo 1803603 4061609 := bstep (se 2 (by rfl) ⟨1523103, by rfl⟩ : syracuseStep 4061609 = 3046207) B3046207
theorem B21953081 : Blo 1803603 21953081 := bstep (se 2 (by rfl) ⟨8232405, by rfl⟩ : syracuseStep 21953081 = 16464811) B16464811
theorem B7814083 : Blo 1803603 7814083 := bstep (se 1 (by rfl) ⟨5860562, by rfl⟩ : syracuseStep 7814083 = 11721125) B11721125
theorem B6855623 : Blo 1803603 6855623 := bstep (se 1 (by rfl) ⟨5141717, by rfl⟩ : syracuseStep 6855623 = 10283435) B10283435
theorem B37051667 : Blo 1803603 37051667 := bstep (se 1 (by rfl) ⟨27788750, by rfl⟩ : syracuseStep 37051667 = 55577501) B55577501
theorem B18054463 : Blo 1803603 18054463 := bstep (se 1 (by rfl) ⟨13540847, by rfl⟩ : syracuseStep 18054463 = 27081695) B27081695
theorem B21962231 : Blo 1803603 21962231 := bstep (se 1 (by rfl) ⟨16471673, by rfl⟩ : syracuseStep 21962231 = 32943347) B32943347
theorem B2285111 : Blo 1803603 2285111 := bstep (se 1 (by rfl) ⟨1713833, by rfl⟩ : syracuseStep 2285111 = 3427667) B3427667
theorem B7708355 : Blo 1803603 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B43917065 : Blo 1803603 43917065 := bstep (se 2 (by rfl) ⟨16468899, by rfl⟩ : syracuseStep 43917065 = 32937799) B32937799
theorem B21693095 : Blo 1803603 21693095 := bstep (se 1 (by rfl) ⟨16269821, by rfl⟩ : syracuseStep 21693095 = 32539643) B32539643
theorem B49374191 : Blo 1803603 49374191 := bstep (se 1 (by rfl) ⟨37030643, by rfl⟩ : syracuseStep 49374191 = 74061287) B74061287
theorem B1926175 : Blo 1803603 1926175 := bstep (se 1 (by rfl) ⟨1444631, by rfl⟩ : syracuseStep 1926175 = 2889263) B2889263
theorem B24701111 : Blo 1803603 24701111 := bstep (se 1 (by rfl) ⟨18525833, by rfl⟩ : syracuseStep 24701111 = 37051667) B37051667
theorem B2705663 : Blo 1803603 2705663 := bstep (se 1 (by rfl) ⟨2029247, by rfl⟩ : syracuseStep 2705663 = 4058495) B4058495
theorem B1804615 : Blo 1803603 1804615 := bstep (se 1 (by rfl) ⟨1353461, by rfl⟩ : syracuseStep 1804615 = 2706923) B2706923
theorem B14641487 : Blo 1803603 14641487 := bstep (se 1 (by rfl) ⟨10981115, by rfl⟩ : syracuseStep 14641487 = 21962231) B21962231
theorem B5138903 : Blo 1803603 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B1804911 : Blo 1803603 1804911 := bstep (se 1 (by rfl) ⟨1353683, by rfl⟩ : syracuseStep 1804911 = 2707367) B2707367
theorem B4631327 : Blo 1803603 4631327 := bstep (se 1 (by rfl) ⟨3473495, by rfl⟩ : syracuseStep 4631327 = 6946991) B6946991
theorem B1805183 : Blo 1803603 1805183 := bstep (se 1 (by rfl) ⟨1353887, by rfl⟩ : syracuseStep 1805183 = 2707775) B2707775
theorem B7711807 : Blo 1803603 7711807 := bstep (se 1 (by rfl) ⟨5783855, by rfl⟩ : syracuseStep 7711807 = 11567711) B11567711
theorem B2706683 : Blo 1803603 2706683 := bstep (se 1 (by rfl) ⟨2030012, by rfl⟩ : syracuseStep 2706683 = 4060025) B4060025
theorem B19509011 : Blo 1803603 19509011 := bstep (se 1 (by rfl) ⟨14631758, by rfl⟩ : syracuseStep 19509011 = 29263517) B29263517
theorem B2707739 : Blo 1803603 2707739 := bstep (se 1 (by rfl) ⟨2030804, by rfl⟩ : syracuseStep 2707739 = 4061609) B4061609
theorem B14635387 : Blo 1803603 14635387 := bstep (se 1 (by rfl) ⟨10976540, by rfl⟩ : syracuseStep 14635387 = 21953081) B21953081
theorem B24072617 : Blo 1803603 24072617 := bstep (se 2 (by rfl) ⟨9027231, by rfl⟩ : syracuseStep 24072617 = 18054463) B18054463
theorem B5140999 : Blo 1803603 5140999 := bstep (se 1 (by rfl) ⟨3855749, by rfl⟩ : syracuseStep 5140999 = 7711499) B7711499
theorem B3044027 : Blo 1803603 3044027 := bstep (se 1 (by rfl) ⟨2283020, by rfl⟩ : syracuseStep 3044027 = 4566041) B4566041
theorem B7320289 : Blo 1803603 7320289 := bstep (se 2 (by rfl) ⟨2745108, by rfl⟩ : syracuseStep 7320289 = 5490217) B5490217
theorem B4059881 : Blo 1803603 4059881 := bstep (se 2 (by rfl) ⟨1522455, by rfl⟩ : syracuseStep 4059881 = 3044911) B3044911
theorem B4060007 : Blo 1803603 4060007 := bstep (se 1 (by rfl) ⟨3045005, by rfl⟩ : syracuseStep 4060007 = 6090011) B6090011
theorem B21959657 : Blo 1803603 21959657 := bstep (se 2 (by rfl) ⟨8234871, by rfl⟩ : syracuseStep 21959657 = 16469743) B16469743
theorem B31242457 : Blo 1803603 31242457 := bstep (se 2 (by rfl) ⟨11715921, by rfl⟩ : syracuseStep 31242457 = 23431843) B23431843
theorem B20551967 : Blo 1803603 20551967 := bstep (se 1 (by rfl) ⟨15413975, by rfl⟩ : syracuseStep 20551967 = 30827951) B30827951
theorem B10418777 : Blo 1803603 10418777 := bstep (se 2 (by rfl) ⟨3907041, by rfl⟩ : syracuseStep 10418777 = 7814083) B7814083
theorem B15416027 : Blo 1803603 15416027 := bstep (se 1 (by rfl) ⟨11562020, by rfl⟩ : syracuseStep 15416027 = 23124041) B23124041
theorem B6093629 : Blo 1803603 6093629 := bstep (se 3 (by rfl) ⟨1142555, by rfl⟩ : syracuseStep 6093629 = 2285111) B2285111
theorem B39042233 : Blo 1803603 39042233 := bstep (se 2 (by rfl) ⟨14640837, by rfl⟩ : syracuseStep 39042233 = 29281675) B29281675
theorem B3710143 : Blo 1803603 3710143 := bstep (se 1 (by rfl) ⟨2782607, by rfl⟩ : syracuseStep 3710143 = 5565215) B5565215
theorem B4570415 : Blo 1803603 4570415 := bstep (se 1 (by rfl) ⟨3427811, by rfl⟩ : syracuseStep 4570415 = 6855623) B6855623
theorem B9133559 : Blo 1803603 9133559 := bstep (se 1 (by rfl) ⟨6850169, by rfl⟩ : syracuseStep 9133559 = 13700339) B13700339
theorem B9133721 : Blo 1803603 9133721 := bstep (se 2 (by rfl) ⟨3425145, by rfl⟩ : syracuseStep 9133721 = 6850291) B6850291
theorem B29278043 : Blo 1803603 29278043 := bstep (se 1 (by rfl) ⟨21958532, by rfl⟩ : syracuseStep 29278043 = 43917065) B43917065
theorem B16048411 : Blo 1803603 16048411 := bstep (se 1 (by rfl) ⟨12036308, by rfl⟩ : syracuseStep 16048411 = 24072617) B24072617
theorem B41656609 : Blo 1803603 41656609 := bstep (se 2 (by rfl) ⟨15621228, by rfl⟩ : syracuseStep 41656609 = 31242457) B31242457
theorem B14639771 : Blo 1803603 14639771 := bstep (se 1 (by rfl) ⟨10979828, by rfl⟩ : syracuseStep 14639771 = 21959657) B21959657
theorem B32916127 : Blo 1803603 32916127 := bstep (se 1 (by rfl) ⟨24687095, by rfl⟩ : syracuseStep 32916127 = 49374191) B49374191
theorem B10282409 : Blo 1803603 10282409 := bstep (se 2 (by rfl) ⟨3855903, by rfl⟩ : syracuseStep 10282409 = 7711807) B7711807
theorem B16467407 : Blo 1803603 16467407 := bstep (se 1 (by rfl) ⟨12350555, by rfl⟩ : syracuseStep 16467407 = 24701111) B24701111
theorem B1803775 : Blo 1803603 1803775 := bstep (se 1 (by rfl) ⟨1352831, by rfl⟩ : syracuseStep 1803775 = 2705663) B2705663
theorem B78055397 : Blo 1803603 78055397 := bstep (se 4 (by rfl) ⟨7317693, by rfl⟩ : syracuseStep 78055397 = 14635387) B14635387
theorem B26028155 : Blo 1803603 26028155 := bstep (se 1 (by rfl) ⟨19521116, by rfl⟩ : syracuseStep 26028155 = 39042233) B39042233
theorem B1804455 : Blo 1803603 1804455 := bstep (se 1 (by rfl) ⟨1353341, by rfl⟩ : syracuseStep 1804455 = 2706683) B2706683
theorem B6089039 : Blo 1803603 6089039 := bstep (se 1 (by rfl) ⟨4566779, by rfl⟩ : syracuseStep 6089039 = 9133559) B9133559
theorem B6089147 : Blo 1803603 6089147 := bstep (se 1 (by rfl) ⟨4566860, by rfl⟩ : syracuseStep 6089147 = 9133721) B9133721
theorem B1805159 : Blo 1803603 1805159 := bstep (se 1 (by rfl) ⟨1353869, by rfl⟩ : syracuseStep 1805159 = 2707739) B2707739
theorem B14462063 : Blo 1803603 14462063 := bstep (se 1 (by rfl) ⟨10846547, by rfl⟩ : syracuseStep 14462063 = 21693095) B21693095
theorem B2706587 : Blo 1803603 2706587 := bstep (se 1 (by rfl) ⟨2029940, by rfl⟩ : syracuseStep 2706587 = 4059881) B4059881
theorem B2706671 : Blo 1803603 2706671 := bstep (se 1 (by rfl) ⟨2030003, by rfl⟩ : syracuseStep 2706671 = 4060007) B4060007
theorem B9760385 : Blo 1803603 9760385 := bstep (se 2 (by rfl) ⟨3660144, by rfl⟩ : syracuseStep 9760385 = 7320289) B7320289
theorem B19787429 : Blo 1803603 19787429 := bstep (se 4 (by rfl) ⟨1855071, by rfl⟩ : syracuseStep 19787429 = 3710143) B3710143
theorem B2568233 : Blo 1803603 2568233 := bstep (se 2 (by rfl) ⟨963087, by rfl⟩ : syracuseStep 2568233 = 1926175) B1926175
theorem B13701311 : Blo 1803603 13701311 := bstep (se 1 (by rfl) ⟨10275983, by rfl⟩ : syracuseStep 13701311 = 20551967) B20551967
theorem B9760991 : Blo 1803603 9760991 := bstep (se 1 (by rfl) ⟨7320743, by rfl⟩ : syracuseStep 9760991 = 14641487) B14641487
theorem B10277351 : Blo 1803603 10277351 := bstep (se 1 (by rfl) ⟨7708013, by rfl⟩ : syracuseStep 10277351 = 15416027) B15416027
theorem B13006007 : Blo 1803603 13006007 := bstep (se 1 (by rfl) ⟨9754505, by rfl⟩ : syracuseStep 13006007 = 19509011) B19509011
theorem B19518695 : Blo 1803603 19518695 := bstep (se 1 (by rfl) ⟨14639021, by rfl⟩ : syracuseStep 19518695 = 29278043) B29278043
theorem B2029351 : Blo 1803603 2029351 := bstep (se 1 (by rfl) ⟨1522013, by rfl⟩ : syracuseStep 2029351 = 3044027) B3044027
theorem B6854665 : Blo 1803603 6854665 := bstep (se 2 (by rfl) ⟨2570499, by rfl⟩ : syracuseStep 6854665 = 5140999) B5140999
theorem B13703741 : Blo 1803603 13703741 := bstep (se 3 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 13703741 = 5138903) B5138903
theorem B6945851 : Blo 1803603 6945851 := bstep (se 1 (by rfl) ⟨5209388, by rfl⟩ : syracuseStep 6945851 = 10418777) B10418777
theorem B3087551 : Blo 1803603 3087551 := bstep (se 1 (by rfl) ⟨2315663, by rfl⟩ : syracuseStep 3087551 = 4631327) B4631327
theorem B4062419 : Blo 1803603 4062419 := bstep (se 1 (by rfl) ⟨3046814, by rfl⟩ : syracuseStep 4062419 = 6093629) B6093629
theorem B3046943 : Blo 1803603 3046943 := bstep (se 1 (by rfl) ⟨2285207, by rfl⟩ : syracuseStep 3046943 = 4570415) B4570415
theorem B6848621 : Blo 1803603 6848621 := bstep (se 3 (by rfl) ⟨1284116, by rfl⟩ : syracuseStep 6848621 = 2568233) B2568233
theorem B9134207 : Blo 1803603 9134207 := bstep (se 1 (by rfl) ⟨6850655, by rfl⟩ : syracuseStep 9134207 = 13701311) B13701311
theorem B55542145 : Blo 1803603 55542145 := bstep (se 2 (by rfl) ⟨20828304, by rfl⟩ : syracuseStep 55542145 = 41656609) B41656609
theorem B10978271 : Blo 1803603 10978271 := bstep (se 1 (by rfl) ⟨8233703, by rfl⟩ : syracuseStep 10978271 = 16467407) B16467407
theorem B52036931 : Blo 1803603 52036931 := bstep (se 1 (by rfl) ⟨39027698, by rfl⟩ : syracuseStep 52036931 = 78055397) B78055397
theorem B17352103 : Blo 1803603 17352103 := bstep (se 1 (by rfl) ⟨13014077, by rfl⟩ : syracuseStep 17352103 = 26028155) B26028155
theorem B26027693 : Blo 1803603 26027693 := bstep (se 3 (by rfl) ⟨4880192, by rfl⟩ : syracuseStep 26027693 = 9760385) B9760385
theorem B9135827 : Blo 1803603 9135827 := bstep (se 1 (by rfl) ⟨6851870, by rfl⟩ : syracuseStep 9135827 = 13703741) B13703741
theorem B4630567 : Blo 1803603 4630567 := bstep (se 1 (by rfl) ⟨3472925, by rfl⟩ : syracuseStep 4630567 = 6945851) B6945851
theorem B1804391 : Blo 1803603 1804391 := bstep (se 1 (by rfl) ⟨1353293, by rfl⟩ : syracuseStep 1804391 = 2706587) B2706587
theorem B2058367 : Blo 1803603 2058367 := bstep (se 1 (by rfl) ⟨1543775, by rfl⟩ : syracuseStep 2058367 = 3087551) B3087551
theorem B1804447 : Blo 1803603 1804447 := bstep (se 1 (by rfl) ⟨1353335, by rfl⟩ : syracuseStep 1804447 = 2706671) B2706671
theorem B2705801 : Blo 1803603 2705801 := bstep (se 2 (by rfl) ⟨1014675, by rfl⟩ : syracuseStep 2705801 = 2029351) B2029351
theorem B13191619 : Blo 1803603 13191619 := bstep (se 1 (by rfl) ⟨9893714, by rfl⟩ : syracuseStep 13191619 = 19787429) B19787429
theorem B6851567 : Blo 1803603 6851567 := bstep (se 1 (by rfl) ⟨5138675, by rfl⟩ : syracuseStep 6851567 = 10277351) B10277351
theorem B9759847 : Blo 1803603 9759847 := bstep (se 1 (by rfl) ⟨7319885, by rfl⟩ : syracuseStep 9759847 = 14639771) B14639771
theorem B26029309 : Blo 1803603 26029309 := bstep (se 3 (by rfl) ⟨4880495, by rfl⟩ : syracuseStep 26029309 = 9760991) B9760991
theorem B8670671 : Blo 1803603 8670671 := bstep (se 1 (by rfl) ⟨6503003, by rfl⟩ : syracuseStep 8670671 = 13006007) B13006007
theorem B13012463 : Blo 1803603 13012463 := bstep (se 1 (by rfl) ⟨9759347, by rfl⟩ : syracuseStep 13012463 = 19518695) B19518695
theorem B43888169 : Blo 1803603 43888169 := bstep (se 2 (by rfl) ⟨16458063, by rfl⟩ : syracuseStep 43888169 = 32916127) B32916127
theorem B4059359 : Blo 1803603 4059359 := bstep (se 1 (by rfl) ⟨3044519, by rfl⟩ : syracuseStep 4059359 = 6089039) B6089039
theorem B4059431 : Blo 1803603 4059431 := bstep (se 1 (by rfl) ⟨3044573, by rfl⟩ : syracuseStep 4059431 = 6089147) B6089147
theorem B2708279 : Blo 1803603 2708279 := bstep (se 1 (by rfl) ⟨2031209, by rfl⟩ : syracuseStep 2708279 = 4062419) B4062419
theorem B9139553 : Blo 1803603 9139553 := bstep (se 2 (by rfl) ⟨3427332, by rfl⟩ : syracuseStep 9139553 = 6854665) B6854665
theorem B342366101 : Blo 1803603 342366101 := bstep (se 6 (by rfl) ⟨8024205, by rfl⟩ : syracuseStep 342366101 = 16048411) B16048411
theorem B6854939 : Blo 1803603 6854939 := bstep (se 1 (by rfl) ⟨5141204, by rfl⟩ : syracuseStep 6854939 = 10282409) B10282409
theorem B9641375 : Blo 1803603 9641375 := bstep (se 1 (by rfl) ⟨7231031, by rfl⟩ : syracuseStep 9641375 = 14462063) B14462063
theorem B2031295 : Blo 1803603 2031295 := bstep (se 1 (by rfl) ⟨1523471, by rfl⟩ : syracuseStep 2031295 = 3046943) B3046943
theorem B2744489 : Blo 1803603 2744489 := bstep (se 2 (by rfl) ⟨1029183, by rfl⟩ : syracuseStep 2744489 = 2058367) B2058367
theorem B74056193 : Blo 1803603 74056193 := bstep (se 2 (by rfl) ⟨27771072, by rfl⟩ : syracuseStep 74056193 = 55542145) B55542145
theorem B17588825 : Blo 1803603 17588825 := bstep (se 2 (by rfl) ⟨6595809, by rfl⟩ : syracuseStep 17588825 = 13191619) B13191619
theorem B17351795 : Blo 1803603 17351795 := bstep (se 1 (by rfl) ⟨13013846, by rfl⟩ : syracuseStep 17351795 = 26027693) B26027693
theorem B1803867 : Blo 1803603 1803867 := bstep (se 1 (by rfl) ⟨1352900, by rfl⟩ : syracuseStep 1803867 = 2705801) B2705801
theorem B23136137 : Blo 1803603 23136137 := bstep (se 2 (by rfl) ⟨8676051, by rfl⟩ : syracuseStep 23136137 = 17352103) B17352103
theorem B4565747 : Blo 1803603 4565747 := bstep (se 1 (by rfl) ⟨3424310, by rfl⟩ : syracuseStep 4565747 = 6848621) B6848621
theorem B6089471 : Blo 1803603 6089471 := bstep (se 1 (by rfl) ⟨4567103, by rfl⟩ : syracuseStep 6089471 = 9134207) B9134207
theorem B2706239 : Blo 1803603 2706239 := bstep (se 1 (by rfl) ⟨2029679, by rfl⟩ : syracuseStep 2706239 = 4059359) B4059359
theorem B2706287 : Blo 1803603 2706287 := bstep (se 1 (by rfl) ⟨2029715, by rfl⟩ : syracuseStep 2706287 = 4059431) B4059431
theorem B1805519 : Blo 1803603 1805519 := bstep (se 1 (by rfl) ⟨1354139, by rfl⟩ : syracuseStep 1805519 = 2708279) B2708279
theorem B7318847 : Blo 1803603 7318847 := bstep (se 1 (by rfl) ⟨5489135, by rfl⟩ : syracuseStep 7318847 = 10978271) B10978271
theorem B6090551 : Blo 1803603 6090551 := bstep (se 1 (by rfl) ⟨4567913, by rfl⟩ : syracuseStep 6090551 = 9135827) B9135827
theorem B117035117 : Blo 1803603 117035117 := bstep (se 3 (by rfl) ⟨21944084, by rfl⟩ : syracuseStep 117035117 = 43888169) B43888169
theorem B13013129 : Blo 1803603 13013129 := bstep (se 2 (by rfl) ⟨4879923, by rfl⟩ : syracuseStep 13013129 = 9759847) B9759847
theorem B34705745 : Blo 1803603 34705745 := bstep (se 2 (by rfl) ⟨13014654, by rfl⟩ : syracuseStep 34705745 = 26029309) B26029309
theorem B4567711 : Blo 1803603 4567711 := bstep (se 1 (by rfl) ⟨3425783, by rfl⟩ : syracuseStep 4567711 = 6851567) B6851567
theorem B2708393 : Blo 1803603 2708393 := bstep (se 2 (by rfl) ⟨1015647, by rfl⟩ : syracuseStep 2708393 = 2031295) B2031295
theorem B6427583 : Blo 1803603 6427583 := bstep (se 1 (by rfl) ⟨4820687, by rfl⟩ : syracuseStep 6427583 = 9641375) B9641375
theorem B5780447 : Blo 1803603 5780447 := bstep (se 1 (by rfl) ⟨4335335, by rfl⟩ : syracuseStep 5780447 = 8670671) B8670671
theorem B6174089 : Blo 1803603 6174089 := bstep (se 2 (by rfl) ⟨2315283, by rfl⟩ : syracuseStep 6174089 = 4630567) B4630567
theorem B34691287 : Blo 1803603 34691287 := bstep (se 1 (by rfl) ⟨26018465, by rfl⟩ : syracuseStep 34691287 = 52036931) B52036931
theorem B6093035 : Blo 1803603 6093035 := bstep (se 1 (by rfl) ⟨4569776, by rfl⟩ : syracuseStep 6093035 = 9139553) B9139553
theorem B228244067 : Blo 1803603 228244067 := bstep (se 1 (by rfl) ⟨171183050, by rfl⟩ : syracuseStep 228244067 = 342366101) B342366101
theorem B4569959 : Blo 1803603 4569959 := bstep (se 1 (by rfl) ⟨3427469, by rfl⟩ : syracuseStep 4569959 = 6854939) B6854939
theorem B8674975 : Blo 1803603 8674975 := bstep (se 1 (by rfl) ⟨6506231, by rfl⟩ : syracuseStep 8674975 = 13012463) B13012463
theorem B8675419 : Blo 1803603 8675419 := bstep (se 1 (by rfl) ⟨6506564, by rfl⟩ : syracuseStep 8675419 = 13013129) B13013129
theorem B4285055 : Blo 1803603 4285055 := bstep (se 1 (by rfl) ⟨3213791, by rfl⟩ : syracuseStep 4285055 = 6427583) B6427583
theorem B11567863 : Blo 1803603 11567863 := bstep (se 1 (by rfl) ⟨8675897, by rfl⟩ : syracuseStep 11567863 = 17351795) B17351795
theorem B1804159 : Blo 1803603 1804159 := bstep (se 1 (by rfl) ⟨1353119, by rfl⟩ : syracuseStep 1804159 = 2706239) B2706239
theorem B1804191 : Blo 1803603 1804191 := bstep (se 1 (by rfl) ⟨1353143, by rfl⟩ : syracuseStep 1804191 = 2706287) B2706287
theorem B78023411 : Blo 1803603 78023411 := bstep (se 1 (by rfl) ⟨58517558, by rfl⟩ : syracuseStep 78023411 = 117035117) B117035117
theorem B23137163 : Blo 1803603 23137163 := bstep (se 1 (by rfl) ⟨17352872, by rfl⟩ : syracuseStep 23137163 = 34705745) B34705745
theorem B46255049 : Blo 1803603 46255049 := bstep (se 2 (by rfl) ⟨17345643, by rfl⟩ : syracuseStep 46255049 = 34691287) B34691287
theorem B11725883 : Blo 1803603 11725883 := bstep (se 1 (by rfl) ⟨8794412, by rfl⟩ : syracuseStep 11725883 = 17588825) B17588825
theorem B7318637 : Blo 1803603 7318637 := bstep (se 3 (by rfl) ⟨1372244, by rfl⟩ : syracuseStep 7318637 = 2744489) B2744489
theorem B1805595 : Blo 1803603 1805595 := bstep (se 1 (by rfl) ⟨1354196, by rfl⟩ : syracuseStep 1805595 = 2708393) B2708393
theorem B3853631 : Blo 1803603 3853631 := bstep (se 1 (by rfl) ⟨2890223, by rfl⟩ : syracuseStep 3853631 = 5780447) B5780447
theorem B19516925 : Blo 1803603 19516925 := bstep (se 3 (by rfl) ⟨3659423, by rfl⟩ : syracuseStep 19516925 = 7318847) B7318847
theorem B6090281 : Blo 1803603 6090281 := bstep (se 2 (by rfl) ⟨2283855, by rfl⟩ : syracuseStep 6090281 = 4567711) B4567711
theorem B4116059 : Blo 1803603 4116059 := bstep (se 1 (by rfl) ⟨3087044, by rfl⟩ : syracuseStep 4116059 = 6174089) B6174089
theorem B152162711 : Blo 1803603 152162711 := bstep (se 1 (by rfl) ⟨114122033, by rfl⟩ : syracuseStep 152162711 = 228244067) B228244067
theorem B3043831 : Blo 1803603 3043831 := bstep (se 1 (by rfl) ⟨2282873, by rfl⟩ : syracuseStep 3043831 = 4565747) B4565747
theorem B4059647 : Blo 1803603 4059647 := bstep (se 1 (by rfl) ⟨3044735, by rfl⟩ : syracuseStep 4059647 = 6089471) B6089471
theorem B4060367 : Blo 1803603 4060367 := bstep (se 1 (by rfl) ⟨3045275, by rfl⟩ : syracuseStep 4060367 = 6090551) B6090551
theorem B49370795 : Blo 1803603 49370795 := bstep (se 1 (by rfl) ⟨37028096, by rfl⟩ : syracuseStep 49370795 = 74056193) B74056193
theorem B15424091 : Blo 1803603 15424091 := bstep (se 1 (by rfl) ⟨11568068, by rfl⟩ : syracuseStep 15424091 = 23136137) B23136137
theorem B4062023 : Blo 1803603 4062023 := bstep (se 1 (by rfl) ⟨3046517, by rfl⟩ : syracuseStep 4062023 = 6093035) B6093035
theorem B3046639 : Blo 1803603 3046639 := bstep (se 1 (by rfl) ⟨2284979, by rfl⟩ : syracuseStep 3046639 = 4569959) B4569959
theorem B11566633 : Blo 1803603 11566633 := bstep (se 2 (by rfl) ⟨4337487, by rfl⟩ : syracuseStep 11566633 = 8674975) B8674975
theorem B11567225 : Blo 1803603 11567225 := bstep (se 2 (by rfl) ⟨4337709, by rfl⟩ : syracuseStep 11567225 = 8675419) B8675419
theorem B101441807 : Blo 1803603 101441807 := bstep (se 1 (by rfl) ⟨76081355, by rfl⟩ : syracuseStep 101441807 = 152162711) B152162711
theorem B10282727 : Blo 1803603 10282727 := bstep (se 1 (by rfl) ⟨7712045, by rfl⟩ : syracuseStep 10282727 = 15424091) B15424091
theorem B30836699 : Blo 1803603 30836699 := bstep (se 1 (by rfl) ⟨23127524, by rfl⟩ : syracuseStep 30836699 = 46255049) B46255049
theorem B7817255 : Blo 1803603 7817255 := bstep (se 1 (by rfl) ⟨5862941, by rfl⟩ : syracuseStep 7817255 = 11725883) B11725883
theorem B13011283 : Blo 1803603 13011283 := bstep (se 1 (by rfl) ⟨9758462, by rfl⟩ : syracuseStep 13011283 = 19516925) B19516925
theorem B2706431 : Blo 1803603 2706431 := bstep (se 1 (by rfl) ⟨2029823, by rfl⟩ : syracuseStep 2706431 = 4059647) B4059647
theorem B4058441 : Blo 1803603 4058441 := bstep (se 2 (by rfl) ⟨1521915, by rfl⟩ : syracuseStep 4058441 = 3043831) B3043831
theorem B2706911 : Blo 1803603 2706911 := bstep (se 1 (by rfl) ⟨2030183, by rfl⟩ : syracuseStep 2706911 = 4060367) B4060367
theorem B52015607 : Blo 1803603 52015607 := bstep (se 1 (by rfl) ⟨39011705, by rfl⟩ : syracuseStep 52015607 = 78023411) B78023411
theorem B2708015 : Blo 1803603 2708015 := bstep (se 1 (by rfl) ⟨2031011, by rfl⟩ : syracuseStep 2708015 = 4062023) B4062023
theorem B15422177 : Blo 1803603 15422177 := bstep (se 2 (by rfl) ⟨5783316, by rfl⟩ : syracuseStep 15422177 = 11566633) B11566633
theorem B4879091 : Blo 1803603 4879091 := bstep (se 1 (by rfl) ⟨3659318, by rfl⟩ : syracuseStep 4879091 = 7318637) B7318637
theorem B2569087 : Blo 1803603 2569087 := bstep (se 1 (by rfl) ⟨1926815, by rfl⟩ : syracuseStep 2569087 = 3853631) B3853631
theorem B4060187 : Blo 1803603 4060187 := bstep (se 1 (by rfl) ⟨3045140, by rfl⟩ : syracuseStep 4060187 = 6090281) B6090281
theorem B2856703 : Blo 1803603 2856703 := bstep (se 1 (by rfl) ⟨2142527, by rfl⟩ : syracuseStep 2856703 = 4285055) B4285055
theorem B15423817 : Blo 1803603 15423817 := bstep (se 2 (by rfl) ⟨5783931, by rfl⟩ : syracuseStep 15423817 = 11567863) B11567863
theorem B32913863 : Blo 1803603 32913863 := bstep (se 1 (by rfl) ⟨24685397, by rfl⟩ : syracuseStep 32913863 = 49370795) B49370795
theorem B4062185 : Blo 1803603 4062185 := bstep (se 2 (by rfl) ⟨1523319, by rfl⟩ : syracuseStep 4062185 = 3046639) B3046639
theorem B15424775 : Blo 1803603 15424775 := bstep (se 1 (by rfl) ⟨11568581, by rfl⟩ : syracuseStep 15424775 = 23137163) B23137163
theorem B2744039 : Blo 1803603 2744039 := bstep (se 1 (by rfl) ⟨2058029, by rfl⟩ : syracuseStep 2744039 = 4116059) B4116059
theorem B34677071 : Blo 1803603 34677071 := bstep (se 1 (by rfl) ⟨26007803, by rfl⟩ : syracuseStep 34677071 = 52015607) B52015607
theorem B10281451 : Blo 1803603 10281451 := bstep (se 1 (by rfl) ⟨7711088, by rfl⟩ : syracuseStep 10281451 = 15422177) B15422177
theorem B3252727 : Blo 1803603 3252727 := bstep (se 1 (by rfl) ⟨2439545, by rfl⟩ : syracuseStep 3252727 = 4879091) B4879091
theorem B5211503 : Blo 1803603 5211503 := bstep (se 1 (by rfl) ⟨3908627, by rfl⟩ : syracuseStep 5211503 = 7817255) B7817255
theorem B1804287 : Blo 1803603 1804287 := bstep (se 1 (by rfl) ⟨1353215, by rfl⟩ : syracuseStep 1804287 = 2706431) B2706431
theorem B10283183 : Blo 1803603 10283183 := bstep (se 1 (by rfl) ⟨7712387, by rfl⟩ : syracuseStep 10283183 = 15424775) B15424775
theorem B2705627 : Blo 1803603 2705627 := bstep (se 1 (by rfl) ⟨2029220, by rfl⟩ : syracuseStep 2705627 = 4058441) B4058441
theorem B1804607 : Blo 1803603 1804607 := bstep (se 1 (by rfl) ⟨1353455, by rfl⟩ : syracuseStep 1804607 = 2706911) B2706911
theorem B1829359 : Blo 1803603 1829359 := bstep (se 1 (by rfl) ⟨1372019, by rfl⟩ : syracuseStep 1829359 = 2744039) B2744039
theorem B7711483 : Blo 1803603 7711483 := bstep (se 1 (by rfl) ⟨5783612, by rfl⟩ : syracuseStep 7711483 = 11567225) B11567225
theorem B67627871 : Blo 1803603 67627871 := bstep (se 1 (by rfl) ⟨50720903, by rfl⟩ : syracuseStep 67627871 = 101441807) B101441807
theorem B1805343 : Blo 1803603 1805343 := bstep (se 1 (by rfl) ⟨1354007, by rfl⟩ : syracuseStep 1805343 = 2708015) B2708015
theorem B20565089 : Blo 1803603 20565089 := bstep (se 2 (by rfl) ⟨7711908, by rfl⟩ : syracuseStep 20565089 = 15423817) B15423817
theorem B2706791 : Blo 1803603 2706791 := bstep (se 1 (by rfl) ⟨2030093, by rfl⟩ : syracuseStep 2706791 = 4060187) B4060187
theorem B20557799 : Blo 1803603 20557799 := bstep (se 1 (by rfl) ⟨15418349, by rfl⟩ : syracuseStep 20557799 = 30836699) B30836699
theorem B21942575 : Blo 1803603 21942575 := bstep (se 1 (by rfl) ⟨16456931, by rfl⟩ : syracuseStep 21942575 = 32913863) B32913863
theorem B2708123 : Blo 1803603 2708123 := bstep (se 1 (by rfl) ⟨2031092, by rfl⟩ : syracuseStep 2708123 = 4062185) B4062185
theorem B13701797 : Blo 1803603 13701797 := bstep (se 4 (by rfl) ⟨1284543, by rfl⟩ : syracuseStep 13701797 = 2569087) B2569087
theorem B17348377 : Blo 1803603 17348377 := bstep (se 2 (by rfl) ⟨6505641, by rfl⟩ : syracuseStep 17348377 = 13011283) B13011283
theorem B6855151 : Blo 1803603 6855151 := bstep (se 1 (by rfl) ⟨5141363, by rfl⟩ : syracuseStep 6855151 = 10282727) B10282727
theorem B3808937 : Blo 1803603 3808937 := bstep (se 2 (by rfl) ⟨1428351, by rfl⟩ : syracuseStep 3808937 = 2856703) B2856703
theorem B23118047 : Blo 1803603 23118047 := bstep (se 1 (by rfl) ⟨17338535, by rfl⟩ : syracuseStep 23118047 = 34677071) B34677071
theorem B9134531 : Blo 1803603 9134531 := bstep (se 1 (by rfl) ⟨6850898, by rfl⟩ : syracuseStep 9134531 = 13701797) B13701797
theorem B3474335 : Blo 1803603 3474335 := bstep (se 1 (by rfl) ⟨2605751, by rfl⟩ : syracuseStep 3474335 = 5211503) B5211503
theorem B10281977 : Blo 1803603 10281977 := bstep (se 2 (by rfl) ⟨3855741, by rfl⟩ : syracuseStep 10281977 = 7711483) B7711483
theorem B1803751 : Blo 1803603 1803751 := bstep (se 1 (by rfl) ⟨1352813, by rfl⟩ : syracuseStep 1803751 = 2705627) B2705627
theorem B1804527 : Blo 1803603 1804527 := bstep (se 1 (by rfl) ⟨1353395, by rfl⟩ : syracuseStep 1804527 = 2706791) B2706791
theorem B1805415 : Blo 1803603 1805415 := bstep (se 1 (by rfl) ⟨1354061, by rfl⟩ : syracuseStep 1805415 = 2708123) B2708123
theorem B13708601 : Blo 1803603 13708601 := bstep (se 2 (by rfl) ⟨5140725, by rfl⟩ : syracuseStep 13708601 = 10281451) B10281451
theorem B45085247 : Blo 1803603 45085247 := bstep (se 1 (by rfl) ⟨33813935, by rfl⟩ : syracuseStep 45085247 = 67627871) B67627871
theorem B13710059 : Blo 1803603 13710059 := bstep (se 1 (by rfl) ⟨10282544, by rfl⟩ : syracuseStep 13710059 = 20565089) B20565089
theorem B23131169 : Blo 1803603 23131169 := bstep (se 2 (by rfl) ⟨8674188, by rfl⟩ : syracuseStep 23131169 = 17348377) B17348377
theorem B17347877 : Blo 1803603 17347877 := bstep (se 4 (by rfl) ⟨1626363, by rfl⟩ : syracuseStep 17347877 = 3252727) B3252727
theorem B14628383 : Blo 1803603 14628383 := bstep (se 1 (by rfl) ⟨10971287, by rfl⟩ : syracuseStep 14628383 = 21942575) B21942575
theorem B2439145 : Blo 1803603 2439145 := bstep (se 2 (by rfl) ⟨914679, by rfl⟩ : syracuseStep 2439145 = 1829359) B1829359
theorem B9140201 : Blo 1803603 9140201 := bstep (se 2 (by rfl) ⟨3427575, by rfl⟩ : syracuseStep 9140201 = 6855151) B6855151
theorem B6855455 : Blo 1803603 6855455 := bstep (se 1 (by rfl) ⟨5141591, by rfl⟩ : syracuseStep 6855455 = 10283183) B10283183
theorem B2539291 : Blo 1803603 2539291 := bstep (se 1 (by rfl) ⟨1904468, by rfl⟩ : syracuseStep 2539291 = 3808937) B3808937
theorem B13705199 : Blo 1803603 13705199 := bstep (se 1 (by rfl) ⟨10278899, by rfl⟩ : syracuseStep 13705199 = 20557799) B20557799
theorem B30056831 : Blo 1803603 30056831 := bstep (se 1 (by rfl) ⟨22542623, by rfl⟩ : syracuseStep 30056831 = 45085247) B45085247
theorem B3385721 : Blo 1803603 3385721 := bstep (se 2 (by rfl) ⟨1269645, by rfl⟩ : syracuseStep 3385721 = 2539291) B2539291
theorem B9136799 : Blo 1803603 9136799 := bstep (se 1 (by rfl) ⟨6852599, by rfl⟩ : syracuseStep 9136799 = 13705199) B13705199
theorem B15412031 : Blo 1803603 15412031 := bstep (se 1 (by rfl) ⟨11559023, by rfl⟩ : syracuseStep 15412031 = 23118047) B23118047
theorem B6089687 : Blo 1803603 6089687 := bstep (se 1 (by rfl) ⟨4567265, by rfl⟩ : syracuseStep 6089687 = 9134531) B9134531
theorem B15420779 : Blo 1803603 15420779 := bstep (se 1 (by rfl) ⟨11565584, by rfl⟩ : syracuseStep 15420779 = 23131169) B23131169
theorem B9752255 : Blo 1803603 9752255 := bstep (se 1 (by rfl) ⟨7314191, by rfl⟩ : syracuseStep 9752255 = 14628383) B14628383
theorem B9139067 : Blo 1803603 9139067 := bstep (se 1 (by rfl) ⟨6854300, by rfl⟩ : syracuseStep 9139067 = 13708601) B13708601
theorem B9140039 : Blo 1803603 9140039 := bstep (se 1 (by rfl) ⟨6855029, by rfl⟩ : syracuseStep 9140039 = 13710059) B13710059
theorem B2316223 : Blo 1803603 2316223 := bstep (se 1 (by rfl) ⟨1737167, by rfl⟩ : syracuseStep 2316223 = 3474335) B3474335
theorem B6854651 : Blo 1803603 6854651 := bstep (se 1 (by rfl) ⟨5140988, by rfl⟩ : syracuseStep 6854651 = 10281977) B10281977
theorem B11565251 : Blo 1803603 11565251 := bstep (se 1 (by rfl) ⟨8673938, by rfl⟩ : syracuseStep 11565251 = 17347877) B17347877
theorem B6093467 : Blo 1803603 6093467 := bstep (se 1 (by rfl) ⟨4570100, by rfl⟩ : syracuseStep 6093467 = 9140201) B9140201
theorem B4570303 : Blo 1803603 4570303 := bstep (se 1 (by rfl) ⟨3427727, by rfl⟩ : syracuseStep 4570303 = 6855455) B6855455
theorem B3252193 : Blo 1803603 3252193 := bstep (se 2 (by rfl) ⟨1219572, by rfl⟩ : syracuseStep 3252193 = 2439145) B2439145
theorem B20037887 : Blo 1803603 20037887 := bstep (se 1 (by rfl) ⟨15028415, by rfl⟩ : syracuseStep 20037887 = 30056831) B30056831
theorem B7710167 : Blo 1803603 7710167 := bstep (se 1 (by rfl) ⟨5782625, by rfl⟩ : syracuseStep 7710167 = 11565251) B11565251
theorem B10274687 : Blo 1803603 10274687 := bstep (se 1 (by rfl) ⟨7706015, by rfl⟩ : syracuseStep 10274687 = 15412031) B15412031
theorem B17345029 : Blo 1803603 17345029 := bstep (se 4 (by rfl) ⟨1626096, by rfl⟩ : syracuseStep 17345029 = 3252193) B3252193
theorem B2257147 : Blo 1803603 2257147 := bstep (se 1 (by rfl) ⟨1692860, by rfl⟩ : syracuseStep 2257147 = 3385721) B3385721
theorem B6091199 : Blo 1803603 6091199 := bstep (se 1 (by rfl) ⟨4568399, by rfl⟩ : syracuseStep 6091199 = 9136799) B9136799
theorem B4059791 : Blo 1803603 4059791 := bstep (se 1 (by rfl) ⟨3044843, by rfl⟩ : syracuseStep 4059791 = 6089687) B6089687
theorem B6501503 : Blo 1803603 6501503 := bstep (se 1 (by rfl) ⟨4876127, by rfl⟩ : syracuseStep 6501503 = 9752255) B9752255
theorem B6092711 : Blo 1803603 6092711 := bstep (se 1 (by rfl) ⟨4569533, by rfl⟩ : syracuseStep 6092711 = 9139067) B9139067
theorem B6093359 : Blo 1803603 6093359 := bstep (se 1 (by rfl) ⟨4570019, by rfl⟩ : syracuseStep 6093359 = 9140039) B9140039
theorem B4569767 : Blo 1803603 4569767 := bstep (se 1 (by rfl) ⟨3427325, by rfl⟩ : syracuseStep 4569767 = 6854651) B6854651
theorem B6093737 : Blo 1803603 6093737 := bstep (se 2 (by rfl) ⟨2285151, by rfl⟩ : syracuseStep 6093737 = 4570303) B4570303
theorem B4062311 : Blo 1803603 4062311 := bstep (se 1 (by rfl) ⟨3046733, by rfl⟩ : syracuseStep 4062311 = 6093467) B6093467
theorem B10280519 : Blo 1803603 10280519 := bstep (se 1 (by rfl) ⟨7710389, by rfl⟩ : syracuseStep 10280519 = 15420779) B15420779
theorem B3088297 : Blo 1803603 3088297 := bstep (se 2 (by rfl) ⟨1158111, by rfl⟩ : syracuseStep 3088297 = 2316223) B2316223
theorem B23126705 : Blo 1803603 23126705 := bstep (se 2 (by rfl) ⟨8672514, by rfl⟩ : syracuseStep 23126705 = 17345029) B17345029
theorem B6849791 : Blo 1803603 6849791 := bstep (se 1 (by rfl) ⟨5137343, by rfl⟩ : syracuseStep 6849791 = 10274687) B10274687
theorem B3009529 : Blo 1803603 3009529 := bstep (se 2 (by rfl) ⟨1128573, by rfl⟩ : syracuseStep 3009529 = 2257147) B2257147
theorem B17337341 : Blo 1803603 17337341 := bstep (se 3 (by rfl) ⟨3250751, by rfl⟩ : syracuseStep 17337341 = 6501503) B6501503
theorem B2706527 : Blo 1803603 2706527 := bstep (se 1 (by rfl) ⟨2029895, by rfl⟩ : syracuseStep 2706527 = 4059791) B4059791
theorem B5140111 : Blo 1803603 5140111 := bstep (se 1 (by rfl) ⟨3855083, by rfl⟩ : syracuseStep 5140111 = 7710167) B7710167
theorem B2708207 : Blo 1803603 2708207 := bstep (se 1 (by rfl) ⟨2031155, by rfl⟩ : syracuseStep 2708207 = 4062311) B4062311
theorem B6853679 : Blo 1803603 6853679 := bstep (se 1 (by rfl) ⟨5140259, by rfl⟩ : syracuseStep 6853679 = 10280519) B10280519
theorem B4117729 : Blo 1803603 4117729 := bstep (se 2 (by rfl) ⟨1544148, by rfl⟩ : syracuseStep 4117729 = 3088297) B3088297
theorem B13358591 : Blo 1803603 13358591 := bstep (se 1 (by rfl) ⟨10018943, by rfl⟩ : syracuseStep 13358591 = 20037887) B20037887
theorem B4060799 : Blo 1803603 4060799 := bstep (se 1 (by rfl) ⟨3045599, by rfl⟩ : syracuseStep 4060799 = 6091199) B6091199
theorem B4061807 : Blo 1803603 4061807 := bstep (se 1 (by rfl) ⟨3046355, by rfl⟩ : syracuseStep 4061807 = 6092711) B6092711
theorem B4062239 : Blo 1803603 4062239 := bstep (se 1 (by rfl) ⟨3046679, by rfl⟩ : syracuseStep 4062239 = 6093359) B6093359
theorem B3046511 : Blo 1803603 3046511 := bstep (se 1 (by rfl) ⟨2284883, by rfl⟩ : syracuseStep 3046511 = 4569767) B4569767
theorem B4062491 : Blo 1803603 4062491 := bstep (se 1 (by rfl) ⟨3046868, by rfl⟩ : syracuseStep 4062491 = 6093737) B6093737
theorem B15417803 : Blo 1803603 15417803 := bstep (se 1 (by rfl) ⟨11563352, by rfl⟩ : syracuseStep 15417803 = 23126705) B23126705
theorem B8905727 : Blo 1803603 8905727 := bstep (se 1 (by rfl) ⟨6679295, by rfl⟩ : syracuseStep 8905727 = 13358591) B13358591
theorem B5490305 : Blo 1803603 5490305 := bstep (se 2 (by rfl) ⟨2058864, by rfl⟩ : syracuseStep 5490305 = 4117729) B4117729
theorem B1804351 : Blo 1803603 1804351 := bstep (se 1 (by rfl) ⟨1353263, by rfl⟩ : syracuseStep 1804351 = 2706527) B2706527
theorem B1805471 : Blo 1803603 1805471 := bstep (se 1 (by rfl) ⟨1354103, by rfl⟩ : syracuseStep 1805471 = 2708207) B2708207
theorem B4566527 : Blo 1803603 4566527 := bstep (se 1 (by rfl) ⟨3424895, by rfl⟩ : syracuseStep 4566527 = 6849791) B6849791
theorem B2707199 : Blo 1803603 2707199 := bstep (se 1 (by rfl) ⟨2030399, by rfl⟩ : syracuseStep 2707199 = 4060799) B4060799
theorem B2707871 : Blo 1803603 2707871 := bstep (se 1 (by rfl) ⟨2030903, by rfl⟩ : syracuseStep 2707871 = 4061807) B4061807
theorem B2708159 : Blo 1803603 2708159 := bstep (se 1 (by rfl) ⟨2031119, by rfl⟩ : syracuseStep 2708159 = 4062239) B4062239
theorem B2708327 : Blo 1803603 2708327 := bstep (se 1 (by rfl) ⟨2031245, by rfl⟩ : syracuseStep 2708327 = 4062491) B4062491
theorem B6853481 : Blo 1803603 6853481 := bstep (se 2 (by rfl) ⟨2570055, by rfl⟩ : syracuseStep 6853481 = 5140111) B5140111
theorem B4569119 : Blo 1803603 4569119 := bstep (se 1 (by rfl) ⟨3426839, by rfl⟩ : syracuseStep 4569119 = 6853679) B6853679
theorem B4012705 : Blo 1803603 4012705 := bstep (se 2 (by rfl) ⟨1504764, by rfl⟩ : syracuseStep 4012705 = 3009529) B3009529
theorem B11558227 : Blo 1803603 11558227 := bstep (se 1 (by rfl) ⟨8668670, by rfl⟩ : syracuseStep 11558227 = 17337341) B17337341
theorem B2031007 : Blo 1803603 2031007 := bstep (se 1 (by rfl) ⟨1523255, by rfl⟩ : syracuseStep 2031007 = 3046511) B3046511
theorem B5350273 : Blo 1803603 5350273 := bstep (se 2 (by rfl) ⟨2006352, by rfl⟩ : syracuseStep 5350273 = 4012705) B4012705
theorem B15410969 : Blo 1803603 15410969 := bstep (se 2 (by rfl) ⟨5779113, by rfl⟩ : syracuseStep 15410969 = 11558227) B11558227
theorem B1804799 : Blo 1803603 1804799 := bstep (se 1 (by rfl) ⟨1353599, by rfl⟩ : syracuseStep 1804799 = 2707199) B2707199
theorem B1805247 : Blo 1803603 1805247 := bstep (se 1 (by rfl) ⟨1353935, by rfl⟩ : syracuseStep 1805247 = 2707871) B2707871
theorem B1805439 : Blo 1803603 1805439 := bstep (se 1 (by rfl) ⟨1354079, by rfl⟩ : syracuseStep 1805439 = 2708159) B2708159
theorem B1805551 : Blo 1803603 1805551 := bstep (se 1 (by rfl) ⟨1354163, by rfl⟩ : syracuseStep 1805551 = 2708327) B2708327
theorem B2708009 : Blo 1803603 2708009 := bstep (se 2 (by rfl) ⟨1015503, by rfl⟩ : syracuseStep 2708009 = 2031007) B2031007
theorem B3044351 : Blo 1803603 3044351 := bstep (se 1 (by rfl) ⟨2283263, by rfl⟩ : syracuseStep 3044351 = 4566527) B4566527
theorem B10278535 : Blo 1803603 10278535 := bstep (se 1 (by rfl) ⟨7708901, by rfl⟩ : syracuseStep 10278535 = 15417803) B15417803
theorem B4568987 : Blo 1803603 4568987 := bstep (se 1 (by rfl) ⟨3426740, by rfl⟩ : syracuseStep 4568987 = 6853481) B6853481
theorem B5937151 : Blo 1803603 5937151 := bstep (se 1 (by rfl) ⟨4452863, by rfl⟩ : syracuseStep 5937151 = 8905727) B8905727
theorem B3660203 : Blo 1803603 3660203 := bstep (se 1 (by rfl) ⟨2745152, by rfl⟩ : syracuseStep 3660203 = 5490305) B5490305
theorem B3046079 : Blo 1803603 3046079 := bstep (se 1 (by rfl) ⟨2284559, by rfl⟩ : syracuseStep 3046079 = 4569119) B4569119
theorem B10273979 : Blo 1803603 10273979 := bstep (se 1 (by rfl) ⟨7705484, by rfl⟩ : syracuseStep 10273979 = 15410969) B15410969
theorem B28534789 : Blo 1803603 28534789 := bstep (se 4 (by rfl) ⟨2675136, by rfl⟩ : syracuseStep 28534789 = 5350273) B5350273
theorem B7916201 : Blo 1803603 7916201 := bstep (se 2 (by rfl) ⟨2968575, by rfl⟩ : syracuseStep 7916201 = 5937151) B5937151
theorem B1805339 : Blo 1803603 1805339 := bstep (se 1 (by rfl) ⟨1354004, by rfl⟩ : syracuseStep 1805339 = 2708009) B2708009
theorem B2029567 : Blo 1803603 2029567 := bstep (se 1 (by rfl) ⟨1522175, by rfl⟩ : syracuseStep 2029567 = 3044351) B3044351
theorem B3045991 : Blo 1803603 3045991 := bstep (se 1 (by rfl) ⟨2284493, by rfl⟩ : syracuseStep 3045991 = 4568987) B4568987
theorem B2440135 : Blo 1803603 2440135 := bstep (se 1 (by rfl) ⟨1830101, by rfl⟩ : syracuseStep 2440135 = 3660203) B3660203
theorem B2030719 : Blo 1803603 2030719 := bstep (se 1 (by rfl) ⟨1523039, by rfl⟩ : syracuseStep 2030719 = 3046079) B3046079
theorem B13704713 : Blo 1803603 13704713 := bstep (se 2 (by rfl) ⟨5139267, by rfl⟩ : syracuseStep 13704713 = 10278535) B10278535
theorem B6849319 : Blo 1803603 6849319 := bstep (se 1 (by rfl) ⟨5136989, by rfl⟩ : syracuseStep 6849319 = 10273979) B10273979
theorem B5277467 : Blo 1803603 5277467 := bstep (se 1 (by rfl) ⟨3958100, by rfl⟩ : syracuseStep 5277467 = 7916201) B7916201
theorem B9136475 : Blo 1803603 9136475 := bstep (se 1 (by rfl) ⟨6852356, by rfl⟩ : syracuseStep 9136475 = 13704713) B13704713
theorem B2706089 : Blo 1803603 2706089 := bstep (se 2 (by rfl) ⟨1014783, by rfl⟩ : syracuseStep 2706089 = 2029567) B2029567
theorem B38046385 : Blo 1803603 38046385 := bstep (se 2 (by rfl) ⟨14267394, by rfl⟩ : syracuseStep 38046385 = 28534789) B28534789
theorem B2707625 : Blo 1803603 2707625 := bstep (se 2 (by rfl) ⟨1015359, by rfl⟩ : syracuseStep 2707625 = 2030719) B2030719
theorem B13014053 : Blo 1803603 13014053 := bstep (se 4 (by rfl) ⟨1220067, by rfl⟩ : syracuseStep 13014053 = 2440135) B2440135
theorem B4061321 : Blo 1803603 4061321 := bstep (se 2 (by rfl) ⟨1522995, by rfl⟩ : syracuseStep 4061321 = 3045991) B3045991
theorem B8676035 : Blo 1803603 8676035 := bstep (se 1 (by rfl) ⟨6507026, by rfl⟩ : syracuseStep 8676035 = 13014053) B13014053
theorem B1804059 : Blo 1803603 1804059 := bstep (se 1 (by rfl) ⟨1353044, by rfl⟩ : syracuseStep 1804059 = 2706089) B2706089
theorem B1805083 : Blo 1803603 1805083 := bstep (se 1 (by rfl) ⟨1353812, by rfl⟩ : syracuseStep 1805083 = 2707625) B2707625
theorem B50728513 : Blo 1803603 50728513 := bstep (se 2 (by rfl) ⟨19023192, by rfl⟩ : syracuseStep 50728513 = 38046385) B38046385
theorem B3518311 : Blo 1803603 3518311 := bstep (se 1 (by rfl) ⟨2638733, by rfl⟩ : syracuseStep 3518311 = 5277467) B5277467
theorem B2707547 : Blo 1803603 2707547 := bstep (se 1 (by rfl) ⟨2030660, by rfl⟩ : syracuseStep 2707547 = 4061321) B4061321
theorem B6090983 : Blo 1803603 6090983 := bstep (se 1 (by rfl) ⟨4568237, by rfl⟩ : syracuseStep 6090983 = 9136475) B9136475
theorem B9132425 : Blo 1803603 9132425 := bstep (se 2 (by rfl) ⟨3424659, by rfl⟩ : syracuseStep 9132425 = 6849319) B6849319
theorem B5784023 : Blo 1803603 5784023 := bstep (se 1 (by rfl) ⟨4338017, by rfl⟩ : syracuseStep 5784023 = 8676035) B8676035
theorem B6088283 : Blo 1803603 6088283 := bstep (se 1 (by rfl) ⟨4566212, by rfl⟩ : syracuseStep 6088283 = 9132425) B9132425
theorem B1805031 : Blo 1803603 1805031 := bstep (se 1 (by rfl) ⟨1353773, by rfl⟩ : syracuseStep 1805031 = 2707547) B2707547
theorem B67638017 : Blo 1803603 67638017 := bstep (se 2 (by rfl) ⟨25364256, by rfl⟩ : syracuseStep 67638017 = 50728513) B50728513
theorem B4691081 : Blo 1803603 4691081 := bstep (se 2 (by rfl) ⟨1759155, by rfl⟩ : syracuseStep 4691081 = 3518311) B3518311
theorem B4060655 : Blo 1803603 4060655 := bstep (se 1 (by rfl) ⟨3045491, by rfl⟩ : syracuseStep 4060655 = 6090983) B6090983
theorem B12509549 : Blo 1803603 12509549 := bstep (se 3 (by rfl) ⟨2345540, by rfl⟩ : syracuseStep 12509549 = 4691081) B4691081
theorem B45092011 : Blo 1803603 45092011 := bstep (se 1 (by rfl) ⟨33819008, by rfl⟩ : syracuseStep 45092011 = 67638017) B67638017
theorem B2707103 : Blo 1803603 2707103 := bstep (se 1 (by rfl) ⟨2030327, by rfl⟩ : syracuseStep 2707103 = 4060655) B4060655
theorem B4058855 : Blo 1803603 4058855 := bstep (se 1 (by rfl) ⟨3044141, by rfl⟩ : syracuseStep 4058855 = 6088283) B6088283
theorem B3856015 : Blo 1803603 3856015 := bstep (se 1 (by rfl) ⟨2892011, by rfl⟩ : syracuseStep 3856015 = 5784023) B5784023
theorem B8339699 : Blo 1803603 8339699 := bstep (se 1 (by rfl) ⟨6254774, by rfl⟩ : syracuseStep 8339699 = 12509549) B12509549
theorem B60122681 : Blo 1803603 60122681 := bstep (se 2 (by rfl) ⟨22546005, by rfl⟩ : syracuseStep 60122681 = 45092011) B45092011
theorem B1804735 : Blo 1803603 1804735 := bstep (se 1 (by rfl) ⟨1353551, by rfl⟩ : syracuseStep 1804735 = 2707103) B2707103
theorem B2705903 : Blo 1803603 2705903 := bstep (se 1 (by rfl) ⟨2029427, by rfl⟩ : syracuseStep 2705903 = 4058855) B4058855
theorem B5141353 : Blo 1803603 5141353 := bstep (se 2 (by rfl) ⟨1928007, by rfl⟩ : syracuseStep 5141353 = 3856015) B3856015
theorem B1803935 : Blo 1803603 1803935 := bstep (se 1 (by rfl) ⟨1352951, by rfl⟩ : syracuseStep 1803935 = 2705903) B2705903
theorem B5559799 : Blo 1803603 5559799 := bstep (se 1 (by rfl) ⟨4169849, by rfl⟩ : syracuseStep 5559799 = 8339699) B8339699
theorem B40081787 : Blo 1803603 40081787 := bstep (se 1 (by rfl) ⟨30061340, by rfl⟩ : syracuseStep 40081787 = 60122681) B60122681
theorem B6855137 : Blo 1803603 6855137 := bstep (se 2 (by rfl) ⟨2570676, by rfl⟩ : syracuseStep 6855137 = 5141353) B5141353
theorem B26721191 : Blo 1803603 26721191 := bstep (se 1 (by rfl) ⟨20040893, by rfl⟩ : syracuseStep 26721191 = 40081787) B40081787
theorem B4570091 : Blo 1803603 4570091 := bstep (se 1 (by rfl) ⟨3427568, by rfl⟩ : syracuseStep 4570091 = 6855137) B6855137
theorem B7413065 : Blo 1803603 7413065 := bstep (se 2 (by rfl) ⟨2779899, by rfl⟩ : syracuseStep 7413065 = 5559799) B5559799
theorem B4942043 : Blo 1803603 4942043 := bstep (se 1 (by rfl) ⟨3706532, by rfl⟩ : syracuseStep 4942043 = 7413065) B7413065
theorem B17814127 : Blo 1803603 17814127 := bstep (se 1 (by rfl) ⟨13360595, by rfl⟩ : syracuseStep 17814127 = 26721191) B26721191
theorem B3046727 : Blo 1803603 3046727 := bstep (se 1 (by rfl) ⟨2285045, by rfl⟩ : syracuseStep 3046727 = 4570091) B4570091
theorem B3294695 : Blo 1803603 3294695 := bstep (se 1 (by rfl) ⟨2471021, by rfl⟩ : syracuseStep 3294695 = 4942043) B4942043
theorem B23752169 : Blo 1803603 23752169 := bstep (se 2 (by rfl) ⟨8907063, by rfl⟩ : syracuseStep 23752169 = 17814127) B17814127
theorem B2031151 : Blo 1803603 2031151 := bstep (se 1 (by rfl) ⟨1523363, by rfl⟩ : syracuseStep 2031151 = 3046727) B3046727
theorem B2196463 : Blo 1803603 2196463 := bstep (se 1 (by rfl) ⟨1647347, by rfl⟩ : syracuseStep 2196463 = 3294695) B3294695
theorem B2708201 : Blo 1803603 2708201 := bstep (se 2 (by rfl) ⟨1015575, by rfl⟩ : syracuseStep 2708201 = 2031151) B2031151
theorem B15834779 : Blo 1803603 15834779 := bstep (se 1 (by rfl) ⟨11876084, by rfl⟩ : syracuseStep 15834779 = 23752169) B23752169
theorem B1805467 : Blo 1803603 1805467 := bstep (se 1 (by rfl) ⟨1354100, by rfl⟩ : syracuseStep 1805467 = 2708201) B2708201
theorem B2928617 : Blo 1803603 2928617 := bstep (se 2 (by rfl) ⟨1098231, by rfl⟩ : syracuseStep 2928617 = 2196463) B2196463
theorem B10556519 : Blo 1803603 10556519 := bstep (se 1 (by rfl) ⟨7917389, by rfl⟩ : syracuseStep 10556519 = 15834779) B15834779
theorem B1952411 : Blo 1803603 1952411 := bstep (se 1 (by rfl) ⟨1464308, by rfl⟩ : syracuseStep 1952411 = 2928617) B2928617
theorem B112602869 : Blo 1803603 112602869 := bstep (se 5 (by rfl) ⟨5278259, by rfl⟩ : syracuseStep 112602869 = 10556519) B10556519
theorem B5206429 : Blo 1803603 5206429 := bstep (se 3 (by rfl) ⟨976205, by rfl⟩ : syracuseStep 5206429 = 1952411) B1952411
theorem B75068579 : Blo 1803603 75068579 := bstep (se 1 (by rfl) ⟨56301434, by rfl⟩ : syracuseStep 75068579 = 112602869) B112602869
theorem B200182877 : Blo 1803603 200182877 := bstep (se 3 (by rfl) ⟨37534289, by rfl⟩ : syracuseStep 200182877 = 75068579) B75068579
theorem B6941905 : Blo 1803603 6941905 := bstep (se 2 (by rfl) ⟨2603214, by rfl⟩ : syracuseStep 6941905 = 5206429) B5206429
theorem B37023493 : Blo 1803603 37023493 := bstep (se 4 (by rfl) ⟨3470952, by rfl⟩ : syracuseStep 37023493 = 6941905) B6941905
theorem B133455251 : Blo 1803603 133455251 := bstep (se 1 (by rfl) ⟨100091438, by rfl⟩ : syracuseStep 133455251 = 200182877) B200182877
theorem B88970167 : Blo 1803603 88970167 := bstep (se 1 (by rfl) ⟨66727625, by rfl⟩ : syracuseStep 88970167 = 133455251) B133455251
theorem B49364657 : Blo 1803603 49364657 := bstep (se 2 (by rfl) ⟨18511746, by rfl⟩ : syracuseStep 49364657 = 37023493) B37023493
theorem B32909771 : Blo 1803603 32909771 := bstep (se 1 (by rfl) ⟨24682328, by rfl⟩ : syracuseStep 32909771 = 49364657) B49364657
theorem B118626889 : Blo 1803603 118626889 := bstep (se 2 (by rfl) ⟨44485083, by rfl⟩ : syracuseStep 118626889 = 88970167) B88970167
theorem B158169185 : Blo 1803603 158169185 := bstep (se 2 (by rfl) ⟨59313444, by rfl⟩ : syracuseStep 158169185 = 118626889) B118626889
theorem B87759389 : Blo 1803603 87759389 := bstep (se 3 (by rfl) ⟨16454885, by rfl⟩ : syracuseStep 87759389 = 32909771) B32909771
theorem B105446123 : Blo 1803603 105446123 := bstep (se 1 (by rfl) ⟨79084592, by rfl⟩ : syracuseStep 105446123 = 158169185) B158169185
theorem B58506259 : Blo 1803603 58506259 := bstep (se 1 (by rfl) ⟨43879694, by rfl⟩ : syracuseStep 58506259 = 87759389) B87759389
theorem B70297415 : Blo 1803603 70297415 := bstep (se 1 (by rfl) ⟨52723061, by rfl⟩ : syracuseStep 70297415 = 105446123) B105446123
theorem B78008345 : Blo 1803603 78008345 := bstep (se 2 (by rfl) ⟨29253129, by rfl⟩ : syracuseStep 78008345 = 58506259) B58506259
theorem B52005563 : Blo 1803603 52005563 := bstep (se 1 (by rfl) ⟨39004172, by rfl⟩ : syracuseStep 52005563 = 78008345) B78008345
theorem B46864943 : Blo 1803603 46864943 := bstep (se 1 (by rfl) ⟨35148707, by rfl⟩ : syracuseStep 46864943 = 70297415) B70297415
theorem B34670375 : Blo 1803603 34670375 := bstep (se 1 (by rfl) ⟨26002781, by rfl⟩ : syracuseStep 34670375 = 52005563) B52005563
theorem B31243295 : Blo 1803603 31243295 := bstep (se 1 (by rfl) ⟨23432471, by rfl⟩ : syracuseStep 31243295 = 46864943) B46864943
theorem B23113583 : Blo 1803603 23113583 := bstep (se 1 (by rfl) ⟨17335187, by rfl⟩ : syracuseStep 23113583 = 34670375) B34670375
theorem B20828863 : Blo 1803603 20828863 := bstep (se 1 (by rfl) ⟨15621647, by rfl⟩ : syracuseStep 20828863 = 31243295) B31243295
theorem B27771817 : Blo 1803603 27771817 := bstep (se 2 (by rfl) ⟨10414431, by rfl⟩ : syracuseStep 27771817 = 20828863) B20828863
theorem B15409055 : Blo 1803603 15409055 := bstep (se 1 (by rfl) ⟨11556791, by rfl⟩ : syracuseStep 15409055 = 23113583) B23113583
theorem B37029089 : Blo 1803603 37029089 := bstep (se 2 (by rfl) ⟨13885908, by rfl⟩ : syracuseStep 37029089 = 27771817) B27771817
theorem B10272703 : Blo 1803603 10272703 := bstep (se 1 (by rfl) ⟨7704527, by rfl⟩ : syracuseStep 10272703 = 15409055) B15409055
theorem B24686059 : Blo 1803603 24686059 := bstep (se 1 (by rfl) ⟨18514544, by rfl⟩ : syracuseStep 24686059 = 37029089) B37029089
theorem B13696937 : Blo 1803603 13696937 := bstep (se 2 (by rfl) ⟨5136351, by rfl⟩ : syracuseStep 13696937 = 10272703) B10272703
theorem B9131291 : Blo 1803603 9131291 := bstep (se 1 (by rfl) ⟨6848468, by rfl⟩ : syracuseStep 9131291 = 13696937) B13696937
theorem B32914745 : Blo 1803603 32914745 := bstep (se 2 (by rfl) ⟨12343029, by rfl⟩ : syracuseStep 32914745 = 24686059) B24686059
theorem B6087527 : Blo 1803603 6087527 := bstep (se 1 (by rfl) ⟨4565645, by rfl⟩ : syracuseStep 6087527 = 9131291) B9131291
theorem B21943163 : Blo 1803603 21943163 := bstep (se 1 (by rfl) ⟨16457372, by rfl⟩ : syracuseStep 21943163 = 32914745) B32914745
theorem B4058351 : Blo 1803603 4058351 := bstep (se 1 (by rfl) ⟨3043763, by rfl⟩ : syracuseStep 4058351 = 6087527) B6087527
theorem B14628775 : Blo 1803603 14628775 := bstep (se 1 (by rfl) ⟨10971581, by rfl⟩ : syracuseStep 14628775 = 21943163) B21943163
theorem B2705567 : Blo 1803603 2705567 := bstep (se 1 (by rfl) ⟨2029175, by rfl⟩ : syracuseStep 2705567 = 4058351) B4058351
theorem B19505033 : Blo 1803603 19505033 := bstep (se 2 (by rfl) ⟨7314387, by rfl⟩ : syracuseStep 19505033 = 14628775) B14628775
theorem B1803711 : Blo 1803603 1803711 := bstep (se 1 (by rfl) ⟨1352783, by rfl⟩ : syracuseStep 1803711 = 2705567) B2705567
theorem B13003355 : Blo 1803603 13003355 := bstep (se 1 (by rfl) ⟨9752516, by rfl⟩ : syracuseStep 13003355 = 19505033) B19505033
theorem B8668903 : Blo 1803603 8668903 := bstep (se 1 (by rfl) ⟨6501677, by rfl⟩ : syracuseStep 8668903 = 13003355) B13003355
theorem B11558537 : Blo 1803603 11558537 := bstep (se 2 (by rfl) ⟨4334451, by rfl⟩ : syracuseStep 11558537 = 8668903) B8668903
theorem B7705691 : Blo 1803603 7705691 := bstep (se 1 (by rfl) ⟨5779268, by rfl⟩ : syracuseStep 7705691 = 11558537) B11558537
theorem B5137127 : Blo 1803603 5137127 := bstep (se 1 (by rfl) ⟨3852845, by rfl⟩ : syracuseStep 5137127 = 7705691) B7705691
theorem B3424751 : Blo 1803603 3424751 := bstep (se 1 (by rfl) ⟨2568563, by rfl⟩ : syracuseStep 3424751 = 5137127) B5137127
theorem B2283167 : Blo 1803603 2283167 := bstep (se 1 (by rfl) ⟨1712375, by rfl⟩ : syracuseStep 2283167 = 3424751) B3424751
theorem B6088445 : Blo 1803603 6088445 := bstep (se 3 (by rfl) ⟨1141583, by rfl⟩ : syracuseStep 6088445 = 2283167) B2283167
theorem B4058963 : Blo 1803603 4058963 := bstep (se 1 (by rfl) ⟨3044222, by rfl⟩ : syracuseStep 4058963 = 6088445) B6088445
theorem B2705975 : Blo 1803603 2705975 := bstep (se 1 (by rfl) ⟨2029481, by rfl⟩ : syracuseStep 2705975 = 4058963) B4058963
theorem B1803983 : Blo 1803603 1803983 := bstep (se 1 (by rfl) ⟨1352987, by rfl⟩ : syracuseStep 1803983 = 2705975) B2705975

theorem C0 (j : ℕ) (h1 : 450900 ≤ j) (h2 : j ≤ 451400) : Blo 1803603 (4 * j + 3) := by
  interval_cases j
  · exact B1803603
  · exact B1803607
  · exact B1803611
  · exact B1803615
  · exact B1803619
  · exact B1803623
  · exact B1803627
  · exact B1803631
  · exact B1803635
  · exact B1803639
  · exact B1803643
  · exact B1803647
  · exact B1803651
  · exact B1803655
  · exact B1803659
  · exact B1803663
  · exact B1803667
  · exact B1803671
  · exact B1803675
  · exact B1803679
  · exact B1803683
  · exact B1803687
  · exact B1803691
  · exact B1803695
  · exact B1803699
  · exact B1803703
  · exact B1803707
  · exact B1803711
  · exact B1803715
  · exact B1803719
  · exact B1803723
  · exact B1803727
  · exact B1803731
  · exact B1803735
  · exact B1803739
  · exact B1803743
  · exact B1803747
  · exact B1803751
  · exact B1803755
  · exact B1803759
  · exact B1803763
  · exact B1803767
  · exact B1803771
  · exact B1803775
  · exact B1803779
  · exact B1803783
  · exact B1803787
  · exact B1803791
  · exact B1803795
  · exact B1803799
  · exact B1803803
  · exact B1803807
  · exact B1803811
  · exact B1803815
  · exact B1803819
  · exact B1803823
  · exact B1803827
  · exact B1803831
  · exact B1803835
  · exact B1803839
  · exact B1803843
  · exact B1803847
  · exact B1803851
  · exact B1803855
  · exact B1803859
  · exact B1803863
  · exact B1803867
  · exact B1803871
  · exact B1803875
  · exact B1803879
  · exact B1803883
  · exact B1803887
  · exact B1803891
  · exact B1803895
  · exact B1803899
  · exact B1803903
  · exact B1803907
  · exact B1803911
  · exact B1803915
  · exact B1803919
  · exact B1803923
  · exact B1803927
  · exact B1803931
  · exact B1803935
  · exact B1803939
  · exact B1803943
  · exact B1803947
  · exact B1803951
  · exact B1803955
  · exact B1803959
  · exact B1803963
  · exact B1803967
  · exact B1803971
  · exact B1803975
  · exact B1803979
  · exact B1803983
  · exact B1803987
  · exact B1803991
  · exact B1803995
  · exact B1803999
  · exact B1804003
  · exact B1804007
  · exact B1804011
  · exact B1804015
  · exact B1804019
  · exact B1804023
  · exact B1804027
  · exact B1804031
  · exact B1804035
  · exact B1804039
  · exact B1804043
  · exact B1804047
  · exact B1804051
  · exact B1804055
  · exact B1804059
  · exact B1804063
  · exact B1804067
  · exact B1804071
  · exact B1804075
  · exact B1804079
  · exact B1804083
  · exact B1804087
  · exact B1804091
  · exact B1804095
  · exact B1804099
  · exact B1804103
  · exact B1804107
  · exact B1804111
  · exact B1804115
  · exact B1804119
  · exact B1804123
  · exact B1804127
  · exact B1804131
  · exact B1804135
  · exact B1804139
  · exact B1804143
  · exact B1804147
  · exact B1804151
  · exact B1804155
  · exact B1804159
  · exact B1804163
  · exact B1804167
  · exact B1804171
  · exact B1804175
  · exact B1804179
  · exact B1804183
  · exact B1804187
  · exact B1804191
  · exact B1804195
  · exact B1804199
  · exact B1804203
  · exact B1804207
  · exact B1804211
  · exact B1804215
  · exact B1804219
  · exact B1804223
  · exact B1804227
  · exact B1804231
  · exact B1804235
  · exact B1804239
  · exact B1804243
  · exact B1804247
  · exact B1804251
  · exact B1804255
  · exact B1804259
  · exact B1804263
  · exact B1804267
  · exact B1804271
  · exact B1804275
  · exact B1804279
  · exact B1804283
  · exact B1804287
  · exact B1804291
  · exact B1804295
  · exact B1804299
  · exact B1804303
  · exact B1804307
  · exact B1804311
  · exact B1804315
  · exact B1804319
  · exact B1804323
  · exact B1804327
  · exact B1804331
  · exact B1804335
  · exact B1804339
  · exact B1804343
  · exact B1804347
  · exact B1804351
  · exact B1804355
  · exact B1804359
  · exact B1804363
  · exact B1804367
  · exact B1804371
  · exact B1804375
  · exact B1804379
  · exact B1804383
  · exact B1804387
  · exact B1804391
  · exact B1804395
  · exact B1804399
  · exact B1804403
  · exact B1804407
  · exact B1804411
  · exact B1804415
  · exact B1804419
  · exact B1804423
  · exact B1804427
  · exact B1804431
  · exact B1804435
  · exact B1804439
  · exact B1804443
  · exact B1804447
  · exact B1804451
  · exact B1804455
  · exact B1804459
  · exact B1804463
  · exact B1804467
  · exact B1804471
  · exact B1804475
  · exact B1804479
  · exact B1804483
  · exact B1804487
  · exact B1804491
  · exact B1804495
  · exact B1804499
  · exact B1804503
  · exact B1804507
  · exact B1804511
  · exact B1804515
  · exact B1804519
  · exact B1804523
  · exact B1804527
  · exact B1804531
  · exact B1804535
  · exact B1804539
  · exact B1804543
  · exact B1804547
  · exact B1804551
  · exact B1804555
  · exact B1804559
  · exact B1804563
  · exact B1804567
  · exact B1804571
  · exact B1804575
  · exact B1804579
  · exact B1804583
  · exact B1804587
  · exact B1804591
  · exact B1804595
  · exact B1804599
  · exact B1804603
  · exact B1804607
  · exact B1804611
  · exact B1804615
  · exact B1804619
  · exact B1804623
  · exact B1804627
  · exact B1804631
  · exact B1804635
  · exact B1804639
  · exact B1804643
  · exact B1804647
  · exact B1804651
  · exact B1804655
  · exact B1804659
  · exact B1804663
  · exact B1804667
  · exact B1804671
  · exact B1804675
  · exact B1804679
  · exact B1804683
  · exact B1804687
  · exact B1804691
  · exact B1804695
  · exact B1804699
  · exact B1804703
  · exact B1804707
  · exact B1804711
  · exact B1804715
  · exact B1804719
  · exact B1804723
  · exact B1804727
  · exact B1804731
  · exact B1804735
  · exact B1804739
  · exact B1804743
  · exact B1804747
  · exact B1804751
  · exact B1804755
  · exact B1804759
  · exact B1804763
  · exact B1804767
  · exact B1804771
  · exact B1804775
  · exact B1804779
  · exact B1804783
  · exact B1804787
  · exact B1804791
  · exact B1804795
  · exact B1804799
  · exact B1804803
  · exact B1804807
  · exact B1804811
  · exact B1804815
  · exact B1804819
  · exact B1804823
  · exact B1804827
  · exact B1804831
  · exact B1804835
  · exact B1804839
  · exact B1804843
  · exact B1804847
  · exact B1804851
  · exact B1804855
  · exact B1804859
  · exact B1804863
  · exact B1804867
  · exact B1804871
  · exact B1804875
  · exact B1804879
  · exact B1804883
  · exact B1804887
  · exact B1804891
  · exact B1804895
  · exact B1804899
  · exact B1804903
  · exact B1804907
  · exact B1804911
  · exact B1804915
  · exact B1804919
  · exact B1804923
  · exact B1804927
  · exact B1804931
  · exact B1804935
  · exact B1804939
  · exact B1804943
  · exact B1804947
  · exact B1804951
  · exact B1804955
  · exact B1804959
  · exact B1804963
  · exact B1804967
  · exact B1804971
  · exact B1804975
  · exact B1804979
  · exact B1804983
  · exact B1804987
  · exact B1804991
  · exact B1804995
  · exact B1804999
  · exact B1805003
  · exact B1805007
  · exact B1805011
  · exact B1805015
  · exact B1805019
  · exact B1805023
  · exact B1805027
  · exact B1805031
  · exact B1805035
  · exact B1805039
  · exact B1805043
  · exact B1805047
  · exact B1805051
  · exact B1805055
  · exact B1805059
  · exact B1805063
  · exact B1805067
  · exact B1805071
  · exact B1805075
  · exact B1805079
  · exact B1805083
  · exact B1805087
  · exact B1805091
  · exact B1805095
  · exact B1805099
  · exact B1805103
  · exact B1805107
  · exact B1805111
  · exact B1805115
  · exact B1805119
  · exact B1805123
  · exact B1805127
  · exact B1805131
  · exact B1805135
  · exact B1805139
  · exact B1805143
  · exact B1805147
  · exact B1805151
  · exact B1805155
  · exact B1805159
  · exact B1805163
  · exact B1805167
  · exact B1805171
  · exact B1805175
  · exact B1805179
  · exact B1805183
  · exact B1805187
  · exact B1805191
  · exact B1805195
  · exact B1805199
  · exact B1805203
  · exact B1805207
  · exact B1805211
  · exact B1805215
  · exact B1805219
  · exact B1805223
  · exact B1805227
  · exact B1805231
  · exact B1805235
  · exact B1805239
  · exact B1805243
  · exact B1805247
  · exact B1805251
  · exact B1805255
  · exact B1805259
  · exact B1805263
  · exact B1805267
  · exact B1805271
  · exact B1805275
  · exact B1805279
  · exact B1805283
  · exact B1805287
  · exact B1805291
  · exact B1805295
  · exact B1805299
  · exact B1805303
  · exact B1805307
  · exact B1805311
  · exact B1805315
  · exact B1805319
  · exact B1805323
  · exact B1805327
  · exact B1805331
  · exact B1805335
  · exact B1805339
  · exact B1805343
  · exact B1805347
  · exact B1805351
  · exact B1805355
  · exact B1805359
  · exact B1805363
  · exact B1805367
  · exact B1805371
  · exact B1805375
  · exact B1805379
  · exact B1805383
  · exact B1805387
  · exact B1805391
  · exact B1805395
  · exact B1805399
  · exact B1805403
  · exact B1805407
  · exact B1805411
  · exact B1805415
  · exact B1805419
  · exact B1805423
  · exact B1805427
  · exact B1805431
  · exact B1805435
  · exact B1805439
  · exact B1805443
  · exact B1805447
  · exact B1805451
  · exact B1805455
  · exact B1805459
  · exact B1805463
  · exact B1805467
  · exact B1805471
  · exact B1805475
  · exact B1805479
  · exact B1805483
  · exact B1805487
  · exact B1805491
  · exact B1805495
  · exact B1805499
  · exact B1805503
  · exact B1805507
  · exact B1805511
  · exact B1805515
  · exact B1805519
  · exact B1805523
  · exact B1805527
  · exact B1805531
  · exact B1805535
  · exact B1805539
  · exact B1805543
  · exact B1805547
  · exact B1805551
  · exact B1805555
  · exact B1805559
  · exact B1805563
  · exact B1805567
  · exact B1805571
  · exact B1805575
  · exact B1805579
  · exact B1805583
  · exact B1805587
  · exact B1805591
  · exact B1805595
  · exact B1805599
  · exact B1805603

theorem solution (m : ℕ) (hlo : 1803603 ≤ m) (hhi : m ≤ 1805603) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 450900 ≤ j := by omega
    have hj2 : j ≤ 451400 := by omega
    have hb : Blo 1803603 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
